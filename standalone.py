#!/usr/bin/env python3
"""
Daily Threads carousel.

Pulls the last N days of published Threads posts from Metricool, scores them on
reach and interaction, throws out the ones that shouldn't be recycled, renders
the survivors as carousel slides, uploads the slides to Cloudinary, and schedules
a TikTok photo carousel back through Metricool.

Designed to run unattended from GitHub Actions once a day.

    python standalone.py --dry-run          render only, nothing leaves the runner
    python standalone.py --no-publish       upload + create the post as a draft
    python standalone.py                    upload + schedule it for real

Environment:
    METRICOOL_TOKEN, METRICOOL_USER_ID, METRICOOL_BLOG_ID
    CLOUDINARY_CLOUD, CLOUDINARY_KEY, CLOUDINARY_SECRET
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import os
import re
import sys
import time
import unicodedata
from dataclasses import dataclass, field
from datetime import datetime, timedelta, timezone
from pathlib import Path

import requests
from PIL import Image, ImageDraw, ImageFont

# --------------------------------------------------------------------------- #
# configuration
# --------------------------------------------------------------------------- #

METRICOOL_BASE = "https://app.metricool.com/api"
CLOUDINARY_BASE = "https://api.cloudinary.com/v1_1"

TIMEZONE_NAME = "America/Los_Angeles"

# Brand-facing strings. Overridable by environment so the same script can be
# pointed at another Metricool brand without editing code.
HANDLE = os.environ.get("CAROUSEL_HANDLE", "@the.alexmaldonado")
COVER_KICKER = os.environ.get("CAROUSEL_KICKER", "from my Threads")
COVER_HEADLINE = os.environ.get(
    "CAROUSEL_HEADLINE", "What the ADHD internet stopped scrolling for")
OUTRO_LINE = os.environ.get(
    "CAROUSEL_OUTRO", "If this is your brain too, you're in the right place.")
HASHTAGS = os.environ.get(
    "CAROUSEL_HASHTAGS",
    "#adhd #adhdtiktok #neurodivergent #adhdcommunity #latediagnosedadhd")
CAPTION_LINE = os.environ.get(
    "CAROUSEL_CAPTION_LINE",
    "{n} things the ADHD side of Threads stopped for this week. Save this one.")

SLIDE_W, SLIDE_H = 1080, 1350
MARGIN = 96

# Palette — deep slate ground, warm accent. Reads well at thumbnail size.
BG = (16, 23, 30)
BG_ALT = (23, 32, 41)
INK = (240, 244, 246)
INK_SOFT = (150, 167, 176)
ACCENT = (232, 176, 96)

# Appended boilerplate signatures — cut from the slide text entirely.
SIGNATURE_MARKERS = (
    "— alex maldonado, circle real estate",
    "- alex maldonado, circle real estate",
    "alex maldonado | circle real estate",
)

# Stock tails from the autolist's mad-lib generator. These posts read as broken
# sentences ("With ADHD loves new ideas but hates follow-through because the
# magic's in the mayhem") and are filler, not the account's real voice. Cutting
# the tail wouldn't rescue the grammar, so they're just scored way down.
STOCK_TAILS = (
    "because the magic's in the mayhem",
    "so i made peace with my process",
    "so i learned to design around my brain",
    "so i built tools that work with it, not against it",
    "so i design around it now",
    "yet here i am, still thriving",
    "but hey, it keeps life interesting",
    "but somehow, i still pull it off",
    "and honestly, i'm proud of the chaos",
    "and i've stopped trying to fight it",
)
TEMPLATE_MARKERS = SIGNATURE_MARKERS + STOCK_TAILS
TEMPLATE_PENALTY = 0.30

# Engagement bait the autolist staples onto the end. Fine in a feed, dead weight
# on a slide — stripped before rendering.
BAIT_SUFFIXES = (
    "this hit.", "this hit", "anyone else?", "anyone else feel this?",
    "relatable?", "you feel this too?", "this one's personal.",
    "drop a if you get this.", "drop a if you get this",
    "be honest — this one's you too, right?", "same.", "let's connect!",
    "who's with me?", "tell me i'm not alone.",
)

# Hard veto — these never make a slide regardless of how well they did.
VETO_PATTERNS = (
    r"link\s*in\s*(my\s*)?bio",
    r"linkinbio",
    r"link\s*in\s*profile",
    r"tap\s*the\s*link",
    r"click\s*the\s*link",
    r"swipe\s*up",
    r"see\s*link\s*below",
)

MIN_CHARS = 25
MAX_CHARS = 300
DEFAULT_LOOKBACK_DAYS = 14
DEFAULT_SLIDES = 6
DEFAULT_MIN_SLIDES = 4
ABSOLUTE_VIEW_FLOOR = 35

FONT_CANDIDATES_BOLD = (
    "/usr/share/fonts/truetype/noto/NotoSans-Bold.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Bold.ttf",
    "/System/Library/Fonts/Supplemental/Arial Bold.ttf",
)
FONT_CANDIDATES_REGULAR = (
    "/usr/share/fonts/truetype/noto/NotoSans-Regular.ttf",
    "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    "/usr/share/fonts/truetype/liberation/LiberationSans-Regular.ttf",
    "/System/Library/Fonts/Supplemental/Arial.ttf",
)


def log(msg: str) -> None:
    print(f"[carousel] {msg}", flush=True)


# --------------------------------------------------------------------------- #
# text handling
# --------------------------------------------------------------------------- #

def strip_emoji(text: str) -> str:
    """Drop pictographs. The bundled fonts have no colour glyphs, and a row of
    tofu boxes looks worse than no emoji at all."""
    out = []
    for ch in text:
        cat = unicodedata.category(ch)
        cp = ord(ch)
        pictographic = (
            0x1F000 <= cp <= 0x1FAFF
            or 0x2600 <= cp <= 0x27BF
            or 0xFE00 <= cp <= 0xFE0F
            or 0x1F1E6 <= cp <= 0x1F1FF
            or cp in (0x200D, 0x20E3, 0x2B50, 0x2B06, 0x2B07)
        )
        if pictographic or cat == "So":
            continue
        out.append(ch)
    return "".join(out)


def straighten(text: str) -> str:
    """Curly quotes in, straight quotes out — the autolist emits typographic
    apostrophes and every marker list here is written with plain ones."""
    return (text.replace("’", "'").replace("‘", "'")
                .replace("“", '"').replace("”", '"'))


def clean_for_slide(text: str) -> str:
    t = straighten(text)
    for marker in SIGNATURE_MARKERS:
        idx = t.lower().find(marker)
        if idx != -1:
            t = t[:idx]
    t = strip_emoji(t)
    t = re.sub(r"#\w+", "", t)
    t = re.sub(r"https?://\S+", "", t)
    t = t.replace("*", "")
    t = re.sub(r"\s+", " ", t).strip()

    # Peel engagement bait off the end, repeatedly — some posts stack two.
    changed = True
    while changed:
        changed = False
        low = t.lower().rstrip()
        for bait in BAIT_SUFFIXES:
            if low.endswith(bait):
                t = t[: len(t) - len(bait)].rstrip()
                changed = True
                break

    t = re.sub(r"\s+", " ", t).strip()
    t = t.strip(" -–—|·,")
    return t


def normalize_key(text: str) -> str:
    """Collapse a post to a comparison key so the same line posted three times
    in a fortnight only earns one slide."""
    t = clean_for_slide(text).lower()
    t = re.sub(r"[^a-z0-9 ]", "", t)
    words = t.split()
    return " ".join(words[:12])


def is_vetoed(text: str) -> bool:
    low = straighten(text).lower()
    return any(re.search(p, low) for p in VETO_PATTERNS)


def is_templated(text: str) -> bool:
    low = straighten(text).lower()
    return any(m in low for m in TEMPLATE_MARKERS)


# --------------------------------------------------------------------------- #
# post model
# --------------------------------------------------------------------------- #

@dataclass
class Post:
    text: str
    url: str
    published: datetime
    views: float = 0.0
    likes: float = 0.0
    replies: float = 0.0
    reposts: float = 0.0
    shares: float = 0.0
    score: float = 0.0
    slide_text: str = ""
    notes: list[str] = field(default_factory=list)

    @property
    def interactions(self) -> float:
        return (
            self.likes * 8
            + self.replies * 12
            + self.reposts * 15
            + self.shares * 10
        )


def _num(v) -> float:
    if v in (None, "", "null"):
        return 0.0
    try:
        return float(v)
    except (TypeError, ValueError):
        return 0.0


def _parse_when(v) -> datetime:
    if isinstance(v, dict):
        v = v.get("dateTime") or v.get("date") or ""
    s = str(v).strip()
    if not s:
        return datetime.utcnow()
    for fmt in ("%Y%m%d%H%M%S", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%d %H:%M:%S", "%Y%m%d", "%Y-%m-%d"):
        try:
            return datetime.strptime(s, fmt)
        except ValueError:
            continue
    try:
        return datetime.fromisoformat(s.replace("Z", "+00:00")).replace(tzinfo=None)
    except ValueError:
        return datetime.utcnow()


# --------------------------------------------------------------------------- #
# Metricool
# --------------------------------------------------------------------------- #

class Metricool:
    def __init__(self, token: str, user_id: str, blog_id: str):
        self.token = token
        self.user_id = str(user_id)
        self.blog_id = str(blog_id)
        self.session = requests.Session()
        self.session.headers.update(
            {"X-Mc-Auth": token, "Accept": "application/json"}
        )

    def _auth_params(self) -> dict:
        return {
            "userId": self.user_id,
            "blogId": self.blog_id,
            "userToken": self.token,
        }

    def fetch_threads_posts(self, start: datetime, end: datetime) -> list[dict]:
        """Metricool has moved this endpoint's parameter spelling around more than
        once, so try the known shapes and keep the first that answers with rows."""
        attempts = [
            ("/v2/analytics/posts/threads",
             {"from": start.strftime("%Y%m%d"), "to": end.strftime("%Y%m%d")}),
            ("/v2/analytics/posts/threads",
             {"start": start.strftime("%Y%m%d"), "end": end.strftime("%Y%m%d")}),
            ("/v2/analytics/posts/threads",
             {"from": start.strftime("%Y-%m-%dT%H:%M:%S"),
              "to": end.strftime("%Y-%m-%dT%H:%M:%S")}),
            ("/stats/threads/posts",
             {"start": start.strftime("%Y%m%d"), "end": end.strftime("%Y%m%d")}),
        ]
        last_error = None
        for path, extra in attempts:
            params = {**self._auth_params(), **extra}
            url = METRICOOL_BASE + path
            try:
                r = self.session.get(url, params=params, timeout=60)
            except requests.RequestException as exc:
                last_error = f"{path} {extra} -> {exc}"
                continue
            if r.status_code != 200:
                last_error = f"{path} {extra} -> HTTP {r.status_code}: {r.text[:200]}"
                continue
            try:
                payload = r.json()
            except ValueError:
                last_error = f"{path} {extra} -> non-JSON body"
                continue
            rows = self._rows_from(payload)
            if rows:
                log(f"analytics: {path} with {sorted(extra)} returned {len(rows)} rows")
                return rows
            last_error = f"{path} {extra} -> 200 but no rows"
        raise RuntimeError(f"could not read Threads posts from Metricool. Last: {last_error}")

    @staticmethod
    def _rows_from(payload) -> list[dict]:
        if isinstance(payload, list):
            return [p for p in payload if isinstance(p, dict)]
        if isinstance(payload, dict):
            for key in ("data", "posts", "results", "items", "rows"):
                val = payload.get(key)
                if isinstance(val, list) and val and isinstance(val[0], dict):
                    return val
        return []

    def create_post(self, body: dict) -> dict:
        url = METRICOOL_BASE + "/v2/scheduler/posts"
        r = self.session.post(
            url,
            params=self._auth_params(),
            json=body,
            headers={"Content-Type": "application/json"},
            timeout=90,
        )
        if r.status_code >= 300:
            raise RuntimeError(f"Metricool rejected the post ({r.status_code}): {r.text[:600]}")
        try:
            return r.json()
        except ValueError:
            return {"raw": r.text}


def posts_from_rows(rows: list[dict]) -> list[Post]:
    """Metricool's post rows are not consistently keyed across accounts, so pull
    each field by the first key that exists."""
    def pick(row: dict, *names, default=None):
        for n in names:
            if n in row and row[n] not in (None, ""):
                return row[n]
        return default

    out = []
    for row in rows:
        text = str(pick(row, "text", "content", "message", "caption", default="") or "")
        if not text.strip():
            continue
        out.append(
            Post(
                text=text,
                url=str(pick(row, "url", "postUrl", "permalink", default="") or ""),
                published=_parse_when(pick(row, "published", "publishedAt", "date",
                                           "publicationDate", "creationDate", default="")),
                views=_num(pick(row, "views", "impressions", "reach")),
                likes=_num(pick(row, "likes", "likeCount")),
                replies=_num(pick(row, "replies", "comments", "replyCount")),
                reposts=_num(pick(row, "reposts", "repostCount", "retweets")),
                shares=_num(pick(row, "shares", "shareCount")),
            )
        )
    return out


# --------------------------------------------------------------------------- #
# selection
# --------------------------------------------------------------------------- #

def score_posts(posts: list[Post], now: datetime) -> list[Post]:
    for p in posts:
        base = p.views + p.interactions
        age_days = max((now - p.published).total_seconds() / 86400.0, 0.0)
        recency = 1.0 + 0.30 * math.exp(-age_days / 7.0)
        penalty = TEMPLATE_PENALTY if is_templated(p.text) else 1.0
        p.score = base * recency * penalty
        if penalty < 1.0:
            p.notes.append("templated")
    return posts


def select(posts: list[Post], want: int, min_slides: int, now: datetime) -> tuple[list[Post], str]:
    usable: list[Post] = []
    for p in posts:
        if is_vetoed(p.text):
            continue
        slide = clean_for_slide(p.text)
        if len(slide) < MIN_CHARS or len(slide) > MAX_CHARS:
            continue
        if not re.search(r"[a-zA-Z]", slide):
            continue
        p.slide_text = slide
        usable.append(p)

    if not usable:
        return [], "nothing survived the filters"

    score_posts(usable, now)

    # One slide per idea — the autolists repeat lines verbatim.
    best: dict[str, Post] = {}
    for p in sorted(usable, key=lambda x: x.score, reverse=True):
        key = normalize_key(p.text)
        if key and key not in best:
            best[key] = p
    deduped = sorted(best.values(), key=lambda x: x.score, reverse=True)

    # The bar: beat the median of the window, and clear an absolute floor. An
    # adaptive bar keeps a quiet fortnight from promoting weak posts.
    scores = sorted(p.score for p in deduped)
    median = scores[len(scores) // 2] if scores else 0.0
    bar = max(median, ABSOLUTE_VIEW_FLOOR)

    qualified = [p for p in deduped if p.score >= bar][:want]
    if len(qualified) < min_slides:
        return qualified, (
            f"only {len(qualified)} post(s) cleared the bar of {bar:.0f}; "
            f"{min_slides} required"
        )
    return qualified, ""


# --------------------------------------------------------------------------- #
# rendering
# --------------------------------------------------------------------------- #

def load_font(paths, size: int):
    for p in paths:
        if os.path.exists(p):
            try:
                return ImageFont.truetype(p, size)
            except OSError:
                continue
    return ImageFont.load_default(size)


def wrap_pixels(draw, text: str, font, max_w: int) -> list[str]:
    """Greedy wrap measured in pixels, not characters — character estimates
    overflow on wide glyphs and long numbers."""
    lines: list[str] = []
    for paragraph in text.split("\n"):
        words = paragraph.split()
        if not words:
            lines.append("")
            continue
        current = ""
        for word in words:
            trial = f"{current} {word}".strip()
            if draw.textlength(trial, font=font) <= max_w or not current:
                # A single word wider than the box gets hard-broken.
                if not current and draw.textlength(word, font=font) > max_w:
                    chunk = ""
                    for ch in word:
                        if draw.textlength(chunk + ch, font=font) > max_w and chunk:
                            lines.append(chunk)
                            chunk = ch
                        else:
                            chunk += ch
                    current = chunk
                else:
                    current = trial
            else:
                lines.append(current)
                current = word
        if current:
            lines.append(current)
    return lines


def fit_text(draw, text: str, font_paths, max_w: int, max_h: int,
             start: int, floor: int = 34):
    """Shrink until the wrapped block fits the text box."""
    size = start
    best = None
    while size >= floor:
        font = load_font(font_paths, size)
        lines = wrap_pixels(draw, text, font, max_w)
        line_h = int(size * 1.30)
        if len(lines) * line_h <= max_h:
            return font, lines, line_h
        best = (font, lines, line_h)
        size -= 3
    font = load_font(font_paths, floor)
    lines = wrap_pixels(draw, text, font, max_w)
    line_h = int(floor * 1.30)
    max_lines = max(int(max_h / line_h), 1)
    if len(lines) > max_lines:
        lines = lines[:max_lines]
        lines[-1] = lines[-1].rstrip(" .,;:") + "..."
    return font, lines, line_h


def draw_block(d, lines, font, line_h, box_top: int, box_h: int,
               x: int, fill, align: str = "center") -> int:
    """Paint a wrapped block inside a box and return the y just past it."""
    block_h = len(lines) * line_h
    if align == "center":
        y = box_top + max((box_h - block_h) // 2, 0)
    else:
        y = box_top
    for line in lines:
        d.text((x, y), line, font=font, fill=fill)
        y += line_h
    return y


def _base_slide(alt: bool = False) -> Image.Image:
    img = Image.new("RGB", (SLIDE_W, SLIDE_H), BG_ALT if alt else BG)
    d = ImageDraw.Draw(img)
    d.rectangle([0, 0, SLIDE_W, 10], fill=ACCENT)
    return img


def _footer(d: ImageDraw.ImageDraw, left: str, right: str) -> None:
    f = load_font(FONT_CANDIDATES_REGULAR, 30)
    y = SLIDE_H - MARGIN - 10
    d.text((MARGIN, y), left, font=f, fill=INK_SOFT)
    w = d.textlength(right, font=f)
    d.text((SLIDE_W - MARGIN - w, y), right, font=f, fill=INK_SOFT)


def render_cover(headline: str, kicker: str, total: int) -> Image.Image:
    img = _base_slide()
    d = ImageDraw.Draw(img)

    kf = load_font(FONT_CANDIDATES_BOLD, 34)
    d.text((MARGIN, MARGIN + 40), kicker.upper(), font=kf, fill=ACCENT)

    box_w = SLIDE_W - MARGIN * 2
    box_top, box_h = 280, 640
    font, lines, line_h = fit_text(d, headline, FONT_CANDIDATES_BOLD, box_w, box_h, 100, 52)
    y = draw_block(d, lines, font, line_h, box_top, box_h, MARGIN, INK)

    d.rectangle([MARGIN, y + 46, MARGIN + 140, y + 54], fill=ACCENT)
    sub = load_font(FONT_CANDIDATES_REGULAR, 40)
    d.text((MARGIN, y + 98), f"{total} of them. Swipe.", font=sub, fill=INK_SOFT)

    _footer(d, HANDLE, "")
    return img


def render_post(post: Post, index: int, total: int) -> Image.Image:
    img = _base_slide(alt=(index % 2 == 0))
    d = ImageDraw.Draw(img)

    nf = load_font(FONT_CANDIDATES_BOLD, 40)
    d.text((MARGIN, MARGIN + 40), f"{index:02d}", font=nf, fill=ACCENT)

    box_w = SLIDE_W - MARGIN * 2
    box_top, box_h = 260, 850
    font, lines, line_h = fit_text(d, post.slide_text, FONT_CANDIDATES_BOLD,
                                   box_w, box_h, 84, 40)
    draw_block(d, lines, font, line_h, box_top, box_h, MARGIN, INK)

    stat = f"{int(post.views):,} views on Threads" if post.views else "from Threads"
    _footer(d, stat, f"{index}/{total}")
    return img


def render_outro() -> Image.Image:
    img = _base_slide()
    d = ImageDraw.Draw(img)
    box_w = SLIDE_W - MARGIN * 2
    font, lines, line_h = fit_text(
        d, OUTRO_LINE, FONT_CANDIDATES_BOLD, box_w, 560, 88, 48)
    y = draw_block(d, lines, font, line_h, 300, 560, MARGIN, INK)
    d.rectangle([MARGIN, y + 50, MARGIN + 140, y + 58], fill=ACCENT)
    sub = load_font(FONT_CANDIDATES_REGULAR, 40)
    d.text((MARGIN, y + 100), f"Follow {HANDLE}", font=sub, fill=INK_SOFT)
    _footer(d, HANDLE, "")
    return img


def build_slides(posts: list[Post], out_dir: Path) -> list[Path]:
    out_dir.mkdir(parents=True, exist_ok=True)
    for old in out_dir.glob("slide-*.jpg"):
        old.unlink()

    images = [render_cover(COVER_HEADLINE, COVER_KICKER, len(posts))]
    for i, p in enumerate(posts, start=1):
        images.append(render_post(p, i, len(posts)))
    images.append(render_outro())

    paths = []
    for i, im in enumerate(images):
        path = out_dir / f"slide-{i:02d}.jpg"
        im.save(path, "JPEG", quality=92, optimize=True)
        paths.append(path)
    return paths


# --------------------------------------------------------------------------- #
# Cloudinary
# --------------------------------------------------------------------------- #

def cloudinary_upload(path: Path, cloud: str, key: str, secret: str, folder: str) -> str:
    timestamp = int(time.time())
    public_id = f"{path.stem}-{timestamp}"
    signed = {"folder": folder, "public_id": public_id, "timestamp": str(timestamp)}
    to_sign = "&".join(f"{k}={signed[k]}" for k in sorted(signed))
    signature = hashlib.sha1((to_sign + secret).encode("utf-8")).hexdigest()

    data = {**signed, "api_key": key, "signature": signature}
    with open(path, "rb") as fh:
        r = requests.post(
            f"{CLOUDINARY_BASE}/{cloud}/image/upload",
            data=data,
            files={"file": (path.name, fh, "image/jpeg")},
            timeout=120,
        )
    if r.status_code >= 300:
        raise RuntimeError(f"Cloudinary rejected {path.name} ({r.status_code}): {r.text[:400]}")
    url = r.json().get("secure_url")
    if not url:
        raise RuntimeError(f"Cloudinary gave no secure_url for {path.name}: {r.text[:400]}")
    return url


# --------------------------------------------------------------------------- #
# caption
# --------------------------------------------------------------------------- #

def build_caption(posts: list[Post]) -> tuple[str, str]:
    lead = posts[0].slide_text
    if len(lead) > 110:
        lead = lead[:107].rsplit(" ", 1)[0] + "..."
    title = lead[:88]
    body = f"{lead}\n\n{CAPTION_LINE.format(n=len(posts))}\n\n{HASHTAGS}"
    return title, body


# --------------------------------------------------------------------------- #
# main
# --------------------------------------------------------------------------- #

def env(name: str, required: bool = True) -> str:
    val = os.environ.get(name, "").strip()
    if required and not val:
        raise SystemExit(f"missing required environment variable: {name}")
    return val


def parse_args(argv=None):
    ap = argparse.ArgumentParser(description="Daily Threads carousel")
    ap.add_argument("--dry-run", action="store_true",
                    help="render slides only; upload nothing, schedule nothing")
    ap.add_argument("--no-publish", action="store_true",
                    help="upload and create the Metricool post as a draft")
    ap.add_argument("--lookback-days", type=int, default=DEFAULT_LOOKBACK_DAYS)
    ap.add_argument("--slides", type=int, default=DEFAULT_SLIDES,
                    help="maximum number of post slides (excludes cover and outro)")
    ap.add_argument("--min-slides", type=int, default=DEFAULT_MIN_SLIDES,
                    help="skip the day if fewer than this many posts clear the bar")
    ap.add_argument("--publish-at", default="18:00",
                    help="local HH:MM to schedule the carousel for")
    ap.add_argument("--out-dir", default="slides")
    ap.add_argument("--posts-json", default="",
                    help="read posts from a local JSON file instead of Metricool (testing)")
    return ap.parse_args(argv)


def scheduled_datetime(publish_at: str, now_local: datetime) -> datetime:
    try:
        hh, mm = (int(x) for x in publish_at.split(":", 1))
    except ValueError:
        hh, mm = 18, 0
    target = now_local.replace(hour=hh, minute=mm, second=0, microsecond=0)
    if target <= now_local + timedelta(minutes=10):
        target += timedelta(days=1)
    return target


def main(argv=None) -> int:
    args = parse_args(argv)
    out_dir = Path(args.out_dir)

    # GitHub Actions runners are UTC; everything user-facing is Pacific.
    now_utc = datetime.now(timezone.utc).replace(tzinfo=None)
    os.environ.setdefault("TZ", TIMEZONE_NAME)
    try:
        time.tzset()
    except AttributeError:
        pass
    now_local = datetime.now()

    if args.posts_json:
        rows = json.loads(Path(args.posts_json).read_text())
        if isinstance(rows, dict):
            rows = Metricool._rows_from(rows)
        posts = posts_from_rows(rows)
        mc = None
        log(f"loaded {len(posts)} posts from {args.posts_json}")
    else:
        mc = Metricool(env("METRICOOL_TOKEN"), env("METRICOOL_USER_ID"), env("METRICOOL_BLOG_ID"))
        start = now_utc - timedelta(days=args.lookback_days)
        rows = mc.fetch_threads_posts(start, now_utc + timedelta(days=1))
        posts = posts_from_rows(rows)
        log(f"pulled {len(posts)} Threads posts from the last {args.lookback_days} days")

    chosen, reason = select(posts, args.slides, args.min_slides, now_utc)
    if reason:
        log(f"skipping today — {reason}")
        return 0

    log(f"selected {len(chosen)} posts:")
    for i, p in enumerate(chosen, 1):
        tag = f" [{','.join(p.notes)}]" if p.notes else ""
        log(f"  {i}. score {p.score:>8.0f}  views {int(p.views):>5}{tag}  {p.slide_text[:70]}")

    paths = build_slides(chosen, out_dir)
    log(f"rendered {len(paths)} slides into {out_dir}/")

    if args.dry_run:
        log("dry run — nothing uploaded, nothing scheduled")
        return 0

    cloud = env("CLOUDINARY_CLOUD")
    key = env("CLOUDINARY_KEY")
    secret = env("CLOUDINARY_SECRET")
    folder = f"threads-carousel/{now_local.strftime('%Y-%m-%d')}"

    urls = []
    for p in paths:
        url = cloudinary_upload(p, cloud, key, secret, folder)
        log(f"uploaded {p.name}")
        urls.append(url)

    title, caption = build_caption(chosen)
    when = scheduled_datetime(args.publish_at, now_local)

    body = {
        "text": caption,
        "providers": [{"network": "tiktok"}],
        "publicationDate": {
            "dateTime": when.strftime("%Y-%m-%dT%H:%M:%S"),
            "timezone": TIMEZONE_NAME,
        },
        "draft": bool(args.no_publish),
        "autoPublish": True,
        "shortener": False,
        "media": urls,
        "mediaAltText": [],
        "tiktokData": {
            "title": title,
            "privacyOption": "PUBLIC_TO_EVERYONE",
            "disableComment": False,
            "disableDuet": False,
            "disableStitch": False,
            "commercialContentThirdParty": False,
            "commercialContentOwnBrand": False,
            "autoAddMusic": True,
            "photoCoverIndex": 0,
        },
    }

    if mc is None:
        log("no Metricool client (posts came from a file) — not scheduling")
        return 0

    result = mc.create_post(body)
    state = "draft" if args.no_publish else "scheduled"
    log(f"{state} for {when:%Y-%m-%d %H:%M} {TIMEZONE_NAME} — id {result.get('id', '?')}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except SystemExit:
        raise
    except Exception as exc:  # noqa: BLE001 - surface the reason in the run log
        log(f"FAILED: {exc}")
        sys.exit(1)

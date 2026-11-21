"""
FundEdge - USD macro-event dashboard for NAS100 and XAUUSD
===========================================================

The fundamental companion to StatEdge. It answers three questions before you
take a technical setup in your execution window:

  1. What US news is out today and this week, in Lagos time?
  2. Am I inside a news "Danger Zone" right now (30 min before/after a
     high-impact USD release)?
  3. After a top-tier release (CPI, NFP, GDP, FOMC), did the number come in
     hot or cool versus the forecast, and what bias does that imply?

Run it with:   streamlit run app.py

Data source
-----------
Forex Factory's public weekly export:
    https://nfs.faireconomy.media/ff_calendar_thisweek.xml

Three facts about that feed shape this code:
  * It carries NO "Actual" values - only forecast and previous. The parser
    still reads an <actual> tag if one ever appears, but in practice you type
    the actual number into the Impact Analyzer after the release.
  * Its <date>/<time> fields carry no time-zone label. Indicator code written
    for it treats the times as GMT. Instead of trusting either assumption, the
    app checks the clock from the data itself (US releases cluster at 8:30 and
    10:00 New York time) and shows you the evidence in the "Feed status" tab.
  * Forex Factory allows about 2 downloads per 5 minutes per file and updates
    the file roughly hourly. The app keeps the last good copy on disk and
    downloads at most once every 15 minutes.

Files the app writes (all inside ./data next to this file)
----------------------------------------------------------
  ff_calendar_thisweek.xml   last good copy of the feed
  ff_feed_meta.json          when the feed was last fetched / last error
  manual_actuals.json        actual numbers you typed into the Impact Analyzer

Testing switches (environment variables, normally unset)
--------------------------------------------------------
  FUNDEDGE_FEED_FILE   path to an XML file to use instead of the internet
  FUNDEDGE_FAKE_NOW    pretend the time is this ISO timestamp,
                       e.g. 2026-11-18T14:15:00+01:00
"""

from __future__ import annotations

import html
import json
import os
import re
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from datetime import date, datetime, timedelta
from decimal import Decimal, InvalidOperation
from pathlib import Path

import pytz
import requests
import streamlit as st

# =============================================================================
# 0. SETTINGS - everything you might want to tweak lives here
# =============================================================================

FEED_URL = "https://nfs.faireconomy.media/ff_calendar_thisweek.xml"

APP_DIR = Path(__file__).resolve().parent
DATA_DIR = APP_DIR / "data"
FEED_CACHE = DATA_DIR / "ff_calendar_thisweek.xml"
FEED_META = DATA_DIR / "ff_feed_meta.json"
MANUAL_ACTUALS = DATA_DIR / "manual_actuals.json"

REFRESH_EVERY_S = 15 * 60   # normal re-download interval (feed changes ~hourly)
MIN_GAP_S = 150             # hard floor between downloads: stays under 2 per 5 min
HTTP_TIMEOUT = (10, 20)     # (connect, read) seconds
HTTP_HEADERS = {
    "User-Agent": "FundEdge/1.0 (personal macro dashboard; polite 15-min cache)",
    "Accept": "application/xml,text/xml;q=0.9,*/*;q=0.5",
}

# Time zones (pytz handles US daylight-saving switches automatically).
LAGOS = pytz.timezone("Africa/Lagos")         # WAT = UTC+1 all year, no DST
NEW_YORK = pytz.timezone("America/New_York")  # EST (UTC-5) / EDT (UTC-4)
UTC = pytz.utc

CURRENCY = "USD"            # NAS100 and XAUUSD are both priced off USD news
DANGER_MINUTES = 30         # blackout before AND after each high-impact release

# Your execution window. Two ways to define it (switch in the sidebar):
#   "ny"    - 9:30-11:00 New York time. Equals 3:30-5:00 PM WAT while the US
#             is on winter time (EST), and 2:30-4:00 PM WAT from 14 Mar 2027
#             when the US moves to EDT. Follows the real NY open.
#   "lagos" - fixed 3:30-5:00 PM WAT all year, exactly as you specified.
EXEC_WINDOW_NY = ((9, 30), (11, 0))
EXEC_WINDOW_LAGOS = ((15, 30), (17, 0))

IMPACT_ORDER = ["High", "Medium", "Low", "Holiday"]
IMPACT_STYLE = {
    #           badge bg    badge text  label
    "High":    ("#e5484d", "#ffffff", "HIGH"),
    "Medium":  ("#f76b15", "#ffffff", "MED"),
    "Low":     ("#ffd60a", "#111111", "LOW"),
    "Holiday": ("#6b7280", "#ffffff", "HOLIDAY"),
}

# -----------------------------------------------------------------------------
# Top-tier events for the Impact Analyzer.
# Each rule: (release family, regex matched against the Forex Factory title,
#             direction).
# direction +1 : a number ABOVE forecast is "hot" (USD-positive)
# direction -1 : a number ABOVE forecast is "cool" (e.g. unemployment rate)
# direction  0 : qualitative event, no number to compare (statement, presser)
# Add PPI / PCE here later if you want them scored too.
# -----------------------------------------------------------------------------
TOP_TIER_RULES = [
    ("CPI",  r"^(core )?cpi (m/m|y/y)$", +1),
    ("NFP",  r"^non-?farm (employment change|payrolls)$", +1),
    ("NFP",  r"^unemployment rate$", -1),
    ("NFP",  r"^average hourly earnings m/m$", +1),
    ("GDP",  r"^((advance|prelim|preliminary|final|second|third) )?gdp q/q$", +1),
    ("GDP",  r"^((advance|prelim|preliminary|final|second|third) )?gdp price index q/q$", +1),
    ("FOMC", r"^federal funds rate$", +1),
    ("FOMC", r"^fomc (statement|press conference|economic projections)$", 0),
]
FAMILY_NAMES = {
    "CPI": "US CPI (inflation)",
    "NFP": "US Jobs report (NFP)",
    "GDP": "US GDP",
    "FOMC": "FOMC rate decision",
}

# The two bias messages, word for word as specified.
HOT_TEXT = ("MACRO BIAS: USD STRENGTH EXPECTED. Inflation/Economy is running hot. "
            "Expect bearish pressure on XAUUSD and NAS100.")
COOL_TEXT = ("MACRO BIAS: USD WEAKNESS EXPECTED. Economy is cooling. "
             "Expect bullish pressure on XAUUSD and NAS100.")
DANGER_TEXT = ("⚠️ DANGER ZONE: High-Impact US News Approaching. Do not execute "
               "technical setups 30 minutes before or after this release. "
               "Let algorithmic manipulation finish.")

# Normal US release times in New York clock. Used only to work out which
# clock the feed is written in (see detect_feed_clock).
US_RELEASE_SLOTS_ET = {(8, 15), (8, 30), (9, 45), (10, 0), (10, 30), (11, 0),
                       (13, 0), (14, 0), (14, 30), (15, 0)}
FEED_CLOCKS = {
    "UTC": "GMT / UTC+0",
    "America/New_York": "US Eastern (EST/EDT)",
}


# =============================================================================
# 1. CLOCK
# =============================================================================

def now_utc() -> datetime:
    """Current time in UTC. FUNDEDGE_FAKE_NOW lets you test any moment."""
    fake = os.environ.get("FUNDEDGE_FAKE_NOW", "").strip()
    if fake:
        dt = datetime.fromisoformat(fake)
        if dt.tzinfo is None:
            raise ValueError("FUNDEDGE_FAKE_NOW needs a UTC offset, e.g. +01:00")
        return dt.astimezone(UTC)
    return datetime.now(UTC)


def fmt_clock(dt: datetime) -> str:
    """'2:30 PM' style, without a leading zero (works on Windows and Linux)."""
    return dt.strftime("%I:%M %p").lstrip("0")


def fmt_delta(seconds: float) -> str:
    """Human countdown: '2h 05m', '12 min', '3d 4h'."""
    s = int(abs(seconds))
    days, rem = divmod(s, 86400)
    hours, rem = divmod(rem, 3600)
    mins = rem // 60
    if days:
        return f"{days}d {hours}h"
    if hours:
        return f"{hours}h {mins:02d}m"
    return f"{mins} min"


# =============================================================================
# 2. FEED DOWNLOAD - polite, cached on disk, survives rate limits and outages
# =============================================================================

def _read_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return default


def _write_atomic(path: Path, data: bytes) -> None:
    """Write to a temp file, then swap it in, so a crash never leaves half a file."""
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_bytes(data)
    os.replace(tmp, path)


def _looks_like_feed(raw: bytes) -> bool:
    """True if the bytes are the calendar XML (not an HTML 'Request Denied' page)."""
    head = raw[:4000].lower()
    return b"<weeklyevents" in head or (b"<event>" in head and b"<html" not in head)


def get_feed(force: bool = False) -> tuple[bytes | None, dict]:
    """
    Return (xml_bytes, status).

    Rules:
      * use the disk copy if it is younger than REFRESH_EVERY_S;
      * otherwise download, but never twice within MIN_GAP_S;
      * if the download fails or Forex Factory rate-limits us, fall back to the
        last good copy and say so in status["message"].
    """
    # Testing / offline switch: read a local file and never touch the network.
    test_file = os.environ.get("FUNDEDGE_FEED_FILE", "").strip()
    if test_file:
        raw = Path(test_file).read_bytes()
        return raw, {"source": "file", "message": f"Loaded from local file {test_file}",
                     "fetched_at": None, "stale": False}

    meta = _read_json(FEED_META, {})
    cached = FEED_CACHE.read_bytes() if FEED_CACHE.exists() else None
    t = time.time()
    last_ok = float(meta.get("last_success_epoch", 0))
    last_try = float(meta.get("last_attempt_epoch", 0))
    fetched_at = datetime.fromtimestamp(last_ok, UTC) if last_ok else None

    due = cached is None or force or (t - last_ok) >= REFRESH_EVERY_S
    if not due:
        return cached, {"source": "cache", "fetched_at": fetched_at, "stale": False,
                        "message": "Using the copy downloaded "
                                   f"{fmt_delta(t - last_ok)} ago (refreshes every 15 min)."}

    if (t - last_try) < MIN_GAP_S:
        wait = MIN_GAP_S - (t - last_try)
        msg = (f"Download paused for {int(wait)} s to respect Forex Factory's limit "
               "(about 2 downloads per 5 minutes).")
        return cached, {"source": "cache" if cached else "none", "fetched_at": fetched_at,
                        "stale": cached is not None and (t - last_ok) >= REFRESH_EVERY_S,
                        "message": msg}

    meta["last_attempt_epoch"] = t
    reason = ""
    try:
        r = requests.get(FEED_URL, headers=HTTP_HEADERS, timeout=HTTP_TIMEOUT)
        body = r.content
        if r.status_code == 200 and _looks_like_feed(body):
            parse_feed(body)                      # refuse to cache a broken file
            _write_atomic(FEED_CACHE, body)
            meta.update(last_success_epoch=t, last_error="")
            _write_atomic(FEED_META, json.dumps(meta).encode())
            return body, {"source": "live", "fetched_at": datetime.fromtimestamp(t, UTC),
                          "stale": False, "message": "Downloaded just now from Forex Factory."}
        if b"request denied" in body.lower() or r.status_code == 429:
            reason = "Forex Factory rate limit hit ('Request Denied')"
        else:
            reason = f"unexpected reply (HTTP {r.status_code})"
    except requests.RequestException as exc:
        reason = f"network error ({exc.__class__.__name__})"
    except FeedError as exc:
        reason = f"downloaded file could not be read ({exc})"

    meta["last_error"] = reason
    _write_atomic(FEED_META, json.dumps(meta).encode())
    if cached is not None:
        return cached, {"source": "cache", "fetched_at": fetched_at, "stale": True,
                        "message": f"Live download failed: {reason}. Showing the last good "
                                   f"copy from {fmt_delta(t - last_ok)} ago."}
    return None, {"source": "none", "fetched_at": None, "stale": True,
                  "message": f"Live download failed: {reason}. No saved copy yet."}


# =============================================================================
# 3. PARSING THE XML
# =============================================================================

class FeedError(Exception):
    """The feed could not be read as calendar XML."""


@dataclass
class Event:
    key: str                 # stable id: date|country|title (used for saved actuals)
    title: str
    country: str
    impact: str              # High / Medium / Low / Holiday
    date_raw: str            # exactly as in the feed, e.g. 11-18-2026
    time_raw: str            # exactly as in the feed, e.g. 1:30pm / All Day / Tentative
    forecast: str
    previous: str
    actual_feed: str         # empty in today's feed; kept in case FF adds it
    url: str
    feed_date: date | None
    naive: datetime | None   # date + time in the feed's own clock (no zone yet)
    utc: datetime | None = None
    lagos: datetime | None = None
    ny: datetime | None = None

    @property
    def timed(self) -> bool:
        return self.lagos is not None

    @property
    def lagos_date(self) -> date | None:
        return self.lagos.date() if self.lagos else self.feed_date


_CLOCK_RE = re.compile(r"^\s*(\d{1,2}):(\d{2})\s*([ap]m)\s*$", re.I)


def parse_clock(text: str) -> tuple[int, int] | None:
    """'8:30am' -> (8, 30); '12:00pm' -> (12, 0); 'All Day'/'Tentative' -> None."""
    m = _CLOCK_RE.match(text or "")
    if not m:
        return None
    hour, minute, ampm = int(m.group(1)), int(m.group(2)), m.group(3).lower()
    if not (1 <= hour <= 12 and 0 <= minute <= 59):
        return None
    hour = hour % 12 + (12 if ampm == "pm" else 0)
    return hour, minute


def parse_date(text: str) -> date | None:
    for fmt in ("%m-%d-%Y", "%Y-%m-%d", "%m/%d/%Y"):
        try:
            return datetime.strptime((text or "").strip(), fmt).date()
        except ValueError:
            continue
    return None


def _xml_root(raw: bytes) -> ET.Element:
    """Parse bytes; if that fails, decode leniently and retry once."""
    try:
        return ET.fromstring(raw)
    except ET.ParseError:
        pass
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError:
        text = raw.decode("cp1252", errors="replace")
    text = re.sub(r"^\s*<\?xml[^>]*\?>", "", text)
    text = re.sub(r"&(?!(amp|lt|gt|quot|apos|#\d+|#x[0-9a-fA-F]+);)", "&amp;", text)
    try:
        return ET.fromstring(text)
    except ET.ParseError as exc:
        raise FeedError(f"not valid XML: {exc}") from exc


def parse_feed(raw: bytes) -> list[Event]:
    """Turn the feed bytes into Event objects (all currencies, no time zone yet)."""
    if not raw or not _looks_like_feed(raw):
        raise FeedError("this is not the Forex Factory calendar XML")
    root = _xml_root(raw)
    events: list[Event] = []
    for node in root.iter("event"):
        def field(tag: str) -> str:
            return (node.findtext(tag) or "").strip()

        title, country = field("title"), field("country").upper()
        date_raw, time_raw = field("date"), field("time")
        d = parse_date(date_raw)
        clock = parse_clock(time_raw)
        naive = datetime(d.year, d.month, d.day, *clock) if (d and clock) else None
        impact = field("impact").capitalize() or "Low"
        if impact not in IMPACT_STYLE:
            impact = "Low"
        events.append(Event(
            key=f"{date_raw}|{country}|{title}",
            title=title, country=country, impact=impact,
            date_raw=date_raw, time_raw=time_raw,
            forecast=field("forecast"), previous=field("previous"),
            actual_feed=field("actual"), url=field("url"),
            feed_date=d, naive=naive,
        ))
    if not events:
        raise FeedError("the file contains no <event> entries")
    return events


# =============================================================================
# 4. TIME ZONES - find the feed's clock, then convert to Lagos
# =============================================================================

def _localize(naive: datetime, tz_name: str) -> datetime:
    tz = pytz.timezone(tz_name)
    return tz.localize(naive)          # pytz picks the correct EST/EDT offset


def detect_feed_clock(events: list[Event]) -> dict:
    """
    Decide whether the feed's times are GMT or US Eastern, using the data.

    US data comes out at fixed New York times (8:30, 10:00, 14:00 ...).
    For each candidate clock we convert every timed USD event to New York time
    and count how many land on one of those standard slots. The right clock
    scores high; a clock that is 4-5 hours off scores near zero.
    """
    usd = [e for e in events if e.country == CURRENCY and e.naive is not None]
    scores = {}
    for tz_name in FEED_CLOCKS:
        hits = 0
        for e in usd:
            ny = _localize(e.naive, tz_name).astimezone(NEW_YORK)
            hits += (ny.hour, ny.minute) in US_RELEASE_SLOTS_ET
        scores[tz_name] = hits
    total = len(usd)
    best = max(scores, key=scores.get) if total else "UTC"
    ranked = sorted(scores.values(), reverse=True)
    if total == 0 or ranked[0] == ranked[-1]:
        best, confidence = "UTC", "low"   # no evidence either way: GMT is the documented norm
    elif ranked[0] >= 0.5 * total and ranked[0] >= 3 * max(ranked[-1], 1):
        confidence = "high"
    else:
        confidence = "medium"
    return {"clock": best, "scores": scores, "total": total, "confidence": confidence}


def apply_clock(events: list[Event], tz_name: str) -> list[Event]:
    """Fill utc / lagos / ny on every timed event using the chosen feed clock."""
    for e in events:
        if e.naive is None:
            e.utc = e.lagos = e.ny = None
            continue
        e.utc = _localize(e.naive, tz_name).astimezone(UTC)
        e.lagos = e.utc.astimezone(LAGOS)
        e.ny = e.utc.astimezone(NEW_YORK)
    return events


def exec_window(day: date, anchor: str) -> tuple[datetime, datetime]:
    """Your execution window on a given Lagos date, as Lagos datetimes."""
    if anchor == "ny":
        (h1, m1), (h2, m2) = EXEC_WINDOW_NY
        start = NEW_YORK.localize(datetime(day.year, day.month, day.day, h1, m1))
        end = NEW_YORK.localize(datetime(day.year, day.month, day.day, h2, m2))
        return start.astimezone(LAGOS), end.astimezone(LAGOS)
    (h1, m1), (h2, m2) = EXEC_WINDOW_LAGOS
    return (LAGOS.localize(datetime(day.year, day.month, day.day, h1, m1)),
            LAGOS.localize(datetime(day.year, day.month, day.day, h2, m2)))


# =============================================================================
# 5. DANGER ZONE LOGIC
# =============================================================================

def danger_events(events: list[Event], now: datetime,
                  minutes: int = DANGER_MINUTES) -> list[tuple[Event, float]]:
    """
    High-impact USD events whose release is within +/- `minutes` of now.
    Returns (event, seconds_until_release); negative = already released.
    """
    out = []
    for e in events:
        if e.country == CURRENCY and e.impact == "High" and e.timed:
            delta = (e.utc - now).total_seconds()
            if abs(delta) <= minutes * 60:
                out.append((e, delta))
    return sorted(out, key=lambda x: x[1])


def tentative_high_today(events: list[Event], today: date) -> list[Event]:
    """High-impact USD events today with no fixed time ('Tentative', 'All Day')."""
    return [e for e in events if e.country == CURRENCY and e.impact == "High"
            and not e.timed and e.lagos_date == today]


def next_high_event(events: list[Event], now: datetime) -> Event | None:
    future = [e for e in events if e.country == CURRENCY and e.impact == "High"
              and e.timed and e.utc > now]
    return min(future, key=lambda e: e.utc) if future else None


def blackouts_in_window(events: list[Event], day: date, anchor: str):
    """For each high-impact USD release on `day`: its blackout and window overlap."""
    w0, w1 = exec_window(day, anchor)
    rows = []
    for e in events:
        if e.country == CURRENCY and e.impact == "High" and e.timed and e.lagos_date == day:
            b0 = e.lagos - timedelta(minutes=DANGER_MINUTES)
            b1 = e.lagos + timedelta(minutes=DANGER_MINUTES)
            o0, o1 = max(b0, w0), min(b1, w1)
            rows.append({"event": e, "start": b0, "end": b1,
                         "overlap": (o0, o1) if o0 < o1 else None})
    return rows


# =============================================================================
# 6. IMPACT ANALYZER LOGIC
# =============================================================================

_VALUE_RE = re.compile(r"^([<>]?)([+-]?\d+(?:\.\d+)?)(%|[KMBT])?$", re.I)


def parse_value(text: str) -> tuple[Decimal, str] | None:
    """'0.3%' -> (0.3, '%'), '-12K' -> (-12, 'K'), '4.25' -> (4.25, ''). Else None."""
    s = (text or "").strip().replace(",", "").replace(" ", "").replace("−", "-")
    m = _VALUE_RE.match(s)
    if not m:
        return None
    try:
        return Decimal(m.group(2)), (m.group(3) or "").upper()
    except InvalidOperation:
        return None


def classify_title(title: str) -> tuple[str, int] | None:
    """Return (family, direction) if the title is a top-tier event, else None."""
    t = title.strip().lower()
    for family, pattern, direction in TOP_TIER_RULES:
        if re.match(pattern, t):
            return family, direction
    return None


def looks_implausible(actual: str, forecast: str, previous: str) -> bool:
    """
    Typo guard: True when the typed actual is more than 3x the size of both the
    forecast and the previous reading away from the forecast - e.g. 2.7% typed
    into 'Core CPI m/m' (forecast 0.3%) because the y/y number was copied.
    It only warns; big genuine surprises still count.
    """
    a, f = parse_value(actual), parse_value(forecast)
    if not a or not f or a[1] != f[1]:
        return False
    p = parse_value(previous)
    scale = max(abs(f[0]), abs(p[0]) if p and p[1] == f[1] else Decimal(0), Decimal("0.1"))
    return abs(a[0] - f[0]) > 3 * scale


def score_component(actual: str, forecast: str, direction: int) -> dict:
    """
    Compare one release with its forecast.

    status: PENDING (no actual yet) | QUALITATIVE | NO_FORECAST | BAD_ACTUAL |
            UNIT_MISMATCH | HOT | COOL | INLINE
    HOT/COOL already include the direction, e.g. unemployment above forecast = COOL.
    """
    if direction == 0:
        return {"status": "QUALITATIVE", "surprise": ""}
    if not (actual or "").strip():
        return {"status": "PENDING", "surprise": ""}
    a = parse_value(actual)
    if a is None:
        return {"status": "BAD_ACTUAL", "surprise": ""}
    f = parse_value(forecast)
    if f is None:
        return {"status": "NO_FORECAST", "surprise": ""}
    if a[1] != f[1]:
        return {"status": "UNIT_MISMATCH",
                "surprise": f"actual unit '{a[1] or 'none'}' vs forecast unit '{f[1] or 'none'}'"}
    diff = a[0] - f[0]
    unit = {"%": " pp", "": ""}.get(a[1], a[1])          # pp = percentage points
    surprise = (f"{diff.normalize():+f}" + unit) if diff else "0"
    if diff == 0:
        return {"status": "INLINE", "surprise": surprise}
    hot = (diff > 0) == (direction > 0)
    return {"status": "HOT" if hot else "COOL", "surprise": surprise}


def group_verdict(statuses: list[str]) -> str:
    """Combine the components of one release into one reading."""
    scored = [s for s in statuses if s in ("HOT", "COOL", "INLINE")]
    if not scored:
        if "PENDING" in statuses:
            return "PENDING"
        if statuses and all(s == "QUALITATIVE" for s in statuses):
            return "QUALITATIVE"
        return "NO_DATA"
    net = scored.count("HOT") - scored.count("COOL")
    if net > 0:
        return "HOT"
    if net < 0:
        return "COOL"
    return "INLINE" if all(s == "INLINE" for s in scored) else "MIXED"


def load_manual_actuals() -> dict:
    return _read_json(MANUAL_ACTUALS, {})


def save_manual_actual(key: str, value: str) -> None:
    data = load_manual_actuals()
    if value.strip():
        data[key] = {"actual": value.strip(), "saved_utc": now_utc().isoformat()}
    else:
        data.pop(key, None)
    _write_atomic(MANUAL_ACTUALS, json.dumps(data, indent=1).encode())


def actual_for(e: Event, manual: dict) -> tuple[str, str]:
    """(actual, source): feed actual wins; otherwise your typed number."""
    if e.actual_feed:
        return e.actual_feed, "feed"
    if e.key in manual:
        return manual[e.key]["actual"], "manual"
    return "", ""


def top_tier_groups(events: list[Event]) -> list[dict]:
    """Group this week's top-tier USD events into releases (family + Lagos date)."""
    groups: dict[tuple, dict] = {}
    for e in events:
        if e.country != CURRENCY:
            continue
        hit = classify_title(e.title)
        if not hit:
            continue
        family, direction = hit
        gkey = (family, e.lagos_date)
        g = groups.setdefault(gkey, {"family": family, "day": e.lagos_date, "items": []})
        g["items"].append((e, direction))
    out = list(groups.values())
    for g in out:
        # by release time; ties keep the feed's own order, which is the order
        # Forex Factory's website lists them in (easier to copy numbers row by row)
        g["items"].sort(key=lambda x: x[0].utc or datetime.max.replace(tzinfo=UTC))
        times = [e.utc for e, _ in g["items"] if e.utc]
        g["first_utc"] = min(times) if times else None
    out.sort(key=lambda g: (g["day"] or date.max, g["family"]))
    return out


# =============================================================================
# 7. HTML / CSS helpers (all feed text is escaped before display)
# =============================================================================

CSS = """
<style>
.block-container{padding-top:1.4rem;}
@keyframes feFlash{0%,100%{background:#8b0016;box-shadow:0 0 0 0 rgba(255,23,68,.0);}
50%{background:#ff1744;box-shadow:0 0 28px 6px rgba(255,23,68,.65);}}
.fe-danger{animation:feFlash 1s ease-in-out infinite;color:#fff;border:3px solid #fff;
border-radius:14px;padding:22px 26px;margin:6px 0 14px 0;}
.fe-danger .big{font-size:1.65rem;font-weight:800;line-height:1.25;}
.fe-danger .sub{font-size:1.05rem;margin-top:10px;font-weight:600;}
@media (prefers-reduced-motion: reduce){.fe-danger{animation:none;background:#d50000;}}
.fe-caution{background:#3a2a00;border:2px solid #ffb300;color:#ffe08a;border-radius:12px;
padding:12px 16px;margin:6px 0 12px 0;font-weight:600;}
.fe-clear{background:#0f2a1c;border:1px solid #1f7a4d;color:#b7f5d3;border-radius:12px;
padding:12px 16px;margin:6px 0 12px 0;}
.fe-strip{display:flex;gap:12px;flex-wrap:wrap;margin:4px 0 8px 0;}
.fe-tile{background:#151a23;border:1px solid #2a3140;border-radius:10px;padding:10px 14px;min-width:170px;}
.fe-tile .k{font-size:.75rem;color:#9aa4b2;text-transform:uppercase;letter-spacing:.04em;}
.fe-tile .v{font-size:1.15rem;font-weight:700;color:#e8ecf2;}
.fe-tile .s{font-size:.8rem;color:#9aa4b2;}
table.fe{width:100%;table-layout:fixed;border-collapse:collapse;font-size:.92rem;margin-bottom:10px;}
table.fe th{color:#9aa4b2;text-align:left;font-weight:600;border-bottom:1px solid #2a3140;padding:6px 8px;}
table.fe td{border-bottom:1px solid #1d2330;padding:7px 8px;vertical-align:middle;}
table.fe tr.high td{background:rgba(229,72,77,.10);}
table.fe tr.high td:first-child{border-left:4px solid #e5484d;}
table.fe tr.past td{opacity:.55;}
table.fe tr.high.past td{opacity:.8;}
.fe-badge{display:inline-block;border-radius:6px;padding:2px 8px;font-size:.72rem;font-weight:800;letter-spacing:.04em;}
.fe-title-high{font-weight:700;color:#ffd7d8;}
.fe-muted{color:#8b95a5;font-size:.8rem;}
.fe-day{font-size:1.05rem;font-weight:700;margin:14px 0 4px 0;color:#e8ecf2;}
.fe-bias{border-radius:12px;padding:16px 18px;margin:8px 0 6px 0;font-weight:800;font-size:1.08rem;line-height:1.35;}
.fe-bias.hot{background:#3b0d12;border:2px solid #e5484d;color:#ffd7d8;}
.fe-bias.cool{background:#0b2e1f;border:2px solid #2fbf71;color:#c6f6dc;}
.fe-bias.inline{background:#1d2330;border:2px solid #6b7280;color:#d6dbe3;}
.fe-bias.mixed{background:#33260a;border:2px solid #ffb300;color:#ffe08a;}
.fe-bias.pending{background:#151a23;border:2px dashed #4b5563;color:#9aa4b2;font-weight:600;}
.fe-tl{position:relative;height:58px;background:#151a23;border:1px solid #2a3140;border-radius:10px;margin:6px 0 4px 0;overflow:hidden;}
.fe-tl .win{position:absolute;top:0;bottom:0;background:rgba(47,191,113,.22);border-left:2px solid #2fbf71;border-right:2px solid #2fbf71;}
.fe-tl .blk{position:absolute;top:0;bottom:0;background:repeating-linear-gradient(45deg,rgba(229,72,77,.55) 0 6px,rgba(229,72,77,.30) 6px 12px);}
.fe-tl .now{position:absolute;top:0;bottom:0;width:2px;background:#fff;}
.fe-tl .tick{position:absolute;bottom:2px;font-size:.68rem;color:#9aa4b2;white-space:nowrap;transform:translateX(-50%);}
</style>
"""


def esc(x) -> str:
    return html.escape(str(x if x is not None else ""))


def badge(impact: str) -> str:
    bg, fg, label = IMPACT_STYLE.get(impact, IMPACT_STYLE["Low"])
    return f'<span class="fe-badge" style="background:{bg};color:{fg}">{label}</span>'


def safe_link(url: str, text: str, cls: str = "") -> str:
    """Link only to http(s) addresses; anything else is shown as plain text."""
    cls_attr = f' class="{cls}"' if cls else ""
    if url.startswith(("https://", "http://")):
        return (f'<a href="{esc(url)}" target="_blank" rel="noopener noreferrer"'
                f'{cls_attr} style="color:inherit;text-decoration:none">{esc(text)}</a>')
    return f"<span{cls_attr}>{esc(text)}</span>"


def events_table(rows: list[Event], now: datetime, manual: dict) -> str:
    """One HTML table of events; high-impact rows are highlighted red."""
    cols = "".join(f"<col style='width:{w}%'>" for w in (10, 10, 8, 33, 10, 9, 9, 11))
    head = ("<table class='fe'><colgroup>" + cols + "</colgroup><tr><th>WAT (Lagos)</th><th>New York</th><th>Impact</th>"
            "<th>Event</th><th>Actual</th><th>Forecast</th><th>Previous</th><th>Status</th></tr>")
    body = []
    for e in rows:
        is_past = e.timed and e.utc <= now
        cls = " ".join(c for c in (e.impact.lower() if e.impact == "High" else "",
                                   "past" if is_past else "") if c)
        wat = fmt_clock(e.lagos) if e.timed else esc(e.time_raw or "—")
        ny = (fmt_clock(e.ny) + " ET") if e.timed else ""
        actual, src = actual_for(e, manual)
        if actual:
            act_cell = esc(actual) + (" <span class='fe-muted'>(typed)</span>" if src == "manual" else "")
        else:
            act_cell = "<span class='fe-muted'>—</span>"
        if e.timed:
            secs = (e.utc - now).total_seconds()
            status = (f"in {fmt_delta(secs)}" if secs > 0 else
                      ("released" if actual else "released · no actual in feed"))
        else:
            status = esc(e.time_raw or "time not set")
        title_cls = "fe-title-high" if e.impact == "High" else ""
        body.append(
            f"<tr class='{cls}'><td><b>{wat}</b></td><td class='fe-muted'>{ny}</td>"
            f"<td>{badge(e.impact)}</td><td>{safe_link(e.url, e.title, title_cls)}</td>"
            f"<td>{act_cell}</td><td>{esc(e.forecast) or '—'}</td><td>{esc(e.previous) or '—'}</td>"
            f"<td class='fe-muted'>{status}</td></tr>")
    return head + "".join(body) + "</table>"


def sort_key(e: Event):
    return (e.lagos_date or date.max, 0 if e.timed else 1,
            e.utc or datetime.max.replace(tzinfo=UTC), IMPACT_ORDER.index(e.impact))


def timeline_html(day: date, events: list[Event], now: datetime, anchor: str) -> str:
    """A day bar in Lagos time: green = execution window, red stripes = blackouts."""
    rows = blackouts_in_window(events, day, anchor)
    w0, w1 = exec_window(day, anchor)
    start_h, end_h = 12, 22
    for r in rows:
        start_h = min(start_h, r["start"].hour)
        end_h = max(end_h, min(24, r["end"].hour + 1))
    t0 = LAGOS.localize(datetime(day.year, day.month, day.day, start_h))
    span = (end_h - start_h) * 3600

    def pct(dt: datetime) -> float:
        return max(0.0, min(100.0, (dt - t0).total_seconds() / span * 100))

    parts = [f"<div class='fe-tl'><div class='win' style='left:{pct(w0):.2f}%;"
             f"width:{pct(w1) - pct(w0):.2f}%'></div>"]
    for r in rows:
        parts.append(f"<div class='blk' title='{esc(r['event'].title)}' style='left:{pct(r['start']):.2f}%;"
                     f"width:{pct(r['end']) - pct(r['start']):.2f}%'></div>")
    if now.astimezone(LAGOS).date() == day:
        parts.append(f"<div class='now' style='left:{pct(now.astimezone(LAGOS)):.2f}%'></div>")
    for h in range(start_h, end_h + 1, 2):
        lab = datetime(2000, 1, 1, h % 24).strftime("%I %p").lstrip("0")
        shift = "0" if h == start_h else ("-100%" if h >= end_h - 1 else "-50%")  # keep edge labels inside
        parts.append(f"<div class='tick' style='left:{(h - start_h) * 3600 / span * 100:.2f}%;"
                     f"transform:translateX({shift});padding:0 4px'>{lab}</div>")
    parts.append("</div>")
    return "".join(parts)


# =============================================================================
# 8. STREAMLIT PAGE SECTIONS
# =============================================================================

@st.fragment(run_every="30s")
def live_header(events: list[Event], anchor: str) -> None:
    """Clock tiles + Danger Zone banner. Re-runs by itself every 30 seconds."""
    now = now_utc()
    lagos_now = now.astimezone(LAGOS)
    today = lagos_now.date()
    w0, w1 = exec_window(today, anchor)

    if lagos_now < w0:
        win_state, win_sub = "Not open yet", f"opens in {fmt_delta((w0 - lagos_now).total_seconds())}"
    elif lagos_now <= w1:
        win_state, win_sub = "OPEN", f"closes in {fmt_delta((w1 - lagos_now).total_seconds())}"
    else:
        win_state, win_sub = "Closed for today", "reopens next trading day"
    if today.weekday() >= 5:
        win_state, win_sub = "Weekend", "US markets closed"

    nxt = next_high_event(events, now)
    nxt_v = (f"{fmt_clock(nxt.lagos)} WAT {nxt.lagos.strftime('%a')}" if nxt else "None left this week")
    nxt_s = (f"{esc(nxt.title)} · in {fmt_delta((nxt.utc - now).total_seconds())}" if nxt else "")

    tiles = [
        ("Lagos time (WAT)", lagos_now.strftime("%a %d %b · ") + fmt_clock(lagos_now), "Africa/Lagos, UTC+1"),
        ("New York time", fmt_clock(now.astimezone(NEW_YORK)) + " " + now.astimezone(NEW_YORK).tzname(),
         "the clock US data is released on"),
        ("Execution window", f"{fmt_clock(w0)} – {fmt_clock(w1)} WAT", f"{win_state} · {win_sub}"),
        ("Next high-impact USD", nxt_v, nxt_s),
    ]
    st.markdown("<div class='fe-strip'>" + "".join(
        f"<div class='fe-tile'><div class='k'>{esc(k)}</div><div class='v'>{esc(v)}</div>"
        f"<div class='s'>{s if k.startswith('Next') else esc(s)}</div></div>"
        for k, v, s in tiles) + "</div>", unsafe_allow_html=True)

    hits = danger_events(events, now)
    if hits:
        lines = []
        for e, secs in hits:
            when = (f"releases in {fmt_delta(secs)}" if secs > 0 else
                    ("releasing now" if secs > -60 else f"released {fmt_delta(secs)} ago"))
            clear_at = e.lagos + timedelta(minutes=DANGER_MINUTES)
            lines.append(f"{esc(e.title)} — {fmt_clock(e.lagos)} WAT ({when}). "
                         f"Clear after {fmt_clock(clear_at)} WAT.")
        st.markdown(f"<div class='fe-danger'><div class='big'>{esc(DANGER_TEXT)}</div>"
                    f"<div class='sub'>{'<br>'.join(lines)}</div></div>", unsafe_allow_html=True)
    else:
        tent = tentative_high_today(events, today)
        if tent:
            names = ", ".join(esc(e.title) for e in tent)
            st.markdown(f"<div class='fe-caution'>⚠️ High-impact USD event today without a fixed "
                        f"time ({names}). Watch the news feed and treat sudden spikes with caution."
                        f"</div>", unsafe_allow_html=True)
        else:
            st.markdown("<div class='fe-clear'>✅ No high-impact USD release within ±30 minutes "
                        "of now.</div>", unsafe_allow_html=True)


def bias_box(verdict: str) -> str:
    if verdict == "HOT":
        return f"<div class='fe-bias hot'>🔴 {esc(HOT_TEXT)}</div>"
    if verdict == "COOL":
        return f"<div class='fe-bias cool'>🟢 {esc(COOL_TEXT)}</div>"
    if verdict == "INLINE":
        return ("<div class='fe-bias inline'>⚪ IN LINE: the release matched forecast. "
                "No fundamental bias from this print; trade your technical plan.</div>")
    if verdict == "MIXED":
        return ("<div class='fe-bias mixed'>🟠 MIXED: components point in opposite directions. "
                "No clean fundamental bias; let price show which number the market cares about.</div>")
    if verdict == "QUALITATIVE":
        return ("<div class='fe-bias pending'>Statement / press conference: there is no number "
                "to compare. Judge the tone (hawkish = USD strength, dovish = USD weakness).</div>")
    if verdict == "NO_DATA":
        return ("<div class='fe-bias pending'>Can't score: the feed has no usable forecast or the "
                "typed actual is not a number in the same unit as the forecast.</div>")
    return "<div class='fe-bias pending'>Awaiting the actual number.</div>"


STATUS_LABEL = {
    "HOT": "🔴 Hot (USD+)", "COOL": "🟢 Cool (USD−)", "INLINE": "⚪ In line",
    "PENDING": "… waiting", "QUALITATIVE": "statement", "NO_FORECAST": "no forecast",
    "BAD_ACTUAL": "⚠ not a number", "UNIT_MISMATCH": "⚠ unit mismatch",
}


def _on_actual_change(state_key: str, event_key: str) -> None:
    """Save a typed actual and copy it to the same box on the other tab."""
    value = st.session_state.get(state_key, "")
    save_manual_actual(event_key, value)
    for prefix in ("today_", "an_"):
        st.session_state[f"{prefix}act_{event_key}"] = value


def analyzer_card(group: dict, now: datetime, manual: dict, what_if: bool, prefix: str) -> None:
    """One release (e.g. the CPI set) with inputs for the actual numbers and the verdict."""
    fam = group["family"]
    first = group["first_utc"]
    when = (f"{first.astimezone(LAGOS).strftime('%a %d %b')} · {fmt_clock(first.astimezone(LAGOS))} WAT "
            f"({fmt_clock(first.astimezone(NEW_YORK))} ET)") if first else (
        group["day"].strftime("%a %d %b") if group["day"] else "date not set")
    released = bool(first) and first <= now
    with st.container(border=True):
        st.markdown(f"**{FAMILY_NAMES.get(fam, fam)}** — {when}")
        statuses = []
        for e, direction in group["items"]:
            actual, src = actual_for(e, manual)
            e_released = e.timed and e.utc <= now
            c1, c2, c3, c4, c5 = st.columns([3.2, 1.1, 1.1, 1.6, 1.6])
            c1.markdown(f"{e.title}" + ("  \n:gray[higher = cooler economy]" if direction < 0 else ""))
            c2.markdown(f":gray[Forecast]  \n**{e.forecast or '—'}**")
            c3.markdown(f":gray[Previous]  \n{e.previous or '—'}")
            if direction == 0:
                c4.markdown(":gray[Actual]  \nn/a (no number)")
                result = score_component("", "", 0)
            elif src == "feed":
                c4.markdown(f":gray[Actual (feed)]  \n**{actual}**")
                result = score_component(actual, e.forecast, direction)
            elif what_if:
                val = c4.text_input("What-if actual", key=f"{prefix}wi_{e.key}",
                                    placeholder=e.forecast or "e.g. 0.3%",
                                    help="Not saved. Try a number to see how it would read.")
                result = score_component(val, e.forecast, direction)
            else:
                skey = f"{prefix}act_{e.key}"
                if skey not in st.session_state:
                    st.session_state[skey] = manual.get(e.key, {}).get("actual", "")
                c4.text_input("Actual", key=skey, disabled=not e_released,
                              placeholder="after release" if not e_released else (e.forecast or "type it"),
                              help="Type the actual exactly as Forex Factory shows it "
                                   "(same unit as the forecast, e.g. 0.4% or 254K). Saved automatically.",
                              on_change=_on_actual_change, args=(skey, e.key))
                result = score_component(st.session_state.get(skey, ""), e.forecast, direction)
            statuses.append(result["status"])
            label = STATUS_LABEL.get(result["status"], result["status"])
            extra = f"  \n:gray[{result['surprise']}]" if result["surprise"] else ""
            typed = actual if src == "feed" else st.session_state.get(
                f"{prefix}{'wi' if what_if else 'act'}_{e.key}", "")
            if result["status"] in ("HOT", "COOL") and looks_implausible(typed, e.forecast, e.previous):
                extra += "  \n:orange[⚠ far from forecast & previous - check the row]"
            c5.markdown(f":gray[Reading]  \n{label}{extra}")
        verdict = group_verdict(statuses)
        if verdict == "PENDING" and not released and not what_if:
            secs = (first - now).total_seconds() if first else 0
            st.markdown(f"<div class='fe-bias pending'>Scheduled — releases in {fmt_delta(secs)}. "
                        "The bias appears once the actual is in.</div>", unsafe_allow_html=True)
        else:
            st.markdown(bias_box(verdict), unsafe_allow_html=True)


# =============================================================================
# 9. MAIN APP
# =============================================================================

def main() -> None:
    st.set_page_config(page_title="FundEdge", page_icon="📰", layout="wide")
    st.markdown(CSS, unsafe_allow_html=True)

    # ---------------- Sidebar: settings ----------------
    with st.sidebar:
        st.header("FundEdge settings")
        clock_choice = st.radio(
            "Feed clock",
            ["Auto-detect (recommended)", "GMT / UTC+0", "US Eastern (EST/EDT)"],
            help="Which clock the Forex Factory times are written in. Auto-detect checks "
                 "the data itself; see the 'Feed status' tab for the evidence.")
        anchor_choice = st.radio(
            "Execution window follows",
            ["New York open (9:30–11:00 ET)", "Fixed Lagos clock (3:30–5:00 PM WAT)"],
            help="Both are 3:30–5:00 PM WAT while the US is on winter time. From 14 Mar 2027 "
                 "the NY open moves to 2:30 PM WAT; the first option moves with it.")
        anchor = "ny" if anchor_choice.startswith("New York") else "lagos"
        week_impacts = st.multiselect("This week: show impact levels", IMPACT_ORDER,
                                      default=["High", "Medium", "Low"])
        force = st.button("🔄 Refresh feed now",
                          help="Downloads again if the last download was over 2.5 minutes ago.")
        uploaded = st.file_uploader("Or load the XML file yourself", type=["xml"],
                                    help="If the download is blocked, open the feed link in "
                                         "your browser, save the page as .xml and drop it here.")
        st.caption(f"Feed: {FEED_URL}")

    st.title("📰 FundEdge")
    st.caption("USD macro calendar for NAS100 & XAUUSD · all times in Lagos (WAT) unless marked ET")

    # ---------------- Load + parse the feed ----------------
    if uploaded is not None:
        raw, status = uploaded.getvalue(), {"source": "upload", "fetched_at": None,
                                             "stale": False, "message": f"Using uploaded file {uploaded.name}"}
    else:
        raw, status = get_feed(force=force)
    if raw is None:
        st.error(f"No calendar data. {status['message']}")
        st.info("Fix: check your internet connection and press 'Refresh feed now' in "
                "2–3 minutes, or load the XML file manually from the sidebar.")
        return
    try:
        all_events = parse_feed(raw)
    except FeedError as exc:
        st.error(f"The calendar file could not be read: {exc}")
        return

    detection = detect_feed_clock(all_events)
    clock = {"Auto-detect (recommended)": detection["clock"], "GMT / UTC+0": "UTC",
             "US Eastern (EST/EDT)": "America/New_York"}[clock_choice]
    apply_clock(all_events, clock)
    usd = sorted([e for e in all_events if e.country == CURRENCY], key=sort_key)

    if status.get("stale"):
        st.warning(status["message"])
    if clock_choice != "Auto-detect (recommended)" and clock != detection["clock"] \
            and detection["confidence"] == "high":
        st.warning(f"You forced the feed clock to {FEED_CLOCKS[clock]}, but the data points "
                   f"strongly to {FEED_CLOCKS[detection['clock']]}. Event times may be off by hours.")

    # ---------------- Live header (auto-refreshing) ----------------
    live_header(usd, anchor)

    now = now_utc()
    today = now.astimezone(LAGOS).date()
    manual = load_manual_actuals()

    tab_today, tab_week, tab_an, tab_feed = st.tabs(
        ["📅 Today's Macro Events", "🗓️ This Week's Outlook", "🧮 Impact Analyzer", "🛰️ Feed status"])

    # ---------------- Today ----------------
    with tab_today:
        todays = [e for e in usd if e.lagos_date == today]
        st.subheader(today.strftime("%A %d %B %Y") + " — USD events")
        if not todays:
            st.info("No USD events on the calendar today (Lagos date).")
        else:
            st.markdown(events_table(todays, now, manual), unsafe_allow_html=True)

        st.markdown("**Execution window vs news blackouts** "
                    "<span class='fe-muted'>(green = your window, red stripes = ±30 min around "
                    "high-impact USD releases, white line = now)</span>", unsafe_allow_html=True)
        st.markdown(timeline_html(today, usd, now, anchor), unsafe_allow_html=True)
        rows = blackouts_in_window(usd, today, anchor)
        w0, w1 = exec_window(today, anchor)
        clashes = [r for r in rows if r["overlap"]]
        if not rows:
            st.success(f"No high-impact USD releases today. Window {fmt_clock(w0)}–{fmt_clock(w1)} WAT is clear of scheduled red-folder news.")
        elif not clashes:
            st.success(f"High-impact news today, but every blackout ends before or starts after "
                       f"your {fmt_clock(w0)}–{fmt_clock(w1)} WAT window.")
        else:
            for r in clashes:
                o0, o1 = r["overlap"]
                st.error(f"No-trade inside your window: {fmt_clock(o0)}–{fmt_clock(o1)} WAT "
                         f"because of {r['event'].title} at {fmt_clock(r['event'].lagos)} WAT.")

        today_groups = [g for g in top_tier_groups(usd) if g["day"] == today]
        if today_groups:
            st.subheader("Top-tier releases today")
            for g in today_groups:
                analyzer_card(g, now, manual, what_if=False, prefix="today_")

    # ---------------- This week ----------------
    with tab_week:
        week = [e for e in usd if e.impact in week_impacts]
        days = sorted({e.lagos_date for e in usd if e.lagos_date})
        if days:
            st.caption(f"Feed week: {days[0].strftime('%a %d %b')} – {days[-1].strftime('%a %d %b %Y')} · "
                       f"{len(usd)} USD events, {sum(e.impact == 'High' for e in usd)} high-impact")
        counts = {k: sum(e.impact == k for e in usd) for k in IMPACT_ORDER}
        st.markdown(" ".join(f"{badge(k)} <span class='fe-muted'>{counts[k]}</span>&nbsp;&nbsp;"
                             for k in IMPACT_ORDER), unsafe_allow_html=True)
        if not week:
            st.info("No USD events match the selected impact levels.")
        for d in sorted({e.lagos_date for e in week if e.lagos_date}):
            label = d.strftime("%A %d %B") + ("  · TODAY" if d == today else "")
            st.markdown(f"<div class='fe-day'>{esc(label)}</div>", unsafe_allow_html=True)
            st.markdown(events_table([e for e in week if e.lagos_date == d], now, manual),
                        unsafe_allow_html=True)

    # ---------------- Impact Analyzer ----------------
    with tab_an:
        st.markdown(
            "Scores this week's **CPI, NFP, GDP and FOMC** releases: actual vs forecast.  \n"
            "The Forex Factory export does not include actual numbers, so after a release "
            "type the actual from forexfactory.com into the box (it saves automatically). "
            "Inputs unlock at the scheduled release time.")
        what_if = st.toggle("What-if mode (try numbers before the release; nothing is saved)",
                            value=False)
        groups = top_tier_groups(usd)
        if not groups:
            st.info("No CPI, NFP, GDP or FOMC releases on this week's calendar.")
        for g in groups:
            analyzer_card(g, now, manual, what_if=what_if, prefix="an_")
        with st.expander("How the reading is decided"):
            st.markdown(
                "- Each component is compared with its forecast at the precision Forex Factory prints.\n"
                "- **Hot** = USD-positive surprise: inflation, payrolls, earnings, GDP or the rate "
                "above forecast, or the unemployment rate *below* forecast.\n"
                "- Components of one release are netted (hot minus cool). Equal counts with at "
                "least one surprise = **Mixed**.\n"
                "- The bias is a starting assumption, not a signal. Big releases often spike one "
                "way and reverse within minutes, which is why the Danger Zone blocks ±30 min.")

    # ---------------- Feed status ----------------
    with tab_feed:
        src = {"live": "Downloaded live", "cache": "Saved copy", "file": "Local test file",
               "upload": "Uploaded file", "none": "None"}[status["source"]]
        st.markdown(f"**Source:** {src}  \n**Note:** {status['message']}")
        if status.get("fetched_at"):
            st.markdown(f"**Last successful download:** "
                        f"{status['fetched_at'].astimezone(LAGOS).strftime('%a %d %b %Y, %I:%M %p')} WAT")
        sc = detection["scores"]
        st.markdown(
            f"**Feed clock in use:** {FEED_CLOCKS[clock]}  \n"
            f"**Auto-detect evidence:** of {detection['total']} timed USD events, "
            f"{sc['UTC']} land on standard US release times if the feed is GMT, "
            f"{sc['America/New_York']} if it is US Eastern → "
            f"{FEED_CLOCKS[detection['clock']]} ({detection['confidence']} confidence).")
        st.caption("Cross-check once: CPI and NFP are released at 8:30 AM New York time. "
                   "If they show as 8:30 AM ET here, the clock is right.")
        sample = [e for e in usd if e.timed][:8]
        if sample:
            st.markdown("**Raw feed vs converted (first USD events):**")
            st.markdown(
                "<table class='fe'><tr><th>Feed date</th><th>Feed time</th><th>Event</th>"
                "<th>UTC</th><th>New York</th><th>Lagos</th></tr>" + "".join(
                    f"<tr><td>{esc(e.date_raw)}</td><td>{esc(e.time_raw)}</td><td>{esc(e.title)}</td>"
                    f"<td>{e.utc.strftime('%a %H:%M')}</td><td>{e.ny.strftime('%a %H:%M')} {e.ny.tzname()}</td>"
                    f"<td>{e.lagos.strftime('%a %H:%M')} WAT</td></tr>" for e in sample) + "</table>",
                unsafe_allow_html=True)
        st.caption(f"{len(all_events)} events in the file across all currencies; "
                   f"{len(usd)} are USD. Saved actuals: {len(manual)}.")


if __name__ == "__main__":
    main()

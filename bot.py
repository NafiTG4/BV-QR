"""
ScanVault — Telegram QR & Barcode Scanner Bot
==============================================
Features:
- Zero commands: everything via inline buttons
- Premium formatting with emoji, dividers, clean layout
- AES-256-GCM encrypted history (in-memory, privacy-first)
- zxing-cpp + OpenCV dual-decoder with image preprocessing
- URL intelligence: short URL expand, title fetch, phishing detection
- Smart parsers: WiFi, vCard, MeCard, Crypto, UPI, Geo, mailto, SMS, tel
- QR code generator: text → QR image
- Barcode format shown in every result (QR / EAN-13 / Code 128 etc.)
- History filter by type, export as JSON file
- Rate limiting, multi-code detection, no disk writes
- USER_DATA TTL cleanup to prevent memory leak
- vCard multi-value TEL/EMAIL support
- Privacy mode: clear button hides when active
"""

import asyncio
import io
import json
import logging
import os
import re
import time
import urllib.parse
from collections import defaultdict
from datetime import datetime, timezone

import cv2
import httpx
import numpy as np
import qrcode
import zxingcpp
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.constants import ParseMode
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------
logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# Config
# ---------------------------------------------------------------------------
BOT_TOKEN   = os.environ["BOT_TOKEN"]
_raw_key    = os.environ.get("STORAGE_KEY", "")
STORAGE_KEY = bytes.fromhex(_raw_key) if len(_raw_key) == 64 else os.urandom(32)

MAX_HISTORY       = 20
RATE_LIMIT_SEC    = 5
MAX_CODES_SHOWN   = 10
USER_TTL_SECONDS  = 60 * 60 * 24 * 7   # 7 days inactive → evict from memory
URL_TIMEOUT       = 4                   # seconds for expand/title requests

SUSPICIOUS_TLDS = {".tk", ".ml", ".ga", ".cf", ".gq", ".xyz", ".top", ".pw"}

SHORTENERS = {
    "bit.ly", "t.ly", "tinyurl.com", "ow.ly", "goo.gl",
    "short.io", "rb.gy", "is.gd", "buff.ly", "cutt.ly",
}

# Human-readable barcode format names
FORMAT_NAMES: dict[str, str] = {
    "QRCode":       "QR Code",
    "DataMatrix":   "Data Matrix",
    "PDF417":       "PDF417",
    "Aztec":        "Aztec",
    "Code128":      "Code 128",
    "Code39":       "Code 39",
    "Code93":       "Code 93",
    "EAN13":        "EAN-13",
    "EAN8":         "EAN-8",
    "UPCA":         "UPC-A",
    "UPCE":         "UPC-E",
    "ITF":          "ITF",
    "Codabar":      "Codabar",
    "DataBar":      "DataBar",
    "MaxiCode":     "MaxiCode",
}

# History filter type labels
FILTER_TYPES = ["url", "wifi", "vcard", "mecard", "crypto", "upi", "geo", "email", "sms", "tel", "text"]

# ---------------------------------------------------------------------------
# In-memory user store
# { uid: { "privacy": bool, "history": [...], "last_scan": float, "last_active": float } }
# ---------------------------------------------------------------------------
USER_DATA: dict[int, dict] = defaultdict(
    lambda: {"privacy": False, "history": [], "last_scan": 0.0, "last_active": time.monotonic()}
)

# ---------------------------------------------------------------------------
# Memory TTL cleanup — called periodically to evict idle users
# ---------------------------------------------------------------------------

def _cleanup_idle_users() -> None:
    now  = time.monotonic()
    dead = [uid for uid, d in USER_DATA.items()
            if now - d.get("last_active", 0) > USER_TTL_SECONDS]
    for uid in dead:
        del USER_DATA[uid]
    if dead:
        logger.info("TTL evicted %d idle user(s)", len(dead))


def _touch_active(uid: int) -> None:
    USER_DATA[uid]["last_active"] = time.monotonic()

# ---------------------------------------------------------------------------
# AES-256-GCM encryption helpers
# ---------------------------------------------------------------------------

def _encrypt(plaintext: str) -> str:
    aesgcm = AESGCM(STORAGE_KEY)
    nonce  = os.urandom(12)
    ct     = aesgcm.encrypt(nonce, plaintext.encode(), None)
    return (nonce + ct).hex()


def _decrypt(hex_data: str) -> str:
    raw    = bytes.fromhex(hex_data)
    aesgcm = AESGCM(STORAGE_KEY)
    return aesgcm.decrypt(raw[:12], raw[12:], None).decode()

# ---------------------------------------------------------------------------
# Rate limiter
# ---------------------------------------------------------------------------

def _is_rate_limited(uid: int) -> bool:
    return (time.monotonic() - USER_DATA[uid]["last_scan"]) < RATE_LIMIT_SEC


def _touch_rate(uid: int) -> None:
    USER_DATA[uid]["last_scan"] = time.monotonic()

# ---------------------------------------------------------------------------
# History
# ---------------------------------------------------------------------------

def _save(uid: int, kind: str, raw: str, fmt: str = "") -> None:
    """Encrypt and append one scan entry to user history."""
    if USER_DATA[uid]["privacy"]:
        return
    entry = {
        "ts":     datetime.now(timezone.utc).strftime("%d %b %Y, %H:%M UTC"),
        "type":   kind,
        "format": fmt,
        "raw":    raw[:200],
    }
    h = USER_DATA[uid]["history"]
    h.append(_encrypt(json.dumps(entry)))
    if len(h) > MAX_HISTORY:
        h.pop(0)


def _load_history(uid: int, filter_type: str = "") -> list[dict]:
    """Decrypt all history entries, optionally filtered by content type."""
    out = []
    for enc in USER_DATA[uid]["history"]:
        try:
            entry = json.loads(_decrypt(enc))
            if not filter_type or entry.get("type") == filter_type:
                out.append(entry)
        except Exception:
            pass
    return out

# ---------------------------------------------------------------------------
# MarkdownV2 escape
# ---------------------------------------------------------------------------

def _e(text: str) -> str:
    """Escape all special chars for Telegram MarkdownV2."""
    for ch in r"\_*[]()~`>#+-=|{}.!":
        text = text.replace(ch, f"\\{ch}")
    return text

# ---------------------------------------------------------------------------
# Divider & badge helpers
# ---------------------------------------------------------------------------

DIV = "┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"


def _badge(kind: str) -> str:
    return {
        "url":    "🔗",
        "wifi":   "📶",
        "vcard":  "👤",
        "mecard": "👤",
        "crypto": "₿",
        "upi":    "💳",
        "geo":    "📍",
        "email":  "✉️",
        "sms":    "💬",
        "tel":    "📞",
        "text":   "📄",
    }.get(kind, "📄")


def _fmt_label(fmt: str) -> str:
    """Return human-readable barcode format name."""
    return FORMAT_NAMES.get(fmt, fmt) if fmt else ""

# ---------------------------------------------------------------------------
# Image decoder — with preprocessing for low-quality images
# ---------------------------------------------------------------------------

def _preprocess_variants(img: np.ndarray) -> list[np.ndarray]:
    """
    Return multiple image variants to maximize decode success.
    Tries grayscale, contrast-enhanced, and adaptive-threshold versions.
    """
    variants = [img]

    gray = cv2.cvtColor(img, cv2.COLOR_BGR2GRAY)
    variants.append(gray)

    # CLAHE: adaptive histogram equalization (great for low contrast/blurry)
    clahe   = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
    enhanced = clahe.apply(gray)
    variants.append(enhanced)

    # Adaptive threshold binarization (handles uneven lighting)
    thresh = cv2.adaptiveThreshold(
        enhanced, 255,
        cv2.ADAPTIVE_THRESH_GAUSSIAN_C,
        cv2.THRESH_BINARY, 11, 2
    )
    variants.append(thresh)

    # Upscale small images — zxing struggles below ~200px
    h, w = gray.shape[:2]
    if max(h, w) < 400:
        scale  = 400 / max(h, w)
        big    = cv2.resize(gray, None, fx=scale, fy=scale, interpolation=cv2.INTER_CUBIC)
        variants.append(big)

    return variants


def _decode(img_bytes: bytes) -> list[tuple[str, str]]:
    """
    Decode barcodes from image bytes.
    Returns list of (text, format_name) tuples, deduplicated.
    """
    arr = np.frombuffer(img_bytes, dtype=np.uint8)
    img = cv2.imdecode(arr, cv2.IMREAD_COLOR)
    if img is None:
        return []

    seen:    set[str]              = set()
    results: list[tuple[str, str]] = []

    for variant in _preprocess_variants(img):
        # Convert grayscale variants to RGB for zxingcpp
        if len(variant.shape) == 2:
            rgb = cv2.cvtColor(variant, cv2.COLOR_GRAY2RGB)
        else:
            rgb = cv2.cvtColor(variant, cv2.COLOR_BGR2RGB)

        try:
            codes = zxingcpp.read_barcodes(rgb)
            for c in codes:
                if c.text and c.text not in seen:
                    seen.add(c.text)
                    fmt = FORMAT_NAMES.get(c.format.name, c.format.name)
                    results.append((c.text, fmt))
        except Exception as ex:
            logger.warning("zxingcpp variant: %s", ex)

        if results:
            break   # stop trying variants once we have results

    # Fallback: OpenCV built-in QR detector
    if not results:
        try:
            det       = cv2.QRCodeDetector()
            data, _, _ = det.detectAndDecodeMulti(img)
            for d in (data or []):
                if d and d not in seen:
                    seen.add(d)
                    results.append((d, "QR Code"))
        except Exception as ex:
            logger.warning("cv2 fallback: %s", ex)

    return results[:MAX_CODES_SHOWN]

# ---------------------------------------------------------------------------
# QR code generator
# ---------------------------------------------------------------------------

def _generate_qr(text: str) -> bytes:
    """Generate a QR code PNG from text. Returns raw PNG bytes."""
    qr = qrcode.QRCode(
        version=None,           # auto-size
        error_correction=qrcode.constants.ERROR_CORRECT_M,
        box_size=10,
        border=4,
    )
    qr.add_data(text)
    qr.make(fit=True)
    img = qr.make_image(fill_color="black", back_color="white")
    buf = io.BytesIO()
    img.save(buf, format="PNG")
    return buf.getvalue()

# ---------------------------------------------------------------------------
# URL intelligence
# ---------------------------------------------------------------------------

async def _expand(url: str) -> str | None:
    """Follow redirects for known shortener domains. Tries HEAD then GET."""
    host = urllib.parse.urlparse(url).netloc.lower().lstrip("www.")
    if host not in SHORTENERS:
        return None
    try:
        async with httpx.AsyncClient(follow_redirects=True, timeout=URL_TIMEOUT) as c:
            try:
                r = await c.head(url)
            except Exception:
                # Some shorteners (e.g. rb.gy) ignore HEAD — fall back to GET
                r = await c.get(url)
            final = str(r.url)
            return final if final != url else None
    except Exception:
        return None


async def _title(url: str) -> str:
    """Fetch <title> from a URL. Returns empty string on failure."""
    try:
        async with httpx.AsyncClient(follow_redirects=True, timeout=URL_TIMEOUT) as c:
            r = await c.get(url, headers={"User-Agent": "Mozilla/5.0"})
            m = re.search(r"<title[^>]*>(.*?)</title>", r.text[:8000], re.I | re.S)
            return m.group(1).strip()[:80] if m else ""
    except Exception:
        return ""


def _phishing(url: str) -> bool:
    """Heuristic phishing check: IP addresses, suspicious TLDs, typosquatting, excess subdomains."""
    host = urllib.parse.urlparse(url).netloc.lower()

    # Bare IP address
    if re.match(r"^\d{1,3}(\.\d{1,3}){3}(:\d+)?$", host):
        return True

    # Suspicious free TLDs
    if any(host.endswith(t) for t in SUSPICIOUS_TLDS):
        return True

    domain_part = host.split(":")[0]   # strip port

    # Homoglyph / digit substitution (paypa1.com, g00gle.com)
    normalized = re.sub(r"[0@]", "o", re.sub(r"[1!|]", "l", domain_part))
    POPULAR = {
        "paypal", "google", "facebook", "amazon", "apple", "microsoft",
        "netflix", "instagram", "whatsapp", "telegram", "twitter",
    }
    for brand in POPULAR:
        # If brand appears in normalized domain but domain is NOT the real brand
        if brand in normalized and not domain_part.endswith(f"{brand}.com"):
            return True

    # Excessive subdomains (e.g. paypal.com.login.evil.ru)
    if len(domain_part.split(".")) > 4:
        return True

    return False

# ---------------------------------------------------------------------------
# Content parsers — return (display_text, buttons, content_kind)
# ---------------------------------------------------------------------------

def _parse(raw: str, fmt: str = "") -> tuple[str, list[list[InlineKeyboardButton]], str]:
    """Route raw barcode text to the right parser. Returns (text, btns, kind)."""
    r       = raw.strip()
    fmt_tag = f"\n_Format: {_e(_fmt_label(fmt))}_" if fmt else ""

    if r.startswith("WIFI:"):                                    return _p_wifi(r, fmt_tag)
    if r.startswith("BEGIN:VCARD"):                              return _p_vcard(r, fmt_tag)
    if r.startswith("MECARD:"):                                  return _p_mecard(r, fmt_tag)
    if re.match(r"^(bitcoin|ethereum|litecoin|monero):", r, re.I): return _p_crypto(r, fmt_tag)
    if r.startswith("upi://"):                                   return _p_upi(r, fmt_tag)
    if r.startswith("geo:"):                                     return _p_geo(r, fmt_tag)
    if r.startswith("mailto:"):                                  return _p_mailto(r, fmt_tag)
    if r.startswith("smsto:") or r.startswith("sms:"):          return _p_sms(r, fmt_tag)
    if r.startswith("tel:"):                                     return _p_tel(r, fmt_tag)
    if re.match(r"^https?://", r, re.I):                        return "", [], "url"
    return _p_text(r, fmt_tag)


def _p_wifi(r: str, fmt_tag: str) -> tuple[str, list, str]:
    m = re.search(r"S:([^;]*)", r);  ssid = m.group(1) if m else "?"
    m = re.search(r"P:([^;]*)", r);  pwd  = m.group(1) if m else ""
    m = re.search(r"T:([^;]*)", r);  enc  = m.group(1) if m else "?"
    m = re.search(r"H:(true|false)", r, re.I); hidden = m.group(1).lower() == "true" if m else False

    lines = [f"📶 *Wi\\-Fi Network*\n`{DIV}`"]
    lines.append(f"*Network* ›  `{_e(ssid)}`")
    lines.append(f"*Password* ›  `{_e(pwd) if pwd else 'none'}`")
    lines.append(f"*Security* ›  `{_e(enc)}`")
    if hidden:
        lines.append("*Hidden* ›  `Yes`")
    lines.append(fmt_tag)
    return "\n".join(lines), [], "wifi"


def _p_vcard(r: str, fmt_tag: str) -> tuple[str, list, str]:
    # Support multi-value fields (multiple TEL / EMAIL lines)
    fn     = re.search(r"^FN:(.*)",         r, re.M)
    org    = re.search(r"^ORG:(.*)",        r, re.M)
    title  = re.search(r"^TITLE:(.*)",      r, re.M)
    url    = re.search(r"^URL:(.*)",        r, re.M)
    addr   = re.search(r"^ADR[^:]*:(.*)",   r, re.M)
    note   = re.search(r"^NOTE:(.*)",       r, re.M)
    phones = re.findall(r"TEL[^:]*:(.*)",   r)
    emails = re.findall(r"EMAIL[^:]*:(.*)", r)

    name = fn.group(1).strip() if fn else "?"

    lines = [f"👤 *Contact Card*\n`{DIV}`"]
    lines.append(f"*Name* ›  {_e(name)}")
    if org:   lines.append(f"*Company* ›  {_e(org.group(1).strip())}")
    if title: lines.append(f"*Title* ›  {_e(title.group(1).strip())}")
    for p in phones[:3]:   lines.append(f"*Phone* ›  `{_e(p.strip())}`")
    for em in emails[:3]:  lines.append(f"*Email* ›  `{_e(em.strip())}`")
    if addr:
        # vCard ADR format: ;;street;city;state;zip;country
        parts = [x.strip() for x in addr.group(1).split(";") if x.strip()]
        if parts: lines.append(f"*Address* ›  {_e(', '.join(parts))}")
    if url:  lines.append(f"*Website* ›  {_e(url.group(1).strip())}")
    if note: lines.append(f"*Note* ›  {_e(note.group(1).strip()[:100])}")
    lines.append(fmt_tag)

    btns: list[list[InlineKeyboardButton]] = []
    if phones:
        row = [InlineKeyboardButton("📞 Call", url=f"tel:{phones[0].strip()}")]
        if len(phones) > 1:
            row.append(InlineKeyboardButton("📞 Alt", url=f"tel:{phones[1].strip()}"))
        btns.append(row)
    if emails:
        row = [InlineKeyboardButton("✉️ Email", url=f"mailto:{emails[0].strip()}")]
        btns.append(row)
    return "\n".join(lines), btns, "vcard"


def _p_mecard(r: str, fmt_tag: str) -> tuple[str, list, str]:
    m_n   = re.search(r"N:([^;]*)",     r)
    m_tel = re.findall(r"TEL:([^;]*)",  r)
    m_em  = re.findall(r"EMAIL:([^;]*)", r)
    m_url = re.search(r"URL:([^;]*)",   r)
    name  = m_n.group(1) if m_n else "?"

    lines = [f"👤 *Contact Card*\n`{DIV}`"]
    lines.append(f"*Name* ›  {_e(name)}")
    for p in m_tel[:3]:  lines.append(f"*Phone* ›  `{_e(p.strip())}`")
    for e in m_em[:3]:   lines.append(f"*Email* ›  `{_e(e.strip())}`")
    if m_url: lines.append(f"*Website* ›  {_e(m_url.group(1).strip())}")
    lines.append(fmt_tag)

    btns: list[list[InlineKeyboardButton]] = []
    if m_tel:
        btns.append([InlineKeyboardButton("📞 Call", url=f"tel:{m_tel[0].strip()}")])
    if m_em:
        btns.append([InlineKeyboardButton("✉️ Email", url=f"mailto:{m_em[0].strip()}")])
    return "\n".join(lines), btns, "mecard"


def _p_crypto(r: str, fmt_tag: str) -> tuple[str, list, str]:
    m = re.match(r"^(\w+):([^?]+)\??(.*)$", r, re.I)
    if not m:
        return f"₿ *Crypto URI*\n`{DIV}`\n`{_e(r)}`", [], "crypto"
    network = m.group(1).capitalize()
    address = m.group(2)
    params  = dict(urllib.parse.parse_qsl(m.group(3)))
    amount  = params.get("amount", "")
    label   = params.get("label", "")

    lines = [f"₿ *{_e(network)} Payment*\n`{DIV}`"]
    lines.append(f"*Address*\n`{_e(address)}`")
    if amount: lines.append(f"*Amount* ›  `{_e(amount)} {_e(network)}`")
    if label:  lines.append(f"*Label* ›  {_e(label)}")
    lines.append(f"*Network* ›  `{_e(network)}`")
    lines.append(fmt_tag)
    return "\n".join(lines), [], "crypto"


def _p_upi(r: str, fmt_tag: str) -> tuple[str, list, str]:
    params = dict(urllib.parse.parse_qsl(urllib.parse.urlparse(r).query))
    pa = params.get("pa", "?")
    pn = params.get("pn", "")
    am = params.get("am", "")
    tn = params.get("tn", "")
    cu = params.get("cu", "INR")

    lines = [f"💳 *UPI Payment*\n`{DIV}`"]
    lines.append(f"*UPI ID* ›  `{_e(pa)}`")
    if pn: lines.append(f"*Payee* ›  {_e(pn)}")
    if am: lines.append(f"*Amount* ›  {_e(cu)} `{_e(am)}`")
    if tn: lines.append(f"*Note* ›  {_e(tn)}")
    lines.append(fmt_tag)
    return "\n".join(lines), [[InlineKeyboardButton("💳 Pay Now", url=r)]], "upi"


def _p_geo(r: str, fmt_tag: str) -> tuple[str, list, str]:
    m = re.match(r"geo:(-?\d+\.?\d*),(-?\d+\.?\d*)", r)
    if not m:
        return f"📍 *Location*\n`{DIV}`\n`{_e(r)}`", [], "geo"
    lat, lon  = m.group(1), m.group(2)
    maps_url  = f"https://maps.google.com/?q={lat},{lon}"
    apple_url = f"https://maps.apple.com/?q={lat},{lon}"
    text = (
        f"📍 *Location*\n`{DIV}`\n"
        f"*Latitude* ›  `{lat}`\n"
        f"*Longitude* ›  `{lon}`\n"
        f"{fmt_tag}"
    )
    btns = [[
        InlineKeyboardButton("🗺 Google Maps", url=maps_url),
        InlineKeyboardButton("🍎 Apple Maps", url=apple_url),
    ]]
    return text, btns, "geo"


def _p_mailto(r: str, fmt_tag: str) -> tuple[str, list, str]:
    addr    = r[7:].split("?")[0]
    params  = dict(urllib.parse.parse_qsl(urllib.parse.urlparse(r).query))
    subject = params.get("subject", "")
    body    = params.get("body", "")

    lines = [f"✉️ *Email Address*\n`{DIV}`", f"*To* ›  `{_e(addr)}`"]
    if subject: lines.append(f"*Subject* ›  {_e(subject)}")
    if body:    lines.append(f"*Body* ›  {_e(body[:100])}")
    lines.append(fmt_tag)
    return "\n".join(lines), [[InlineKeyboardButton("✉️ Send Email", url=r)]], "email"


def _p_sms(r: str, fmt_tag: str) -> tuple[str, list, str]:
    m   = re.match(r"(?:smsto?):([^:?]+):?(.*)", r)
    num = m.group(1) if m else "?"
    msg = m.group(2) if m else ""
    lines = [f"💬 *SMS*\n`{DIV}`", f"*To* ›  `{_e(num)}`"]
    if msg: lines.append(f"*Message* ›  {_e(msg)}")
    lines.append(fmt_tag)
    return "\n".join(lines), [[InlineKeyboardButton("💬 Send SMS", url=f"sms:{num}")]], "sms"


def _p_tel(r: str, fmt_tag: str) -> tuple[str, list, str]:
    num  = r[4:]
    text = f"📞 *Phone Number*\n`{DIV}`\n*Number* ›  `{_e(num)}`\n{fmt_tag}"
    return text, [[InlineKeyboardButton("📞 Call", url=r)]], "tel"


def _p_text(r: str, fmt_tag: str) -> tuple[str, list, str]:
    preview = r[:500]
    # Plain escaped text — no backtick wrap (avoids MarkdownV2 parse errors with backticks in content)
    text = f"📄 *Scanned Data*\n`{DIV}`\n{_e(preview)}\n{fmt_tag}"
    return text, [], "text"

# ---------------------------------------------------------------------------
# Welcome / menu
# ---------------------------------------------------------------------------

def _welcome(name: str, uid: int) -> tuple[str, InlineKeyboardMarkup]:
    priv  = USER_DATA[uid]["privacy"]
    count = len(USER_DATA[uid]["history"])
    priv_label = "🔒 Privacy  ON" if priv else "🔓 Privacy  OFF"
    cnt_label  = f"📋 History  ({count} scan{'s' if count != 1 else ''})"

    text = (
        f"✦ *ScanVault*\n"
        f"`{DIV}`\n"
        f"Hello, *{_e(name)}* — send me any photo containing a\n"
        f"QR code or barcode and I'll decode it instantly\\.\n\n"
        f"*Supported formats*\n"
        f"› QR Code · Data Matrix · PDF417 · Aztec\n"
        f"› Code 128 · Code 39 · EAN · UPC · and more\n\n"
        f"*Smart detection*\n"
        f"› Wi\\-Fi · Contacts · Crypto · UPI · Geo\n"
        f"› URLs with phishing check · SMS · Email · Phone\n\n"
        f"*Also*\n"
        f"› Send any text to generate a QR code\n\n"
        f"`{DIV}`\n"
        f"_No image is ever saved to disk\\._"
    )

    btns = [[InlineKeyboardButton(priv_label, callback_data="toggle_privacy")]]

    if not priv:
        # History row: view + filter + export
        btns.append([
            InlineKeyboardButton(cnt_label,    callback_data="show_history"),
            InlineKeyboardButton("🔍 Filter",  callback_data="filter_history"),
        ])
        btns.append([
            InlineKeyboardButton("📤 Export",  callback_data="export_history"),
            InlineKeyboardButton("🗑 Clear",   callback_data="clear_history"),
        ])
    # When privacy is ON, hide history controls entirely (no "Nothing to clear" confusion)

    return text, InlineKeyboardMarkup(btns)

# ---------------------------------------------------------------------------
# URL result sender (async enriched)
# ---------------------------------------------------------------------------

async def _send_url(
    update: Update,
    edit_msg,
    raw: str,
    prefix: str,
    uid: int,
    fmt: str = "",
) -> None:
    # Expand and fetch title concurrently
    expanded, page_title = await asyncio.gather(
        _expand(raw),
        _title(raw),
        return_exceptions=False,
    )

    final  = expanded if expanded else raw
    risky  = _phishing(final)
    domain = urllib.parse.urlparse(final).netloc or final[:50]

    # If we expanded to a new URL and still have no title, try the expanded URL
    if expanded and not page_title:
        page_title = await _title(final)

    fmt_tag = f"\n_Format: {_e(_fmt_label(fmt))}_" if fmt else ""

    lines = [f"{prefix}🔗 *Link*\n`{DIV}`"]
    lines.append(f"`{_e(raw[:200])}`")
    if expanded:
        lines.append(f"\n*Redirects to*\n`{_e(final[:200])}`")
    if page_title:
        lines.append(f"\n*Page* ›  {_e(page_title)}")
    else:
        lines.append(f"\n*Domain* ›  `{_e(domain)}`")
    if risky:
        lines.append(f"\n⚠️ *Warning:* This URL may be a phishing attempt\\.")
    lines.append(fmt_tag)

    text = "\n".join(lines)
    kb   = InlineKeyboardMarkup([[InlineKeyboardButton("🌐 Open Link", url=final)]])

    # Save to history
    _save(uid, "url", raw, fmt)

    try:
        if edit_msg:
            await edit_msg.edit_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
        else:
            await update.message.reply_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
    except Exception as ex:
        logger.error("_send_url render failed: %s", ex)
        # Fallback plain text so "Scanning..." doesn't get stuck
        try:
            fallback = f"🔗 Link: {raw[:200]}"
            if edit_msg:
                await edit_msg.edit_text(fallback)
            else:
                await update.message.reply_text(fallback)
        except Exception:
            pass

# ---------------------------------------------------------------------------
# Handlers
# ---------------------------------------------------------------------------

async def handle_start(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle /start command and plain text — show welcome or generate QR."""
    user = update.effective_user
    uid  = user.id
    _touch_active(uid)

    msg = update.message.text or ""

    # If user sends non-command text, generate a QR code from it
    if msg and not msg.startswith("/"):
        await handle_qr_generate(update, msg)
        return

    name      = user.first_name or "there"
    text, kb  = _welcome(name, uid)
    await update.message.reply_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)


async def handle_qr_generate(update: Update, text: str) -> None:
    """Generate and send a QR code image for the given text."""
    status = await update.message.reply_text(
        "⚙️ _Generating QR code\\.\\.\\._", parse_mode=ParseMode.MARKDOWN_V2
    )
    try:
        png = await asyncio.get_event_loop().run_in_executor(None, _generate_qr, text)
        caption = f"✅ *QR Code generated*\n`{DIV}`\n_Data:_ {_e(text[:100])}"
        await update.message.reply_photo(
            photo=io.BytesIO(png),
            caption=caption,
            parse_mode=ParseMode.MARKDOWN_V2,
        )
        await status.delete()
    except Exception as ex:
        logger.error("QR generate error: %s", ex)
        await status.edit_text(
            "❌ *Could not generate QR code\\.*",
            parse_mode=ParseMode.MARKDOWN_V2,
        )


async def handle_image(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle photo / document image uploads — decode all barcodes found."""
    uid = update.effective_user.id
    _touch_active(uid)

    if _is_rate_limited(uid):
        await update.message.reply_text(
            "⏳ *Slow down a bit\\!*\n_Please wait a few seconds between scans\\._",
            parse_mode=ParseMode.MARKDOWN_V2,
        )
        return
    _touch_rate(uid)

    status = await update.message.reply_text(
        "🔍 _Scanning\\.\\.\\._", parse_mode=ParseMode.MARKDOWN_V2
    )

    # Download image into memory — no disk write
    try:
        if update.message.document:
            f = await update.message.document.get_file()
        else:
            f = await update.message.photo[-1].get_file()
        buf = io.BytesIO()
        await f.download_to_memory(buf)
        img_bytes = buf.getvalue()
    except Exception as ex:
        logger.error("Download error: %s", ex)
        await status.edit_text(
            "❌ *Could not load the image\\.*\n_Please try again\\._",
            parse_mode=ParseMode.MARKDOWN_V2,
        )
        return

    # Run decode in thread pool to avoid blocking the event loop
    codes = await asyncio.get_event_loop().run_in_executor(None, _decode, img_bytes)

    if not codes:
        await status.edit_text(
            "🔍 *Nothing found*\n"
            f"`{DIV}`\n"
            "No QR code or barcode was detected\\.\n\n"
            "*Tips*\n"
            "› Make sure the code is fully visible\n"
            "› Use a well\\-lit, clear photo\n"
            "› Try sending as a *file* for higher quality",
            parse_mode=ParseMode.MARKDOWN_V2,
        )
        return

    total = len(codes)

    for idx, (raw, fmt) in enumerate(codes, 1):
        prefix = f"*\\[{idx} / {total}\\]*  " if total > 1 else ""
        text, btns, kind = _parse(raw, fmt)

        if kind == "url":
            await _send_url(update, status if idx == 1 else None, raw, prefix, uid, fmt)
        else:
            _save(uid, kind, raw, fmt)
            full = prefix + text if prefix else text
            kb   = InlineKeyboardMarkup(btns) if btns else None
            if idx == 1:
                await status.edit_text(full, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
            else:
                await update.message.reply_text(full, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)


async def handle_callback(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    """Handle all inline keyboard button presses."""
    q   = update.callback_query
    uid = q.from_user.id
    _touch_active(uid)
    await q.answer()

    data = q.data or ""

    # ── Toggle privacy ───────────────────────────────────────────────────────
    if data == "toggle_privacy":
        current   = USER_DATA[uid]["privacy"]
        new_state = not current
        USER_DATA[uid]["privacy"] = new_state
        icon  = "🔒" if new_state else "🔓"
        label = "Enabled" if new_state else "Disabled"
        note  = (
            f"{icon} *Privacy Mode {_e(label)}*\n`{DIV}`\n"
            + (
                "_Your scans will no longer be stored\\._"
                if new_state else
                "_Your scans will now be saved \\(encrypted\\)\\._"
            )
        )
        await q.message.reply_text(note, parse_mode=ParseMode.MARKDOWN_V2)
        name = q.from_user.first_name or "there"
        text, kb = _welcome(name, uid)
        try:
            await q.message.edit_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
        except Exception:
            pass
        return

    # ── Show history ─────────────────────────────────────────────────────────
    if data == "show_history":
        entries = _load_history(uid)
        if not entries:
            await q.message.reply_text(
                f"📭 *No History Yet*\n`{DIV}`\n"
                "_Start scanning and your results will appear here\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
            return
        lines = [f"📋 *Scan History*  _{len(entries)} entries_\n`{DIV}`"]
        for i, e in enumerate(reversed(entries), 1):
            kind    = e.get("type", "?")
            ts      = _e(e.get("ts", "?"))
            preview = _e(e.get("raw", "")[:55])
            fmt     = e.get("format", "")
            badge   = _badge(kind)
            fmt_str = f" · _{_e(fmt)}_" if fmt else ""
            lines.append(f"{badge}  *{i:02d}*{fmt_str}  `{preview}`\n      __{ts}__")
            if i < len(entries):
                lines.append("")
        await q.message.reply_text("\n".join(lines), parse_mode=ParseMode.MARKDOWN_V2)
        return

    # ── Filter history ───────────────────────────────────────────────────────
    if data == "filter_history":
        # Build type filter buttons based on what's actually in history
        entries   = _load_history(uid)
        available = sorted({e.get("type", "") for e in entries if e.get("type")})
        if not available:
            await q.message.reply_text(
                f"📭 *No History Yet*\n`{DIV}`\n_Nothing to filter\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
            return
        rows = []
        row  = []
        for t in available:
            row.append(InlineKeyboardButton(
                f"{_badge(t)} {t.capitalize()}",
                callback_data=f"filter_type:{t}"
            ))
            if len(row) == 3:
                rows.append(row)
                row = []
        if row:
            rows.append(row)
        rows.append([InlineKeyboardButton("✖ Cancel", callback_data="filter_cancel")])
        await q.message.reply_text(
            f"🔍 *Filter History*\n`{DIV}`\n_Choose a type:_",
            parse_mode=ParseMode.MARKDOWN_V2,
            reply_markup=InlineKeyboardMarkup(rows),
        )
        return

    if data.startswith("filter_type:"):
        ft      = data.split(":", 1)[1]
        entries = _load_history(uid, filter_type=ft)
        if not entries:
            await q.message.reply_text(
                f"📭 *No {_e(ft.capitalize())} entries found\\.*",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
            return
        lines = [f"{_badge(ft)} *{_e(ft.capitalize())} History*  _{len(entries)} entries_\n`{DIV}`"]
        for i, e in enumerate(reversed(entries), 1):
            ts      = _e(e.get("ts", "?"))
            preview = _e(e.get("raw", "")[:55])
            fmt     = e.get("format", "")
            fmt_str = f" · _{_e(fmt)}_" if fmt else ""
            lines.append(f"*{i:02d}*{fmt_str}  `{preview}`\n      __{ts}__")
            if i < len(entries):
                lines.append("")
        await q.message.reply_text("\n".join(lines), parse_mode=ParseMode.MARKDOWN_V2)
        return

    if data == "filter_cancel":
        try:
            await q.message.delete()
        except Exception:
            pass
        return

    # ── Export history ───────────────────────────────────────────────────────
    if data == "export_history":
        entries = _load_history(uid)
        if not entries:
            await q.message.reply_text(
                f"📭 *No History to Export*\n`{DIV}`\n_Scan something first\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
            return
        payload = json.dumps(entries, ensure_ascii=False, indent=2)
        bio     = io.BytesIO(payload.encode())
        bio.name = "scanvault_history.json"
        await q.message.reply_document(
            document=bio,
            caption=f"📤 *History Export*  _({len(entries)} entries)_",
            parse_mode=ParseMode.MARKDOWN_V2,
        )
        return

    # ── Clear history ────────────────────────────────────────────────────────
    if data == "clear_history":
        count = len(USER_DATA[uid]["history"])
        USER_DATA[uid]["history"] = []
        if count == 0:
            await q.message.reply_text(
                "📭 *Nothing to clear*\n_Your history was already empty\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
        else:
            await q.message.reply_text(
                f"🗑 *History Cleared*\n`{DIV}`\n"
                f"_{_e(str(count))} {'entry' if count == 1 else 'entries'} deleted\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
        name = q.from_user.first_name or "there"
        text, kb = _welcome(name, uid)
        try:
            await q.message.edit_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
        except Exception:
            pass
        return

# ---------------------------------------------------------------------------
# Periodic TTL cleanup job
# ---------------------------------------------------------------------------

async def _ttl_cleanup_job(ctx: ContextTypes.DEFAULT_TYPE) -> None:
    _cleanup_idle_users()

# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    app = Application.builder().token(BOT_TOKEN).build()

    # /start + plain text (QR generate or welcome)
    app.add_handler(MessageHandler(filters.COMMAND | filters.TEXT, handle_start))

    # Photo and document (original quality) image uploads
    app.add_handler(MessageHandler(filters.PHOTO | filters.Document.IMAGE, handle_image))

    # All inline button callbacks
    app.add_handler(CallbackQueryHandler(handle_callback))

    # Hourly idle-user cleanup to prevent memory leak
    app.job_queue.run_repeating(_ttl_cleanup_job, interval=3600, first=3600)

    logger.info("ScanVault bot started.")
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()

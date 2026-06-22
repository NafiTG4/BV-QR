"""
ScanVault — Telegram QR & Barcode Scanner Bot
==============================================
- Zero commands: everything via inline buttons
- Premium formatting with emoji, dividers, clean layout
- AES-256-GCM encrypted history (in-memory, privacy-first)
- zxing-cpp decoder (no system library dependency)
- URL intelligence: short URL expand, title fetch, phishing detection
- Smart parsers: WiFi, vCard, MeCard, Crypto, UPI, Geo, mailto, SMS, tel
- Rate limiting, multi-code detection, no disk writes
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

MAX_HISTORY     = 20
RATE_LIMIT_SEC  = 5
MAX_CODES_SHOWN = 10

SUSPICIOUS_TLDS = {".tk", ".ml", ".ga", ".cf", ".gq", ".xyz", ".top", ".pw"}

# ---------------------------------------------------------------------------
# In-memory user store
# { uid: { "privacy": bool, "history": [encrypted_str, ...], "last_scan": float } }
# ---------------------------------------------------------------------------
USER_DATA: dict[int, dict] = defaultdict(
    lambda: {"privacy": False, "history": [], "last_scan": 0.0}
)

# ---------------------------------------------------------------------------
# AES-256-GCM
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

def _save(uid: int, kind: str, raw: str) -> None:
    if USER_DATA[uid]["privacy"]:
        return
    entry = {
        "ts":   datetime.now(timezone.utc).strftime("%d %b %Y, %H:%M UTC"),
        "type": kind,
        "raw":  raw[:200],
    }
    h = USER_DATA[uid]["history"]
    h.append(_encrypt(json.dumps(entry)))
    if len(h) > MAX_HISTORY:
        h.pop(0)


def _load_history(uid: int) -> list[dict]:
    out = []
    for enc in USER_DATA[uid]["history"]:
        try:
            out.append(json.loads(_decrypt(enc)))
        except Exception:
            pass
    return out

# ---------------------------------------------------------------------------
# Markdown escape (MarkdownV2)
# ---------------------------------------------------------------------------

def _e(text: str) -> str:
    """Escape special chars for Telegram MarkdownV2."""
    for ch in r"\_*[]()~`>#+-=|{}.!":
        text = text.replace(ch, f"\\{ch}")
    return text

# ---------------------------------------------------------------------------
# Divider & formatting helpers
# ---------------------------------------------------------------------------

DIV = "┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄"

def _badge(kind: str) -> str:
    """Return emoji badge for content type."""
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

# ---------------------------------------------------------------------------
# URL intelligence
# ---------------------------------------------------------------------------

SHORTENERS = {
    "bit.ly", "t.ly", "tinyurl.com", "ow.ly", "goo.gl",
    "short.io", "rb.gy", "is.gd", "buff.ly", "cutt.ly",
}

async def _expand(url: str) -> str | None:
    host = urllib.parse.urlparse(url).netloc.lower().lstrip("www.")
    if host not in SHORTENERS:
        return None
    try:
        async with httpx.AsyncClient(follow_redirects=True, timeout=6) as c:
            r = await c.head(url)
            final = str(r.url)
            return final if final != url else None
    except Exception:
        return None


async def _title(url: str) -> str:
    try:
        async with httpx.AsyncClient(follow_redirects=True, timeout=6) as c:
            r    = await c.get(url, headers={"User-Agent": "Mozilla/5.0"})
            m    = re.search(r"<title[^>]*>(.*?)</title>",
                             r.text[:8000], re.I | re.S)
            return m.group(1).strip()[:80] if m else ""
    except Exception:
        return ""


def _phishing(url: str) -> bool:
    host = urllib.parse.urlparse(url).netloc.lower()
    # Bare IP address
    if re.match(r"^\d{1,3}(\.\d{1,3}){3}(:\d+)?$", host):
        return True
    # Suspicious free TLDs
    if any(host.endswith(t) for t in SUSPICIOUS_TLDS):
        return True
    # Homoglyph / typosquatting: digits substituted for letters in popular brands
    domain_part = host.split(":")[0]  # strip port
    squatted = re.sub(r"[0@]", "o", re.sub(r"1|!", "l", domain_part))
    POPULAR = {"paypal", "google", "facebook", "amazon", "apple", "microsoft",
               "netflix", "instagram", "whatsapp", "telegram", "twitter", "x"}
    for brand in POPULAR:
        if brand in squatted and not domain_part.endswith(f"{brand}.com"):
            return True
    # Excessive subdomains (e.g. paypal.com.evil.xyz)
    parts = domain_part.split(".")
    if len(parts) > 4:
        return True
    return False

# ---------------------------------------------------------------------------
# Image decoder
# ---------------------------------------------------------------------------

def _decode(img_bytes: bytes) -> list[str]:
    arr = np.frombuffer(img_bytes, dtype=np.uint8)
    img = cv2.imdecode(arr, cv2.IMREAD_COLOR)
    if img is None:
        return []

    results: list[str] = []

    # Primary: zxing-cpp (pure wheel, no system lib)
    try:
        codes = zxingcpp.read_barcodes(cv2.cvtColor(img, cv2.COLOR_BGR2RGB))
        results = [c.text for c in codes if c.text]
    except Exception as ex:
        logger.warning("zxingcpp: %s", ex)

    # Fallback: OpenCV built-in QR
    if not results:
        try:
            det  = cv2.QRCodeDetector()
            data, _, _ = det.detectAndDecodeMulti(img)
            results = [d for d in (data or []) if d]
        except Exception as ex:
            logger.warning("cv2 fallback: %s", ex)

    # Deduplicate, preserve order
    seen: set[str] = set()
    out:  list[str] = []
    for r in results:
        if r not in seen:
            seen.add(r)
            out.append(r)
    return out[:MAX_CODES_SHOWN]

# ---------------------------------------------------------------------------
# Content parsers — return (display_text, buttons_list)
# ---------------------------------------------------------------------------

def _parse(raw: str) -> tuple[str, list[list[InlineKeyboardButton]], str]:
    """Returns (formatted_text, button_rows, content_kind)."""
    r = raw.strip()

    if r.startswith("WIFI:"):             return _p_wifi(r)
    if r.startswith("BEGIN:VCARD"):       return _p_vcard(r)
    if r.startswith("MECARD:"):           return _p_mecard(r)
    if re.match(r"^(bitcoin|ethereum|litecoin|monero):", r, re.I):
                                          return _p_crypto(r)
    if r.startswith("upi://"):            return _p_upi(r)
    if r.startswith("geo:"):              return _p_geo(r)
    if r.startswith("mailto:"):           return _p_mailto(r)
    if r.startswith("smsto:") or r.startswith("sms:"): return _p_sms(r)
    if r.startswith("tel:"):              return _p_tel(r)
    if re.match(r"^https?://", r, re.I): return "", [], "url"  # async handled separately
    return _p_text(r)


def _p_wifi(r: str) -> tuple[str, list, str]:
    m = re.search(r"S:([^;]*)", r); ssid = m.group(1) if m else "?"
    m = re.search(r"P:([^;]*)", r); pwd  = m.group(1) if m else ""
    m = re.search(r"T:([^;]*)", r); enc  = m.group(1) if m else "?"

    text = (
        f"📶 *Wi\\-Fi Network*\n"
        f"`{DIV}`\n"
        f"*Network* ›  `{_e(ssid)}`\n"
        f"*Password* ›  `{_e(pwd) if pwd else '—'}`\n"
        f"*Security* ›  `{_e(enc)}`"
    )
    buttons: list[list[InlineKeyboardButton]] = []
    return text, buttons, "wifi"


def _p_vcard(r: str) -> tuple[str, list, str]:
    m_fn    = re.search(r"FN:(.*)",        r)
    m_tel   = re.search(r"TEL[^:]*:(.*)",  r)
    m_email = re.search(r"EMAIL[^:]*:(.*)",r)
    m_org   = re.search(r"ORG:(.*)",       r)
    name  = m_fn.group(1).strip()    if m_fn    else "?"
    phone = m_tel.group(1).strip()   if m_tel   else ""
    email = m_email.group(1).strip() if m_email else ""
    org   = m_org.group(1).strip()   if m_org   else ""

    lines = [f"👤 *Contact Card*\n`{DIV}`"]
    lines.append(f"*Name* ›  {_e(name)}")
    if org:   lines.append(f"*Company* ›  {_e(org)}")
    if phone: lines.append(f"*Phone* ›  `{_e(phone)}`")
    if email: lines.append(f"*Email* ›  `{_e(email)}`")
    lines.append(f"\n_Tap below to get in touch_")

    btns: list[list[InlineKeyboardButton]] = []
    row = []
    if phone: row.append(InlineKeyboardButton("📞 Call", url=f"tel:{phone}"))
    if email: row.append(InlineKeyboardButton("✉️ Email", url=f"mailto:{email}"))
    if row: btns.append(row)
    return "\n".join(lines), btns, "vcard"


def _p_mecard(r: str) -> tuple[str, list, str]:
    m_n   = re.search(r"N:([^;]*)",     r)
    m_tel = re.search(r"TEL:([^;]*)",   r)
    m_em  = re.search(r"EMAIL:([^;]*)", r)
    name  = m_n.group(1)   if m_n   else "?"
    phone = m_tel.group(1) if m_tel else ""
    email = m_em.group(1)  if m_em  else ""

    lines = [f"👤 *Contact Card*\n`{DIV}`"]
    lines.append(f"*Name* ›  {_e(name)}")
    if phone: lines.append(f"*Phone* ›  `{_e(phone)}`")
    if email: lines.append(f"*Email* ›  `{_e(email)}`")

    btns: list[list[InlineKeyboardButton]] = []
    row = []
    if phone: row.append(InlineKeyboardButton("📞 Call", url=f"tel:{phone}"))
    if email: row.append(InlineKeyboardButton("✉️ Email", url=f"mailto:{email}"))
    if row: btns.append(row)
    return "\n".join(lines), btns, "mecard"


def _p_crypto(r: str) -> tuple[str, list, str]:
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

    return "\n".join(lines), [], "crypto"


def _p_upi(r: str) -> tuple[str, list, str]:
    params = dict(urllib.parse.parse_qsl(urllib.parse.urlparse(r).query))
    pa = params.get("pa", "?")
    pn = params.get("pn", "")
    am = params.get("am", "")
    tn = params.get("tn", "")

    lines = [f"💳 *UPI Payment*\n`{DIV}`"]
    lines.append(f"*UPI ID* ›  `{_e(pa)}`")
    if pn: lines.append(f"*Payee* ›  {_e(pn)}")
    if am: lines.append(f"*Amount* ›  ₹ `{_e(am)}`")
    if tn: lines.append(f"*Note* ›  {_e(tn)}")

    btns = [[InlineKeyboardButton("💳 Pay Now", url=r)]]
    return "\n".join(lines), btns, "upi"


def _p_geo(r: str) -> tuple[str, list, str]:
    m = re.match(r"geo:(-?\d+\.?\d*),(-?\d+\.?\d*)", r)
    if not m:
        return f"📍 *Location*\n`{DIV}`\n`{_e(r)}`", [], "geo"
    lat, lon = m.group(1), m.group(2)
    maps = f"https://maps.google.com/?q={lat},{lon}"
    text = (
        f"📍 *Location*\n`{DIV}`\n"
        f"*Latitude* ›  `{lat}`\n"
        f"*Longitude* ›  `{lon}`"
    )
    btns = [[InlineKeyboardButton("🗺 Open in Maps", url=maps)]]
    return text, btns, "geo"


def _p_mailto(r: str) -> tuple[str, list, str]:
    addr    = r[7:].split("?")[0]
    params  = dict(urllib.parse.parse_qsl(urllib.parse.urlparse(r).query))
    subject = params.get("subject", "")
    lines   = [f"✉️ *Email Address*\n`{DIV}`", f"*To* ›  `{_e(addr)}`"]
    if subject: lines.append(f"*Subject* ›  {_e(subject)}")
    btns = [[InlineKeyboardButton("✉️ Send Email", url=r)]]
    return "\n".join(lines), btns, "email"


def _p_sms(r: str) -> tuple[str, list, str]:
    m   = re.match(r"(?:smsto?):([^:?]+):?(.*)", r)
    num = m.group(1) if m else "?"
    msg = m.group(2) if m else ""
    lines = [f"💬 *SMS*\n`{DIV}`", f"*To* ›  `{_e(num)}`"]
    if msg: lines.append(f"*Message* ›  {_e(msg)}")
    btns = [[InlineKeyboardButton("💬 Send SMS", url=f"sms:{num}")]]
    return "\n".join(lines), btns, "sms"


def _p_tel(r: str) -> tuple[str, list, str]:
    num  = r[4:]
    text = f"📞 *Phone Number*\n`{DIV}`\n*Number* ›  `{_e(num)}`"
    btns = [[InlineKeyboardButton("📞 Call", url=r)]]
    return text, btns, "tel"


def _p_text(r: str) -> tuple[str, list, str]:
    preview = r[:500]
    # Use blockquote-style (no backtick wrapping) to avoid MarkdownV2 parse errors
    # when raw data contains backticks or other special characters
    text = f"📄 *Scanned Data*\n`{DIV}`\n{_e(preview)}"
    return text, [], "text"

# ---------------------------------------------------------------------------
# Welcome / menu message builder
# ---------------------------------------------------------------------------

def _welcome(name: str, uid: int) -> tuple[str, InlineKeyboardMarkup]:
    priv = USER_DATA[uid]["privacy"]
    count = len(USER_DATA[uid]["history"])
    priv_label = "🔒 Privacy  ON" if priv else "🔓 Privacy  OFF"

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
        f"`{DIV}`\n"
        f"_No image is ever saved to disk\\._"
    )
    btns = [
        [
            InlineKeyboardButton(priv_label,       callback_data="toggle_privacy"),
        ],
        [
            InlineKeyboardButton(
                f"📋 History  ({count} scan{'s' if count != 1 else ''})",
                callback_data="show_history",
            ),
            InlineKeyboardButton("🗑 Clear",               callback_data="clear_history"),
        ],
    ]
    return text, InlineKeyboardMarkup(btns)

# ---------------------------------------------------------------------------
# URL result (async, enriched)
# ---------------------------------------------------------------------------

async def _send_url(
    update: Update,
    edit_msg,
    raw: str,
    prefix: str,
    uid: int,
) -> None:
    # Run expand and title fetch concurrently — they are independent
    expanded, page_title = await asyncio.gather(
        _expand(raw),
        _title(raw),
        return_exceptions=False,
    )

    final  = expanded if expanded else raw
    risky  = _phishing(final)
    domain = urllib.parse.urlparse(final).netloc or final[:50]

    # Fetch title for the expanded URL if we got a redirect and title was empty
    if expanded and not page_title:
        page_title = await _title(final)

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

    text = "\n".join(lines)
    btns = [[InlineKeyboardButton("🌐 Open Link", url=final)]]
    kb   = InlineKeyboardMarkup(btns)

    # Save URL to history now that we have all enriched data
    _save(uid, "url", raw)

    try:
        if edit_msg:
            await edit_msg.edit_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
        else:
            await update.message.reply_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
    except Exception as ex:
        logger.error("_send_url edit/reply failed: %s", ex)
        # Fallback: plain text so "Scanning..." doesn't get stuck
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
    """Handle /start command and plain text messages that aren't images."""
    user = update.effective_user
    name = user.first_name or "there"
    uid  = user.id
    text, kb = _welcome(name, uid)
    await update.message.reply_text(text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)


async def handle_image(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    uid = update.effective_user.id

    if _is_rate_limited(uid):
        await update.message.reply_text(
            "⏳ *Slow down a bit\\!*\n_Please wait a few seconds between scans\\._",
            parse_mode=ParseMode.MARKDOWN_V2,
        )
        return
    _touch_rate(uid)

    status = await update.message.reply_text("🔍 _Scanning\\.\\.\\._", parse_mode=ParseMode.MARKDOWN_V2)

    # Download image into memory only — no disk write
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

    codes = _decode(img_bytes)

    if not codes:
        await status.edit_text(
            "🔍 *Nothing found*\n"
            "`┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄`\n"
            "No QR code or barcode was detected\\.\n\n"
            "*Tips*\n"
            "› Make sure the code is fully visible\n"
            "› Use a well\\-lit, clear photo\n"
            "› Try sending as a *file* for higher quality",
            parse_mode=ParseMode.MARKDOWN_V2,
        )
        return

    total = len(codes)

    for idx, raw in enumerate(codes, 1):
        prefix = f"*\\[{idx} / {total}\\]*  " if total > 1 else ""
        text, btns, kind = _parse(raw)

        if kind == "url":
            # _send_url handles both history save and error fallback internally
            await _send_url(update, status if idx == 1 else None, raw, prefix, uid)
        else:
            _save(uid, kind, raw)
            full = prefix + text if prefix else text
            kb   = InlineKeyboardMarkup(btns) if btns else None
            if idx == 1:
                await status.edit_text(full, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)
            else:
                await update.message.reply_text(full, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=kb)


async def handle_callback(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> None:
    q   = update.callback_query
    uid = q.from_user.id
    await q.answer()

    data = q.data or ""

    # ── Toggle privacy ──────────────────────────────────────────────────────
    if data == "toggle_privacy":
        current = USER_DATA[uid]["privacy"]
        USER_DATA[uid]["privacy"] = not current
        new_state = not current
        state_text = "enabled" if new_state else "disabled"
        icon       = "🔒" if new_state else "🔓"

        note = (
            f"{icon} *Privacy Mode {_e(state_text.capitalize())}*\n"
            f"`{DIV}`\n"
            + (
                "_Your scans will no longer be stored\\._"
                if new_state else
                "_Your scans will now be saved \\(encrypted\\)\\._"
            )
        )
        await q.message.reply_text(note, parse_mode=ParseMode.MARKDOWN_V2)

        # Refresh the welcome message keyboard
        name = q.from_user.first_name or "there"
        new_text, new_kb = _welcome(name, uid)
        try:
            await q.message.edit_text(new_text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=new_kb)
        except Exception:
            pass
        return

    # ── Show history ────────────────────────────────────────────────────────
    if data == "show_history":
        if USER_DATA[uid]["privacy"]:
            await q.message.reply_text(
                "🔒 *Privacy Mode is On*\n"
                "`┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄`\n"
                "_Scan history is disabled\\. Toggle privacy off to start logging\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
            return

        entries = _load_history(uid)
        if not entries:
            await q.message.reply_text(
                "📭 *No History Yet*\n"
                "`┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄┄`\n"
                "_Start scanning and your results will appear here\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )
            return

        lines = [f"📋 *Scan History*  _{len(entries)} entries_\n`{DIV}`"]
        for i, e in enumerate(reversed(entries), 1):
            kind    = e.get("type", "?")
            ts      = _e(e.get("ts", "?"))
            preview = _e(e.get("raw", "")[:55])
            badge   = _badge(kind)
            lines.append(f"{badge}  *{i:02d}*  `{preview}`\n      __{ts}__")
            if i < len(entries):
                lines.append("")

        await q.message.reply_text(
            "\n".join(lines), parse_mode=ParseMode.MARKDOWN_V2
        )
        return

    # ── Clear history ───────────────────────────────────────────────────────
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
                f"🗑 *History Cleared*\n"
                f"`{DIV}`\n"
                f"_{_e(str(count))} {'entry' if count == 1 else 'entries'} deleted\\._",
                parse_mode=ParseMode.MARKDOWN_V2,
            )

        # Refresh welcome keyboard counts
        name = q.from_user.first_name or "there"
        new_text, new_kb = _welcome(name, uid)
        try:
            await q.message.edit_text(new_text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=new_kb)
        except Exception:
            pass
        return

# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def main() -> None:
    app = Application.builder().token(BOT_TOKEN).build()

    # /start command + plain text messages both show the welcome screen
    app.add_handler(MessageHandler(filters.COMMAND | filters.TEXT, handle_start))

    # Photos and documents (original quality uploads)
    app.add_handler(MessageHandler(filters.PHOTO | filters.Document.IMAGE, handle_image))

    # All button callbacks
    app.add_handler(CallbackQueryHandler(handle_callback))

    logger.info("ScanVault bot started.")
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()

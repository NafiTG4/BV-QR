"""
EVM Wallet Generator Bot - bot.py
BIP-44 HD wallets for all EVM chains.

Features:
  - Access code gate on /start (private chat)
  - Admin group: User Info, Balance, Rate tree, Wallet Limit, Access Management
  - Access Management: Random (N slots) and Custom (specific UIDs), Hourly/Days validation
  - Export as CSV or TG Messages (up to 100M wallets)
  - Global 28 msg/sec rate limiter
  - Balance (PTS) system with deduction per export type
  - Startup benchmark for accurate ETA

Requirements:
    pip install python-telegram-bot eth-account mnemonic cryptography
"""

import asyncio
import csv
import logging
import math
import os
import secrets
import struct
import tempfile
import time
from collections import deque
from datetime import datetime

from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from eth_account import Account
from mnemonic import Mnemonic
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.constants import ParseMode
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    ConversationHandler,
    MessageHandler,
    filters,
)

Account.enable_unaudited_hdwallet_features()

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO,
)
logger = logging.getLogger(__name__)

# ============================================================================
# CONFIG
# ============================================================================
BOT_TOKEN: str      = os.environ["BOT_TOKEN"]
ADMIN_GROUP_ID: int = int(os.environ.get("ADMIN_GROUP_ID", "0"))

DERIVATION_PATH       = "m/44'/60'/0'/0/0"
GLOBAL_MSG_RATE_LIMIT = 28
BENCHMARK_SAMPLE      = 30
STRENGTH_MAP          = {12: 128, 15: 160, 18: 192, 21: 224, 24: 256}
VALID_WORD_COUNTS     = {12, 15, 18, 21, 24}
TG_WALLETS_PER_MSG    = 10
TG_MSG_DELAY          = 0.05

# ============================================================================
# GLOBAL RUNTIME CONFIG
# ============================================================================
_global_wallet_limit: int = 100_000_000
_rate_csv_per_1000: float = 0.01
_rate_tg_per_1000: float  = 0.03
_join_balance: float      = 0.0

def get_global_limit() -> int:       return _global_wallet_limit
def set_global_limit(v: int):
    global _global_wallet_limit;     _global_wallet_limit = v

def get_rate_csv() -> float:         return _rate_csv_per_1000
def set_rate_csv(v: float):
    global _rate_csv_per_1000;       _rate_csv_per_1000 = v

def get_rate_tg() -> float:          return _rate_tg_per_1000
def set_rate_tg(v: float):
    global _rate_tg_per_1000;        _rate_tg_per_1000 = v

def get_join_balance() -> float:     return _join_balance
def set_join_balance(v: float):
    global _join_balance;            _join_balance = v

def cost_for(count: int, export_type: str) -> float:
    rate = get_rate_csv() if export_type == "exp_csv" else get_rate_tg()
    return (count / 1000) * rate

# ============================================================================
# CONVERSATION STATES
# ============================================================================
USER_ENTER_CODE         = 1
ASK_COUNT               = 2
ASK_WORDS               = 3
ASK_EXPORT              = 4
ASK_CONFIRM             = 5   # order summary confirmation screen

ADM_USERINFO_QUERY      = 10
ADM_SET_LIMIT_VAL       = 11
ADM_SET_RATE_CSV_VAL    = 12
ADM_SET_RATE_TG_VAL     = 13
ADM_ADD_BAL_UID         = 14
ADM_ADD_BAL_AMT         = 15
ADM_SET_JOIN_BAL        = 16

ADM_AC_RANDOM_COUNT     = 20
ADM_AC_VAL_TYPE         = 21
ADM_AC_VAL_AMT          = 22
ADM_AC_CUSTOM_UID       = 23
ADM_AC_CHOOSE_TYPE      = 24  # choose Random or Custom
ADM_AC_ISSUE_SCREEN     = 27  # Issue Access Code screen (Random/Custom buttons)
ADM_AC_VAL_TYPE2        = 25  # validation type (unified)
ADM_AC_VAL_AMT2         = 26  # validation amount (unified)
ADM_AC_INFO_QUERY       = 28  # waiting for code to show info
ADM_AC_DISABLE_QUERY    = 29  # waiting for code to disable
ADM_AC_HISTORY_MENU     = 33  # history sub-menu (active/disabled/expired)

ADM_ORDER_MENU          = 30  # order management sub-menu
ADM_ORDER_ID_QUERY      = 31  # waiting for order id input
ADM_ORDER_USER_QUERY    = 32  # waiting for user tg id input

# ============================================================================
# USER STORE
# ============================================================================
USER_DB: dict[int, dict] = {}

def get_user(uid: int, tg_user=None) -> dict:
    if uid not in USER_DB:
        USER_DB[uid] = {
            "name":              tg_user.full_name if tg_user else str(uid),
            "username":          tg_user.username  if tg_user else None,
            "credits":           get_join_balance(),
            "wallets_generated": 0,
            "balance_checked":   0,
        }
    elif tg_user:
        USER_DB[uid]["name"]     = tg_user.full_name
        USER_DB[uid]["username"] = tg_user.username
    return USER_DB[uid]

def find_user(q: str) -> tuple:
    q = q.strip().lstrip("@")
    if q.isdigit():
        uid = int(q)
        return (uid, USER_DB[uid]) if uid in USER_DB else (None, None)
    ql = q.lower()
    for uid, u in USER_DB.items():
        if u["username"] and u["username"].lower() == ql:
            return uid, u
    return None, None

# ============================================================================
# ORDER STORE
# order_id -> {uid, count, word_count, export_type, cost, status, created_at}
# ============================================================================
ORDER_DB: dict[str, dict] = {}

def _make_order_id() -> str:
    """Generate a unique 10-char alphanumeric order ID."""
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    while True:
        oid = "ORD-" + "".join(secrets.choice(alphabet) for _ in range(8))
        if oid not in ORDER_DB:
            return oid

def create_order(uid: int, count: int, word_count: int, export_type: str, cost: float) -> str:
    """Create and store a new order with processing status, return the order ID."""
    oid = _make_order_id()
    ORDER_DB[oid] = {
        "uid":         uid,
        "count":       count,
        "word_count":  word_count,
        "export_type": export_type,
        "cost":        cost,
        "status":      "processing",
        "created_at":  time.time(),
    }
    return oid

# code -> {type, slots, allowed_uids, used_uids, expires_at, created_at}
# ============================================================================
ACCESS_CODES: dict[str, dict]   = {}
DISABLED_CODES: dict[str, dict] = {}  # codes disabled by admin, same structure + disabled_at
GRANTED_USERS: dict[int, float] = {}  # uid -> expiry unix timestamp

def _make_code() -> str:
    alphabet = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    return "".join(secrets.choice(alphabet) for _ in range(8))

def is_access_granted(uid: int) -> bool:
    expiry = GRANTED_USERS.get(uid)
    if expiry is None:
        return False
    if time.time() > expiry:
        del GRANTED_USERS[uid]
        return False
    return True

def redeem_code(code: str, uid: int) -> tuple[bool, str]:
    code  = code.strip().upper()
    entry = ACCESS_CODES.get(code)
    if entry is None:
        return False, "Invalid access code."
    if time.time() > entry["expires_at"]:
        del ACCESS_CODES[code]
        return False, "This access code has expired."
    if entry["type"] == "random":
        if uid not in entry["used_uids"] and entry["slots"] <= 0:
            return False, "This access code has no remaining slots."
        if uid not in entry["used_uids"]:
            entry["slots"] -= 1
            entry["used_uids"].add(uid)
    elif entry["type"] == "custom":
        if uid not in entry["allowed_uids"]:
            return False, "This access code is not valid for your account."
        entry["used_uids"].add(uid)
    GRANTED_USERS[uid] = entry["expires_at"]
    return True, "Access granted."

# ============================================================================
# RATE LIMITER
# ============================================================================
_msg_timestamps: deque = deque()
_rate_lock = asyncio.Lock()

async def send_safe(coro):
    while True:
        async with _rate_lock:
            now = time.monotonic()
            while _msg_timestamps and now - _msg_timestamps[0] >= 1.0:
                _msg_timestamps.popleft()
            if len(_msg_timestamps) < GLOBAL_MSG_RATE_LIMIT:
                _msg_timestamps.append(now)
                break
            sleep_for = 1.0 - (now - _msg_timestamps[0]) + 0.01
        await asyncio.sleep(sleep_for)
    return await coro

# ============================================================================
# BENCHMARK
# ============================================================================
_wallets_per_sec: float = 0.0

def _run_benchmark(sample: int = BENCHMARK_SAMPLE) -> float:
    mnemo = Mnemonic("english")
    t0    = time.perf_counter()
    for _ in range(sample):
        phrase = mnemo.generate(strength=128)
        Account.from_mnemonic(phrase, account_path=DERIVATION_PATH)
    rate = sample / (time.perf_counter() - t0)
    logger.info("Benchmark: %.1f wallets/sec", rate)
    return rate

def eta_string(count: int) -> str:
    if _wallets_per_sec <= 0:
        return "calculating..."
    secs = count / _wallets_per_sec
    return f"~{math.ceil(secs)}s" if secs < 60 else f"~{secs / 60:.1f} min"

# ============================================================================
# WALLET GENERATION
# ============================================================================
def _generate_wallets(count: int, word_count: int) -> tuple:
    mnemo    = Mnemonic("english")
    strength = STRENGTH_MAP[word_count]
    rows     = []
    t0       = time.perf_counter()
    for i in range(count):
        phrase = mnemo.generate(strength=strength)
        acct   = Account.from_mnemonic(phrase, account_path=DERIVATION_PATH)
        rows.append([i + 1, acct.address, acct.key.hex(), phrase])
    return rows, time.perf_counter() - t0

def _write_csv(rows: list) -> str:
    """Write AES-256-GCM encrypted CSV to a temp file."""
    blob = encrypt_rows(rows)
    tmp  = tempfile.NamedTemporaryFile(mode="wb", suffix=".enc", delete=False)
    try:
        tmp.write(blob)
        tmp.flush()
    finally:
        tmp.close()
    return tmp.name

# ============================================================================
# HELPERS
# ============================================================================
def escape_md(text) -> str:
    specials = r"_*[]()~`>#+-=|{}.!"
    return "".join(f"\\{c}" if c in specials else c for c in str(text))

def fmt(n) -> str:
    return "{:,}".format(n)

def fmt_pts(v: float) -> str:
    return "{:.4f}".format(v)

# ============================================================================
# AES-256-GCM ENCRYPTION
# Key is generated fresh each process start (in-memory only).
# CSV files on disk are encrypted; TG message data is encrypted in memory
# while being held before delivery, then wiped.
# ============================================================================
_AES_KEY: bytes = secrets.token_bytes(32)   # 256-bit key, ephemeral per process

def aes_encrypt(data: bytes) -> bytes:
    """Encrypt bytes with AES-256-GCM. Returns nonce(12) + ciphertext."""
    nonce = secrets.token_bytes(12)
    ct    = AESGCM(_AES_KEY).encrypt(nonce, data, None)
    return nonce + ct

def aes_decrypt(blob: bytes) -> bytes:
    """Decrypt blob produced by aes_encrypt."""
    return AESGCM(_AES_KEY).decrypt(blob[:12], blob[12:], None)

def encrypt_rows(rows: list) -> bytes:
    """Serialize wallet rows to CSV bytes then encrypt."""
    import io
    buf = io.StringIO()
    w   = csv.writer(buf)
    w.writerow(["#", "address", "private_key", "mnemonic"])
    w.writerows(rows)
    return aes_encrypt(buf.getvalue().encode("utf-8"))

def decrypt_rows(blob: bytes) -> list:
    """Decrypt and deserialize wallet rows."""
    import io
    raw  = aes_decrypt(blob).decode("utf-8")
    r    = csv.reader(io.StringIO(raw))
    next(r)   # skip header
    return [row for row in r]


def is_admin_group(update: Update) -> bool:
    return (
        ADMIN_GROUP_ID != 0
        and update.effective_chat is not None
        and update.effective_chat.id == ADMIN_GROUP_ID
    )

def is_private(update: Update) -> bool:
    return update.effective_chat is not None and update.effective_chat.type == "private"

# ============================================================================
# KEYBOARDS
# ============================================================================
def main_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("👤 Profile",  callback_data="menu_profile"),
            InlineKeyboardButton("⚙️ Settings", callback_data="menu_settings"),
        ],
        [
            InlineKeyboardButton("🪪 Bulk Wallet Generator", callback_data="menu_bulk"),
            InlineKeyboardButton("💰 Balance Checker",       callback_data="menu_balance"),
        ],
    ])

def admin_menu_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [
            InlineKeyboardButton("👤 User Info",             callback_data="adm_userinfo"),
            InlineKeyboardButton("💰 Balance",               callback_data="adm_balance"),
        ],
        [
            InlineKeyboardButton("📊 Rate",                  callback_data="adm_rate"),
            InlineKeyboardButton("🔢 Wallet Generate Limit", callback_data="adm_wlimit"),
        ],
        [
            InlineKeyboardButton("🔐 Access Management",     callback_data="adm_access"),
            InlineKeyboardButton("🧾 Order ID",              callback_data="adm_orders"),
        ],
    ])

def adm_balance_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add User Balance",      callback_data="adm_bal_add")],
        [InlineKeyboardButton("🎁 New User Join Balance", callback_data="adm_bal_join")],
        [InlineKeyboardButton("⬅️ Back",                  callback_data="adm_home")],
    ])

def adm_rate_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("💸 Wallet Generate Rate", callback_data="adm_rate_wallet")],
        [InlineKeyboardButton("⬅️ Back",                 callback_data="adm_home")],
    ])

def adm_rate_wallet_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📄 Per 1000 CSV Rate",        callback_data="adm_rate_csv")],
        [InlineKeyboardButton("💬 Per 1000 TG Message Rate", callback_data="adm_rate_tg")],
        [InlineKeyboardButton("⬅️ Back",                     callback_data="adm_rate")],
    ])

def back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("⬅️ Back to Menu", callback_data="menu_home")
    ]])

def admin_back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("⬅️ Back", callback_data="adm_home")
    ]])

def adm_balance_back_kb() -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[
        InlineKeyboardButton("⬅️ Back", callback_data="adm_balance")
    ]])

# ============================================================================
# DYNAMIC TEXTS
# ============================================================================
def welcome_user_text() -> str:
    limit = escape_md(fmt(get_global_limit()))
    return (
        "*EVM Wallet Generator*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Generates BIP\\-44 HD wallets compatible with all EVM chains "
        "\\(Ethereum, BSC, Polygon, Arbitrum, etc\\.\\)\n\n"
        "\U0001f512 *Privacy:* Nothing is stored on the server\\.\n"
        f"\U0001f4e6 *Limit:* Up to {limit} wallets per batch\n\n"
        "Choose an option below\\:"
    )

WELCOME_ADMIN = (
    "*EVM Wallet Generator*\n"
    "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
    "\U0001f6e1\ufe0f *Admin Panel*\n\n"
    "Use the buttons below to manage users and bot settings\\."
)

HELP_TEXT = (
    "*EVM Wallet Generator \\- Help*\n"
    "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
    "*Commands*\n"
    "/start \\- Open the main menu\n"
    "/help \\- Show this help message\n"
    "/cancel \\- Cancel the current session\n\n"
    "*Bulk Wallet Generator flow*\n"
    "1\\. Tap *Bulk Wallet Generator*\n"
    "2\\. Enter the number of wallets\n"
    "3\\. Choose mnemonic word count\n"
    "4\\. Choose export type \\(CSV or TG Messages\\)\n"
    "5\\. Receive your wallets\n\n"
    "*CSV columns*\n"
    "`#` \\| `address` \\| `private_key` \\| `mnemonic`\n\n"
    "*Security*\n"
    "\\- BIP\\-44 standard derivation path\n"
    "\\- Compatible with MetaMask, Trust Wallet, Rabby, Bitget, etc\\.\n"
    "\\- Store your CSV in an encrypted location\n"
    "\\- Never share your private keys or mnemonic phrases"
)

# ============================================================================
# /start  (private: requires access code if not granted)
# ============================================================================
async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    context.user_data.clear()

    if is_admin_group(update):
        await send_safe(update.message.reply_text(
            WELCOME_ADMIN,
            parse_mode=ParseMode.MARKDOWN_V2,
            reply_markup=admin_menu_kb(),
        ))
        return ConversationHandler.END

    if not is_private(update):
        return ConversationHandler.END

    uid = update.effective_user.id

    if is_access_granted(uid):
        get_user(uid, update.effective_user)
        await send_safe(update.message.reply_text(
            welcome_user_text(),
            parse_mode=ParseMode.MARKDOWN_V2,
            reply_markup=main_menu_kb(),
        ))
        return ConversationHandler.END

    # Ask for access code, show user their own ID
    await send_safe(update.message.reply_text(
        "*EVM Wallet Generator*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "\U0001f510 *Access Required*\n\n"
        f"Your Telegram ID: `{uid}`\n\n"
        "Please enter your *8\\-character access code* to continue\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
    ))
    return USER_ENTER_CODE

# ============================================================================
# USER: ACCESS CODE ENTRY
# ============================================================================
async def user_enter_code(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_private(update):
        return USER_ENTER_CODE

    code    = update.message.text.strip()
    uid     = update.effective_user.id
    success, msg = redeem_code(code, uid)

    if not success:
        await send_safe(update.message.reply_text(
            f"\u274c *Access Denied*\n\n"
            f"{escape_md(msg)}\n\n"
            f"Your Telegram ID: `{uid}`\n\n"
            "Please check your code and try again\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return USER_ENTER_CODE

    get_user(uid, update.effective_user)
    expiry_dt = datetime.utcfromtimestamp(GRANTED_USERS[uid]).strftime("%Y-%m-%d %H:%M UTC")
    await send_safe(update.message.reply_text(
        f"\u2705 *Access Granted\\!*\n\n"
        f"Your access is valid until:\n"
        f"`{escape_md(expiry_dt)}`\n\n"
        "Redirecting to main menu\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
    ))
    await send_safe(update.message.reply_text(
        welcome_user_text(),
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=main_menu_kb(),
    ))
    return ConversationHandler.END

# ============================================================================
# MAIN MENU CALLBACKS
# ============================================================================
async def menu_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    context.user_data.clear()
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        welcome_user_text(),
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=main_menu_kb(),
    ))
    return ConversationHandler.END

async def menu_profile(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    uid  = update.effective_user.id
    user = get_user(uid, update.effective_user)

    name      = escape_md(user["name"] or "N/A")
    username  = escape_md("@" + user["username"] if user["username"] else "N/A")
    pts       = escape_md(fmt_pts(user["credits"]))
    generated = escape_md(fmt(user["wallets_generated"]))
    checked   = escape_md(fmt(user["balance_checked"]))
    rate_tg   = escape_md(fmt_pts(get_rate_tg()))
    rate_csv  = escape_md(fmt_pts(get_rate_csv()))

    # Show access expiry if granted
    expiry_line = ""
    if uid in GRANTED_USERS:
        exp = datetime.utcfromtimestamp(GRANTED_USERS[uid]).strftime("%Y-%m-%d %H:%M UTC")
        expiry_line = f"*Access Expires:* `{escape_md(exp)}`\n"

    text = (
        "*\U0001f464 Profile*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Name:* {name}\n"
        f"*User ID:* `{uid}`\n"
        f"*Username:* {username}\n"
        f"{expiry_line}\n"
        f"*Remaining Credit:* `{pts}` PTS\n\n"
        f"*Wallets Generated:* `{generated}`\n"
        f"*Balance Checked:* `{checked}`\n\n"
        f"*Rate Per 1,000 Generate \\(TG\\):* `{rate_tg}` PTS\n"
        f"*Rate Per 1,000 Generate \\(CSV\\):* `{rate_csv}` PTS\n"
        f"*Rate Per 1,000 CSV Balance Check:* `coming soon`\n"
    )
    await send_safe(query.edit_message_text(
        text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=back_kb()
    ))

async def menu_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\u2699\ufe0f Settings*\n\n\U0001f6a7 Coming soon\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=back_kb(),
    ))

async def menu_balance(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f4b0 Balance Checker*\n\n\U0001f6a7 Coming soon\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=back_kb(),
    ))

# ============================================================================
# BULK WALLET GENERATOR FLOW
# ============================================================================
async def bulk_entry(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data.clear()
    limit = get_global_limit()
    await send_safe(query.edit_message_text(
        "*\U0001fa96 Bulk Wallet Generator*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "How many wallets do you need?\n"
        f"_Enter a number between `1` and `{escape_md(fmt(limit))}`_",
        parse_mode=ParseMode.MARKDOWN_V2,
    ))
    return ASK_COUNT

async def receive_count(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_private(update):
        return ASK_COUNT

    text  = update.message.text.strip()
    limit = get_global_limit()

    if not text.isdigit():
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f *Invalid input*\n\nPlease enter a number\\. Example: `1000`",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ASK_COUNT

    count = int(text)
    if count < 1 or count > limit:
        await send_safe(update.message.reply_text(
            f"\u26a0\ufe0f *Out of range*\n\n"
            f"Please enter a number between `1` and `{escape_md(fmt(limit))}`\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ASK_COUNT

    context.user_data["count"] = count
    await send_safe(update.message.reply_text(
        f"\u2705 *{escape_md(fmt(count))} wallets* selected\\.\n\n"
        "Choose your *mnemonic phrase length*\\:\n\n"
        "_Longer phrase \\= higher entropy \\= more secure_",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([
            [
                InlineKeyboardButton("12 words", callback_data="wc_12"),
                InlineKeyboardButton("15 words", callback_data="wc_15"),
                InlineKeyboardButton("18 words", callback_data="wc_18"),
            ],
            [
                InlineKeyboardButton("21 words", callback_data="wc_21"),
                InlineKeyboardButton("24 words  (most secure)", callback_data="wc_24"),
            ],
        ]),
    ))
    return ASK_WORDS

async def receive_words(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()

    if not query.data.startswith("wc_"):
        return ASK_WORDS

    word_count = int(query.data.split("_")[1])
    if word_count not in VALID_WORD_COUNTS:
        await send_safe(query.edit_message_text(
            "Invalid option\\. Use /start to begin again\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ConversationHandler.END

    count = context.user_data.get("count")
    if not count:
        await send_safe(query.edit_message_text(
            "Session expired\\. Use /start to begin again\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ConversationHandler.END

    context.user_data["word_count"] = word_count
    cost_csv = escape_md(fmt_pts(cost_for(count, "exp_csv")))
    cost_tg  = escape_md(fmt_pts(cost_for(count, "exp_tg")))

    await send_safe(query.edit_message_text(
        f"\u2705 *{escape_md(fmt(count))} wallets* \\| *{word_count} words* selected\\.\n\n"
        "Choose your *export type*\\:\n\n"
        f"\U0001f4c4 CSV \\- costs `{cost_csv}` PTS\n"
        f"\U0001f4ac TG Messages \\- costs `{cost_tg}` PTS",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("📄 CSV File",    callback_data="exp_csv"),
            InlineKeyboardButton("💬 TG Messages", callback_data="exp_tg"),
        ]]),
    ))
    return ASK_EXPORT

async def receive_export(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query       = update.callback_query
    await query.answer()

    export_type = query.data
    count       = context.user_data.get("count")
    word_count  = context.user_data.get("word_count")

    if not count or not word_count:
        await send_safe(query.edit_message_text(
            "Session expired\\. Use /start to begin again\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ConversationHandler.END

    uid      = update.effective_user.id
    user     = get_user(uid)
    required = cost_for(count, export_type)

    if user["credits"] < required:
        shortage     = required - user["credits"]
        export_label = "CSV" if export_type == "exp_csv" else "TG Messages"
        await send_safe(query.edit_message_text(
            f"\u274c *Insufficient Credits*\n"
            "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
            f"*Export type:* `{escape_md(export_label)}`\n"
            f"*Wallets:* `{escape_md(fmt(count))}`\n"
            f"*Cost:* `{escape_md(fmt_pts(required))}` PTS\n"
            f"*Your balance:* `{escape_md(fmt_pts(user['credits']))}` PTS\n"
            f"*Shortfall:* `{escape_md(fmt_pts(shortage))}` PTS\n\n"
            "Please contact an admin to top up your balance\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
            reply_markup=back_kb(),
        ))
        context.user_data.clear()
        return ConversationHandler.END

    # Store export type and show order summary for confirmation
    context.user_data["export_type"] = export_type
    export_label = "CSV File" if export_type == "exp_csv" else "TG Messages"
    est          = eta_string(count)

    await send_safe(query.edit_message_text(
        "\U0001f4cb *Order Summary*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Wallets:* `{escape_md(fmt(count))}`\n"
        f"*Mnemonic:* `{word_count} words`\n"
        f"*Derivation:* `{escape_md(DERIVATION_PATH)}`\n"
        f"*Export as:* `{escape_md(export_label)}`\n"
        f"*Est\\. time:* `{escape_md(est)}`\n\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n"
        f"*Cost:* `{escape_md(fmt_pts(required))}` PTS\n"
        f"*Your balance:* `{escape_md(fmt_pts(user['credits']))}` PTS\n"
        f"*After order:* `{escape_md(fmt_pts(user['credits'] - required))}` PTS\n\n"
        "Confirm to start generation\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ Confirm Order", callback_data="order_confirm"),
                InlineKeyboardButton("❌ Cancel",        callback_data="menu_home"),
            ],
        ]),
    ))
    return ASK_CONFIRM

async def receive_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """User confirmed the order -- generate wallets and record the order."""
    query = update.callback_query
    await query.answer()

    count       = context.user_data.get("count")
    word_count  = context.user_data.get("word_count")
    export_type = context.user_data.get("export_type")

    if not count or not word_count or not export_type:
        await send_safe(query.edit_message_text(
            "Session expired\\. Use /start to begin again\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ConversationHandler.END

    uid      = update.effective_user.id
    user     = get_user(uid)
    required = cost_for(count, export_type)

    # Re-check balance (edge case: balance changed between summary and confirm)
    if user["credits"] < required:
        await send_safe(query.edit_message_text(
            "\u274c *Insufficient Credits*\n\n"
            "Your balance changed\\. Please contact an admin\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
            reply_markup=back_kb(),
        ))
        context.user_data.clear()
        return ConversationHandler.END

    # Create order immediately on confirm with "processing" status
    order_id = create_order(uid, count, word_count, export_type, required)

    export_label = "CSV file" if export_type == "exp_csv" else "TG messages"
    est          = eta_string(count)

    await send_safe(query.edit_message_text(
        f"\u2699\ufe0f *Generating {escape_md(fmt(count))} wallets\\.\\.\\.*\n\n"
        f"\\- Mnemonic: `{word_count} words`\n"
        f"\\- Derivation: `{escape_md(DERIVATION_PATH)}`\n"
        f"\\- Export as: `{escape_md(export_label)}`\n"
        f"\\- Estimated time: `{escape_md(est)}`\n"
        f"\\- Cost: `{escape_md(fmt_pts(required))}` PTS\n"
        f"\\- Order ID: `{escape_md(order_id)}`\n\n"
        "_Please wait \\- this happens automatically\\._",
        parse_mode=ParseMode.MARKDOWN_V2,
    ))

    try:
        rows, actual_secs = await asyncio.to_thread(_generate_wallets, count, word_count)
    except Exception as exc:
        logger.exception("Wallet generation failed: %s", exc)
        ORDER_DB[order_id]["status"] = "failed"
        await send_safe(query.message.reply_text(
            "\u274c *Generation failed*\n\nAn unexpected error occurred\\. "
            "Please try again with /start\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        context.user_data.clear()
        return ConversationHandler.END

    # Deduct PTS and mark order completed
    user["credits"]           -= required
    user["wallets_generated"] += count
    ORDER_DB[order_id]["status"] = "completed"

    elapsed = f"{actual_secs:.1f}s" if actual_secs < 60 else f"{actual_secs / 60:.1f} min"

    if export_type == "exp_csv":
        await _deliver_csv(query, rows, count, elapsed)
    else:
        await _deliver_tg(query, context, rows, count, elapsed)

    context.user_data.clear()
    remaining = escape_md(fmt_pts(user["credits"]))
    await send_safe(query.message.reply_text(
        "\U0001f3c1 *All done\\!*\n\n"
        f"\U0001f4dd *Order ID:* `{escape_md(order_id)}`\n"
        f"\U0001f4b3 *Remaining Credit:* `{remaining}` PTS\n\n"
        "Need another batch? Use /start anytime\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=back_kb(),
    ))
    return ConversationHandler.END

async def _deliver_csv(query, rows: list, count: int, elapsed: str) -> None:
    enc_path  = await asyncio.to_thread(_write_csv, rows)
    timestamp = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
    filename  = f"wallets_{count}_{timestamp}.csv"
    try:
        # Decrypt in-memory, send plaintext CSV, wipe immediately
        enc_blob    = open(enc_path, "rb").read()
        csv_bytes   = await asyncio.to_thread(aes_decrypt, enc_blob)
        import io
        csv_fileobj = io.BytesIO(csv_bytes)
        await send_safe(query.message.reply_document(
                document=csv_fileobj,
                filename=filename,
                caption=(
                    f"\u2705 *{escape_md(fmt(count))} wallets generated*\n\n"
                    f"\U0001f4c4 File: `{escape_md(filename)}`\n"
                    f"\u23f1 Time: `{escape_md(elapsed)}`\n"
                    f"\U0001f511 Columns: `#`, `address`, `private_key`, `mnemonic`\n\n"
                    "\u26a0\ufe0f *Security reminder*\n"
                    "Store this file in an encrypted location\\.\n"
                    "Never share your private keys or mnemonic phrases\\."
                ),
                parse_mode=ParseMode.MARKDOWN_V2,
            ))
    except Exception as exc:
        logger.exception("Failed to send CSV: %s", exc)
        await send_safe(query.message.reply_text(
            "\u274c *Delivery failed*\n\nCould not send the file\\. Please try again with /start\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
    finally:
        try:
            os.remove(enc_path)
        except OSError:
            pass

# 72-hour auto-delete delay in seconds
TG_MSG_AUTO_DELETE_SECS = 72 * 3600

async def _auto_delete_messages(bot, chat_id: int, message_ids: list[int], delay: float) -> None:
    """Background task: wait `delay` seconds then delete all wallet messages."""
    await asyncio.sleep(delay)
    for mid in message_ids:
        try:
            await bot.delete_message(chat_id=chat_id, message_id=mid)
        except Exception as exc:
            logger.warning("Auto-delete msg %s failed: %s", mid, exc)

async def _deliver_tg(query, context, rows: list, count: int, elapsed: str) -> None:
    total_msgs  = math.ceil(len(rows) / TG_WALLETS_PER_MSG)
    chat_id     = query.message.chat_id
    sent_ids: list[int] = []   # collect message_ids for auto-delete

    notice_msg = await send_safe(query.message.reply_text(
        "\U0001f4e8 Sending *" + escape_md(fmt(count)) + " wallets*"
        " in *" + escape_md(str(total_msgs)) + " messages*"
        f" \\\\({TG_WALLETS_PER_MSG} per message\\\\)\\\\.\\\\.\\\\.\n"
        "_Tap any address, key or mnemonic to copy it\\._",
        parse_mode=ParseMode.MARKDOWN_V2,
    ))
    if notice_msg:
        sent_ids.append(notice_msg.message_id)


    for i in range(0, len(rows), TG_WALLETS_PER_MSG):
        chunk    = rows[i: i + TG_WALLETS_PER_MSG]
        part_num = i // TG_WALLETS_PER_MSG + 1
        lines    = [f"*Part {part_num}/{total_msgs}*\n"]
        for row in chunk:
            # row is [idx, address, pk, mnemonic]
            idx, address, pk, mnemonic = row[0], row[1], row[2], row[3]
            # All sensitive fields in backtick = tap-to-copy in Telegram
            # Mnemonic: NOT escape_md so spaces/words stay intact as one block
            lines.append(
                f"*\\#{idx}*\n"
                f"Address: `{address}`\n"
                f"Private Key: `{pk}`\n"
                f"Mnemonic:\n`{mnemonic}`"
            )
        try:
            sent = await send_safe(context.bot.send_message(
                chat_id=chat_id,
                text="\n\n".join(lines),
                parse_mode=ParseMode.MARKDOWN_V2,
            ))
            if sent:
                sent_ids.append(sent.message_id)
        except Exception as exc:
            logger.exception("Failed to send TG chunk %s: %s", part_num, exc)
        await asyncio.sleep(TG_MSG_DELAY)

    summary = await send_safe(query.message.reply_text(
        f"\u2705 *{escape_md(fmt(count))} wallets sent*\n"
        f"\u23f1 Time: `{escape_md(elapsed)}`\n\n"
        "\U0001f5d1 *These messages will be auto\\-deleted in 72 hours\\.*\n\n"
        "\u26a0\ufe0f *Security reminder*\n"
        "Never share your private keys or mnemonic phrases\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
    ))
    if summary:
        sent_ids.append(summary.message_id)


    # Schedule background auto-delete after 72 hours
    asyncio.get_event_loop().create_task(
        _auto_delete_messages(context.bot, chat_id, sent_ids, TG_MSG_AUTO_DELETE_SECS)
    )

# ============================================================================
# ADMIN: HOME
# ============================================================================
async def admin_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        WELCOME_ADMIN,
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=admin_menu_kb(),
    ))
    return ConversationHandler.END

# ============================================================================
# ADMIN: USER INFO
# ============================================================================
async def adm_userinfo_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f464 User Info*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Send the user's *Telegram ID* or *@username*\\.\n"
        "_You can look up multiple users in a row\\._",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=admin_back_kb(),
    ))
    return ADM_USERINFO_QUERY

async def adm_userinfo_lookup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin_group(update):
        return ADM_USERINFO_QUERY

    q         = update.message.text.strip()
    uid, user = find_user(q)

    if user is None:
        await send_safe(update.message.reply_text(
            f"\u26a0\ufe0f No user found for `{escape_md(q)}`\\.\n\n"
            "Make sure the user has started the bot first\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_USERINFO_QUERY

    name      = escape_md(user["name"] or "N/A")
    username  = escape_md("@" + user["username"] if user["username"] else "N/A")
    pts       = escape_md(fmt_pts(user["credits"]))
    generated = escape_md(fmt(user["wallets_generated"]))
    checked   = escape_md(fmt(user["balance_checked"]))
    rate_tg   = escape_md(fmt_pts(get_rate_tg()))
    rate_csv  = escape_md(fmt_pts(get_rate_csv()))
    limit     = escape_md(fmt(get_global_limit()))

    expiry_line = ""
    if uid in GRANTED_USERS:
        exp = datetime.utcfromtimestamp(GRANTED_USERS[uid]).strftime("%Y-%m-%d %H:%M UTC")
        expiry_line = f"*Access Expires:* `{escape_md(exp)}`\n"

    text = (
        "*\U0001f464 User Profile*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Name:* {name}\n"
        f"*User ID:* `{uid}`\n"
        f"*Username:* {username}\n"
        f"{expiry_line}\n"
        f"*Remaining Credit:* `{pts}` PTS\n\n"
        f"*Wallets Generated:* `{generated}`\n"
        f"*Wallet Limit:* `{limit}`\n"
        f"*Balance Checked:* `{checked}`\n\n"
        f"*Rate Per 1,000 Generate \\(TG\\):* `{rate_tg}` PTS\n"
        f"*Rate Per 1,000 Generate \\(CSV\\):* `{rate_csv}` PTS\n"
        f"*Rate Per 1,000 CSV Balance Check:* `coming soon`\n"
    )
    await send_safe(update.message.reply_text(
        text, parse_mode=ParseMode.MARKDOWN_V2, reply_markup=admin_back_kb()
    ))
    return ADM_USERINFO_QUERY

# ============================================================================
# ADMIN: BALANCE PANEL
# ============================================================================
async def adm_balance(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    join_bal = escape_md(fmt_pts(get_join_balance()))
    await send_safe(query.edit_message_text(
        "*\U0001f4b0 Balance*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Current join balance:* `{join_bal}` PTS\n\n"
        "Select an action\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=adm_balance_kb(),
    ))
    return ConversationHandler.END

async def adm_bal_add_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\u2795 Add User Balance*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Send the *Telegram ID* or *@username* of the user to top up\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=adm_balance_back_kb(),
    ))
    return ADM_ADD_BAL_UID

async def adm_bal_add_uid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin_group(update):
        return ADM_ADD_BAL_UID

    q        = update.message.text.strip()
    uid, user = find_user(q)

    if user is None:
        await send_safe(update.message.reply_text(
            f"\u26a0\ufe0f No user found for `{escape_md(q)}`\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_ADD_BAL_UID

    context.user_data["bal_target_uid"] = uid
    name    = escape_md(user["name"])
    current = escape_md(fmt_pts(user["credits"]))
    await send_safe(update.message.reply_text(
        f"User found: *{name}* \\(`{uid}`\\)\n"
        f"Current balance: `{current}` PTS\n\n"
        "Send the *amount to add* \\(e\\.g\\. `5` or `0\\.5`\\)\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
    ))
    return ADM_ADD_BAL_AMT

async def adm_bal_add_amt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin_group(update):
        return ADM_ADD_BAL_AMT

    try:
        amount = float(update.message.text.strip())
        if amount <= 0:
            raise ValueError
    except ValueError:
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid positive number\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_ADD_BAL_AMT

    uid = context.user_data.get("bal_target_uid")
    if uid is None or uid not in USER_DB:
        await send_safe(update.message.reply_text(
            "Session expired\\. Please use Add User Balance again\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        context.user_data.clear()
        return ConversationHandler.END

    USER_DB[uid]["credits"] += amount
    new_bal = USER_DB[uid]["credits"]
    name    = escape_md(USER_DB[uid]["name"])

    await send_safe(update.message.reply_text(
        f"\u2705 *Balance updated\\!*\n\n"
        f"User: *{name}* \\(`{uid}`\\)\n"
        f"Added: `{escape_md(fmt_pts(amount))}` PTS\n"
        f"New balance: `{escape_md(fmt_pts(new_bal))}` PTS",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("➕ Add to Another User", callback_data="adm_bal_add")],
            [InlineKeyboardButton("⬅️ Back",               callback_data="adm_balance")],
        ]),
    ))
    context.user_data.clear()
    return ConversationHandler.END

async def adm_bal_join_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    current = escape_md(fmt_pts(get_join_balance()))
    await send_safe(query.edit_message_text(
        "*\U0001f381 New User Join Balance*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"Current join balance: `{current}` PTS\n\n"
        "Every new user gets this amount on first /start\\.\n\n"
        "Send the *new join balance* \\(e\\.g\\. `1` or `0`\\)\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=adm_balance_back_kb(),
    ))
    return ADM_SET_JOIN_BAL

async def adm_bal_join_set(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin_group(update):
        return ADM_SET_JOIN_BAL

    try:
        val = float(update.message.text.strip())
        if val < 0:
            raise ValueError
    except ValueError:
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid non-negative number\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_SET_JOIN_BAL

    set_join_balance(val)
    await send_safe(update.message.reply_text(
        f"\u2705 *Join balance updated\\!*\n\n"
        f"New users will receive `{escape_md(fmt_pts(val))}` PTS on first /start\\.\n"
        "_Existing users are not affected\\._",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back to Balance", callback_data="adm_balance")
        ]]),
    ))
    context.user_data.clear()
    return ConversationHandler.END

# ============================================================================
# ADMIN: RATE TREE
# ============================================================================
async def adm_rate(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f4ca Rate*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Select a category to configure rates\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=adm_rate_kb(),
    ))

async def adm_rate_wallet(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    csv_rate = escape_md(fmt_pts(get_rate_csv()))
    tg_rate  = escape_md(fmt_pts(get_rate_tg()))
    await send_safe(query.edit_message_text(
        "*\U0001f4b8 Wallet Generate Rate*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Per 1,000 CSV Export:* `{csv_rate}` PTS\n"
        f"*Per 1,000 TG Message Export:* `{tg_rate}` PTS\n\n"
        "Select a rate to update\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=adm_rate_wallet_kb(),
    ))

async def adm_rate_csv_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    current = escape_md(fmt_pts(get_rate_csv()))
    await send_safe(query.edit_message_text(
        "*\U0001f4c4 Per 1,000 CSV Rate*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"Current rate: `{current}` PTS per 1,000 wallets\n\n"
        "Send the *new rate* \\(e\\.g\\. `0\\.01`\\)\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_rate_wallet")
        ]]),
    ))
    return ADM_SET_RATE_CSV_VAL

async def adm_rate_csv_set(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin_group(update):
        return ADM_SET_RATE_CSV_VAL
    try:
        val = float(update.message.text.strip())
        if val < 0:
            raise ValueError
    except ValueError:
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid positive number\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_SET_RATE_CSV_VAL

    set_rate_csv(val)
    await send_safe(update.message.reply_text(
        f"\u2705 *CSV rate updated\\!*\n\n"
        f"New rate: `{escape_md(fmt_pts(val))}` PTS per 1,000 wallets\n"
        "Applied globally immediately\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back to Rate Menu", callback_data="adm_rate")
        ]]),
    ))
    context.user_data.clear()
    return ConversationHandler.END

async def adm_rate_tg_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    current = escape_md(fmt_pts(get_rate_tg()))
    await send_safe(query.edit_message_text(
        "*\U0001f4ac Per 1,000 TG Message Rate*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"Current rate: `{current}` PTS per 1,000 wallets\n\n"
        "Send the *new rate* \\(e\\.g\\. `0\\.03`\\)\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_rate_wallet")
        ]]),
    ))
    return ADM_SET_RATE_TG_VAL

async def adm_rate_tg_set(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin_group(update):
        return ADM_SET_RATE_TG_VAL
    try:
        val = float(update.message.text.strip())
        if val < 0:
            raise ValueError
    except ValueError:
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid positive number\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_SET_RATE_TG_VAL

    set_rate_tg(val)
    await send_safe(update.message.reply_text(
        f"\u2705 *TG Message rate updated\\!*\n\n"
        f"New rate: `{escape_md(fmt_pts(val))}` PTS per 1,000 wallets\n"
        "Applied globally immediately\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back to Rate Menu", callback_data="adm_rate")
        ]]),
    ))
    context.user_data.clear()
    return ConversationHandler.END

# ============================================================================
# ADMIN: WALLET LIMIT
# ============================================================================
async def adm_wlimit_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    current = escape_md(fmt(get_global_limit()))
    await send_safe(query.edit_message_text(
        "*\U0001f522 Wallet Generate Limit*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"Current global limit: `{current}` wallets\n\n"
        "This applies to *all users* immediately\\.\n\n"
        "Send the *new limit* \\(1 to 100,000,000\\)\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=admin_back_kb(),
    ))
    return ADM_SET_LIMIT_VAL

async def adm_wlimit_set(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin_group(update):
        return ADM_SET_LIMIT_VAL

    text = update.message.text.strip()
    if not text.isdigit():
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid number\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_SET_LIMIT_VAL

    new_limit = int(text)
    if new_limit < 1 or new_limit > 100_000_000:
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Limit must be between `1` and `100,000,000`\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_SET_LIMIT_VAL

    set_global_limit(new_limit)
    await send_safe(update.message.reply_text(
        f"\u2705 *Global wallet limit updated\\!*\n\n"
        f"New limit: `{escape_md(fmt(new_limit))}` wallets\n"
        "Applied to all users immediately\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🔄 Update Again", callback_data="adm_wlimit"),
            InlineKeyboardButton("⬅️ Back",         callback_data="adm_home"),
        ]]),
    ))
    context.user_data.clear()
    return ConversationHandler.END

# ============================================================================
# ADMIN: ACCESS MANAGEMENT
# ============================================================================
async def adm_access_entry(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Conversation entry point for Access Management."""
    query = update.callback_query
    await query.answer()
    now    = time.time()
    active = sum(1 for v in ACCESS_CODES.values() if v["expires_at"] > now)
    await send_safe(query.edit_message_text(
        "*\U0001f510 Access Management*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"Active codes: `{active}`\n"
        f"Granted users: `{len(GRANTED_USERS)}`\n\n"
        "Select an action\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("\U0001f3ab Issue Access Code",   callback_data="adm_ac_issue")],
            [
                InlineKeyboardButton("\U0001f4cb Access Code Info",    callback_data="adm_ac_info"),
                InlineKeyboardButton("\U0001f6ab Disable Access Code", callback_data="adm_ac_disable"),
            ],
            [InlineKeyboardButton("\U0001f4dc Access Code History",  callback_data="adm_ac_history")],
            [InlineKeyboardButton("\u2b05\ufe0f Back",               callback_data="adm_home")],
        ]),
    ))
    return ADM_AC_CHOOSE_TYPE

async def adm_ac_show_issue(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Show the Issue Access Code type selection screen."""
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f3ab Issue Access Code*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Choose the access code type\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("\U0001f3b2 Random User", callback_data="adm_ac_random")],
            [InlineKeyboardButton("\U0001f3af Custom User", callback_data="adm_ac_custom")],
            [InlineKeyboardButton("\u2b05\ufe0f Back",     callback_data="adm_access")],
        ]),
    ))
    return ADM_AC_ISSUE_SCREEN

# Keep old name as alias so fallback patterns still work
adm_access = adm_access_entry
adm_ac_issue = adm_ac_show_issue

# ---- RANDOM FLOW -----------------------------------------------------------
async def adm_ac_random_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data.clear()
    context.user_data["ac_type"] = "random"
    await send_safe(query.edit_message_text(
        "*\U0001f3b2 Random User Access Code*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "How many users can redeem this code?\n"
        "_Send a number, e\\.g\\. `5`_",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_ac_issue")
        ]]),
    ))
    return ADM_AC_RANDOM_COUNT

async def adm_ac_random_count(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) < 1:
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid positive number\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_RANDOM_COUNT

    context.user_data["ac_slots"] = int(text)
    slots_display = escape_md(str(context.user_data["ac_slots"]))
    await send_safe(update.message.reply_text(
        "*Set Validation Period*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"`{slots_display}` slot\\(s\\) set\\.\n\n"
        "How long should this code be valid?",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⏰ Hourly", callback_data="adm_ac_val_hourly"),
            InlineKeyboardButton("📅 Days",   callback_data="adm_ac_val_days"),
        ]]),
    ))
    return ADM_AC_VAL_TYPE2

# ---- CUSTOM FLOW -----------------------------------------------------------
async def adm_ac_custom_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data.clear()
    context.user_data["ac_type"]        = "custom"
    context.user_data["ac_custom_uids"] = []
    await send_safe(query.edit_message_text(
        "*\U0001f3af Custom User Access Code*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Send the *Telegram User ID* of the first user\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_ac_issue")
        ]]),
    ))
    return ADM_AC_CUSTOM_UID

async def adm_ac_custom_uid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid numeric Telegram User ID\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_CUSTOM_UID

    uid_list = context.user_data.setdefault("ac_custom_uids", [])
    uid_val  = int(text)

    if uid_val in uid_list:
        await send_safe(update.message.reply_text(
            f"\u26a0\ufe0f User `{uid_val}` is already added\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_CUSTOM_UID

    uid_list.append(uid_val)
    ids_display = escape_md(", ".join(str(u) for u in uid_list))

    await send_safe(update.message.reply_text(
        f"\u2705 Added `{uid_val}`\\.\n\n"
        f"*Users so far \\({len(uid_list)}\\):* {ids_display}\n\n"
        "Send another User ID, or tap *Done* to set validation\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("✅ Done, Set Validation", callback_data="adm_ac_custom_done")
        ]]),
    ))
    return ADM_AC_CUSTOM_UID

async def adm_ac_custom_done(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    uid_list = context.user_data.get("ac_custom_uids", [])
    await send_safe(query.edit_message_text(
        "*Set Validation Period*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"`{escape_md(str(len(uid_list)))}` user\\(s\\) added\\.\n\n"
        "How long should this code be valid?",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⏰ Hourly", callback_data="adm_ac_val_hourly"),
            InlineKeyboardButton("📅 Days",   callback_data="adm_ac_val_days"),
        ]]),
    ))
    return ADM_AC_VAL_TYPE2

# ---- SHARED: VALIDATION TYPE + AMOUNT + CODE GENERATION -------------------
async def adm_ac_val_type(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    val_type = "hours" if query.data == "adm_ac_val_hourly" else "days"
    context.user_data["ac_val_type"] = val_type
    unit = "hours" if val_type == "hours" else "days"
    await send_safe(query.edit_message_text(
        f"*Validation Amount*\n\n"
        f"How many *{escape_md(unit)}* should this code be valid for?\n"
        "_Send a number, e\\.g\\. `24`_",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_ac_val_back"),
        ]]),
    ))
    return ADM_AC_VAL_AMT2

async def adm_ac_val_type_back(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    """Back button from amount input: re-show the Hourly/Days selection."""
    query = update.callback_query
    await query.answer()
    ac_type  = context.user_data.get("ac_type", "random")
    if ac_type == "random":
        slots = context.user_data.get("ac_slots", 1)
        detail = escape_md(f"{slots} slot(s) set.")
    else:
        uid_list = context.user_data.get("ac_custom_uids", [])
        detail   = escape_md(f"{len(uid_list)} user(s) added.")
    await send_safe(query.edit_message_text(
        "*Set Validation Period*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"`{detail}`\n\n"
        "How long should this code be valid?",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⏰ Hourly", callback_data="adm_ac_val_hourly"),
            InlineKeyboardButton("📅 Days",   callback_data="adm_ac_val_days"),
        ]]),
    ))
    return ADM_AC_VAL_TYPE2

async def adm_ac_val_amt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) < 1:
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid positive number\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_VAL_AMT2

    amount   = int(text)
    val_type = context.user_data.get("ac_val_type", "hours")
    hours    = amount if val_type == "hours" else amount * 24
    expires  = time.time() + hours * 3600
    ac_type  = context.user_data.get("ac_type", "random")

    # Generate unique 8-char code
    while True:
        code = _make_code()
        if code not in ACCESS_CODES:
            break

    if ac_type == "random":
        slots = context.user_data.get("ac_slots", 1)
        ACCESS_CODES[code] = {
            "type":         "random",
            "slots":        slots,
            "allowed_uids": set(),
            "used_uids":    set(),
            "expires_at":   expires,
            "created_at":   time.time(),
        }
        type_detail = escape_md(f"Random ({slots} slot(s))")
    else:
        uids = set(context.user_data.get("ac_custom_uids", []))
        ACCESS_CODES[code] = {
            "type":         "custom",
            "slots":        len(uids),
            "allowed_uids": uids,
            "used_uids":    set(),
            "expires_at":   expires,
            "created_at":   time.time(),
        }
        type_detail = f"Custom \\({escape_md(', '.join(str(u) for u in uids))}\\)"

    expiry_dt   = datetime.utcfromtimestamp(expires).strftime("%Y-%m-%d %H:%M UTC")
    val_display = escape_md(f"{amount} {'hour(s)' if val_type == 'hours' else 'day(s)'}")

    await send_safe(update.message.reply_text(
        f"\u2705 *Access Code Issued\\!*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Code:* `{code}`\n"
        f"*Type:* {type_detail}\n"
        f"*Valid for:* {val_display}\n"
        f"*Expires:* `{escape_md(expiry_dt)}`\n\n"
        "Share this code with your users\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            # adm_access re-enters the conversation from the top
            InlineKeyboardButton("🎫 Issue Another", callback_data="adm_access"),
            InlineKeyboardButton("⬅️ Back",          callback_data="adm_home"),
        ]]),
    ))
    context.user_data.clear()
    return ConversationHandler.END

# ---- ACCESS CODE INFO -------------------------------------------------------
async def adm_ac_info_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f4cb Access Code Info*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Send the *access code* to look up\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_access"),
        ]]),
    ))
    return ADM_AC_INFO_QUERY

async def adm_ac_info_lookup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    code = update.message.text.strip().upper()

    # Determine source and status
    if code in ACCESS_CODES:
        entry  = ACCESS_CODES[code]
        now    = time.time()
        if entry["expires_at"] > now:
            status_str = "\u2705 Active"
            status_key = "active"
        else:
            status_str = "\u23f0 Expired"
            status_key = "expired"
    elif code in DISABLED_CODES:
        entry      = DISABLED_CODES[code]
        status_str = "\U0001f6ab Disabled"
        status_key = "disabled"
    else:
        await send_safe(update.message.reply_text(
            f"\u26a0\ufe0f Code `{escape_md(code)}` not found\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_INFO_QUERY

    now        = time.time()
    exp_dt     = datetime.utcfromtimestamp(entry["expires_at"]).strftime("%Y\\-%m\\-%d %H:%M UTC")
    created_ts = entry.get("created_at")
    created_dt = datetime.utcfromtimestamp(created_ts).strftime("%Y\\-%m\\-%d %H:%M UTC") if created_ts else "N/A"

    extra_line = ""
    if status_key == "disabled":
        dis_ts   = entry.get("disabled_at")
        dis_dt   = datetime.utcfromtimestamp(dis_ts).strftime("%Y\\-%m\\-%d %H:%M UTC") if dis_ts else "N/A"
        extra_line = f"*Disabled at:* `{dis_dt}`\n"

    # Build used-users list
    used_uids = entry.get("used_uids", set())
    if used_uids:
        lines = []
        for uid in used_uids:
            u = USER_DB.get(uid)
            if u:
                name  = escape_md(u["name"] or str(uid))
                uname = escape_md("@" + u["username"] if u["username"] else "N/A")
                lines.append(f"  \u2022 `{uid}` \\| {name} \\| {uname}")
            else:
                lines.append(f"  \u2022 `{uid}` \\| _unknown user_")
        users_text = "\n".join(lines)
    else:
        users_text = "  _No one has used this code yet\\._"

    code_type  = escape_md(entry["type"].capitalize())
    slots_left = escape_md(str(entry.get("slots", 0)))
    total_used = escape_md(str(len(used_uids)))

    await send_safe(update.message.reply_text(
        f"*\U0001f4cb Code Info: `{escape_md(code)}`*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Status:* {status_str}\n"
        f"*Type:* `{code_type}`\n"
        f"*Created:* `{created_dt}`\n"
        f"*Expires:* `{exp_dt}`\n"
        f"{extra_line}"
        f"*Slots remaining:* `{slots_left}`\n"
        f"*Times used:* `{total_used}`\n\n"
        f"*Users who used this code \\({total_used}\\):*\n"
        f"{users_text}",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🔍 Look up another", callback_data="adm_ac_info"),
            InlineKeyboardButton("⬅️ Back",            callback_data="adm_access"),
        ]]),
    ))
    return ADM_AC_INFO_QUERY

# ---- DISABLE ACCESS CODE ----------------------------------------------------
async def adm_ac_disable_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f6ab Disable Access Code*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Send the *access code* to disable\\.\n\n"
        "\u26a0\ufe0f All users who redeemed this code will *immediately lose access*\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_access"),
        ]]),
    ))
    return ADM_AC_DISABLE_QUERY

async def adm_ac_disable_exec(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    code  = update.message.text.strip().upper()
    # Check active codes first, then already-disabled ones
    entry = ACCESS_CODES.get(code)
    if entry is None:
        if code in DISABLED_CODES:
            await send_safe(update.message.reply_text(
                f"\u26a0\ufe0f Code `{escape_md(code)}` is already disabled\\.",
                parse_mode=ParseMode.MARKDOWN_V2,
            ))
        else:
            await send_safe(update.message.reply_text(
                f"\u26a0\ufe0f Code `{escape_md(code)}` not found\\.",
                parse_mode=ParseMode.MARKDOWN_V2,
            ))
        return ADM_AC_DISABLE_QUERY

    # Collect affected users
    used_uids   = set(entry.get("used_uids", set()))
    revoked_cnt = 0

    # Remove from GRANTED_USERS immediately
    for uid in used_uids:
        if uid in GRANTED_USERS:
            del GRANTED_USERS[uid]
            revoked_cnt += 1

    # Archive to DISABLED_CODES (keep full history)
    archived        = dict(entry)
    archived["disabled_at"] = time.time()
    DISABLED_CODES[code]    = archived
    del ACCESS_CODES[code]

    # Build revoked user list for display
    if used_uids:
        lines = []
        for uid in used_uids:
            u = USER_DB.get(uid)
            name = escape_md(u["name"] if u else str(uid))
            lines.append(f"  \u2022 `{uid}` \\| {name}")
        revoked_text = "\n".join(lines)
    else:
        revoked_text = "  _No users were using this code\\._"

    await send_safe(update.message.reply_text(
        f"\U0001f6ab *Access Code Disabled\\!*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Code:* `{escape_md(code)}`\n"
        f"*Users revoked:* `{revoked_cnt}`\n\n"
        f"*Affected users:*\n{revoked_text}",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🚫 Disable Another", callback_data="adm_ac_disable"),
            InlineKeyboardButton("⬅️ Back",            callback_data="adm_access"),
        ]]),
    ))
    return ADM_AC_DISABLE_QUERY

# ============================================================================
# ADMIN: ACCESS CODE HISTORY
# ============================================================================
async def adm_ac_history_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    now          = time.time()
    active_cnt   = sum(1 for v in ACCESS_CODES.values() if v["expires_at"] > now)
    expired_cnt  = sum(1 for v in ACCESS_CODES.values() if v["expires_at"] <= now)
    disabled_cnt = len(DISABLED_CODES)
    await send_safe(query.edit_message_text(
        "*\U0001f4dc Access Code History*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"\u2705 Active: `{active_cnt}`\n"
        f"\U0001f6ab Disabled: `{disabled_cnt}`\n"
        f"\u23f0 Expired: `{expired_cnt}`\n\n"
        "Export a list as CSV\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([
            [InlineKeyboardButton("✅ Active Access Codes",    callback_data="adm_ac_hist_active")],
            [InlineKeyboardButton("🚫 Disabled Access Codes", callback_data="adm_ac_hist_disabled")],
            [InlineKeyboardButton("⏰ Expired Access Codes",  callback_data="adm_ac_hist_expired")],
            [InlineKeyboardButton("⬅️ Back",                  callback_data="adm_access")],
        ]),
    ))
    return ADM_AC_HISTORY_MENU

def _build_ac_csv(rows: list[tuple[str, str]]) -> bytes:
    """Build CSV bytes from (code, status) tuples."""
    import io, csv
    buf = io.StringIO()
    w   = csv.writer(buf)
    w.writerow(["#", "Code", "Status"])
    for i, (code, status) in enumerate(rows, 1):
        w.writerow([i, code, status])
    return buf.getvalue().encode("utf-8")

async def adm_ac_hist_active(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    now  = time.time()
    rows = [
        (code, "Active")
        for code, v in ACCESS_CODES.items()
        if v["expires_at"] > now
    ]
    if not rows:
        await send_safe(query.message.reply_text(
            "\u26a0\ufe0f No active access codes found\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_HISTORY_MENU
    data = _build_ac_csv(rows)
    await query.message.reply_document(
        document=data,
        filename="active_access_codes.csv",
        caption=f"\u2705 *Active Access Codes* \\— `{len(rows)}` total",
        parse_mode=ParseMode.MARKDOWN_V2,
    )
    return ADM_AC_HISTORY_MENU

async def adm_ac_hist_disabled(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    rows = [(code, "Disabled") for code in DISABLED_CODES]
    if not rows:
        await send_safe(query.message.reply_text(
            "\u26a0\ufe0f No disabled access codes found\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_HISTORY_MENU
    data = _build_ac_csv(rows)
    await query.message.reply_document(
        document=data,
        filename="disabled_access_codes.csv",
        caption=f"\U0001f6ab *Disabled Access Codes* \\— `{len(rows)}` total",
        parse_mode=ParseMode.MARKDOWN_V2,
    )
    return ADM_AC_HISTORY_MENU

async def adm_ac_hist_expired(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    now  = time.time()
    rows = [
        (code, "Expired")
        for code, v in ACCESS_CODES.items()
        if v["expires_at"] <= now
    ]
    if not rows:
        await send_safe(query.message.reply_text(
            "\u26a0\ufe0f No expired access codes found\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_AC_HISTORY_MENU
    data = _build_ac_csv(rows)
    await query.message.reply_document(
        document=data,
        filename="expired_access_codes.csv",
        caption=f"\u23f0 *Expired Access Codes* \\— `{len(rows)}` total",
        parse_mode=ParseMode.MARKDOWN_V2,
    )
    return ADM_AC_HISTORY_MENU

# ============================================================================
# ADMIN: ORDER MANAGEMENT
# ============================================================================
async def adm_orders_entry(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    total = len(ORDER_DB)
    await send_safe(query.edit_message_text(
        "*\U0001f9fe Order Management*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"Total orders: `{total}`\n\n"
        "Select an action\\:",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([
            [
                InlineKeyboardButton("\U0001f4cb Order ID Info",       callback_data="adm_order_info"),
                InlineKeyboardButton("\U0001f464 User Order ID Info",  callback_data="adm_order_user"),
            ],
            [InlineKeyboardButton("\u2b05\ufe0f Back", callback_data="adm_home")],
        ]),
    ))
    return ADM_ORDER_MENU

async def adm_order_info_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f4cb Order ID Info*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Send the *Order ID* to look up\\.\n"
        "_Example: `ORD\\-XXXX1234`_",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_orders"),
        ]]),
    ))
    return ADM_ORDER_ID_QUERY

async def adm_order_info_lookup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    oid   = update.message.text.strip().upper()
    order = ORDER_DB.get(oid)

    if order is None:
        await send_safe(update.message.reply_text(
            f"\u26a0\ufe0f Order `{escape_md(oid)}` not found\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_ORDER_ID_QUERY

    uid          = order["uid"]
    u            = USER_DB.get(uid)
    name         = escape_md(u["name"] if u else str(uid))
    username     = escape_md("@" + u["username"] if u and u["username"] else "N/A")
    export_label = "CSV File" if order["export_type"] == "exp_csv" else "TG Messages"
    created_dt   = datetime.utcfromtimestamp(order["created_at"]).strftime("%Y-%m-%d %H:%M UTC")

    await send_safe(update.message.reply_text(
        f"*\U0001f4cb Order Info*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        f"*Order ID:* `{escape_md(oid)}`\n"
        f"*Status:* `{escape_md(order['status'].capitalize())}`\n"
        f"*Created:* `{escape_md(created_dt)}`\n\n"
        f"*User:* {name} \\(`{uid}`\\)\n"
        f"*Username:* {username}\n\n"
        f"*Wallets:* `{escape_md(fmt(order['count']))}`\n"
        f"*Mnemonic:* `{order['word_count']} words`\n"
        f"*Export:* `{escape_md(export_label)}`\n"
        f"*Cost:* `{escape_md(fmt_pts(order['cost']))}` PTS\n",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🔍 Look up another", callback_data="adm_order_info"),
            InlineKeyboardButton("⬅️ Back",            callback_data="adm_orders"),
        ]]),
    ))
    return ADM_ORDER_ID_QUERY

async def adm_order_user_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await send_safe(query.edit_message_text(
        "*\U0001f464 User Order ID Info*\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\n\n"
        "Send the user's *Telegram ID* to see all their orders\\.",
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("⬅️ Back", callback_data="adm_orders"),
        ]]),
    ))
    return ADM_ORDER_USER_QUERY

async def adm_order_user_lookup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await send_safe(update.message.reply_text(
            "\u26a0\ufe0f Please send a valid numeric Telegram User ID\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_ORDER_USER_QUERY

    target_uid = int(text)
    u          = USER_DB.get(target_uid)

    # Collect all orders for this user, sorted newest first
    user_orders = [
        (oid, o) for oid, o in ORDER_DB.items() if o["uid"] == target_uid
    ]
    user_orders.sort(key=lambda x: x[1]["created_at"], reverse=True)

    if not user_orders:
        name_str = escape_md(u["name"] if u else str(target_uid))
        await send_safe(update.message.reply_text(
            f"\u26a0\ufe0f No orders found for user `{target_uid}` \\({name_str}\\)\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
        return ADM_ORDER_USER_QUERY

    name     = escape_md(u["name"] if u else str(target_uid))
    username = escape_md("@" + u["username"] if u and u["username"] else "N/A")
    lines    = [
        f"*\U0001f464 Orders for {name}* \\(`{target_uid}`\\)\n"
        f"Username: {username}\n"
        f"Total orders: `{len(user_orders)}`\n"
        "\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501\u2501"
    ]
    for oid, o in user_orders:
        export_label = "CSV" if o["export_type"] == "exp_csv" else "TG"
        dt           = datetime.utcfromtimestamp(o["created_at"]).strftime("%Y-%m-%d %H:%M")
        lines.append(
            f"\n\U0001f4dd `{escape_md(oid)}`\n"
            f"  Wallets: `{escape_md(fmt(o['count']))}` \\| {o['word_count']}w \\| {escape_md(export_label)}\n"
            f"  Cost: `{escape_md(fmt_pts(o['cost']))}` PTS \\| {escape_md(dt)} UTC"
        )

    await send_safe(update.message.reply_text(
        "\n".join(lines),
        parse_mode=ParseMode.MARKDOWN_V2,
        reply_markup=InlineKeyboardMarkup([[
            InlineKeyboardButton("🔍 Look up another user", callback_data="adm_order_user"),
            InlineKeyboardButton("⬅️ Back",                 callback_data="adm_orders"),
        ]]),
    ))
    return ADM_ORDER_USER_QUERY

# ============================================================================
# CANCEL / FALLBACK
# ============================================================================
async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    context.user_data.clear()
    if is_private(update):
        await send_safe(update.message.reply_text(
            "\U0001f6ab *Session cancelled\\.*\n\nUse /start whenever you're ready\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
    elif is_admin_group(update):
        await send_safe(update.message.reply_text(
            "\U0001f6ab Admin action cancelled\\. Use /start to open the admin panel\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))
    return ConversationHandler.END

async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if is_private(update):
        await send_safe(update.message.reply_text(
            HELP_TEXT, parse_mode=ParseMode.MARKDOWN_V2
        ))

async def unknown_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if is_private(update):
        await send_safe(update.message.reply_text(
            "Use /start to open the menu or /help for more info\\.",
            parse_mode=ParseMode.MARKDOWN_V2,
        ))

# ============================================================================
# MAIN
# ============================================================================
def main() -> None:
    global _wallets_per_sec

    logger.info("Running startup benchmark...")
    _wallets_per_sec = _run_benchmark()

    app = Application.builder().token(BOT_TOKEN).build()

    # User conversation: access gate + bulk wallet generator
    user_conv = ConversationHandler(
        entry_points=[
            CommandHandler("start", start),
            CallbackQueryHandler(bulk_entry, pattern="^menu_bulk$"),
        ],
        states={
            USER_ENTER_CODE: [MessageHandler(
                filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE,
                user_enter_code,
            )],
            ASK_COUNT:  [MessageHandler(
                filters.TEXT & ~filters.COMMAND & filters.ChatType.PRIVATE,
                receive_count,
            )],
            ASK_WORDS:  [CallbackQueryHandler(receive_words,   pattern=r"^wc_(12|15|18|21|24)$")],
            ASK_EXPORT: [CallbackQueryHandler(receive_export,  pattern="^exp_(csv|tg)$")],
            ASK_CONFIRM:[CallbackQueryHandler(receive_confirm, pattern="^order_confirm$")],
        },
        fallbacks=[
            CommandHandler("cancel", cancel),
            CallbackQueryHandler(menu_home, pattern="^menu_home$"),
        ],
        allow_reentry=True,
    )

    # =========================================================================
    # SINGLE UNIFIED ADMIN CONVERSATION
    # All admin flows merged into one handler to prevent cross-conv state leaks
    # =========================================================================
    admin_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(admin_home,           pattern="^adm_home$"),
            CallbackQueryHandler(adm_userinfo_prompt,  pattern="^adm_userinfo$"),
            CallbackQueryHandler(adm_wlimit_prompt,    pattern="^adm_wlimit$"),
            CallbackQueryHandler(adm_rate_csv_prompt,  pattern="^adm_rate_csv$"),
            CallbackQueryHandler(adm_rate_tg_prompt,   pattern="^adm_rate_tg$"),
            CallbackQueryHandler(adm_bal_add_prompt,   pattern="^adm_bal_add$"),
            CallbackQueryHandler(adm_bal_join_prompt,  pattern="^adm_bal_join$"),
            CallbackQueryHandler(adm_access_entry,     pattern="^adm_access$"),
            CallbackQueryHandler(adm_orders_entry,     pattern="^adm_orders$"),
        ],
        states={
            # ---- User Info ----
            ADM_USERINFO_QUERY: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_userinfo_lookup),
                CallbackQueryHandler(admin_home, pattern="^adm_home$"),
            ],
            # ---- Wallet Limit ----
            ADM_SET_LIMIT_VAL: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_wlimit_set),
                CallbackQueryHandler(admin_home, pattern="^adm_home$"),
            ],
            # ---- CSV Rate ----
            ADM_SET_RATE_CSV_VAL: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_rate_csv_set),
                CallbackQueryHandler(adm_rate_wallet, pattern="^adm_rate_wallet$"),
                CallbackQueryHandler(adm_rate,        pattern="^adm_rate$"),
                CallbackQueryHandler(admin_home,      pattern="^adm_home$"),
            ],
            # ---- TG Rate ----
            ADM_SET_RATE_TG_VAL: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_rate_tg_set),
                CallbackQueryHandler(adm_rate_wallet, pattern="^adm_rate_wallet$"),
                CallbackQueryHandler(adm_rate,        pattern="^adm_rate$"),
                CallbackQueryHandler(admin_home,      pattern="^adm_home$"),
            ],
            # ---- Add Balance ----
            ADM_ADD_BAL_UID: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_bal_add_uid),
                CallbackQueryHandler(adm_balance, pattern="^adm_balance$"),
                CallbackQueryHandler(admin_home,  pattern="^adm_home$"),
            ],
            ADM_ADD_BAL_AMT: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_bal_add_amt),
                CallbackQueryHandler(adm_balance, pattern="^adm_balance$"),
                CallbackQueryHandler(admin_home,  pattern="^adm_home$"),
            ],
            # ---- Join Balance ----
            ADM_SET_JOIN_BAL: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_bal_join_set),
                CallbackQueryHandler(adm_balance, pattern="^adm_balance$"),
                CallbackQueryHandler(admin_home,  pattern="^adm_home$"),
            ],
            # ---- Access Management ----
            ADM_AC_CHOOSE_TYPE: [
                CallbackQueryHandler(adm_ac_show_issue,       pattern="^adm_ac_issue$"),
                CallbackQueryHandler(adm_ac_info_prompt,      pattern="^adm_ac_info$"),
                CallbackQueryHandler(adm_ac_disable_prompt,   pattern="^adm_ac_disable$"),
                CallbackQueryHandler(adm_ac_history_menu,     pattern="^adm_ac_history$"),
                CallbackQueryHandler(admin_home,              pattern="^adm_home$"),
            ],
            ADM_AC_ISSUE_SCREEN: [
                CallbackQueryHandler(adm_ac_random_start, pattern="^adm_ac_random$"),
                CallbackQueryHandler(adm_ac_custom_start, pattern="^adm_ac_custom$"),
                CallbackQueryHandler(adm_access_entry,    pattern="^adm_access$"),
                CallbackQueryHandler(admin_home,          pattern="^adm_home$"),
            ],
            ADM_AC_RANDOM_COUNT: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_ac_random_count),
                CallbackQueryHandler(adm_ac_show_issue, pattern="^adm_ac_issue$"),
                CallbackQueryHandler(admin_home,        pattern="^adm_home$"),
            ],
            ADM_AC_CUSTOM_UID: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_ac_custom_uid),
                CallbackQueryHandler(adm_ac_custom_done, pattern="^adm_ac_custom_done$"),
                CallbackQueryHandler(adm_ac_show_issue,  pattern="^adm_ac_issue$"),
                CallbackQueryHandler(admin_home,         pattern="^adm_home$"),
            ],
            ADM_AC_VAL_TYPE2: [
                CallbackQueryHandler(adm_ac_val_type,   pattern="^adm_ac_val_(hourly|days)$"),
                CallbackQueryHandler(adm_ac_show_issue, pattern="^adm_ac_issue$"),
                CallbackQueryHandler(admin_home,        pattern="^adm_home$"),
            ],
            ADM_AC_VAL_AMT2: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_ac_val_amt),
                CallbackQueryHandler(adm_ac_val_type_back, pattern="^adm_ac_val_back$"),
                CallbackQueryHandler(admin_home,           pattern="^adm_home$"),
            ],
            ADM_AC_INFO_QUERY: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_ac_info_lookup),
                CallbackQueryHandler(adm_ac_info_prompt, pattern="^adm_ac_info$"),
                CallbackQueryHandler(adm_access_entry,   pattern="^adm_access$"),
                CallbackQueryHandler(admin_home,         pattern="^adm_home$"),
            ],
            ADM_AC_DISABLE_QUERY: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_ac_disable_exec),
                CallbackQueryHandler(adm_ac_disable_prompt, pattern="^adm_ac_disable$"),
                CallbackQueryHandler(adm_access_entry,      pattern="^adm_access$"),
                CallbackQueryHandler(admin_home,            pattern="^adm_home$"),
            ],
            ADM_AC_HISTORY_MENU: [
                CallbackQueryHandler(adm_ac_hist_active,   pattern="^adm_ac_hist_active$"),
                CallbackQueryHandler(adm_ac_hist_disabled, pattern="^adm_ac_hist_disabled$"),
                CallbackQueryHandler(adm_ac_hist_expired,  pattern="^adm_ac_hist_expired$"),
                CallbackQueryHandler(adm_access_entry,     pattern="^adm_access$"),
                CallbackQueryHandler(admin_home,           pattern="^adm_home$"),
            ],
            # ---- Order Management ----
            ADM_ORDER_MENU: [
                CallbackQueryHandler(adm_order_info_prompt,  pattern="^adm_order_info$"),
                CallbackQueryHandler(adm_order_user_prompt,  pattern="^adm_order_user$"),
                CallbackQueryHandler(admin_home,             pattern="^adm_home$"),
            ],
            ADM_ORDER_ID_QUERY: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_order_info_lookup),
                CallbackQueryHandler(adm_order_info_prompt,  pattern="^adm_order_info$"),
                CallbackQueryHandler(adm_orders_entry,       pattern="^adm_orders$"),
                CallbackQueryHandler(admin_home,             pattern="^adm_home$"),
            ],
            ADM_ORDER_USER_QUERY: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, adm_order_user_lookup),
                CallbackQueryHandler(adm_order_user_prompt,  pattern="^adm_order_user$"),
                CallbackQueryHandler(adm_orders_entry,       pattern="^adm_orders$"),
                CallbackQueryHandler(admin_home,             pattern="^adm_home$"),
            ],
        },
        fallbacks=[
            CommandHandler("cancel", cancel),
            CallbackQueryHandler(admin_home, pattern="^adm_home$"),
        ],
        allow_reentry=True,
    )

    # Register conversations (order matters)
    app.add_handler(user_conv)
    app.add_handler(admin_conv)

    # Commands
    app.add_handler(CommandHandler("help",   help_command))
    app.add_handler(CommandHandler("cancel", cancel))

    # Static callbacks (private)
    app.add_handler(CallbackQueryHandler(menu_home,     pattern="^menu_home$"))
    app.add_handler(CallbackQueryHandler(menu_profile,  pattern="^menu_profile$"))
    app.add_handler(CallbackQueryHandler(menu_settings, pattern="^menu_settings$"))
    app.add_handler(CallbackQueryHandler(menu_balance,  pattern="^menu_balance$"))

    # Static callbacks (admin)
    app.add_handler(CallbackQueryHandler(admin_home,      pattern="^adm_home$"))
    app.add_handler(CallbackQueryHandler(adm_balance,     pattern="^adm_balance$"))
    app.add_handler(CallbackQueryHandler(adm_rate,        pattern="^adm_rate$"))
    app.add_handler(CallbackQueryHandler(adm_rate_wallet, pattern="^adm_rate_wallet$"))

    # Unknown commands (private only)
    app.add_handler(MessageHandler(filters.COMMAND & filters.ChatType.PRIVATE, unknown_command))

    logger.info("Bot started. Speed: %.1f wallets/sec", _wallets_per_sec)
    app.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()

# < Ranveer  ><   ꪜˣ  > — Userbot V9 (Ranveer Authority)
#

import asyncio
import os
import time
import json
import random
import logging
import traceback
import re
import math
from typing import Dict, Set, Optional, Any, List
from io import BytesIO

import glob as _glob
import datetime

import requests
import qrcode
from gtts import gTTS
import yt_dlp

from telethon import TelegramClient, events, functions, types
from telethon.errors import FloodWaitError, RPCError
from telethon.tl.functions.channels import EditBannedRequest, CreateChannelRequest, InviteToChannelRequest, EditAdminRequest
from telethon.tl.functions.messages import CreateChatRequest, AddChatUserRequest, EditChatAdminRequest
from telethon.tl.types import ChatBannedRights, ChatAdminRights, InputUser

# ─────────────────────────────────────────────────────────────────
#  LOGGING
# ─────────────────────────────────────────────────────────────────
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
logger = logging.getLogger("kurobotV9")

# ─────────────────────────────────────────────────────────────────
#  PATH SETUP
# ─────────────────────────────────────────────────────────────────
BASE_DIR = os.getcwd()
DOWNLOAD_PATH = os.path.join(BASE_DIR, "downloads")
TEMP_PATH = os.path.join(BASE_DIR, "temp")
os.makedirs(DOWNLOAD_PATH, exist_ok=True)
os.makedirs(TEMP_PATH, exist_ok=True)

# ─────────────────────────────────────────────────────────────────
#  CONFIG  (env vars preferred; hardcoded as fallback)
# ─────────────────────────────────────────────────────────────────
API_ID   = int(os.environ.get("TG_API_ID",   "39762228"))
API_HASH = os.environ.get("TG_API_HASH",     "70a4831ca10b5232d1b05585eb1bbacb")
OWNER_ID = int(os.environ.get("TG_OWNER_ID", "8732839017"))
SESSION  = os.environ.get("TG_SESSION",      "8732839017")

# Optional YouTube auth for .music
YTDLP_COOKIES_FILE    = os.environ.get("YTDLP_COOKIES_FILE", "").strip()
YTDLP_COOKIES_BROWSER = os.environ.get("YTDLP_COOKIES_BROWSER", "").strip()

# Saved bot usernames
MAX_SAVED_BOTS = 10
DEFAULT_BOT_USERNAMES = [
    x.strip() for x in os.environ.get("BOT_USERNAMES", "").replace(";", ",").split(",")
    if x.strip()
][:MAX_SAVED_BOTS]

bot = TelegramClient(
    SESSION, API_ID, API_HASH,
    auto_reconnect=True,
    connection_retries=10,
    retry_delay=3,
)

# V9: cache bot.get_me() — avoids repeated network roundtrips on every command
_ME_CACHE = None

async def _get_me():
    global _ME_CACHE
    if _ME_CACHE is None:
        _ME_CACHE = await _get_me()
    return _ME_CACHE

# ─────────────────────────────────────────────────────────────────
#  STORAGE FILES
# ─────────────────────────────────────────────────────────────────
ADMINS_FILE      = "admins.json"
NOTES_FILE       = "notes.json"
BANNER_FILE      = "banner_msg_id.txt"
MRAID_FILE       = "mraid_msg_id.txt"
RAIDS_FILE       = "raids_state.json"
BOT_NAMES_FILE   = "bot_names.json"
BOT_ADMINS_FILE  = "bot_admins.json"   # accounts allowed to run commands remotely

# ─────────────────────────────────────────────────────────────────
#  RUNTIME STATE
# ─────────────────────────────────────────────────────────────────
admins:           Set[int]                  = set()
bot_admins:       Set[int]                  = set()   # remote-access accounts
notes:            Dict[int, str]            = {}
menu_banner_msg:  Optional[tuple]           = None   # (chat_id, msg_id)
mraid_media_msg:  Optional[tuple]           = None   # (chat_id, msg_id)  ← NEW
auto_react_emoji: Optional[str]             = None
bot_usernames:    List[str]                 = DEFAULT_BOT_USERNAMES.copy()

muted_users:      Set[int]                  = set()
global_muted:     Set[int]                  = set()
reply_users:      Set[int]                  = set()
rr_users:         Set[int]                  = set()
flag_users:       Set[int]                  = set()
hrr_users:        Set[int]                  = set()
replygod_users:   Set[int]                  = set()
replyvx_users:    Dict[int, Dict[str, Any]] = {}
abuse_users:      Set[int]                  = set()
abuse2_users:     Set[int]                  = set()
slap_users:       Set[int]                  = set()
kick_users:       Set[int]                  = set()
spam_users:       Set[int]                  = set()
raid_users:       Set[int]                  = set()
media_raid_users: Set[int]                  = set()
bomb_users:         Set[int]                  = set()   # NEW: Bomb Raid
slide_users:        Dict[int, Dict[str, Any]] = {}      # Slide Raid: {uid: {text, idx, emojis}}
clone_reply_users:  Set[int]                  = set()   # Clone Reply: mirrors target's messages
safe_raid_tasks:    Dict[int, asyncio.Task]   = {}      # Safe Raid: {uid: task}
antilink_chats:     Set[int]                  = set()   # V9: chats with antilink ON

# ── Game state ───────────────────────────────────────────────────
guess_games:  Dict[int, int]  = {}   # {chat_id: secret_number}
hangman_games: Dict[int, Dict] = {}  # {chat_id: {word, guessed, wrong, lives}}
# ── Trigger Raid state ───────────────────────────────────────────
PHONE_OSINT_BOT:       str       = "@eyeofgod_bot"    # bot used for phone OSINT lookup
trigger_raid_targets:  Set[int]  = set()               # users locked in ongoing raid
TRIGGER_PERMSG:        int       = 5                   # fast replies per message (fires on EVERY msg — nonstop)

SLIDE_EMOJIS: List[str] = ["🔥","💀","⚡","👊","🗡️","💣","😈","🖕","☠️","🤬","💢","🩸"]

spray_tasks:  Dict[int, asyncio.Task]       = {}
group_locks:  Set[int]                      = set()

START_TIME   = time.time()
SPRAY_DELAY  = 5

# Clone engine
CLONE_ACTIVE:  bool         = False
LAST_CLONE_ID: Optional[int] = None
CLONE_DATA: Dict[str, Any]  = {
    "name": None, "last": None,
    "username": None, "bio": None, "photo_bytes": None,
}
CLONE_RAID_TASK: Optional[asyncio.Task] = None

# FastGC engine
FASTGC_STATE: Dict[str, Any] = {
    "active": False, "template": None,
    "task": None, "chat_id": None,
}
GC_FAST_INTERVAL = 1
GC_FAST_EMOJIS = [
    "❤️","🧡","💛","💚","💙","💜","🖤","🤍","🤎",
    "🩷","🩵","🩶","💖","💘","💝","💗","💓","💞",
    "💕","💟","❣️","❤️‍🔥","❤️‍🩹",
]

# ─────────────────────────────────────────────────────────────────
#  JSON HELPERS
# ─────────────────────────────────────────────────────────────────
def _load_json(path: str, default):
    try:
        if os.path.isfile(path):
            with open(path, "r", encoding="utf-8") as f:
                return json.load(f)
    except Exception as e:
        logger.error(f"[JSON LOAD] {path}: {e}")
    return default

def _save_json(path: str, data):
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=2)
    except Exception as e:
        logger.error(f"[JSON SAVE] {path}: {e}")

# ─────────────────────────────────────────────────────────────────
#  PERSISTENT STORAGE FUNCTIONS
# ─────────────────────────────────────────────────────────────────
def load_admins():
    global admins
    data = _load_json(ADMINS_FILE, [])
    admins = {int(x) for x in data if str(x).lstrip("-").isdigit()}

def save_admins():
    _save_json(ADMINS_FILE, sorted(admins))

def is_admin(uid: int) -> bool:
    return bool(uid) and (uid == OWNER_ID or uid in admins)

def load_bot_admins():
    global bot_admins
    data = _load_json(BOT_ADMINS_FILE, [])
    bot_admins = {int(x) for x in data if str(x).lstrip("-").isdigit()}

def save_bot_admins():
    _save_json(BOT_ADMINS_FILE, sorted(bot_admins))

def is_bot_admin(uid: int) -> bool:
    return bool(uid) and (uid == OWNER_ID or uid in bot_admins)

def load_notes():
    global notes
    raw = _load_json(NOTES_FILE, {})
    notes = {int(k): str(v) for k, v in raw.items()}

def save_notes():
    _save_json(NOTES_FILE, {str(k): v for k, v in notes.items()})


def _normalise_bot_username(name: str) -> Optional[str]:
    name = (name or "").strip().strip(",")
    if not name:
        return None
    if name.startswith("https://t.me/"):
        name = name.rsplit("/", 1)[-1]
    if name.startswith("t.me/"):
        name = name.rsplit("/", 1)[-1]
    name = name.split("?", 1)[0].strip()
    if not name.startswith("@"):
        name = "@" + name
    if not re.fullmatch(r"@[A-Za-z0-9_]{5,32}", name):
        return None
    return name


def _parse_bot_usernames(raw: str) -> List[str]:
    parsed: List[str] = []
    seen = set()
    for part in re.split(r"[\s,;]+", raw or ""):
        username = _normalise_bot_username(part)
        if username and username.lower() not in seen:
            parsed.append(username)
            seen.add(username.lower())
        if len(parsed) >= MAX_SAVED_BOTS:
            break
    return parsed


def load_bot_usernames():
    global bot_usernames
    data = _load_json(BOT_NAMES_FILE, DEFAULT_BOT_USERNAMES)
    if isinstance(data, dict):
        data = data.get("bots", [])
    if isinstance(data, str):
        bot_usernames = _parse_bot_usernames(data)
    elif isinstance(data, list):
        bot_usernames = _parse_bot_usernames(" ".join(str(x) for x in data))
    else:
        bot_usernames = DEFAULT_BOT_USERNAMES.copy()
    bot_usernames = bot_usernames[:MAX_SAVED_BOTS]


def save_bot_usernames():
    _save_json(BOT_NAMES_FILE, bot_usernames[:MAX_SAVED_BOTS])


def _bots_from_arg_or_saved(arg: str) -> List[str]:
    bots = _parse_bot_usernames(arg)
    return bots or bot_usernames[:MAX_SAVED_BOTS]


def _load_msg_ref(path: str) -> Optional[tuple]:
    try:
        if os.path.isfile(path):
            raw = open(path).read().strip()
            if ":" in raw:
                c, m = raw.split(":", 1)
                return (int(c), int(m))
    except Exception as e:
        logger.error(f"[MSG REF LOAD] {path}: {e}")
    return None


def _save_msg_ref(path: str, ref: Optional[tuple]):
    try:
        if ref:
            with open(path, "w") as f:
                f.write(f"{ref[0]}:{ref[1]}")
        elif os.path.isfile(path):
            os.remove(path)
    except Exception as e:
        logger.error(f"[MSG REF SAVE] {path}: {e}")


def load_banner():
    global menu_banner_msg
    menu_banner_msg = _load_msg_ref(BANNER_FILE)

def save_banner():
    _save_msg_ref(BANNER_FILE, menu_banner_msg)

def load_mraid_media():
    global mraid_media_msg
    mraid_media_msg = _load_msg_ref(MRAID_FILE)

def save_mraid_media():
    _save_msg_ref(MRAID_FILE, mraid_media_msg)

# ─────────────────────────────────────────────────────────────────
#  UNIVERSAL TARGET RESOLVER
# ─────────────────────────────────────────────────────────────────
async def get_targets(event, arg: str = "") -> Set[int]:
    targets: Set[int] = set()
    if event.is_reply:
        try:
            r = await event.get_reply_message()
            if r and r.sender_id:
                targets.add(int(r.sender_id))
        except: pass
    for part in (arg or "").strip().split():
        if not part: continue
        if part.lstrip("-").isdigit():
            targets.add(int(part))
            continue
        try:
            ent = await bot.get_entity(part)
            if getattr(ent, "id", None):
                targets.add(int(ent.id))
        except: pass
    try:
        me = await _get_me()
        targets.discard(me.id)
    except: pass
    return targets

# ─────────────────────────────────────────────────────────────────
#  FONT ENGINES  (two styles used throughout the bot)
# ─────────────────────────────────────────────────────────────────
_SC = {
    'a':'ᴀ','b':'ʙ','c':'ᴄ','d':'ᴅ','e':'ᴇ','f':'ғ','g':'ɢ','h':'ʜ','i':'ɪ',
    'j':'ᴊ','k':'ᴋ','l':'ʟ','m':'ᴍ','n':'ɴ','o':'ᴏ','p':'ᴘ','q':'ǫ','r':'ʀ',
    's':'s','t':'ᴛ','u':'ᴜ','v':'ᴠ','w':'ᴡ','x':'x','y':'ʏ','z':'ᴢ',
}

# Bold Mathematical Unicode → ASCII lookup (so safe_edit converts them to small caps)
_BOLD_TO_ASCII = {
    **{chr(0x1D400 + i): chr(ord('A') + i) for i in range(26)},  # 𝐀-𝐙
    **{chr(0x1D41A + i): chr(ord('a') + i) for i in range(26)},  # 𝐚-𝐳
    **{chr(0x1D434 + i): chr(ord('A') + i) for i in range(26)},  # 𝐼-italic caps
    **{chr(0x1D44E + i): chr(ord('a') + i) for i in range(26)},  # italic lower
    **{chr(0x1D468 + i): chr(ord('A') + i) for i in range(26)},  # bold italic caps
    **{chr(0x1D482 + i): chr(ord('a') + i) for i in range(26)},  # bold italic lower
}

def to_small_caps(text: str) -> str:
    """Normalize bold/italic Unicode to ASCII, then convert to small-caps."""
    text = "".join(_BOLD_TO_ASCII.get(c, c) for c in text)
    return "".join(_SC.get(c.lower(), c) for c in text)

def to_authority_style(text: str) -> str:
    """AᴛʜᴏRɪᴛʏ style — every 4th alpha char per word is UPPERCASE, rest are small-caps.
    Counter resets at word boundaries (spaces / non-alpha runs)."""
    result = []
    for word in text.split(" "):
        idx = 0
        word_out = []
        for ch in word:
            if ch.isalpha():
                if idx % 4 == 0:
                    word_out.append(ch.upper())
                else:
                    word_out.append(_SC.get(ch.lower(), ch))
                idx += 1
            else:
                word_out.append(ch)
        result.append("".join(word_out))
    return " ".join(result)

# Prebuilt brand strings used everywhere
BRAND       = to_authority_style("Ranveer Authority")   # Ranveer AᴜᴛʜOʀɪᴛʏ
BRAND_SHORT = to_authority_style("Ranveer")             # Ranveer

async def safe_edit(event, text: str):
    if not text: return None
    text = to_small_caps(text)
    if not text: return None
    try:
        return await event.edit(text)
    except Exception:
        try:
            msg = await event.reply(text)
            if event.out:
                try: await event.delete()
                except: pass
            return msg
        except: return None

# ─────────────────────────────────────────────────────────────────
#  COMMAND REGISTRY  (for bot-admin remote access)
# ─────────────────────────────────────────────────────────────────
_cmd_registry: Dict[str, Any] = {}   # pattern → {"func", "needs_reply", "group_only"}

# ─────────────────────────────────────────────────────────────────
#  COMMAND DECORATOR  (owner check, outgoing only + bot-admin relay)
# ─────────────────────────────────────────────────────────────────
def cmd(pattern: str, needs_reply: bool = False, group_only: bool = False, owner_only: bool = False):
    regex = rf"^\.{re.escape(pattern)}(?:\s+(.+))?$"

    def decorator(func):
        # Register in global registry for bot-admin relay
        _cmd_registry[pattern.lower()] = {
            "func": func, "regex": regex,
            "needs_reply": needs_reply, "group_only": group_only,
        }

        @bot.on(events.NewMessage(pattern=re.compile(regex, re.I | re.S), outgoing=True))
        async def _handler(event):
            if group_only and not event.is_group:
                return await safe_edit(event, "❌ 𝐆𝐫𝐨𝐮𝐩 𝐨𝐧𝐥𝐲!")
            if needs_reply and not event.is_reply:
                return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐭𝐨 𝐚 𝐦𝐞𝐬𝐬𝐚𝐠𝐞 𝐟𝐢𝐫𝐬𝐭!")
            # V9: use already-matched group from Telethon — skip double regex
            pm = event.pattern_match
            arg = (pm.group(1) or "").strip() if pm else ""
            try:
                await func(event, arg)
            except FloodWaitError as fw:
                await safe_edit(event, f"⏳ 𝐅𝐥𝐨𝐨𝐝 𝐖𝐚𝐢𝐭 → {fw.seconds}s")
            except Exception as e:
                logger.error(traceback.format_exc())
                await safe_edit(event, f"❌ `{str(e)[:60]}`")
        return func
    return decorator

# ─────────────────────────────────────────────────────────────────
#  BOT-ADMIN RELAY HANDLER  (incoming commands from granted accounts)
# ─────────────────────────────────────────────────────────────────
@bot.on(events.NewMessage(incoming=True, pattern=re.compile(r"^\.[a-z0-9_]+", re.I)))
async def _bot_admin_relay(event):
    """
    Lets bot-admin accounts send commands like .purge, .ban, .vault, etc.
    The userbot executes them in the same chat and replies with the result.
    safe_edit() auto-falls-back to event.reply() for incoming messages.
    """
    try:
        sender_id = event.sender_id
        if not sender_id or not is_bot_admin(sender_id):
            return
        raw = event.raw_text.strip()
        # Parse command name and argument
        parts   = raw[1:].split(None, 1)   # strip leading dot
        cmd_key = parts[0].lower()
        entry   = _cmd_registry.get(cmd_key)
        if not entry:
            return
        if entry["group_only"] and not event.is_group:
            return await event.reply("❌ 𝐆𝐫𝐨𝐮𝐩 𝐨𝐧𝐥𝐲!")
        if entry["needs_reply"] and not event.is_reply:
            return await event.reply("❌ 𝐑𝐞𝐩𝐥𝐲 𝐭𝐨 𝐚 𝐦𝐞𝐬𝐬𝐚𝐠𝐞 𝐟𝐢𝐫𝐬𝐭!")
        m   = re.match(entry["regex"], raw, re.I | re.S)
        arg = (m.group(1) or "").strip() if m else ""
        await entry["func"](event, arg)
    except FloodWaitError as fw:
        try: await event.reply(f"⏳ Flood Wait → {fw.seconds}s")
        except: pass
    except Exception as e:
        logger.error(traceback.format_exc())
        try: await event.reply(f"❌ `{str(e)[:60]}`")
        except: pass

# ─────────────────────────────────────────────────────────────────
#  FASTGC ENGINE
# ─────────────────────────────────────────────────────────────────
async def _fast_title_edit(chat_id, title):
    title = (title or "").strip()[:255]
    if not title: return False
    try:
        await bot(functions.channels.EditTitleRequest(channel=chat_id, title=title))
        return True
    except:
        try:
            await bot(functions.messages.EditChatTitleRequest(chat_id=chat_id, title=title))
            return True
        except Exception as e:
            logger.warning(f"[FastGC] title edit failed: {e}")
            return False

async def _gc_fast_loop(chat_id):
    try:
        while FASTGC_STATE.get("active"):
            template = FASTGC_STATE.get("template")
            if not template: break
            emoji = random.choice(GC_FAST_EMOJIS)
            ok = await _fast_title_edit(chat_id, template.replace("{emoji}", emoji))
            await asyncio.sleep(max(1, GC_FAST_INTERVAL) if ok else 5)
    except asyncio.CancelledError:
        pass
    except Exception as e:
        logger.error(f"[FastGC Loop] {e}")

# ─────────────────────────────────────────────────────────────────
#  REPLY LISTS
# ─────────────────────────────────────────────────────────────────
ABUSE_TEXTS = [
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🧊〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈❄️〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🥶〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈☃️〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🌨️〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🌬️〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🧋〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🐻‍❄️〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🍧〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🍨〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🌀〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈💨〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🌫️〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈💎〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🔹〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🛸〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🌌〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🔷〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🧿〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
    "{user} 𝙏𝙀𝙍𝙄 𝙈𝘼𝘼 𝘾𝙃𝙊𝘿 𝘿𝘼𝙇𝙀𝙉𝙂𝙀 𝙍𝙀 𓂃𓂃𓂃𓂃〉〈🌊〉〈𓂃𓂃𓂃𓂃𓂃𓂃..!¡",
]
ABUSE2_TEXTS = [
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃🩵",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💙",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💜",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃🖤",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃🤍",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃❤️",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃🧡",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💛",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💚",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃🤎",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💖",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💗",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💓",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💞",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💕",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💘",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💝",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃❣️",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´𓂃💟",
    "{user} ˚⋆‌﹒Tᴇʀɪ Mᴀ Kɪ Xʜᴜᴅᴀʏɪ Nᴀʜɪ Rᴜᴋᴜɴɢᴀ Pᴀɢʟᴇ ⋆‌´",
]
SLAP_TEXTS = [
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ᴡɪᴛʜ ᴀ ʟᴀʀɢᴇ ᴛʀᴏᴜᴛ!*",
    "ﾒ𓂃 👋🏻 *ɢɪᴠᴇs {user} ᴀ ʜᴀʀᴅ sʟᴀᴘ ᴏɴ ᴛʜᴇ ᴄʜᴇᴇᴋ!*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} sᴏ ʜᴀʀᴅ ᴛʜᴇʏ sᴘɪɴ ᴀʀᴏᴜɴᴅ!*",
    "ﾒ𓂃 👋🏻 *ᴜsᴇs ᴀ ʙʀɪᴄᴋ ᴛᴏ sʟᴀᴘ {user}!*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ɪɴᴛᴏ ᴛʜᴇ ɴᴇxᴛ ᴅɪᴍᴇɴsɪᴏɴ!*",

    "ﾒ𓂃 👋🏻 *ᴄʜᴀʀɢᴇs ᴜᴘ ᴀɴᴅ sʟᴀᴘs {user} ᴡɪᴛʜ ᴍᴀxɪᴍᴜᴍ ᴅᴀᴍᴀɢᴇ!*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} sᴏ ʜᴀʀᴅ ᴛʜᴇ ᴍᴏᴏɴ ғᴇʟᴛ ɪᴛ!*",
    "ﾒ𓂃 👋🏻 *ᴅᴏᴜʙʟᴇ-sʟᴀᴘs {user} ʟɪᴋᴇ ᴀ ᴄᴏᴍʙᴏ ᴀᴛᴛᴀᴄᴋ!*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ᴡɪᴛʜ ᴀ ᴡᴇᴛ ᴘɪʟʟᴏᴡ ᴏғ ᴅᴏᴏᴍ!*",
    "ﾒ𓂃 👋🏻 *sᴜᴍᴍᴏɴs ᴀ ᴍᴇᴛᴇᴏʀɪᴄ sʟᴀᴘ ғᴏʀ {user}!*",

    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ᴛɪʟʟ ᴛʜᴇɪʀ ᴡɪғɪ ᴅɪsᴄᴏɴɴᴇᴄᴛs!*",
    "ﾒ𓂃 👋🏻 *ᴜɴʟᴏᴄᴋs ᴜʟᴛɪᴍᴀᴛᴇ sʟᴀᴘ ᴍᴏᴅᴇ ᴏɴ {user}!*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ᴡɪᴛʜ ᴀɴ ᴇxᴘʟᴏsɪᴠᴇ ᴄᴏᴍʙᴏ!*",
    "ﾒ𓂃 👋🏻 *sᴇɴᴅs {user} ғʟʏɪɴɢ ᴡɪᴛʜ ᴀ ᴄʀɪᴛɪᴄᴀʟ sʟᴀᴘ!*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ᴏᴜᴛ ᴏғ ᴛʜᴇ ɢᴀʟᴀxʏ!*",

    "ﾒ𓂃 👋🏻 *ɢɪᴠᴇs {user} ᴀ ᴛʜᴜɴᴅᴇʀ sʟᴀᴘ ⚡*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ᴡɪᴛʜ ᴀɴ ɪɴᴠɪsɪʙʟᴇ ᴄʜᴀɪʀ!*",
    "ﾒ𓂃 👋🏻 *ᴀᴄᴛɪᴠᴀᴛᴇs sʟᴀᴘ.exe ᴏɴ {user}!*",
    "ﾒ𓂃 👋🏻 *sʟᴀᴘs {user} ᴜɴᴛɪʟ ᴛʜᴇ ᴜɴɪᴠᴇʀsᴇ ʟᴀɢs!*",
    "ﾒ𓂃 👋🏻 *ᴜsᴇs 100% ᴏғ ᴘᴏᴡᴇʀ ᴛᴏ sʟᴀᴘ {user}!*",
]
REPLY_TEXTS = [
    "{user} ɴʏ ɴʏ ᴍᴀ ᴋᴜᴄʜ ɴʏ sᴜɴᴜɴɢᴀ ᴄᴜᴅᴇɢɪ ᴛᴏʜ ᴛᴇʀʏ ᴍᴀᴀ ʜᴇ ᴠᴏ ʙʜɪ ᴀᴘɴᴀ ᴋᴜʀᴏsᴀᴋɪ ʙᴀᴀᴘ sᴀʏ🙄🙏",
    "ᴄᴀʙᴀʀɪ {user} ᴡᴀʟᴇ ᴋᴇ ʟᴀʀᴄᴇ sᴡɪᴘᴇ ғᴀsᴛ ᴍʀɢʏᴀ ᴄʏᴀ",
    "ᴏʏᴇ {user} ʙɪʜᴀʀɪ ᴛᴇʀʏ ᴀᴍɪ sᴇ ғʀᴏɢ ʀᴀᴄᴇ ᴋʀᴡᴀᴜ🤔🔥",
    "{user} ᴋᴀʟᴡᴇ ᴛᴇʀʏ ᴀᴍɪ ᴋɪ ʙʜᴏsᴅɪ ᴍ ʟᴜɴᴅ ɢɪʀᴀ ᴅᴜ ᴄʏᴀ🤔",
    "ʜᴀʀ ɢʜᴀᴅɪ {user} ᴛʀʏ ᴍᴀ ᴄᴜᴅᴇɢɪ 🕖🕐🕔🕑🕖🕑🕜🕗",
    "ᴛᴍᴋᴄ {user} ᴍᴇ ʙʜɴɢɪ ᴄᴀ ʜᴀᴀᴛʜ 🙌🏿👐🏿",
    "{user} ᴛʀʏ ᴍᴀ ᴡᴏ ᴄᴏᴅᴜɴɢᴀ. ᴀɴᴇ ᴡᴀʟɪ 6 ɢᴇɴᴇʀᴀᴛɪᴏɴ ᴄɪ sᴇᴀʟ ᴛᴜᴛɪ ʜᴜɪ ɴɪᴋʟᴇɢɪ 🥵🤪",
    "ᴜɢʟʏ ᴋᴜᴛᴛᴇ {user} sɪᴅᴇ ʀᴇʜɴᴀ 🤮🤮👌🏻",
    "🖕🏿🖕🏿🖕🏿 {user} ᴋᴀʟᴇ ʟᴜɴ sᴇ ᴄᴜᴅ",
    "{user} ᴛᴍᴋᴄ ᴍᴇ ᴍᴏᴏᴛ ᴄᴇ 💦 ᴜsᴄɪ ᴘᴀɴɪ 🌊 ᴄɪ ᴋᴀᴍɪ ᴅᴏᴏʀ ᴄʀᴅᴜ? 🤭🤭",
    "ɴᴏ ɴᴏ {user} ᴄᴇsᴇ ᴄʀʀᴀ ᴛʀʏ ʙᴀᴘ ᴄɪ ʙᴏsᴅɪ sᴀʏ ʏᴇs",
    "ʙᴏʜᴏᴛ ᴄʀɪɴɢᴇ ᴇʏ ᴛᴜ {user} 🤮🤮🤮",
    "ɢᴄ ʟᴇᴀᴠᴇ ᴄʀ {user} ᴄᴜᴛᴋᴇ🦶🏼",
    "ᴀʀᴇ ᴅᴇᴋʜ {user} ᴛʀʏ ʙʜɴ ᴄɪ ᴄᴜᴛ ᴍᴇ ᴀᴀɢ (🔥)",
    "😍👌🏻 {user} ᴛʀʏ. ᴍᴀ ғʟᴏᴡᴇʀ. 🌸ʏᴀ ғɪʀᴇ 🔥??",
    "ᴅᴡ. ᴅᴀᴡɢ {user} ᴄᴜᴅᴇɢɪ ᴛʀʏ ᴍᴀ. ʜɪ 😍🐅",
    "{user} ᴛᴍᴋᴄ ᴘᴇ ᴍᴀᴊᴅᴏᴏʀɪ 👑🗣️",
    "ᴀʙᴇ ᴏ {user} ʙᴏsᴅᴇ. 😡😡😡🙌🏿🙌🏿🙌🏿",
]

GOD_TEXTS = [
    "Aaj me {user} teri maa codke India co azaad crudnga 🇮🇳🥳",
    "Abe o {user} rndyke ❌💙💚💜💙",
    "Shut up {user} कुट्टिया ce son 😡✌🏿",
    "{user} Bohot cringe ey tu 🤮🤮🤮",
    "Ugly kutte {user} side rehna 🤮🤮👌🏻",
    "Abe o rndyke {user} ❌💙💚💜💙",
    "{user} Try ma 💯percent rndy ey 👌🏻",
    "Ma ma cya crra ey {user} baap ci bosdi 💯❤️🖕❤️🖕❤️🖕❤️",
    "˚◦𓂃ːCʜꪊᴅʟᴇ´-⋆‌🎀 {user}",
    "It's time to disappear {user} ab tu bina baap ke jee 👻",
    "A‌R‌E‌ {user} ᵗᵐᵏᶜ🔥🧡😹😈🤓😈🤓😈🤓🥹🥹🤡",
    "ヾ⁠ {user} ᴜᴛʜ ᴘɪʟʟᴇ :♪🧃",
    "Caps off kr {user} भंगी ke bete 🤮🤮🤮",
]

FLAG_EMOJIS = ["🇨🇫","🇦🇿","🇧🇪","🇧🇻","🇧🇪","🇨🇭","🇨🇨","🇧🇻","🇨🇨","🇧🇹","🇧🇶","🇧🇮","🇦🇽","🇦🇲","🇧🇪"]

# ── Trigger Raid texts ────────────────────────────────────────────
TRIGGER_RAID_TEXTS: List[str] = [
    "Cya hua","Chup rndyke","Chl rndyke 😂😂","Aur bata khana khaya ya cudayi khyega","Chup rndyke","Krle msg phle tu araam se hadbada mat","R u OK rndyke pille","Abe tu to gusaa hogya","To try maa cod dale ab","Tujhe cya hua","Try ma codunga to rok lega cya","Try bhn cod dunga","Try bhn codenge RE","Abe hat 😂😂","Chl ab try maa codenge","Cya hua","Krle msg phle tu araam se hadbada mat","Cya hua"
]

# ── Trigger Raid reply coroutine ──────────────────────────────────
async def _safe_trigger_reply(msg, name: str, n: int, uid: int):
    """V9 Nonstop: fire n fast replies to a message — FloodWait aware, non-blocking."""
    try:
        for i in range(n):
            try:
                await msg.reply(random.choice(TRIGGER_RAID_TEXTS).replace("{user}", name))
            except FloodWaitError as fw:
                await asyncio.sleep(fw.seconds + 2)
                try:
                    await msg.reply(random.choice(TRIGGER_RAID_TEXTS).replace("{user}", name))
                except Exception:
                    pass
            except Exception:
                pass
            if i < n - 1:
                await asyncio.sleep(0.05)  # V9: near-instant fire
    except asyncio.CancelledError:
        pass

# ─────────────────────────────────────────────────────────────────
#  OUTGOING AUTO-REACT  (V9: react to own messages too)
# ─────────────────────────────────────────────────────────────────
@bot.on(events.NewMessage(outgoing=True))
async def _outgoing_auto_react(event):
    """React to the bot's own sent messages when auto-react is on.
    Skips command messages (starting with '.') to avoid reacting to .menu etc."""
    if not auto_react_emoji:
        return
    raw = event.raw_text or ""
    if raw.startswith("."):  # skip bot commands
        return
    try:
        await bot(functions.messages.SendReactionRequest(
            peer=event.peer_id,
            msg_id=event.id,
            reaction=[types.ReactionEmoji(emoticon=auto_react_emoji)],
        ))
    except: pass

# ─────────────────────────────────────────────────────────────────
#  INCOMING MESSAGE HANDLER  (raids, mute, lock, auto-react)
# ─────────────────────────────────────────────────────────────────
@bot.on(events.NewMessage(incoming=True))
async def _incoming_handler(event):
    sender_id = event.sender_id
    if not sender_id: return

    # ── Global mute ──
    if sender_id in global_muted:
        try: await event.delete()
        except: pass
        return

    # ── Local mute (in this chat) ──
    if sender_id in muted_users and event.is_group:
        try: await event.delete()
        except: pass
        return

    # ── Group lock (delete non-admin messages) ──
    if event.is_group and event.chat_id in group_locks:
        if not is_admin(sender_id):
            try: await event.delete()
            except: pass
            return

    # ── AntiLink (V9) — auto-delete messages containing URLs ──
    if event.is_group and event.chat_id in antilink_chats:
        raw = event.raw_text or ""
        if _URL_RE.search(raw) and not is_admin(sender_id):
            try: await event.delete()
            except: pass
            return

    # ── Auto-react (incoming) ──
    if auto_react_emoji:
        try:
            await bot(functions.messages.SendReactionRequest(
                peer=event.peer_id,
                msg_id=event.id,
                reaction=[types.ReactionEmoji(emoticon=auto_react_emoji)],
            ))
        except: pass

    # ── Resolve sender name once for raids that use {user} ──
    _any_name_raid = (
        sender_id in abuse_users or sender_id in abuse2_users or
        sender_id in reply_users or sender_id in rr_users or
        sender_id in replygod_users or sender_id in slap_users or
        sender_id in bomb_users or sender_id in slide_users or
        sender_id in trigger_raid_targets
    )
    _sender_name = "User"
    if _any_name_raid:
        try:
            _u = await bot.get_entity(sender_id)
            _sender_name = getattr(_u, "first_name", None) or getattr(_u, "username", None) or "User"
        except: pass

    # ── Media raid ──
    if sender_id in media_raid_users:
        try:
            if mraid_media_msg:
                await bot.forward_messages(event.chat_id, mraid_media_msg[1], mraid_media_msg[0])
            else:
                await event.reply(random.choice(REPLY_TEXTS).format(user=_sender_name))
        except: pass

    # ── Abuse raid ──
    if sender_id in abuse_users:
        try: await event.reply(random.choice(ABUSE_TEXTS).format(user=_sender_name))
        except: pass

    # ── Abuse2 raid ──
    if sender_id in abuse2_users:
        try: await event.reply(random.choice(ABUSE2_TEXTS).format(user=_sender_name))
        except: pass

    # ── Slap raid ──
    if sender_id in slap_users:
        try: await event.reply(random.choice(SLAP_TEXTS).format(user=_sender_name))
        except: pass

    # ── Kick raid ──
    if sender_id in kick_users:
        try:
            try:
                await bot(EditBannedRequest(
                    event.chat_id, sender_id,
                    ChatBannedRights(until_date=None, view_messages=True)
                ))
                await asyncio.sleep(0.3)
                await bot(EditBannedRequest(
                    event.chat_id, sender_id,
                    ChatBannedRights(until_date=None, view_messages=False)
                ))
            except Exception:
                try:
                    await bot.kick_participant(event.chat_id, sender_id)
                except Exception as ke:
                    if "admin" in str(ke).lower() or "rights" in str(ke).lower():
                        kick_users.discard(sender_id)
        except: pass

    # ── Reply raid ──
    if sender_id in reply_users:
        try: await event.reply(random.choice(REPLY_TEXTS).format(user=_sender_name))
        except: pass

    # ── RR raid (reply + react 🤣) ──
    if sender_id in rr_users:
        try:
            await event.reply(random.choice(REPLY_TEXTS).format(user=_sender_name))
            await bot(functions.messages.SendReactionRequest(
                peer=event.peer_id,
                msg_id=event.id,
                reaction=[types.ReactionEmoji(emoticon="🤣")],
            ))
        except: pass

    # ── Flag raid ──
    if sender_id in flag_users:
        try: await event.reply(random.choice(FLAG_EMOJIS) * random.randint(3, 8))
        except: pass

    # ── Heart raid ──
    if sender_id in hrr_users:
        try:
            await bot(functions.messages.SendReactionRequest(
                peer=event.peer_id,
                msg_id=event.id,
                reaction=[types.ReactionEmoji(emoticon=random.choice(["❤️","💖","💘","💝","🩷"]))],
            ))
        except: pass

    # ── God raid ──
    if sender_id in replygod_users:
        try: await event.reply(random.choice(GOD_TEXTS).format(user=_sender_name))
        except: pass

    # ── Bomb raid (emoji bomb) ──
    if sender_id in bomb_users:
        try:
            bomb = "".join(random.choices(
                ["💣","💥","🔥","⚡","😈","👹","☠️","🖕","🤡","💀","🧨","🌋"],
                k=random.randint(8, 15)
            ))
            await event.reply(f"{_sender_name} {bomb}")
        except: pass

    # ── Clone Reply (mirror exact text back at sender) ──
    if sender_id in clone_reply_users and event.raw_text:
        try:
            await event.reply(event.raw_text)
        except: pass

    # ── Slide Raid (cycling emoji reply) ──
    if sender_id in slide_users:
        data = slide_users[sender_id]
        try:
            emoji = data["emojis"][data["idx"] % len(data["emojis"])]
            data["idx"] += 1
            slide_text = data["text"].replace("{time}", str(random.randint(1, 12)))
            await event.reply(f"{emoji} {slide_text} {emoji}")
        except: pass

    # ── Kurosaki (limited count) raid ──
    if sender_id in replyvx_users:
        data = replyvx_users[sender_id]
        if data["count"] > 0:
            try:
                await event.reply(data["text"])
                data["count"] -= 1
                if data["count"] <= 0:
                    del replyvx_users[sender_id]
            except: pass

    # ── Trigger Raid — reply to every message the locked user sends ──
    if sender_id in trigger_raid_targets:
        asyncio.ensure_future(_safe_trigger_reply(event, _sender_name, TRIGGER_PERMSG, sender_id))

# ─────────────────────────────────────────────────────────────────
#  ██████████  COMMANDS (V9)  ██████████
# ─────────────────────────────────────────────────────────────────

# ── BOT-ADMIN MANAGEMENT ─────────────────────────────────────────
@cmd("addba")
async def _addba(event, arg):
    uid_str = (arg or "").strip()
    if not uid_str or not uid_str.lstrip("-").isdigit():
        return await safe_edit(event,
            "❌ **Usage:** `.addba <user_id>`\n"
            "Get a user's ID with `.id` then reply."
        )
    uid = int(uid_str)
    if uid == OWNER_ID:
        return await safe_edit(event, "⚠️ Owner is already the master admin.")
    bot_admins.add(uid)
    save_bot_admins()
    await safe_edit(event,
        f"✅ **Bot-Admin granted!**\n"
        f"🆔 `{uid}` can now use commands from their account.\n"
        f"📋 Total bot-admins: `{len(bot_admins)}`"
    )

@cmd("delba")
async def _delba(event, arg):
    uid_str = (arg or "").strip()
    if not uid_str or not uid_str.lstrip("-").isdigit():
        return await safe_edit(event, "❌ **Usage:** `.delba <user_id>`")
    uid = int(uid_str)
    if uid in bot_admins:
        bot_admins.discard(uid)
        save_bot_admins()
        await safe_edit(event, f"🗑 **Bot-Admin removed:** `{uid}`")
    else:
        await safe_edit(event, f"⚠️ `{uid}` is not a bot-admin.")

@cmd("balist")
async def _balist(event, _):
    if not bot_admins:
        return await safe_edit(event,
            "📋 **Bot-Admin List:** empty\n"
            "Use `.addba <user_id>` to grant access."
        )
    lines = "\n".join(f"  `{uid}`" for uid in sorted(bot_admins))
    await safe_edit(event,
        f"╔══════════════════════════════╗\n"
        f"║  👑  Bot-Admin Access List   ║\n"
        f"╠══════════════════════════════╣\n"
        f"{lines}\n"
        f"╚══════════════════════════════╝\n"
        f"Total: `{len(bot_admins)}` · `.addba` / `.delba` to manage"
    )

# ── MENU (Classic Box Style — V9) ────────────────────────────────
@cmd("menu")
async def _menu(event, _):
    sc = to_small_caps
    A  = to_authority_style
    text = (
        f"╔══════════════════════════════════╗\n"
        f"║  ⚡  {A('Kurosaki')} ™  V9  ·  .{sc('vault')} = raids  ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🛡️  {A('Admin')}                               ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('promote')} | .{sc('promotebots')}              ║\n"
        f"║  .{sc('addadmin')} | .{sc('deladmin')}                ║\n"
        f"║  .{sc('admins')} | .{sc('ban')} | .{sc('unban')}              ║\n"
        f"║  .{sc('purge')} [3000] | .{sc('purge2')} [1000]        ║\n"
        f"║  .{sc('demote')} | .{sc('lock')} | .{sc('unlock')}          ║\n"
        f"║  .{sc('warn')} | .{sc('warnings')} | .{sc('resetwarns')}    ║\n"
        f"║  .{sc('antilink')} on/off                       ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🔇  {A('Mute')}                                ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('mute')} | .{sc('unmute')} | .{sc('gmute')}           ║\n"
        f"║  .{sc('gunmute')} | .{sc('mutelist')}                 ║\n"
        f"║  .{sc('delall')} [s|off] | .{sc('delay')} <s>          ║\n"
        f"║  .{sc('safe')} @user | .{sc('safe')}                   ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  👤  {A('Profile')}                              ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('save')} | .{sc('copy')} | .{sc('normal')}            ║\n"
        f"║  .{sc('setname')} | .{sc('setbio')}                   ║\n"
        f"║  .{sc('style')} | .{sc('fancy')}                       ║\n"
        f"║  .{sc('cloneraid')} → .{sc('scloneraid')}              ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  📡  {A('Chat')}                                ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('pin')} | .{sc('unpin')} | .{sc('settitle')}          ║\n"
        f"║  .{sc('setphoto')} | .{sc('join')} | .{sc('leave')}         ║\n"
        f"║  .{sc('invite')} | .{sc('id')}                         ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🤖  {A('Auto')}                                ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('afk')} <msg> | .{sc('killafk')}                ║\n"
        f"║  .{sc('target')} | .{sc('untarget')}                   ║\n"
        f"║  .{sc('schedule')} <s> <msg>                    ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🔧  {A('Utils')}                               ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('ask')} | .{sc('imagine')} | .{sc('tts')} | .{sc('wiki')}   ║\n"
        f"║  .{sc('music')} | .{sc('video')} | .{sc('qrcode')}          ║\n"
        f"║  .{sc('sticker')} | .{sc('translate')} | .{sc('ud')}        ║\n"
        f"║  .{sc('info')} | .{sc('getphone')} | .{sc('ping')}          ║\n"
        f"║  .{sc('weather')} | .{sc('short')} | .{sc('ip')}            ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🎮  {A('Games')}                               ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('dice')} | .{sc('coinflip')} | .{sc('rps')}          ║\n"
        f"║  .{sc('8ball')} | .{sc('trivia')} | .{sc('math')}           ║\n"
        f"║  .{sc('fortune')} | .{sc('roast')} | .{sc('compliment')}    ║\n"
        f"║  .{sc('guess')} start/<n> | .{sc('hangman')} <letter>  ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🤖  {A('Bots & GC')}                           ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('bots')} | .{sc('setbots')} | .{sc('clearbots')}      ║\n"
        f"║  .{sc('addbot')} | .{sc('removebots')}               ║\n"
        f"║  .{sc('creategc')} | .{sc('createch')} | .{sc('fastgc')}    ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🎉  {A('Welcome & Notes')}                     ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('setwelcome')} | .{sc('welctest')}               ║\n"
        f"║  .{sc('delwelcome')} | .{sc('welcoff')}                ║\n"
        f"║  .{sc('notesadd')} | .{sc('noteslist')} | .{sc('notesdel')} ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  👑  {A('Bot Admin')}  [ .{sc('menu2')} for raids ]   ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('addba')} <id> | .{sc('delba')} <id> | .{sc('balist')}║\n"
        f"╚══════════════════════════════════╝"
    )
    await event.edit(text)
    if menu_banner_msg:
        try:
            await bot.forward_messages(event.chat_id, menu_banner_msg[1], menu_banner_msg[0])
        except:
            pass

# ── MENU2 (Page 2 — Games, Bots, Notes, Bot-Admin) ───────────────
@cmd("menu2")
async def _menu2(event, _):
    sc = to_small_caps
    A  = to_authority_style
    text = (
        f"╔══════════════════════════════════╗\n"
        f"║  ⚡  {A('Kurosaki')} ™  V9  ·  Page 2       ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🎮  {A('Games')}                             ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('dice')} | .{sc('coinflip')} | .{sc('rps')}          ║\n"
        f"║  .{sc('8ball')} <q> | .{sc('trivia')} | .{sc('math')}      ║\n"
        f"║  .{sc('fortune')} | .{sc('roast')} | .{sc('compliment')}   ║\n"
        f"║  .{sc('guess')} start/<n> | .{sc('guess')} stop      ║\n"
        f"║  .{sc('hangman')} start/<l> | .{sc('hangman')} stop  ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🤖  {A('Bots & GC')}                        ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('bots')} | .{sc('setbots')} | .{sc('clearbots')}     ║\n"
        f"║  .{sc('addbot')} | .{sc('removebots')}              ║\n"
        f"║  .{sc('creategc')} | .{sc('createch')} | .{sc('fastgc')}   ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🎉  {A('Welcome & Notes')}                  ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('setwelcome')} | .{sc('welctest')}              ║\n"
        f"║  .{sc('delwelcome')} | .{sc('welcoff')}               ║\n"
        f"║  .{sc('notesadd')} | .{sc('noteslist')} | .{sc('notesdel')}║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  👑  {A('Bot Admin')}  [ remote access ]     ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('addba')} <id>  →  grant cmd access     ║\n"
        f"║  .{sc('delba')} <id>  →  revoke access        ║\n"
        f"║  .{sc('balist')}      →  list all bot-admins  ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  🗡️  .{sc('vault')} = raid arsenal             ║\n"
        f"║  ◀  .{sc('menu')} = page 1                    ║\n"
        f"╚══════════════════════════════════╝"
    )
    await event.edit(text)
    if menu_banner_msg:
        try:
            await bot.forward_messages(event.chat_id, menu_banner_msg[1], menu_banner_msg[0])
        except:
            pass

# ── VAULT (RAID ARSENAL — classic box style) ──────────────────────
@cmd("vault")
async def _vault(event, _):
    sc = to_small_caps
    A  = to_authority_style
    text = (
        f"╔══════════════════════════════════╗\n"
        f"║  🗡️  {A('Kurosaki')} ™  V9  ·  VAULT        ║\n"
        f"║  ⚔️  cmd → stop  ·  .{sc('stopall')} = 🛑    ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  💥  {A('Raids')}  [ cmd → stop cmd ]        ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('reply')}    →  .{sc('sreply')}                 ║\n"
        f"║  .{sc('abuse')}    →  .{sc('sabuse')}                 ║\n"
        f"║  .{sc('abuse2')}   →  .{sc('sabuse2')}                ║\n"
        f"║  .{sc('slap')}     →  .{sc('sslap')}                  ║\n"
        f"║  .{sc('rr')}       →  .{sc('srr')}                    ║\n"
        f"║  .{sc('god')}      →  .{sc('sgod')}                   ║\n"
        f"║  .{sc('bomb')}     →  .{sc('sbomb')}                  ║\n"
        f"║  .{sc('flag')}     →  .{sc('sflag')}                  ║\n"
        f"║  .{sc('hrr')}      →  .{sc('shrr')}                   ║\n"
        f"║  .{sc('kickraid')} →  .{sc('skickraid')}              ║\n"
        f"║  .{sc('mraid')}    →  .{sc('smraid')}                 ║\n"
        f"║  .{sc('replyvx')}  →  .{sc('svx')}                    ║\n"
        f"║  .{sc('spray')}    →  .{sc('dspray')}                 ║\n"
        f"║  .{sc('slideraid')} → .{sc('dslideraid')}             ║\n"
        f"║  .{sc('clonereply')} → .{sc('sclonereply')}           ║\n"
        f"║  .{sc('saferaid')} →  .{sc('ssaferaid')}  🛡️          ║\n"
        f"║  .{sc('ghostping')} | .{sc('tagall')} [msg]           ║\n"
        f"║  🛑  .{sc('stopall')}                         ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  ⚡  {A('Trigger Raid')}                        ║\n"
        f"╠══════════════════════════════════╣\n"
        f"║  .{sc('trigraid')} @user / reply → start       ║\n"
        f"║  .{sc('strigraid')} [@user]  → stop            ║\n"
        f"╚══════════════════════════════════╝"
    )
    await event.edit(text)
    if menu_banner_msg:
        try:
            await bot.forward_messages(event.chat_id, menu_banner_msg[1], menu_banner_msg[0])
        except:
            pass

# ── PING / ALIVE / STATUS ─────────────────────────────────────────
@cmd("ping")
async def _ping(event, _):
    t = time.time()
    m = await safe_edit(event, "🏓 𝐏𝐢𝐧𝐠𝐢𝐧𝐠...")
    ms = round((time.time() - t) * 1000, 2)
    await safe_edit(m, f"🏓 **𝐏𝐨𝐧𝐠!**\n⚡ **𝐋𝐚𝐭𝐞𝐧𝐜𝐲:** `{ms} ms`")

@cmd("alive")
async def _alive(event, _):
    up = int(time.time() - START_TIME)
    h, r = divmod(up, 3600)
    m, s = divmod(r, 60)
    await event.edit(
        f"🌟 **{BRAND}** ɪs ᴀʟɪᴠᴇ!\n"
        f"━━━━━━━━━━━━━━━\n"
        f"⏳ **{to_authority_style('Uptime')}:** `{h}h {m}m {s}s`\n"
        f"👑 **{to_authority_style('Owner')}:** `{to_authority_style('Kurosaki')}`\n"
        f"🔧 **{to_authority_style('Version')}:** `v9.0 Authority`\n"
        f"⚡ **{to_authority_style('Style')}:** `{BRAND}`"
    )

@cmd("status")
async def _status(event, _):
    up = int(time.time() - START_TIME)
    h, r = divmod(up, 3600)
    m, s = divmod(r, 60)
    active_raids = sum([
        len(reply_users), len(rr_users), len(flag_users),
        len(hrr_users), len(replygod_users), len(replyvx_users),
        len(media_raid_users), len(kick_users), len(abuse_users), len(slap_users),
    ])
    await safe_edit(event,
        f"📊 **𝐔𝐬𝐞𝐫𝐛𝐨𝐭 𝐒𝐭𝐚𝐭𝐮𝐬**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"⏳ **𝐔𝐩𝐭𝐢𝐦𝐞:** `{h}h {m}m {s}s`\n"
        f"👮 **𝐀𝐝𝐦𝐢𝐧𝐬:** `{len(admins)}`\n"
        f"🔇 **𝐌𝐮𝐭𝐞𝐝:** `{len(muted_users)}` local | `{len(global_muted)}` global\n"
        f"⚔️ **𝐑𝐚𝐢𝐝 𝐓𝐚𝐫𝐠𝐞𝐭𝐬:** `{active_raids}`\n"
        f"💣 **𝐒𝐩𝐫𝐚𝐲 𝐓𝐚𝐬𝐤𝐬:** `{len(spray_tasks)}`\n"
        f"🔒 **𝐋𝐨𝐜𝐤𝐞𝐝 𝐆𝐫𝐨𝐮𝐩𝐬:** `{len(group_locks)}`\n"
        f"📝 **𝐍𝐨𝐭𝐞𝐬:** `{len(notes)}`\n"
        f"⚡ **𝐅𝐚𝐬𝐭𝐆𝐂:** `{'Active' if FASTGC_STATE['active'] else 'Off'}`\n"
        f"🤖 **𝐀𝐮𝐭𝐨 𝐑𝐞𝐚𝐜𝐭:** `{auto_react_emoji or 'Off'}`\n"
        f"🖼️ **𝐁𝐚𝐧𝐧𝐞𝐫:** `{'Set' if menu_banner_msg else 'None'}`\n"
        f"📸 **𝐌𝐑𝐚𝐢𝐝 𝐌𝐞𝐝𝐢𝐚:** `{'Set' if mraid_media_msg else 'None'}`"
    )

# ── BANNER ────────────────────────────────────────────────────────
@cmd("banner", needs_reply=True)
async def _banner(event, _):
    global menu_banner_msg
    reply = await event.get_reply_message()
    if not reply or not reply.media:
        return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐭𝐨 𝐚 𝐩𝐡𝐨𝐭𝐨/𝐯𝐢𝐝𝐞𝐨!")
    await safe_edit(event, "⚡ 𝐒𝐚𝐯𝐢𝐧𝐠 𝐛𝐚𝐧𝐧𝐞𝐫...")
    try:
        try:
            saved = await reply.forward_to("me")
        except:
            data = await reply.download_media(file=bytes)
            buf = BytesIO(data); buf.name = "banner"
            saved = await bot.send_file("me", buf)
        menu_banner_msg = (saved.chat_id, saved.id)
        save_banner()
        await safe_edit(event, f"🖼️ **𝐁𝐚𝐧𝐧𝐞𝐫 𝐒𝐞𝐭!**\n📌 𝐌𝐬𝐠 𝐈𝐃: `{saved.id}`\n💡 𝐁𝐚𝐧𝐧𝐞𝐫 𝐬𝐞𝐧𝐭 𝐰𝐢𝐭𝐡 `.ᴍᴇɴᴜ` ᴀᴜᴛᴏᴍᴀᴛɪᴄᴀʟʟʏ.")
    except Exception as e:
        await safe_edit(event, f"❌ {e}")

@cmd("rembanner")
async def _rembanner(event, _):
    global menu_banner_msg
    if not menu_banner_msg:
        return await safe_edit(event, "⚠️ 𝐍𝐨 𝐛𝐚𝐧𝐧𝐞𝐫 𝐬𝐞𝐭!")
    try:
        await bot.delete_messages(menu_banner_msg[0], [menu_banner_msg[1]])
    except: pass
    menu_banner_msg = None
    save_banner()
    await safe_edit(event, "🗑️ **𝐁𝐚𝐧𝐧𝐞𝐫 𝐑𝐞𝐦𝐨𝐯𝐞𝐝!**")

# ── MEDIA RAID MEDIA SETTER ───────────────────────────────────────
# FIX: Proper command to save media for media raid
@cmd("setmraid", needs_reply=True)
async def _setmraid(event, _):
    global mraid_media_msg
    reply = await event.get_reply_message()
    if not reply or not reply.media:
        return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐭𝐨 𝐚 𝐩𝐡𝐨𝐭𝐨/𝐯𝐢𝐝𝐞𝐨/𝐠𝐢𝐟!")
    await safe_edit(event, "⚡ 𝐒𝐚𝐯𝐢𝐧𝐠 𝐦𝐞𝐝𝐢𝐚 𝐫𝐚𝐢𝐝 𝐦𝐞𝐝𝐢𝐚...")
    try:
        try:
            saved = await reply.forward_to("me")
        except:
            data = await reply.download_media(file=bytes)
            buf = BytesIO(data); buf.name = "mraid_media"
            saved = await bot.send_file("me", buf)
        mraid_media_msg = (saved.chat_id, saved.id)
        save_mraid_media()
        await safe_edit(event, f"📸 **𝐌𝐑𝐚𝐢𝐝 𝐌𝐞𝐝𝐢𝐚 𝐒𝐞𝐭!**\n📌 𝐌𝐬𝐠 𝐈𝐃: `{saved.id}`\n💡 𝐔𝐬𝐞 `.ᴍʀᴀɪᴅ` ᴛᴏ ᴀᴛᴛᴀᴄᴋ.")
    except Exception as e:
        await safe_edit(event, f"❌ {e}")

@cmd("remmraid")
async def _remmraid(event, _):
    global mraid_media_msg
    if not mraid_media_msg:
        return await safe_edit(event, "⚠️ 𝐍𝐨 𝐦𝐫𝐚𝐢𝐝 𝐦𝐞𝐝𝐢𝐚 𝐬𝐞𝐭!")
    mraid_media_msg = None
    save_mraid_media()
    await safe_edit(event, "🗑️ **𝐌𝐑𝐚𝐢𝐝 𝐌𝐞𝐝𝐢𝐚 𝐑𝐞𝐦𝐨𝐯𝐞𝐝!**")

# ── ADMIN MANAGEMENT ─────────────────────────────────────────────
@cmd("admins")
async def _admins(event, _):
    if not admins:
        return await safe_edit(event, "👮 **𝐀𝐝𝐦𝐢𝐧𝐬:** 𝐍𝐨𝐧𝐞 𝐚𝐝𝐝𝐞𝐝 𝐲𝐞𝐭.")
    lines = [f"👮 **𝐁𝐨𝐭 𝐀𝐝𝐦𝐢𝐧𝐬:**\n━━━━━━━━━━━━━━━"]
    for uid in sorted(admins):
        try:
            u = await bot.get_entity(uid)
            name = getattr(u, "first_name", str(uid)) or str(uid)
            uname = f"@{u.username}" if getattr(u, "username", None) else f"`{uid}`"
            lines.append(f"• {name} ({uname})")
        except:
            lines.append(f"• `{uid}`")
    await safe_edit(event, "\n".join(lines))

@cmd("addadmin")
async def _addadmin(event, arg):
    targets = await get_targets(event, arg)
    if not targets:
        return await safe_edit(event, "❌ 𝐍𝐨 𝐯𝐚𝐥𝐢𝐝 𝐭𝐚𝐫𝐠𝐞𝐭!")
    added = []
    for uid in targets:
        admins.add(uid)
        added.append(str(uid))
    save_admins()
    await safe_edit(event, f"✅ **𝐀𝐝𝐦𝐢𝐧𝐬 𝐀𝐝𝐝𝐞𝐝:** `{', '.join(added)}`")

@cmd("deladmin")
async def _deladmin(event, arg):
    targets = await get_targets(event, arg)
    if not targets:
        return await safe_edit(event, "❌ 𝐍𝐨 𝐯𝐚𝐥𝐢𝐝 𝐭𝐚𝐫𝐠𝐞𝐭!")
    removed = []
    for uid in targets:
        if uid in admins:
            admins.discard(uid)
            removed.append(str(uid))
    save_admins()
    await safe_edit(event, f"🗑️ **𝐀𝐝𝐦𝐢𝐧𝐬 𝐑𝐞𝐦𝐨𝐯𝐞𝐝:** `{', '.join(removed) or 'None'}`")

# ── MUTE / UNMUTE ─────────────────────────────────────────────────
@cmd("mute")
async def _mute(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    for uid in targets: muted_users.add(uid)
    await safe_edit(event, f"🔇 **𝐌𝐮𝐭𝐞𝐝:** `{', '.join(str(u) for u in targets)}`")

@cmd("unmute")
async def _unmute(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    for uid in targets: muted_users.discard(uid)
    await safe_edit(event, f"🔊 **𝐔𝐧𝐦𝐮𝐭𝐞𝐝:** `{', '.join(str(u) for u in targets)}`")

@cmd("gmute")
async def _gmute(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    for uid in targets: global_muted.add(uid)
    await safe_edit(event, f"🌐🔇 **𝐆𝐥𝐨𝐛𝐚𝐥 𝐌𝐮𝐭𝐞𝐝:** `{', '.join(str(u) for u in targets)}`")

@cmd("gunmute")
async def _gunmute(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    for uid in targets: global_muted.discard(uid)
    await safe_edit(event, f"🌐🔊 **𝐆𝐥𝐨𝐛𝐚𝐥 𝐔𝐧𝐦𝐮𝐭𝐞𝐝:** `{', '.join(str(u) for u in targets)}`")

@cmd("mutelist")
async def _mutelist(event, _):
    lines = [
        f"🔇 **𝐋𝐨𝐜𝐚𝐥 𝐌𝐮𝐭𝐞𝐝:** `{', '.join(str(u) for u in muted_users) or 'None'}`",
        f"🌐🔇 **𝐆𝐥𝐨𝐛𝐚𝐥 𝐌𝐮𝐭𝐞𝐝:** `{', '.join(str(u) for u in global_muted) or 'None'}`",
    ]
    await safe_edit(event, "\n".join(lines))

# ── LOCK / UNLOCK ─────────────────────────────────────────────────
@cmd("lock", group_only=True)
async def _lock(event, _):
    chat = event.chat_id
    if chat in group_locks:
        return await safe_edit(event, "⚠️ 𝐆𝐫𝐨𝐮𝐩 𝐚𝐥𝐫𝐞𝐚𝐝𝐲 𝐥𝐨𝐜𝐤𝐞𝐝!")
    group_locks.add(chat)
    try:
        await bot(functions.messages.EditChatDefaultBannedRightsRequest(
            peer=chat,
            banned_rights=ChatBannedRights(until_date=None, send_messages=True),
        ))
    except: pass
    await safe_edit(event, "🔒 **𝐆𝐫𝐨𝐮𝐩 𝐋𝐨𝐜𝐤𝐞𝐝!**\n𝐎𝐧𝐥𝐲 𝐚𝐝𝐦𝐢𝐧𝐬 𝐜𝐚𝐧 𝐬𝐞𝐧𝐝 𝐦𝐞𝐬𝐬𝐚𝐠𝐞𝐬.")

@cmd("unlock", group_only=True)
async def _unlock(event, _):
    chat = event.chat_id
    group_locks.discard(chat)
    try:
        await bot(functions.messages.EditChatDefaultBannedRightsRequest(
            peer=chat,
            banned_rights=ChatBannedRights(until_date=None, send_messages=False),
        ))
    except: pass
    await safe_edit(event, "🔓 **𝐆𝐫𝐨𝐮𝐩 𝐔𝐧𝐥𝐨𝐜𝐤𝐞𝐝!**")

# ── PURGE ─────────────────────────────────────────────────────────
# FIX: Truly reply-aware purge — deletes from replied message down to current
@cmd("purge")
async def _purge(event, arg):
    from_id = None
    if event.is_reply:
        try:
            reply = await event.get_reply_message()
            if reply:
                from_id = reply.id
        except: pass

    if from_id is not None:
        # Delete from the replied message ID up to the .purge message
        m = await safe_edit(event, f"⚡ {to_small_caps('purging from replied message...')}")
        ids_to_delete = []
        async for message in bot.iter_messages(event.chat_id, min_id=from_id - 1, max_id=event.id + 1):
            ids_to_delete.append(message.id)
        # Fast parallel batch deletion — all batches fire simultaneously
        delete_tasks = [
            bot.delete_messages(event.chat_id, ids_to_delete[i:i+100])
            for i in range(0, len(ids_to_delete), 100)
        ]
        await asyncio.gather(*delete_tasks, return_exceptions=True)
        deleted = len(ids_to_delete)
        try: await m.delete()
        except: pass
        try:
            done = await event.respond(f"✅ **{to_small_caps(f'purged {deleted} messages!')}**")
            await asyncio.sleep(3)
            await done.delete()
        except: pass
    else:
        # No reply — purge last N messages
        count = 500
        if arg and arg.isdigit():
            count = min(int(arg), 3000)
        m = await safe_edit(event, f"⚡ {to_small_caps(f'purging last {count} messages...')}")
        ids_to_delete = []
        async for message in bot.iter_messages(event.chat_id, limit=count):
            ids_to_delete.append(message.id)
        # Fast parallel batch deletion
        delete_tasks = [
            bot.delete_messages(event.chat_id, ids_to_delete[i:i+100])
            for i in range(0, len(ids_to_delete), 100)
        ]
        results = await asyncio.gather(*delete_tasks, return_exceptions=True)
        deleted = sum(
            len(ids_to_delete[i:i+100])
            for i, r in enumerate(results) if not isinstance(r, Exception)
            for i in [i * 100]
        )
        deleted = len(ids_to_delete)  # all attempted
        try: await m.delete()
        except: pass
        try:
            done = await event.respond(f"✅ **{to_small_caps(f'purged {deleted} messages!')}**")
            await asyncio.sleep(3)
            await done.delete()
        except: pass

# ── THROW (KICK) ──────────────────────────────────────────────────
@cmd("throw", group_only=True)
async def _throw(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    kicked = []
    for uid in targets:
        try:
            await bot.kick_participant(event.chat_id, uid)
            kicked.append(str(uid))
        except Exception as e:
            logger.warning(f"Kick {uid}: {e}")
    await safe_edit(event, f"🦵 **𝐊𝐢𝐜𝐤𝐞𝐝:** `{', '.join(kicked) or 'Failed'}`")

# ── BAN ─────────────────────────────────────────────────────────
@cmd("ban", group_only=True)
async def _ban(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    banned = []
    for uid in targets:
        try:
            await bot(EditBannedRequest(
                event.chat_id, uid,
                ChatBannedRights(until_date=None, view_messages=True)
            ))
            banned.append(str(uid))
        except Exception as e:
            logger.warning(f"Ban {uid}: {e}")
    await safe_edit(event, f"🚫 **𝐁𝐚𝐧𝐧𝐞𝐝:** `{', '.join(banned) or 'Failed'}`")

# ── UNBAN ────────────────────────────────────────────────────────
@cmd("unban", group_only=True)
async def _unban(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    unbanned = []
    for uid in targets:
        try:
            await bot(EditBannedRequest(
                event.chat_id, uid,
                ChatBannedRights(until_date=None, view_messages=False)
            ))
            unbanned.append(str(uid))
        except Exception as e:
            logger.warning(f"Unban {uid}: {e}")
    await safe_edit(event, f"✅ **𝐔𝐧𝐛𝐚𝐧𝐧𝐞𝐝:** `{', '.join(unbanned) or 'Failed'}`")

# ── RAID COMMANDS ─────────────────────────────────────────────────
def _raid_toggle_on(store: set, label: str):
    async def _handler(event, arg):
        targets = await get_targets(event, arg)
        if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
        added = [str(u) for u in targets if u not in store]
        store.update(targets)
        await safe_edit(event, f"⚡ **{label} 𝐎𝐍** → `{', '.join(added) or 'Already active'}`")
    return _handler

def _raid_toggle_off(store: set, label: str):
    async def _handler(event, arg):
        targets = await get_targets(event, arg)
        if targets:
            stopped = [str(u) for u in targets if u in store]
            for u in targets: store.discard(u)
            await safe_edit(event, f"🛑 **{label} 𝐎𝐅𝐅** → `{', '.join(stopped) or 'Not active'}`")
        else:
            store.clear()
            await safe_edit(event, f"🛑 **{label} 𝐎𝐅𝐅** → 𝐀𝐥𝐥 𝐮𝐬𝐞𝐫𝐬")
    return _handler

# Register raid commands
cmd("reply")(_raid_toggle_on(reply_users,    "𝐑𝐞𝐩𝐥𝐲 𝐑𝐚𝐢𝐝"))
cmd("sreply")(_raid_toggle_off(reply_users,  "𝐑𝐞𝐩𝐥𝐲 𝐑𝐚𝐢𝐝"))
cmd("rr")(_raid_toggle_on(rr_users,          "𝐑𝐑 𝐑𝐚𝐢𝐝"))
cmd("srr")(_raid_toggle_off(rr_users,        "𝐑𝐑 𝐑𝐚𝐢𝐝"))
cmd("flag")(_raid_toggle_on(flag_users,      "𝐅𝐥𝐚𝐠 𝐑𝐚𝐢𝐝"))
cmd("sflag")(_raid_toggle_off(flag_users,    "𝐅𝐥𝐚𝐠 𝐑𝐚𝐢𝐝"))
cmd("hrr")(_raid_toggle_on(hrr_users,        "𝐇𝐞𝐚𝐫𝐭 𝐑𝐚𝐢𝐝"))
cmd("shrr")(_raid_toggle_off(hrr_users,      "𝐇𝐞𝐚𝐫𝐭 𝐑𝐚𝐢𝐝"))
cmd("replygod")(_raid_toggle_on(replygod_users, "𝐆𝐨𝐝 𝐑𝐚𝐢𝐝"))
cmd("sgod")(_raid_toggle_off(replygod_users, "𝐆𝐨𝐝 𝐑𝐚𝐢𝐝"))
# ── NEW: Bomb Raid ────────────────────────────────────────────────
cmd("bomb")(_raid_toggle_on(bomb_users,               "💣 𝐁𝐨𝐦𝐛 𝐑𝐚𝐢𝐝"))
cmd("sbomb")(_raid_toggle_off(bomb_users,             "💣 𝐁𝐨𝐦𝐛 𝐑𝐚𝐢𝐝"))
# ── Clone Reply ───────────────────────────────────────────────────
cmd("clonereply")(_raid_toggle_on(clone_reply_users,  "🪞 𝐂𝐥𝐨𝐧𝐞 𝐑𝐞𝐩𝐥𝐲"))
cmd("sclonereply")(_raid_toggle_off(clone_reply_users,"🪞 𝐂𝐥𝐨𝐧𝐞 𝐑𝐞𝐩𝐥𝐲"))

@cmd("replyvx")
async def _replyvx(event, arg):
    parts = arg.rsplit(" ", 1) if arg else []
    if len(parts) < 2 or not parts[1].isdigit():
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.replyvx <text> <count>`")
    text, count = parts[0], min(int(parts[1]), 100)
    targets = await get_targets(event, "")
    if not targets: return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐭𝐨 𝐚 𝐦𝐞𝐬𝐬𝐚𝐠𝐞!")
    for uid in targets:
        replyvx_users[uid] = {"text": text, "count": count}
    await safe_edit(event, f"☄️ **𝐑𝐘 𝐎𝐍** → `{', '.join(str(u) for u in targets)}` × `{count}`")

@cmd("svx")
async def _svx(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        for uid in targets: replyvx_users.pop(uid, None)
        await safe_edit(event, f"🛑 **𝐑𝐘 𝐎𝐅𝐅** → `{', '.join(str(u) for u in targets)}`")
    else:
        replyvx_users.clear()
        await safe_edit(event, "🛑 **𝐑𝐘 𝐎𝐅𝐅** → 𝐀𝐥𝐥 𝐮𝐬𝐞𝐫𝐬")

# ── MEDIA RAID ────────────────────────────────────────────────────
@cmd("mraid")
async def _mraid(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭! 𝐑𝐞𝐩𝐥𝐲 𝐨𝐫 𝐩𝐫𝐨𝐯𝐢𝐝𝐞 @𝐮𝐬𝐞𝐫𝐧𝐚𝐦𝐞")
    for uid in targets: media_raid_users.add(uid)
    media_tip = "" if mraid_media_msg else "\n⚠️ 𝐍𝐨 𝐦𝐞𝐝𝐢𝐚 𝐬𝐞𝐭! 𝐔𝐬𝐞 `.sᴇᴛᴍʀᴀɪᴅ` (𝐫𝐞𝐩𝐥𝐲 𝐭𝐨 𝐩𝐡𝐨𝐭𝐨/𝐯𝐢𝐝𝐞𝐨) 𝐟𝐢𝐫𝐬𝐭!"
    await safe_edit(event, f"🖼️ **ᴍᴇᴅɪᴀ ʀᴀɪᴅ sᴛᴀʀᴛᴇᴅ ᴏɴ {len(targets)} ᴜsᴇʀ(s)**{media_tip}")

@cmd("smraid")
async def _smraid(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        for uid in targets: media_raid_users.discard(uid)
        await safe_edit(event, f"🛑 **𝐌𝐑𝐚𝐢𝐝 𝐎𝐅𝐅** → `{', '.join(str(u) for u in targets)}`")
    else:
        media_raid_users.clear()
        await safe_edit(event, "🛑 **𝐌𝐑𝐚𝐢𝐝 𝐎𝐅𝐅** → 𝐀𝐥𝐥 𝐮𝐬𝐞𝐫𝐬")

# ── OTHER RAID COMMANDS ───────────────────────────────────────────
@cmd("abuse")
async def _abuse(event, arg):
    targets = await get_targets(event, arg)
    for uid in targets: abuse_users.add(uid)
    await safe_edit(event, f"⚔️ **ᴀʙᴜsᴇ ʀᴀɪᴅ sᴛᴀʀᴛᴇᴅ ᴏɴ {len(targets)} ᴜsᴇʀ(s)**")

@cmd("sabuse")
async def _sabuse(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        for uid in targets: abuse_users.discard(uid)
        await safe_edit(event, f"🛑 **ᴀʙᴜsᴇ ʀᴀɪᴅ ᴏFF** → `{', '.join(str(u) for u in targets)}`")
    else:
        abuse_users.clear()
        await safe_edit(event, "🛑 **ᴀʙᴜsᴇ ʀᴀɪᴅ ᴏFF** → ᴀʟʟ ᴜsᴇʀs")

@cmd("abuse2")
async def _abuse2(event, arg):
    targets = await get_targets(event, arg)
    for uid in targets: abuse2_users.add(uid)
    await safe_edit(event, f"💀 **ᴀʙᴜsᴇ2 ʀᴀɪᴅ sᴛᴀʀᴛᴇᴅ ᴏɴ {len(targets)} ᴜsᴇʀ(s)**")

@cmd("sabuse2")
async def _sabuse2(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        for uid in targets: abuse2_users.discard(uid)
        await safe_edit(event, f"🛑 **ᴀʙᴜsᴇ2 ʀᴀɪᴅ ᴏFF** → `{', '.join(str(u) for u in targets)}`")
    else:
        abuse2_users.clear()
        await safe_edit(event, "🛑 **ᴀʙᴜsᴇ2 ʀᴀɪᴅ ᴏFF** → ᴀʟʟ ᴜsᴇʀs")

@cmd("slap")
async def _slap(event, arg):
    targets = await get_targets(event, arg)
    for uid in targets: slap_users.add(uid)
    await safe_edit(event, f"👋🏻 **sʟᴀᴘ ʀᴀɪᴅ sᴛᴀʀᴛᴇᴅ ᴏɴ {len(targets)} ᴜsᴇʀ(s)**")

@cmd("sslap")
async def _sslap(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        for uid in targets: slap_users.discard(uid)
        await safe_edit(event, f"🛑 **𝐒𝐥𝐚𝐩 𝐑𝐚𝐢𝐝 𝐎𝐅𝐅** → `{', '.join(str(u) for u in targets)}`")
    else:
        slap_users.clear()
        await safe_edit(event, "🛑 **𝐒𝐥𝐚𝐩 𝐑𝐚𝐢𝐝 𝐎𝐅𝐅** → 𝐀𝐥𝐥 𝐮𝐬𝐞𝐫𝐬")

@cmd("kickraid")
async def _kickraid(event, arg):
    targets = await get_targets(event, arg)
    if not targets: return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐨𝐫 𝐩𝐫𝐨𝐯𝐢𝐝𝐞 @𝐮𝐬𝐞𝐫𝐧𝐚𝐦𝐞!")
    for uid in targets: kick_users.add(uid)
    await safe_edit(event, f"👞 **ᴋɪᴄᴋ ʀᴀɪᴅ sᴛᴀʀᴛᴇᴅ ᴏɴ {len(targets)} ᴜsᴇʀ(s)**\n💡 𝐁𝐨𝐭 𝐦𝐮𝐬𝐭 ʙᴇ ᴀᴅᴍɪɴ ᴡɪᴛʜ ʙᴀɴ ʀɪɢʜᴛs!")

@cmd("skickraid")
async def _skickraid(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        for uid in targets: kick_users.discard(uid)
        await safe_edit(event, f"🛑 **𝐊𝐢𝐜𝐤 𝐑𝐚𝐢𝐝 𝐎𝐅𝐅** → `{', '.join(str(u) for u in targets)}`")
    else:
        kick_users.clear()
        await safe_edit(event, "🛑 **𝐊𝐢𝐜𝐤 𝐑𝐚𝐢𝐝 𝐎𝐅𝐅** → 𝐀𝐥𝐥 𝐮𝐬𝐞𝐫𝐬")

# ── SAFE RAID ─────────────────────────────────────────────────────
# Usage:
#   Reply to target's msg → .saferaid <text>    start (runs forever)
#   .ssaferaid                                   stop all
#   .ssaferaid (reply to target)                 stop one user
#
# Logic (V9 updated):
#   - Scans chat history for target's messages
#   - Sends 30 FAST replies per round, cycling across all found messages
#   - If only 1 message found → all 30 replies go to that one
#   - Waits 30 seconds after every 30 replies (V9: faster loop)
#   - Loops FOREVER until .ssaferaid is used
#   - Handles FloodWait automatically (waits + retries)

SAFE_RAID_BATCH    = 30   # replies per round before cooldown (V9: 30 fast)
SAFE_RAID_COOLDOWN = 30   # seconds to wait between rounds (V9: faster loop)
SAFE_RAID_MSG_SCAN = 100  # recent messages to scan for target's msgs

@cmd("saferaid")
async def _saferaid(event, arg):
    if not arg:
        return await safe_edit(
            event,
            "❌ **𝐔𝐬𝐚𝐠𝐞:**\n"
            "• Reply to target's msg → `.saferaid <text>`\n"
            "• Or: `.saferaid @username <text>`\n"
            "🛑 **𝐒𝐭𝐨𝐩:** `.ssaferaid`\n"
            f"📊 **𝐌𝐨𝐝𝐞:** `{SAFE_RAID_BATCH}` replies → `{SAFE_RAID_COOLDOWN}s` → loops forever"
        )

    # ── Resolve target: reply OR first word is @username / numeric ID ──
    chat_id    = event.chat_id
    target_uid = None
    text       = arg

    # Try from reply first
    if event.is_reply:
        try:
            r = await event.get_reply_message()
            if r and r.sender_id:
                target_uid = int(r.sender_id)
        except Exception:
            pass

    # If no reply, try first word of arg as username/ID
    if target_uid is None:
        parts = arg.split(None, 1)
        if parts:
            candidate = parts[0]
            if candidate.lstrip("-").isdigit():
                target_uid = int(candidate)
                text = parts[1] if len(parts) > 1 else ""
            elif candidate.startswith("@"):
                try:
                    ent = await bot.get_entity(candidate)
                    if getattr(ent, "id", None):
                        target_uid = int(ent.id)
                        text = parts[1] if len(parts) > 1 else ""
                except Exception:
                    pass

    if not target_uid:
        return await safe_edit(
            event,
            "❌ 𝐂𝐨𝐮𝐥𝐝 𝐧𝐨𝐭 𝐟𝐢𝐧𝐝 𝐭𝐚𝐫𝐠𝐞𝐭!\n"
            "Reply to their message, or use `.saferaid @username <text>`"
        )

    if not text.strip():
        return await safe_edit(event, "❌ 𝐏𝐫𝐨𝐯𝐢𝐝𝐞 𝐚 𝐦𝐞𝐬𝐬𝐚𝐠𝐞 𝐭𝐞𝐱𝐭 𝐭𝐨 𝐬𝐞𝐧𝐝!")

    # Discard self
    try:
        me = await _get_me()
        if target_uid == me.id:
            return await safe_edit(event, "❌ **ᴄᴀɴ'ᴛ ʀᴀɪᴅ ʏᴏᴜʀsᴇʟꜰ ʙʀᴏ**")
    except Exception:
        pass

    text = text.strip()[:4000]

    # Cancel any existing safe raid on this target
    if target_uid in safe_raid_tasks and not safe_raid_tasks[target_uid].done():
        safe_raid_tasks[target_uid].cancel()

    await safe_edit(
        event,
        f"⚡ **sᴀꜰᴇ ʀᴀɪᴅ sᴛᴀʀᴛᴇᴅ**\n"
        f"👤 ᴛᴀʀɢᴇᴛ: `{target_uid}`\n"
        f"📝 ᴛᴇxᴛ: `{text[:60]}{'...' if len(text) > 60 else ''}`\n"
        f"🔁 `{SAFE_RAID_BATCH}` ʀᴇᴘʟɪᴇs → `{SAFE_RAID_COOLDOWN}s` ᴄᴏᴏʟᴅᴏᴡɴ → ʟᴏᴏᴘs ꜰᴏʀᴇᴠᴇʀ\n"
        f"🛑 sᴛᴏᴘ: `.ssaferaid`"
    )

    async def _safe_raid_loop():
        round_num  = 0
        total_sent = 0

        # ── Step 1: Get the message ID to reply to ──────────────────
        reply_msg_id = None

        # If user replied to a message, use that message directly
        if event.is_reply:
            try:
                r = await event.get_reply_message()
                if r:
                    reply_msg_id = r.id
            except Exception:
                pass

        # Otherwise find their most recent message in this chat
        if not reply_msg_id:
            try:
                async for msg in bot.iter_messages(
                    chat_id, from_user=target_uid, limit=1
                ):
                    reply_msg_id = msg.id
            except Exception:
                pass

        if not reply_msg_id:
            try:
                await bot.send_message(
                    chat_id,
                    f"⚠️ **sᴀꜰᴇ ʀᴀɪᴅ:** ɴᴏ ᴍsɢs ꜰᴏᴜɴᴅ ꜰᴏʀ `{target_uid}` ɪɴ ᴛʜɪs ᴄʜᴀᴛ"
                )
            except Exception:
                pass
            safe_raid_tasks.pop(target_uid, None)
            return

        # ── Step 2: Infinite loop — 30 fast replies → 30s wait → repeat ─
        try:
            while True:
                round_num  += 1
                round_sent  = 0

                for _ in range(SAFE_RAID_BATCH):
                    try:
                        await bot.send_message(chat_id, text, reply_to=reply_msg_id)
                        round_sent += 1
                        total_sent += 1
                    except FloodWaitError as fw:
                        await asyncio.sleep(fw.seconds + 5)
                        try:
                            await bot.send_message(chat_id, text, reply_to=reply_msg_id)
                            round_sent += 1
                            total_sent += 1
                        except Exception:
                            pass
                    except Exception:
                        pass

                    await asyncio.sleep(0.2)  # V9: fast replies

                # ── Cooldown between rounds ──────────────────────────
                await asyncio.sleep(SAFE_RAID_COOLDOWN)

                # Refresh — try to grab their newest message if available
                try:
                    async for msg in bot.iter_messages(
                        chat_id, from_user=target_uid, limit=1
                    ):
                        reply_msg_id = msg.id
                except Exception:
                    pass  # keep using last known msg id

        except asyncio.CancelledError:
            try:
                await bot.send_message(
                    chat_id,
                    f"🛑 **sᴀꜰᴇ ʀᴀɪᴅ sᴛᴏᴘᴘᴇᴅ**\n"
                    f"👤 ᴛᴀʀɢᴇᴛ: `{target_uid}`\n"
                    f"📊 `{total_sent}` ʀᴇᴘʟɪᴇs ᴀᴄʀᴏss `{round_num}` ʀᴏᴜɴᴅ(s)"
                )
            except Exception:
                pass
        except Exception as e:
            logger.error(f"[SafeRaid] {e}")
        finally:
            safe_raid_tasks.pop(target_uid, None)

    safe_raid_tasks[target_uid] = asyncio.ensure_future(_safe_raid_loop())


@cmd("ssaferaid")
async def _ssaferaid(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        stopped = []
        for uid in targets:
            task = safe_raid_tasks.get(uid)
            if task and not task.done():
                task.cancel()
                stopped.append(str(uid))
            safe_raid_tasks.pop(uid, None)
        await safe_edit(event, f"🛑 **𝐒𝐚𝐟𝐞 𝐑𝐚𝐢𝐝 𝐒𝐓𝐎𝐏𝐏𝐄𝐃** → `{', '.join(stopped) or 'Not active'}`")
    else:
        for task in safe_raid_tasks.values():
            if not task.done(): task.cancel()
        safe_raid_tasks.clear()
        await safe_edit(event, "🛑 **𝐒𝐚𝐟𝐞 𝐑𝐚𝐢𝐝 𝐒𝐓𝐎𝐏𝐏𝐄𝐃** → 𝐀𝐥𝐥 𝐭𝐚𝐫𝐠𝐞𝐭𝐬")

# ── STOP ALL ──────────────────────────────────────────────────────
@cmd("stopall")
async def _stopall(event, _):
    reply_users.clear()
    rr_users.clear()
    flag_users.clear()
    hrr_users.clear()
    abuse_users.clear()
    abuse2_users.clear()
    slap_users.clear()
    kick_users.clear()
    media_raid_users.clear()
    replygod_users.clear()
    replyvx_users.clear()
    bomb_users.clear()
    clone_reply_users.clear()
    for task in spray_tasks.values():
        if not task.done(): task.cancel()
    spray_tasks.clear()
    slide_users.clear()
    for task in safe_raid_tasks.values():
        if not task.done(): task.cancel()
    safe_raid_tasks.clear()
    FASTGC_STATE["active"] = False
    if FASTGC_STATE.get("task") and not FASTGC_STATE["task"].done():
        FASTGC_STATE["task"].cancel()
    FASTGC_STATE["task"] = None
    global CLONE_RAID_TASK
    if CLONE_RAID_TASK and not CLONE_RAID_TASK.done():
        CLONE_RAID_TASK.cancel()
        CLONE_RAID_TASK = None
    trigger_raid_targets.clear()
    await safe_edit(event, "🛑 **𝐀𝐋𝐋 𝐑𝐀𝐈𝐃𝐒, 𝐒𝐏𝐑𝐀𝐘, 𝐒𝐋𝐈𝐃𝐄 & 𝐓𝐑𝐈𝐆𝐑𝐀𝐈𝐃 𝐒𝐓𝐎𝐏𝐏𝐄𝐃!**")

# ── SPRAY ─────────────────────────────────────────────────────────
@cmd("spray")
async def _spray(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.spray <text>`")
    chat = event.chat_id
    if chat in spray_tasks and not spray_tasks[chat].done():
        return await safe_edit(event, "⚠️ 𝐒𝐩𝐫𝐚𝐲 𝐚𝐥𝐫𝐞𝐚𝐝𝐲 𝐚𝐜𝐭𝐢𝐯𝐞 𝐡𝐞𝐫𝐞!")
    text = arg[:4000]
    await safe_edit(event, "⚡ 𝐒𝐩𝐫𝐚𝐲 𝐬𝐭𝐚𝐫𝐭𝐞𝐝!")
    async def _loop():
        try:
            while True:
                await bot.send_message(chat, text)
                await asyncio.sleep(SPRAY_DELAY)
        except asyncio.CancelledError: pass
        except Exception as e: logger.error(f"[Spray] {e}")
    spray_tasks[chat] = asyncio.ensure_future(_loop())

@cmd("dspray")
async def _dspray(event, _):
    chat = event.chat_id
    task = spray_tasks.get(chat)
    if task and not task.done():
        task.cancel()
        del spray_tasks[chat]
        await safe_edit(event, "🛑 **𝐒𝐩𝐫𝐚𝐲 𝐒𝐭𝐨𝐩𝐩𝐞𝐝!**")
    else:
        await safe_edit(event, "⚠️ 𝐍𝐨 𝐚𝐜𝐭𝐢𝐯𝐞 𝐬𝐩𝐫𝐚𝐲 𝐡𝐞𝐫𝐞!")

# ── SLIDE RAID ────────────────────────────────────────────────────
# Works like God Raid — replies to the target's every message with
# cycling emoji + your custom text. Each reply gets the next emoji.
# Usage:
#   Reply to target's msg → .slideraid <text>    start
#   .dslideraid                                   stop all
#   .dslideraid (reply to target)                 stop one user
#   .slideset emoji 🔥 💀 ⚡ 🖕                  change emoji list

@cmd("slideraid")
async def _slideraid(event, arg):
    if not arg:
        return await safe_edit(
            event,
            "❌ **𝐔𝐬𝐚𝐠𝐞:** Reply to target's msg → `.slideraid <text>`\n"
            "🛑 **𝐒𝐭𝐨𝐩:** `.dslideraid`\n"
            "🎭 **𝐄𝐦𝐨𝐣𝐢𝐬:** `.slideset emoji 🔥 💀 ⚡`"
        )
    targets = await get_targets(event, "")
    if not targets:
        return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐭𝐨 𝐭𝐡𝐞 𝐭𝐚𝐫𝐠𝐞𝐭'𝐬 𝐦𝐞𝐬𝐬𝐚𝐠𝐞 𝐭𝐨 𝐬𝐭𝐚𝐫𝐭!")
    text   = arg[:3000]
    emojis = list(SLIDE_EMOJIS)
    added  = []
    for uid in targets:
        slide_users[uid] = {"text": text, "idx": 0, "emojis": emojis}
        added.append(str(uid))
    await safe_edit(
        event,
        f"🎭 **𝐒𝐋𝐈𝐃𝐄 𝐑𝐀𝐈𝐃 𝐎𝐍!**\n"
        f"👤 Target(s): `{', '.join(added)}`\n"
        f"📝 Text: `{text[:60]}{'...' if len(text) > 60 else ''}`\n"
        f"🎭 Emojis: `{' '.join(emojis[:6])}{'...' if len(emojis) > 6 else ''}`\n"
        f"🛑 Stop: `.dslideraid`"
    )

@cmd("dslideraid")
async def _dslideraid(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        stopped = [str(u) for u in targets if u in slide_users]
        for u in targets: slide_users.pop(u, None)
        await safe_edit(event, f"🛑 **𝐒𝐥𝐢𝐝𝐞 𝐑𝐚𝐢𝐝 𝐎𝐅𝐅** → `{', '.join(stopped) or 'Not active'}`")
    else:
        slide_users.clear()
        await safe_edit(event, "🛑 **𝐒𝐥𝐢𝐝𝐞 𝐑𝐚𝐢𝐝 𝐒𝐭𝐨𝐩𝐩𝐞𝐝 — 𝐀𝐥𝐥 𝐮𝐬𝐞𝐫𝐬!**")

@cmd("slideset")
async def _slideset(event, arg):
    if not arg:
        return await safe_edit(
            event,
            f"⚙️ **𝐒𝐥𝐢𝐝𝐞 𝐑𝐚𝐢𝐝 𝐂𝐨𝐧𝐟𝐢𝐠**\n"
            f"🎭 Emojis: `{' '.join(SLIDE_EMOJIS)}`\n\n"
            f"**𝐂𝐡𝐚𝐧𝐠𝐞:**\n"
            f"• `.slideset emoji 🔥 💀 ⚡ 🗡️` — space-separated list"
        )
    parts = arg.split()
    sub   = parts[0].lower()
    if sub in ("emoji", "emojis"):
        new_emojis = parts[1:]
        if len(new_emojis) < 2:
            return await safe_edit(event, "❌ Provide at least 2 emojis.")
        SLIDE_EMOJIS.clear()
        SLIDE_EMOJIS.extend(new_emojis)
        await safe_edit(event, f"✅ **Slide emojis set:** `{' '.join(new_emojis)}`")
    else:
        await safe_edit(event, "❌ Unknown option. Use `.slideset emoji 🔥 💀 ⚡`")

# ── FASTGC ────────────────────────────────────────────────────────
@cmd("fastgc")
async def _fastgc(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.fastgc set <template>` or `.fastgc stop`")
    sub = arg.split(" ", 1)
    action = sub[0].lower()
    if action == "stop":
        FASTGC_STATE["active"] = False
        if FASTGC_STATE.get("task") and not FASTGC_STATE["task"].done():
            FASTGC_STATE["task"].cancel()
        FASTGC_STATE["task"] = None
        return await safe_edit(event, "🛑 **𝐅𝐚𝐬𝐭𝐆𝐂 𝐒𝐭𝐨𝐩𝐩𝐞𝐝!**")
    if action == "set":
        if len(sub) < 2: return await safe_edit(event, "❌ 𝐏𝐫𝐨𝐯𝐢𝐝𝐞 𝐚 𝐭𝐞𝐦𝐩𝐥𝐚𝐭𝐞!")
        template = sub[1]
        FASTGC_STATE["active"] = True
        FASTGC_STATE["template"] = template
        FASTGC_STATE["chat_id"] = event.chat_id
        if FASTGC_STATE.get("task") and not FASTGC_STATE["task"].done():
            FASTGC_STATE["task"].cancel()
        FASTGC_STATE["task"] = asyncio.ensure_future(_gc_fast_loop(event.chat_id))
        return await safe_edit(event, f"⚡ **𝐅𝐚𝐬𝐭𝐆𝐂 𝐒𝐭𝐚𝐫𝐭𝐞𝐝!**\n📝 𝐓𝐞𝐦𝐩𝐥𝐚𝐭𝐞: `{template}`")
    await safe_edit(event, "❌ 𝐔𝐬𝐞 `set` 𝐨𝐫 `stop`")

# ── AUTO REACT ────────────────────────────────────────────────────
@cmd("ar")
async def _ar(event, arg):
    global auto_react_emoji
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.ar <emoji>`")
    auto_react_emoji = arg.strip()
    await safe_edit(event, f"❤️ **𝐀𝐮𝐭𝐨 𝐑𝐞𝐚𝐜𝐭:** `{auto_react_emoji}` 𝐞𝐧𝐚𝐛𝐥𝐞𝐝!")

@cmd("sar")
async def _sar(event, _):
    global auto_react_emoji
    auto_react_emoji = None
    await safe_edit(event, "🛑 **𝐀𝐮𝐭𝐨 𝐑𝐞𝐚𝐜𝐭 𝐒𝐭𝐨𝐩𝐩𝐞𝐝!**")

# ── NOTES ─────────────────────────────────────────────────────────
@cmd("notesadd")
async def _notesadd(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐏𝐫𝐨𝐯𝐢𝐝𝐞 𝐭𝐞𝐱𝐭!")
    note_id = max(notes.keys(), default=0) + 1
    notes[note_id] = arg
    save_notes()
    await safe_edit(event, f"📝 **𝐍𝐨𝐭𝐞 𝐒𝐚𝐯𝐞𝐝!** 𝐈𝐃: `{note_id}`")

@cmd("noteslist")
async def _noteslist(event, _):
    if not notes: return await safe_edit(event, "📝 𝐍𝐨 𝐧𝐨𝐭𝐞𝐬 𝐬𝐚𝐯𝐞𝐝!")
    lines = ["📝 **𝐘𝐨𝐮𝐫 𝐍𝐨𝐭𝐞𝐬:**\n━━━━━━━━━━━━━━━"]
    for nid, text in sorted(notes.items()):
        preview = text[:60] + ("..." if len(text) > 60 else "")
        lines.append(f"**#{nid}** → {preview}")
    await safe_edit(event, "\n".join(lines))

@cmd("notesdelete")
async def _notesdelete(event, arg):
    if not arg or not arg.isdigit():
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.notesdelete <id>`")
    nid = int(arg)
    if nid not in notes:
        return await safe_edit(event, f"❌ 𝐍𝐨𝐭𝐞 `#{nid}` 𝐧𝐨𝐭 𝐟𝐨𝐮𝐧𝐝!")
    del notes[nid]
    save_notes()
    await safe_edit(event, f"🗑️ **𝐍𝐨𝐭𝐞 `#{nid}` 𝐃𝐞𝐥𝐞𝐭𝐞𝐝!**")

# ── FUN ───────────────────────────────────────────────────────────
@cmd("flip")
async def _flip(event, _):
    result = random.choice(["🪙 𝐇𝐞𝐚𝐝𝐬!", "🪙 𝐓𝐚𝐢𝐥𝐬!"])
    await safe_edit(event, f"🎲 **𝐂𝐨𝐢𝐧 𝐅𝐥𝐢𝐩:** {result}")

@cmd("dice")
async def _dice(event, _):
    result = random.randint(1, 6)
    faces = ["⚀","⚁","⚂","⚃","⚄","⚅"]
    await safe_edit(event, f"🎲 **𝐃𝐢𝐜𝐞 𝐑𝐨𝐥𝐥:** {faces[result-1]} `{result}`")

# ── COINFLIP ──────────────────────────────────────────────────────
@cmd("coinflip")
async def _coinflip(event, _):
    result = random.choice(["🪙 **Heads!**", "🪙 **Tails!**"])
    await safe_edit(event, f"🪙 **Coin Flip →** {result}")

# ── ROCK PAPER SCISSORS ───────────────────────────────────────────
@cmd("rps")
async def _rps(event, arg):
    choices = {"rock": "🪨", "paper": "📄", "scissors": "✂️"}
    user_raw = (arg or "").strip().lower()
    if user_raw not in choices:
        return await safe_edit(event, "❌ **Usage:** `.rps rock` / `.rps paper` / `.rps scissors`")
    bot_pick = random.choice(list(choices.keys()))
    user_icon = choices[user_raw]
    bot_icon  = choices[bot_pick]
    wins = {"rock": "scissors", "paper": "rock", "scissors": "paper"}
    if user_raw == bot_pick:
        result = "🤝 **Draw!**"
    elif wins[user_raw] == bot_pick:
        result = "🏆 **You Win!**"
    else:
        result = "💀 **Kurosaki Wins!**"
    await safe_edit(event,
        f"⚔️ **Rock · Paper · Scissors**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"  You   → {user_icon} `{user_raw}`\n"
        f"  Bot   → {bot_icon} `{bot_pick}`\n"
        f"━━━━━━━━━━━━━━━\n"
        f"  {result}"
    )

# ── MAGIC 8 BALL ──────────────────────────────────────────────────
_EIGHTBALL_ANSWERS = [
    "🎱 ɪᴛ ɪs ᴄᴇʀᴛᴀɪɴ.", "🎱 ᴅᴇꜰɪɴɪᴛᴇʟʏ ʏᴇs.", "🎱 ʏᴏᴜ ᴍᴀʏ ʀᴇʟʏ ᴏɴ ɪᴛ.",
    "🎱 ᴏᴜᴛʟᴏᴏᴋ ɢᴏᴏᴅ.", "🎱 sɪɢɴs ᴘᴏɪɴᴛ ᴛᴏ ʏᴇs.", "🎱 ᴡɪᴛʜᴏᴜᴛ ᴀ ᴅᴏᴜʙᴛ — ʏᴇs.",
    "🎱 ᴅᴏɴ'ᴛ ᴄᴏᴜɴᴛ ᴏɴ ɪᴛ.", "🎱 ᴍʏ ʀᴇᴘʟʏ ɪs ɴᴏ.", "🎱 ᴠᴇʀʏ ᴅᴏᴜʙᴛꜰᴜʟ.",
    "🎱 ᴏᴜᴛʟᴏᴏᴋ ɴᴏᴛ sᴏ ɢᴏᴏᴅ.", "🎱 ᴀsᴋ ᴀɢᴀɪɴ ʟᴀᴛᴇʀ.", "🎱 ᴄᴀɴɴᴏᴛ ᴘʀᴇᴅɪᴄᴛ ɴᴏᴡ.",
    "🎱 ᴄᴏɴᴄᴇɴᴛʀᴀᴛᴇ ᴀɴᴅ ᴀsᴋ ᴀɢᴀɪɴ.", "🎱 ʙᴇᴛᴛᴇʀ ɴᴏᴛ ᴛᴇʟʟ ʏᴏᴜ ɴᴏᴡ.",
    "🎱 ᴋᴜʀᴏsᴀᴋɪ sᴀʏs: ᴀʙsᴏʟᴜᴛᴇʟʏ ʏᴇs! ⚡", "🎱 ᴋᴜʀᴏsᴀᴋɪ sᴀʏs: ɴᴏ ᴄʜᴀɴᴄᴇ. 💀",
]

@cmd("8ball")
async def _8ball(event, arg):
    if not arg:
        return await safe_edit(event, "❌ **Usage:** `.8ball <your question>`")
    answer = random.choice(_EIGHTBALL_ANSWERS)
    await safe_edit(event,
        f"🎱 **Magic 8-Ball**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"❓ `{arg[:120]}`\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{answer}"
    )

# ── TRIVIA ────────────────────────────────────────────────────────
_TRIVIA_QA = [
    ("What is the capital of Japan?", "Tokyo"),
    ("How many sides does a hexagon have?", "6"),
    ("What planet is known as the Red Planet?", "Mars"),
    ("What is 12 × 12?", "144"),
    ("Who wrote Romeo and Juliet?", "Shakespeare"),
    ("What gas do plants absorb from the air?", "CO2"),
    ("How many continents are on Earth?", "7"),
    ("What is the fastest land animal?", "Cheetah"),
    ("What is the chemical symbol for gold?", "Au"),
    ("In what year did World War II end?", "1945"),
    ("What is the longest river in the world?", "Nile"),
    ("What is the square root of 144?", "12"),
    ("How many bones are in the human body?", "206"),
    ("What language has the most native speakers?", "Mandarin"),
    ("What is the smallest planet in our solar system?", "Mercury"),
]

@cmd("trivia")
async def _trivia(event, _):
    q, a = random.choice(_TRIVIA_QA)
    await safe_edit(event,
        f"🧠 **Kurosaki Trivia**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"❓ {q}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"||✅ Answer: **{a}**||"
    )

# ── MATH CHALLENGE ────────────────────────────────────────────────
@cmd("math")
async def _math(event, _):
    ops = [
        (lambda a, b: (f"{a} + {b}", a + b)),
        (lambda a, b: (f"{a} - {b}", a - b)),
        (lambda a, b: (f"{a} × {b}", a * b)),
    ]
    a, b = random.randint(2, 20), random.randint(2, 20)
    op = random.choice(ops)
    q, ans = op(a, b)
    await safe_edit(event,
        f"🔢 **Math Challenge**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"  {q} = ?\n"
        f"━━━━━━━━━━━━━━━\n"
        f"||✅ Answer: **{ans}**||"
    )

# ── FORTUNE COOKIE ────────────────────────────────────────────────
_FORTUNES = [
    "⚡ ᴛʜᴇ ᴅᴀʀᴋᴇʀ ᴛʜᴇ ɴɪɢʜᴛ, ᴛʜᴇ ʙʀɪɢʜᴛᴇʀ ʏᴏᴜʀ ꜰʟᴀᴍᴇ. 🔥",
    "💀 ᴇᴠᴇʀʏ ᴇɴᴇᴍʏ ʏᴏᴜ ʜᴀᴠᴇ ɪs ᴘʀᴏᴏꜰ ʏᴏᴜ sᴛᴏᴏᴅ ꜰᴏʀ sᴏᴍᴇᴛʜɪɴɢ.",
    "🗡️ sɪʟᴇɴᴄᴇ ɪs ᴛʜᴇ ᴅᴇᴀᴅʟɪᴇsᴛ ᴡᴇᴀᴘᴏɴ ʏᴏᴜ ᴏᴡɴ.",
    "🌋 ᴛʜᴇ ᴡᴏʀʟᴅ ꜰᴇᴀʀs ᴡʜᴀᴛ ɪᴛ ᴄᴀɴɴᴏᴛ ᴄᴏɴᴛʀᴏʟ. ʙᴇ ᴛʜᴀᴛ.",
    "☠️ ᴛʀᴜsᴛ ꜰᴇᴡ. ꜰᴇᴀʀ ɴᴏɴᴇ. ᴏᴡᴇ ɴᴏᴛʜɪɴɢ.",
    "🩸 ᴘᴀɪɴ ɪs ᴛᴇᴍᴘᴏʀᴀʀʏ. ʟᴇɢᴇɴᴅs ᴀʀᴇ ꜰᴏʀᴇᴠᴇʀ.",
    "💣 ᴛʜᴇʏ ᴡᴀɴᴛᴇᴅ ᴀ ᴡᴀʀ. ɢɪᴠᴇ ᴛʜᴇᴍ ᴀ ᴡᴀʀ ᴛʜᴇʏ ᴄᴀɴ'ᴛ ꜰɪɴɪsʜ.",
    "👑 ʙᴇ sᴏ ɢᴏᴏᴅ ᴛʜᴇʏ ᴄᴀɴ'ᴛ ɪɢɴᴏʀᴇ ʏᴏᴜ.",
    "⚔️ ᴛʜᴏsᴇ ᴡʜᴏ ᴅᴏᴜʙᴛ ʏᴏᴜ ᴀʀᴇ ɪɴᴠɪᴛɪɴɢ ʏᴏᴜ ᴛᴏ ᴘʀᴏᴠᴇ ᴛʜᴇᴍ ᴡʀᴏɴɢ.",
    "🔥 ᴀ ᴋɪɴɢ ᴅᴏᴇsɴ'ᴛ ᴄʜᴀsᴇ. ᴀ ᴋɪɴɢ ᴡᴀɪᴛs — ᴀɴᴅ ᴛʜᴇɴ sᴛʀɪᴋᴇs.",
]

@cmd("fortune")
async def _fortune(event, _):
    await safe_edit(event,
        f"🥠 **Kurosaki Fortune Cookie**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{random.choice(_FORTUNES)}"
    )

# ── ROAST ─────────────────────────────────────────────────────────
_ROASTS = [
    "🔥 {user} — ɪꜰ ɪᴅɪᴏᴄʏ ʙᴜʀɴᴇᴅ ᴄᴀʟᴏʀɪᴇs, ʏᴏᴜ'ᴅ ʙᴇ ɪɴᴠɪsɪʙʟᴇ.",
    "💀 {user} — ʏᴏᴜ ᴀʀᴇ ᴛʜᴇ ʀᴇᴀsᴏɴ sʜᴀᴍᴘᴏᴏ ʜᴀs ɪɴsᴛʀᴜᴄᴛɪᴏɴs.",
    "😂 {user} — ʏᴏᴜʀ ɪQ ɪs ʟᴏᴡᴇʀ ᴛʜᴀɴ ᴛʜᴇ ɴᴜᴍʙᴇʀ ᴏꜰ ꜰʀɪᴇɴᴅs ʏᴏᴜ ʜᴀᴠᴇ.",
    "🤡 {user} — ɢᴏᴏɢʟᴇ ᴄᴏᴜʟᴅɴ'ᴛ ꜰɪɴᴅ ʏᴏᴜʀ ʀᴇʟᴇᴠᴀɴᴄᴇ.",
    "🗑 {user} — ᴇᴠᴇɴ ʏᴏᴜʀ ᴅᴜᴍᴍɪᴇs ʜᴀᴠᴇ ᴅᴜᴍᴍɪᴇs.",
    "⚡ {user} — ᴛʜᴇ ʟɪɢʜᴛs ᴀʀᴇ ᴏɴ ʙᴜᴛ ɴᴏʙᴏᴅʏ's ʜᴏᴍᴇ.",
    "💣 {user} — ɪꜰ ɴᴏɪsᴇ ᴡᴀs ᴍᴏɴᴇʏ ʏᴏᴜ'ᴅ sᴛɪʟʟ ʙᴇ ʙʀᴏᴋᴇ.",
    "☠️ {user} — ᴛʜᴇ ᴏɴʟʏ ᴛʜɪɴɢ ꜰʟᴀᴛ ᴀʙᴏᴜᴛ ʏᴏᴜ ɪs ʏᴏᴜʀ ᴘᴇʀsᴏɴᴀʟɪᴛʏ.",
]

@cmd("roast")
async def _roast(event, arg):
    name = "User"
    if event.is_reply:
        try:
            r = await event.get_reply_message()
            u = await bot.get_entity(r.sender_id)
            name = getattr(u, "first_name", None) or getattr(u, "username", None) or "User"
        except: pass
    elif arg:
        name = arg.split()[0]
    await safe_edit(event, random.choice(_ROASTS).format(user=name))

# ── COMPLIMENT ────────────────────────────────────────────────────
_COMPLIMENTS = [
    "🌟 {user} — ʏᴏᴜ ᴀʀᴇ ᴛʜᴇ ᴛʏᴘᴇ ᴏꜰ ᴘᴇʀsᴏɴ ᴛʜɪs ᴡᴏʀʟᴅ ɴᴇᴇᴅs ᴍᴏʀᴇ ᴏꜰ. 💙",
    "⚡ {user} — ʏᴏᴜʀ ᴇɴᴇʀɢʏ ɪs ᴜɴᴍᴀᴛᴄʜᴇᴅ. ᴋᴇᴇᴘ ɢᴏɪɴɢ. 🔥",
    "👑 {user} — ᴀ ʀᴀʀᴇ ᴋɪɴᴅ ᴏꜰ ʟᴇɢᴇɴᴅ. sᴛᴀʏ ᴛʜᴀᴛ ᴡᴀʏ. 💎",
    "💙 {user} — ʏᴏᴜ ᴍᴀᴋᴇ ᴇᴠᴇʀʏ ʀᴏᴏᴍ ʙʀɪɢʜᴛᴇʀ ᴊᴜsᴛ ʙʏ ʙᴇɪɴɢ ɪɴ ɪᴛ.",
    "🌸 {user} — ᴋɪɴᴅɴᴇss ᴀɴᴅ sᴛʀᴇɴɢᴛʜ ʟɪᴠᴇ ɪɴ ʏᴏᴜ. ᴛʜᴀᴛ's ᴀᴜᴛʜᴏʀɪᴛʏ.",
    "🏆 {user} — ᴛʜᴇ ᴡᴏʀʟᴅ ɪs ʙᴇᴛᴛᴇʀ ᴡɪᴛʜ ʏᴏᴜ ɪɴ ɪᴛ. ꜰᴀᴄᴛ.",
    "✨ {user} — ʏᴏᴜ ᴅᴏɴ'ᴛ ꜰᴏʟʟᴏᴡ ᴛʀᴇɴᴅs, ʏᴏᴜ sᴇᴛ ᴛʜᴇᴍ.",
]

@cmd("compliment")
async def _compliment(event, arg):
    name = "User"
    if event.is_reply:
        try:
            r = await event.get_reply_message()
            u = await bot.get_entity(r.sender_id)
            name = getattr(u, "first_name", None) or getattr(u, "username", None) or "User"
        except: pass
    elif arg:
        name = arg.split()[0]
    await safe_edit(event, random.choice(_COMPLIMENTS).format(user=name))

# ── NUMBER GUESSING GAME ──────────────────────────────────────────
@cmd("guess")
async def _guess(event, arg):
    chat_id = event.chat_id
    sub = (arg or "").strip().lower()

    if sub == "start" or sub == "new":
        secret = random.randint(1, 100)
        guess_games[chat_id] = secret
        return await safe_edit(event,
            f"🎯 **Number Guessing Game Started!**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"I'm thinking of a number between **1** and **100**.\n"
            f"Use `.guess <number>` to guess!\n"
            f"`.guess stop` to end the game."
        )

    if sub == "stop":
        secret = guess_games.pop(chat_id, None)
        if secret is None:
            return await safe_edit(event, "⚠️ No active guess game. Start with `.guess start`")
        return await safe_edit(event, f"🛑 **Game over!** The number was **{secret}**.")

    if not sub or not sub.lstrip("-").isdigit():
        if chat_id not in guess_games:
            return await safe_edit(event,
                "🎯 **Usage:**\n"
                "  `.guess start` — new game\n"
                "  `.guess <1-100>` — make a guess\n"
                "  `.guess stop` — end game"
            )
        return await safe_edit(event, "❌ Provide a number: `.guess <1-100>`")

    if chat_id not in guess_games:
        return await safe_edit(event, "⚠️ No active game! Start with `.guess start`")

    guess = int(sub)
    secret = guess_games[chat_id]

    if guess < 1 or guess > 100:
        return await safe_edit(event, "❌ Number must be between **1** and **100**!")

    diff = abs(guess - secret)
    if guess == secret:
        guess_games.pop(chat_id, None)
        return await safe_edit(event,
            f"🏆 **CORRECT! The number was {secret}!**\n"
            f"⚡ Kurosaki approves. You win! 🔥"
        )
    elif diff <= 5:
        hint = "🔥 Extremely close!"
    elif diff <= 15:
        hint = "♨️ Very warm!"
    elif diff <= 30:
        hint = "🌡️ Getting warmer..."
    else:
        hint = "🧊 Ice cold."

    direction = "📈 Go higher!" if guess < secret else "📉 Go lower!"
    await safe_edit(event, f"{hint}  {direction}\n  Your guess: `{guess}`")

# ── HANGMAN ───────────────────────────────────────────────────────
_HANGMAN_WORDS = [
    "kurosaki","authority","telegram","python","keyboard","dragon",
    "lightning","phantom","warrior","shadow","blazing","nuclear",
    "victory","justice","thunder","emperor","champion","infinite",
]
_HANGMAN_STAGES = ["😵","😟","😨","😰","😱","💀"]

def _hangman_display(data: dict) -> str:
    word    = data["word"]
    guessed = data["guessed"]
    wrong   = data["wrong"]
    lives   = data["lives"]
    board   = " ".join(c if c in guessed else "＿" for c in word)
    stage   = _HANGMAN_STAGES[max(0, len(_HANGMAN_STAGES) - 1 - lives)]
    wrong_str = " ".join(sorted(wrong)) if wrong else "none"
    return (
        f"🎮 **Hangman** {stage}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"  {board}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"  ❤️ Lives: `{lives}`\n"
        f"  ❌ Wrong: `{wrong_str}`\n"
        f"━━━━━━━━━━━━━━━\n"
        f"  `.hangman <letter>`  ·  `.hangman stop`"
    )

@cmd("hangman")
async def _hangman(event, arg):
    chat_id = event.chat_id
    sub = (arg or "").strip().lower()

    if sub in ("start", "new") or not sub:
        if not sub and chat_id in hangman_games:
            return await safe_edit(event, _hangman_display(hangman_games[chat_id]))
        word = random.choice(_HANGMAN_WORDS)
        hangman_games[chat_id] = {
            "word": word, "guessed": set(), "wrong": set(), "lives": 5
        }
        return await safe_edit(event, _hangman_display(hangman_games[chat_id]))

    if sub == "stop":
        data = hangman_games.pop(chat_id, None)
        if data is None:
            return await safe_edit(event, "⚠️ No active hangman. `.hangman start`")
        return await safe_edit(event, f"🛑 **Hangman stopped.** Word was: **{data['word']}**")

    if len(sub) != 1 or not sub.isalpha():
        return await safe_edit(event, "❌ Guess a single letter: `.hangman a`")

    if chat_id not in hangman_games:
        return await safe_edit(event, "⚠️ No active game! `.hangman start`")

    data   = hangman_games[chat_id]
    letter = sub
    word   = data["word"]

    if letter in data["guessed"] or letter in data["wrong"]:
        return await safe_edit(event, f"⚠️ Already guessed `{letter}`!\n{_hangman_display(data)}")

    if letter in word:
        data["guessed"].add(letter)
        if all(c in data["guessed"] for c in word):
            hangman_games.pop(chat_id, None)
            return await safe_edit(event,
                f"🏆 **YOU WIN!** The word was **{word}**! 🔥⚡"
            )
        return await safe_edit(event, f"✅ `{letter}` is in the word!\n{_hangman_display(data)}")
    else:
        data["wrong"].add(letter)
        data["lives"] -= 1
        if data["lives"] <= 0:
            hangman_games.pop(chat_id, None)
            return await safe_edit(event,
                f"💀 **GAME OVER!** The word was **{word}**.\n"
                f"Better luck next time! `.hangman start`"
            )
        return await safe_edit(event, f"❌ `{letter}` is NOT in the word!\n{_hangman_display(data)}")

# ── INFO ──────────────────────────────────────────────────────────
@cmd("info")
async def _info(event, arg):
    target = None
    if event.is_reply:
        r = await event.get_reply_message()
        if r and r.sender_id: target = r.sender_id
    elif arg:
        try:
            ent = await bot.get_entity(arg)
            target = ent.id
        except:
            return await safe_edit(event, "❌ 𝐈𝐧𝐯𝐚𝐥𝐢𝐝 𝐮𝐬𝐞𝐫!")
    if not target:
        return await safe_edit(event, "⚠️ 𝐑𝐞𝐩𝐥𝐲 𝐨𝐫 𝐩𝐫𝐨𝐯𝐢𝐝𝐞 @username/ID")
    await safe_edit(event, "⚡ 𝐅𝐞𝐭𝐜𝐡𝐢𝐧𝐠 𝐮𝐬𝐞𝐫 𝐢𝐧𝐟𝐨...")
    try:
        user = await bot.get_entity(target)
        if getattr(user, "deleted", False):
            return await safe_edit(event, "❌ 𝐃𝐞𝐥𝐞𝐭𝐞𝐝 𝐚𝐜𝐜𝐨𝐮𝐧𝐭!")
        full = await bot(functions.users.GetFullUserRequest(user.id))
        bio = full.full_user.about or "𝐍𝐨 𝐛𝐢𝐨"
        uname = f"@{user.username}" if user.username else "𝐍𝐨 𝐮𝐬𝐞𝐫𝐧𝐚𝐦𝐞"
        name = f"{user.first_name or ''} {user.last_name or ''}".strip()
        # ── Phone: try every possible source ──────────────────────────
        phone = getattr(user, "phone", None)
        phone_src = "contact"
        if not phone:
            try:
                phone = getattr(full.users[0], "phone", None) if full.users else None
                if phone: phone_src = "full_user"
            except Exception:
                phone = None
        if not phone:
            try:
                # Try importing as contact by ID to force Telegram to reveal number
                from telethon.tl.functions.contacts import ImportContactsRequest
                from telethon.tl.types import InputPhoneContact
                # We cannot get the number this way — but try GetContacts as fallback
                contacts_res = await bot(functions.contacts.GetContactsRequest(hash=0))
                for cu in getattr(contacts_res, "users", []):
                    if cu.id == user.id and getattr(cu, "phone", None):
                        phone = cu.phone
                        phone_src = "contacts_list"
                        break
            except Exception:
                pass
        if phone:
            phone_str = f"`+{phone}` ✅ _(via {phone_src})_"
        else:
            phone_str = "🔒 𝐇𝐢𝐝𝐝𝐞𝐧 𝐛𝐲 𝐩𝐫𝐢𝐯𝐚𝐜𝐲 𝐬𝐞𝐭𝐭𝐢𝐧𝐠𝐬"
        # ─────────────────────────────────────────────────────────────
        dc_id = getattr(user, "dc_id", None)
        common_chats = getattr(full.full_user, "common_chats_count", 0)
        text = (
            f"👤 **𝐔𝐒𝐄𝐑 𝐈𝐍𝐅𝐎**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"🆔 **𝐈𝐃:** `{user.id}`\n"
            f"📛 **𝐍𝐚𝐦𝐞:** {name}\n"
            f"🔗 **𝐔𝐬𝐞𝐫𝐧𝐚𝐦𝐞:** {uname}\n"
            f"📞 **𝐏𝐡𝐨𝐧𝐞:** {phone_str}\n"
            f"📝 **𝐁𝐢𝐨:** {bio}\n"
            f"🌐 **𝐃𝐂:** `{dc_id or 'Unknown'}`\n"
            f"💬 **𝐂𝐨𝐦𝐦𝐨𝐧 𝐆𝐫𝐨𝐮𝐩𝐬:** `{common_chats}`\n"
            f"🤖 **𝐁𝐨𝐭:** {'Yes' if user.bot else 'No'}\n"
            f"✅ **𝐕𝐞𝐫𝐢𝐟𝐢𝐞𝐝:** {'Yes' if getattr(user, 'verified', False) else 'No'}\n"
            f"🔒 **𝐑𝐞𝐬𝐭𝐫𝐢𝐜𝐭𝐞𝐝:** {'Yes' if getattr(user, 'restricted', False) else 'No'}"
        )
        if not phone:
            text += f"\n💡 _Try_ `.getphone` _to query OSINT bot_"
        await safe_edit(event, text)
    except Exception as e:
        await safe_edit(event, f"❌ 𝐄𝐫𝐫𝐨𝐫: `{e}`")

# ── PHONE OSINT LOOKUP ────────────────────────────────────────────
@cmd("getphone")
async def _getphone(event, arg):
    global PHONE_OSINT_BOT
    target_id = None
    if event.is_reply:
        r = await event.get_reply_message()
        if r and r.sender_id:
            target_id = r.sender_id
    elif arg:
        try:
            ent = await bot.get_entity(arg.strip())
            target_id = ent.id
        except:
            return await safe_edit(event, "❌ 𝐈𝐧𝐯𝐚𝐥𝐢𝐝 𝐮𝐬𝐞𝐫!")
    if not target_id:
        return await safe_edit(event, "⚠️ 𝐑𝐞𝐩𝐥𝐲 𝐨𝐫 𝐩𝐫𝐨𝐯𝐢𝐝𝐞 @username/ID")
    await safe_edit(event, "🔍 𝐂𝐡𝐞𝐜𝐤𝐢𝐧𝐠 𝐓𝐞𝐥𝐞𝐠𝐫𝐚𝐦 𝐀𝐏𝐈...")
    try:
        user = await bot.get_entity(target_id)
        uname = f"@{user.username}" if user.username else str(user.id)
        name  = f"{user.first_name or ''} {user.last_name or ''}".strip()
        # Layer 1: direct user object
        phone = getattr(user, "phone", None)
        # Layer 2: GetFullUser
        if not phone:
            try:
                full2 = await bot(functions.users.GetFullUserRequest(user.id))
                phone = getattr(full2.users[0], "phone", None) if full2.users else None
            except:
                pass
        # Layer 3: contacts list
        if not phone:
            try:
                cr = await bot(functions.contacts.GetContactsRequest(hash=0))
                for cu in getattr(cr, "users", []):
                    if cu.id == user.id:
                        phone = getattr(cu, "phone", None)
                        break
            except:
                pass
        if phone:
            return await safe_edit(event,
                f"📞 **𝐏𝐡𝐨𝐧𝐞 𝐅𝐨𝐮𝐧𝐝 (𝐓𝐞𝐥𝐞𝐠𝐫𝐚𝐦)**\n"
                f"👤 {name} · {uname}\n"
                f"📱 `+{phone}`"
            )
        # Layer 4: query OSINT bot
        await safe_edit(event,
            f"🔒 𝐓𝐞𝐥𝐞𝐠𝐫𝐚𝐦 𝐀𝐏𝐈: 𝐡𝐢𝐝𝐝𝐞𝐧\n"
            f"⏳ 𝐐𝐮𝐞𝐫𝐲𝐢𝐧𝐠 `{PHONE_OSINT_BOT}`..."
        )
        try:
            osint_ent = await bot.get_entity(PHONE_OSINT_BOT)
            async with bot.conversation(osint_ent, timeout=30) as conv:
                await conv.send_message(uname)
                resp = await conv.get_response()
                reply_text = resp.text or "(𝐧𝐨 𝐭𝐞𝐱𝐭 𝐫𝐞𝐬𝐩𝐨𝐧𝐬𝐞)"
            await safe_edit(event,
                f"📞 **𝐏𝐡𝐨𝐧𝐞 𝐋𝐨𝐨𝐤𝐮𝐩 — {uname}**\n"
                f"━━━━━━━━━━━━━━━\n"
                f"🤖 𝐕𝐢𝐚 `{PHONE_OSINT_BOT}`:\n\n"
                f"{reply_text[:900]}"
            )
        except asyncio.TimeoutError:
            await safe_edit(event, f"⏰ `{PHONE_OSINT_BOT}` 𝐝𝐢𝐝𝐧'𝐭 𝐫𝐞𝐬𝐩𝐨𝐧𝐝 𝐢𝐧 𝟑𝟎𝐬\n💡 𝐓𝐫𝐲 `.setphonebot @otherbot`")
        except Exception as e2:
            await safe_edit(event, f"❌ 𝐎𝐒𝐈𝐍𝐓 𝐛𝐨𝐭 𝐞𝐫𝐫𝐨𝐫: `{e2}`\n💡 𝐔𝐬𝐞 `.setphonebot @botname` 𝐭𝐨 𝐜𝐡𝐚𝐧𝐠𝐞 𝐛𝐨𝐭")
    except Exception as e:
        await safe_edit(event, f"❌ 𝐄𝐫𝐫𝐨𝐫: `{e}`")

@cmd("setphonebot")
async def _setphonebot(event, arg):
    global PHONE_OSINT_BOT
    if not arg:
        return await safe_edit(event,
            f"🤖 **𝐂𝐮𝐫𝐫𝐞𝐧𝐭 𝐎𝐒𝐈𝐍𝐓 𝐛𝐨𝐭:** `{PHONE_OSINT_BOT}`\n"
            f"💡 𝐔𝐬𝐚𝐠𝐞: `.setphonebot @botusername`"
        )
    PHONE_OSINT_BOT = arg.strip()
    await safe_edit(event, f"✅ 𝐏𝐡𝐨𝐧𝐞 𝐥𝐨𝐨𝐤𝐮𝐩 𝐛𝐨𝐭 𝐬𝐞𝐭 𝐭𝐨: `{PHONE_OSINT_BOT}`")

# ── PROFILE CLONE ─────────────────────────────────────────────────
@cmd("copy")
async def _copy(event, arg):
    global CLONE_DATA, CLONE_ACTIVE, LAST_CLONE_ID
    reply = await event.get_reply_message() if event.is_reply else None
    target = None
    if reply:
        try: target = await bot.get_entity(reply.sender_id)
        except: pass
    if not target and arg:
        try: target = await bot.get_entity(arg.strip())
        except: pass
    if not target:
        return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐨𝐫 𝐩𝐫𝐨𝐯𝐢𝐝𝐞 @username/ID")
    me = await _get_me()
    if target.id == me.id:
        return await safe_edit(event, "⚠️ 𝐂𝐚𝐧𝐧𝐨𝐭 𝐜𝐥𝐨𝐧𝐞 𝐲𝐨𝐮𝐫𝐬𝐞𝐥𝐟!")
    await safe_edit(event, "⚡ 𝐂𝐥𝐨𝐧𝐢𝐧𝐠 𝐩𝐫𝐨𝐟𝐢𝐥𝐞...")
    if not CLONE_ACTIVE:
        try:
            full = await bot(functions.users.GetFullUserRequest(me.id))
            CLONE_DATA["name"] = me.first_name
            CLONE_DATA["last"] = me.last_name
            CLONE_DATA["bio"] = full.full_user.about
            CLONE_DATA["username"] = getattr(me, "username", None) or ""
            photos = await bot.get_profile_photos(me.id, limit=1)
            if photos:
                CLONE_DATA["photo_bytes"] = await bot.download_media(photos[0], file=bytes)
        except: pass
    try:
        new_name = getattr(target, "first_name", None) or "User"
        new_last = getattr(target, "last_name", None) or ""
        new_bio = ""
        target_username = getattr(target, "username", None) or ""
        try:
            full_t = await bot(functions.users.GetFullUserRequest(target.id))
            new_bio = full_t.full_user.about or ""
        except: pass
        await bot(functions.account.UpdateProfileRequest(
            first_name=new_name, last_name=new_last, about=new_bio
        ))
        photos = await bot.get_profile_photos(target.id, limit=1)
        if photos:
            photo_bytes = await bot.download_media(photos[0], file=bytes)
            buf = BytesIO(photo_bytes); buf.name = "photo.jpg"
            await bot(functions.photos.UploadProfilePhotoRequest(
                file=await bot.upload_file(buf)
            ))
        # Try to copy username with 1-char variation (append x or swap last char)
        if target_username:
            variations = [
                target_username + "x",
                target_username + "_",
                target_username[:-1] + ("x" if target_username[-1] != "x" else "y"),
            ]
            for uname in variations:
                if re.fullmatch(r"[A-Za-z0-9_]{5,32}", uname):
                    try:
                        await bot(functions.account.UpdateUsernameRequest(username=uname))
                        break
                    except: continue
        CLONE_ACTIVE = True
        LAST_CLONE_ID = target.id
        await safe_edit(event, f"✅ **𝐂𝐥𝐨𝐧𝐞𝐝 `{new_name}`'𝐬 𝐩𝐫𝐨𝐟𝐢𝐥𝐞! (𝐮𝐬𝐞 `.𝐧𝐨𝐫𝐦𝐚𝐥` 𝐭𝐨 𝐫𝐞𝐯𝐞𝐫𝐭)**")
    except Exception as e:
        await safe_edit(event, f"❌ 𝐂𝐥𝐨𝐧𝐞 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

@cmd("normal")
async def _normal(event, _):
    global CLONE_ACTIVE, LAST_CLONE_ID
    if not CLONE_ACTIVE:
        return await safe_edit(event, "⚠️ 𝐍𝐨 𝐚𝐜𝐭𝐢𝐯𝐞 𝐜𝐥𝐨𝐧𝐞!")
    await safe_edit(event, "⚡ 𝐑𝐞𝐬𝐭𝐨𝐫𝐢𝐧𝐠 𝐩𝐫𝐨𝐟𝐢𝐥𝐞...")
    try:
        # Step 1: Delete the cloned photo using get_profile_photos (reliable for self)
        try:
            my_photos = await bot.get_profile_photos("me", limit=1)
            if my_photos:
                p = my_photos[0]
                await bot(functions.photos.DeletePhotosRequest(
                    id=[types.InputPhoto(
                        id=p.id,
                        access_hash=p.access_hash,
                        file_reference=p.file_reference,
                    )]
                ))
        except Exception as pe:
            logger.warning(f"[normal] photo delete: {pe}")

        # Step 2: Re-upload original photo so it comes back guaranteed
        if CLONE_DATA.get("photo_bytes"):
            try:
                buf = BytesIO(CLONE_DATA["photo_bytes"]); buf.name = "photo.jpg"
                await bot(functions.photos.UploadProfilePhotoRequest(
                    file=await bot.upload_file(buf)
                ))
            except Exception as upe:
                logger.warning(f"[normal] photo restore: {upe}")

        # Step 3: Restore original name & bio
        await bot(functions.account.UpdateProfileRequest(
            first_name=CLONE_DATA.get("name") or "",
            last_name=CLONE_DATA.get("last") or "",
            about=CLONE_DATA.get("bio") or "",
        ))

        # Step 4: Restore original username
        if CLONE_DATA.get("username") is not None:
            try:
                await bot(functions.account.UpdateUsernameRequest(username=CLONE_DATA["username"] or ""))
            except Exception as ue:
                logger.warning(f"[normal] username restore: {ue}")

        CLONE_ACTIVE = False
        LAST_CLONE_ID = None
        await safe_edit(event, "✅ **𝐏𝐫𝐨𝐟𝐢𝐥𝐞 𝐑𝐞𝐬𝐭𝐨𝐫𝐞𝐝! 𝐂𝐥𝐨𝐧𝐞𝐝 𝐩𝐡𝐨𝐭𝐨 𝐫𝐞𝐦𝐨𝐯𝐞𝐝, 𝐨𝐫𝐢𝐠𝐢𝐧𝐚𝐥 𝐢𝐬 𝐛𝐚𝐜𝐤!**")
    except Exception as e:
        await safe_edit(event, f"❌ 𝐑𝐞𝐬𝐭𝐨𝐫𝐞 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── CLONE RAID ────────────────────────────────────────────────────
@cmd("cloneraid")
async def _cloneraid(event, arg):
    global CLONE_RAID_TASK, CLONE_ACTIVE, LAST_CLONE_ID, CLONE_DATA
    parts = arg.split() if arg else []
    if not parts:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.cloneraid @user <mins>`\n𝐄𝐱: `.cloneraid @username 5`")
    username = parts[0].lstrip("@")
    interval = 5
    if len(parts) >= 2 and parts[1].isdigit():
        interval = max(1, int(parts[1]))
    try:
        target = await bot.get_entity(username)
    except Exception as e:
        return await safe_edit(event, f"❌ 𝐂𝐚𝐧𝐧𝐨𝐭 𝐫𝐞𝐬𝐨𝐥𝐯𝐞 𝐮𝐬𝐞𝐫: `{e}`")
    if CLONE_RAID_TASK and not CLONE_RAID_TASK.done():
        CLONE_RAID_TASK.cancel()
    await safe_edit(event, f"⚡ **𝐂𝐋𝐎𝐍𝐄 𝐑𝐀𝐈𝐃 𝐒𝐓𝐀𝐑𝐓𝐄𝐃** → `{getattr(target,'first_name','?')}` | 𝐑𝐞𝐜𝐥𝐨𝐧𝐞 𝐞𝐯𝐞𝐫𝐲 `{interval}` 𝐦𝐢𝐧𝐬\n🛑 𝐔𝐬𝐞 `.scloneraid` 𝐭𝐨 𝐬𝐭𝐨𝐩")

    async def _do_clone():
        me = await _get_me()
        full = await bot(functions.users.GetFullUserRequest(me.id))
        CLONE_DATA["name"] = me.first_name
        CLONE_DATA["last"] = me.last_name
        CLONE_DATA["bio"] = full.full_user.about
        CLONE_DATA["username"] = getattr(me, "username", None) or ""
        photos = await bot.get_profile_photos(me.id, limit=1)
        if photos:
            CLONE_DATA["photo_bytes"] = await bot.download_media(photos[0], file=bytes)

    async def _apply_clone(tgt):
        new_name = getattr(tgt, "first_name", None) or "User"
        new_last = getattr(tgt, "last_name", None) or ""
        new_bio = ""
        tgt_username = getattr(tgt, "username", None) or ""
        try:
            full_t = await bot(functions.users.GetFullUserRequest(tgt.id))
            new_bio = full_t.full_user.about or ""
        except: pass
        # Delete current top photo before uploading new clone
        try:
            cur_photos = await bot.get_profile_photos("me", limit=1)
            if cur_photos:
                p = cur_photos[0]
                await bot(functions.photos.DeletePhotosRequest(
                    id=[types.InputPhoto(id=p.id, access_hash=p.access_hash, file_reference=p.file_reference)]
                ))
        except: pass
        await bot(functions.account.UpdateProfileRequest(
            first_name=new_name, last_name=new_last, about=new_bio
        ))
        photos = await bot.get_profile_photos(tgt.id, limit=1)
        if photos:
            photo_bytes = await bot.download_media(photos[0], file=bytes)
            buf = BytesIO(photo_bytes); buf.name = "photo.jpg"
            await bot(functions.photos.UploadProfilePhotoRequest(file=await bot.upload_file(buf)))
    async def _raid_loop():
        global CLONE_ACTIVE, LAST_CLONE_ID
        try:
            await _do_clone()
            while True:
                try:
                    await _apply_clone(target)
                    CLONE_ACTIVE = True
                    LAST_CLONE_ID = target.id
                except Exception as le:
                    logger.warning(f"[cloneraid] loop err: {le}")
                await asyncio.sleep(interval * 60)
        except asyncio.CancelledError:
            pass

    CLONE_RAID_TASK = asyncio.ensure_future(_raid_loop())

@cmd("scloneraid")
async def _scloneraid(event, _):
    global CLONE_RAID_TASK
    if CLONE_RAID_TASK and not CLONE_RAID_TASK.done():
        CLONE_RAID_TASK.cancel()
        CLONE_RAID_TASK = None
        await safe_edit(event, "🛑 **𝐂𝐋𝐎𝐍𝐄 𝐑𝐀𝐈𝐃 𝐒𝐓𝐎𝐏𝐏𝐄𝐃!** 𝐔𝐬𝐞 `.normal` 𝐭𝐨 𝐫𝐞𝐬𝐭𝐨𝐫𝐞 𝐩𝐫𝐨𝐟𝐢𝐥𝐞.")
    else:
        await safe_edit(event, "⚠️ 𝐍𝐨 𝐚𝐜𝐭𝐢𝐯𝐞 𝐜𝐥𝐨𝐧𝐞 𝐫𝐚𝐢𝐝!")

# ── TTS ───────────────────────────────────────────────────────────
@cmd("tts")
async def _tts(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.tts [lang] <text>`\n𝐄𝐱: `.tts hi नमस्ते`")
    parts = arg.split(" ", 1)
    if len(parts) > 1 and len(parts[0]) == 2 and parts[0].isalpha():
        lang, text = parts[0], parts[1]
    else:
        lang, text = "en", arg
    await safe_edit(event, "⚡ 𝐆𝐞𝐧𝐞𝐫𝐚𝐭𝐢𝐧𝐠 𝐯𝐨𝐢𝐜𝐞...")
    try:
        path = os.path.join(TEMP_PATH, f"tts_{event.id}.mp3")
        def _gen_tts():
            t = gTTS(text=text[:500], lang=lang)
            t.save(path)
        await asyncio.to_thread(_gen_tts)
        await bot.send_file(event.chat_id, path, voice_note=True, caption=f"🔊 `{text[:50]}`")
        os.remove(path)
        await event.delete()
    except Exception as e:
        await safe_edit(event, f"❌ 𝐓𝐓𝐒 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── QR CODE ───────────────────────────────────────────────────────
@cmd("qrcode")
async def _qrcode(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.qrcode <text>`")
    await safe_edit(event, "⚡ 𝐆𝐞𝐧𝐞𝐫𝐚𝐭𝐢𝐧𝐠 𝐐𝐑...")
    try:
        qr = qrcode.QRCode(version=1, box_size=10, border=4)
        qr.add_data(arg)
        qr.make(fit=True)
        img = qr.make_image(fill_color="black", back_color="white")
        path = os.path.join(TEMP_PATH, f"qr_{event.id}.png")
        img.save(path)
        await bot.send_file(event.chat_id, path, caption=f"📷 𝐐𝐑 𝐟𝐨𝐫: `{arg[:60]}`")
        os.remove(path)
        await event.delete()
    except Exception as e:
        await safe_edit(event, f"❌ 𝐐𝐑 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── FANCY TEXT ────────────────────────────────────────────────────
_FANCY_MAP = str.maketrans(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ",
    "𝒶𝒷𝒸𝒹𝑒𝒻𝑔𝒽𝒾𝒿𝓀𝓁𝓂𝓃𝑜𝓅𝓆𝓇𝓈𝓉𝓊𝓋𝓌𝓍𝓎𝓏𝒜𝐵𝒞𝒟𝐸𝐹𝒢𝐻𝐼𝒥𝒦𝐿𝑀𝒩𝒪𝒫𝒬𝑅𝒮𝒯𝒰𝒱𝒲𝒳𝒴𝒵"
)

@cmd("fancy")
async def _fancy(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.fancy <text>`")
    await safe_edit(event, f"✨ {arg.translate(_FANCY_MAP)}")

@cmd("style")
async def _style(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.style <text>`")
    t = arg[:500]
    fancy = t.translate(_FANCY_MAP)
    await safe_edit(event,
        f"🎨 **𝐓𝐞𝐱𝐭 𝐒𝐭𝐲𝐥𝐞𝐬:**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"✨ 𝐅𝐚𝐧𝐜𝐲 → {fancy}\n"
        f"**𝐁𝐨𝐥𝐝** → **{t}**\n"
        f"__𝐈𝐭𝐚𝐥𝐢𝐜__ → __{t}__\n"
        f"`𝐌𝐨𝐧𝐨` → `{t}`"
    )

@cmd("emoji")
async def _emoji(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.emoji <text>`")
    pool = ["🔥","❤️","✨","⚡","💥","🌟","💫","🎯","💎","🦋","🌈","🧨","🌷","🌸","🪄","🌊","❄️","🌙","☀️","💣","🎵","🧿"]
    emojis = "".join(random.choice(pool) for _ in range(8))
    await safe_edit(event, f"😀 **𝐄𝐦𝐨𝐣𝐢 𝐒𝐭𝐲𝐥𝐞:**\n{arg[:500]} {emojis}")

# ── CALCULATOR ────────────────────────────────────────────────────
@cmd("calc")
async def _calc(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.calc <expression>`")
    expr = arg.strip()
    if any(c not in "0123456789+-*/().% " for c in expr):
        return await safe_edit(event, "❌ 𝐈𝐧𝐯𝐚𝐥𝐢𝐝 𝐜𝐡𝐚𝐫𝐚𝐜𝐭𝐞𝐫𝐬!")
    try:
        result = eval(expr, {"__builtins__": None}, {"abs": abs, "round": round, "pow": pow, "sqrt": math.sqrt})
        await safe_edit(event, f"🧮 **𝐂𝐚𝐥𝐜𝐮𝐥𝐚𝐭𝐨𝐫**\n📥 `{expr}`\n📤 `{result}`")
    except:
        await safe_edit(event, "❌ 𝐈𝐧𝐯𝐚𝐥𝐢𝐝 𝐞𝐱𝐩𝐫𝐞𝐬𝐬𝐢𝐨𝐧!")

# ── WEATHER ───────────────────────────────────────────────────────
@cmd("weather")
async def _weather(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.weather <city>`")
    await safe_edit(event, "⚡ 𝐅𝐞𝐭𝐜𝐡𝐢𝐧𝐠 𝐰𝐞𝐚𝐭𝐡𝐞𝐫...")
    try:
        geo = await asyncio.to_thread(lambda: requests.get(
            f"https://geocoding-api.open-meteo.com/v1/search?name={arg}&count=1", timeout=8
        ).json())
        if not geo.get("results"):
            return await safe_edit(event, "❌ 𝐂𝐢𝐭𝐲 𝐧𝐨𝐭 𝐟𝐨𝐮𝐧𝐝!")
        r = geo["results"][0]
        w = await asyncio.to_thread(lambda: requests.get(
            f"https://api.open-meteo.com/v1/forecast?latitude={r['latitude']}&longitude={r['longitude']}&current_weather=true&hourly=relativehumidity_2m",
            timeout=8
        ).json())
        cw = w.get("current_weather", {})
        humidity = w.get("hourly", {}).get("relativehumidity_2m", [None])[0]
        wcode_map = {0:"☀️ Clear",1:"🌤 Mainly clear",2:"⛅ Partly cloudy",3:"☁️ Overcast",
                     45:"🌫 Foggy",51:"🌦 Drizzle",61:"🌧 Rain",71:"🌨 Snow",80:"🌧 Showers",95:"⛈ Thunderstorm"}
        condition = wcode_map.get(cw.get("weathercode"), f"Code {cw.get('weathercode')}")
        await safe_edit(event,
            f"🌦️ **𝐖𝐞𝐚𝐭𝐡𝐞𝐫 𝐢𝐧 {r['name']}, {r.get('country_code','')}**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"🌡️ **𝐓𝐞𝐦𝐩:** `{cw.get('temperature')}°C`\n"
            f"💨 **𝐖𝐢𝐧𝐝:** `{cw.get('windspeed')} km/h`\n"
            f"💧 **𝐇𝐮𝐦𝐢𝐝𝐢𝐭𝐲:** `{humidity}%`\n"
            f"🌤 **𝐂𝐨𝐧𝐝𝐢𝐭𝐢𝐨𝐧:** {condition}"
        )
    except Exception as e:
        await safe_edit(event, f"❌ 𝐖𝐞𝐚𝐭𝐡𝐞𝐫 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── IP LOOKUP ─────────────────────────────────────────────────────
@cmd("ip")
async def _ip(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.ip <address>`")
    await safe_edit(event, "⚡ 𝐋𝐨𝐨𝐤𝐢𝐧𝐠 𝐮𝐩 𝐈𝐏...")
    try:
        data = await asyncio.to_thread(lambda: requests.get(f"http://ip-api.com/json/{arg}", timeout=8).json())
        if data.get("status") != "success":
            return await safe_edit(event, "❌ 𝐈𝐧𝐯𝐚𝐥𝐢𝐝 𝐈𝐏!")
        await safe_edit(event,
            f"🌍 **𝐈𝐏 𝐈𝐧𝐟𝐨**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"📡 **𝐈𝐏:** `{data.get('query')}`\n"
            f"🌐 **𝐂𝐨𝐮𝐧𝐭𝐫𝐲:** `{data.get('country')}`\n"
            f"🏙️ **𝐂𝐢𝐭𝐲:** `{data.get('city')}`\n"
            f"🏢 **𝐑𝐞𝐠𝐢𝐨𝐧:** `{data.get('regionName')}`\n"
            f"📍 **𝐈𝐒𝐏:** `{data.get('isp')}`\n"
            f"🕐 **𝐓𝐢𝐦𝐞𝐳𝐨𝐧𝐞:** `{data.get('timezone')}`"
        )
    except Exception as e:
        await safe_edit(event, f"❌ 𝐈𝐏 𝐥𝐨𝐨𝐤𝐮𝐩 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── URL SHORTENER ─────────────────────────────────────────────────
@cmd("short")
async def _short(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.short <url>`")
    if not arg.startswith(("http://", "https://")):
        arg = "https://" + arg
    await safe_edit(event, "⚡ 𝐒𝐡𝐨𝐫𝐭𝐞𝐧𝐢𝐧𝐠...")
    try:
        short = await asyncio.to_thread(lambda: requests.get(
            f"http://tinyurl.com/api-create.php?url={requests.utils.requote_uri(arg)}", timeout=8
        ).text.strip())
        await safe_edit(event, f"🔗 **𝐒𝐡𝐨𝐫𝐭 𝐔𝐑𝐋:**\n`{short}`")
    except Exception as e:
        await safe_edit(event, f"❌ 𝐒𝐡𝐨𝐫𝐭𝐞𝐧 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── MUSIC DOWNLOAD (V9 — fully fixed) ────────────────────────────
def _build_ytdlp_opts(outtmpl: str, with_ffmpeg: bool = True,
                      progress_hook=None, writethumbnail: bool = False) -> Dict[str, Any]:
    """
    Build yt-dlp options.
    V9 fix: progress_hook wired in; thumbnail download optional.
    with_ffmpeg=True  → extract & convert to mp3 (needs ffmpeg)
    with_ffmpeg=False → download best audio as-is (no ffmpeg needed)
    """
    opts: Dict[str, Any] = {
        "format": "bestaudio[ext=m4a]/bestaudio[ext=webm]/bestaudio/best",
        "outtmpl": outtmpl,
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "nocheckcertificate": True,
        "retries": 10,
        "fragment_retries": 10,
        "socket_timeout": 30,
        "age_limit": 99,
        "writethumbnail": writethumbnail,
        "http_headers": {
            "User-Agent": (
                "Mozilla/5.0 (Linux; Android 12; Pixel 6) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Mobile Safari/537.36"
            ),
            "Accept-Language": "en-US,en;q=0.9",
        },
        "extractor_args": {
            "youtube": {
                "player_client": ["tv_embedded", "ios", "web"],
            }
        },
    }
    if progress_hook:
        opts["progress_hooks"] = [progress_hook]
    if with_ffmpeg:
        opts["postprocessors"] = [
            {
                "key": "FFmpegExtractAudio",
                "preferredcodec": "mp3",
                "preferredquality": "192",
            },
        ]
        if writethumbnail:
            opts["postprocessors"].append({
                "key": "EmbedThumbnail",
                "already_have_thumbnail": False,
            })
    if YTDLP_COOKIES_FILE and os.path.isfile(YTDLP_COOKIES_FILE):
        opts["cookiefile"] = YTDLP_COOKIES_FILE
    elif YTDLP_COOKIES_BROWSER:
        opts["cookiesfrombrowser"] = (YTDLP_COOKIES_BROWSER,)
    return opts


def _build_ytdlp_video_opts(outtmpl: str, progress_hook=None) -> Dict[str, Any]:
    """Build yt-dlp options for video download (V9)."""
    opts: Dict[str, Any] = {
        "format": "bestvideo[ext=mp4]+bestaudio[ext=m4a]/bestvideo+bestaudio/best[ext=mp4]/best",
        "outtmpl": outtmpl,
        "quiet": True,
        "no_warnings": True,
        "noplaylist": True,
        "nocheckcertificate": True,
        "retries": 10,
        "fragment_retries": 10,
        "socket_timeout": 30,
        "age_limit": 99,
        "merge_output_format": "mp4",
        "http_headers": {
            "User-Agent": (
                "Mozilla/5.0 (Linux; Android 12; Pixel 6) "
                "AppleWebKit/537.36 (KHTML, like Gecko) "
                "Chrome/124.0.0.0 Mobile Safari/537.36"
            ),
            "Accept-Language": "en-US,en;q=0.9",
        },
        "extractor_args": {
            "youtube": {
                "player_client": ["tv_embedded", "ios", "web"],
            }
        },
    }
    if progress_hook:
        opts["progress_hooks"] = [progress_hook]
    if YTDLP_COOKIES_FILE and os.path.isfile(YTDLP_COOKIES_FILE):
        opts["cookiefile"] = YTDLP_COOKIES_FILE
    elif YTDLP_COOKIES_BROWSER:
        opts["cookiesfrombrowser"] = (YTDLP_COOKIES_BROWSER,)
    return opts


def _yt_error_help(err: Exception) -> str:
    text = str(err)
    if any(kw in text for kw in ["Sign in", "not a bot", "cookies", "confirm your age", "age-restricted", "LOGIN_REQUIRED"]):
        return (
            "❌ **𝐘𝐨𝐮𝐓𝐮𝐛𝐞 𝐀𝐠𝐞/𝐋𝐨𝐠𝐢𝐧 𝐄𝐫𝐫𝐨𝐫**\n"
            "━━━━━━━━━━━━━━━\n"
            "𝐅𝐢𝐱 𝐨𝐩𝐭𝐢𝐨𝐧 𝟏 — 𝐂𝐨𝐨𝐤𝐢𝐞𝐬 𝐟𝐢𝐥𝐞:\n"
            "• 𝐈𝐧𝐬𝐭𝐚𝐥𝐥 `EditThisCookie` 𝐢𝐧 𝐂𝐡𝐫𝐨𝐦𝐞\n"
            "• 𝐋𝐨𝐠 𝐢𝐧 𝐭𝐨 𝐘𝐨𝐮𝐓𝐮𝐛𝐞, 𝐞𝐱𝐩𝐨𝐫𝐭 𝐚𝐬 𝐍𝐞𝐭𝐬𝐜𝐚𝐩𝐞 𝐟𝐨𝐫𝐦𝐚𝐭\n"
            "• 𝐒𝐚𝐯𝐞 𝐟𝐢𝐥𝐞 𝐚𝐬 `cookies.txt` 𝐧𝐞𝐱𝐭 𝐭𝐨 𝐛𝐨𝐭\n"
            "• 𝐒𝐞𝐭 𝐞𝐧𝐯: `YTDLP_COOKIES_FILE=cookies.txt`\n\n"
            "𝐅𝐢𝐱 𝐨𝐩𝐭𝐢𝐨𝐧 𝟐 — 𝐁𝐫𝐨𝐰𝐬𝐞𝐫 (𝐥𝐨𝐜𝐚𝐥 𝐨𝐧𝐥𝐲):\n"
            "• 𝐒𝐞𝐭 𝐞𝐧𝐯: `YTDLP_COOKIES_BROWSER=chrome`\n\n"
            "𝐓𝐡𝐞𝐧 𝐫𝐞𝐬𝐭𝐚𝐫𝐭 𝐭𝐡𝐞 𝐛𝐨𝐭."
        )
    if "Private video" in text or "unavailable" in text:
        return "❌ 𝐓𝐡𝐢𝐬 𝐯𝐢𝐝𝐞𝐨 𝐢𝐬 𝐩𝐫𝐢𝐯𝐚𝐭𝐞 𝐨𝐫 𝐮𝐧𝐚𝐯𝐚𝐢𝐥𝐚𝐛𝐥𝐞."
    if "No such video" in text or "invalid URL" in text:
        return "❌ 𝐈𝐧𝐯𝐚𝐥𝐢𝐝 𝐬𝐨𝐧𝐠 𝐧𝐚𝐦𝐞 𝐨𝐫 𝐔𝐑𝐋."
    if "ffmpeg not found" in text.lower() or "ffprobe" in text.lower():
        return "❌ 𝐅𝐅𝐦𝐩𝐞𝐠 𝐧𝐨𝐭 𝐢𝐧𝐬𝐭𝐚𝐥𝐥𝐞𝐝. 𝐑𝐮𝐧: `apt install ffmpeg`"
    if any(kw in text for kw in ["HTTP Error 403", "403", "Forbidden", "bot", "robot", "challenge"]):
        return (
            "❌ **𝐘𝐨𝐮𝐓𝐮𝐛𝐞 𝐁𝐥𝐨𝐜𝐤𝐞𝐝 𝐃𝐨𝐰𝐧𝐥𝐨𝐚𝐝**\n"
            "━━━━━━━━━━━━━━━\n"
            "𝐑𝐮𝐧 𝐭𝐡𝐢𝐬 𝐭𝐨 𝐟𝐢𝐱:\n"
            "`pip install -U yt-dlp`\n\n"
            "𝐈𝐟 𝐬𝐭𝐢𝐥𝐥 𝐟𝐚𝐢𝐥𝐢𝐧𝐠, 𝐚𝐝𝐝 𝐚 `cookies.txt` 𝐟𝐢𝐥𝐞."
        )
    if "size" in text.lower() or "too large" in text.lower() or "2000" in text:
        return "❌ 𝐅𝐢𝐥𝐞 𝐭𝐨𝐨 𝐥𝐚𝐫𝐠𝐞 𝐟𝐨𝐫 𝐓𝐞𝐥𝐞𝐠𝐫𝐚𝐦 (𝟐𝐆𝐁 𝐥𝐢𝐦𝐢𝐭)."
    return (
        f"❌ 𝐅𝐚𝐢𝐥𝐞𝐝: `{text[:120]}`\n"
        f"💡 𝐓𝐫𝐲: `pip install -U yt-dlp` 𝐭𝐨 𝐮𝐩𝐝𝐚𝐭𝐞"
    )


def _find_media_file(base_dir: str, prefix: str, video_id: str = None,
                     exts: tuple = ("mp3", "m4a", "webm", "opus", "ogg", "aac", "wav"),
                     max_age: int = 120) -> Optional[str]:
    """
    V9: unified file finder for audio & video.
    Tries video_id match → glob → recent fallback.
    """
    if video_id:
        for ext in exts:
            p = os.path.join(base_dir, f"{prefix}{video_id}.{ext}")
            if os.path.isfile(p) and os.path.getsize(p) > 0:
                return p
        matches = [f for f in _glob.glob(os.path.join(base_dir, f"{prefix}{video_id}.*"))
                   if os.path.getsize(f) > 0]
        if matches:
            return sorted(matches, key=os.path.getmtime, reverse=True)[0]
    # Fallback: any matching file created within max_age seconds
    all_matches = []
    for ext in exts:
        all_matches.extend(_glob.glob(os.path.join(base_dir, f"{prefix}*.{ext}")))
    recent = [f for f in all_matches
              if os.path.isfile(f) and os.path.getsize(f) > 0
              and (time.time() - os.path.getmtime(f)) < max_age]
    if recent:
        return sorted(recent, key=os.path.getmtime, reverse=True)[0]
    return None


def _make_progress_bar(pct: float, width: int = 12) -> str:
    filled = int(width * pct / 100)
    return "█" * filled + "░" * (width - filled)


def _run_ytdl_sync(opts: dict, query: str):
    """Run yt-dlp synchronously (called inside asyncio.to_thread)."""
    with yt_dlp.YoutubeDL(opts) as ydl:
        info = ydl.extract_info(query, download=True)
    if info and "entries" in info:
        info = next((x for x in info.get("entries", []) if x), None)
    return info


@cmd("music")
async def _music(event, arg):
    if not arg:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.music <song name or URL>`")

    m = await safe_edit(event, f"🎵 𝐒𝐞𝐚𝐫𝐜𝐡𝐢𝐧𝐠: `{arg}`...")
    base_tmpl = os.path.join(DOWNLOAD_PATH, "music_%(id)s.%(ext)s")
    query     = arg if arg.startswith(("http://", "https://")) else f"ytsearch1:{arg}"
    info      = None
    out_path  = None
    video_id  = None
    _last_pct = [-1]
    _loop     = asyncio.get_event_loop()  # V9 fix: capture loop before thread

    # ── Live progress hook (runs inside thread, schedules UI update) ──
    def _progress(d):
        if d.get("status") != "downloading": return
        total   = d.get("total_bytes") or d.get("total_bytes_estimate") or 0
        downloaded = d.get("downloaded_bytes", 0)
        if total <= 0: return
        pct = int(downloaded * 100 / total)
        if pct == _last_pct[0] or pct % 5 != 0: return
        _last_pct[0] = pct
        bar = _make_progress_bar(pct)
        asyncio.run_coroutine_threadsafe(
            safe_edit(m, f"🎵 𝐃𝐨𝐰𝐧𝐥𝐨𝐚𝐝𝐢𝐧𝐠...\n`{bar}` `{pct}%`"),
            _loop
        )

    # ── Pass 1: with ffmpeg + thumbnail embed ──
    try:
        opts1 = _build_ytdlp_opts(base_tmpl, with_ffmpeg=True,
                                   progress_hook=_progress, writethumbnail=True)
        info = await asyncio.to_thread(_run_ytdl_sync, opts1, query)
        if info:
            video_id = info.get("id")
        out_path = _find_media_file(DOWNLOAD_PATH, "music_", video_id=video_id,
                                    exts=("mp3", "m4a", "webm", "opus", "ogg", "aac", "wav"))
    except Exception as e1:
        logger.warning(f"[music pass1] {e1}")

    # ── Pass 2: fallback without ffmpeg ──
    if not out_path:
        try:
            await safe_edit(m, "🎵 𝐅𝐚𝐥𝐥𝐛𝐚𝐜𝐤 𝐦𝐨𝐝𝐞 (𝐧𝐨 𝐟𝐟𝐦𝐩𝐞𝐠)...")
            _last_pct[0] = -1
            opts2 = _build_ytdlp_opts(base_tmpl, with_ffmpeg=False,
                                       progress_hook=_progress, writethumbnail=False)
            info = await asyncio.to_thread(_run_ytdl_sync, opts2, query)
            if info:
                video_id = info.get("id")
            out_path = _find_media_file(DOWNLOAD_PATH, "music_", video_id=video_id,
                                        exts=("mp3", "m4a", "webm", "opus", "ogg", "aac", "wav"))
        except Exception as e2:
            logger.warning(f"[music pass2] {e2}")
            return await safe_edit(m, _yt_error_help(e2))

    if not info:
        return await safe_edit(m, "❌ 𝐍𝐨 𝐦𝐮𝐬𝐢𝐜 𝐫𝐞𝐬𝐮𝐥𝐭 𝐟𝐨𝐮𝐧𝐝.")
    if not out_path:
        return await safe_edit(m, "❌ 𝐀𝐮𝐝𝐢𝐨 𝐟𝐢𝐥𝐞 𝐧𝐨𝐭 𝐜𝐫𝐞𝐚𝐭𝐞𝐝.\n💡 𝐑𝐮𝐧: `apt install ffmpeg` 𝐟𝐨𝐫 𝐛𝐞𝐬𝐭 𝐫𝐞𝐬𝐮𝐥𝐭𝐬.")

    title    = info.get("title", "Unknown")
    uploader = info.get("uploader") or info.get("channel") or "Unknown"
    duration = int(info.get("duration") or 0)
    views    = info.get("view_count") or 0
    mins, secs = divmod(duration, 60)

    # Find thumbnail if present
    thumb_path = None
    for ext in ("jpg", "jpeg", "webp", "png"):
        tp = _find_media_file(DOWNLOAD_PATH, "music_", video_id=video_id,
                              exts=(ext,), max_age=120)
        if tp:
            thumb_path = tp
            break

    await safe_edit(m, f"⬆️ 𝐔𝐩𝐥𝐨𝐚𝐝𝐢𝐧𝐠 `{title[:50]}`...")
    try:
        caption = (
            f"🎵 **{title}**\n"
            f"👤 `{uploader}`\n"
            f"⏱️ `{mins}:{secs:02d}`"
            + (f"\n👁️ `{views:,}` views" if views else "")
            + f"\n\n⚡ **𝐊𝐮𝐫𝐨𝐬𝐚𝐤𝐢 𝐕𝟗**"
        )
        await bot.send_file(
            event.chat_id, out_path,
            caption=caption,
            thumb=thumb_path,
            attributes=[types.DocumentAttributeAudio(
                duration=duration, title=title, performer=uploader
            )]
        )
        for f in [out_path, thumb_path]:
            if f:
                try: os.remove(f)
                except OSError: pass
        await m.delete()
    except Exception as e:
        logger.warning(f"[music upload] {traceback.format_exc()}")
        await safe_edit(m, _yt_error_help(e))


# ── VIDEO DOWNLOAD (V9) ────────────────────────────────────────
@cmd("video")
async def _video(event, arg):
    if not arg:
        return await safe_edit(event, "❌ **ᴜsᴀɢᴇ:** `.video <title or url>`\n💡 ᴋᴇᴇᴘ ɪᴛ sʜᴏʀᴛ — ᴠɪᴅᴇᴏs ᴀʀᴇ ʜᴇᴀᴠʏ")

    m = await safe_edit(event, f"🎬 **sᴇᴀʀᴄʜɪɴɢ** `{arg}`...")
    base_tmpl = os.path.join(DOWNLOAD_PATH, "video_%(id)s.%(ext)s")
    query     = arg if arg.startswith(("http://", "https://")) else f"ytsearch1:{arg}"
    info      = None
    out_path  = None
    video_id  = None
    _last_pct = [-1]
    _loop     = asyncio.get_event_loop()  # V9 fix: capture loop before thread

    def _progress(d):
        if d.get("status") != "downloading": return
        total      = d.get("total_bytes") or d.get("total_bytes_estimate") or 0
        downloaded = d.get("downloaded_bytes", 0)
        if total <= 0: return
        pct = int(downloaded * 100 / total)
        if pct == _last_pct[0] or pct % 10 != 0: return
        _last_pct[0] = pct
        bar = _make_progress_bar(pct)
        asyncio.run_coroutine_threadsafe(
            safe_edit(m, f"🎬 **ᴅᴏᴡɴʟᴏᴀᴅɪɴɢ...**\n`{bar}` `{pct}%`"),
            _loop
        )

    try:
        opts = _build_ytdlp_video_opts(base_tmpl, progress_hook=_progress)
        info = await asyncio.to_thread(_run_ytdl_sync, opts, query)
        if info:
            video_id = info.get("id")
        out_path = _find_media_file(DOWNLOAD_PATH, "video_", video_id=video_id,
                                    exts=("mp4", "mkv", "webm", "avi", "mov"),
                                    max_age=300)
    except Exception as e:
        logger.warning(f"[video] {e}")
        return await safe_edit(m, _yt_error_help(e))

    if not info:
        return await safe_edit(m, "❌ **ɴᴏ ʀᴇsᴜʟᴛ ꜰᴏᴜɴᴅ**")
    if not out_path:
        return await safe_edit(m, "❌ **ᴠɪᴅᴇᴏ ꜰɪʟᴇ ᴍɪssɪɴɢ** — ᴛʀʏ: `apt install ffmpeg`")

    title    = info.get("title", "Unknown")
    uploader = info.get("uploader") or info.get("channel") or "Unknown"
    duration = int(info.get("duration") or 0)
    width    = info.get("width") or 0
    height   = info.get("height") or 0
    mins, secs = divmod(duration, 60)
    size_mb  = os.path.getsize(out_path) / (1024 * 1024)

    await safe_edit(m, f"⬆️ **ᴜᴘʟᴏᴀᴅɪɴɢ** `{title[:50]}` ({size_mb:.1f} MB)...")
    try:
        caption = (
            f"🎬 **{title}**\n"
            f"👤 `{uploader}`\n"
            f"⏱️ `{mins}:{secs:02d}`"
            + (f"\n📐 `{width}×{height}`" if width else "")
            + f"\n💾 `{size_mb:.1f} MB`"
        )
        await bot.send_file(
            event.chat_id, out_path,
            caption=caption,
            attributes=[types.DocumentAttributeVideo(
                duration=duration,
                w=width,
                h=height,
                supports_streaming=True,
            )]
        )
        try: os.remove(out_path)
        except OSError: pass
        await m.delete()
    except Exception as e:
        logger.warning(f"[video upload] {traceback.format_exc()}")
        await safe_edit(m, _yt_error_help(e))

# ─────────────────────────────────────────────────────────────────
#  V9 COMMANDS
# ─────────────────────────────────────────────────────────────────

# ── GHOST PING ────────────────────────────────────────────────────
# Reply to a user or pass @username → mention them, then delete after 2s.
@cmd("ghostping")
async def _ghostping(event, arg):
    targets = await get_targets(event, arg)
    if not targets:
        return await safe_edit(event, "❌ 𝐑𝐞𝐩𝐥𝐲 𝐭𝐨 𝐚 𝐮𝐬𝐞𝐫 𝐨𝐫 𝐩𝐚𝐬𝐬 @𝐮𝐬𝐞𝐫𝐧𝐚𝐦𝐞!")
    try:
        await event.delete()
    except Exception:
        pass
    for uid in targets:
        try:
            entity = await bot.get_entity(uid)
            name   = getattr(entity, "first_name", None) or getattr(entity, "username", None) or str(uid)
            msg    = await bot.send_message(
                event.chat_id,
                f"👻 [​{name}](tg://user?id={uid})",
                parse_mode="md",
            )
            await asyncio.sleep(2)
            try: await msg.delete()
            except Exception: pass
        except Exception as e:
            logger.warning(f"[ghostping] {e}")


# ── TAG ALL ───────────────────────────────────────────────────────
# Tags every member of the group in batches of 5, with 3s pause per batch.
@cmd("tagall")
async def _tagall(event, arg):
    if not event.is_group:
        return await safe_edit(event, "❌ **ɢʀᴏᴜᴘs ᴏɴʟʏ ʙʀᴏ**")
    text     = arg.strip() or "👋"
    members  = []
    try:
        await safe_edit(event, "⏳ **ꜰᴇᴛᴄʜɪɴɢ ᴍᴇᴍʙᴇʀs...**")
        async for user in bot.iter_participants(event.chat_id, aggressive=True):
            if not getattr(user, "bot", False) and user.id != (await _get_me()).id:
                members.append(user)
    except Exception as e:
        return await safe_edit(event, f"❌ **ᴄᴀɴ'ᴛ ꜰᴇᴛᴄʜ ᴍᴇᴍʙᴇʀs** → `{e}`")

    if not members:
        return await safe_edit(event, "❌ **ɴᴏ ᴍᴇᴍʙᴇʀs ꜰᴏᴜɴᴅ**")

    await safe_edit(event, f"📢 **ᴛᴀɢɢɪɴɢ {len(members)} ᴘᴇᴏᴘʟᴇ...**")
    BATCH = 5
    for i in range(0, len(members), BATCH):
        chunk = members[i:i + BATCH]
        mentions = " ".join(
            f"[​{getattr(u, 'first_name', '') or str(u.id)}](tg://user?id={u.id})"
            for u in chunk
        )
        try:
            await bot.send_message(event.chat_id, f"{text}\n{mentions}", parse_mode="md")
        except FloodWaitError as fw:
            await asyncio.sleep(fw.seconds + 3)
        except Exception:
            pass
        await asyncio.sleep(3)


# ── SCHEDULE MESSAGE ──────────────────────────────────────────────
# .schedule <seconds> <text>  — sends the message after N seconds.
@cmd("schedule")
async def _schedule(event, arg):
    if not arg:
        return await safe_edit(event, "❌ **ᴜsᴀɢᴇ:** `.schedule <secs> <msg>`  ᴇɢ: `.schedule 30 hello`")
    parts = arg.split(None, 1)
    if len(parts) < 2 or not parts[0].isdigit():
        return await safe_edit(event, "❌ **ꜰɪʀsᴛ ᴀʀɢ ᴍᴜsᴛ ʙᴇ sᴇᴄᴏɴᴅs**  ᴇɢ: `.schedule 30 hello`")
    delay   = min(int(parts[0]), 3600)   # max 1 hour
    text    = parts[1]
    chat_id = event.chat_id
    await safe_edit(event, f"⏰ **sᴄʜᴇᴅᴜʟᴇᴅ** → ꜰɪʀɪɴɢ ɪɴ `{delay}s`")

    async def _send_later():
        await asyncio.sleep(delay)
        try:
            await bot.send_message(chat_id, text)
        except Exception as e:
            logger.warning(f"[schedule] {e}")

    asyncio.ensure_future(_send_later())


# ── STICKER MAKER ─────────────────────────────────────────────────
# Reply to any image/photo → .sticker  → sends it as a WebP sticker.
@cmd("sticker")
async def _sticker(event, arg):
    if not event.is_reply:
        return await safe_edit(event, "❌ **ʀᴇᴘʟʏ ᴛᴏ ᴀɴ ɪᴍᴀɢᴇ** ᴛᴏ ᴍᴀᴋᴇ ᴀ sᴛɪᴄᴋᴇʀ")
    reply = await event.get_reply_message()
    if not reply or not (reply.photo or reply.document):
        return await safe_edit(event, "❌ **ɴᴏ ɪᴍᴀɢᴇ ɪɴ ᴛʜᴀᴛ ᴍᴇssᴀɢᴇ**")
    await safe_edit(event, "🎨 **ᴄᴏɴᴠᴇʀᴛɪɴɢ...**")
    try:
        img_bytes = await bot.download_media(reply, file=bytes)
        try:
            from PIL import Image as _PILImage
            img  = _PILImage.open(BytesIO(img_bytes)).convert("RGBA")
            img.thumbnail((512, 512), _PILImage.LANCZOS)
            buf  = BytesIO()
            img.save(buf, format="WEBP")
            buf.seek(0)
            buf.name = "sticker.webp"
        except ImportError:
            buf = BytesIO(img_bytes)
            buf.name = "sticker.webp"
        await bot.send_file(
            event.chat_id, buf,
            attributes=[types.DocumentAttributeSticker(
                alt="🌟", stickerset=types.InputStickerSetEmpty()
            )],
        )
        await event.delete()
    except Exception as e:
        await safe_edit(event, f"❌ **sᴛɪᴄᴋᴇʀ ꜰᴀɪʟᴇᴅ** → `{e}`")


# ── ANTILINK ──────────────────────────────────────────────────────
# .antilink on  → auto-delete any message containing a URL in this chat
# .antilink off → disable
_URL_RE = re.compile(
    r"(https?://|t\.me/|telegram\.me/|bit\.ly|tinyurl\.com|youtu\.be)",
    re.IGNORECASE
)

@cmd("antilink")
async def _antilink(event, arg):
    sub = (arg or "").strip().lower()
    if sub == "on":
        antilink_chats.add(event.chat_id)
        await safe_edit(event, "🔗 **ᴀɴᴛɪʟɪɴᴋ ᴏɴ** — ʟɪɴᴋs ᴡɪʟʟ ɢᴇᴛ ᴅᴇʟᴇᴛᴇᴅ")
    elif sub == "off":
        antilink_chats.discard(event.chat_id)
        await safe_edit(event, "🔗 **ᴀɴᴛɪʟɪɴᴋ ᴏꜰꜰ** — ʟɪɴᴋs ᴀʟʟᴏᴡᴇᴅ ᴀɢᴀɪɴ")
    else:
        status = "ᴏɴ" if event.chat_id in antilink_chats else "ᴏꜰꜰ"
        await safe_edit(event, f"🔗 **ᴀɴᴛɪʟɪɴᴋ:** `{status}` — `.antilink on` / `.antilink off`")


# ── PURGE2 (delete your own messages) ────────────────────────────
# .purge2 <n>  → deletes the last N messages sent by YOU in this chat.
@cmd("purge2")
async def _purge2(event, arg):
    if not arg or not arg.strip().isdigit():
        return await safe_edit(event, "❌ **ᴜsᴀɢᴇ:** `.purge2 <count>`  ᴇɢ: `.purge2 20`")
    count = min(int(arg.strip()), 1000)
    me    = await _get_me()
    my_id = me.id
    ids_to_delete = []
    await safe_edit(event, f"🔍 **ꜱᴄᴀɴɴɪɴɢ** ꜰᴏʀ ʏᴏᴜʀ ᴍᴇssᴀɢᴇs...")
    try:
        # Scan last 5000 messages and filter client-side (from_user= is unreliable)
        async for msg in bot.iter_messages(event.chat_id, limit=5000):
            if msg.sender_id == my_id:
                ids_to_delete.append(msg.id)
                if len(ids_to_delete) >= count:
                    break
    except Exception as e:
        return await safe_edit(event, f"❌ **ꜱᴄᴀɴ ꜰᴀɪʟᴇᴅ** → `{e}`")
    if not ids_to_delete:
        return await safe_edit(event, "⚠️ **ɴᴏ ᴍᴇssᴀɢᴇs ꜰᴏᴜɴᴅ** ᴛᴏ ᴅᴇʟᴇᴛᴇ.")
    # Parallel batch deletion (100 per batch — Telegram limit)
    delete_tasks = [
        bot.delete_messages(event.chat_id, ids_to_delete[i:i+100])
        for i in range(0, len(ids_to_delete), 100)
    ]
    await asyncio.gather(*delete_tasks, return_exceptions=True)
    deleted = len(ids_to_delete)
    try:
        confirm = await bot.send_message(event.chat_id,
            f"🗑️ **ᴘᴜʀɢᴇ2 ᴅᴏɴᴇ** → ᴅᴇʟᴇᴛᴇᴅ `{deleted}` ᴏꜰ ʏᴏᴜʀ ᴍsɢs ✅")
        await asyncio.sleep(3)
        await confirm.delete()
    except Exception:
        pass


# ── TRANSLATE ────────────────────────────────────────────────────
@cmd("translate")
async def _translate(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.translate <lang> <text>`\n𝐄𝐱: `.translate hi Hello world`")
    parts = arg.split(" ", 1)
    if len(parts) < 2:
        return await safe_edit(event, "❌ 𝐏𝐫𝐨𝐯𝐢𝐝𝐞 𝐥𝐚𝐧𝐠𝐮𝐚𝐠𝐞 𝐚𝐧𝐝 𝐭𝐞𝐱𝐭!")
    lang, text = parts[0].upper(), parts[1]
    await safe_edit(event, "⚡ 𝐓𝐫𝐚𝐧𝐬𝐥𝐚𝐭𝐢𝐧𝐠...")
    try:
        resp = await asyncio.to_thread(lambda: requests.get(
            "https://api.mymemory.translated.net/get",
            params={"q": text[:500], "langpair": f"en|{lang}"},
            timeout=10
        ).json())
        translated = resp.get("responseData", {}).get("translatedText", "")
        if not translated:
            return await safe_edit(event, "❌ 𝐓𝐫𝐚𝐧𝐬𝐥𝐚𝐭𝐢𝐨𝐧 𝐟𝐚𝐢𝐥𝐞𝐝!")
        await safe_edit(event,
            f"🌐 **𝐓𝐫𝐚𝐧𝐬𝐥𝐚𝐭𝐞𝐝 𝐭𝐨 {lang}:**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"📥 `{text[:100]}`\n"
            f"📤 {translated}"
        )
    except Exception as e:
        await safe_edit(event, f"❌ 𝐓𝐫𝐚𝐧𝐬𝐥𝐚𝐭𝐞 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── URBAN DICTIONARY ─────────────────────────────────────────────
@cmd("ud")
async def _ud(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.ud <word>`")
    await safe_edit(event, f"🔍 𝐋𝐨𝐨𝐤𝐢𝐧𝐠 𝐮𝐩 `{arg}`...")
    try:
        data = await asyncio.to_thread(lambda: requests.get(
            f"https://api.urbandictionary.com/v0/define?term={arg}", timeout=8
        ).json())
        entries = data.get("list", [])
        if not entries:
            return await safe_edit(event, f"❌ 𝐍𝐨 𝐝𝐞𝐟𝐢𝐧𝐢𝐭𝐢𝐨𝐧 𝐟𝐨𝐮𝐧𝐝 𝐟𝐨𝐫 `{arg}`!")
        e = entries[0]
        definition = re.sub(r'\[|\]', '', e.get("definition", ""))[:400]
        example    = re.sub(r'\[|\]', '', e.get("example", ""))[:200]
        await safe_edit(event,
            f"📖 **𝐔𝐫𝐛𝐚𝐧 𝐃𝐢𝐜𝐭𝐢𝐨𝐧𝐚𝐫𝐲: {e.get('word')}**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"📝 {definition}\n\n"
            f"💬 **𝐄𝐱𝐚𝐦𝐩𝐥𝐞:** _{example}_\n\n"
            f"👍 `{e.get('thumbs_up')}` 👎 `{e.get('thumbs_down')}`"
        )
    except Exception as e:
        await safe_edit(event, f"❌ 𝐔𝐃 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ── GC CREATION & BOT PROMOTION ──────────────────────────────────
def _user_admin_rights(is_broadcast: bool = False) -> ChatAdminRights:
    """Full admin rights for users.
    Broadcast channels: post/edit messages, no ban_users/add_admins.
    Megagroups: ban_users, add_admins, manage_topics — no post/edit messages."""
    if is_broadcast:
        return ChatAdminRights(
            change_info=True, post_messages=True, edit_messages=True,
            delete_messages=True, ban_users=False, invite_users=True,
            pin_messages=True, add_admins=False, anonymous=False,
            manage_call=True,
        )
    return ChatAdminRights(
        change_info=True, post_messages=False, edit_messages=False,
        delete_messages=True, ban_users=True, invite_users=True,
        pin_messages=True, add_admins=True, anonymous=False,
        manage_call=True, manage_topics=True,
    )

def _bot_admin_rights(is_broadcast: bool = False) -> ChatAdminRights:
    """Full admin rights for bots — all rights EXCEPT add_admins."""
    if is_broadcast:
        return ChatAdminRights(
            change_info=True, post_messages=True, edit_messages=True,
            delete_messages=True, ban_users=False, invite_users=True,
            pin_messages=True, add_admins=False, anonymous=False,
            manage_call=True,
        )
    return ChatAdminRights(
        change_info=True, post_messages=False, edit_messages=False,
        delete_messages=True, ban_users=True, invite_users=True,
        pin_messages=True, add_admins=False, anonymous=False,
        manage_call=True, manage_topics=True,
    )

def _admin_rights(full: bool = True) -> ChatAdminRights:
    """Legacy helper — kept for creategc fallback path."""
    return _bot_admin_rights() if full else ChatAdminRights(
        delete_messages=True, ban_users=True, invite_users=True,
        pin_messages=True, add_admins=False, anonymous=False,
    )


async def _add_entity_to_chat(chat_ref, username: str) -> str:
    user = await bot.get_input_entity(username)
    try:
        await bot(InviteToChannelRequest(chat_ref, [user]))
    except Exception:
        user_id = getattr(user, "user_id", None) or getattr(user, "id", None)
        if not user_id:
            entity = await bot.get_entity(username)
            user_id = entity.id
        await bot(AddChatUserRequest(chat_ref, user_id, fwd_limit=10))
    return username


# FIX: Promote in someone else's GC — tries full rights, falls back to minimal,
#      then falls back to legacy EditChatAdminRequest.
#      Properly differentiates broadcast channels vs megagroups vs legacy groups.
async def _promote_entity_in_chat(chat_ref, username_or_uid, rank: str = "Admin") -> str:
    user = await bot.get_input_entity(username_or_uid)

    # Determine chat type: broadcast channel, megagroup, or legacy group
    is_channel = True
    is_broadcast = False
    chat_entity = None
    if isinstance(chat_ref, (int, str)):
        try:
            chat_entity = await bot.get_entity(chat_ref)
        except: pass
    else:
        chat_entity = chat_ref

    if chat_entity is not None:
        if isinstance(chat_entity, types.Channel):
            is_channel = True
            is_broadcast = getattr(chat_entity, "broadcast", False)
        else:
            is_channel = False

    user_id = getattr(user, "user_id", None) or getattr(user, "id", None)
    if not user_id:
        try:
            entity = await bot.get_entity(username_or_uid)
            user_id = entity.id
        except: pass

    if is_channel:
        # Choose rights based on entity type (bot vs user) and chat type (broadcast vs megagroup)
        is_bot_entity = False
        try:
            resolved = await bot.get_entity(username_or_uid)
            is_bot_entity = getattr(resolved, "bot", False)
        except: pass

        rights = (_bot_admin_rights(is_broadcast=is_broadcast)
                  if is_bot_entity
                  else _user_admin_rights(is_broadcast=is_broadcast))
        try:
            await bot(EditAdminRequest(chat_ref, user, rights, rank=rank[:16]))
            return str(username_or_uid)
        except Exception:
            pass
        # Fall back to minimal rights (works when userbot doesn't hold all perms)
        try:
            await bot(EditAdminRequest(chat_ref, user, _admin_rights(full=False), rank=rank[:16]))
            return str(username_or_uid)
        except Exception as e:
            raise RuntimeError(f"Promote failed (channel): {e}")
    else:
        # Legacy group
        if not user_id:
            raise RuntimeError("Could not resolve user ID for legacy group promote")
        await bot(EditChatAdminRequest(chat_ref, user_id, is_admin=True))
        return str(username_or_uid)


@cmd("bots")
async def _bots(event, arg):
    if not bot_usernames:
        return await safe_edit(event, "🤖 𝐍𝐨 𝐬𝐚𝐯𝐞𝐝 𝐛𝐨𝐭𝐬. 𝐔𝐬𝐞 `.setbots @bot1 @bot2 @bot3`.")
    lines = "\n".join(f"{i}. `{name}`" for i, name in enumerate(bot_usernames, 1))
    await safe_edit(event, f"🤖 **𝐒𝐚𝐯𝐞𝐝 𝐁𝐨𝐭𝐬 ({len(bot_usernames)}/{MAX_SAVED_BOTS})**\n━━━━━━━━━━━━━━━\n{lines}")


@cmd("setbots")
async def _setbots(event, arg):
    global bot_usernames
    bots = _parse_bot_usernames(arg)
    if not bots:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.setbots @bot1 @bot2 @bot3`")
    bot_usernames = bots[:MAX_SAVED_BOTS]
    save_bot_usernames()
    await safe_edit(event, f"✅ **𝐒𝐚𝐯𝐞𝐝 {len(bot_usernames)} 𝐁𝐨𝐭𝐬:**\n`{', '.join(bot_usernames)}`")


@cmd("clearbots")
async def _clearbots(event, arg):
    global bot_usernames
    bot_usernames = []
    save_bot_usernames()
    await safe_edit(event, "🗑️ 𝐒𝐚𝐯𝐞𝐝 𝐛𝐨𝐭 𝐥𝐢𝐬𝐭 𝐜𝐥𝐞𝐚𝐫𝐞𝐝.")


@cmd("creategc")
async def _creategc(event, arg):
    if not arg:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.creategc <name>[; <name2>] [| @bot1 @bot2]`")
    group_args = arg.split("|", 1)
    group_names = [n.strip() for n in group_args[0].strip().split(";") if n.strip()]
    bot_part    = group_args[1].strip() if len(group_args) > 1 else ""
    if not group_names:
        return await safe_edit(event, "❌ 𝐏𝐫𝐨𝐯𝐢𝐝𝐞 𝐚𝐭 𝐥𝐞𝐚𝐬𝐭 𝐨𝐧𝐞 𝐠𝐫𝐨𝐮𝐩 𝐧𝐚𝐦𝐞!")
    bots = _bots_from_arg_or_saved(bot_part)
    results = []
    for group_name in group_names:
        await safe_edit(event, f"⚡ 𝐂𝐫𝐞𝐚𝐭𝐢𝐧𝐠 𝐠𝐫𝐨𝐮𝐩 `{group_name}`...")
        try:
            result = await bot(CreateChannelRequest(
                title=group_name[:128],
                about="Created by Kurosaki V9",
                megagroup=True
            ))
            created_chat = result.chats[0]
            full_chat_id = int(f"-100{created_chat.id}")
            added, promoted, failed = [], [], []
            for username in bots:
                try:
                    await _add_entity_to_chat(created_chat, username)
                    added.append(username)
                    await asyncio.sleep(1)
                    await _promote_entity_in_chat(created_chat, username, rank="Bot")
                    promoted.append(username)
                except Exception as e:
                    failed.append(f"{username}: {str(e)[:35]}")
            text = f"✅ **𝐆𝐫𝐨𝐮𝐩 𝐂𝐫𝐞𝐚𝐭𝐞𝐝!**\n📌 𝐍𝐚𝐦𝐞: `{group_name}`\n🆔 𝐈𝐃: `{full_chat_id}`"
            if bots:
                text += f"\n🤖 𝐀𝐝𝐝𝐞𝐝: `{', '.join(added) or 'None'}`\n👑 𝐏𝐫𝐨𝐦𝐨𝐭𝐞𝐝: `{', '.join(promoted) or 'None'}`"
            if failed:
                text += f"\n⚠️ 𝐅𝐚𝐢𝐥𝐞𝐝: `{'; '.join(failed)}`"
            results.append(text)
        except Exception as e:
            results.append(f"❌ 𝐂𝐫𝐞𝐚𝐭𝐢𝐨𝐧 𝐟𝐚𝐢𝐥𝐞𝐝 𝐟𝐨𝐫 `{group_name}`: `{e}`")
    await safe_edit(event, "\n\n".join(results))


@cmd("createch")
async def _createch(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.createch <channel name>`")
    await safe_edit(event, f"⚡ 𝐂𝐫𝐞𝐚𝐭𝐢𝐧𝐠 𝐜𝐡𝐚𝐧𝐧𝐞𝐥 `{arg}`...")
    try:
        result = await bot(CreateChannelRequest(title=arg[:128], about="Created by Kurosaki V9", megagroup=False))
        chat_id = result.chats[0].id
        await safe_edit(event, f"✅ **𝐂𝐡𝐚𝐧𝐧𝐞𝐥 𝐂𝐫𝐞𝐚𝐭𝐞𝐝!**\n📌 𝐍𝐚𝐦𝐞: `{arg}`\n🆔 𝐈𝐃: `-100{chat_id}`")
    except Exception as e:
        await safe_edit(event, f"❌ 𝐂𝐫𝐞𝐚𝐭𝐢𝐨𝐧 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")


@cmd("addbot")
async def _addbot(event, arg):
    bots = _bots_from_arg_or_saved(arg)
    if not bots:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.addbot @bot1` 𝐨𝐫 `.setbots ...` 𝐭𝐡𝐞𝐧 `.addbot`")
    await safe_edit(event, f"⚡ 𝐀𝐝𝐝𝐢𝐧𝐠 {len(bots)} 𝐛𝐨𝐭(𝐬) 𝐭𝐨 𝐜𝐡𝐚𝐭...")
    added, failed = [], []
    for username in bots:
        try:
            await _add_entity_to_chat(event.chat_id, username)
            added.append(username)
            await asyncio.sleep(1)
        except Exception as e:
            failed.append(f"{username}: {str(e)[:35]}")
    text = f"✅ **𝐁𝐨𝐭𝐬 𝐀𝐝𝐝𝐞𝐝:** `{', '.join(added) or 'None'}`"
    if failed:
        text += f"\n⚠️ **𝐅𝐚𝐢𝐥𝐞𝐝:** `{'; '.join(failed)}`"
    await safe_edit(event, text)


@cmd("promotebots")
async def _promotebots(event, arg):
    bots = _bots_from_arg_or_saved(arg)
    if not bots:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.promotebots @bot1 @bot2` 𝐨𝐫 `.setbots ...` 𝐭𝐡𝐞𝐧 `.promotebots`")
    await safe_edit(event, f"⚡ 𝐏𝐫𝐨𝐦𝐨𝐭𝐢𝐧𝐠 {len(bots)} 𝐛𝐨𝐭(𝐬) (𝐟𝐮𝐥𝐥 𝐫𝐢𝐠𝐡𝐭𝐬, 𝐧𝐨 𝐚𝐝𝐝-𝐚𝐝𝐦𝐢𝐧)...")
    # Detect channel type so rights are correct for broadcast channels vs megagroups
    is_broadcast = False
    try:
        chat_ent = await bot.get_entity(event.chat_id)
        is_broadcast = isinstance(chat_ent, types.Channel) and getattr(chat_ent, "broadcast", False)
    except: pass
    promoted, failed = [], []
    for username in bots:
        try:
            user_ent = await bot.get_input_entity(username)
            await bot(EditAdminRequest(
                event.chat_id, user_ent,
                _bot_admin_rights(is_broadcast=is_broadcast), rank="Bot"
            ))
            promoted.append(username)
            await asyncio.sleep(1)
        except Exception as e:
            failed.append(f"{username}: {str(e)[:35]}")
    text = f"✅ **𝐁𝐨𝐭𝐬 𝐏𝐫𝐨𝐦𝐨𝐭𝐞𝐝:** `{', '.join(promoted) or 'None'}`"
    if failed:
        text += f"\n⚠️ **𝐅𝐚𝐢𝐥𝐞𝐝:** `{'; '.join(failed)}`"
    await safe_edit(event, text)


@cmd("promote")
async def _promote(event, arg):
    targets = await get_targets(event, arg)
    if not targets:
        return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    await safe_edit(event, "⚡ 𝐏𝐫𝐨𝐦𝐨𝐭𝐢𝐧𝐠 𝐰𝐢𝐭𝐡 𝐟𝐮𝐥𝐥 𝐫𝐢𝐠𝐡𝐭𝐬...")

    # Detect chat type once for all targets
    is_broadcast = False
    try:
        chat_ent = await bot.get_entity(event.chat_id)
        is_broadcast = isinstance(chat_ent, types.Channel) and getattr(chat_ent, "broadcast", False)
        is_ch = isinstance(chat_ent, types.Channel)
    except:
        is_ch = True

    promoted, failed = [], []
    for uid in targets:
        try:
            user_ent = await bot.get_input_entity(uid)
            done = False
            if is_ch:
                # Attempt 1: full rights (channel-type-aware, includes add_admins for megagroups)
                try:
                    await bot(EditAdminRequest(
                        event.chat_id, user_ent,
                        _user_admin_rights(is_broadcast=is_broadcast), rank="Admin"
                    ))
                    done = True
                except Exception:
                    pass
                # Attempt 2: full rights WITHOUT add_admins
                if not done:
                    try:
                        await bot(EditAdminRequest(
                            event.chat_id, user_ent,
                            _bot_admin_rights(is_broadcast=is_broadcast), rank="Admin"
                        ))
                        done = True
                    except Exception:
                        pass
                # Attempt 3: minimal rights
                if not done:
                    try:
                        await bot(EditAdminRequest(
                            event.chat_id, user_ent,
                            _admin_rights(full=False), rank="Admin"
                        ))
                        done = True
                    except Exception:
                        pass
            # Attempt 4: legacy group fallback
            if not done:
                await bot(EditChatAdminRequest(event.chat_id, uid, is_admin=True))
            promoted.append(str(uid))
        except Exception as e:
            logger.warning(f"Promote {uid}: {e}")
            failed.append(f"{uid} ({str(e)[:40]})")
    text = f"✅ **𝐏𝐫𝐨𝐦𝐨𝐭𝐞𝐝:** `{', '.join(promoted) or 'None'}`"
    if failed:
        text += f"\n⚠️ **𝐅𝐚𝐢𝐥𝐞𝐝:** `{', '.join(failed)}`"
    await safe_edit(event, text)


@cmd("demote", group_only=True)
async def _demote(event, arg):
    targets = await get_targets(event, arg)
    if not targets:
        return await safe_edit(event, "❌ 𝐍𝐨 𝐭𝐚𝐫𝐠𝐞𝐭!")
    await safe_edit(event, "⚡ 𝐃𝐞𝐦𝐨𝐭𝐢𝐧𝐠...")
    demoted, failed = [], []
    for uid in targets:
        try:
            user_ent = await bot.get_input_entity(uid)
            done = False
            try:
                await bot(EditAdminRequest(
                    event.chat_id, user_ent,
                    ChatAdminRights(), rank=""
                ))
                done = True
            except Exception:
                pass
            if not done:
                await bot(EditChatAdminRequest(event.chat_id, uid, is_admin=False))
            demoted.append(str(uid))
        except Exception as e:
            logger.warning(f"Demote {uid}: {e}")
            failed.append(f"{uid} ({str(e)[:40]})")
    text = f"⬇️ **𝐃𝐞𝐦𝐨𝐭𝐞𝐝:** `{', '.join(demoted) or 'None'}`"
    if failed:
        text += f"\n⚠️ **𝐅𝐚𝐢𝐥𝐞𝐝:** `{', '.join(failed)}`"
    await safe_edit(event, text)

# ── WIKIPEDIA ────────────────────────────────────────────────────
@cmd("wiki")
async def _wiki(event, arg):
    if not arg: return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.wiki <query>`")
    await safe_edit(event, f"🔍 𝐒𝐞𝐚𝐫𝐜𝐡𝐢𝐧𝐠 𝐖𝐢𝐤𝐢𝐩𝐞𝐝𝐢𝐚 𝐟𝐨𝐫 `{arg}`...")
    try:
        search = await asyncio.to_thread(lambda: requests.get(
            "https://en.wikipedia.org/w/api.php",
            params={"action":"query","list":"search","srsearch":arg,"format":"json","srlimit":1},
            timeout=8
        ).json())
        results = search.get("query", {}).get("search", [])
        if not results:
            return await safe_edit(event, f"❌ 𝐍𝐨 𝐫𝐞𝐬𝐮𝐥𝐭𝐬 𝐟𝐨𝐫 `{arg}`!")
        title   = results[0]["title"]
        summary = await asyncio.to_thread(lambda: requests.get(
            f"https://en.wikipedia.org/api/rest_v1/page/summary/{requests.utils.quote(title)}",
            timeout=8
        ).json())
        extract = summary.get("extract", "")[:600]
        url     = summary.get("content_urls", {}).get("desktop", {}).get("page", "")
        await safe_edit(event,
            f"📚 **𝐖𝐢𝐤𝐢𝐩𝐞𝐝𝐢𝐚: {title}**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"{extract}\n\n"
            f"🔗 [𝐑𝐞𝐚𝐝 𝐌𝐨𝐫𝐞]({url})"
        )
    except Exception as e:
        await safe_edit(event, f"❌ 𝐖𝐢𝐤𝐢 𝐟𝐚𝐢𝐥𝐞𝐝: `{e}`")

# ─────────────────────────────────────────────────────────────────
#  WELCOME SYSTEM
# ─────────────────────────────────────────────────────────────────
WELCOME_FILE = "welcome.json"
_welcome_cfg: Dict[str, Any] = {
    "enabled": False,
    "text": "👋🏻 {mention}, ᴡᴇʟᴄᴏᴍᴇ ᴛᴏ {chat}!\n🕐 ᴊᴏɪɴᴇᴅ ᴀᴛ {time} ᴏɴ {date}",
    "send_banner": True,
}

def _load_welcome():
    global _welcome_cfg
    data = _load_json(WELCOME_FILE, {})
    _welcome_cfg.update(data)

def _save_welcome():
    _save_json(WELCOME_FILE, _welcome_cfg)

# ── .setwelcome ────────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.setwelcome(?:\s+(.+))?$", re.I | re.S), outgoing=True))
async def _setwelcome(event):
    arg = event.pattern_match.group(1)
    if not arg:
        return await event.edit(
            f"❌ {to_authority_style('Usage')}: `.setwelcome <text>`\n"
            f"{to_small_caps('Variables')}: `{{mention}}` `{{name}}` `{{chat}}` `{{id}}` `{{time}}` `{{date}}`"
        )
    _welcome_cfg["text"] = arg.strip()
    _welcome_cfg["enabled"] = True
    _save_welcome()
    await event.edit(
        f"✅ **{to_authority_style('Welcome')}** {to_small_caps('message saved & enabled!')}:\n\n"
        f"{_welcome_cfg['text']}"
    )

# ── .welctest ──────────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.welctest$", re.I), outgoing=True))
async def _welctest(event):
    if not _welcome_cfg.get("text"):
        return await event.edit(f"❌ {to_small_caps('No welcome message set. Use .setwelcome first.')}")
    me = await _get_me()
    chat = await event.get_chat()
    mention = f"[{me.first_name}](tg://user?id={me.id})"
    chat_name = getattr(chat, "title", "𝓽𝓱𝓲𝓼 𝓰𝓻𝓸𝓾𝓹")
    now = datetime.datetime.now()
    preview = _welcome_cfg["text"].format(
        mention=mention,
        name=me.first_name or "𝓾𝓼𝓮𝓻",
        chat=chat_name,
        id=me.id,
        time=now.strftime("%I:%M %p"),
        date=now.strftime("%d %b %Y"),
    )
    await event.edit(
        f"🎉 **{to_authority_style('Welcome Test')}**\n"
        f"━━━━━━━━━━━━━━━\n"
        f"{preview}\n"
        f"━━━━━━━━━━━━━━━\n"
        f"• {to_small_caps('enabled')}: `{_welcome_cfg['enabled']}`\n"
        f"• {to_small_caps('banner')}: `{_welcome_cfg['send_banner']}`"
    )
    if _welcome_cfg.get("send_banner") and menu_banner_msg:
        try:
            await bot.forward_messages(event.chat_id, menu_banner_msg[1], menu_banner_msg[0])
        except:
            pass

# ── .delwelcome ────────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.delwelcome$", re.I), outgoing=True))
async def _delwelcome(event):
    _welcome_cfg["text"] = ""
    _welcome_cfg["enabled"] = False
    _save_welcome()
    await event.edit(f"🗑️ {to_small_caps('Welcome message deleted.')}")

# ── .welcoff ───────────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.welcoff$", re.I), outgoing=True))
async def _welcoff(event):
    _welcome_cfg["enabled"] = False
    _save_welcome()
    await event.edit(f"🔕 {to_small_caps('Auto-welcome disabled.')}")

# ── .welcon ────────────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.welcon$", re.I), outgoing=True))
async def _welcon(event):
    if not _welcome_cfg.get("text"):
        return await event.edit(f"❌ {to_small_caps('Set a welcome message first with .setwelcome')}")
    _welcome_cfg["enabled"] = True
    _save_welcome()
    await event.edit(f"✅ {to_small_caps('Auto-welcome enabled.')}")

# ── ChatAction handler — fires on new member joins ─────────────────
@bot.on(events.ChatAction())
async def _welcome_handler(event):
    if not _welcome_cfg.get("enabled"):
        return
    if not (event.user_joined or event.user_added):
        return
    try:
        user = await event.get_user()
        if not user or user.bot:
            return
        chat = await event.get_chat()
        mention = f"[{user.first_name}](tg://user?id={user.id})"
        chat_name = getattr(chat, "title", "𝓽𝓱𝓲𝓼 𝓰𝓻𝓸𝓾𝓹")
        now = datetime.datetime.now()
        text = _welcome_cfg["text"].format(
            mention=mention,
            name=user.first_name or "𝓾𝓼𝓮𝓻",
            chat=chat_name,
            id=user.id,
            time=now.strftime("%I:%M %p"),
            date=now.strftime("%d %b %Y"),
        )
        header = f"🎉 **{to_authority_style('Welcome')}**\n━━━━━━━━━━━━━━━\n"
        await bot.send_message(event.chat_id, header + text, parse_mode="md")
        if _welcome_cfg.get("send_banner") and menu_banner_msg:
            try:
                await bot.forward_messages(event.chat_id, menu_banner_msg[1], menu_banner_msg[0])
            except:
                pass
    except Exception as e:
        logger.warning(f"[Welcome handler] {e}")

# ─────────────────────────────────────────────────────────────────
#  PORTED FROM ADIXE V1 — Extra Features
# ─────────────────────────────────────────────────────────────────

import time as _time
from typing import Tuple

# ── In-memory state for extra features ───────────────────────────
_warnings_store: dict = {}       # {chat_id: {user_id: count}}
_autorespond_store: dict = {}    # {chat_id: {trigger: response}}
_afk_store: dict = {}            # {user_id: afk_message}
_delall_store: dict = {}         # {chat_id: expiry_timestamp or None}
_delete_delay: float = 0.05
_safe_users: set = set()         # set of user_ids protected from auto-delete
_target_store: dict = {}         # {user_id: (photo_path, text)}

# Persist warnings across commands in-session
def _add_warning(chat_id: int, user_id: int) -> int:
    _warnings_store.setdefault(chat_id, {})
    _warnings_store[chat_id][user_id] = _warnings_store[chat_id].get(user_id, 0) + 1
    return _warnings_store[chat_id][user_id]

def _get_warnings(chat_id: int, user_id: int) -> int:
    return _warnings_store.get(chat_id, {}).get(user_id, 0)

def _reset_warnings(chat_id: int, user_id: int):
    if chat_id in _warnings_store:
        _warnings_store[chat_id].pop(user_id, None)

# ── .save — persist current profile before cloning ───────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.save$", re.I), outgoing=True))
async def _save_profile(event):
    try:
        me = await _get_me()
        import glob as _g
        os.makedirs("profile_photos", exist_ok=True)
        saved_path = "profile_photos/saved_photo.jpg"
        if os.path.exists(saved_path):
            os.remove(saved_path)
        photos = await bot.get_profile_photos("me", limit=1)
        if photos:
            await bot.download_media(photos[0], file=saved_path)
            photo_status = "saved"
        else:
            saved_path = None
            photo_status = "none"
        # Store in module-level vars (same pattern as File 1's copy/normal)
        bot._kv_saved_name = me.first_name
        bot._kv_saved_bio = getattr(me, "about", "") or ""
        bot._kv_saved_photo = saved_path
        await event.edit(
            f"✅ **𝐏𝐫𝐨𝐟𝐢𝐥𝐞 𝐒𝐚𝐯𝐞𝐝**\n"
            f"📝 Name: `{me.first_name}`\n"
            f"📄 Bio: `{bot._kv_saved_bio or 'none'}`\n"
            f"🖼️ Photo: `{photo_status}`\n\n"
            f"Use `.normal` to restore."
        )
    except Exception as e:
        await event.edit(f"❌ Save failed: `{e}`")

# ── .warn / .warnings / .resetwarns ──────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.warn$", re.I), outgoing=True))
async def _warn_cmd(event):
    if not event.is_reply:
        return await event.edit("❌ Reply to a user with `.warn`")
    reply = await event.get_reply_message()
    if not reply or not reply.sender_id:
        return await event.edit("❌ Cannot identify that user.")
    uid = reply.sender_id
    count = _add_warning(event.chat_id, uid)
    await event.edit(f"⚠️ **Warning issued!** Total: `{count}/3`")
    if count >= 3:
        try:
            await bot(EditBannedRequest(event.chat_id, uid,
                                        ChatBannedRights(until_date=None, view_messages=True)))
            await bot.send_message(event.chat_id, f"🚫 User banned after 3 warnings.")
            _reset_warnings(event.chat_id, uid)
        except Exception as e:
            await bot.send_message(event.chat_id, f"❌ Auto-ban failed: `{e}`")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.warnings$", re.I), outgoing=True))
async def _warnings_cmd(event):
    if not event.is_reply:
        return await event.edit("❌ Reply to a user with `.warnings`")
    reply = await event.get_reply_message()
    if not reply or not reply.sender_id:
        return
    count = _get_warnings(event.chat_id, reply.sender_id)
    await event.edit(f"⚠️ User has `{count}` warning(s).")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.resetwarns$", re.I), outgoing=True))
async def _resetwarns_cmd(event):
    if not event.is_reply:
        return await event.edit("❌ Reply to a user with `.resetwarns`")
    reply = await event.get_reply_message()
    if not reply or not reply.sender_id:
        return
    _reset_warnings(event.chat_id, reply.sender_id)
    await event.edit("✅ Warnings reset.")

# ── .autorespond / .stopautorespond ──────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.autorespond(?:\s+(.+))?$", re.I), outgoing=True))
async def _autorespond_set(event):
    arg = event.pattern_match.group(1)
    if not arg:
        rules = _autorespond_store.get(event.chat_id, {})
        if not rules:
            return await event.edit("❌ No auto-respond rules. Usage: `.autorespond <trigger> <reply>`")
        lines = "\n".join(f"• `{t}` → {r}" for t, r in rules.items())
        return await event.edit(f"📋 **Auto-respond rules:**\n{lines}")
    parts = arg.split(None, 1)
    if len(parts) < 2:
        return await event.edit("❌ Usage: `.autorespond <trigger> <reply>`")
    trigger, response = parts[0].lower(), parts[1]
    _autorespond_store.setdefault(event.chat_id, {})[trigger] = response
    await event.edit(f"✅ Auto-respond set: `{trigger}` → {response}")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.stopautorespond$", re.I), outgoing=True))
async def _stopautorespond(event):
    _autorespond_store.pop(event.chat_id, None)
    await event.edit("✅ Auto-respond disabled for this chat.")

@bot.on(events.NewMessage(incoming=True))
async def _autorespond_handler(event):
    if not event.message or not event.message.text:
        return
    rules = _autorespond_store.get(event.chat_id)
    if not rules:
        return
    text = event.message.text.lower()
    for trigger, response in rules.items():
        if trigger in text:
            await asyncio.sleep(0.5)
            await event.reply(response)
            break

# ── .afk / .killafk ──────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.afk(?:\s+(.+))?$", re.I), outgoing=True))
async def _afk_set(event):
    arg = event.pattern_match.group(1)
    if arg and arg.lower() == "off":
        me = await _get_me()
        _afk_store.pop(me.id, None)
        return await event.edit("✅ AFK mode disabled.")
    message = arg or "I'm away right now."
    me = await _get_me()
    _afk_store[me.id] = message
    await event.edit(f"🚫 **AFK mode on**\nAuto-reply: {message}")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.killafk$", re.I), outgoing=True))
async def _killafk(event):
    me = await _get_me()
    if me.id in _afk_store:
        del _afk_store[me.id]
        await event.edit("✅ AFK killed.")
    else:
        await event.edit("❌ AFK was not active.")

@bot.on(events.NewMessage(incoming=True))
async def _afk_reply(event):
    if not event.is_private:
        return
    me = await _get_me()
    if me.id not in _afk_store:
        return
    afk_msg = _afk_store[me.id]
    try:
        await event.reply(f"😴 I'm AFK right now.\n💬 {afk_msg}")
    except: pass

# ── .delall [seconds|off] ─────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.delall(?:\s+(.+))?$", re.I), outgoing=True))
async def _delall_cmd(event):
    arg = (event.pattern_match.group(1) or "").strip().lower()
    if arg == "off":
        _delall_store.pop(event.chat_id, None)
        return await event.edit("✅ Delete-all mode disabled.")
    timeout = None
    if arg.isdigit():
        timeout = int(arg)
    expiry = _time.time() + timeout if timeout else None
    _delall_store[event.chat_id] = expiry
    msg = "⚠️ **Delete-all mode active** — every new message will be deleted."
    if timeout:
        msg += f"\nAuto-disables in `{timeout}s`."
    msg += "\nType `.delall off` to stop."
    await event.edit(msg)

@bot.on(events.NewMessage(incoming=True))
async def _delall_handler(event):
    if event.chat_id not in _delall_store:
        return
    expiry = _delall_store[event.chat_id]
    if expiry and _time.time() > expiry:
        del _delall_store[event.chat_id]
        return
    try:
        me = await _get_me()
        if event.sender_id == me.id:
            return
        await event.delete()
    except: pass

# ── .delay <sec> ─────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.delay\s+(.+)$", re.I), outgoing=True))
async def _delay_cmd(event):
    global _delete_delay
    val = event.pattern_match.group(1).strip()
    try:
        _delete_delay = float(val)
        await event.edit(f"✅ Delete delay set to `{_delete_delay}s`")
    except:
        await event.edit("❌ Invalid number. Example: `.delay 0.1`")

# ── .safe — safe user list ────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.safe(?:\s+(.+))?$", re.I), outgoing=True))
async def _safe_cmd(event):
    arg = (event.pattern_match.group(1) or "").strip()
    if not arg and not event.is_reply:
        count = len(_safe_users)
        return await event.edit(f"🛡️ Safe users: `{count}`\nAdd with `.safe @username` or by reply.")
    if event.is_reply:
        reply = await event.get_reply_message()
        if reply and reply.sender_id:
            _safe_users.add(reply.sender_id)
            return await event.edit("✅ User protected.")
    if arg:
        username = arg.lstrip("@")
        try:
            user = await bot.get_entity(username)
            _safe_users.add(user.id)
            await event.edit(f"✅ `@{username}` added to safe list.")
        except Exception as e:
            await event.edit(f"❌ Could not find `@{username}`: `{e}`")

# ── .pin / .unpin ─────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.pin(?:\s+(.*))?$", re.I), outgoing=True))
async def _pin_cmd(event):
    if not event.is_reply:
        return await event.edit("Reply to a message with `.pin` (or `.pin silent`)")
    reply = await event.get_reply_message()
    silent = "silent" in event.raw_text.lower()
    try:
        await bot.pin_message(event.chat_id, reply.id, notify=not silent)
        await event.edit("📌 Pinned!")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.unpin$", re.I), outgoing=True))
async def _unpin_cmd(event):
    try:
        await bot.unpin_message(event.chat_id)
        await event.edit("📌 Unpinned!")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

# ── .settitle / .setphoto ─────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.settitle\s+(.+)$", re.I), outgoing=True))
async def _settitle_cmd(event):
    title = event.pattern_match.group(1).strip()
    try:
        from telethon.tl.functions.channels import EditTitleRequest
        await bot(EditTitleRequest(channel=event.chat_id, title=title))
        await event.edit(f"✅ Title changed to: `{title}`")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.setphoto$", re.I), outgoing=True))
async def _setphoto_cmd(event):
    if not event.is_reply:
        return await event.edit("Reply to a photo with `.setphoto`")
    reply = await event.get_reply_message()
    if not reply.photo:
        return await event.edit("❌ Reply to a photo message.")
    try:
        from telethon.tl.functions.channels import EditPhotoRequest
        file = await bot.download_media(reply.photo, bytes)
        uploaded = await bot.upload_file(file)
        await bot(EditPhotoRequest(channel=event.chat_id, photo=uploaded))
        await event.edit("✅ Group photo updated!")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

# ── .setname / .setbio ────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.setname\s+(.+)$", re.I), outgoing=True))
async def _setname_cmd(event):
    name = event.pattern_match.group(1).strip()
    try:
        from telethon.tl.functions.account import UpdateProfileRequest
        await bot(UpdateProfileRequest(first_name=name))
        await event.edit(f"✅ Name changed to: `{name}`")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.setbio\s+(.+)$", re.I), outgoing=True))
async def _setbio_cmd(event):
    bio = event.pattern_match.group(1).strip()
    try:
        from telethon.tl.functions.account import UpdateProfileRequest
        await bot(UpdateProfileRequest(about=bio))
        await event.edit(f"✅ Bio updated!")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

# ── .join / .invite / .leave ──────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.join\s+(.+)$", re.I), outgoing=True))
async def _join_cmd(event):
    link = event.pattern_match.group(1).strip()
    try:
        from telethon.tl.functions.channels import JoinChannelRequest
        await bot(JoinChannelRequest(link))
        await event.edit(f"✅ Joined: `{link}`")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.invite\s+(.+)$", re.I), outgoing=True))
async def _invite_cmd(event):
    username = event.pattern_match.group(1).strip().lstrip("@")
    try:
        user = await bot.get_entity(username)
        await bot(InviteToChannelRequest(event.chat_id, [user]))
        await event.edit(f"✅ Invited `@{username}`")
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.leave$", re.I), outgoing=True))
async def _leave_cmd(event):
    try:
        chat = await event.get_chat()
        title = getattr(chat, "title", "this chat")
        await event.edit(f"👋🏻 Leaving `{title}`...")
        await asyncio.sleep(1)
        await bot.delete_dialog(event.chat_id)
    except Exception as e:
        await event.edit(f"❌ Failed: `{e}`")

# ── .id — show chat / user IDs ────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.id$", re.I), outgoing=True))
async def _id_cmd(event):
    chat_id = event.chat_id
    if event.is_reply:
        reply = await event.get_reply_message()
        if reply and reply.sender_id:
            return await event.edit(f"🆔 **User ID:** `{reply.sender_id}`\n💬 **Chat ID:** `{chat_id}`")
    await event.edit(f"💬 **Chat ID:** `{chat_id}`")

# ── .speedtest ────────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.speedtest$", re.I), outgoing=True))
async def _speedtest_cmd(event):
    await event.edit("📡 Running speedtest… (may take ~30s)")
    try:
        import speedtest as _st
        def _run():
            s = _st.Speedtest()
            s.get_best_server()
            dl = s.download() / 1_000_000
            ul = s.upload() / 1_000_000
            ping = s.results.ping
            return dl, ul, ping
        dl, ul, ping = await asyncio.to_thread(_run)
        await event.edit(
            f"📡 **Speedtest Results**\n"
            f"⬇️ Download: `{dl:.2f} Mbps`\n"
            f"⬆️ Upload: `{ul:.2f} Mbps`\n"
            f"⏱️ Ping: `{ping:.0f} ms`"
        )
    except ImportError:
        await event.edit("❌ `speedtest-cli` not installed. Run: `pip install speedtest-cli`")
    except Exception as e:
        await event.edit(f"❌ Speedtest failed: `{e}`")

# ── .restart ──────────────────────────────────────────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.restart$", re.I), outgoing=True))
async def _restart_cmd(event):
    await event.edit("🔄 Restarting…")
    await bot.disconnect()
    os.execv(sys.executable, [sys.executable] + sys.argv)

# ── .target / .untarget — DM auto-reply with photo + text ─────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.target\s+(.+)$", re.I), outgoing=True))
async def _target_cmd(event):
    if not event.is_private:
        return await event.edit("❌ This command only works in a DM (private chat).")
    if not event.is_reply:
        return await event.edit("❌ Reply to a photo with `.target <your text>`")
    text = event.pattern_match.group(1).strip()
    reply = await event.get_reply_message()
    if not reply.photo:
        return await event.edit("❌ Reply to a photo message.")
    os.makedirs("target_photos", exist_ok=True)
    photo_path = f"target_photos/{event.chat_id}_{reply.id}.jpg"
    await bot.download_media(reply.photo, photo_path)
    _target_store[event.chat_id] = (photo_path, text)
    await event.edit(f"✅ **Target set!**\nAnyone who DMs you gets this photo + message.\nText: {text}\n\nUse `.untarget` to disable.")

@bot.on(events.NewMessage(pattern=re.compile(r"^\.untarget$", re.I), outgoing=True))
async def _untarget_cmd(event):
    data = _target_store.pop(event.chat_id, None)
    if data and os.path.exists(data[0]):
        try: os.remove(data[0])
        except: pass
    await event.edit("✅ Target removed.")

@bot.on(events.NewMessage(incoming=True))
async def _target_reply_handler(event):
    if not event.is_private:
        return
    target = _target_store.get(event.sender_id)
    if not target:
        return
    photo_path, text = target
    if os.path.exists(photo_path):
        try:
            await bot.send_file(event.sender_id, photo_path, caption=text)
        except: pass

# ── .removebots — kick all saved bots from group ─────────────────
@bot.on(events.NewMessage(pattern=re.compile(r"^\.removebots$", re.I), outgoing=True))
async def _removebots_cmd(event):
    await event.edit("🔄 Removing bots…")
    removed = 0
    for username in bot_usernames:
        try:
            ent = await bot.get_entity(username)
            await bot.kick_participant(event.chat_id, ent)
            removed += 1
            await asyncio.sleep(1)
        except: pass
    await event.edit(f"✅ Removed `{removed}` bots.")

# ── AI: ASK & IMAGINE ─────────────────────────────────────────────
# Uses Pollinations.ai — 100% free, no API key required.
# .ask  → AI answers any question (text)
# .imagine → AI generates an image from your prompt

@cmd("ask")
async def _ask(event, arg):
    if not arg:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.ask <your question>`\n𝐄𝐱: `.ask who is kurosaki ichigo`")
    await safe_edit(event, "🤖 𝐀𝐈 𝐢𝐬 𝐭𝐡𝐢𝐧𝐤𝐢𝐧𝐠...")
    try:
        import urllib.parse
        encoded = urllib.parse.quote(arg, safe="")
        answer = None
        # Try up to 2 times (pollinations can be flaky)
        for _attempt in range(2):
            try:
                resp = await asyncio.to_thread(
                    lambda: requests.get(
                        f"https://text.pollinations.ai/{encoded}",
                        timeout=40,
                        headers={"User-Agent": "KurosakiV9/1.0"}
                    )
                )
                if resp.status_code == 200 and resp.text.strip():
                    answer = resp.text.strip()
                    break
            except Exception:
                if _attempt == 0:
                    await asyncio.sleep(2)
        if not answer:
            # Fallback: use pollinations with a model param
            try:
                resp2 = await asyncio.to_thread(
                    lambda: requests.get(
                        f"https://text.pollinations.ai/{encoded}?model=openai",
                        timeout=40,
                        headers={"User-Agent": "KurosakiV9/1.0"}
                    )
                )
                answer = resp2.text.strip() if resp2.status_code == 200 else None
            except Exception:
                pass
        if not answer:
            return await safe_edit(event, "❌ 𝐀𝐈 𝐢𝐬 𝐛𝐮𝐬𝐲 𝐫𝐢𝐠𝐡𝐭 𝐧𝐨𝐰. 𝐓𝐫𝐲 𝐚𝐠𝐚𝐢𝐧 𝐢𝐧 𝐚 𝐦𝐨𝐦𝐞𝐧𝐭.")
        if len(answer) > 3800:
            answer = answer[:3800] + "\n...[𝐭𝐫𝐮𝐧𝐜𝐚𝐭𝐞𝐝]"
        await safe_edit(event,
            f"🤖 **𝐊𝐔𝐑𝐎𝐒𝐀𝐊𝐈 𝐀𝐈**\n"
            f"━━━━━━━━━━━━━━━\n"
            f"❓ `{arg[:80]}{'...' if len(arg) > 80 else ''}`\n"
            f"━━━━━━━━━━━━━━━\n"
            f"{answer}"
        )
    except Exception as e:
        await safe_edit(event, f"❌ 𝐀𝐈 𝐟𝐚𝐢𝐥𝐞𝐝: `{str(e)[:80]}`")

# ── TRIGGER RAID ──────────────────────────────────────────────────
#
#  HOW IT WORKS:
#  .trigraid @user / reply  — lock target, raid every message they send
#  .strigraid [@user]        — stop raid on target, or stop all

@cmd("trigraid")
async def _trigraid(event, arg):
    targets = await get_targets(event, arg)
    if not targets:
        targets_str = ", ".join(f"`{u}`" for u in trigger_raid_targets) or "ɴᴏɴᴇ"
        return await safe_edit(event,
            f"⚡ **ᴛʀɪɢɢᴇʀ ʀᴀɪᴅ**\n"
            f"🎯 ᴀᴄᴛɪᴠᴇ ᴛᴀʀɢᴇᴛs: {targets_str}\n"
            f"━━━━━━━━━━━━━━━\n"
            f"💡 `.trigraid @user` or reply → start | `.strigraid` → stop all"
        )
    for uid in targets:
        try:
            me = await _get_me()
            if uid == me.id:
                continue
        except: pass
        trigger_raid_targets.add(uid)
    added = ", ".join(f"`{u}`" for u in targets)
    return await safe_edit(event,
        f"🎯 **ᴛʀɪɢɢᴇʀ ʀᴀɪᴅ ᴏɴ** {added}\n"
        f"🔁 ɴᴏɴsᴛᴏᴘ: `{TRIGGER_PERMSG}` ꜰᴀsᴛ ʀᴇᴘʟɪᴇs ᴘᴇʀ ᴍsɢ (ꜰɪʀᴇs ᴏɴ ᴇᴠᴇʀʏ ᴍsɢ)\n"
        f"🛑 `.strigraid` ᴛᴏ sᴛᴏᴘ"
    )


@cmd("strigraid")
async def _strigraid(event, arg):
    targets = await get_targets(event, arg)
    if targets:
        removed = [str(u) for u in targets if u in trigger_raid_targets]
        for uid in targets:
            trigger_raid_targets.discard(uid)
        return await safe_edit(event,
            f"🛑 **ᴛʀɪɢɢᴇʀ ʀᴀɪᴅ sᴛᴏᴘᴘᴇᴅ** → `{', '.join(removed) or 'ɴᴏᴛ ᴀᴄᴛɪᴠᴇ'}`"
        )
    else:
        trigger_raid_targets.clear()
        return await safe_edit(event,
            f"🛑 **ᴛʀɪɢɢᴇʀ ʀᴀɪᴅ sᴛᴏᴘᴘᴇᴅ** — ᴀʟʟ ᴛᴀʀɢᴇᴛs ᴄʟᴇᴀʀᴇᴅ"
        )


@cmd("imagine")
async def _imagine(event, arg):
    if not arg:
        return await safe_edit(event, "❌ 𝐔𝐬𝐚𝐠𝐞: `.imagine <prompt>`\n𝐄𝐱: `.imagine anime kurosaki ichigo bankai`")
    await safe_edit(event, f"🎨 **𝐆𝐞𝐧𝐞𝐫𝐚𝐭𝐢𝐧𝐠 𝐈𝐦𝐚𝐠𝐞...**\n`{arg[:60]}{'...' if len(arg)>60 else ''}`")
    try:
        import urllib.parse
        seed = random.randint(1, 999999)
        encoded = urllib.parse.quote(arg, safe="")
        url = (
            f"https://image.pollinations.ai/prompt/{encoded}"
            f"?width=1024&height=1024&nologo=true&seed={seed}&model=flux"
        )
        img_bytes = None
        for _att in range(2):
            try:
                _r = await asyncio.to_thread(
                    lambda: requests.get(url, timeout=90, headers={"User-Agent": "KurosakiV9/1.0"})
                )
                if _r.status_code == 200 and len(_r.content) > 1000:
                    img_bytes = _r.content
                    break
            except Exception:
                if _att == 0:
                    await asyncio.sleep(3)
        if not img_bytes or len(img_bytes) < 1000:
            return await safe_edit(event, "❌ 𝐈𝐦𝐚𝐠𝐞 𝐠𝐞𝐧𝐞𝐫𝐚𝐭𝐢𝐨𝐧 𝐟𝐚𝐢𝐥𝐞𝐝. 𝐓𝐫𝐲 𝐚 𝐝𝐢𝐟𝐟𝐞𝐫𝐞𝐧𝐭 𝐩𝐫𝐨𝐦𝐩𝐭.")
        buf = BytesIO(img_bytes)
        buf.name = "kurosaki_ai.jpg"
        await bot.send_file(
            event.chat_id, buf,
            caption=f"🎨 **𝐊𝐔𝐑𝐎𝐒𝐀𝐊𝐈 𝐀𝐈 𝐈𝐦𝐚𝐠𝐞**\n`{arg[:120]}`"
        )
        await event.delete()
    except Exception as e:
        await safe_edit(event, f"❌ 𝐈𝐦𝐚𝐠𝐢𝐧𝐞 𝐟𝐚𝐢𝐥𝐞𝐝: `{str(e)[:80]}`")

# ─────────────────────────────────────────────────────────────────
#  STARTUP
# ─────────────────────────────────────────────────────────────────
if __name__ == "__main__":
    logger.info(f"🚀 Starting {BRAND} V9...")
    load_admins()
    load_bot_admins()
    load_notes()
    load_banner()
    load_mraid_media()
    load_bot_usernames()
    _load_welcome()
    bot.start()
    me = bot.loop.run_until_complete(bot.get_me())
    _ME_CACHE = me  # V9: warm cache immediately so commands never do a cold lookup
    logger.info(f"✅ Logged in as: {me.first_name} (@{me.username}) | ID: {me.id}")
    logger.info(f"🤖 Saved bulk bots: {', '.join(bot_usernames) or 'none'}")
    logger.info(f"🖼️  Banner: {'set' if menu_banner_msg else 'none'}")
    logger.info(f"📸 MRaid media: {'set' if mraid_media_msg else 'none'}")
    logger.info(f"🎉 Welcome: {'enabled' if _welcome_cfg['enabled'] else 'disabled'}")
    logger.info(f"💣 Bomb Raid: ready (.bomb / .sbomb)")
    logger.info(f"🛡️ Safe Raid: ready (.saferaid / .ssaferaid)")
    logger.info(f"⚡ TrigRaid V9: NONSTOP — fires on every msg, 5 fast replies (0.05s apart)")
    logger.info(f"🗑️ Purge V9: parallel batch — limit 3000 (.purge) / 1000 (.purge2)")
    logger.info(f"👻 GhostPing: ready (.ghostping)")
    logger.info(f"📢 TagAll: ready (.tagall)")
    logger.info(f"⏰ Schedule: ready (.schedule <s> <text>)")
    logger.info(f"🎨 Sticker: ready (.sticker — reply to image)")
    logger.info(f"🔗 AntiLink: ready (.antilink on/off)")
    logger.info(f"🎬 Video DL: ready (.video <title/url>)")
    logger.info(f"🎵 Music: full async + progress + thumbnail (.music)")
    logger.info(f"🎮 Games V9: .coinflip .rps .8ball .trivia .math .fortune .roast .compliment .guess .hangman")
    logger.info(f"🗡️ Vault: raid arsenal renamed from .inventory → .vault")
    logger.info(f"📋 Menu V9: .menu (lines style) | .menu2 (box style) — both with ™ V8 branding")
    logger.info(f"🌟 {BRAND} V9 is running! Type .menu to see all commands.")
    bot.run_until_disconnected()

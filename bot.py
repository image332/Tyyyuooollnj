import telebot
from telebot import types
import subprocess
import os
import sys
import psutil
import json
import time
import threading
import re
import shutil
import signal
import uuid
import ast
import importlib.util
import requests
from flask import Flask, request

# ----------------- ENVIRONMENT VARIABLES -----------------
BOT_TOKEN = os.getenv("BOT_TOKEN")
OWNER_ID_ENV = os.getenv("OWNER_ID")
OWNER_ID_2_ENV = os.getenv("OWNER_ID_2", "").strip()

if not BOT_TOKEN:
    sys.exit("[CRITICAL ERROR] 'BOT_TOKEN' environment variable is missing! Please configure it in Render.")

if not OWNER_ID_ENV:
    sys.exit("[CRITICAL ERROR] 'OWNER_ID' environment variable is missing! Please configure it in Render.")

try:
    OWNER_ID = int(OWNER_ID_ENV)
except ValueError:
    sys.exit("[CRITICAL ERROR] 'OWNER_ID' must be a valid integer Telegram user ID!")

OWNER_IDS = {OWNER_ID}
if OWNER_ID_2_ENV:
    try:
        OWNER_IDS.add(int(OWNER_ID_2_ENV))
    except ValueError:
        sys.exit("[CRITICAL ERROR] 'OWNER_ID_2' must be a valid integer Telegram user ID!")

bot = telebot.TeleBot(BOT_TOKEN)

USERS_FILE = "allowed_users.json"
CONFIG_FILE = "bot_config.json"
KNOWN_FILE = "known_users.json"      # everyone who ever pressed /start (for stats + broadcast)
MAX_CHANNELS = 10
USERS_PER_PAGE = 8
DIV = "━━━━━━━━━━━━━━━━━━"

current_dir = os.getcwd()
bg_processes = {}
waiting_for_channel_forward = set()  # Owner state waiting for channel forward
waiting_for_broadcast = set()        # Owner state waiting for the broadcast message
pending_broadcast = {}               # owner_id -> (chat_id, message_id) waiting for confirmation
pending_requests = set()             # User IDs with active approval request sent to admin
waiting_for_project_name = set()     # users who sent a file and must now type a project name
pending_uploads = {}                 # uid -> [messages] waiting for the project name
active_project = {}                  # uid -> {name, dir, ts}  (open project, expires after idle)
pending_lock = threading.Lock()
PROJECT_IDLE = 600                   # seconds

START_TIME = time.time()

# ----------------- COLOURED BUTTONS (Telegram Bot API 9.4 "style") -----------------
# Official button colours: "primary" = blue, "success" = green, "danger" = red.
# These small subclasses add the `style` field to the button JSON, so they work with
# any pyTelegramBotAPI version (older Telegram apps just show the normal grey button).

PRIMARY = "primary"
SUCCESS = "success"
DANGER = "danger"


class IBtn(types.InlineKeyboardButton):
    """Inline button with an official colour."""
    def __init__(self, text, style=None, **kwargs):
        super().__init__(text, **kwargs)
        self._btn_style = style

    def to_dict(self):
        data = super().to_dict()
        if self._btn_style:
            data["style"] = self._btn_style
        return data


class RBtn(types.KeyboardButton):
    """Reply-keyboard button (the keyboard at the bottom) with an official colour."""
    def __init__(self, text, style=None, **kwargs):
        super().__init__(text, **kwargs)
        self._btn_style = style

    def to_dict(self):
        data = super().to_dict()
        if self._btn_style:
            data["style"] = self._btn_style
        return data

# ----------------- ESCAPE / SANITIZATION HELPERS -----------------

def escape_markdown(text):
    """
    Escapes Telegram legacy Markdown special characters (*, _, `, [).
    Prevents 'can't parse entities' errors when usernames or names contain symbols.
    """
    if not text:
        return ""
    chars = ['*', '_', '`', '[']
    for ch in chars:
        text = text.replace(ch, f"\\{ch}")
    return text

def code_safe(text, limit=60):
    """Makes text safe to place inside a `code span`."""
    text = (text or "").replace("`", "'").replace("\n", " ")
    return text if len(text) <= limit else text[:limit - 1] + "…"

def bar(percent, size=10):
    """Little progress bar for CPU / RAM / Disk."""
    filled = int(round(max(0, min(100, percent)) / 100 * size))
    return "▰" * filled + "▱" * (size - filled)

# ----------------- STORAGE HELPERS -----------------

def load_users():
    if os.path.exists(USERS_FILE):
        try:
            with open(USERS_FILE, "r") as f:
                return set(json.load(f))
        except Exception:
            return set(OWNER_IDS)
    return set(OWNER_IDS)

def save_users(users_set):
    with open(USERS_FILE, "w") as f:
        json.dump(list(users_set), f)

def load_config():
    default_config = {"required_channels": []}
    if os.path.exists(CONFIG_FILE):
        try:
            with open(CONFIG_FILE, "r") as f:
                data = json.load(f)
                if "required_channel_id" in data and data["required_channel_id"]:
                    data["required_channels"] = [{
                        "id": data["required_channel_id"],
                        "title": data.get("required_channel_title") or "Required Channel",
                        "username": data.get("required_channel_username"),
                        "invite_link": data.get("required_channel_invite_link")
                    }]
                if "required_channels" not in data:
                    data["required_channels"] = []
                return data
        except Exception:
            return default_config
    return default_config

def save_config(cfg):
    with open(CONFIG_FILE, "w") as f:
        json.dump(cfg, f, indent=4)

def load_known():
    if os.path.exists(KNOWN_FILE):
        try:
            with open(KNOWN_FILE, "r") as f:
                data = json.load(f)
                if isinstance(data, dict):
                    return data
        except Exception:
            pass
    return {}

def save_known(data):
    with open(KNOWN_FILE, "w") as f:
        json.dump(data, f)

allowed_users = load_users()
bot_config = load_config()
known_users = load_known()

def track_user(user):
    """Remember everyone who talks to the bot (used for stats, user manager and broadcast)."""
    key = str(user.id)
    name = f"{user.first_name or ''} {user.last_name or ''}".strip() or "User"
    old = known_users.get(key)
    if old and old.get("name") == name and old.get("username") == user.username:
        return
    known_users[key] = {
        "name": name,
        "username": user.username,
        "joined": old.get("joined") if old else int(time.time())
    }
    try:
        save_known(known_users)
    except Exception as e:
        print(f"[!] Could not save known users: {e}")

# ----------------- VERIFICATION HELPERS -----------------

def is_owner(user_id):
    return user_id in OWNER_IDS

def is_allowed_user(user_id):
    return user_id in allowed_users or user_id in OWNER_IDS

def check_channel_subscriptions(user_id):
    """
    Checks if a user is subscribed to ALL configured channels (up to 10).
    Returns: (is_all_joined: bool, missing_channels: list of dicts)
    """
    if is_owner(user_id):
        return True, []

    channels = bot_config.get("required_channels", [])
    if not channels:
        return True, []

    missing = []
    for ch in channels:
        ch_id = ch.get("id")
        try:
            member = bot.get_chat_member(ch_id, user_id)
            if member.status not in ['member', 'administrator', 'creator']:
                missing.append(ch)
        except Exception as e:
            print(f"[!] Error checking channel {ch_id}: {e}")
            missing.append(ch)

    return (len(missing) == 0), missing

def get_forward_chat(msg):
    """Works with both the old (forward_from_chat) and new (forward_origin) forward fields."""
    chat = getattr(msg, "forward_from_chat", None)
    if chat:
        return chat
    origin = getattr(msg, "forward_origin", None)
    return getattr(origin, "chat", None) if origin else None

def get_uptime():
    uptime_seconds = int(time.time() - START_TIME)
    days = uptime_seconds // 86400
    hours = (uptime_seconds % 86400) // 3600
    minutes = (uptime_seconds % 3600) // 60
    seconds = uptime_seconds % 60
    return f"{days}d {hours}h {minutes}m {seconds}s"

def active_engines():
    return sum(1 for info in bg_processes.values() if info['process'].poll() is None)

# ----------------- REPLY KEYBOARD (bottom keyboard) -----------------

BTN_UPLOAD = "📤 Upload File"
BTN_FILES = "📂 My Files"
BTN_STATUS = "⏳ Status"
BTN_VITALS = "🧬 Vitals"
BTN_RAM = "🧠 RAM"
BTN_DISK = "💽 Disk"
BTN_ENGINES = "⚙️ Engines"
BTN_MYID = "🪪 My ID"
BTN_HELP = "📖 Help"
BTN_ADMIN = "👑 Admin Panel"

MENU_TEXTS = {BTN_UPLOAD, BTN_FILES, BTN_STATUS, BTN_VITALS, BTN_RAM, BTN_DISK, BTN_ENGINES, BTN_MYID, BTN_HELP, BTN_ADMIN}

def get_reply_keyboard(user_id):
    rows = [
        [RBtn(BTN_UPLOAD, style=SUCCESS), RBtn(BTN_FILES, style=PRIMARY)],
        [RBtn(BTN_STATUS, style=SUCCESS), RBtn(BTN_VITALS, style=PRIMARY)],
        [RBtn(BTN_RAM, style=PRIMARY), RBtn(BTN_DISK, style=PRIMARY)],
        [RBtn(BTN_ENGINES, style=DANGER), RBtn(BTN_MYID, style=PRIMARY)],
        [RBtn(BTN_HELP, style=SUCCESS)],
    ]
    if is_owner(user_id):
        rows[-1].append(RBtn(BTN_ADMIN, style=DANGER))

    try:
        markup = types.ReplyKeyboardMarkup(
            resize_keyboard=True,
            is_persistent=True,
            input_field_placeholder="⌨️ Type a command or tap a button..."
        )
    except TypeError:
        markup = types.ReplyKeyboardMarkup(resize_keyboard=True)
    for row in rows:
        markup.row(*row)
    return markup

# ----------------- INLINE KEYBOARDS -----------------

def get_join_channels_keyboard(missing_channels):
    markup = types.InlineKeyboardMarkup(row_width=1)
    for i, ch in enumerate(missing_channels, 1):
        link = ch.get("invite_link")
        title = ch.get("title", f"Channel {i}")
        if link:
            markup.add(IBtn(f"📢 Join {title}", style=PRIMARY, url=link))
    markup.add(IBtn("🔄 Verify Membership", style=SUCCESS, callback_data="verify_membership"))
    return markup

def get_request_access_keyboard():
    markup = types.InlineKeyboardMarkup()
    markup.add(IBtn("📩 Request Access from Admin", style=SUCCESS, callback_data="send_auth_request"))
    return markup

def get_main_menu_keyboard(user_id):
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(
        IBtn("📤 Upload File", style=SUCCESS, callback_data="btn_upload"),
        IBtn("📂 My Files", style=PRIMARY, callback_data="btn_files")
    )
    markup.add(
        IBtn("⏳ Status", style=SUCCESS, callback_data="btn_status"),
        IBtn("🧬 Vitals", style=PRIMARY, callback_data="btn_sysinfo")
    )
    markup.add(
        IBtn("🧠 RAM", style=PRIMARY, callback_data="btn_memory"),
        IBtn("💽 Disk", style=PRIMARY, callback_data="btn_disk")
    )
    markup.add(
        IBtn("⚙️ Engines", style=DANGER, callback_data="btn_ps"),
        IBtn("🪪 My ID", style=PRIMARY, callback_data="btn_myid")
    )
    markup.add(IBtn("📖 Help Guide", style=SUCCESS, callback_data="btn_help"))
    if is_owner(user_id):
        markup.add(IBtn("👑 Admin Panel", style=DANGER, callback_data="adm_panel"))
    return markup

def get_back_keyboard():
    markup = types.InlineKeyboardMarkup()
    markup.add(IBtn("🔙 Back to Menu", style=PRIMARY, callback_data="btn_main_menu"))
    return markup

def get_admin_back_keyboard():
    markup = types.InlineKeyboardMarkup()
    markup.add(IBtn("🔙 Admin Panel", style=PRIMARY, callback_data="adm_panel"))
    return markup

# ----------------- TEXTS -----------------

def get_welcome_text(user):
    uid = user.id
    name = escape_markdown(user.first_name or "there")
    role = "👑 Owner" if is_owner(uid) else "✅ Approved User"
    return (
        f"⚡️ *PYTHON HOSTING BOT V2*\n"
        f"_Your personal server, right inside Telegram_\n"
        f"{DIV}\n\n"
        f"👋 Hey *{name}*, welcome!\n\n"
        f"🖥 Run terminal commands & scripts\n"
        f"🚀 Send a file — it loads and runs by itself\n"
        f"📥 Download your files any time\n"
        f"⚙️ Keep your bots running in the background\n"
        f"📊 Watch live server health\n\n"
        f"{DIV}\n"
        f"🪪 *ID:* `{uid}`\n"
        f"🔰 *Access:* {role}\n"
        f"🟢 *Server:* Online · ⏱ `{get_uptime()}`\n"
        f"{DIV}\n"
        f"👇 _Pick an option below or just type a command_"
    )

WELCOME_IMAGE = "https://i.ibb.co/QFPrdV53/IMG-20261004-175229-951.jpg"

def send_welcome(chat_id, user):
    try:
        bot.send_photo(chat_id, WELCOME_IMAGE)
    except Exception:
        pass
    bot.send_message(chat_id, get_welcome_text(user), parse_mode="Markdown", reply_markup=get_reply_keyboard(user.id))

def get_locked_text(user, joined):
    name = escape_markdown(user.first_name or "there")
    head = (
        f"⚡️ *PYTHON HOSTING BOT V2*\n"
        f"_Your personal server, right inside Telegram_\n"
        f"{DIV}\n\n"
        f"👋 Hey *{name}*, welcome!\n\n"
        f"This is a private hosting terminal — run scripts, host your bots and manage files, all from Telegram.\n\n"
    )
    if not joined:
        steps = (
            "🔒 *Unlock access in 3 steps*\n"
            "1️⃣ Join the channel(s) below 📢\n"
            "2️⃣ Tap *Verify Membership* 🔄\n"
            "3️⃣ Get approved by the Admin ✅"
        )
    else:
        steps = (
            "✅ *Channels verified!*\n\n"
            "🔒 *One last step*\n"
            "Tap the button below to ask the Admin for access."
        )
    return head + steps

def get_dashboard_text():
    return (
        f"🎛 *DASHBOARD*\n"
        f"{DIV}\n\n"
        f"🟢 *Server:* Online\n"
        f"⏱ *Uptime:* `{get_uptime()}`\n"
        f"⚙️ *Engines:* `{active_engines()}`\n\n"
        f"_Tap an option below_ 👇"
    )

def get_help_text(user_id=None):
    count = len(bot_config.get("required_channels", []))
    text = (
        f"⚡️ *PYTHON HOSTING BOT V2 — COMMAND GUIDE*\n"
        f"{DIV}\n\n"
        f"💻 *Terminal*\n"
        f"• Just type a command — `ls`, `git status`\n"
        f"• `cd <dir>` — change folder 📂\n"
        f"• `pip install <pkg>` — install a package 💉\n"
        f"• `python <script.py>` — run a script 🔥\n\n"
        f"🗂 *Files*\n"
        f"• Send a `.py` `.js` `.sh` file — it loads and *runs by itself* 🚀\n"
        f"• `/upload` — upload guide · `/files` — your files 📂\n"
        f"• `/newproject` — start another project 📁\n"
        f"• Each file has its own ▶️ Run ⏹ Stop 📜 Log buttons\n"
        f"• `/download <filename>` — get a server file back 📥\n\n"
        f"⚙️ *Background Engines*\n"
        f"• `/run <cmd>` — start in background 🟢\n"
        f"• `/ps` — list running engines 📊\n"
        f"• `/stop <pid>` — stop an engine 🛑\n\n"
        f"🖥 *System*\n"
        f"• `/status` ⏳  `/sysinfo` 🧬  `/memory` 🧠  `/disk` 💽\n"
        f"• `/myid` — your Telegram ID 🪪\n"
        f"• `/menu` — quick action buttons 🎛\n"
    )
    if user_id is not None and is_owner(user_id):
        text += (
            f"\n👑 *Admin*\n"
            f"• `/admin` — admin panel\n"
            f"• `/broadcast` — message all users 📣\n"
            f"• `/channel` · `/channels` — force-join channels ({count}/{MAX_CHANNELS}) 📢\n"
            f"• `/add <id>` · `/remove <id>` — approve / remove users 👥\n"
        )
    text += f"\n{DIV}\n_SYSTEM READY_ ▍ type a command or use the buttons"
    return text

def get_status_text():
    return (
        f"🟢 *SERVER STATUS*\n"
        f"{DIV}\n\n"
        f"📡 *State:* `ONLINE`\n"
        f"⏳ *Runtime:* `{get_uptime()}`\n"
        f"⚙️ *Engines:* `{active_engines()}`\n"
        f"🔐 *Connection:* `SECURE`"
    )

def get_vitals_text():
    cpu = psutil.cpu_percent(interval=0.4)
    ram = psutil.virtual_memory().percent
    return (
        f"🧬 *SYSTEM VITALS*\n"
        f"{DIV}\n\n"
        f"🔥 *CPU:* `{cpu}%`\n`{bar(cpu)}`\n\n"
        f"🧠 *RAM:* `{ram}%`\n`{bar(ram)}`"
    )

def get_memory_text():
    mem = psutil.virtual_memory()
    return (
        f"🧠 *MEMORY CORE*\n"
        f"{DIV}\n\n"
        f"`{bar(mem.percent)}` *{mem.percent}%*\n\n"
        f"*Total:* `{mem.total / (1024**3):.2f} GB`\n"
        f"*Used:* `{mem.used / (1024**3):.2f} GB`\n"
        f"*Free:* `{mem.available / (1024**3):.2f} GB`"
    )

def get_disk_text():
    disk = psutil.disk_usage('/')
    return (
        f"💽 *STORAGE VAULT*\n"
        f"{DIV}\n\n"
        f"`{bar(disk.percent)}` *{disk.percent}%*\n\n"
        f"*Total:* `{disk.total / (1024**3):.2f} GB`\n"
        f"*Used:* `{disk.used / (1024**3):.2f} GB`\n"
        f"*Free:* `{disk.free / (1024**3):.2f} GB`"
    )

def get_myid_text(user_id):
    return f"🪪 *YOUR TELEGRAM ID*\n{DIV}\n\n`{user_id}`\n\n_Tap the number to copy_ ⚡️"

def get_engines_view(with_back=False):
    """Returns (text, markup) for the running engines list."""
    alive = {}
    for pid, info in list(bg_processes.items()):
        if info['process'].poll() is None:
            alive[pid] = info
        else:
            del bg_processes[pid]

    markup = types.InlineKeyboardMarkup(row_width=1)
    if not alive:
        text = (
            f"💤 *SYSTEM IDLE*\n"
            f"{DIV}\n\n"
            f"No background engines running.\n"
            f"Start one with `/run python app.py`"
        )
    else:
        text = f"⚙️ *ACTIVE ENGINES* ({len(alive)})\n{DIV}\n\n"
        for pid, info in alive.items():
            text += f"🟢 `{pid}` — `{code_safe(info['cmd'])}`\n"
            markup.add(IBtn(f"🛑 Kill PID {pid}", style=DANGER, callback_data=f"kill_{pid}"))
    if with_back:
        markup.add(IBtn("🔙 Back to Menu", style=PRIMARY, callback_data="btn_main_menu"))
    return text, markup

# ----------------- SAFE EDIT HELPERS -----------------

def safe_edit(chat_id, message_id, text, markup=None):
    try:
        bot.edit_message_text(chat_id=chat_id, message_id=message_id, text=text, parse_mode="Markdown", reply_markup=markup)
    except Exception as e:
        if "not modified" not in str(e):
            print(f"[!] Edit failed: {e}")

def edit(call, text, markup=None):
    safe_edit(call.message.chat.id, call.message.message_id, text, markup)

# ----------------- ACCESS GATES -----------------

def access_ok(message):
    """Used by every protected command: whitelisted + joined all channels."""
    uid = message.from_user.id
    if not is_allowed_user(uid):
        bot.reply_to(message, "⛔️ *ACCESS RESTRICTED*\nSend /start to request access.", parse_mode="Markdown")
        return False
    is_all_joined, missing = check_channel_subscriptions(uid)
    if not is_all_joined:
        bot.reply_to(message, "⚠️ *Access Denied:* Please join all channels first.", reply_markup=get_join_channels_keyboard(missing), parse_mode="Markdown")
        return False
    return True

def entry_gate(message):
    """
    Used by /start, /menu, /help. Returns True if the user may continue,
    otherwise sends the right prompt (join channels / ask the admin) and returns False.
    """
    user = message.from_user
    uid = user.id
    if is_owner(uid):
        return True

    is_all_joined, missing = check_channel_subscriptions(uid)
    if not is_all_joined:
        bot.send_message(message.chat.id, get_locked_text(user, joined=False), parse_mode="Markdown", reply_markup=get_join_channels_keyboard(missing))
        return False

    if not is_allowed_user(uid):
        bot.send_message(message.chat.id, get_locked_text(user, joined=True), parse_mode="Markdown", reply_markup=get_request_access_keyboard())
        return False

    return True

# ----------------- COMMAND MENU (the "/" menu next to the typing box) -----------------

USER_COMMANDS = [
    ("start", "🚀 Open your dashboard"),
    ("menu", "🎛 Quick action buttons"),
    ("help", "📖 Full command guide"),
    ("status", "⏳ Server status & uptime"),
    ("sysinfo", "🧬 CPU & RAM usage"),
    ("memory", "🧠 Memory details"),
    ("disk", "💽 Storage details"),
    ("ps", "⚙️ Running background engines"),
    ("upload", "📤 Upload a file (auto-runs)"),
    ("files", "📂 Your hosted files"),
    ("run", "🟢 Start a background engine"),
    ("stop", "🛑 Stop an engine by PID"),
    ("download", "📥 Download a file from the server"),
    ("myid", "🪪 Show your Telegram ID"),
    ("newproject", "🆕 Start a new project"),
    ("cancel", "❌ Cancel the current action"),
]

OWNER_COMMANDS = USER_COMMANDS + [
    ("admin", "👑 Open the admin panel"),
    ("broadcast", "📣 Send a message to all users"),
    ("channels", "📢 Manage force-join channels"),
    ("channel", "➕ Add a force-join channel"),
    ("add", "✅ Approve a user by ID"),
    ("remove", "🗑 Remove a user by ID"),
]

def setup_command_menu():
    try:
        bot.set_my_commands([types.BotCommand(c, d) for c, d in USER_COMMANDS])
        bot.set_chat_menu_button(menu_button=types.MenuButtonCommands())
    except Exception as e:
        print(f"[!] Could not set command menu: {e}")
    set_owner_commands()

def set_owner_commands():
    try:
        for owner_id in OWNER_IDS:
            bot.set_my_commands(
                [types.BotCommand(c, d) for c, d in OWNER_COMMANDS],
                scope=types.BotCommandScopeChat(owner_id)
            )
    except Exception as e:
        print(f"[!] Could not set owner command menu (open the bot and send /start once): {e}")

# ----------------- ADMIN PANEL -----------------

def get_admin_panel_text():
    total = len(known_users)
    approved = len(allowed_users - OWNER_IDS)
    channels = len(bot_config.get("required_channels", []))
    return (
        f"👑 *ADMIN PANEL*\n"
        f"{DIV}\n\n"
        f"👥 *Users started:* `{total}`\n"
        f"✅ *Approved:* `{approved}`\n"
        f"📢 *Force-join channels:* `{channels}/{MAX_CHANNELS}`\n"
        f"⚙️ *Engines running:* `{active_engines()}`\n"
        f"⏱ *Uptime:* `{get_uptime()}`\n\n"
        f"{DIV}\n"
        f"_Choose an action below_"
    )

def get_admin_panel_keyboard():
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(
        IBtn("📣 Broadcast", style=SUCCESS, callback_data="adm_broadcast"),
        IBtn("👥 Users", style=PRIMARY, callback_data="adm_users_0")
    )
    markup.add(
        IBtn("📢 Channels", style=PRIMARY, callback_data="btn_channel_info"),
        IBtn("🔄 Refresh", callback_data="adm_panel")
    )
    markup.add(IBtn("🔙 Main Menu", style=PRIMARY, callback_data="btn_main_menu"))
    return markup

def show_admin_panel(chat_id, message_id=None):
    if message_id:
        safe_edit(chat_id, message_id, get_admin_panel_text(), get_admin_panel_keyboard())
    else:
        bot.send_message(chat_id, get_admin_panel_text(), parse_mode="Markdown", reply_markup=get_admin_panel_keyboard())

def show_users_manager(chat_id, message_id, page=0):
    ids = sorted(allowed_users - OWNER_IDS)
    total_pages = max(1, (len(ids) + USERS_PER_PAGE - 1) // USERS_PER_PAGE)
    page = max(0, min(page, total_pages - 1))
    chunk = ids[page * USERS_PER_PAGE:(page + 1) * USERS_PER_PAGE]

    markup = types.InlineKeyboardMarkup(row_width=1)
    if not ids:
        text = (
            f"👥 *USER MANAGER*\n"
            f"{DIV}\n\n"
            f"No approved users yet.\n"
            f"New access requests will appear in this chat."
        )
    else:
        text = (
            f"👥 *USER MANAGER* — {len(ids)} approved\n"
            f"{DIV}\n"
            f"_Tap a user to remove their access_\n\n"
        )
        for uid in chunk:
            info = known_users.get(str(uid), {})
            name = info.get("name") or "User"
            uname = info.get("username")
            line = f"▪️ {escape_markdown(name)} — `{uid}`"
            if uname:
                line += f" (@{escape_markdown(uname)})"
            text += line + "\n"
            markup.add(IBtn(f"🗑 Remove {name[:18]}", style=DANGER, callback_data=f"adm_rm_{uid}_{page}"))

        if total_pages > 1:
            nav = []
            if page > 0:
                nav.append(IBtn("⬅️ Prev", style=PRIMARY, callback_data=f"adm_users_{page - 1}"))
            if page < total_pages - 1:
                nav.append(IBtn("Next ➡️", style=PRIMARY, callback_data=f"adm_users_{page + 1}"))
            markup.row(*nav)
            text += f"\n_Page {page + 1}/{total_pages}_"

    markup.add(IBtn("🔙 Admin Panel", style=PRIMARY, callback_data="adm_panel"))
    safe_edit(chat_id, message_id, text, markup)

def broadcast_prompt_text():
    return (
        f"📣 *BROADCAST*\n"
        f"{DIV}\n\n"
        f"Send me the message you want to deliver to *all users* ({len([u for u in known_users if int(u) not in OWNER_IDS])} people).\n\n"
        f"Text, photo, video, file — anything works.\n"
        f"_You'll get a confirmation before it is sent._"
    )

def broadcast_cancel_keyboard():
    markup = types.InlineKeyboardMarkup()
    markup.add(IBtn("❌ Cancel", style=DANGER, callback_data="bc_cancel"))
    return markup

def run_broadcast(owner_id, chat_id, status_message_id):
    source = pending_broadcast.pop(owner_id, None)
    if not source:
        return
    src_chat, src_msg = source
    targets = [int(u) for u in known_users if int(u) not in OWNER_IDS]
    sent = 0
    failed = 0
    for target in targets:
        try:
            bot.copy_message(target, src_chat, src_msg)
            sent += 1
        except Exception:
            failed += 1
        time.sleep(0.05)  # stay under Telegram's flood limits

    safe_edit(
        chat_id, status_message_id,
        f"✅ *BROADCAST COMPLETE*\n{DIV}\n\n📨 *Delivered:* `{sent}`\n🚫 *Failed:* `{failed}`\n\n_Failed = users who blocked the bot._",
        get_admin_back_keyboard()
    )

# ----------------- OWNER CHANNEL MANAGEMENT -----------------

@bot.message_handler(commands=['channel'])
def set_channel_prompt(message):
    if not is_owner(message.from_user.id):
        bot.reply_to(message, "💀 *[ACCESS DENIED]* Owner only.", parse_mode="Markdown")
        return

    current_count = len(bot_config.get("required_channels", []))
    if current_count >= MAX_CHANNELS:
        bot.reply_to(
            message,
            f"⚠️ *LIMIT REACHED*\nYou already have `{MAX_CHANNELS}` channels added!\n"
            f"Use `/channels` or `/channel_del <id>` to remove one first.",
            parse_mode="Markdown"
        )
        return

    waiting_for_channel_forward.add(message.from_user.id)
    text = (
        f"📢 *ADD CHANNEL* ({current_count}/{MAX_CHANNELS})\n"
        f"{DIV}\n\n"
        f"1️⃣ Add this bot as an *Administrator* in your channel (with invite link permission).\n"
        f"2️⃣ *Forward any post from that channel to this chat right now.*\n\n"
        f"_Send /cancel any time to stop._"
    )
    markup = types.InlineKeyboardMarkup()
    markup.add(IBtn("❌ Cancel Setup", style=DANGER, callback_data="cancel_channel_setup"))
    bot.reply_to(message, text, parse_mode="Markdown", reply_markup=markup)

@bot.message_handler(commands=['channels'])
def list_channels_cmd(message):
    if not is_owner(message.from_user.id):
        return
    show_channel_manager(message.chat.id, None)

@bot.message_handler(commands=['channel_del'])
def delete_channel_by_arg(message):
    if not is_owner(message.from_user.id):
        return
    args = message.text.split(" ")
    if len(args) < 2:
        bot.reply_to(message, "⚠️ *Format Error:*\nUse `/channel_del <channel_id>` or `/channels` to manage with buttons.", parse_mode="Markdown")
        return
    try:
        del_id = int(args[1])
        channels = bot_config.get("required_channels", [])
        before = len(channels)
        bot_config["required_channels"] = [c for c in channels if c.get("id") != del_id]
        if len(bot_config["required_channels"]) < before:
            save_config(bot_config)
            bot.reply_to(message, f"✅ Removed channel `{del_id}`.", parse_mode="Markdown")
        else:
            bot.reply_to(message, f"❌ Channel ID `{del_id}` not found in list.", parse_mode="Markdown")
    except ValueError:
        bot.reply_to(message, "⚠️ Channel ID must be a numeric integer.")

def show_channel_manager(chat_id, message_id=None):
    channels = bot_config.get("required_channels", [])
    markup = types.InlineKeyboardMarkup(row_width=1)

    if not channels:
        text = (
            f"📢 *CHANNEL MANAGER* (0/{MAX_CHANNELS})\n"
            f"{DIV}\n\n"
            f"No required channels yet.\n"
            f"Tap *Add New Channel* to set one up!"
        )
    else:
        text = f"📢 *CHANNEL MANAGER* ({len(channels)}/{MAX_CHANNELS})\n{DIV}\n\n"
        for i, ch in enumerate(channels, 1):
            clean_title = escape_markdown(ch.get('title', 'Channel'))
            link = escape_markdown(ch.get('invite_link') or 'None')
            text += f"{i}. *{clean_title}*\n   🆔 `{ch.get('id')}`\n   🔗 {link}\n\n"
            markup.add(IBtn(f"🗑 Remove: {ch.get('title', 'Channel')[:25]}", style=DANGER, callback_data=f"del_ch_{ch.get('id')}"))

    if len(channels) < MAX_CHANNELS:
        markup.add(IBtn("➕ Add New Channel", style=SUCCESS, callback_data="add_new_channel_btn"))
    markup.add(IBtn("🔙 Admin Panel", style=PRIMARY, callback_data="adm_panel"))

    if message_id:
        safe_edit(chat_id, message_id, text, markup)
    else:
        bot.send_message(chat_id, text, parse_mode="Markdown", reply_markup=markup)

@bot.message_handler(commands=['cancel'])
def cancel_action(message):
    uid = message.from_user.id
    cancelled = False
    if uid in waiting_for_channel_forward:
        waiting_for_channel_forward.discard(uid)
        cancelled = True
    if uid in waiting_for_broadcast:
        waiting_for_broadcast.discard(uid)
        cancelled = True
    if pending_broadcast.pop(uid, None):
        cancelled = True
    if uid in waiting_for_project_name:
        waiting_for_project_name.discard(uid)
        pending_uploads.pop(uid, None)
        cancelled = True
    if cancelled:
        bot.reply_to(message, "❌ Cancelled.")

@bot.message_handler(commands=['add'])
def add_user(message):
    if not is_owner(message.from_user.id):
        bot.reply_to(message, "💀 *[ACCESS DENIED]* Owner only.", parse_mode="Markdown")
        return
    try:
        new_id = int(message.text.split(" ")[1])
        allowed_users.add(new_id)
        save_users(allowed_users)
        bot.reply_to(message, f"⚡️ *ACCESS GRANTED*\nUser `{new_id}` added to the authorized list! 🚀", parse_mode="Markdown")
        try:
            bot.send_message(
                new_id,
                "🎉 *ACCESS APPROVED*\n\nThe Admin approved your access! Your keyboard is ready below 👇",
                parse_mode="Markdown",
                reply_markup=get_reply_keyboard(new_id)
            )
        except Exception:
            pass
    except Exception:
        bot.reply_to(message, "⚠️ *Format Error:*\nUse: `/add <userid>`", parse_mode="Markdown")

@bot.message_handler(commands=['remove'])
def remove_user(message):
    if not is_owner(message.from_user.id):
        return
    try:
        del_id = int(message.text.split(" ")[1])
        if del_id in OWNER_IDS:
            bot.reply_to(message, "👑 *[SYSTEM ERROR]* Cannot disconnect the master owner! 🧠", parse_mode="Markdown")
            return
        if del_id in allowed_users:
            allowed_users.remove(del_id)
            save_users(allowed_users)
            bot.reply_to(message, f"🗑 *USER REMOVED*\nUser `{del_id}` removed from the authorized list! 🔌", parse_mode="Markdown")
        else:
            bot.reply_to(message, "⚠️ User ID not found in whitelist.")
    except Exception:
        bot.reply_to(message, "⚠️ *Format Error:*\nUse: `/remove <userid>`", parse_mode="Markdown")

@bot.message_handler(commands=['admin'])
def admin_cmd(message):
    if not is_owner(message.from_user.id):
        bot.reply_to(message, "💀 *[ACCESS DENIED]* Owner only.", parse_mode="Markdown")
        return
    show_admin_panel(message.chat.id)

@bot.message_handler(commands=['broadcast'])
def broadcast_cmd(message):
    if not is_owner(message.from_user.id):
        bot.reply_to(message, "💀 *[ACCESS DENIED]* Owner only.", parse_mode="Markdown")
        return
    waiting_for_broadcast.add(message.from_user.id)
    bot.send_message(message.chat.id, broadcast_prompt_text(), parse_mode="Markdown", reply_markup=broadcast_cancel_keyboard())

# ----------------- CHANNEL FORWARD CAPTURE (UP TO 10) -----------------

FORWARD_TYPES = ['text', 'photo', 'video', 'document', 'audio', 'animation', 'voice']

@bot.message_handler(
    func=lambda msg: msg.from_user.id in waiting_for_channel_forward and get_forward_chat(msg) is not None,
    content_types=FORWARD_TYPES
)
def handle_channel_forward(message):
    user_id = message.from_user.id
    chat = get_forward_chat(message)
    waiting_for_channel_forward.discard(user_id)

    if chat.type != 'channel':
        bot.reply_to(message, "❌ The forwarded message must be from a *Channel*. Setup cancelled.", parse_mode="Markdown")
        return

    channels = bot_config.get("required_channels", [])
    if len(channels) >= MAX_CHANNELS:
        bot.reply_to(message, f"⚠️ Maximum limit of {MAX_CHANNELS} channels reached. Remove one first using `/channels`.", parse_mode="Markdown")
        return

    channel_id = chat.id
    channel_title = chat.title or "Required Channel"
    channel_username = chat.username

    if any(c.get("id") == channel_id for c in channels):
        bot.reply_to(message, f"⚠️ Channel *{escape_markdown(channel_title)}* (`{channel_id}`) is already in your required list!", parse_mode="Markdown")
        return

    invite_link = None
    try:
        chat_info = bot.get_chat(channel_id)
        if chat_info.invite_link:
            invite_link = chat_info.invite_link
        elif channel_username:
            invite_link = f"https://t.me/{channel_username}"
        else:
            link_obj = bot.create_chat_invite_link(channel_id)
            invite_link = link_obj.invite_link
    except Exception as e:
        if channel_username:
            invite_link = f"https://t.me/{channel_username}"
        print(f"[!] Could not create or fetch invite link: {e}")

    new_channel = {
        "id": channel_id,
        "title": channel_title,
        "username": channel_username,
        "invite_link": invite_link
    }
    channels.append(new_channel)
    bot_config["required_channels"] = channels
    save_config(bot_config)

    clean_title = escape_markdown(channel_title)
    link_text = escape_markdown(invite_link) if invite_link else "No link generated"
    markup = types.InlineKeyboardMarkup()
    markup.add(IBtn("📢 Open Channel Manager", style=PRIMARY, callback_data="btn_channel_info"))
    success_text = (
        f"✅ *CHANNEL #{len(channels)} ADDED*\n"
        f"{DIV}\n\n"
        f"📌 *Title:* {clean_title}\n"
        f"🆔 *ID:* `{channel_id}`\n"
        f"🔗 *Link:* {link_text}\n\n"
        f"Active channels: `{len(channels)}/{MAX_CHANNELS}`\n"
        f"_Users must now join all active channels before using the bot!_"
    )
    bot.reply_to(message, success_text, parse_mode="Markdown", reply_markup=markup)

# ----------------- BROADCAST CAPTURE (OWNER) -----------------

BROADCAST_TYPES = ['text', 'photo', 'video', 'document', 'audio', 'animation', 'voice', 'sticker']

@bot.message_handler(
    func=lambda msg: msg.from_user.id in waiting_for_broadcast and not (msg.text or "").startswith("/"),
    content_types=BROADCAST_TYPES
)
def capture_broadcast(message):
    uid = message.from_user.id
    waiting_for_broadcast.discard(uid)
    pending_broadcast[uid] = (message.chat.id, message.message_id)

    count = len([u for u in known_users if int(u) not in OWNER_IDS])
    markup = types.InlineKeyboardMarkup(row_width=2)
    markup.add(
        IBtn(f"✅ Send to {count} users", style=SUCCESS, callback_data="bc_confirm"),
        IBtn("❌ Cancel", style=DANGER, callback_data="bc_cancel")
    )
    bot.reply_to(
        message,
        f"📣 *READY TO SEND*\n{DIV}\n\nThe message above will be delivered to *{count}* users.\nConfirm?",
        parse_mode="Markdown",
        reply_markup=markup
    )

# ----------------- START / MENU / HELP -----------------

@bot.message_handler(commands=['start'])
def send_start(message):
    user = message.from_user
    track_user(user)
    if is_owner(user.id):
        set_owner_commands()
    if not entry_gate(message):
        return
    send_welcome(message.chat.id, user)

@bot.message_handler(commands=['menu'])
def send_menu(message):
    track_user(message.from_user)
    if not entry_gate(message):
        return
    try:
        bot.send_photo(message.chat.id, "https://i.ibb.co/QFPrdV53/IMG-20261004-175229-951.jpg")
    except Exception as e:
        print(f"[WELCOME PHOTO ERROR] {e}")

    bot.send_message(message.chat.id, get_dashboard_text(), parse_mode="Markdown", reply_markup=get_main_menu_keyboard(message.from_user.id))

@bot.message_handler(commands=['help', 'commands'])
def send_help(message):
    track_user(message.from_user)
    if not entry_gate(message):
        return
    uid = message.from_user.id
    bot.send_message(message.chat.id, get_help_text(uid), parse_mode="Markdown", reply_markup=get_main_menu_keyboard(uid))

@bot.message_handler(commands=['myid'])
def my_id(message):
    bot.reply_to(message, get_myid_text(message.from_user.id), parse_mode="Markdown")

# ----------------- SYSTEM INFO / VITALS -----------------

@bot.message_handler(commands=['status'])
def server_status(message):
    if not access_ok(message):
        return
    bot.reply_to(message, get_status_text(), parse_mode="Markdown", reply_markup=get_main_menu_keyboard(message.from_user.id))

@bot.message_handler(commands=['sysinfo'])
def sysinfo_cmd(message):
    if not access_ok(message):
        return
    bot.reply_to(message, get_vitals_text(), parse_mode="Markdown")

@bot.message_handler(commands=['memory'])
def memory_cmd(message):
    if not access_ok(message):
        return
    bot.reply_to(message, get_memory_text(), parse_mode="Markdown")

@bot.message_handler(commands=['disk'])
def disk_cmd(message):
    if not access_ok(message):
        return
    bot.reply_to(message, get_disk_text(), parse_mode="Markdown")

# ----------------- BACKGROUND ENGINES (RUN, PS, STOP) -----------------

@bot.message_handler(commands=['run'])
def run_bg(message):
    if not access_ok(message):
        return

    global current_dir
    cmd = message.text.replace('/run', '', 1).strip()
    if not cmd:
        bot.reply_to(message, "⚠️ *Format Error:*\nUse: `/run <command>` (e.g. `/run python app.py`)", parse_mode="Markdown")
        return

    try:
        # DEVNULL (not PIPE): nobody reads the pipe, so a chatty script would freeze once it filled up.
        proc = subprocess.Popen(cmd, shell=True, cwd=current_dir, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        bg_processes[proc.pid] = {'process': proc, 'cmd': cmd}
        bot.reply_to(
            message,
            f"🟢 *ENGINE STARTED*\n{DIV}\n\n⚙️ *PID:* `{proc.pid}`\n💻 *CMD:* `{code_safe(cmd)}`\n\n_Running in background..._ 🥷",
            parse_mode="Markdown"
        )
    except Exception as e:
        bot.reply_to(message, f"❌ *CRASH* Engine failed: {e}", parse_mode=None)

@bot.message_handler(commands=['ps'])
def list_ps(message):
    if not access_ok(message):
        return
    text, markup = get_engines_view()
    bot.reply_to(message, text, parse_mode="Markdown", reply_markup=markup)

@bot.message_handler(commands=['stop'])
def stop_ps(message):
    if not access_ok(message):
        return

    try:
        pid = int(message.text.split(" ")[1])
        if pid in bg_processes:
            bg_processes[pid]['process'].terminate()
            del bg_processes[pid]
            bot.reply_to(message, f"🛑 *ENGINE KILLED*\nPID `{pid}` terminated successfully! 💀", parse_mode="Markdown")
        else:
            bot.reply_to(message, "⚠️ *NOT FOUND*\nTarget PID does not exist in active processes.", parse_mode="Markdown")
    except Exception:
        bot.reply_to(message, "⚠️ *Format Error:*\nUse: `/stop <pid>`", parse_mode="Markdown")

# ----------------- FILE HOSTING (send a file → it loads and runs by itself) -----------------

HOST_DIR = os.path.abspath("hosted_files")
HOST_INDEX = os.path.join(HOST_DIR, "index.json")
MAX_UPLOAD = 20 * 1024 * 1024      # Telegram bots can only download files up to 20 MB
BOOT_WAIT = 2.5                    # seconds we watch a fresh script before calling it "running"
SPIN = "⠋⠙⠹⠸⠼⠴⠦⠧⠇⠏"

hosted = {}                        # file id -> info dict (one entry per uploaded file)
hosted_lock = threading.Lock()

# How each file type is started. Anything else is just stored (and can be downloaded again).
RUNNERS = {
    ".py": [sys.executable, "-u"],   # -u = unbuffered, so /log shows output instantly
    ".js": ["node"],
    ".sh": ["bash"],
}
SAVE_KEYS = ("fid", "uid", "name", "project", "dir", "path", "log", "size", "speed", "load_time", "created")


def build_cmd(name):
    """Command used to run a file, or None if this file type can't be run."""
    runner = RUNNERS.get(os.path.splitext(name)[1].lower())
    return (runner + [name]) if runner else None


# ---- small formatting helpers ----

def fmt_size(n):
    n = float(n or 0)
    for unit in ("B", "KB", "MB"):
        if n < 1024:
            return f"{int(n)} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024
    return f"{n:.1f} GB"

def fmt_dur(sec):
    sec = max(0.0, sec)
    if sec < 60:
        return f"{sec:.1f}s"
    sec = int(sec)
    h, rem = divmod(sec, 3600)
    m, s = divmod(rem, 60)
    return f"{h}h {m}m {s}s" if h else f"{m}m {s}s"

def spinner():
    return SPIN[int(time.time() * 8) % len(SPIN)]

def shuttle(size=12, width=4):
    """Little block that slides left-right — for steps where we don't know the length."""
    span = size - width
    pos = int(time.time() * 6) % (span * 2)
    if pos > span:
        pos = span * 2 - pos
    return "▱" * pos + "▰" * width + "▱" * (size - width - pos)

def block_safe(text):
    """Makes text safe inside a ``` code block."""
    return (text or "").replace("`", "'")


class LiveMsg:
    """Edits ONE Telegram message again and again (live animation) without hitting flood limits."""
    MIN_GAP = 0.9

    def __init__(self, chat_id, message_id, first_text=None):
        self.chat_id = chat_id
        self.message_id = message_id
        self.last_time = time.time()
        self.last_text = first_text

    def update(self, text, markup=None, force=False):
        if text == self.last_text and markup is None:
            return
        if not force and time.time() - self.last_time < self.MIN_GAP:
            return
        for _ in range(3):
            try:
                bot.edit_message_text(chat_id=self.chat_id, message_id=self.message_id, text=text,
                                      parse_mode="Markdown", reply_markup=markup)
                break
            except Exception as e:
                err = str(e)
                if "not modified" in err:
                    break
                if "Too Many Requests" in err or "429" in err:
                    m = re.search(r"retry after (\d+)", err)
                    time.sleep(min(int(m.group(1)) if m else 2, 10) + 0.5)
                    continue
                print(f"[!] Live edit failed: {e}")
                break
        self.last_time = time.time()
        self.last_text = text


# ---- loading screen ----

def stage_lines(stage, runnable, spin):
    names = ["📥 Receive", "💾 Save"] + (["🚀 Start"] if runnable else [])
    out = []
    for i, label in enumerate(names):
        if i < stage:
            out.append(f"✅ {label}")
        elif i == stage:
            out.append(f"{spin} {label}")
        else:
            out.append(f"▫️ {label}")
    return "\n".join(out)

def loading_text(name, stage, runnable, elapsed, done=0, total=0, speed=0.0, note=None):
    lines = [
        "⚡️ *LOADING FILE*", DIV, "",
        f"📄 `{code_safe(name, 40)}`", "",
        stage_lines(stage, runnable, spinner()), "",
    ]
    if stage == 0:
        if total:
            pct = min(100.0, done / total * 100)
            lines += [f"`{bar(pct, 12)}` *{pct:.0f}%*", f"📦 `{fmt_size(done)}` / `{fmt_size(total)}`"]
        else:
            lines += [f"`{shuttle()}`", f"📦 `{fmt_size(done)}`"]
        lines.append(f"⚡ `{fmt_size(speed)}/s`")
    elif stage == 1:
        lines += [f"`{bar(100, 12)}` *100%*", "💾 Writing to the server…"]
    else:
        lines += [f"`{shuttle()}`", f"📦 {note}" if note else "🚀 Booting your script…"]
    lines.append(f"⏱ `{fmt_dur(elapsed)}`")
    return "\n".join(lines)


# ---- registry (remembers uploaded files across restarts) ----

def new_fid():
    while True:
        fid = uuid.uuid4().hex[:6]
        if fid not in hosted:
            return fid

def save_hosted_index():
    try:
        with hosted_lock:
            data = {fid: {k: h.get(k) for k in SAVE_KEYS} for fid, h in hosted.items()}
        os.makedirs(HOST_DIR, exist_ok=True)
        tmp = HOST_INDEX + ".tmp"
        with open(tmp, "w") as f:
            json.dump(data, f)
        os.replace(tmp, HOST_INDEX)
    except Exception as e:
        print(f"[!] Could not save file index: {e}")

def load_hosted_index():
    if not os.path.exists(HOST_INDEX):
        return
    try:
        with open(HOST_INDEX, "r") as f:
            data = json.load(f)
    except Exception as e:
        print(f"[!] Could not read file index: {e}")
        return
    for fid, d in data.items():
        if d.get("path") and os.path.exists(d["path"]):
            d.update(cmd=build_cmd(d["name"]), proc=None, started_at=None,
                     stopped_by_user=False, start_error=None, busy=False)
            hosted[fid] = d


# ---- process control ----

def trim_log(path, keep=200_000, limit=1_000_000):
    """Keeps run.log from growing forever."""
    try:
        if os.path.getsize(path) > limit:
            with open(path, "rb") as f:
                f.seek(-keep, os.SEEK_END)
                tail = f.read()
            with open(path, "wb") as f:
                f.write(tail)
    except Exception:
        pass

def read_log_tail(path, chars=3000):
    try:
        with open(path, "rb") as f:
            f.seek(0, os.SEEK_END)
            size = f.tell()
            f.seek(max(0, size - chars * 4))
            data = f.read()
        return data.decode("utf-8", "replace")[-chars:].strip()
    except Exception:
        return ""

def start_process(h):
    """Starts the script, output goes to its own run.log. Returns None if OK, else an error text."""
    cmd = h.get("cmd")
    if not cmd:
        return "This file type can't be run."
    trim_log(h["log"])
    h["start_error"] = None
    try:
        with open(h["log"], "ab") as lg:
            lg.write(f"\n===== START {time.strftime('%Y-%m-%d %H:%M:%S')} =====\n".encode())
            lg.flush()
            proc = subprocess.Popen(cmd, cwd=h["dir"], stdin=subprocess.DEVNULL,
                                    stdout=lg, stderr=subprocess.STDOUT, start_new_session=True)
    except Exception as e:
        h["proc"] = None
        h["start_error"] = str(e)
        return str(e)
    h["proc"] = proc
    h["started_at"] = time.time()
    h["stopped_by_user"] = False
    bg_processes[proc.pid] = {"process": proc, "cmd": " ".join([os.path.basename(cmd[0])] + cmd[1:])}
    return None

def kill_hosted(h):
    p = h.get("proc")
    if not p:
        return
    if p.poll() is None:
        h["stopped_by_user"] = True
        for sig in (signal.SIGTERM, getattr(signal, "SIGKILL", signal.SIGTERM)):
            try:
                if hasattr(os, "killpg"):
                    os.killpg(os.getpgid(p.pid), sig)   # whole group, so child processes die too
                elif sig == signal.SIGTERM:
                    p.terminate()
                else:
                    p.kill()
            except Exception:
                try:
                    p.terminate()
                except Exception:
                    pass
            try:
                p.wait(timeout=3)
                break
            except subprocess.TimeoutExpired:
                continue
    bg_processes.pop(p.pid, None)

def boot_wait(h, render):
    """Watches a fresh process for BOOT_WAIT seconds (stops early if it dies) and animates meanwhile."""
    t0 = time.time()
    last = 0.0
    while time.time() - t0 < BOOT_WAIT:
        p = h.get("proc")
        if p is None or p.poll() is not None:
            break
        if time.time() - last >= 0.9:
            render()
            last = time.time()
        time.sleep(0.1)


# ---- cards & keyboards ----

def host_status(h):
    p = h.get("proc")
    if h.get("start_error"):
        return "💥 *Could not start*", False
    if p is None:
        return "⚪️ *Not running*", False
    rc = p.poll()
    if rc is None:
        return f"🟢 *Running* · PID `{p.pid}`", True
    if h.get("stopped_by_user"):
        return "🔴 *Stopped*", False
    if rc == 0:
        return "⚪️ *Finished* (exit 0)", False
    return f"💥 *Crashed* (exit `{rc}`)", False

def host_keyboard(h):
    fid = h["fid"]
    m = types.InlineKeyboardMarkup()
    if h.get("cmd"):
        m.row(IBtn("▶️ Run", style=SUCCESS, callback_data=f"h_run_{fid}"),
              IBtn("⏹ Stop", style=DANGER, callback_data=f"h_stop_{fid}"))
        m.row(IBtn("📜 Log", style=PRIMARY, callback_data=f"h_log_{fid}"),
              IBtn("🔄 Restart", style=PRIMARY, callback_data=f"h_re_{fid}"))
    m.row(IBtn("📥 Download", callback_data=f"h_dl_{fid}"),
          IBtn("🗑 Delete", style=DANGER, callback_data=f"h_delq_{fid}"))
    m.row(IBtn("🔃 Refresh", callback_data=f"h_card_{fid}"),
          IBtn("🏠 Home", style=PRIMARY, callback_data="btn_main_menu"))
    return m

def host_card(h, title="📄 *FILE PANEL*"):
    status, running = host_status(h)
    lines = [title, DIV, "",
             f"📄 *File:* `{code_safe(h['name'], 40)}`",
             f"📦 *Size:* `{fmt_size(h.get('size'))}`"]
    if h.get("project"):
        lines.insert(3, f"📁 *Project:* `{code_safe(h['project'], 30)}`")
    if h.get("speed"):
        lines.append(f"⚡ *Speed:* `{fmt_size(h['speed'])}/s`")
    if h.get("load_time") is not None:
        lines.append(f"⏱ *Loaded in:* `{fmt_dur(h['load_time'])}`")
    lines.append(f"🆔 *ID:* `{h['fid']}`")
    lines += ["", DIV, f"🔰 *Status:* {status}"]
    if running and h.get("started_at"):
        lines.append(f"⏳ *Up:* `{fmt_dur(time.time() - h['started_at'])}`")
    if not h.get("cmd"):
        lines.append("📁 _Stored only — this file type can't be run._")
    if h.get("start_error"):
        lines += ["", f"```\n{block_safe(code_safe(h['start_error'], 300))}\n```"]
    elif h.get("cmd") and h.get("proc") is not None and not running and not h.get("stopped_by_user"):
        if h["proc"].poll() not in (None, 0):          # crashed → show the last lines right here
            tail = read_log_tail(h["log"], 700)
            if tail:
                lines += ["", f"```\n{block_safe(tail)}\n```"]
    return "\n".join(lines), host_keyboard(h)

def log_view(h):
    tail = read_log_tail(h["log"], 3000)
    body = block_safe(tail) if tail else "(no output yet)"
    text = f"📜 *LOG* — `{code_safe(h['name'], 30)}`\n{DIV}\n```\n{body}\n```"
    m = types.InlineKeyboardMarkup()
    m.row(IBtn("🔃 Refresh", style=PRIMARY, callback_data=f"h_log_{h['fid']}"),
          IBtn("📄 Full Log", callback_data=f"h_flog_{h['fid']}"))
    m.row(IBtn("⬅️ Back", callback_data=f"h_card_{h['fid']}"),
          IBtn("🏠 Home", style=PRIMARY, callback_data="btn_main_menu"))
    return text, m

def files_view(user_id):
    mine = [h for h in hosted.values() if h["uid"] == user_id or is_owner(user_id)]
    mine.sort(key=lambda h: h.get("created", 0), reverse=True)
    m = types.InlineKeyboardMarkup(row_width=1)
    if not mine:
        text = f"📂 *MY FILES*\n{DIV}\n\nNothing here yet.\nSend me a `.py` file and I'll run it for you 🚀"
    else:
        text = f"📂 *MY FILES* ({len(mine)})\n{DIV}\n\n_Tap a file to open its panel_ 👇"
        for h in mine[:15]:
            _, running = host_status(h)
            icon = "🟢" if running else ("📁" if not h.get("cmd") else "⚪️")
            m.add(IBtn(f"{icon} {(h['project'] + '/') if h.get('project') else ''}{h['name']}"[:40], callback_data=f"h_card_{h['fid']}"))
    m.row(IBtn("📤 Upload File", style=SUCCESS, callback_data="btn_upload"),
          IBtn("🏠 Home", style=PRIMARY, callback_data="btn_main_menu"))
    return text, m

def upload_prompt_text():
    return (
        f"📤 *UPLOAD FILE*\n{DIV}\n\n"
        f"Send me your file now 👇\n"
        f"_I'll ask for a *project name* first — all files go inside it._\n\n"
        f"🚀 `.py` `.js` `.sh` — loads and *runs by itself*\n"
        f"📦 `requirements.txt` — optional, any order. If you skip it, I install the packages by myself.\n"
        f"📁 Other files — stored safely, download any time\n\n"
        f"_Max size: 20 MB_"
    )


# ---- the upload pipeline ----

@bot.message_handler(content_types=['document'])
def handle_upload(message):
    if not access_ok(message):
        return
    uid = message.from_user.id
    proj = get_active_project(uid)
    if proj:
        # a project is already open -> file goes straight into it
        threading.Thread(target=host_pipeline, args=(message, proj), daemon=True).start()
        return
    # no project yet -> ask for the project name first, keep the file(s) waiting
    with pending_lock:
        pending_uploads.setdefault(uid, []).append(message)
        first = uid not in waiting_for_project_name
        waiting_for_project_name.add(uid)
    if first:
        bot.reply_to(message, project_prompt_text(), parse_mode="Markdown")

def project_prompt_text():
    return (
        f"📁 *PROJECT NAME*\n{DIV}\n\n"
        f"What should I call this project?\n"
        f"Send a short name 👇\n\n"
        f"_All your files (and `requirements.txt`, in any order) go inside this project._\n"
        f"_/cancel to stop._"
    )

def clean_project_name(text):
    n = re.sub(r"[^\w\- \u0B80-\u0BFF]+", "", text or "", flags=re.UNICODE).strip()
    n = re.sub(r"\s+", "_", n)[:40]
    return n or "project"

def get_active_project(uid):
    ap = active_project.get(uid)
    if ap and time.time() - ap["ts"] < PROJECT_IDLE:
        ap["ts"] = time.time()
        return ap
    active_project.pop(uid, None)
    return None

def set_active_project(uid, pname):
    pdir = os.path.join(HOST_DIR, str(uid), "proj_" + pname)
    os.makedirs(pdir, exist_ok=True)
    ap = {"name": pname, "dir": pdir, "ts": time.time()}
    active_project[uid] = ap
    return ap

@bot.message_handler(
    func=lambda m: m.from_user.id in waiting_for_project_name and m.text is not None
                   and not m.text.startswith("/") and m.text not in MENU_TEXTS,
    content_types=['text']
)
def capture_project_name(message):
    uid = message.from_user.id
    pname = clean_project_name(message.text)
    with pending_lock:
        waiting_for_project_name.discard(uid)
        queued = pending_uploads.pop(uid, [])
    proj = set_active_project(uid, pname)
    bot.reply_to(
        message,
        f"📁 *PROJECT READY:* `{code_safe(pname, 40)}`\n{DIV}\n\n"
        f"Loading {len(queued)} file(s) into it…\n"
        f"_More files you send in the next 10 min go into this project too. /newproject for another one._",
        parse_mode="Markdown"
    )
    # requirements.txt first (if it came along), then the rest — one after another
    queued.sort(key=lambda m: 0 if (m.document.file_name or "").lower() in REQ_NAMES else 1)
    def work():
        for m in queued:
            try:
                host_pipeline(m, proj)
            except Exception as e:
                print(f"[!] pipeline error: {e}")
    threading.Thread(target=work, daemon=True).start()

@bot.message_handler(commands=['newproject'])
def newproject_cmd(message):
    if not access_ok(message):
        return
    active_project.pop(message.from_user.id, None)
    bot.reply_to(message, "🆕 *NEW PROJECT*\nSend your file — I'll ask for its project name. 📁", parse_mode="Markdown")

REQ_NAMES = ("requirements.txt", "requirement.txt")

# import name -> pip package name (only where they differ)
PIP_MAP = {
    "telebot": "pyTelegramBotAPI", "cv2": "opencv-python", "PIL": "Pillow", "bs4": "beautifulsoup4",
    "yaml": "PyYAML", "sklearn": "scikit-learn", "dotenv": "python-dotenv", "telegram": "python-telegram-bot",
    "dateutil": "python-dateutil", "Crypto": "pycryptodome", "serial": "pyserial", "jwt": "PyJWT",
    "nacl": "PyNaCl", "git": "GitPython", "discord": "discord.py", "attr": "attrs",
    "OpenSSL": "pyOpenSSL", "magic": "python-magic", "docx": "python-docx", "pptx": "python-pptx",
    "fitz": "PyMuPDF", "skimage": "scikit-image", "zmq": "pyzmq", "MySQLdb": "mysqlclient",
    "psycopg2": "psycopg2-binary", "socks": "PySocks", "googleapiclient": "google-api-python-client",
    "flask_cors": "Flask-Cors", "flask_sqlalchemy": "Flask-SQLAlchemy", "Levenshtein": "python-Levenshtein",
}
deps_done = {}   # project dir -> mtime of the requirements.txt we already installed

def pip_install(args, cwd):
    # returns (ok, last lines of output)
    try:
        r = subprocess.run([sys.executable, "-m", "pip", "install", "--no-input", "--disable-pip-version-check"] + list(args),
                           cwd=cwd, capture_output=True, text=True, timeout=600)
        out = ((r.stdout or "") + (r.stderr or "")).strip()[-600:]
        return r.returncode == 0, out
    except Exception as e:
        return False, str(e)

def missing_imports(path, pdir):
    # reads the script, finds every `import x` that is not installed → returns pip package names
    try:
        with open(path, "r", encoding="utf-8", errors="replace") as f:
            tree = ast.parse(f.read())
    except Exception:
        return []
    mods = set()
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                mods.add(a.name.split(".")[0])
        elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
            mods.add(node.module.split(".")[0])
    try:
        local = {os.path.splitext(x)[0] for x in os.listdir(pdir)}
    except Exception:
        local = set()
    std = getattr(sys, "stdlib_module_names", set())
    need = []
    for m in sorted(mods):
        if m in std or m in local or m.startswith("_"):
            continue
        try:
            if importlib.util.find_spec(m):
                continue
        except Exception:
            pass
        pkg = PIP_MAP.get(m, m)
        if pkg not in need:
            need.append(pkg)
    return need

def ensure_packages(h):
    # requirements.txt in the project → use it. Otherwise → install whatever the script imports.
    d = h["dir"]
    req = os.path.join(d, "requirements.txt")
    if os.path.exists(req):
        mt = os.path.getmtime(req)
        if deps_done.get(d) != mt:
            ok, _ = pip_install(["-r", req], d)
            if ok:
                deps_done[d] = mt
        return
    need = missing_imports(h["path"], d)
    if need:
        ok, _ = pip_install(need, d)
        if not ok:
            for pkg in need:
                pip_install([pkg], d)

def missing_module(log):
    found = re.findall(r"No module named '([\w\.]+)'", read_log_tail(log, 2000))
    return found[-1].split(".")[0] if found else None

def start_with_deps(h, render):
    # installs packages automatically, starts the script, and if it dies with
    # "No module named X" it installs X and starts again (max 4 tries)
    is_py = h["name"].lower().endswith(".py")
    if is_py:
        render("Checking packages…")
        ensure_packages(h)
    tried = set()
    for _ in range(4):
        err = start_process(h)
        if err:
            return err
        boot_wait(h, lambda: render(None))
        rc = h["proc"].poll()
        if not is_py or rc is None or rc == 0:
            return None
        mod = missing_module(h["log"])
        if not mod or mod in tried:
            return None
        tried.add(mod)
        render(f"Installing {mod}…")
        ok, _ = pip_install([PIP_MAP.get(mod, mod)], h["dir"])
        if not ok:
            return None
    return None

def remove_hosted(h):
    kill_hosted(h)
    for p in (h.get("path"), h.get("log")):
        try:
            if p and os.path.exists(p):
                os.remove(p)
        except Exception:
            pass
    with hosted_lock:
        hosted.pop(h["fid"], None)
        others = [x for x in hosted.values() if x.get("dir") == h["dir"]]
    if not others:
        shutil.rmtree(h["dir"], ignore_errors=True)
        for uid_, ap in list(active_project.items()):
            if ap["dir"] == h["dir"]:
                active_project.pop(uid_, None)
    save_hosted_index()

def handle_requirements_file(proj, live, req_path, name):
    live.update(f"📦 *INSTALLING PACKAGES*\n{DIV}\n\nProject `{code_safe(proj['name'], 30)}` … please wait", force=True)
    ok, out = pip_install(["-r", req_path], proj["dir"])
    if not ok:
        live.update(f"❌ *INSTALL FAILED*\n{DIV}\n\n`{code_safe(out, 500)}`", force=True)
        return
    deps_done[proj["dir"]] = os.path.getmtime(req_path)
    with hosted_lock:
        targets = [x for x in hosted.values() if x.get("dir") == proj["dir"] and x.get("cmd")
                   and x.get("proc") is not None and not x.get("stopped_by_user")]
    if not targets:
        live.update(f"✅ *PACKAGES INSTALLED*\n{DIV}\n\nNow send your script — it starts by itself 🚀", force=True)
        return
    for t in targets:
        kill_hosted(t)
        if not start_process(t):
            boot_wait(t, lambda: None)
    text, markup = host_card(targets[0], "✅ *PACKAGES INSTALLED & RESTARTED*")
    live.update(text, markup, force=True)

def host_pipeline(message, proj):
    uid = message.from_user.id
    chat_id = message.chat.id
    doc = message.document
    name = os.path.basename(doc.file_name or "file").replace("\x00", "").strip()
    if name in ("", ".", ".."):
        name = "file"
    is_req = name.lower() in REQ_NAMES
    if is_req:
        name = "requirements.txt"
    total = doc.file_size or 0
    cmd = build_cmd(name)
    runnable = cmd is not None
    t0 = time.time()

    first = loading_text(name, 0, runnable, 0, 0, total)
    try:
        sent = bot.reply_to(message, first, parse_mode="Markdown")
    except Exception as e:
        print(f"[!] Could not start upload screen: {e}")
        return
    live = LiveMsg(chat_id, sent.message_id, first)

    if total > MAX_UPLOAD:
        live.update(f"❌ *TOO BIG*\n{DIV}\n\n`{fmt_size(total)}` is over the 20 MB limit Telegram gives bots.", force=True)
        return

    fid = new_fid()
    fdir = proj["dir"]
    path = os.path.join(fdir, name)

    # same file name uploaded again in this project → replace the old one
    with hosted_lock:
        olds = [x for x in hosted.values() if x.get("dir") == fdir and x.get("name") == name]
    for old in olds:
        kill_hosted(old)
        with hosted_lock:
            hosted.pop(old["fid"], None)

    # 1) receive — real progress, read straight from Telegram in chunks
    try:
        url = bot.get_file_url(doc.file_id)
        os.makedirs(fdir, exist_ok=True)
        done = 0
        t_dl = time.time()
        with requests.get(url, stream=True, timeout=(10, 60)) as r:
            r.raise_for_status()
            with open(path, "wb") as f:
                for chunk in r.iter_content(64 * 1024):
                    if not chunk:
                        continue
                    f.write(chunk)
                    done += len(chunk)
                    speed = done / max(time.time() - t_dl, 0.001)
                    live.update(loading_text(name, 0, runnable, time.time() - t0, done, total, speed))
        speed = done / max(time.time() - t_dl, 0.001)
    except Exception as e:
        try:
            os.remove(path)
        except Exception:
            pass
        live.update(f"❌ *UPLOAD FAILED*\n{DIV}\n\n`{code_safe(str(e), 200)}`", force=True)
        return

    # 2) save
    live.update(loading_text(name, 1, runnable, time.time() - t0, done, total, speed), force=True)

    if is_req:
        handle_requirements_file(proj, live, path, name)
        return

    h = {"fid": fid, "uid": uid, "name": name, "project": proj["name"], "dir": fdir, "path": path,
         "log": os.path.join(fdir, name + ".log"), "cmd": cmd, "size": done, "speed": speed,
         "load_time": time.time() - t0, "created": int(time.time()),
         "proc": None, "started_at": None, "stopped_by_user": False, "start_error": None, "busy": False}
    with hosted_lock:
        hosted[fid] = h
    save_hosted_index()

    if not runnable:
        text, markup = host_card(h, "✅ *LOAD SUCCESS*")
        live.update(text, markup, force=True)
        return

    # 3) start — packages are installed automatically, then it just runs
    def render(note=None):
        live.update(loading_text(name, 2, True, time.time() - t0, done, total, speed, note), force=bool(note))
    live.update(loading_text(name, 2, True, time.time() - t0, done, total, speed), force=True)
    start_with_deps(h, render)
    _, running = host_status(h)
    title = "✅ *LOAD SUCCESS*" if running else "⚠️ *LOADED — BUT THE SCRIPT STOPPED*"
    text, markup = host_card(h, title)
    live.update(text, markup, force=True)

def run_and_animate(chat_id, message_id, fid, restart=False):
    """Used by the Run / Restart buttons: live 'starting' animation, then the file panel again."""
    h = hosted.get(fid)
    if not h:
        return
    live = LiveMsg(chat_id, message_id)
    t0 = time.time()

    def starting():
        return "\n".join([
            "🚀 *STARTING ENGINE*", DIV, "",
            f"📄 `{code_safe(h['name'], 40)}`", "",
            f"{spinner()} Booting…", f"`{shuttle()}`",
            f"⏱ `{fmt_dur(time.time() - t0)}`",
        ])

    try:
        live.update(starting(), force=True)
        if restart:
            kill_hosted(h)
        start_with_deps(h, lambda note=None: live.update(
            starting() if not note else f"📦 *{note}*\n{DIV}\n\n`{shuttle()}`", force=bool(note)))
        text, markup = host_card(h)
        live.update(text, markup, force=True)
    finally:
        h["busy"] = False


# ---- button presses ----

def handle_host_callback(call):
    uid = call.from_user.id
    data = call.data
    chat_id = call.message.chat.id
    mid = call.message.message_id

    if data == "btn_upload":
        bot.answer_callback_query(call.id)
        bot.send_message(chat_id, upload_prompt_text(), parse_mode="Markdown")
        return
    if data == "btn_files":
        text, markup = files_view(uid)
        edit(call, text, markup)
        bot.answer_callback_query(call.id)
        return

    parts = data.split("_", 2)
    if len(parts) != 3:
        bot.answer_callback_query(call.id)
        return
    _, action, fid = parts
    h = hosted.get(fid)
    if not h:
        bot.answer_callback_query(call.id, "⚠️ File not found — maybe it was deleted.", show_alert=True)
        return
    if h["uid"] != uid and not is_owner(uid):
        bot.answer_callback_query(call.id, "⛔ This file belongs to someone else.", show_alert=True)
        return

    _, running = host_status(h)

    if action == "card":
        text, markup = host_card(h)
        edit(call, text, markup)
        bot.answer_callback_query(call.id, "🔃 Updated")

    elif action in ("run", "re"):
        if h.get("busy"):
            bot.answer_callback_query(call.id, "⏳ Please wait a moment…")
        elif action == "run" and running:
            bot.answer_callback_query(call.id, "🟢 Already running!")
        else:
            h["busy"] = True
            bot.answer_callback_query(call.id, "🚀 Starting…" if action == "run" else "🔄 Restarting…")
            threading.Thread(target=run_and_animate, args=(chat_id, mid, fid, action == "re"), daemon=True).start()

    elif action == "stop":
        if running:
            kill_hosted(h)
            bot.answer_callback_query(call.id, "🛑 Stopped")
        else:
            bot.answer_callback_query(call.id, "Not running right now.")
        text, markup = host_card(h)
        edit(call, text, markup)

    elif action == "log":
        text, markup = log_view(h)
        edit(call, text, markup)
        bot.answer_callback_query(call.id, "📜 Log")

    elif action == "flog":
        if os.path.exists(h["log"]) and os.path.getsize(h["log"]) > 0:
            with open(h["log"], "rb") as f:
                bot.send_document(chat_id, f, visible_file_name=f"{h['name']}.log")
            bot.answer_callback_query(call.id)
        else:
            bot.answer_callback_query(call.id, "Log is empty.", show_alert=True)

    elif action == "dl":
        try:
            with open(h["path"], "rb") as f:
                bot.send_document(chat_id, f, visible_file_name=h["name"])
            bot.answer_callback_query(call.id, "📥 Sent")
        except Exception as e:
            bot.answer_callback_query(call.id, f"Failed: {str(e)[:150]}", show_alert=True)

    elif action == "delq":
        m = types.InlineKeyboardMarkup()
        m.row(IBtn("✅ Yes, delete", style=DANGER, callback_data=f"h_del_{fid}"),
              IBtn("❌ Cancel", style=PRIMARY, callback_data=f"h_card_{fid}"))
        edit(call, f"🗑 *DELETE FILE?*\n{DIV}\n\n`{code_safe(h['name'], 40)}`\n\n"
                   f"The file, its log and the running script will be removed. This can't be undone.", m)
        bot.answer_callback_query(call.id)

    elif action == "del":
        remove_hosted(h)
        m = types.InlineKeyboardMarkup()
        m.row(IBtn("📂 My Files", callback_data="btn_files"), IBtn("🏠 Home", style=PRIMARY, callback_data="btn_main_menu"))
        edit(call, f"🗑 *DELETED*\n{DIV}\n\n`{code_safe(h['name'], 40)}` has been removed.", m)
        bot.answer_callback_query(call.id, "🗑 Deleted")

    else:
        bot.answer_callback_query(call.id)

@bot.message_handler(commands=['upload'])
def upload_cmd(message):
    if not access_ok(message):
        return
    bot.reply_to(message, upload_prompt_text(), parse_mode="Markdown")

@bot.message_handler(commands=['files'])
def files_cmd(message):
    if not access_ok(message):
        return
    text, markup = files_view(message.from_user.id)
    bot.reply_to(message, text, parse_mode="Markdown", reply_markup=markup)

# ----------------- FILE OPERATIONS -----------------

@bot.message_handler(commands=['download'])
def download_file(message):
    if not access_ok(message):
        return

    global current_dir
    filename = message.text.replace('/download', '', 1).strip()
    if not filename:
        bot.reply_to(message, "⚠️ *Usage:* `/download <filename>`", parse_mode="Markdown")
        return

    filepath = os.path.join(current_dir, filename)
    if os.path.exists(filepath) and os.path.isfile(filepath):
        bot.reply_to(message, "📥 *EXTRACTING*\nTransmitting file... ⏳", parse_mode="Markdown")
        try:
            with open(filepath, 'rb') as f:
                bot.send_document(message.chat.id, f)
        except Exception as e:
            bot.reply_to(message, f"❌ Failed to send file: {e}")
    else:
        bot.reply_to(message, "❌ *404* File not found in current directory! 🔍", parse_mode="Markdown")

# ----------------- BOTTOM KEYBOARD BUTTONS -----------------
# Must stay ABOVE the terminal handler, otherwise button texts would be run as shell commands.

@bot.message_handler(func=lambda message: message.text in MENU_TEXTS)
def handle_menu_buttons(message):
    uid = message.from_user.id
    text = message.text

    if text == BTN_ADMIN:
        if not is_owner(uid):
            bot.reply_to(message, "💀 *[ACCESS DENIED]* Owner only.", parse_mode="Markdown")
            return
        show_admin_panel(message.chat.id)
        return

    if not access_ok(message):
        return

    if text == BTN_UPLOAD:
        bot.send_message(message.chat.id, upload_prompt_text(), parse_mode="Markdown")
    elif text == BTN_FILES:
        view_text, markup = files_view(uid)
        bot.send_message(message.chat.id, view_text, parse_mode="Markdown", reply_markup=markup)
    elif text == BTN_STATUS:
        bot.send_message(message.chat.id, get_status_text(), parse_mode="Markdown")
    elif text == BTN_VITALS:
        bot.send_message(message.chat.id, get_vitals_text(), parse_mode="Markdown")
    elif text == BTN_RAM:
        bot.send_message(message.chat.id, get_memory_text(), parse_mode="Markdown")
    elif text == BTN_DISK:
        bot.send_message(message.chat.id, get_disk_text(), parse_mode="Markdown")
    elif text == BTN_ENGINES:
        view_text, markup = get_engines_view()
        bot.send_message(message.chat.id, view_text, parse_mode="Markdown", reply_markup=markup)
    elif text == BTN_MYID:
        bot.send_message(message.chat.id, get_myid_text(uid), parse_mode="Markdown")
    elif text == BTN_HELP:
        bot.send_message(message.chat.id, get_help_text(uid), parse_mode="Markdown")

# ----------------- DIRECT TERMINAL COMMANDS -----------------

@bot.message_handler(func=lambda message: message.text is not None and not message.text.startswith('/'))
def direct_terminal(message):
    if not access_ok(message):
        return

    global current_dir
    cmd = message.text.strip()

    if cmd.startswith("cd "):
        new_dir = cmd[3:].strip()
        target_path = os.path.abspath(os.path.join(current_dir, new_dir))
        if os.path.exists(target_path) and os.path.isdir(target_path):
            current_dir = target_path
            bot.reply_to(message, f"📂 *DIR CHANGED*\nNow in:\n`{code_safe(current_dir, 200)}` ⚡️", parse_mode="Markdown")
        else:
            bot.reply_to(message, "❌ *404* Directory does not exist!", parse_mode="Markdown")
        return

    try:
        bot.send_chat_action(message.chat.id, 'typing')
        result = subprocess.check_output(cmd, shell=True, text=True, stderr=subprocess.STDOUT, cwd=current_dir)

        if not result.strip():
            bot.reply_to(message, "✅ *EXECUTED*\nCommand succeeded with empty output. 🥷", parse_mode="Markdown")
        else:
            if len(result) > 4000:
                out_path = "output.txt"
                with open(out_path, "w", encoding="utf-8") as f:
                    f.write(result)
                with open(out_path, "rb") as f:
                    bot.send_document(message.chat.id, f, caption="⚠️ Output is too long — sent as a file.")
            else:
                bot.reply_to(message, f"```\n{result.replace('```', chr(39) * 3)}\n```", parse_mode="Markdown")
    except subprocess.CalledProcessError as e:
        out = (e.output or "").replace('```', chr(39) * 3)
        if len(out) > 3900:
            out = out[-3900:]
        bot.reply_to(message, f"🛑 *COMMAND ERROR*\n```\n{out}\n```", parse_mode="Markdown")
    except Exception as e:
        bot.reply_to(message, f"❌ *SYSTEM ERROR*: {e}", parse_mode=None)

# ----------------- INLINE CALLBACK HANDLERS -----------------

@bot.callback_query_handler(func=lambda call: True)
def handle_callbacks(call):
    user_id = call.from_user.id
    data = call.data

    # 1. Verification of Channel Subscriptions
    if data == "verify_membership":
        is_all_joined, missing = check_channel_subscriptions(user_id)
        if is_all_joined:
            if is_allowed_user(user_id):
                bot.answer_callback_query(call.id, "✅ Verified! Welcome back.")
                edit(call, "✅ *VERIFIED*\n\nAll channels joined — you're good to go! 🚀")
                send_welcome(call.message.chat.id, call.from_user)
            else:
                bot.answer_callback_query(call.id, "✅ All channels verified!")
                edit(call, get_locked_text(call.from_user, joined=True), get_request_access_keyboard())
        else:
            bot.answer_callback_query(call.id, f"❌ You still have {len(missing)} channel(s) left to join!", show_alert=True)
            try:
                bot.edit_message_reply_markup(
                    chat_id=call.message.chat.id,
                    message_id=call.message.message_id,
                    reply_markup=get_join_channels_keyboard(missing)
                )
            except Exception:
                pass
        return

    # 2. User Sends Auth Request to Admin
    if data == "send_auth_request":
        is_all_joined, missing = check_channel_subscriptions(user_id)
        if not is_all_joined:
            bot.answer_callback_query(call.id, "❌ You must join all channels first!", show_alert=True)
            return

        if is_allowed_user(user_id):
            bot.answer_callback_query(call.id, "✅ You are already authorized!")
            edit(call, "✅ *You already have access!*\n\nSend /start to open your dashboard.")
            send_welcome(call.message.chat.id, call.from_user)
            return

        if user_id in pending_requests:
            bot.answer_callback_query(call.id, "⏳ Your request is already with the Admin.", show_alert=True)
            return

        track_user(call.from_user)

        # Sanitize names to prevent Markdown parse error
        raw_full_name = f"{call.from_user.first_name} {call.from_user.last_name or ''}".strip()
        safe_full_name = escape_markdown(raw_full_name)

        if call.from_user.username:
            safe_username = "@" + escape_markdown(call.from_user.username)
        else:
            safe_username = "None"

        admin_markup = types.InlineKeyboardMarkup(row_width=2)
        admin_markup.add(
            IBtn("✅ Allow", style=SUCCESS, callback_data=f"auth_allow_{user_id}"),
            IBtn("❌ Deny", style=DANGER, callback_data=f"auth_deny_{user_id}")
        )

        channels_count = len(bot_config.get("required_channels", []))
        admin_text = (
            f"🔔 *NEW ACCESS REQUEST*\n"
            f"{DIV}\n\n"
            f"👤 *Name:* {safe_full_name}\n"
            f"🔗 *Username:* {safe_username}\n"
            f"🆔 *User ID:* `{user_id}`\n"
            f"📢 *Channels:* Joined all `{channels_count}` ✅\n\n"
            f"Grant terminal access to this user?"
        )
        user_wait_text = (
            "⏳ *REQUEST SENT*\n\n"
            "Your request is with the Admin now.\n"
            "You'll get a message here as soon as it's approved! 🚀"
        )

        try:
            for owner_id in OWNER_IDS:
                bot.send_message(owner_id, admin_text, parse_mode="Markdown", reply_markup=admin_markup)
        except Exception:
            # Fallback to plain text if Markdown still hits a formatting conflict
            try:
                plain_text = (
                    f"🔔 NEW ACCESS REQUEST\n\n"
                    f"Name: {raw_full_name}\n"
                    f"Username: @{call.from_user.username if call.from_user.username else 'None'}\n"
                    f"User ID: {user_id}\n"
                    f"Channels: Joined all {channels_count}\n\n"
                    f"Grant terminal access to this user?"
                )
                for owner_id in OWNER_IDS:
                    bot.send_message(owner_id, plain_text, reply_markup=admin_markup)
            except Exception as e2:
                bot.answer_callback_query(call.id, f"Error reaching Admin: {e2}", show_alert=True)
                return

        pending_requests.add(user_id)
        bot.answer_callback_query(call.id, "📨 Request sent to Admin!")
        edit(call, user_wait_text)
        return

    # 3. Admin Decision: ALLOW
    if data.startswith("auth_allow_"):
        if not is_owner(user_id):
            bot.answer_callback_query(call.id, "⛔ Owner only.", show_alert=True)
            return
        target_uid = int(data.replace("auth_allow_", ""))
        allowed_users.add(target_uid)
        save_users(allowed_users)
        pending_requests.discard(target_uid)

        bot.answer_callback_query(call.id, f"User {target_uid} approved!")
        try:
            bot.edit_message_text(
                chat_id=call.message.chat.id,
                message_id=call.message.message_id,
                text=call.message.text + f"\n\n🟢 DECISION: Allowed on {time.strftime('%Y-%m-%d %H:%M:%S')}"
            )
        except Exception:
            pass

        try:
            bot.send_message(
                target_uid,
                "🎉 *ACCESS APPROVED*\n\nThe Admin approved your request — you now have full terminal access.\nYour keyboard is ready below 👇",
                parse_mode="Markdown",
                reply_markup=get_reply_keyboard(target_uid)
            )
        except Exception as e:
            print(f"[!] Notification to user {target_uid} failed: {e}")
        return

    # 4. Admin Decision: DENY
    if data.startswith("auth_deny_"):
        if not is_owner(user_id):
            bot.answer_callback_query(call.id, "⛔ Owner only.", show_alert=True)
            return
        target_uid = int(data.replace("auth_deny_", ""))
        pending_requests.discard(target_uid)

        bot.answer_callback_query(call.id, f"User {target_uid} denied.")
        try:
            bot.edit_message_text(
                chat_id=call.message.chat.id,
                message_id=call.message.message_id,
                text=call.message.text + f"\n\n🔴 DECISION: Denied on {time.strftime('%Y-%m-%d %H:%M:%S')}"
            )
        except Exception:
            pass

        try:
            bot.send_message(target_uid, "🚫 *ACCESS DENIED*\nThe Admin has rejected your request.", parse_mode="Markdown")
        except Exception:
            pass
        return

    # ----------------- OWNER-ONLY ACTIONS -----------------
    owner_actions = (
        "adm_panel", "btn_channel_info", "add_new_channel_btn", "cancel_channel_setup",
        "adm_broadcast", "bc_cancel", "bc_confirm"
    )
    if data in owner_actions or data.startswith(("adm_users_", "adm_rm_", "del_ch_")):
        if not is_owner(user_id):
            bot.answer_callback_query(call.id, "⛔ Owner only.", show_alert=True)
            return

        chat_id = call.message.chat.id
        msg_id = call.message.message_id

        if data == "adm_panel":
            waiting_for_broadcast.discard(user_id)
            bot.answer_callback_query(call.id)
            show_admin_panel(chat_id, msg_id)

        elif data.startswith("adm_users_"):
            try:
                page = int(data.replace("adm_users_", ""))
            except ValueError:
                page = 0
            bot.answer_callback_query(call.id)
            show_users_manager(chat_id, msg_id, page)

        elif data.startswith("adm_rm_"):
            try:
                _, _, uid_s, page_s = data.split("_")
                target = int(uid_s)
                page = int(page_s)
            except ValueError:
                bot.answer_callback_query(call.id)
                return
            if target in OWNER_IDS:
                bot.answer_callback_query(call.id, "👑 You can't remove the owner.", show_alert=True)
                return
            if target in allowed_users:
                allowed_users.discard(target)
                save_users(allowed_users)
                bot.answer_callback_query(call.id, "🗑 Access removed")
            else:
                bot.answer_callback_query(call.id, "User already removed.")
            show_users_manager(chat_id, msg_id, page)

        elif data == "adm_broadcast":
            waiting_for_broadcast.add(user_id)
            bot.answer_callback_query(call.id)
            safe_edit(chat_id, msg_id, broadcast_prompt_text(), broadcast_cancel_keyboard())

        elif data == "bc_cancel":
            waiting_for_broadcast.discard(user_id)
            pending_broadcast.pop(user_id, None)
            bot.answer_callback_query(call.id, "Cancelled")
            safe_edit(chat_id, msg_id, "❌ *Broadcast cancelled.*", get_admin_back_keyboard())

        elif data == "bc_confirm":
            if user_id not in pending_broadcast:
                bot.answer_callback_query(call.id, "Nothing to send.", show_alert=True)
                return
            bot.answer_callback_query(call.id, "📤 Sending...")
            safe_edit(chat_id, msg_id, "📤 *Sending broadcast...*\n_Please wait_")
            threading.Thread(target=run_broadcast, args=(user_id, chat_id, msg_id), daemon=True).start()

        elif data == "btn_channel_info":
            bot.answer_callback_query(call.id)
            show_channel_manager(chat_id, msg_id)

        elif data == "add_new_channel_btn":
            current_count = len(bot_config.get("required_channels", []))
            if current_count >= MAX_CHANNELS:
                bot.answer_callback_query(call.id, f"Limit reached ({MAX_CHANNELS} channels maximum).", show_alert=True)
                return
            waiting_for_channel_forward.add(user_id)
            text = (
                f"📢 *ADD CHANNEL* ({current_count}/{MAX_CHANNELS})\n"
                f"{DIV}\n\n"
                f"Make sure the bot is *admin* in the channel.\n"
                f"Now *forward any post from that channel* here.\n\n"
                f"_Send /cancel to stop._"
            )
            markup = types.InlineKeyboardMarkup()
            markup.add(IBtn("❌ Cancel", style=DANGER, callback_data="cancel_channel_setup"))
            safe_edit(chat_id, msg_id, text, markup)
            bot.answer_callback_query(call.id)

        elif data.startswith("del_ch_"):
            target_ch_id = int(data.replace("del_ch_", ""))
            channels = bot_config.get("required_channels", [])
            bot_config["required_channels"] = [c for c in channels if c.get("id") != target_ch_id]
            save_config(bot_config)
            bot.answer_callback_query(call.id, "Channel removed!")
            show_channel_manager(chat_id, msg_id)

        elif data == "cancel_channel_setup":
            waiting_for_channel_forward.discard(user_id)
            bot.answer_callback_query(call.id)
            safe_edit(chat_id, msg_id, "❌ *Channel setup cancelled.*", get_admin_back_keyboard())
        return

    # Check authorization for other controls
    if not is_allowed_user(user_id):
        bot.answer_callback_query(call.id, "⛔ Access denied. Unauthorized.", show_alert=True)
        return

    is_all_joined, missing = check_channel_subscriptions(user_id)
    if not is_all_joined:
        bot.answer_callback_query(call.id, "⚠️ Channel membership required!", show_alert=True)
        return

    # File hosting buttons (Run / Stop / Log / Restart / Delete ...)
    if data.startswith("h_") or data in ("btn_upload", "btn_files"):
        handle_host_callback(call)
        return

    # Kill Process Callback
    if data.startswith("kill_"):
        pid = int(data.replace("kill_", ""))
        if pid in bg_processes:
            try:
                bg_processes[pid]['process'].terminate()
                del bg_processes[pid]
                bot.answer_callback_query(call.id, f"Engine {pid} killed!")
                bot.send_message(call.message.chat.id, f"🛑 *ENGINE KILLED*\nPID `{pid}` successfully terminated.", parse_mode="Markdown")
            except Exception as e:
                bot.answer_callback_query(call.id, f"Error: {e}", show_alert=True)
        else:
            bot.answer_callback_query(call.id, "PID already stopped or not found.")
        return

    # Dashboard Actions
    if data == "btn_main_menu":
        edit(call, get_dashboard_text(), get_main_menu_keyboard(user_id))
        bot.answer_callback_query(call.id)

    elif data == "btn_status":
        edit(call, get_status_text(), get_back_keyboard())
        bot.answer_callback_query(call.id)

    elif data == "btn_sysinfo":
        edit(call, get_vitals_text(), get_back_keyboard())
        bot.answer_callback_query(call.id)

    elif data == "btn_memory":
        edit(call, get_memory_text(), get_back_keyboard())
        bot.answer_callback_query(call.id)

    elif data == "btn_disk":
        edit(call, get_disk_text(), get_back_keyboard())
        bot.answer_callback_query(call.id)

    elif data == "btn_ps":
        text, markup = get_engines_view(with_back=True)
        edit(call, text, markup)
        bot.answer_callback_query(call.id)

    elif data == "btn_myid":
        edit(call, get_myid_text(call.from_user.id), get_back_keyboard())
        bot.answer_callback_query(call.id)

    elif data == "btn_help":
        edit(call, get_help_text(user_id), get_back_keyboard())
        bot.answer_callback_query(call.id)

    else:
        bot.answer_callback_query(call.id)

# ----------------- RENDER WEB SERVICE / TELEGRAM WEBHOOK -----------------

app = Flask(__name__)
WEBHOOK_SECRET = __import__("hashlib").sha256(BOT_TOKEN.encode()).hexdigest()[:32]

@app.get("/")
def home():
    return "PYTHON HOSTING BOT V2 is online.", 200

@app.get("/health")
def health():
    return "OK", 200

@app.post(f"/telegram/{WEBHOOK_SECRET}")
def telegram_webhook():
    if not request.is_json:
        return "Bad Request", 400
    try:
        update = types.Update.de_json(request.get_json())
        bot.process_new_updates([update])
        return "OK", 200
    except Exception as e:
        print(f"[WEBHOOK ERROR] {e}")
        return "Internal Server Error", 500

def start_webhook():
    load_hosted_index()
    setup_command_menu()
    public_url = os.getenv("RENDER_EXTERNAL_URL", "").rstrip("/")
    if not public_url:
        print("[WEBHOOK ERROR] RENDER_EXTERNAL_URL is missing.")
        return
    webhook_url = f"{public_url}/telegram/{WEBHOOK_SECRET}"
    try:
        bot.remove_webhook()
        bot.set_webhook(url=webhook_url)
        print(f"⚡️ Telegram webhook enabled: {webhook_url}")
    except Exception as e:
        print(f"[WEBHOOK ERROR] Could not set webhook: {e}")

if __name__ == "__main__":
    start_webhook()
    port = int(os.getenv("PORT", "10000"))
    app.run(host="0.0.0.0", port=port, threaded=True)

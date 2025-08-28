# -*- coding: utf-8 -*-
"""
Cobalt v2.7.2 — Python (AutoIt) port of your AHK workflow
--------------------------------------------------------
- AutoIt (py-autoit) for all input
- Tkinter GUI with visible checkboxes (no duplicate kwargs)
- Config persistence via configparser (config.ini)
- Pixel search via Pillow+NumPy; template search via OpenCV
- Robust reconnect with debouncing + cycle locking
- Shop-open detection tolerant to placeholder images
- Center-click recall wrench path

Requirements (Windows):
    pip install autoit keyboard pillow opencv-python numpy
"""

import os
import sys
import math
import json
import time
import webbrowser
import re
import threading
from threading import Lock
import configparser
from typing import List, Tuple, Optional

# Third-party
import autoit
import keyboard
from PIL import ImageGrab, Image, ImageStat
import numpy as np
import cv2

# GUI
import tkinter as tk
from tkinter import ttk, messagebox

# ---------------------- Constants & Globals ----------------------

VERSION = "v2.7.2"
WINDOW_TITLE = "Roblox"  # change if your Roblox window title differs

# State
started = 0
finished = True
cycleCount = 0
eggCounter = 0
canDoEgg = True
longRecon = False
adminAbuse = False

# Concurrency / stability
cycle_lock: Lock = Lock()
reconnecting: bool = False
last_reconnect_ts: float = 0.0
suppress_exit_until: float = 0.0

sleepPerf = 200
perfSetting = "Default"

# User-configurable values (loaded/saved via config.ini)
privateServerLink = ""
webhookURL = ""
discordID = ""
uiNavKeybind = "\\"  # default "\"
invNavKeybind = "`"  # literal backtick

# Item lists
seedItems = ["Carrot Seed", "Strawberry Seed", "Blueberry Seed",
             "Orange Tulip Seed", "Tomato Seed", "Corn Seed",
             "Daffodil Seed", "Watermelon Seed", "Pumpkin Seed",
             "Apple Seed", "Bamboo Seed", "Coconut Seed", "Cactus Seed",
             "Dragon Fruit Seed", "Mango Seed", "Grape Seed", "Mushroom Seed",
             "Pepper Seed", "Cacao Seed", "Beanstalk Seed", "Ember Lily",
             "Sugar Apple", "Burning Bud", "Giant Pinecone Seed", "Elder Strawberry", "Romanesco"]

gearItems = ["Watering Can", "Trading Ticket", "Trowel",
             "Recall Wrench", "Basic Sprinkler", "Advanced Sprinkler",
             "Medium Toy", "Medium Treat", "Godly Sprinkler",
             "Magnifying Glass", "Master Sprinkler", "Cleaning Spray", "Cleansing Pet Shard",
             "Favorite Tool", "Harvest Tool", "Friendship Pot",
             "Grandmaster Sprinkler", "Levelup Lollipop"]

eggItems = ["Common Egg", "Uncommon Egg", "Rare Egg", "Legendarry Egg", "Mythical Egg", "Bug Egg"]

pingList_default = ["Beanstalk Seed", "Ember Lily", "Sugar Apple", "Burning Bud",
                    "Giant Pinecone Seed", "Elder Strawberry", "Master Sprinkler",
                    "Grandmaster Sprinkler", "Levelup Lollipop", "Medium Treat",
                    "Medium Toy", "Mythical Egg", "Paradise Egg", "Bug Egg"]

allList = seedItems + gearItems + eggItems

currentlyAllowedSeeds: List[str] = []
currentlyAllowedGear: List[str] = []
currentlyAllowedEggs: List[str] = []
currentlyAllowedEvent: List[str] = []  # reserved

pingList: List[str] = pingList_default.copy()
messageQueue: List[str] = []

# GUI references
root: Optional[tk.Tk] = None
status_var: Optional[tk.StringVar] = None

# GUI state lists
seed_vars = []
gear_vars = []
egg_vars = []
ping_listbox = None


# INI
INI_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.ini")

# Image paths
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
IMG_DIR = os.path.join(SCRIPT_DIR, "images")
IMG_GRAY = os.path.join(IMG_DIR, "gray.png")
IMG_CLOSE = os.path.join(IMG_DIR, "close.png")
IMG_CLOSE_HOVER = os.path.join(IMG_DIR, "close_hover.png")

# ---------------------- Utilities ----------------------

def hex_to_rgb(hex_val: int) -> Tuple[int, int, int]:
    r = (hex_val >> 16) & 0xFF
    g = (hex_val >> 8) & 0xFF
    b = hex_val & 0xFF
    return (r, g, b)

def array_to_string(arr: List[str], delimiter: str = ", ") -> str:
    return delimiter.join(arr) if arr else ""

def index_of(arr: List[str], value: str) -> int:
    try:
        return arr.index(value)
    except ValueError:
        return -1

def arr_contains(arr: List[str], value: str) -> bool:
    return value in arr

def insert_by_reference_order(target: List[str], value: str, reference: List[str]):
    if value not in reference:
        return
    ref_idx = reference.index(value)
    insert_pos = 0
    for i, v in enumerate(target):
        if v in reference and reference.index(v) <= ref_idx:
            insert_pos = i + 1
    target.insert(insert_pos, value)

def tooltip_log(msg: str, duration_ms: int = 3000):
    if status_var is not None and root is not None:
        status_var.set(msg)
        root.after(duration_ms, lambda: status_var.set(""))

def send_input(keys: str):
    """Send keystrokes via AutoIt to the active window."""
    try:
        autoit.send(keys)
    except Exception:
        time.sleep(0.05)
        autoit.send(keys)




def _select_dialog_option_one():
    """Select '#1 [Show me the Egg Shop]' without moving the character."""
    # Prefer the keyboard hotkey first (Roblox dialogs accept 1–6)
    for _ in range(2):
        send_input("1"); time.sleep(0.08)
    time.sleep(0.25)
    if not is_shop_open():
        # Click 3 nearby points where the '#1' line appears on the right list
        rect = get_roblox_rect()
        if rect:
            x, y, w, h = rect
            pts = [
                (x + int(0.64 * w), y + int(0.60 * h)),  # main
                (x + int(0.66 * w), y + int(0.58 * h)),  # up-right
                (x + int(0.62 * w), y + int(0.62 * h)),  # down-left
            ]
        else:
            sw, sh = screen_size()
            pts = [
                (int(0.64 * sw), int(0.60 * sh)),
                (int(0.66 * sw), int(0.58 * sh)),
                (int(0.62 * sw), int(0.62 * sh)),
            ]
        for cx, cy in pts:
            autoit.mouse_click("left", cx, cy, 1, 1)
            time.sleep(0.25)
            if is_shop_open():
                break
    time.sleep(0.5)


def start_ui_nav():
    send_input(uiNavKeybind)
    time.sleep(0.05)

def start_inv_action():
    send_input(invNavKeybind)
    time.sleep(0.05)

def repeat_key(key: str, count: int = 1):
    for _ in range(count):
        send_input("{" + key.upper() + "}")
        time.sleep(sleepPerf / 1000.0)

def hold_key(key: str, ms: int):
    send_input("{" + key + " down}")
    time.sleep(ms / 1000.0)
    send_input("{" + key + " up}")

def key_encoder(seq: str):
    """AHK keyEncoder clone: R/L/U/D/E/W"""
    mapping = {"r": "RIGHT", "l": "LEFT", "u": "UP", "d": "DOWN", "e": "ENTER"}
    for ch in seq.lower():
        if ch in mapping:
            repeat_key(mapping[ch])
        elif ch == "w":
            time.sleep(0.1)

def win_activate_roblox():
    autoit.win_activate(WINDOW_TITLE)
    autoit.win_wait_active(WINDOW_TITLE, 3)

def _process_exists(image: str = "RobloxPlayerBeta.exe") -> bool:
    try:
        out = os.popen('tasklist /FI "IMAGENAME eq %s"' % image).read().lower()
        return image.lower() in out
    except Exception:
        return False

def win_exists_roblox() -> bool:
    # Treat as alive if window OR process exists (window title can blip)
    return autoit.win_exists(WINDOW_TITLE) == 1 or _process_exists()

def get_roblox_rect() -> Optional[Tuple[int, int, int, int]]:
    if not win_exists_roblox():
        return None
    x, y, w, h = autoit.win_get_pos(WINDOW_TITLE)
    return (int(x), int(y), int(w), int(h))

def safe_move_relative(x_ratio: float, y_ratio: float):
    rect = get_roblox_rect()
    if not rect:
        return
    x, y, w, h = rect
    mx = x + int(x_ratio * w)
    my = y + int(y_ratio * h)
    autoit.mouse_move(mx, my, 1)

def safe_click_relative(x_ratio: float, y_ratio: float, button: str = "left"):
    rect = get_roblox_rect()
    if not rect:
        return
    x, y, w, h = rect
    cx = x + int(x_ratio * w)
    cy = y + int(y_ratio * h)
    autoit.mouse_click(button, cx, cy, 1, 1)

def mouse_pos_screen() -> Tuple[int, int]:
    return autoit.mouse_get_pos()

def screen_size() -> Tuple[int, int]:
    img = ImageGrab.grab()
    return img.size  # (width, height)

def pixel_region_bbox(percent_box: Tuple[int, int, int, int]) -> Tuple[int, int, int, int]:
    sw, sh = screen_size()
    spx, spy, epx, epy = percent_box
    x1 = int((spx / 100.0) * sw); y1 = int((spy / 100.0) * sh)
    x2 = int((epx / 100.0) * sw); y2 = int((epy / 100.0) * sh)
    return (x1, y1, x2, y2)

def color_detect(hex_color: int, var: int = 10) -> bool:
    bbox = pixel_region_bbox((40, 27, 60, 85))
    img = ImageGrab.grab(bbox=bbox).convert("RGB")
    arr = np.array(img)
    target = np.array(hex_to_rgb(hex_color), dtype=np.int16)
    diff = np.abs(arr.astype(np.int16) - target)
    dist = np.max(diff, axis=2)
    return np.any(dist <= var)

def _is_valid_template(path: str) -> bool:
    """Only allow real (non-placeholder) images to be used for template matching."""
    try:
        if not os.path.isfile(path):
            return False
        if os.path.getsize(path) < 2048:  # tiny placeholders
            return False
        im = Image.open(path).convert("RGBA")
        stat = ImageStat.Stat(im)
        variance = sum(stat.var[:3])
        mean_alpha = stat.mean[3]
        return variance > 5 and mean_alpha > 5
    except Exception:
        return False

def template_find(path: str, bbox_percent=(40, 27, 80, 85), threshold: float = 0.85) -> Optional[Tuple[int, int]]:
    if not _is_valid_template(path):
        return None
    x1, y1, x2, y2 = pixel_region_bbox(bbox_percent)
    scr = ImageGrab.grab(bbox=(x1, y1, x2, y2)).convert("RGB")
    scr_np = np.array(scr)[:, :, ::-1]  # BGR
    tmpl = cv2.imread(path, cv2.IMREAD_COLOR)
    if tmpl is None:
        return None
    res = cv2.matchTemplate(scr_np, tmpl, cv2.TM_CCOEFF_NORMED)
    _, max_val, _, max_loc = cv2.minMaxLoc(res)
    if max_val >= threshold:
        tx, ty = max_loc
        return (x1 + tx, y1 + ty)
    return None

def disconnect_color_check() -> bool:
    global longRecon
    pt = template_find(IMG_GRAY, (40, 27, 60, 85), threshold=0.80)
    if pt is not None:
        longRecon = True
        return True
    return False

def is_shop_open() -> bool:
    time.sleep(0.05)
    # AHK: (colorDetect(0x50240c) || colorDetect(0x360805)) && !disconnectColorCheck()
    return (color_detect(0x50240c) or color_detect(0x360805)) and (not disconnect_color_check())

def go_to_egg_close():
    pt = None
    if _is_valid_template(IMG_CLOSE):
        pt = template_find(IMG_CLOSE, (40, 24, 80, 85), threshold=0.80)
    if pt is None and _is_valid_template(IMG_CLOSE_HOVER):
        pt = template_find(IMG_CLOSE_HOVER, (40, 24, 80, 85), threshold=0.80)
    if pt is not None:
        x, y = pt
        sw, sh = screen_size()
        cx = x + int(0.01 * sw)
        cy = y + int(0.01 * sh)
        autoit.mouse_click("left", cx, cy, 1, 1)
    else:
        tooltip_log("Error: Did not find egg shop close button")
        send_discord_message("Did not find egg shop close button! Reconnecting...", 0xFF0000)
        reconnect()

def recalibrate_camera_distance():
    for _ in range(35):
        send_input("{WHEELUP}"); time.sleep(0.01)
    time.sleep(0.5)
    for _ in range(7):
        send_input("{WHEELDOWN}"); time.sleep(0.01)

def safe_move_center():
    safe_move_relative(0.5, 0.5)

def search_item(item: str):
    start_inv_action()
    start_ui_nav()
    key_encoder("E")
    start_inv_action()
    start_ui_nav()
    key_encoder("ULLULLULLULLULLULL")
    key_encoder("RERRRDDRRRUUUE")
    repeat_key("BACKSPACE", 30)
    type_string(item)

def type_string(s: str):
    if not s:
        return
    for ch in s:
        send_input(ch); time.sleep(0.05)


def tp_to_gear():
    tooltip_log("Going to gear shop...")
    win_activate_roblox()
    send_input("{2}")  # equip Recall Wrench
    time.sleep(0.10)
    # Double-click center with a small hold to ensure the wrench triggers
    rect = get_roblox_rect()
    if rect:
        x, y, w, h = rect
        cx = x + int(0.5 * w)
        cy = y + int(0.5 * h)
        autoit.mouse_move(cx, cy, 1)
        autoit.mouse_down("left")
        time.sleep(0.12)
        autoit.mouse_up("left")
        time.sleep(0.05)
        autoit.mouse_click("left", cx, cy, 1, 1)
    else:
        safe_click_relative(0.5, 0.5)
    time.sleep(0.40)
    send_input("{2}")
    time.sleep(0.40)


def buy_all_available(spam_count: int = 50, item: str = ""):
    repeat_key("ENTER")
    repeat_key("DOWN")
    if is_there_stock():
        if item != "Trowel":
            repeat_key("LEFT")
        repeat_key("ENTER", spam_count)
        messageQueue.append(f"Bought {item}!")
    repeat_key("DOWN")

def is_there_stock() -> bool:
    time.sleep(0.2)
    return color_detect(0x20b41c) or color_detect(0x26EE26)

def go_shopping(arr: List[str], all_arr: List[str], spam_count: int = 50):
    key_encoder("RRRR")
    repeat_key("UP", 40)
    key_encoder("LLRDRD")
    for item in all_arr:
        if item not in arr:
            repeat_key("DOWN")
            continue
        buy_all_available(spam_count, item)
    if len(messageQueue) == 0:
        messageQueue.append("Bought nothing...")
    repeat_key("UP", 40)
    key_encoder("LLRDRWEWW")

def go_shopping_egg(arr: List[str], all_arr: List[str]):
    key_encoder("RRRR")
    repeat_key("UP", 40)
    key_encoder("R")
    for item in all_arr:
        if item not in arr:
            repeat_key("DOWN")
            continue
        buy_all_available(5, item)
    if len(messageQueue) == 0:
        messageQueue.append("Bought nothing...")
    go_to_egg_close()

def send_discord_queue(title: str = "Bulk Message"):
    final = f"**{title}:**\n"
    should_ping = False
    for msg in messageQueue:
        final += f"- -# {msg}\n"
        for p in pingList:
            if p in msg:
                should_ping = True; break
    send_discord_message(final, 0x0000FF, should_ping)
    messageQueue.clear()

def send_discord_message(message: str, color: int = 0x0000FF, ping: bool = False):
    if not webhookURL:
        return
    import urllib.request, urllib.error
    msg_time = time.strftime("%I:%M %p")
    payload = {"embeds": [{
        "type": "rich",
        "description": f"``{msg_time}`` | {message}",
        "color": int(color)
    }]}
    if ping and discordID:
        payload["content"] = f"<@!{discordID}>"
    data = json.dumps(payload).encode("utf-8")
    req = urllib.request.Request(webhookURL, data=data, headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=5) as resp:
            _ = resp.read()
    except urllib.error.URLError:
        pass

def reconnect():
    global longRecon, reconnecting, last_reconnect_ts, suppress_exit_until
    if reconnecting:
        return
    reconnecting = True
    try:
        now = time.time()
        if now - last_reconnect_ts < 20:
            return
        last_reconnect_ts = now

        import re as _re2
        valid = bool(_re2.match(r"^https?://(w{3}\.)?roblox\.com", privateServerLink or ""))
        if not valid:
            send_discord_message("Reconnect requested but no valid private server link is set; skipping.", 0xFF0000)
            longRecon = False
            return

        # Suppress exit checks during the reconnect routine
        extra_wait = 180 if longRecon else 0
        suppress_exit_until = time.time() + extra_wait + 90  # covers 45s load + 15s buffer + margin

        # Close Roblox (best-effort) and wait
        os.system('taskkill /IM RobloxPlayerBeta.exe /F >NUL 2>&1')
        time.sleep(1.0)
        os.system('taskkill /IM RobloxPlayerBeta.exe /F >NUL 2>&1')
        time.sleep(3.0)
        if longRecon:
            time.sleep(180)  # 3 minutes
            longRecon = False

        webbrowser.open(privateServerLink)

        time.sleep(45.0)
        send_input("{TAB}")
        time.sleep(1.0)
        safe_move_center()
        autoit.mouse_click("left")
        time.sleep(15.0)
        send_discord_message("Reconnected to the game!", 0x00FF00)
        alignment()  # resume
    finally:
        reconnecting = False


_last_dead_check = 0.0

def exit_if_window_dies():
    global _last_dead_check
    # Skip death handling while reconnecting or during suppression window
    if reconnecting or (time.time() < suppress_exit_until):
        _last_dead_check = 0.0
        return
    # Debounce for 2s to avoid false negatives during teleports or alt-tab flickers
    if win_exists_roblox():
        _last_dead_check = 0.0
        return
    if _last_dead_check == 0.0:
        _last_dead_check = time.time()
        return
    if time.time() - _last_dead_check >= 2.0:
        on_close()

def alignment():
    exit_if_window_dies()
    tooltip_log("Placing Recall Wrench in slot 2...")
    search_item("recall")
    key_encoder("EDUUEDRE")
    start_inv_action()
    tooltip_log("Aligning camera...")
    recalibrate_camera_distance()

    time.sleep(0.5)
    autoit.mouse_down("right")
    time.sleep(0.1)
    safe_move_center()
    time.sleep(0.1)

    _, ypos = mouse_pos_screen()
    _, screenHeight = screen_size()
    moveDistance = -round(screenHeight * 0.75) if ypos >= screenHeight * 0.90 else round(screenHeight * 0.75)

    x, y = mouse_pos_screen()
    autoit.mouse_move(x, y + moveDistance, 1)
    time.sleep(0.1)
    autoit.mouse_up("right")
    time.sleep(0.1)

    repeat_key("ESC"); time.sleep(0.1)
    repeat_key("TAB"); time.sleep(0.1)
    key_encoder("UUUUUUUUUUUDRRW")
    repeat_key("ESC")
    time.sleep(0.5)
    start_ui_nav()
    key_encoder("ULLULLULLULLULLULLRRRRRRLELERRELLRELERRELLRELERRELLRELERRELLRELERRELLW")
    start_ui_nav()
    repeat_key("ESC"); time.sleep(0.1)
    repeat_key("TAB"); time.sleep(0.1)
    key_encoder("UUUUUUUUUUUDRRW")
    repeat_key("ESC")
    key_encoder("WDREWW")
    tooltip_log("Alignment complete!")


def seed_cycle():
    exit_if_window_dies()
    if len(currentlyAllowedSeeds) == 0:
        gear_cycle(); return
    start_ui_nav()
    time.sleep(1.0)
    key_encoder("ULLULLULLULLULLULLWRRRRRLLEW")
    win_activate_roblox()
    send_input("e")  # open shop
    start_ui_nav(); start_ui_nav()
    time.sleep(3.0)
    if is_shop_open():
        tooltip_log("Shopping for seeds...")
        go_shopping(currentlyAllowedSeeds, seedItems)
        send_discord_queue("Seed Shop")
        start_ui_nav()
    else:
        tooltip_log("Error: Seed shop did not open")
        send_discord_message("Seed shop did not open! Reconnecting...", 0xFF0000)
        reconnect()



def gear_cycle():
    exit_if_window_dies()
    if len(currentlyAllowedGear) == 0:
        egg_cycle(); return
    tp_to_gear()
    tooltip_log("Opening gear shop...")
    win_activate_roblox()
    send_input("e")
    time.sleep(3.0)
    if is_shop_open():
        start_ui_nav()
        tooltip_log("Shopping for gear...")
        go_shopping(currentlyAllowedGear, gearItems, 20)
        send_discord_queue("Gear Shop")
        start_ui_nav()
        time.sleep(0.1)
    else:
        tooltip_log("Error: Gear shop did not open")
        send_discord_message("Gear shop did not open! Reconnecting...", 0xFF0000)
        reconnect()





def camera_zoom_in_max_then_backoff(max_in: int = 30, backoff: int = 3, delay: float = 0.015):
    """Zoom all the way in, then slightly back out for consistent dialog placement."""
    win_activate_roblox()
    # Zoom in hard (wheel up), then back off a little (wheel down)
    for _ in range(max_in):
        send_input("{WHEELUP}"); time.sleep(delay)
    time.sleep(0.12)
    for _ in range(backoff):
        send_input("{WHEELDOWN}"); time.sleep(delay)
    time.sleep(0.15)


def ensure_dialog_then_select_egg_shop(max_attempts: int = 3):
    """
    Open the pet dialog and pick #1 'Show me the Egg Shop'.
    We do NOT move unless TWO full select attempts fail.
    """
    for attempt in range(max_attempts):
        win_activate_roblox()
        autoit.mouse_up("left"); autoit.mouse_up("right")
        # Normalize camera so dialog renders consistently
        camera_zoom_in_max_then_backoff()
        # Try 2 full cycles of [E -> select #1] before any nudge
        for cycle in range(2):
            # Press E twice to open dialog
            send_input("e"); time.sleep(0.15)
            send_input("e"); time.sleep(0.25)
            _select_dialog_option_one()
            time.sleep(1.0)
            if is_shop_open():
                return True
        # Only now, if still not open, try a tiny nudge and loop
        if attempt == 0:
            hold_key("d", 140)   # small right step
        elif attempt == 1:
            hold_key("a", 180)   # small left step
        else:
            hold_key("s", 120)   # small back step
        time.sleep(0.25)
    return False


def egg_cycle():
    global canDoEgg
    exit_if_window_dies()
    if len(currentlyAllowedGear) == 0 and len(currentlyAllowedEggs) > 0:
        tp_to_gear()
    if len(currentlyAllowedEggs) > 0 and canDoEgg:
        canDoEgg = False
        tooltip_log("Going to egg shop...")
        recalibrate_camera_distance()
        hold_key("w", 600)
        time.sleep(sleepPerf / 1000.0)
        hold_key("d", 220)  # FIX: strafe right to egg shop (was "a" left)
        time.sleep(sleepPerf / 1000.0)
        win_activate_roblox()
        autoit.mouse_up("left"); autoit.mouse_up("right")
        # Ensure no buttons are held then talk
        # Press E a couple of times in case the first one is swallowed
        for _ in range(2):
            send_input("e"); time.sleep(0.15)
        time.sleep(2.5)

        for _ in range(5):
            send_input("{WHEELUP}"); time.sleep(0.01)
        time.sleep(0.5)

        # Ensure no mouse button is stuck down (wrench click carry-over guard)
        autoit.mouse_up("left"); autoit.mouse_up("right")
        # Prefer pressing "1" (dialog hotkey) to open the Egg Shop; fallback click near the option text
        success = ensure_dialog_then_select_egg_shop(3)
        time.sleep(0.5)

        if not is_shop_open():
            # One soft retry + nudge left and re-open with E (range/angle fix)
            hold_key("d", 180)
            success = ensure_dialog_then_select_egg_shop(2)
            time.sleep(0.8)

        if is_shop_open():
            start_ui_nav()
            tooltip_log("Shopping for eggs...")
            go_shopping_egg(currentlyAllowedEggs, eggItems)
            send_discord_queue("Egg Shop")
            time.sleep(0.5)
            start_ui_nav()
            for _ in range(5):
                send_input("{WHEELDOWN}"); time.sleep(0.01)
            time.sleep(0.5)
        else:
            tooltip_log("Error: Egg shop did not open")
            # Only reconnect if we detect the disconnect overlay; otherwise skip this egg cycle
            if disconnect_color_check():
                send_discord_message("Egg shop did not open and disconnect overlay detected — reconnecting...", 0xFF0000)
                reconnect()
            else:
                send_discord_message("Egg shop did not open — skipping this egg cycle.", 0xFF0000)


def wait_for_next_cycle():
    global finished, cycleCount
    safe_move_center()
    finished = True
    cycleCount += 1
    send_discord_message(f"Cycle {cycleCount} finished", 0x00FF00)

# ---------------------- Timer Thread (ShowTimeTip emulation) ----------------------

def seconds_until(interval_minutes: int) -> int:
    now = time.localtime()
    seconds_past_hour = now.tm_min * 60 + now.tm_sec
    interval = interval_minutes * 60
    rem = interval - (seconds_past_hour % interval)
    rem = rem % (interval + 1)
    return rem

def timer_loop():
    global canDoEgg, finished
    while True:
        try:
            if reconnecting:
                time.sleep(1.0); continue
            if adminAbuse:
                canDoEgg = True
                finished = False
                try_run_cycle()
            s5 = seconds_until(5)
            s30 = seconds_until(30)
            if not adminAbuse and status_var is not None:
                status_var.set(f"Next cycle in {s5//60:02d}:{s5%60:02d} | Next Egg Cycle in {s30//60:02d}:{s30%60:02d}")
            if s30 < 3 or adminAbuse:
                canDoEgg = True
            if s5 < 3 or adminAbuse:
                finished = False
                recalibrate_camera_distance()
                try_run_cycle()
            time.sleep(1.0)
        except Exception:
            time.sleep(1.0)

def try_run_cycle():
    if started == 0 or reconnecting:
        return
    if not cycle_lock.acquire(blocking=False):
        return
    try:
        win_activate_roblox()
        alignment()
        seed_cycle()
        gear_cycle()
        egg_cycle()
        wait_for_next_cycle()
    finally:
        cycle_lock.release()

# ---------------------- Config (INI) ----------------------

def load_values():
    global webhookURL, privateServerLink, discordID, perfSetting, uiNavKeybind
    global currentlyAllowedSeeds, currentlyAllowedGear, currentlyAllowedEggs, pingList

    cfg = configparser.ConfigParser()
    if os.path.isfile(INI_PATH):
        cfg.read(INI_PATH, encoding="utf-8")

    webhookURL = cfg.get("PlayerConf", "webhookURL", fallback="").strip()
    privateServerLink = cfg.get("PlayerConf", "privateServerLink", fallback="").strip()
    discordID = cfg.get("PlayerConf", "discordID", fallback="").strip()
    perfSetting = cfg.get("PlayerConf", "perfSetting", fallback="Default").strip()
    uiNavKeybind_read = cfg.get("PlayerConf", "uiNavKeybind", fallback="\\").strip()
    if uiNavKeybind_read:
        globals()["uiNavKeybind"] = uiNavKeybind_read

    seeds_str = cfg.get("PersistentData", "currentlyAllowedSeeds", fallback="")
    gear_str = cfg.get("PersistentData", "currentlyAllowedGear", fallback="")
    eggs_str = cfg.get("PersistentData", "currentlyAllowedEggs", fallback="")
    ping_str = cfg.get("PersistentData", "pingList", fallback="")

    currentlyAllowedSeeds = [s for s in map(str.strip, seeds_str.split(", ")) if s] if seeds_str else []
    currentlyAllowedGear = [s for s in map(str.strip, gear_str.split(", ")) if s] if gear_str else []
    currentlyAllowedEggs = [s for s in map(str.strip, eggs_str.split(", ")) if s] if eggs_str else []

    if ping_str:
        pl = [s for s in map(str.strip, ping_str.split(", ")) if s]
        if pl:
            pingList = [s for s in pl if s in allList]

def save_values():
    cfg = configparser.ConfigParser()
    if os.path.isfile(INI_PATH):
        cfg.read(INI_PATH, encoding="utf-8")

    if "PlayerConf" not in cfg:
        cfg["PlayerConf"] = {}
    if "PersistentData" not in cfg:
        cfg["PersistentData"] = {}

    cfg["PlayerConf"]["privateServerLink"] = privateServerLink
    cfg["PlayerConf"]["webhookURL"] = webhookURL
    cfg["PlayerConf"]["discordID"] = discordID
    cfg["PlayerConf"]["perfSetting"] = perfSetting
    cfg["PlayerConf"]["uiNavKeybind"] = uiNavKeybind

    cfg["PersistentData"]["currentlyAllowedSeeds"] = array_to_string(currentlyAllowedSeeds)
    cfg["PersistentData"]["currentlyAllowedGear"] = array_to_string(currentlyAllowedGear)
    cfg["PersistentData"]["currentlyAllowedEggs"] = array_to_string(currentlyAllowedEggs)
    cfg["PersistentData"]["pingList"] = array_to_string(pingList)

    with open(INI_PATH, "w", encoding="utf-8") as f:
        cfg.write(f)

# ---------------------- GUI ----------------------

def set_perf_from_setting():
    global sleepPerf
    perfMode = perfSetting.split(" ")[0]
    if perfMode == "Modern":
        sleepPerf = 50
    elif perfMode == "Default":
        sleepPerf = 75
    elif perfMode == "Chromebook":
        sleepPerf = 125
    elif perfMode == "Atari":
        sleepPerf = 200
    elif perfMode == "Supercomputer":
        sleepPerf = 0
    else:
        sleepPerf = 100
    save_values()

def on_update_player_values():
    global privateServerLink, webhookURL, discordID, uiNavKeybind
    privateServerLink = entry_psl.get().strip()
    webhookURL = entry_webhook.get().strip()
    discordID = entry_discord.get().strip()
    nav_key = entry_navkey.get().strip()
    uiNavKeybind = nav_key if nav_key else "\\"
    if any(not ch.isdigit() for ch in discordID if discordID):
        tooltip_log("Your Discord ID must only contain numbers")
    if not privateServerLink:
        tooltip_log("If you want to rejoin on error, you must provide a private server link")
    save_values()

def on_update_perf(*_):
    global perfSetting
    perfSetting = perf_combo.get()
    set_perf_from_setting()

def toggle_all(group: str, state: bool):
    if group == "seeds":
        for var in seed_vars:
            var.set(state)
        update_items_from_vars("seeds")
    elif group == "gear":
        for var in gear_vars:
            var.set(state)
        update_items_from_vars("gear")
    elif group == "eggs":
        for var in egg_vars:
            var.set(state)
        update_items_from_vars("eggs")

def update_items_from_vars(group: str):
    global currentlyAllowedSeeds, currentlyAllowedGear, currentlyAllowedEggs
    if group == "seeds":
        currentlyAllowedSeeds = []
        for val, item in zip([v.get() for v in seed_vars], seedItems):
            if val:
                insert_by_reference_order(currentlyAllowedSeeds, item, seedItems)
    elif group == "gear":
        currentlyAllowedGear = []
        for val, item in zip([v.get() for v in gear_vars], gearItems):
            if val:
                insert_by_reference_order(currentlyAllowedGear, item, gearItems)
    elif group == "eggs":
        currentlyAllowedEggs = []
        for val, item in zip([v.get() for v in egg_vars], eggItems):
            if val:
                insert_by_reference_order(currentlyAllowedEggs, item, eggItems)
    save_values()

def on_ping_select():
    global pingList
    sel = [allList[i] for i in ping_listbox.curselection()]
    pingList = sel
    save_values()

def on_start():
    global started
    started = 1
    send_discord_message("Macro started!", 0x00FF00)
    win_activate_roblox()
    tooltip_log("Macro started")
    try_run_cycle()

def on_pause():
    global started
    send_discord_message("Macro paused!", 0xFF0000)
    started = 0
    tooltip_log("Macro paused")

def on_close():
    send_discord_message("Macro Exited!", 0xFF0000, True)
    try:
        root.destroy()
    except Exception:
        pass
    sys.exit(0)

def build_gui():
    global root, status_var
    global entry_psl, entry_webhook, entry_discord, entry_navkey, perf_combo
    global seed_vars, gear_vars, egg_vars, ping_listbox

    root = tk.Tk()
    root.title(f"Cobalt {VERSION}")
    root.geometry("580x560")
    root.configure(bg="#000000")
    root.protocol("WM_DELETE_WINDOW", on_close)

    title = tk.Label(root, text=f"Cobalt {VERSION}", fg="white", bg="#000000", font=("Segoe UI", 12, "bold"))
    title.pack(side="top", pady=5)

    notebook = ttk.Notebook(root)
    notebook.pack(fill="both", expand=True, padx=10, pady=(0,5))

    def mk_tab(name):
        frame = tk.Frame(notebook, bg="#000000")
        notebook.add(frame, text=name)
        return frame

    seeds_tab = mk_tab("Seeds")
    gear_tab = mk_tab("Gear")
    eggs_tab = mk_tab("Eggs")
    ping_tab = mk_tab("Ping List")
    settings_tab = mk_tab("Settings")
    credits_tab = mk_tab("Credits")

    # Seeds
    seed_all_var = tk.BooleanVar(value=False)
    tk.Checkbutton(seeds_tab, text="Select All Seeds", variable=seed_all_var,
                   command=lambda: toggle_all("seeds", seed_all_var.get()),
                   fg="#1C96EF", bg="#000000", activebackground="#000000", selectcolor="#1C96EF").place(x=205, y=15)

    cols = 3
    seed_vars.clear()
    seed_vars.extend([tk.BooleanVar(value=(seed in currentlyAllowedSeeds)) for seed in seedItems])
    for idx, seed in enumerate(seedItems):
        var = seed_vars[idx]
        row = idx % math.ceil(len(seedItems)/cols)
        col = idx // math.ceil(len(seedItems)/cols)
        x = 25 + col * 170
        y = 50 + row * 26
        tk.Checkbutton(seeds_tab, text=seed, variable=var,
                       command=lambda: update_items_from_vars("seeds"),
                       fg="white", bg="#000000", activebackground="#000000", selectcolor="#1C96EF").place(x=x, y=y)

    # Gear
    gear_all_var = tk.BooleanVar(value=False)
    tk.Checkbutton(gear_tab, text="Select All Gear", variable=gear_all_var,
                   command=lambda: toggle_all("gear", gear_all_var.get()),
                   fg="#32FF32", bg="#000000", activebackground="#000000", selectcolor="#32FF32").place(x=205, y=15)

    gear_vars.clear()
    gear_vars.extend([tk.BooleanVar(value=(gear in currentlyAllowedGear)) for gear in gearItems])
    for idx, gear in enumerate(gearItems):
        var = gear_vars[idx]
        row = idx % math.ceil(len(gearItems)/cols)
        col = idx // math.ceil(len(gearItems)/cols)
        x = 25 + col * 170
        y = 50 + row * 26
        tk.Checkbutton(gear_tab, text=gear, variable=var,
                       command=lambda: update_items_from_vars("gear"),
                       fg="white", bg="#000000", activebackground="#000000", selectcolor="#32FF32").place(x=x, y=y)

    # Eggs
    eggs_all_var = tk.BooleanVar(value=False)
    tk.Checkbutton(eggs_tab, text="Select All Eggs", variable=eggs_all_var,
                   command=lambda: toggle_all("eggs", eggs_all_var.get()),
                   fg="#FFFF28", bg="#000000", activebackground="#000000", selectcolor="#FFFF28").place(x=55, y=15)

    egg_vars.clear()
    egg_vars.extend([tk.BooleanVar(value=(egg in currentlyAllowedEggs)) for egg in eggItems])
    for idx, egg in enumerate(eggItems):
        var = egg_vars[idx]
        x = 25; y = 50 + idx * 26
        tk.Checkbutton(eggs_tab, text=egg, variable=var,
                       command=lambda: update_items_from_vars("eggs"),
                       fg="white", bg="#000000", activebackground="#000000", selectcolor="#FFFF28").place(x=x, y=y)

    # Ping List
    tk.Label(ping_tab, text="Ping List", fg="white", bg="#000000").place(x=20, y=10)
    ping_listbox = tk.Listbox(ping_tab, selectmode=tk.MULTIPLE, width=55, height=17, bg="#000000", fg="white")
    ping_listbox.place(x=20, y=35)
    ping_listbox.delete(0, tk.END)
    for item in allList:
        ping_listbox.insert(tk.END, item)
    # set checks
    for i, item in enumerate(allList):
        if item in pingList:
            ping_listbox.selection_set(i)
    ping_listbox.bind("<<ListboxSelect>>", lambda e: on_ping_select())

    # Settings
    tk.Label(settings_tab, text="Private Server Link", fg="white", bg="#000000").place(x=50, y=30)
    tk.Label(settings_tab, text="Webhook URL", fg="white", bg="#000000").place(x=50, y=70)
    tk.Label(settings_tab, text="Discord User ID", fg="white", bg="#000000").place(x=50, y=110)
    tk.Label(settings_tab, text="Performance Setting", fg="white", bg="#000000").place(x=50, y=150)
    tk.Label(settings_tab, text="UI Navigation Keybind", fg="white", bg="#000000").place(x=50, y=190)
    tk.Label(settings_tab, text="(Enable Developer Mode in Discord to get your ID)",
             fg="gray", bg="#000000", font=("Segoe UI", 8)).place(x=50, y=130)

    entry_psl = tk.Entry(settings_tab, width=35); entry_psl.insert(0, privateServerLink); entry_psl.place(x=300, y=30)
    entry_webhook = tk.Entry(settings_tab, width=35); entry_webhook.insert(0, webhookURL); entry_webhook.place(x=300, y=70)
    entry_discord = tk.Entry(settings_tab, width=35); entry_discord.insert(0, discordID); entry_discord.place(x=300, y=110)
    entry_navkey = tk.Entry(settings_tab, width=35); entry_navkey.insert(0, uiNavKeybind); entry_navkey.place(x=300, y=190)

    options = ["Supercomputer (Doesnt work, for fun)","Modern PC (stable FPS on high)",
               "Default","Chromebook (cannot get stable FPS)","Atari 2600 (bless your soul)"]
    perf_combo = ttk.Combobox(settings_tab, values=options, state="readonly", width=32)
    try:
        choice_idx = options.index(perfSetting)
    except ValueError:
        choice_idx = options.index("Default")
    perf_combo.current(choice_idx); perf_combo.place(x=300, y=150)
    perf_combo.bind("<<ComboboxSelected>>", on_update_perf)

    start_btn = tk.Button(settings_tab, text="Start Macro (F5)", command=on_start, width=25, height=1); start_btn.place(x=50, y=230)
    stop_btn = tk.Button(settings_tab, text="Stop Macro (F7)", command=on_pause, width=25, height=1);  stop_btn.place(x=300, y=230)

    def toggle_admin():
        global adminAbuse
        adminAbuse = admin_var.get()
    admin_var = tk.BooleanVar(value=False)
    tk.Checkbutton(settings_tab, text="Admin Abuse", variable=admin_var,
                   command=toggle_admin, fg="white", bg="#000000",
                   activebackground="#000000", selectcolor="#444444").place(x=50, y=270)

    # Credits
    tk.Label(credits_tab, text=f"Cobalt {VERSION} by Clovalt, Cobblestone",
             fg="white", bg="#000000").place(x=50, y=20)

    # Bottom status
    global status_var
    status_var = tk.StringVar(value="")
    status = tk.Label(root, textvariable=status_var, fg="white", bg="#000000")
    status.pack(side="bottom", fill="x")

    # Bindings
    root.bind("<F5>", lambda e: on_start())
    root.bind("<F7>", lambda e: on_pause())

    try:
        keyboard.add_hotkey("F5", on_start)
        keyboard.add_hotkey("F7", on_pause)
    except Exception:
        pass

    # Save updates on field blur
    for e in (entry_psl, entry_webhook, entry_discord, entry_navkey):
        e.bind("<FocusOut>", lambda _e: on_update_player_values())

    return root

# ---------------------- Main ----------------------

def main():
    load_values()
    set_perf_from_setting()

    gui = build_gui()
    try:
        win_activate_roblox()
    except Exception:
        pass

    t = threading.Thread(target=timer_loop, daemon=True)
    t.start()

    gui.mainloop()

if __name__ == "__main__":
    main()

seed_vars = []
gear_vars = []
egg_vars = []

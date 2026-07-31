from __future__ import annotations

import ctypes
from ctypes import wintypes
from datetime import date, datetime, timedelta
import json
import math
import random
import sys
import time
import tkinter as tk
from tkinter import messagebox, scrolledtext, ttk
import uuid
import winreg
import winsound
from pathlib import Path
from PIL import Image, ImageTk
import pygame


APP_NAME = "大耳桌宠"
WINDOW_SIZE = 256
FRAME_MS = 110
MOVE_PIXELS = 5
TRANSPARENT_KEY = "#010203"
LONG_DRAG_SECONDS = 1.5
STARTUP_VALUE_NAME = "BigEarDesktopPet"
WATER_REMINDER_SECONDS = 45 * 60
SITTING_REMINDER_SECONDS = 60 * 60


class LASTINPUTINFO(ctypes.Structure):
    _fields_ = [("cbSize", wintypes.UINT), ("dwTime", wintypes.DWORD)]


class POINT(ctypes.Structure):
    _fields_ = [("x", wintypes.LONG), ("y", wintypes.LONG)]


def app_dir() -> Path:
    if getattr(sys, "frozen", False):
        return Path(sys.executable).resolve().parent
    return Path(__file__).resolve().parent


def resource_dir() -> Path:
    return app_dir() / "assets"


def sound_dir() -> Path:
    return app_dir() / "sounds"


def work_area() -> tuple[int, int, int, int]:
    """Return the Windows desktop work area, excluding the taskbar."""
    rect = wintypes.RECT()
    spi_getworkarea = 0x0030
    if ctypes.windll.user32.SystemParametersInfoW(spi_getworkarea, 0, ctypes.byref(rect), 0):
        return rect.left, rect.top, rect.right, rect.bottom
    return 0, 0, ctypes.windll.user32.GetSystemMetrics(0), ctypes.windll.user32.GetSystemMetrics(1)


def system_idle_seconds() -> float:
    info = LASTINPUTINFO()
    info.cbSize = ctypes.sizeof(info)
    if not ctypes.windll.user32.GetLastInputInfo(ctypes.byref(info)):
        return 0.0
    elapsed_ms = (ctypes.windll.kernel32.GetTickCount() - info.dwTime) & 0xFFFFFFFF
    return elapsed_ms / 1000.0


def cursor_position() -> tuple[int, int]:
    point = POINT()
    if ctypes.windll.user32.GetCursorPos(ctypes.byref(point)):
        return point.x, point.y
    return 0, 0


class DesktopPet:
    def __init__(self) -> None:
        self.settings_path = app_dir() / "settings.json"
        self.todos_path = app_dir() / "todos.json"
        self.settings = self._load_settings()
        self.todos = self._load_todos()
        self.pet_size_percent = int(self.settings["pet_size_percent"])
        self.window_size = round(WINDOW_SIZE * self.pet_size_percent / 100)
        self.volume = int(self.settings["volume"])
        self.sound_cache: dict[str, pygame.mixer.Sound] = {}
        try:
            pygame.mixer.init()
            self.mixer_ready = True
        except pygame.error:
            self.mixer_ready = False
        self.root = tk.Tk()
        self.root.title(APP_NAME)
        self.root.overrideredirect(True)
        self.root.attributes("-topmost", bool(self.settings["always_on_top"]))
        self.root.attributes("-transparentcolor", TRANSPARENT_KEY)
        self.root.configure(bg=TRANSPARENT_KEY)
        self.root.geometry(f"{self.window_size}x{self.window_size}+100+100")

        self.canvas = tk.Canvas(
            self.root,
            width=self.window_size,
            height=self.window_size,
            bg=TRANSPARENT_KEY,
            highlightthickness=0,
            borderwidth=0,
        )
        self.canvas.pack(fill="both", expand=True)

        self.images = self._load_images()
        self.sprite = self.canvas.create_image(0, 0, anchor="nw", image=self.images["idle"])
        self.stars = [
            self.canvas.create_polygon(
                0, 0, 1, 0, 0, 1,
                fill="#ffd84d",
                outline="#ef9f28",
                width=1,
                state="hidden",
            )
            for _ in range(3)
        ]
        self.zzz_items = [
            self.canvas.create_text(0, 0, text="z", fill=color, font=("Segoe UI", size, "bold"), state="hidden")
            for size, color in ((11, "#74cfd0"), (15, "#69bdc5"), (20, "#f39aa7"))
        ]
        self.heart_items = [
            self.canvas.create_text(0, 0, text="♥", fill=color, font=("Segoe UI Symbol", size, "bold"), state="hidden")
            for size, color in ((12, "#f6a1ae"), (16, "#ef7f95"), (20, "#f3a0b5"))
        ]

        self.left, self.top, self.right, self.bottom = work_area()
        self.x = max(self.left, min(self.right - self.window_size, self.right - self.window_size - 40))
        self.y = self.bottom - self.window_size
        self._place()

        self.direction = random.choice((-1, 1))
        self.frame_index = 0
        self.walking = False
        self.roaming = bool(self.settings["roaming"])
        self.sound_enabled = bool(self.settings["sound_enabled"])
        self.auto_sleep = bool(self.settings["auto_sleep"])
        self.show_mini_todo = bool(self.settings["show_mini_todo"])
        self.water_reminder_enabled = bool(self.settings["water_reminder"])
        self.sitting_reminder_enabled = bool(self.settings["sitting_reminder"])
        self.follow_mouse_enabled = bool(self.settings["follow_mouse"])
        self.dragging = False
        self.reacting = False
        self.sleeping = False
        self.woke_on_press = False
        self.drag_offset = (0, 0)
        self.press_position = (0, 0)
        self.drag_phase = False
        self.drag_started_at = 0.0
        self.last_drag_release_at = 0.0
        self.zzz_token = 0
        self.effect_token = 0
        self.pointer_down = False
        self.patting = False
        self.hold_job: str | None = None
        self.click_count = 0
        self.last_click_at = 0.0
        self.click_reset_job: str | None = None
        self.action_job: str | None = None
        self.blink_job: str | None = None
        self.sleep_check_job: str | None = None
        self.todo_check_job: str | None = None
        self.wellness_check_job: str | None = None
        self.follow_job: str | None = None
        self.settings_window: tk.Toplevel | None = None
        self.todo_window: tk.Toplevel | None = None
        self.mini_todo_window: tk.Toplevel | None = None
        self.mini_todo_body: tk.Frame | None = None
        self.help_window: tk.Toplevel | None = None
        self.reminder_bubble: tk.Toplevel | None = None
        self.context_panel: tk.Toplevel | None = None
        now_monotonic = time.monotonic()
        self.next_water_reminder = now_monotonic + WATER_REMINDER_SECONDS
        self.next_sitting_reminder = now_monotonic + SITTING_REMINDER_SECONDS
        self.follow_goal: tuple[int, int] | None = None
        self.follow_reacted = False
        self.follow_pause_until = 0.0

        self._build_menu()
        self._bind_events()
        self._schedule_next_action(600)
        self._schedule_blink()
        self._schedule_sleep_check()
        self._schedule_todo_check(1500)
        self._schedule_wellness_check()
        self._schedule_follow_mouse(300)
        self._update_mini_todo_visibility()

    def _load_settings(self) -> dict:
        defaults = {
            "roaming": True,
            "sound_enabled": True,
            "always_on_top": True,
            "auto_sleep": True,
            "show_mini_todo": False,
            "water_reminder": False,
            "sitting_reminder": False,
            "follow_mouse": False,
            "volume": 70,
            "pet_size_percent": 100,
        }
        if not self.settings_path.exists():
            return defaults
        try:
            loaded = json.loads(self.settings_path.read_text(encoding="utf-8"))
            for key in defaults:
                if key in loaded:
                    if key in ("volume", "pet_size_percent"):
                        defaults[key] = int(loaded[key])
                    else:
                        defaults[key] = bool(loaded[key])
            defaults["volume"] = max(0, min(100, defaults["volume"]))
            defaults["pet_size_percent"] = max(60, min(160, defaults["pet_size_percent"]))
        except (OSError, ValueError, TypeError):
            pass
        return defaults

    def _save_settings(self) -> None:
        self.settings.update(
            roaming=self.roaming,
            sound_enabled=self.sound_enabled,
            always_on_top=bool(self.root.attributes("-topmost")),
            auto_sleep=self.auto_sleep,
            show_mini_todo=self.show_mini_todo,
            water_reminder=self.water_reminder_enabled,
            sitting_reminder=self.sitting_reminder_enabled,
            follow_mouse=self.follow_mouse_enabled,
            volume=self.volume,
            pet_size_percent=self.pet_size_percent,
        )
        self.settings_path.write_text(
            json.dumps(self.settings, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )

    def _load_todos(self) -> list[dict]:
        if not self.todos_path.exists():
            return []
        try:
            data = json.loads(self.todos_path.read_text(encoding="utf-8"))
            if isinstance(data, list):
                return [item for item in data if isinstance(item, dict) and item.get("title")]
        except (OSError, ValueError, TypeError):
            pass
        return []

    def _save_todos(self) -> None:
        self.todos_path.write_text(
            json.dumps(self.todos, ensure_ascii=False, indent=2),
            encoding="utf-8",
        )

    def _startup_command(self) -> str:
        if getattr(sys, "frozen", False):
            return f'"{Path(sys.executable).resolve()}"'
        executable = Path(sys.executable).resolve()
        if executable.name.lower() == "python.exe":
            pythonw = executable.with_name("pythonw.exe")
            if pythonw.exists():
                executable = pythonw
        return f'"{executable}" "{Path(__file__).resolve()}"'

    def _is_auto_start_enabled(self) -> bool:
        key_path = r"Software\Microsoft\Windows\CurrentVersion\Run"
        try:
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER, key_path) as key:
                value, _ = winreg.QueryValueEx(key, STARTUP_VALUE_NAME)
                return bool(value)
        except OSError:
            return False

    def _set_auto_start(self, enabled: bool) -> None:
        key_path = r"Software\Microsoft\Windows\CurrentVersion\Run"
        with winreg.CreateKey(winreg.HKEY_CURRENT_USER, key_path) as key:
            if enabled:
                winreg.SetValueEx(key, STARTUP_VALUE_NAME, 0, winreg.REG_SZ, self._startup_command())
            else:
                try:
                    winreg.DeleteValue(key, STARTUP_VALUE_NAME)
                except FileNotFoundError:
                    pass

    def _load_images(self) -> dict[str, ImageTk.PhotoImage | list[ImageTk.PhotoImage]]:
        assets = resource_dir()

        def load(name: str) -> ImageTk.PhotoImage:
            path = assets / name
            if not path.exists():
                raise FileNotFoundError(f"缺少素材：{path}")
            image = Image.open(path).convert("RGBA")
            image = image.resize((self.window_size, self.window_size), Image.Resampling.LANCZOS)
            return ImageTk.PhotoImage(image)

        return {
            "idle": load("front_master.png"),
            "blink_half": load("blink_half.png"),
            "blink_closed": load("blink_closed.png"),
            "dizzy": load("dizzy.png"),
            "drag": load("drag_surprised.png"),
            "bounce_happy": load("bounce_happy.png"),
            "annoyed": load("click_annoyed.png"),
            "look_left": load("look_left.png"),
            "look_right": load("look_right.png"),
            "left": [load(f"walk_left_0{i}.png") for i in range(1, 4)],
            "right": [load(f"walk_right_0{i}.png") for i in range(1, 4)],
        }

    def _build_menu(self) -> None:
        self.menu = None

    def _bind_events(self) -> None:
        # Canvas fills the whole window. Binding both canvas and root causes one
        # physical release to bubble through twice and be misread as a click.
        self.canvas.bind("<ButtonPress-1>", self.start_drag)
        self.canvas.bind("<B1-Motion>", self.drag)
        self.canvas.bind("<ButtonRelease-1>", self.end_drag)
        self.canvas.bind("<Button-3>", self.show_menu)
        self.root.bind("<Escape>", lambda _event: self.close())

    def _show(self, image: ImageTk.PhotoImage) -> None:
        self.canvas.itemconfigure(self.sprite, image=image)

    def _play_sound(self, name: str) -> None:
        if not self.sound_enabled or self.volume <= 0:
            return
        path = sound_dir() / f"{name}.wav"
        if self.mixer_ready and path.exists():
            try:
                sound = self.sound_cache.get(name)
                if sound is None:
                    sound = pygame.mixer.Sound(str(path))
                    self.sound_cache[name] = sound
                sound.set_volume(self.volume / 100)
                sound.play()
            except pygame.error:
                pass
        elif path.exists():
            winsound.PlaySound(
                str(path),
                winsound.SND_FILENAME | winsound.SND_ASYNC | winsound.SND_NODEFAULT,
            )

    def _place(self) -> None:
        self.root.geometry(f"{self.window_size}x{self.window_size}+{int(self.x)}+{int(self.y)}")
        self._position_mini_todo()

    def _schedule_next_action(self, delay: int | None = None) -> None:
        if self.action_job:
            self.root.after_cancel(self.action_job)
        wait = delay if delay is not None else random.randint(1400, 4200)
        self.action_job = self.root.after(wait, self._choose_action)

    def _choose_action(self) -> None:
        self.action_job = None
        if not self.roaming or self.dragging or self.reacting:
            self._schedule_next_action()
            return
        if random.random() < 0.56:
            self._start_walk()
        else:
            self._random_idle_action()

    def _random_idle_action(self) -> None:
        self.effect_token += 1
        token = self.effect_token
        self.reacting = True
        action = random.choice(("look", "doze", "bounce"))

        if action == "look":
            if random.choice((True, False)):
                first, second = self.images["look_left"], self.images["look_right"]
            else:
                first, second = self.images["look_right"], self.images["look_left"]
            sequence = [
                (self.images["idle"], 0, 0, 180),
                (first, 0, 0, 620),
                (self.images["idle"], 0, 0, 180),
                (second, 0, 0, 520),
                (self.images["idle"], 0, 0, 0),
            ]
        elif action == "doze":
            self._start_zzz()
            sequence = [
                (self.images["blink_half"], 0, 2, 520),
                (self.images["blink_closed"], 0, 6, 3000),
                (self.images["blink_half"], 0, 3, 480),
                (self.images["idle"], 0, 0, 0),
            ]
        else:
            sequence = [
                (self.images["bounce_happy"], 0, 4, 100),
                (self.images["bounce_happy"], 0, -9, 120),
                (self.images["bounce_happy"], 0, -14, 100),
                (self.images["bounce_happy"], 0, -7, 100),
                (self.images["bounce_happy"], 0, 3, 110),
                (self.images["idle"], 0, 0, 0),
            ]

        def advance(index: int) -> None:
            if token != self.effect_token or not self.reacting or self.dragging:
                self._hide_zzz()
                return
            image, x, y, delay = sequence[index]
            self._show(image)
            self.canvas.coords(self.sprite, x, y)
            if index + 1 < len(sequence):
                self.root.after(delay, lambda: advance(index + 1))
            else:
                self.canvas.coords(self.sprite, 0, 0)
                self._hide_zzz()
                self.reacting = False
                self._schedule_next_action()

        advance(0)

    def _start_walk(self) -> None:
        if not self.roaming or self.dragging or self.reacting:
            self._schedule_next_action()
            return
        self.walking = True
        self.frame_index = 0
        self.direction = random.choice((-1, 1))
        duration = random.randint(18, 52)
        self._walk_step(duration)

    def _walk_step(self, remaining: int) -> None:
        if not self.walking or self.dragging or self.reacting or remaining <= 0:
            self.walking = False
            self._show(self.images["idle"])
            self._schedule_next_action()
            return

        next_x = self.x + self.direction * MOVE_PIXELS
        if next_x <= self.left:
            next_x = self.left
            self.direction = 1
            self._play_sound("turn")
        elif next_x >= self.right - self.window_size:
            next_x = self.right - self.window_size
            self.direction = -1
            self._play_sound("turn")

        self.x = next_x
        self._place()
        frames = self.images["left" if self.direction < 0 else "right"]
        self._show(frames[self.frame_index % len(frames)])
        self.frame_index += 1
        self.action_job = self.root.after(FRAME_MS, lambda: self._walk_step(remaining - 1))

    def _schedule_blink(self) -> None:
        if self.blink_job:
            self.root.after_cancel(self.blink_job)
        self.blink_job = self.root.after(random.randint(2200, 6000), self._blink)

    def _schedule_sleep_check(self) -> None:
        if self.sleep_check_job:
            self.root.after_cancel(self.sleep_check_job)
        self.sleep_check_job = self.root.after(1000, self._check_sleep_state)

    def _schedule_todo_check(self, delay: int = 15000) -> None:
        if self.todo_check_job:
            self.root.after_cancel(self.todo_check_job)
        self.todo_check_job = self.root.after(delay, self._check_due_todos)

    def _check_due_todos(self) -> None:
        self.todo_check_job = None
        now = datetime.now()
        due_task = None
        for task in self.todos:
            due = self._task_due_datetime(task)
            if due and not task.get("completed") and not task.get("reminded") and due <= now:
                due_task = task
                break
        if due_task:
            due_task["reminded"] = True
            due_task["reminded_at"] = now.isoformat(timespec="seconds")
            self._save_todos()
            self._todo_reminder_reaction(due_task["title"])
        self._schedule_todo_check()

    def _todo_reminder_reaction(self, title: str) -> None:
        self._gentle_reminder_reaction(f"该做「{title}」啦～")

    def _schedule_wellness_check(self) -> None:
        if self.wellness_check_job:
            self.root.after_cancel(self.wellness_check_job)
        self.wellness_check_job = self.root.after(30000, self._check_wellness_reminders)

    def _check_wellness_reminders(self) -> None:
        self.wellness_check_job = None
        now = time.monotonic()
        user_is_active = not self.sleeping and system_idle_seconds() < 120
        if user_is_active and self.water_reminder_enabled and now >= self.next_water_reminder:
            self.next_water_reminder = now + WATER_REMINDER_SECONDS
            self._gentle_reminder_reaction("记得喝口水呀～")
        elif user_is_active and self.sitting_reminder_enabled and now >= self.next_sitting_reminder:
            self.next_sitting_reminder = now + SITTING_REMINDER_SECONDS
            self._gentle_reminder_reaction("坐得有点久啦，起来活动一下吧～")
        self._schedule_wellness_check()

    def _schedule_follow_mouse(self, delay: int = 90) -> None:
        if self.follow_job:
            self.root.after_cancel(self.follow_job)
        self.follow_job = self.root.after(delay, self._follow_mouse_tick)

    def _follow_mouse_tick(self) -> None:
        self.follow_job = None
        if not self.follow_mouse_enabled:
            return
        if self.sleeping or self.dragging or self.patting or self.reacting or time.monotonic() < self.follow_pause_until:
            self._schedule_follow_mouse(100)
            return

        mouse_x, mouse_y = cursor_position()
        if self.follow_goal is None or abs(mouse_x - self.follow_goal[0]) > 36 or abs(mouse_y - self.follow_goal[1]) > 36:
            self.follow_goal = (mouse_x, mouse_y)
            self.follow_reacted = False

        target_x = max(self.left, min(mouse_x - self.window_size // 2, self.right - self.window_size))
        delta = target_x - self.x
        if abs(delta) > 7:
            self.walking = True
            self.direction = 1 if delta > 0 else -1
            self.x += self.direction * min(11, abs(delta))
            self._place()
            frames = self.images["right" if self.direction > 0 else "left"]
            self._show(frames[self.frame_index % len(frames)])
            self.frame_index += 1
            self._schedule_follow_mouse(80)
            return

        self.walking = False
        self._show(self.images["idle"])
        if not self.follow_reacted:
            self.follow_reacted = True
            head_top = self.y + self.window_size * 54 / WINDOW_SIZE
            feet_bottom = self.y + self.window_size * 212 / WINDOW_SIZE
            if mouse_y < head_top:
                if head_top - mouse_y <= 105:
                    self._follow_feedback(happy=True, jumping=True)
                else:
                    self._follow_feedback(happy=False, jumping=False)
            elif mouse_y > feet_bottom:
                self._follow_feedback(happy=False, jumping=False)
            else:
                self._follow_feedback(happy=True, jumping=False)
        self._schedule_follow_mouse(100)

    def _follow_feedback(self, happy: bool, jumping: bool) -> None:
        self.effect_token += 1
        token = self.effect_token
        self.reacting = True
        self.walking = False
        self.follow_pause_until = time.monotonic() + 1.25
        self._hide_interaction_effects()
        if happy:
            self._show(self.images["bounce_happy"])
            self._play_sound("tap")
            sequence = ((4, 90), (-8, 110), (-22 if jumping else -14, 120), (-8, 100), (2, 100), (0, 180))
        else:
            self._show(self.images["annoyed"])
            self._play_sound("scare")
            sequence = ((-6, 90), (6, 90), (-6, 90), (6, 90), (0, 260))

        def animate(index: int) -> None:
            if token != self.effect_token or self.dragging or self.patting:
                return
            offset, delay = sequence[index]
            if happy:
                self.canvas.coords(self.sprite, 0, offset)
                if index in (1, 2):
                    for heart_index, item in enumerate(self.heart_items[:2]):
                        self.canvas.coords(item, 177 + heart_index * 25, 56 - index * 7 - heart_index * 10)
                        self.canvas.itemconfigure(item, state="normal")
                        self.canvas.tag_raise(item)
            else:
                self.canvas.coords(self.sprite, offset, 0)
            if index + 1 < len(sequence):
                self.root.after(delay, lambda: animate(index + 1))
            else:
                self._hide_interaction_effects()
                self.canvas.coords(self.sprite, 0, 0)
                self._show(self.images["idle"])
                self.reacting = False

        animate(0)

    def _gentle_reminder_reaction(self, message: str) -> None:
        if self.sleeping:
            self.sleeping = False
            self._hide_zzz()
        self.effect_token += 1
        token = self.effect_token
        self.reacting = True
        self.walking = False
        if self.action_job:
            self.root.after_cancel(self.action_job)
            self.action_job = None
        self._hide_interaction_effects()
        self._show(self.images["bounce_happy"])
        self._play_sound("tap")
        self._show_reminder_bubble(message)

        sequence = ((5, 100), (-8, 120), (-13, 110), (-6, 110), (3, 120), (0, 500))

        def animate(index: int) -> None:
            if token != self.effect_token or self.dragging or self.patting:
                return
            y, delay = sequence[index]
            self.canvas.coords(self.sprite, 0, y)
            if index + 1 < len(sequence):
                self.root.after(delay, lambda: animate(index + 1))
            else:
                self.canvas.coords(self.sprite, 0, 0)
                self._show(self.images["idle"])
                self.reacting = False
                self._schedule_next_action(1000)

        animate(0)

    def _show_reminder_bubble(self, message: str) -> None:
        if self.reminder_bubble and self.reminder_bubble.winfo_exists():
            self.reminder_bubble.destroy()
        bubble = tk.Toplevel(self.root)
        self.reminder_bubble = bubble
        bubble.overrideredirect(True)
        bubble.attributes("-topmost", True)
        bubble.configure(bg="#d9899a")
        width, height = 285, 96
        x = min(self.right - width - 8, int(self.x + self.window_size - 70))
        y = max(self.top + 8, int(self.y - 46))
        bubble.geometry(f"{width}x{height}+{x}+{y}")
        inner = tk.Frame(bubble, bg="#fff7f8", bd=0)
        inner.pack(fill="both", expand=True, padx=2, pady=2)
        tk.Label(
            inner,
            text=f"{message}\n慢慢来，我陪着你。",
            justify="left",
            anchor="w",
            wraplength=250,
            bg="#fff7f8",
            fg="#624d55",
            font=("Microsoft YaHei UI", 10),
        ).pack(fill="both", expand=True, padx=13, pady=10)
        bubble.bind("<Button-1>", lambda _event: bubble.destroy())

        def close_if_current() -> None:
            if bubble.winfo_exists():
                bubble.destroy()

        bubble.after(9000, close_if_current)

    def _check_sleep_state(self) -> None:
        self.sleep_check_job = None
        idle = system_idle_seconds()
        hour = time.localtime().tm_hour
        threshold = 300 if hour >= 23 or hour < 6 else 600
        if self.sleeping:
            if not self.auto_sleep or idle < 1.5:
                self._wake_from_sleep()
        elif self.auto_sleep and idle >= threshold and not self.dragging and not self.patting:
            self._enter_sleep()
        self._schedule_sleep_check()

    def _enter_sleep(self) -> None:
        if self.sleeping:
            return
        self.effect_token += 1
        token = self.effect_token
        self.sleeping = True
        self.reacting = True
        self.walking = False
        if self.action_job:
            self.root.after_cancel(self.action_job)
            self.action_job = None
        self._hide_interaction_effects()
        self._show(self.images["blink_half"])

        def settle() -> None:
            if token != self.effect_token or not self.sleeping:
                return
            self._show(self.images["blink_closed"])
            self._animate_sleep(token, 0)

        self.root.after(520, settle)

    def _animate_sleep(self, token: int, step: int) -> None:
        if token != self.effect_token or not self.sleeping:
            return
        self.canvas.coords(self.sprite, 0, 5 + math.sin(step * 0.18) * 1.6)
        origins = ((168, 66), (187, 49), (207, 31))
        for index, (item, (base_x, base_y)) in enumerate(zip(self.zzz_items, origins)):
            local = (step - index * 5) % 34
            if step >= index * 5:
                self.canvas.coords(
                    item,
                    base_x + math.sin(step * 0.22 + index) * 2.5,
                    base_y - local * 0.45,
                )
                self.canvas.itemconfigure(item, state="normal")
                self.canvas.tag_raise(item)
        self.root.after(110, lambda: self._animate_sleep(token, step + 1))

    def _wake_from_sleep(self) -> None:
        if not self.sleeping:
            return
        self.effect_token += 1
        token = self.effect_token
        self.sleeping = False
        self._hide_zzz()
        self.canvas.coords(self.sprite, 0, 0)
        recovery = [
            (self.images["blink_closed"], 260),
            (self.images["blink_half"], 320),
            (self.images["idle"], 0),
        ]

        def advance(index: int) -> None:
            if token != self.effect_token or self.sleeping:
                return
            image, delay = recovery[index]
            self._show(image)
            if index + 1 < len(recovery):
                self.root.after(delay, lambda: advance(index + 1))
            else:
                self.reacting = False
                self._schedule_next_action(900)

        advance(0)

    def _blink(self) -> None:
        self.blink_job = None
        if self.walking or self.dragging or self.reacting:
            self._schedule_blink()
            return
        token = self.effect_token
        sequence = [
            (self.images["blink_half"], 65),
            (self.images["blink_closed"], 90),
            (self.images["blink_half"], 65),
            (self.images["idle"], 0),
        ]

        def advance(index: int) -> None:
            if token != self.effect_token or self.walking or self.dragging or self.reacting:
                self._schedule_blink()
                return
            image, delay = sequence[index]
            self._show(image)
            if index + 1 < len(sequence):
                self.root.after(delay, lambda: advance(index + 1))
            else:
                self._schedule_blink()

        advance(0)

    def start_drag(self, event: tk.Event) -> None:
        self._close_context_panel()
        if self.sleeping:
            self.woke_on_press = True
            self._wake_from_sleep()
            return
        self.pointer_down = True
        self.press_position = (event.x_root, event.y_root)
        self.drag_offset = (event.x_root - self.x, event.y_root - self.y)
        if 45 <= event.y <= 155:
            self.hold_job = self.root.after(420, self._start_pat)

    def _cancel_hold(self) -> None:
        if self.hold_job:
            self.root.after_cancel(self.hold_job)
            self.hold_job = None

    def _begin_drag(self) -> None:
        self._cancel_hold()
        if self.patting:
            self._end_pat(schedule=False)
        self.effect_token += 1
        self._hide_interaction_effects()
        self._hide_zzz()
        self.dragging = True
        self.drag_started_at = time.monotonic()
        self.reacting = False
        self.walking = False
        if self.action_job:
            self.root.after_cancel(self.action_job)
            self.action_job = None
        self._show(self.images["drag"])
        self._play_sound("scare")

    def drag(self, event: tk.Event) -> None:
        if not self.dragging:
            dx = event.x_root - self.press_position[0]
            dy = event.y_root - self.press_position[1]
            if dx * dx + dy * dy < 25:
                return
            self._begin_drag()
        if not self.dragging:
            return
        self.x = event.x_root - self.drag_offset[0]
        self.y = event.y_root - self.drag_offset[1]
        self.drag_phase = not self.drag_phase
        self.canvas.coords(self.sprite, 2 if self.drag_phase else -2, 1)
        self._place()

    def end_drag(self, _event: tk.Event) -> None:
        if self.woke_on_press:
            self.woke_on_press = False
            return
        self.pointer_down = False
        self._cancel_hold()
        if self.patting:
            self._end_pat()
            return
        if not self.dragging:
            if time.monotonic() - self.last_drag_release_at < 0.25:
                return
            self.register_click()
            return
        self.dragging = False
        self.last_drag_release_at = time.monotonic()
        drag_seconds = time.monotonic() - self.drag_started_at
        self.canvas.coords(self.sprite, 0, 0)
        self._show(self.images["idle"])
        self._play_sound("release")
        self.left, self.top, self.right, self.bottom = work_area()
        self.x = max(self.left, min(self.x, self.right - self.window_size))
        self.y = max(self.top, min(self.y, self.bottom - self.window_size))
        self._place()
        if drag_seconds >= LONG_DRAG_SECONDS:
            self.dizzy_reaction()
        else:
            self._schedule_next_action()

    @staticmethod
    def _star_points(cx: float, cy: float, outer: float = 7, inner: float = 3.2) -> list[float]:
        points: list[float] = []
        for index in range(10):
            radius = outer if index % 2 == 0 else inner
            angle = -math.pi / 2 + index * math.pi / 5
            points.extend((cx + math.cos(angle) * radius, cy + math.sin(angle) * radius))
        return points

    def _start_zzz(self) -> None:
        self.zzz_token += 1
        token = self.zzz_token
        origins = ((168, 66), (187, 49), (207, 31))

        def animate(step: int) -> None:
            if token != self.zzz_token or not self.reacting or self.dragging:
                return
            for index, (item, (base_x, base_y)) in enumerate(zip(self.zzz_items, origins)):
                delay = index * 2
                if step >= delay:
                    rise = ((step - delay) % 18) * 0.75
                    sway = math.sin(step * 0.45 + index) * 2
                    self.canvas.coords(item, base_x + sway, base_y - rise)
                    self.canvas.itemconfigure(item, state="normal")
                    self.canvas.tag_raise(item)
            if step < 46:
                self.root.after(90, lambda: animate(step + 1))

        animate(0)

    def _hide_zzz(self) -> None:
        self.zzz_token += 1
        for item in self.zzz_items:
            self.canvas.itemconfigure(item, state="hidden")

    def dizzy_reaction(self) -> None:
        self.effect_token += 1
        token = self.effect_token
        self.reacting = True
        self.walking = False
        self._show(self.images["dizzy"])
        self._play_sound("dizzy")
        total_steps = 52

        def animate(step: int) -> None:
            if token != self.effect_token or not self.reacting or self.dragging:
                self._hide_stars()
                return
            phase = step * 0.43
            self.canvas.coords(self.sprite, math.sin(phase) * 7, abs(math.sin(phase)) * 2)
            for index, star in enumerate(self.stars):
                angle = phase * 0.7 + index * (2 * math.pi / 3)
                radius_x = 43
                radius_y = 12
                cx = 128 + math.cos(angle) * radius_x
                cy = 49 + math.sin(angle) * radius_y
                self.canvas.coords(star, *self._star_points(cx, cy, 7, 3.1))
                self.canvas.itemconfigure(star, state="normal")
                self.canvas.tag_raise(star)
            if step < total_steps:
                self.root.after(50, lambda: animate(step + 1))
            else:
                self._finish_dizzy()

        animate(0)

    def _hide_stars(self) -> None:
        for star in self.stars:
            self.canvas.itemconfigure(star, state="hidden")

    def _finish_dizzy(self) -> None:
        self._hide_stars()
        self.canvas.coords(self.sprite, 0, 0)
        recovery = [
            (self.images["blink_closed"], 260),
            (self.images["blink_half"], 220),
            (self.images["idle"], 0),
        ]

        def advance(index: int) -> None:
            image, delay = recovery[index]
            self._show(image)
            if index + 1 < len(recovery):
                self.root.after(delay, lambda: advance(index + 1))
            else:
                self.reacting = False
                self._schedule_next_action(700)

        advance(0)

    def _start_pat(self) -> None:
        self.hold_job = None
        if not self.pointer_down or self.dragging:
            return
        self.effect_token += 1
        token = self.effect_token
        self.patting = True
        self.reacting = True
        self.walking = False
        if self.action_job:
            self.root.after_cancel(self.action_job)
            self.action_job = None
        self._hide_zzz()
        self._hide_interaction_effects()
        self._show(self.images["bounce_happy"])
        self._play_sound("pat")

        origins = ((165, 69), (188, 49), (208, 29))

        def animate(step: int) -> None:
            if token != self.effect_token or not self.patting or not self.pointer_down or self.dragging:
                return
            self.canvas.coords(self.sprite, math.sin(step * 0.42) * 2.5, 3 + math.sin(step * 0.35) * 1.5)
            for index, (item, (base_x, base_y)) in enumerate(zip(self.heart_items, origins)):
                local = (step - index * 3) % 24
                if step >= index * 3:
                    self.canvas.coords(item, base_x + math.sin(step * 0.3 + index) * 3, base_y - local * 0.65)
                    self.canvas.itemconfigure(item, state="normal")
                    self.canvas.tag_raise(item)
            self.root.after(80, lambda: animate(step + 1))

        animate(0)

    def _end_pat(self, schedule: bool = True) -> None:
        self.patting = False
        self.effect_token += 1
        self._hide_interaction_effects()
        self.canvas.coords(self.sprite, 0, 0)
        self._show(self.images["idle"])
        self.reacting = False
        if schedule:
            self._schedule_next_action(700)

    def _hide_interaction_effects(self) -> None:
        for item in self.heart_items:
            self.canvas.itemconfigure(item, state="hidden")

    def register_click(self) -> None:
        now = time.monotonic()
        if now - self.last_click_at <= 1.2:
            self.click_count += 1
        else:
            self.click_count = 1
        self.last_click_at = now
        if self.click_reset_job:
            self.root.after_cancel(self.click_reset_job)
        self.click_reset_job = self.root.after(2000, self._reset_click_count)
        self.click_reaction(self.click_count)

    def _reset_click_count(self) -> None:
        self.click_reset_job = None
        self.click_count = 0

    def click_reaction(self, count: int = 1) -> None:
        if self.dragging or self.patting:
            return
        self.effect_token += 1
        token = self.effect_token
        self._hide_interaction_effects()
        self.reacting = True
        self._play_sound("scare" if count >= 3 else "tap")
        self.walking = False
        if self.action_job:
            self.root.after_cancel(self.action_job)
            self.action_job = None

        if count >= 3:
            sequence = [
                (self.images["annoyed"], -3, 0, 180),
                (self.images["annoyed"], 3, 0, 180),
                (self.images["annoyed"], -2, 0, 180),
                (self.images["annoyed"], 2, 0, 180),
                (self.images["annoyed"], 0, 0, 360),
            ]
        else:
            sequence = [
                (self.images["blink_half"], 0, 7, 70),
                (self.images["blink_closed"], 0, 13, 90),
                (self.images["blink_half"], 0, -9, 85),
                (self.images["idle"], 0, 0, 110),
            ]

        def advance(index: int) -> None:
            if token != self.effect_token or self.dragging or self.patting:
                return
            image, x, y, delay = sequence[index]
            self._show(image)
            self.canvas.coords(self.sprite, x, y)
            if index + 1 < len(sequence):
                self.root.after(delay, lambda: advance(index + 1))
            else:
                self._hide_interaction_effects()
                self._show(self.images["idle"])
                self.canvas.coords(self.sprite, 0, 0)
                self.reacting = False
                self._schedule_next_action()

        advance(0)

    def show_menu(self, event: tk.Event) -> None:
        self._show_context_panel(event.x_root, event.y_root)

    def _close_context_panel(self) -> None:
        if self.context_panel and self.context_panel.winfo_exists():
            self.context_panel.destroy()
        self.context_panel = None

    def _show_context_panel(self, pointer_x: int, pointer_y: int) -> None:
        self._close_context_panel()
        panel = tk.Toplevel(self.root)
        self.context_panel = panel
        panel.overrideredirect(True)
        panel.attributes("-topmost", True)
        panel.configure(bg="#e89aaa")
        width, height = 210, 282
        x = min(max(6, pointer_x - 18), self.right - width - 6)
        y = min(max(6, pointer_y - 18), self.bottom - height - 6)
        panel.geometry(f"{width}x{height}+{x}+{y}")

        card = tk.Frame(panel, bg="#fff7f9")
        card.pack(fill="both", expand=True, padx=2, pady=2)
        buttons = tk.Frame(card, bg="#fff7f9")
        buttons.pack(fill="both", expand=True, padx=10, pady=10)

        def add_button(row: int, col: int, icon: str, command, accent: bool = False) -> None:
            bg = "#fde1e7" if accent else "#fff0f3"
            fg = "#c95e78" if accent else "#765563"
            button = tk.Button(
                buttons,
                text=icon,
                command=lambda: (self._close_context_panel(), command()),
                bg=bg,
                activebackground="#f7c7d2",
                activeforeground="#b34c68",
                fg=fg,
                relief="flat",
                bd=0,
                highlightthickness=0,
                width=4,
                height=1,
                font=("Segoe UI Symbol", 18),
                cursor="hand2",
            )
            button.grid(row=row, column=col, sticky="nsew", padx=3, pady=3)

        for col in range(2):
            buttons.columnconfigure(col, weight=1)
        add_button(0, 0, "🔊" if self.sound_enabled else "🔇", self.toggle_sound, True)
        add_button(0, 1, "📌" if bool(self.root.attributes("-topmost")) else "📍", self.toggle_topmost, True)
        add_button(1, 0, "☑", self.open_todo_list)
        add_button(1, 1, "ⓘ", self.open_help)
        add_button(2, 0, "⚙", self.open_settings)
        add_button(2, 1, "⌂", self.reset_position)
        add_button(3, 0, "Ⅱ" if self.roaming else "▶", self.toggle_roaming)
        add_button(3, 1, "×", self.close)
        panel.bind("<FocusOut>", lambda _event: panel.after(80, self._close_context_panel_if_unfocused))
        panel.focus_force()

    def _close_context_panel_if_unfocused(self) -> None:
        panel = self.context_panel
        if not panel or not panel.winfo_exists():
            return
        focus = self.root.focus_get()
        if focus is None or not str(focus).startswith(str(panel)):
            self._close_context_panel()

    def _todo_time_label(self, task: dict) -> str:
        due_date = task.get("due_date")
        if not due_date:
            return ""
        try:
            task_date = date.fromisoformat(due_date)
        except ValueError:
            return ""
        days = (task_date - date.today()).days
        if days == 0:
            return task.get("due_time") or "今天"
        if days == 1:
            return "明天"
        if days == 2:
            return "后天"
        if days < 0:
            return "已过期"
        return "更久"

    def _task_due_datetime(self, task: dict) -> datetime | None:
        if not task.get("due_date") or not task.get("due_time"):
            return None
        try:
            return datetime.fromisoformat(f'{task["due_date"]}T{task["due_time"]}:00')
        except ValueError:
            return None

    def _pending_todos(self) -> list[dict]:
        pending = [task for task in self.todos if not task.get("completed")]
        pending.sort(key=lambda task: (self._task_due_datetime(task) or datetime.max, task.get("created_at", "")))
        return pending

    def _update_mini_todo_visibility(self) -> None:
        if not self.show_mini_todo:
            if self.mini_todo_window and self.mini_todo_window.winfo_exists():
                self.mini_todo_window.destroy()
            self.mini_todo_window = None
            self.mini_todo_body = None
            return
        if self.mini_todo_window and self.mini_todo_window.winfo_exists():
            self._refresh_mini_todo()
            return
        window = tk.Toplevel(self.root)
        self.mini_todo_window = window
        window.overrideredirect(True)
        window.attributes("-topmost", True)
        window.configure(bg="#dc8b9d")
        body = tk.Frame(window, bg="#fff8fa")
        body.pack(fill="both", expand=True, padx=1, pady=1)
        self.mini_todo_body = body
        window.bind("<Button-3>", lambda _event: self.open_todo_list())
        self._refresh_mini_todo()

    def _position_mini_todo(self) -> None:
        window = getattr(self, "mini_todo_window", None)
        if not window or not window.winfo_exists():
            return
        window.update_idletasks()
        width = max(1, window.winfo_width())
        height = max(1, window.winfo_height())
        preferred_x = int(self.x + self.window_size - 42)
        if preferred_x + width > self.right - 4:
            preferred_x = int(self.x - width + 42)
        x = max(self.left + 4, min(preferred_x, self.right - width - 4))
        y = max(self.top + 4, min(int(self.y + 24), self.bottom - height - 4))
        window.geometry(f"+{x}+{y}")

    def _refresh_mini_todo(self) -> None:
        body = self.mini_todo_body
        window = self.mini_todo_window
        if not body or not window or not body.winfo_exists() or not window.winfo_exists():
            return
        for child in body.winfo_children():
            child.destroy()
        pending = self._pending_todos()
        visible = pending[:5]
        if not visible:
            tk.Label(
                body,
                text="暂无待办",
                bg="#fff8fa",
                fg="#a98e97",
                font=("Microsoft YaHei UI", 8),
                padx=7,
                pady=5,
            ).pack()
        for task in visible:
            row = tk.Frame(body, bg="#fff8fa")
            row.pack(fill="x")
            tk.Button(
                row,
                text="☐",
                command=lambda task_id=task["id"]: self._toggle_todo(task_id),
                relief="flat",
                bd=0,
                bg="#fff8fa",
                activebackground="#ffecef",
                fg="#df8195",
                font=("Segoe UI Symbol", 9),
                padx=2,
                pady=0,
            ).pack(side="left")
            display_title = task["title"] if len(task["title"]) <= 13 else task["title"][:12] + "…"
            tk.Label(
                row,
                text=display_title,
                anchor="w",
                bg="#fff8fa",
                fg="#514349",
                font=("Microsoft YaHei UI", 8),
                width=14,
            ).pack(side="left", padx=(0, 2))
            time_label = self._todo_time_label(task)
            tk.Label(
                row,
                text=time_label,
                anchor="e",
                bg="#fff8fa",
                fg="#cb7185",
                font=("Microsoft YaHei UI", 7),
                width=5,
            ).pack(side="right", padx=(0, 4))
        if len(pending) > len(visible):
            tk.Label(
                body,
                text=f"还有 {len(pending) - len(visible)} 项",
                bg="#fff8fa",
                fg="#a98e97",
                font=("Microsoft YaHei UI", 7),
                pady=2,
            ).pack(fill="x")
        window.update_idletasks()
        width = 190
        height = max(26, body.winfo_reqheight() + 2)
        window.geometry(f"{width}x{height}")
        self._position_mini_todo()

    def open_todo_list(self) -> None:
        if self.todo_window and self.todo_window.winfo_exists():
            self.todo_window.deiconify()
            self.todo_window.lift()
            self.todo_window.focus_force()
            self._refresh_todo_window()
            return

        window = tk.Toplevel(self.root)
        self.todo_window = window
        window.title("待办清单")
        window_width, window_height = 540, 650
        center_x = self.left + max(0, (self.right - self.left - window_width) // 2)
        center_y = self.top + max(0, (self.bottom - self.top - window_height) // 2)
        window.geometry(f"{window_width}x{window_height}+{center_x}+{center_y}")
        window.minsize(500, 560)
        window.attributes("-topmost", True)
        window.configure(bg="#fff9fa")

        tk.Label(
            window,
            text="待办清单",
            font=("Microsoft YaHei UI", 16, "bold"),
            bg="#fff9fa",
            fg="#654b55",
        ).pack(pady=(15, 8))

        form = tk.Frame(window, bg="#fbecef", bd=1, relief="solid")
        form.pack(fill="x", padx=18, pady=(0, 10))
        tk.Label(form, text="任务", bg="#fbecef", font=("Microsoft YaHei UI", 10)).grid(row=0, column=0, padx=(12, 5), pady=10)
        title_entry = tk.Entry(form, font=("Microsoft YaHei UI", 10))
        title_entry.grid(row=0, column=1, columnspan=5, sticky="ew", padx=(0, 12), pady=10)

        tk.Label(form, text="日期", bg="#fbecef", font=("Microsoft YaHei UI", 10)).grid(row=1, column=0, padx=(12, 5), pady=(0, 10))
        date_mode = ttk.Combobox(form, values=("无日期", "今天", "明天", "后天", "自定义"), state="readonly", width=8)
        date_mode.set("今天")
        date_mode.grid(row=1, column=1, sticky="w", pady=(0, 10))
        tk.Label(form, text="时间", bg="#fbecef", font=("Microsoft YaHei UI", 10)).grid(row=1, column=2, padx=(10, 4), pady=(0, 10))
        time_values = ["不设置"] + [f"{hour:02d}:{minute:02d}" for hour in range(24) for minute in (0, 15, 30, 45)]
        time_picker = ttk.Combobox(form, values=time_values, state="readonly", width=7, height=12)
        time_picker.set("不设置")
        time_picker.grid(row=1, column=3, pady=(0, 10))
        tk.Label(form, text="自定义日期", bg="#fbecef", font=("Microsoft YaHei UI", 9)).grid(row=1, column=4, padx=(10, 4), pady=(0, 10))
        custom_date = tk.Entry(form, width=11)
        custom_date.insert(0, date.today().isoformat())
        custom_date.grid(row=1, column=5, sticky="w", padx=(0, 12), pady=(0, 10))
        form.columnconfigure(1, weight=1)

        hint = tk.Label(form, text="时间可按15分钟间隔选择；不设置时间则不会到点提醒", bg="#fbecef", fg="#9a7f88", font=("Microsoft YaHei UI", 8))
        hint.grid(row=2, column=0, columnspan=5, sticky="w", padx=12, pady=(0, 10))

        def add_task() -> None:
            title = title_entry.get().strip()
            if not title:
                messagebox.showwarning("无法添加", "请先填写任务标题。", parent=window)
                return
            mode = date_mode.get()
            due_date: str | None = None
            if mode != "无日期":
                if mode == "今天":
                    selected_date = date.today()
                elif mode == "明天":
                    selected_date = date.today() + timedelta(days=1)
                elif mode == "后天":
                    selected_date = date.today() + timedelta(days=2)
                else:
                    try:
                        selected_date = date.fromisoformat(custom_date.get().strip())
                    except ValueError:
                        messagebox.showwarning("日期格式错误", "自定义日期请使用 YYYY-MM-DD。", parent=window)
                        return
                due_date = selected_date.isoformat()
            selected_time = time_picker.get()
            due_time = selected_time if due_date and selected_time != "不设置" else ""
            self.todos.append(
                {
                    "id": uuid.uuid4().hex,
                    "title": title,
                    "due_date": due_date,
                    "due_time": due_time or None,
                    "completed": False,
                    "created_at": datetime.now().isoformat(timespec="seconds"),
                    "completed_at": None,
                    "reminded": False,
                }
            )
            self._save_todos()
            title_entry.delete(0, "end")
            self._refresh_todo_window()
            self._refresh_mini_todo()

        tk.Button(form, text="添加任务", command=add_task, bg="#ef9daf", fg="white", activebackground="#e8899d", relief="flat", padx=13).grid(
            row=2, column=5, padx=(5, 12), pady=(0, 10), sticky="e"
        )
        title_entry.bind("<Return>", lambda _event: add_task())

        list_outer = tk.Frame(window, bg="#fff9fa")
        list_outer.pack(fill="both", expand=True, padx=18, pady=(0, 16))
        canvas = tk.Canvas(list_outer, bg="#fff9fa", highlightthickness=0)
        scrollbar = ttk.Scrollbar(list_outer, orient="vertical", command=canvas.yview)
        body = tk.Frame(canvas, bg="#fff9fa")
        canvas_window = canvas.create_window((0, 0), window=body, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")
        body.bind("<Configure>", lambda _event: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.bind("<Configure>", lambda event: canvas.itemconfigure(canvas_window, width=event.width))
        self.todo_list_body = body
        self._refresh_todo_window()

    def _refresh_todo_window(self) -> None:
        body = getattr(self, "todo_list_body", None)
        if body is None or not body.winfo_exists():
            return
        for child in body.winfo_children():
            child.destroy()
        pending = self._pending_todos()
        completed = [task for task in self.todos if task.get("completed")]
        completed.sort(key=lambda task: task.get("completed_at") or "", reverse=True)
        self._render_todo_section(body, "待完成", pending, completed=False)
        self._render_todo_section(body, "已完成", completed, completed=True)

    def _render_todo_section(self, parent: tk.Frame, title: str, tasks: list[dict], completed: bool) -> None:
        header = tk.Label(parent, text=f"{title}  {len(tasks)}", anchor="w", bg="#fff9fa", fg="#765e67", font=("Microsoft YaHei UI", 11, "bold"))
        header.pack(fill="x", pady=(8, 5))
        if not tasks:
            tk.Label(parent, text="暂无任务", anchor="w", bg="#fff9fa", fg="#b39da5", font=("Microsoft YaHei UI", 9)).pack(fill="x", padx=8, pady=(2, 8))
            return
        for task in tasks:
            row = tk.Frame(parent, bg="#ffffff", bd=1, relief="solid")
            row.pack(fill="x", pady=3)
            tk.Button(
                row,
                text="☑" if completed else "☐",
                command=lambda task_id=task["id"]: self._toggle_todo(task_id),
                relief="flat",
                bg="#ffffff",
                activebackground="#fff0f3",
                fg="#df8195",
                font=("Segoe UI Symbol", 13),
                width=2,
            ).pack(side="left", padx=(5, 2), pady=5)
            font_style = ("Microsoft YaHei UI", 10, "overstrike") if completed else ("Microsoft YaHei UI", 10)
            tk.Label(
                row,
                text=task["title"],
                anchor="w",
                justify="left",
                wraplength=320,
                bg="#ffffff",
                fg="#a69a9e" if completed else "#4f4146",
                font=font_style,
            ).pack(side="left", fill="x", expand=True, padx=3, pady=8)
            label = self._todo_time_label(task)
            if label:
                tk.Label(row, text=label, bg="#ffffff", fg="#d0778a", font=("Microsoft YaHei UI", 9)).pack(side="left", padx=7)
            tk.Button(
                row,
                text="×",
                command=lambda task_id=task["id"]: self._delete_todo(task_id),
                relief="flat",
                bg="#ffffff",
                activebackground="#fff0f3",
                fg="#aa949c",
                font=("Segoe UI", 11),
            ).pack(side="right", padx=(2, 7))

    def _toggle_todo(self, task_id: str) -> None:
        completed_now = False
        for task in self.todos:
            if task.get("id") == task_id:
                was_completed = bool(task.get("completed"))
                task["completed"] = not was_completed
                completed_now = task["completed"] and not was_completed
                task["completed_at"] = datetime.now().isoformat(timespec="seconds") if task["completed"] else None
                break
        self._save_todos()
        if completed_now:
            self._play_sound("todo_done")
        self._refresh_todo_window()
        self._refresh_mini_todo()

    def _delete_todo(self, task_id: str) -> None:
        self.todos = [task for task in self.todos if task.get("id") != task_id]
        self._save_todos()
        self._refresh_todo_window()
        self._refresh_mini_todo()

    def open_help(self) -> None:
        if self.help_window and self.help_window.winfo_exists():
            self.help_window.deiconify()
            self.help_window.lift()
            self.help_window.focus_force()
            return

        window = tk.Toplevel(self.root)
        self.help_window = window
        window.title("查看说明")
        width, height = 560, 650
        center_x = self.left + max(0, (self.right - self.left - width) // 2)
        center_y = self.top + max(0, (self.bottom - self.top - height) // 2)
        window.geometry(f"{width}x{height}+{center_x}+{center_y}")
        window.minsize(480, 520)
        window.attributes("-topmost", True)
        window.configure(bg="#fff9fa")

        tk.Label(
            window,
            text="使用说明",
            font=("Microsoft YaHei UI", 16, "bold"),
            bg="#fff9fa",
            fg="#654b55",
        ).pack(pady=(16, 9))

        content = """【基础操作】
• 桌宠会在屏幕底部随机左右走动，并随机眨眼、观察、困倦或开心弹跳。
• 按住鼠标左键拖动桌宠；拖动超过 1.5 秒后松手，会触发眩晕效果。
• 在桌宠头部按住约 0.4 秒，会触发摸头表情和爱心。
• 快速点击 1～2 次会触发普通反馈；1.2 秒内连续点击 3 次以上会出现不耐烦反应。
• 右键桌宠可以暂停走动、开关音效、复位位置、打开待办清单和设置。
• 按 Esc 可以退出桌宠。

【睡眠模式】
• 设置中开启“长时间无操作时自动睡眠”后，桌宠会检测电脑的键盘和鼠标活动。
• 白天连续 10 分钟无操作，桌宠进入睡眠。
• 夜间 23:00 至次日 6:00，连续 5 分钟无操作后进入睡眠。
• 睡眠时桌宠停止走动和互动，保持闭眼呼吸，并持续显示 zzz。
• 任意鼠标或键盘操作都会唤醒桌宠。
• 可以在设置中关闭自动睡眠。

【待办清单】
• 右键桌宠，选择“待办清单…”即可打开完整清单。
• 输入任务标题，选择今天、明天、后天、自定义日期或无日期。
• 时间使用下拉框选择，以 15 分钟为间隔；选择“不设置”则不会到点提醒。
• 当天任务显示具体时间；明天显示“明天”；后天显示“后天”；更晚显示“更久”。
• 点击任务左侧方框即可完成任务。完成项会移动到下方“已完成”并以划掉形式显示。
• 再次点击已完成项的方框可以恢复任务；点击 × 可以删除任务。

【到点提醒】
• 设置了日期和具体时间的未完成任务，到点后会自动提醒一次。
• 桌宠会切换开心表情并弹跳，右上方弹出温柔提示聊天框。
• 提醒框会在 9 秒后自动关闭，也可以单击关闭。

【迷你待办】
• 在设置中勾选“在桌宠旁始终显示迷你待办”，即可开启紧凑悬浮清单。
• 迷你清单只显示未完成任务，并会跟随桌宠移动。
• 点击迷你清单中的方框，可以直接完成任务。
• 最多显示 5 条任务，超出的任务会显示剩余数量。

【健康提醒】
• 设置中可以分别开启喝水提醒和久坐提醒。
• 喝水提醒每 45 分钟触发一次，久坐提醒每 60 分钟触发一次。
• 提醒时桌宠会开心弹跳，并在右上方显示温柔聊天框。
• 用户离开电脑或桌宠正在睡眠时暂不弹出，返回后再提醒。

【跟随鼠标】
• 在设置中开启“跟随鼠标”后，桌宠会跑向鼠标所在的水平位置。
• 鼠标在角色可触及范围内时，桌宠会开心；在头顶上方但可及的位置会跳起来够。
• 鼠标太高或位于角色脚下时，桌宠会显示不耐烦反应。
• 移动鼠标到新位置后，桌宠才会再次判断和反馈。

【设置】
• 右键选择“设置…”，可以开关随机走动、互动音效、自动睡眠、迷你待办、健康提醒和始终置顶。
• 可以选择登录 Windows 后自动启动桌宠。
• 所有设置和待办任务都会自动保存在桌宠文件夹中。
"""

        viewer = scrolledtext.ScrolledText(
            window,
            wrap="word",
            font=("Microsoft YaHei UI", 10),
            bg="#ffffff",
            fg="#514349",
            relief="solid",
            bd=1,
            padx=14,
            pady=12,
            spacing1=2,
            spacing3=5,
        )
        viewer.pack(fill="both", expand=True, padx=18, pady=(0, 12))
        viewer.insert("1.0", content)
        viewer.configure(state="disabled")

        tk.Button(window, text="关闭", width=11, command=window.destroy).pack(pady=(0, 14))
        window.protocol("WM_DELETE_WINDOW", window.destroy)

    def open_settings(self) -> None:
        if self.settings_window and self.settings_window.winfo_exists():
            self.settings_window.deiconify()
            self.settings_window.lift()
            self.settings_window.focus_force()
            return

        window = tk.Toplevel(self.root)
        self.settings_window = window
        window.title("B站@布洛Blo  小红书@madoka")
        window.resizable(False, False)
        window.attributes("-topmost", True)
        width, height = 360, 660
        x = max(0, int(self.x + self.window_size / 2 - width / 2))
        y = max(0, int(self.y - height + 80))
        window.geometry(f"{width}x{height}+{x}+{y}")
        window.configure(bg="#fff0f4")

        header = tk.Frame(window, bg="#ffe0e8", bd=0)
        header.pack(fill="x", padx=12, pady=(12, 10))
        tk.Label(header, text="设置", font=("Microsoft YaHei UI", 15, "bold"), bg="#ffe0e8", fg="#684c55").pack(side="left", padx=14, pady=8)
        tk.Label(header, text="♡", font=("Segoe UI Symbol", 17), bg="#ffe0e8", fg="#d87691").pack(side="right", padx=14)

        roaming_var = tk.BooleanVar(value=self.roaming)
        sound_var = tk.BooleanVar(value=self.sound_enabled)
        topmost_var = tk.BooleanVar(value=bool(self.root.attributes("-topmost")))
        auto_sleep_var = tk.BooleanVar(value=self.auto_sleep)
        mini_todo_var = tk.BooleanVar(value=self.show_mini_todo)
        water_var = tk.BooleanVar(value=self.water_reminder_enabled)
        sitting_var = tk.BooleanVar(value=self.sitting_reminder_enabled)
        follow_mouse_var = tk.BooleanVar(value=self.follow_mouse_enabled)
        startup_var = tk.BooleanVar(value=self._is_auto_start_enabled())
        volume_var = tk.IntVar(value=self.volume)
        pet_size_var = tk.IntVar(value=self.pet_size_percent)

        options = tk.Frame(window, bg="#fff7f9", bd=1, relief="solid")
        options.pack(fill="x", padx=18, pady=(0, 4))
        for text, variable in (
            ("允许随机走动和待机动作", roaming_var),
            ("开启互动音效", sound_var),
            ("长时间无操作时自动睡眠", auto_sleep_var),
            ("在桌宠旁始终显示迷你待办", mini_todo_var),
            ("喝水提醒（每 45 分钟）", water_var),
            ("久坐提醒（每 60 分钟）", sitting_var),
            ("跟随鼠标", follow_mouse_var),
            ("桌宠始终置顶", topmost_var),
            ("登录 Windows 后自动启动", startup_var),
        ):
            tk.Checkbutton(
                options,
                text=text,
                variable=variable,
                bg="#fff7f9",
                activebackground="#ffe8ee",
                selectcolor="#f7c6d2",
                fg="#55434a",
                font=("Microsoft YaHei UI", 10),
                anchor="w",
            ).pack(fill="x", padx=12, pady=3)

        sliders = tk.Frame(window, bg="#fff7f9", bd=1, relief="solid")
        sliders.pack(fill="x", padx=18, pady=(5, 2))
        tk.Scale(
            sliders, from_=0, to=100, orient="horizontal", variable=volume_var,
            label="\u97f3\u91cf", resolution=5, bg="#fff7f9", troughcolor="#f6c3d0",
            activebackground="#df8195", highlightthickness=0, fg="#55434a",
            font=("Microsoft YaHei UI", 10),
        ).pack(fill="x", padx=12, pady=(5, 0))
        tk.Scale(
            sliders, from_=60, to=160, orient="horizontal", variable=pet_size_var,
            label="\u684c\u5ba0\u5927\u5c0f (%)", resolution=5, bg="#fff7f9", troughcolor="#f6c3d0",
            activebackground="#df8195", highlightthickness=0, fg="#55434a",
            font=("Microsoft YaHei UI", 10),
        ).pack(fill="x", padx=12, pady=(0, 5))

        buttons = tk.Frame(window, bg="#fff0f4")
        buttons.pack(side="bottom", pady=15)

        def apply_and_close() -> None:
            try:
                self._apply_settings(
                    roaming_var.get(),
                    sound_var.get(),
                    auto_sleep_var.get(),
                    mini_todo_var.get(),
                    water_var.get(),
                    sitting_var.get(),
                    follow_mouse_var.get(),
                    topmost_var.get(),
                    startup_var.get(),
                    volume_var.get(),
                    pet_size_var.get(),
                )
            except OSError as exc:
                messagebox.showerror("设置失败", str(exc), parent=window)
                return
            window.destroy()

        tk.Button(buttons, text="保存", width=10, command=apply_and_close, bg="#ee9bad", activebackground="#df8195", fg="white", relief="flat", bd=0).pack(side="left", padx=7)
        tk.Button(buttons, text="取消", width=10, command=window.destroy, bg="#ffe0e8", activebackground="#f7c7d2", fg="#765563", relief="flat", bd=0).pack(side="left", padx=7)
        window.protocol("WM_DELETE_WINDOW", window.destroy)

    def _apply_settings(
        self,
        roaming: bool,
        sound_enabled: bool,
        auto_sleep: bool,
        show_mini_todo: bool,
        water_reminder: bool,
        sitting_reminder: bool,
        follow_mouse: bool,
        always_on_top: bool,
        auto_start: bool,
        volume: int,
        pet_size_percent: int,
    ) -> None:
        roaming_changed = self.roaming != roaming
        self.roaming = roaming
        self.sound_enabled = sound_enabled
        self.auto_sleep = auto_sleep
        self.show_mini_todo = show_mini_todo
        water_changed = self.water_reminder_enabled != water_reminder
        sitting_changed = self.sitting_reminder_enabled != sitting_reminder
        self.water_reminder_enabled = water_reminder
        self.sitting_reminder_enabled = sitting_reminder
        follow_changed = self.follow_mouse_enabled != follow_mouse
        self.follow_mouse_enabled = follow_mouse
        self.volume = max(0, min(100, int(volume)))
        self._set_pet_size(pet_size_percent)
        self.root.attributes("-topmost", always_on_top)
        self._set_auto_start(auto_start)
        if not sound_enabled or self.volume <= 0:
            winsound.PlaySound(None, 0)
            if self.mixer_ready:
                pygame.mixer.stop()
        if not auto_sleep and self.sleeping:
            self._wake_from_sleep()
        self._update_mini_todo_visibility()
        now_monotonic = time.monotonic()
        if water_changed and water_reminder:
            self.next_water_reminder = now_monotonic + WATER_REMINDER_SECONDS
        if sitting_changed and sitting_reminder:
            self.next_sitting_reminder = now_monotonic + SITTING_REMINDER_SECONDS
        if follow_changed:
            self.follow_goal = None
            self.follow_reacted = False
            if follow_mouse:
                self.walking = False
                if self.action_job:
                    self.root.after_cancel(self.action_job)
                    self.action_job = None
                self._schedule_follow_mouse(100)
            elif self.roaming:
                self._schedule_next_action(400)
        if roaming_changed:
            if roaming:
                # 跟随鼠标开启时由跟随定时器接管移动，避免随机待机动作抢占位置。
                if not follow_mouse:
                    self._schedule_next_action(300)
            else:
                self.walking = False
                if self.action_job:
                    self.root.after_cancel(self.action_job)
                    self.action_job = None
                self._show(self.images["idle"])
        self._save_settings()

    def _set_pet_size(self, percent: int) -> None:
        percent = max(60, min(160, int(percent)))
        if percent == self.pet_size_percent:
            return
        old_size = self.window_size
        self.pet_size_percent = percent
        self.window_size = round(WINDOW_SIZE * percent / 100)
        self.x += (old_size - self.window_size) / 2
        self.y += old_size - self.window_size
        self.x = max(self.left, min(self.x, self.right - self.window_size))
        self.y = max(self.top, min(self.y, self.bottom - self.window_size))
        self.canvas.configure(width=self.window_size, height=self.window_size)
        self.images = self._load_images()
        self._show(self.images["idle"])
        self._place()

    def toggle_sound(self) -> None:
        self.sound_enabled = not self.sound_enabled
        if not self.sound_enabled:
            winsound.PlaySound(None, 0)
            if self.mixer_ready:
                pygame.mixer.stop()
        else:
            self._play_sound("tap")
        self._save_settings()

    def toggle_topmost(self) -> None:
        enabled = not bool(self.root.attributes("-topmost"))
        self.root.attributes("-topmost", enabled)
        self._save_settings()

    def toggle_roaming(self) -> None:
        self.roaming = not self.roaming
        if not self.roaming:
            self.walking = False
            if self.action_job:
                self.root.after_cancel(self.action_job)
                self.action_job = None
            self._show(self.images["idle"])
        elif not self.follow_mouse_enabled:
            self._schedule_next_action(300)
        self._save_settings()

    def reset_position(self) -> None:
        self.left, self.top, self.right, self.bottom = work_area()
        self.x = self.right - self.window_size - 40
        self.y = self.bottom - self.window_size
        self._place()

    def close(self) -> None:
        self.root.destroy()

    def run(self) -> None:
        self.root.mainloop()


if __name__ == "__main__":
    DesktopPet().run()

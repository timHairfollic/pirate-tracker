"""
Fortnite Pirate Token Chest Tracker (with Duo sync) - v5
--------------------------------------------------------
UP arrow   = +1 chest (works even while Fortnite is focused)
DOWN arrow = undo your last chest

Duo sync: everyone types the same room code and presses Join.
Each tracker keeps its OWN chest count and shares it instantly through the
room's Firebase database. Whoever creates the room is its leader, and only
the leader can reset it.

Odds of at least one token = 1 - product of (1 - p) for every chest opened,
where p is the per-chest rate active when that chest was counted.
Normal: 1 in 137,500   Treasure Hour 1.5x: 1 in 91,667   Treasure Hour 2x: 1 in 68,750
"""
import json
import math
import os
import random
import subprocess
import sys
import threading
import time
import tkinter as tk
import tkinter.messagebox as mb
import tkinter.simpledialog as sd
import urllib.request
import uuid
from tkinter import font as tkfont

try:
    from pynput import keyboard
except ImportError:
    r = tk.Tk(); r.withdraw()
    mb.showerror("Missing package", "Open Command Prompt and run:\n\npython -m pip install pynput\n\nthen start the tracker again.")
    raise SystemExit

APP_VERSION = 5
# Where updates come from. version.txt holds the newest version number;
# pirate_token_tracker.pyw next to it is the new app. Leave "" to turn updates off.
UPDATE_BASE = "https://raw.githubusercontent.com/timHairfollic/pirate-tracker/main/"
UPDATE_API = "https://api.github.com/repos/timHairfollic/pirate-tracker/contents/pirate_token_tracker.pyw"
UPDATE_CHECK_EVERY = 10 * 60   # seconds

DB = "https://pirate-tracker-2dbd7-default-rtdb.firebaseio.com"

BASE_RATE = 1 / 137_500
MODES = {"Normal (1x)": 1.0, "Treasure Hour 1.5x": 1.5, "Treasure Hour 2x": 2.0}
_APP_DIR = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
SAVE_FILE = os.path.join(_APP_DIR, "pirate_tracker_save.json")
CODE_CHARS = "ACDEFHJKMNPRTUVWXY34679"   # no look-alikes (O/0, I/1/L, S/5, B/8, Z/2, G)

# Treasure-map palette: parchment, ink and sealing-wax red
BG, CARD, GOLD, TEXT, DIM, GREEN, RED = "#e9d3a0", "#dcc08a", "#7a1f12", "#2b1a0c", "#6b4a2b", "#2f5e22", "#8b1e1e"
CHAR = "#120a04"                      # burnt edge
SERIF = "Georgia"
BURN_LAYERS = [(4, 22, "#2a160a"), (10, 20, "#4a2a12"), (16, 18, "#6e4420"), (22, 16, "#94652f"),
               (28, 14, "#b78a4c"), (34, 12, "#d1ad70"), (40, 10, BG)]


def odds_from_counts(counts):
    """counts: {multiplier_str: number_of_chests} -> chance of at least one token."""
    miss = 1.0
    for mult, n in counts.items():
        miss *= (1 - BASE_RATE * float(mult)) ** n
    return 1 - miss


def tally(stack):
    c = {}
    for m in stack:
        k = str(float(m)).replace(".", "_")      # Firebase keys can't contain "."
        c[k] = c.get(k, 0) + 1
    return c


def untally(counts):
    out = {}
    for k, n in (counts or {}).items():
        try:
            m = str(float(str(k).replace("_", ".")))
            out[m] = out.get(m, 0) + max(0, int(n))
        except (ValueError, TypeError):
            pass
    return out


def db_request(path, method="GET", data=None, timeout=15):
    body = None if data is None else json.dumps(data).encode()
    req = urllib.request.Request(f"{DB}/{path}.json", data=body, method=method,
                                 headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read() or b"null")


class Tracker:
    def __init__(self, root):
        self.root = root
        self.cid = uuid.uuid4().hex[:12]   # this tracker's id in a room
        self.solo = []                     # solo chest multipliers
        self.room = None                   # active room code
        self.rooms = {}                    # code -> {"mine": [...], "epoch": n}
        self.others = {}                   # cid -> counts (current room, from the database)
        self.leader = None                 # cid of the room's leader
        self.mode = tk.StringVar(value="Normal (1x)")
        self.on_top = tk.BooleanVar(value=True)
        self.room_var = tk.StringVar()
        self._saved_geometry = None
        self._stream_gen = 0
        self._pulling = set()
        self._pull_again = False
        self.connected = False
        self.dirty = False
        self.sending = False
        self.send_error = False
        self.updating = False
        self.load()

        root.title(f"Pirate Token Tracker v{APP_VERSION}")
        root.configure(bg=CHAR)
        root.resizable(True, True)
        root.attributes("-topmost", True)
        self._scale = 1.0
        rnd = random.Random(1717)
        self.noise = [rnd.random() for _ in range(400)]
        self.bg = tk.Canvas(root, bg=CHAR, highlightthickness=0)
        self.bg.place(x=0, y=0, relwidth=1, relheight=1)
        self.page = tk.Frame(root, bg=BG)
        page = self.page

        self.base_sizes = {"title": 13, "small": 9, "big": 34, "odds": 28, "body": 10, "plain": 9}
        self.fonts = {k: tkfont.Font(family=SERIF, size=s, weight="normal" if k == "plain" else "bold")
                      for k, s in self.base_sizes.items()}
        F = self.fonts

        self.header = tk.Canvas(page, bg=BG, highlightthickness=0, height=74, width=420)
        self.header.pack(pady=(4, 2), fill="x")
        self.header.bind("<Configure>", lambda e: self.draw_header())

        card = tk.Frame(page, bg=CARD, padx=24, pady=14, highlightthickness=2,
                        highlightbackground="#8a6236", highlightcolor="#8a6236")
        card.pack(padx=16, fill="both", expand=True)
        inner = tk.Frame(card, bg=CARD)
        inner.pack(expand=True)
        self.count_title = tk.Label(inner, bg=CARD, fg=DIM, font=F["small"])
        self.count_title.pack()
        self.count_lbl = tk.Label(inner, bg=CARD, fg=TEXT, font=F["big"])
        self.count_lbl.pack()
        self.split_lbl = tk.Label(inner, bg=CARD, fg=DIM, font=F["plain"])
        self.split_lbl.pack()
        tk.Label(inner, text="~ CHANCE YE'D HAVE FOUND THE TOKEN ~", bg=CARD, fg=DIM, font=F["small"]).pack(pady=(8, 0))
        self.odds_lbl = tk.Label(inner, bg=CARD, fg=GOLD, font=F["odds"])
        self.odds_lbl.pack()
        self.per_lbl = tk.Label(inner, bg=CARD, fg=DIM, font=F["plain"])
        self.per_lbl.pack(pady=(4, 0))

        row = tk.Frame(page, bg=BG)
        row.pack(pady=(10, 6))
        tk.Label(row, text="Rate:", bg=BG, fg=TEXT, font=F["body"]).pack(side="left")
        opt = tk.OptionMenu(row, self.mode, *MODES, command=lambda _: self.refresh())
        opt.config(bg=CARD, fg=TEXT, activebackground="#c49a52", activeforeground=TEXT, highlightthickness=0,
                   relief="ridge", bd=2, font=F["body"])
        opt["menu"].config(bg=BG, fg=TEXT, activebackground="#c49a52", activeforeground=TEXT, font=F["body"])
        opt.pack(side="left", padx=6)

        btns = tk.Frame(page, bg=BG)
        btns.pack()
        for txt, cmd in (("+1", self.add), ("Undo", self.undo), ("Set count", self.set_count)):
            tk.Button(btns, text=txt, command=cmd, width=8, **self.btn_style()).pack(side="left", padx=4)
        self.reset_btn = tk.Button(btns, text="Reset", command=self.reset, width=8, **self.btn_style())
        self.reset_btn.pack(side="left", padx=4)

        duo = tk.Frame(page, bg=BG)
        duo.pack(pady=(10, 0))
        tk.Label(duo, text="Duo room:", bg=BG, fg=TEXT, font=F["body"]).pack(side="left")
        self.room_entry = tk.Entry(duo, textvariable=self.room_var, width=9, bg="#f3e4bf", fg=TEXT,
                                   insertbackground=TEXT, relief="sunken", bd=2, font=F["body"], justify="center")
        self.room_entry.pack(side="left", padx=4, ipady=2)
        self.join_btn = tk.Button(duo, text="Join", command=self.toggle_room, width=6, **self.btn_style())
        self.join_btn.pack(side="left", padx=2)
        self.code_btn = tk.Button(duo, text="New code", command=self.new_code, **self.btn_style())
        self.code_btn.pack(side="left", padx=2)
        self.status_lbl = tk.Label(page, bg=BG, fg=DIM, font=F["plain"])
        self.status_lbl.pack(pady=(4, 0))

        tk.Checkbutton(page, text="Keep on top of game", variable=self.on_top, bg=BG, fg=DIM,
                       selectcolor="#f3e4bf", activebackground=BG, activeforeground=TEXT, font=F["plain"],
                       command=lambda: root.attributes("-topmost", self.on_top.get())).pack(pady=(6, 0))
        tk.Label(page, text="↑ Up arrow = +1 chest    ↓ Down arrow = undo", bg=BG, fg=DIM,
                 font=F["plain"]).pack(pady=(4, 6))

        root.update_idletasks()
        self.base_w = page.winfo_reqwidth() + 2 * 62
        self.base_h = page.winfo_reqheight() + 2 * 62
        root.geometry(f"{self.base_w}x{self.base_h}")
        root.minsize(int(self.base_w * 0.6), int(self.base_h * 0.6))
        self._scale = 1.0
        root.bind("<Configure>", self.on_resize)
        self.page.place(relx=0.5, rely=0.5, anchor="center")
        self.root.after(50, self.draw_map)
        if self._saved_geometry:
            try:
                root.geometry(self._saved_geometry)
            except tk.TclError:
                pass

        if self.room:
            self.room_var.set(self.room)
            self.enter_room(self.room)
        self.refresh()
        keyboard.Listener(on_press=self.on_key, daemon=True).start()
        root.protocol("WM_DELETE_WINDOW", self.close)
        self.root.after(1500, self.check_for_update)

    # ---------- state helpers ----------
    @property
    def R(self):
        return self.rooms[self.room] if self.room else None

    def my_stack(self):
        return self.R["mine"] if self.room else self.solo

    def is_leader(self):
        return bool(self.room) and self.leader == self.cid

    def total_counts(self):
        total = {}
        for m in self.my_stack():
            k = str(float(m))
            total[k] = total.get(k, 0) + 1
        if self.room:
            for counts in self.others.values():
                for m, n in counts.items():
                    total[m] = total.get(m, 0) + n
        return total

    # ---------- resize ----------
    def on_resize(self, event):
        if event.widget is not self.root:
            return
        self.root.after_idle(self.draw_map)
        scale = max(0.6, round(min(event.width / self.base_w, event.height / self.base_h), 2))
        if abs(scale - self._scale) < 0.03:
            return
        self._scale = scale
        for k, f in self.fonts.items():
            f.configure(size=max(7, int(self.base_sizes[k] * scale)))
        self.header.config(height=int(74 * scale), width=int(420 * scale))
        self.draw_header()

    # ---------- treasure-map drawing ----------
    def btn_style(self):
        return dict(bg=CARD, fg=TEXT, relief="ridge", bd=2, activebackground="#c49a52", activeforeground=TEXT,
                    disabledforeground="#a08a62", font=self.fonts["body"], cursor="hand2")

    def ragged(self, w, h, inset, amp, step=16):
        """Points around the window edge, pushed inward by a burnt, ragged amount."""
        pts, i = [], 0
        def off(k):
            return inset + amp * self.noise[k % len(self.noise)]
        x = 0
        while x < w:                        # top edge
            pts += [x, off(i)]; i += 1; x += step
        y = 0
        while y < h:                        # right edge
            pts += [w - off(i), y]; i += 1; y += step
        x = w
        while x > 0:                        # bottom edge
            pts += [x, h - off(i)]; i += 1; x -= step
        y = h
        while y > 0:                        # left edge
            pts += [off(i), y]; i += 1; y -= step
        return pts

    def draw_map(self):
        c = self.bg
        w, h = self.root.winfo_width(), self.root.winfo_height()
        if w < 50 or h < 50:
            return
        c.delete("all")
        for inset, amp, color in BURN_LAYERS:
            c.create_polygon(self.ragged(w, h, inset, amp), fill=color, outline="", smooth=True)
        # age stains and scorch spots on the parchment margins
        for fx, fy, r, col in ((0.12, 0.18, 34, "#d8b97c"), (0.9, 0.82, 44, "#d5b478"),
                               (0.85, 0.12, 22, "#cfa96b"), (0.1, 0.88, 26, "#cda766")):
            c.create_oval(fx * w - r, fy * h - r, fx * w + r, fy * h + r, outline=col, width=3)
        for fx, fy, r in ((0.06, 0.5, 9), (0.95, 0.4, 7), (0.5, 0.97, 8)):
            c.create_oval(fx * w - r, fy * h - r, fx * w + r, fy * h + r, fill="#5a3416", outline="")

    def draw_header(self):
        c = self.header
        c.delete("all")
        w = max(c.winfo_width(), 200)
        h = max(c.winfo_height(), 60)
        s = self._scale
        cx, cy = w / 2, h / 2
        # dotted trail leading to the X
        trail = [(30 * s, h - 12), (w * 0.2, h * 0.75), (w * 0.35, h - 8), (w * 0.65, h - 6), (w * 0.8, h * 0.72),
                 (w - 34 * s, h * 0.5)]
        flat = [v for p in trail for v in p]
        c.create_line(*flat, smooth=True, fill="#8a6236", dash=(4, 5), width=2)
        # red X marks the spot
        x0, y0, r = w - 34 * s, h * 0.5, 9 * s
        c.create_line(x0 - r, y0 - r, x0 + r, y0 + r, fill=RED, width=max(2, int(4 * s)), capstyle="round")
        c.create_line(x0 - r, y0 + r, x0 + r, y0 - r, fill=RED, width=max(2, int(4 * s)), capstyle="round")
        # compass rose
        rx, ry, R = 30 * s, h * 0.42, 20 * s
        c.create_oval(rx - R, ry - R, rx + R, ry + R, outline="#6b4a2b", width=1)
        for a in range(0, 360, 45):
            L = R if a % 90 == 0 else R * 0.55
            ang = math.radians(a)
            tip = (rx + L * math.sin(ang), ry - L * math.cos(ang))
            side1 = (rx + 4 * s * math.sin(ang + math.pi / 2), ry - 4 * s * math.cos(ang + math.pi / 2))
            side2 = (rx + 4 * s * math.sin(ang - math.pi / 2), ry - 4 * s * math.cos(ang - math.pi / 2))
            c.create_polygon(*side1, *tip, rx, ry, fill=TEXT if a % 90 == 0 else DIM, outline="")
            c.create_polygon(*side2, *tip, rx, ry, fill="#b08a55", outline="")
        c.create_text(rx, ry - R - 6 * s, text="N", fill=TEXT, font=(SERIF, max(6, int(7 * s)), "bold"))
        # title lettering
        c.create_text(cx + 1, cy - 4 * s + 1, text="Pirate Token Tracker", fill="#c9a064",
                      font=(SERIF, max(9, int(19 * s)), "bold italic"))
        c.create_text(cx, cy - 4 * s, text="Pirate Token Tracker", fill=TEXT,
                      font=(SERIF, max(9, int(19 * s)), "bold italic"))
        c.create_text(cx, cy + 16 * s, text="☠  a ledger of chests plundered  ☠", fill=DIM,
                      font=(SERIF, max(7, int(9 * s)), "italic"))

    # ---------- input ----------
    def on_key(self, key):
        if key == keyboard.Key.up:
            self.root.after(0, self.add)
        elif key == keyboard.Key.down:
            self.root.after(0, self.undo)

    def changed(self):
        if self.room:
            self.dirty = True
            self.push_soon()
        self.refresh(); self.save()

    def add(self):
        if self.updating:
            return
        self.my_stack().append(MODES[self.mode.get()])
        self.changed()

    def undo(self):
        if self.updating:
            return
        if self.my_stack():
            self.my_stack().pop()
            self.changed()

    def set_count(self):
        if self.updating:
            return
        who = "your own" if self.room else "your"
        n = sd.askinteger("Set count", f"How many chests should {who} count be?\n"
                          f"(New chests use the current Rate setting.)",
                          parent=self.root, minvalue=0, maxvalue=10_000_000, initialvalue=len(self.my_stack()))
        if n is None:
            return
        stack = self.my_stack()
        if n < len(stack):
            del stack[n:]
        else:
            stack.extend([MODES[self.mode.get()]] * (n - len(stack)))
        self.changed()

    def reset(self):
        if self.room and not self.is_leader():
            mb.showinfo("Reset", "Only the room leader can reset the duo count.", parent=self.root)
            return
        msg = "Reset the duo count to 0 for EVERYONE in the room?" if self.room else "Reset your chest count to 0?"
        if not mb.askyesno("Reset", msg, parent=self.root):
            return
        if self.room:
            new_epoch = self.R["epoch"] + 1
            self.R["epoch"] = new_epoch
            self.R["mine"].clear()
            self.others = {}
            code, cid = self.room, self.cid
            payload = {"epoch": new_epoch, "players": {cid: {"c": {}, "epoch": new_epoch, "t": int(time.time())}}}
            threading.Thread(target=lambda: self._safe(lambda: db_request(f"rooms/{code}", "PATCH", payload)),
                             daemon=True).start()
        else:
            self.solo.clear()
        self.refresh(); self.save()

    @staticmethod
    def _safe(fn):
        try:
            fn()
        except Exception:
            pass

    # ---------- rooms ----------
    def new_code(self):
        if not self.room:
            self.room_var.set("".join(random.choices(CODE_CHARS, k=5)))

    def toggle_room(self):
        if self.room:   # leave
            self.room = None
            self._stream_gen += 1
            self.connected = False
            self.others = {}
            self.leader = None
            self.refresh(); self.save()
            return
        code = "".join(ch for ch in self.room_var.get().strip().upper() if ch.isalnum())
        code = code.replace("O", "0").replace("I", "1").replace("L", "1")  # forgive look-alikes
        if len(code) < 4:
            mb.showinfo("Room code", "Type a room code (at least 4 letters/numbers),\n"
                                     "or press New code and send it to your duo.", parent=self.root)
            return
        self.room_var.set(code)
        is_new = code not in self.rooms
        self.rooms.setdefault(code, {"mine": [], "epoch": 0})
        if is_new and self.solo and mb.askyesno(
                "Bring your chests?", f"You have {len(self.solo):,} solo chests counted.\n"
                                      f"Add them to your count in this duo room?", parent=self.root):
            self.rooms[code]["mine"].extend(self.solo)
        self.enter_room(code)
        self.refresh(); self.save()

    def enter_room(self, code):
        self.room = code
        self.others = {}
        self.leader = None
        self.dirty = True
        self._stream_gen += 1
        gen = self._stream_gen
        threading.Thread(target=self.stream_loop, args=(gen, code), daemon=True).start()

    # ---------- sending ----------
    def push_soon(self):
        if not self.sending:
            self.sending = True
            self.root.after(700, self._push)

    def _push(self):
        self.sending = False
        if not self.room or not self.dirty:
            return
        code, cid = self.room, self.cid
        snap = {"c": tally(self.R["mine"]), "epoch": self.R["epoch"], "t": int(time.time())}
        self.dirty = False

        def worker():
            try:
                db_request(f"rooms/{code}/players/{cid}", "PUT", snap)
                self.root.after(0, lambda: self._push_done(True))
            except Exception:
                self.root.after(0, lambda: self._push_done(False))
        threading.Thread(target=worker, daemon=True).start()

    def _push_done(self, ok):
        self.send_error = not ok
        if not ok:
            self.dirty = True
            self.root.after(5000, self.push_soon)   # retry; nothing is lost
        self.refresh()

    # ---------- receiving ----------
    def stream_loop(self, gen, code):
        # Whoever creates the room (first to join it) becomes its leader
        try:
            if not db_request(f"rooms/{code}/leader"):
                db_request(f"rooms/{code}", "PATCH", {"leader": self.cid})
        except Exception:
            pass
        while gen == self._stream_gen:
            try:
                self.root.after(0, lambda: self.pull(gen, code))
                req = urllib.request.Request(f"{DB}/rooms/{code}.json", headers={"Accept": "text/event-stream"})
                with urllib.request.urlopen(req, timeout=90) as resp:
                    self.root.after(0, lambda: self.set_connected(True))
                    for raw in resp:
                        if gen != self._stream_gen:
                            return
                        line = raw.decode("utf-8", "ignore").strip()
                        if line in ("event: put", "event: patch"):
                            self.root.after(0, lambda: self.pull(gen, code))
            except Exception:
                if gen != self._stream_gen:
                    return
                self.root.after(0, lambda: self.set_connected(False))
                time.sleep(4)

    def pull(self, gen, code):
        if code in self._pulling:
            self._pull_again = True
            return
        self._pulling.add(code)

        def worker():
            try:
                data = db_request(f"rooms/{code}") or {}
                self.root.after(0, lambda: self.apply_room(gen, code, data))
            except Exception:
                pass
            finally:
                self._pulling.discard(code)
        threading.Thread(target=worker, daemon=True).start()

    def apply_room(self, gen, code, data):
        if gen != self._stream_gen or code != self.room:
            return
        R = self.R
        epoch = int(data.get("epoch") or 0)
        if epoch > R["epoch"]:               # the leader reset the room
            R["epoch"] = epoch
            R["mine"].clear()
            self.dirty = True
        self.leader = data.get("leader")
        players = data.get("players") or {}
        self.others = {cid: untally(p.get("c")) for cid, p in players.items()
                       if cid != self.cid and isinstance(p, dict) and int(p.get("epoch") or 0) == R["epoch"]}
        mine_online = players.get(self.cid)
        if not isinstance(mine_online, dict) or untally(mine_online.get("c")) != untally(tally(R["mine"])):
            self.dirty = True
        if self.dirty:
            self.push_soon()
        self.refresh(); self.save()
        if self._pull_again:
            self._pull_again = False
            self.root.after(300, lambda: self.pull(gen, code))

    def set_connected(self, ok):
        if self.room:
            self.connected = ok
            self.refresh()

    # ---------- forced updates ----------
    def check_for_update(self):
        if not UPDATE_BASE or getattr(sys, "frozen", False):
            return

        def worker():
            try:
                req = urllib.request.Request(UPDATE_BASE + "version.txt?t=" + str(int(time.time())),
                                             headers={"Cache-Control": "no-cache"})
                latest = int(urllib.request.urlopen(req, timeout=10).read().decode().strip())
            except Exception:
                latest = 0
            if latest > APP_VERSION:
                self.root.after(0, lambda: self.start_update(latest))
            else:
                self.root.after(UPDATE_CHECK_EVERY * 1000, self.check_for_update)
        threading.Thread(target=worker, daemon=True).start()

    def download_update(self):
        # GitHub's API serves the newest file right away; the raw link can lag a few minutes
        try:
            req = urllib.request.Request(UPDATE_API, headers={"Accept": "application/vnd.github.raw"})
            return urllib.request.urlopen(req, timeout=30).read()
        except Exception:
            req = urllib.request.Request(UPDATE_BASE + "pirate_token_tracker.pyw?t=" + str(int(time.time())),
                                         headers={"Cache-Control": "no-cache"})
            return urllib.request.urlopen(req, timeout=30).read()

    def start_update(self, latest):
        if self.updating:
            return
        self.updating = True
        if self.room and self.dirty:
            self._push()             # share your latest count before restarting
        self.save()
        win = tk.Toplevel(self.root)
        win.title("Update required")
        win.configure(bg=BG)
        win.attributes("-topmost", True)
        win.protocol("WM_DELETE_WINDOW", lambda: None)   # can't be closed
        win.transient(self.root)
        self.upd_lbl = tk.Label(win, text=f"Updating to v{latest}…\nYour chest count is saved.",
                                bg=BG, fg=GOLD, font=(SERIF, 12, "bold"), padx=30, pady=24)
        self.upd_lbl.pack()
        win.grab_set()

        def worker():
            try:
                code = self.download_update()
                text = code.decode("utf-8")
                compile(text, "update", "exec")                 # make sure it's a real, working file
                if f"APP_VERSION = {latest}" not in text:
                    raise ValueError("version mismatch")
                me = os.path.abspath(__file__)
                tmp = me + ".new"
                with open(tmp, "wb") as f:
                    f.write(code)
                os.replace(tmp, me)
                self.root.after(0, self.restart)
            except Exception:
                self.root.after(0, lambda: self.upd_lbl.config(
                    text="Update required, but the download failed.\nRetrying in 30 seconds…", fg=RED))
                self.root.after(30_000, lambda: (setattr(self, "updating", False), win.destroy(),
                                                 self.start_update(latest)))
        threading.Thread(target=worker, daemon=True).start()

    def restart(self):
        self._stream_gen += 1
        self.save()
        exe = sys.executable
        if exe.lower().endswith("python.exe"):
            exe = exe[:-10] + "pythonw.exe" if os.path.exists(exe[:-10] + "pythonw.exe") else exe
        subprocess.Popen([exe, os.path.abspath(__file__)], cwd=_APP_DIR)
        self.root.destroy()

    # ---------- display ----------
    def refresh(self):
        counts = self.total_counts()
        n = sum(counts.values())
        pct = odds_from_counts(counts) * 100
        decimals = 5 if pct < 0.01 else 4 if pct < 1 else 2
        self.count_title.config(text="DUO CHESTS OPENED" if self.room else "CHESTS OPENED")
        self.count_lbl.config(text=f"{n:,}")
        self.odds_lbl.config(text=f"{pct:.{decimals}f}%")
        mult = MODES[self.mode.get()]
        self.per_lbl.config(text=f"Per chest now: {BASE_RATE * mult * 100:.5f}%  (1 in {round(1 / (BASE_RATE * mult)):,})")
        if self.room:
            mine = len(self.R["mine"])
            split = f"You: {mine:,}"
            if self.others:
                split += "   ·   Duo: " + "  +  ".join(f"{sum(c.values()):,}" for c in self.others.values())
            else:
                split += "   ·   Duo: waiting for them to join…"
            self.split_lbl.config(text=split)
            self.join_btn.config(text="Leave")
            self.code_btn.pack_forget()
            self.room_entry.config(state="disabled", disabledbackground=CARD, disabledforeground=GOLD)
            self.reset_btn.config(state="normal" if self.is_leader() else "disabled")
            crown = "👑 You're the leader · " if self.is_leader() else ""
            if self.send_error:
                self.status_lbl.config(text="⚠ Couldn't share your count — retrying (no chests lost)", fg=RED)
            elif self.connected:
                self.status_lbl.config(text=f"● {crown}Room {self.room} — live sync", fg=GREEN)
            else:
                self.status_lbl.config(text=f"○ Connecting to room {self.room}…", fg=DIM)
        else:
            self.split_lbl.config(text="")
            self.join_btn.config(text="Join")
            self.code_btn.pack(side="left", padx=2)
            self.room_entry.config(state="normal")
            self.reset_btn.config(state="normal")
            self.status_lbl.config(text="Solo mode — join a room to share chests with your duo", fg=DIM)

    # ---------- save / load ----------
    def save(self):
        try:
            with open(SAVE_FILE, "w") as f:
                json.dump({"v": 4, "cid": self.cid, "solo": self.solo, "mode": self.mode.get(), "room": self.room,
                           "rooms": self.rooms, "geometry": self.root.winfo_geometry()}, f)
        except (OSError, tk.TclError):
            pass

    def load(self):
        try:
            with open(SAVE_FILE) as f:
                data = json.load(f)
        except (OSError, ValueError):
            return
        self._saved_geometry = data.get("geometry")
        if data.get("mode") in MODES:
            self.mode.set(data["mode"])
        v = data.get("v")
        if v in (2, 3, 4):
            self.cid = data.get("cid") or self.cid
            self.solo = [float(m) for m in data.get("solo", [])]
            # keep only your own chests per room; the database has everyone else's
            self.rooms = {code: {"mine": [float(m) for m in r.get("mine", [])],
                                 "epoch": int(r.get("epoch", 0)) if v == 4 else 0}
                          for code, r in (data.get("rooms") or {}).items() if isinstance(r, dict)}
            room = data.get("room")
            self.room = room if room in self.rooms else None
            return
        # ---- upgrade from v1 ----
        self.solo = [float(m) for m in data.get("history", [])]
        old_room = data.get("room")
        old_rooms = data.get("rooms", {}) or {}
        if old_room in old_rooms:
            self.solo = [float(m) for m in old_rooms[old_room].get("history", [])]

    def close(self):
        if self.room and self.dirty and self.R is not None:
            try:
                db_request(f"rooms/{self.room}/players/{self.cid}", "PUT",
                           {"c": tally(self.R["mine"]), "epoch": self.R["epoch"], "t": int(time.time())}, timeout=3)
            except Exception:
                pass
        self._stream_gen += 1
        self.save()
        self.root.destroy()


def rescue_update(err):
    """If the app ever crashes on startup, still pull a fixed version from GitHub."""
    try:
        latest = int(urllib.request.urlopen(UPDATE_BASE + "version.txt", timeout=10).read().decode().strip())
        if latest > APP_VERSION:
            req = urllib.request.Request(UPDATE_API, headers={"Accept": "application/vnd.github.raw"})
            code = urllib.request.urlopen(req, timeout=30).read()
            compile(code.decode("utf-8"), "update", "exec")
            me = os.path.abspath(__file__)
            with open(me + ".new", "wb") as f:
                f.write(code)
            os.replace(me + ".new", me)
            subprocess.Popen([sys.executable, me], cwd=_APP_DIR)
            return
    except Exception:
        pass
    r = tk.Tk(); r.withdraw()
    mb.showerror("Pirate Tracker crashed", f"Something broke on startup:\n\n{err}\n\n"
                                           "Send a screenshot of this to whoever runs the tracker.")


if __name__ == "__main__":
    try:
        root = tk.Tk()
        Tracker(root)
    except Exception as e:
        try:
            root.destroy()
        except Exception:
            pass
        rescue_update(e)
        raise SystemExit
    root.mainloop()

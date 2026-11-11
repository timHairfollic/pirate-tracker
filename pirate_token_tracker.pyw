"""
Fortnite Pirate Token Chest Tracker (with Duo sync) - v2
--------------------------------------------------------
UP arrow   = +1 chest (works even while Fortnite is focused)
DOWN arrow = undo your last chest

Duo sync: both players type the same room code and press Join.
Each tracker keeps its OWN chest count and shares its total with the room
every couple of minutes, so the free relay (ntfy.sh) never gets flooded and
no chest is ever lost if a send fails - it just retries.

Odds of at least one token = 1 - product of (1 - p) for every chest opened,
where p is the per-chest rate active when that chest was counted.
Normal: 1 in 137,500   Treasure Hour 1.5x: 1 in 91,667   Treasure Hour 2x: 1 in 68,750
"""
import json
import os
import random
import subprocess
import sys
import threading
import time
import tkinter as tk
import tkinter.messagebox as mb
import urllib.parse
import urllib.request
import uuid
from tkinter import font as tkfont

try:
    from pynput import keyboard
except ImportError:
    r = tk.Tk(); r.withdraw()
    mb.showerror("Missing package", "Open Command Prompt and run:\n\npython -m pip install pynput\n\nthen start the tracker again.")
    raise SystemExit

APP_VERSION = 2
# Where updates come from. version.txt holds the newest version number;
# pirate_token_tracker.pyw next to it is the new app. Leave "" to turn updates off.
UPDATE_BASE = "https://raw.githubusercontent.com/timHairfollic/pirate-tracker/main/"
UPDATE_CHECK_EVERY = 10 * 60   # seconds

BASE_RATE = 1 / 137_500
MODES = {"Normal (1x)": 1.0, "Treasure Hour 1.5x": 1.5, "Treasure Hour 2x": 2.0}
_APP_DIR = os.path.dirname(sys.executable) if getattr(sys, "frozen", False) else os.path.dirname(os.path.abspath(__file__))
SAVE_FILE = os.path.join(_APP_DIR, "pirate_tracker_save.json")
RELAY = "https://ntfy.sh"
TOPIC_PREFIX = "fn-pirate-v2-"
SEND_EVERY = 120           # seconds between shares of your total (keeps under the relay's limits)
CODE_CHARS = "ACDEFHJKMNPRTUVWXY34679"   # no look-alikes (O/0, I/1/L, S/5, B/8, Z/2, G)

BG, CARD, GOLD, TEXT, DIM, GREEN, RED = "#14110d", "#221c14", "#f2b632", "#f4ead8", "#9c8f78", "#6fcf7a", "#e86a5a"


def odds_from_counts(counts):
    """counts: {multiplier_str: number_of_chests} -> chance of at least one token."""
    miss = 1.0
    for mult, n in counts.items():
        miss *= (1 - BASE_RATE * float(mult)) ** n
    return 1 - miss


def tally(stack):
    c = {}
    for m in stack:
        c[str(m)] = c.get(str(m), 0) + 1
    return c


class Tracker:
    def __init__(self, root):
        self.root = root
        self.cid = uuid.uuid4().hex[:12]   # this tracker's id in a room
        self.solo = []                     # solo chest multipliers
        self.room = None                   # active room code
        self.rooms = {}                    # code -> {"mine": [...], "others": {cid: {"c":{}, "seq":n, "epoch":e}},
                                           #          "epoch": e, "seq": n, "last_id": str}
        self.mode = tk.StringVar(value="Normal (1x)")
        self.on_top = tk.BooleanVar(value=True)
        self.room_var = tk.StringVar()
        self._saved_geometry = None
        self._stream_gen = 0
        self.connected = False
        self.dirty = False                 # my room count changed but not shared yet
        self.last_send = 0.0
        self.send_scheduled = False
        self.send_error = False
        self.load()

        root.title(f"Pirate Token Tracker v{APP_VERSION}")
        root.configure(bg=BG)
        root.resizable(True, True)
        root.attributes("-topmost", True)

        self.base_sizes = {"title": 13, "small": 9, "big": 34, "odds": 28, "body": 10, "plain": 9}
        self.fonts = {k: tkfont.Font(family="Segoe UI", size=s, weight="normal" if k == "plain" else "bold")
                      for k, s in self.base_sizes.items()}
        F = self.fonts

        tk.Label(root, text="🏴‍☠️ PIRATE TOKEN TRACKER", bg=BG, fg=GOLD, font=F["title"]).pack(pady=(14, 6))

        card = tk.Frame(root, bg=CARD, padx=24, pady=14)
        card.pack(padx=16, fill="both", expand=True)
        inner = tk.Frame(card, bg=CARD)
        inner.pack(expand=True)
        self.count_title = tk.Label(inner, bg=CARD, fg=DIM, font=F["small"])
        self.count_title.pack()
        self.count_lbl = tk.Label(inner, bg=CARD, fg=TEXT, font=F["big"])
        self.count_lbl.pack()
        self.split_lbl = tk.Label(inner, bg=CARD, fg=DIM, font=F["plain"])
        self.split_lbl.pack()
        tk.Label(inner, text="CHANCE YOU'D HAVE FOUND A TOKEN", bg=CARD, fg=DIM, font=F["small"]).pack(pady=(8, 0))
        self.odds_lbl = tk.Label(inner, bg=CARD, fg=GOLD, font=F["odds"])
        self.odds_lbl.pack()
        self.per_lbl = tk.Label(inner, bg=CARD, fg=DIM, font=F["plain"])
        self.per_lbl.pack(pady=(4, 0))

        row = tk.Frame(root, bg=BG)
        row.pack(pady=(10, 6))
        tk.Label(row, text="Rate:", bg=BG, fg=TEXT, font=F["body"]).pack(side="left")
        opt = tk.OptionMenu(row, self.mode, *MODES, command=lambda _: self.refresh())
        opt.config(bg=CARD, fg=TEXT, activebackground=GOLD, highlightthickness=0, relief="flat", font=F["body"])
        opt["menu"].config(bg=CARD, fg=TEXT)
        opt.pack(side="left", padx=6)

        btns = tk.Frame(root, bg=BG)
        btns.pack()
        for txt, cmd in (("+1", self.add), ("Undo", self.undo), ("Reset", self.reset)):
            tk.Button(btns, text=txt, command=cmd, width=7, bg=CARD, fg=TEXT, relief="flat",
                      activebackground=GOLD, font=F["body"]).pack(side="left", padx=4)

        duo = tk.Frame(root, bg=BG)
        duo.pack(pady=(10, 0))
        tk.Label(duo, text="Duo room:", bg=BG, fg=TEXT, font=F["body"]).pack(side="left")
        self.room_entry = tk.Entry(duo, textvariable=self.room_var, width=9, bg=CARD, fg=TEXT,
                                   insertbackground=TEXT, relief="flat", font=F["body"], justify="center")
        self.room_entry.pack(side="left", padx=4, ipady=2)
        self.join_btn = tk.Button(duo, text="Join", command=self.toggle_room, width=6, bg=CARD, fg=TEXT,
                                  relief="flat", activebackground=GOLD, font=F["body"])
        self.join_btn.pack(side="left", padx=2)
        self.code_btn = tk.Button(duo, text="New code", command=self.new_code, bg=CARD, fg=TEXT, relief="flat",
                                  activebackground=GOLD, font=F["body"])
        self.code_btn.pack(side="left", padx=2)
        self.sync_btn = tk.Button(duo, text="Sync now", command=lambda: self.schedule_send(force=True),
                                  bg=CARD, fg=TEXT, relief="flat", activebackground=GOLD, font=F["body"])
        self.status_lbl = tk.Label(root, bg=BG, fg=DIM, font=F["plain"])
        self.status_lbl.pack(pady=(4, 0))

        tk.Checkbutton(root, text="Keep on top of game", variable=self.on_top, bg=BG, fg=DIM,
                       selectcolor=CARD, activebackground=BG, activeforeground=TEXT, font=F["plain"],
                       command=lambda: root.attributes("-topmost", self.on_top.get())).pack(pady=(6, 0))
        tk.Label(root, text="↑ Up arrow = +1 chest    ↓ Down arrow = undo", bg=BG, fg=DIM,
                 font=F["plain"]).pack(pady=(4, 14))

        root.update_idletasks()
        self.base_w, self.base_h = root.winfo_reqwidth(), root.winfo_reqheight()
        root.geometry(f"{self.base_w}x{self.base_h}")
        root.minsize(int(self.base_w * 0.6), int(self.base_h * 0.6))
        self._scale = 1.0
        root.bind("<Configure>", self.on_resize)
        if self._saved_geometry:
            try:
                root.geometry(self._saved_geometry)
            except tk.TclError:
                pass

        if self.room:
            self.room_var.set(self.room)
            self.start_stream()
            self.schedule_send(force=True)   # announce my total on startup
        self.refresh()
        keyboard.Listener(on_press=self.on_key, daemon=True).start()
        root.protocol("WM_DELETE_WINDOW", self.close)
        self.updating = False
        self.root.after(1500, self.check_for_update)

    # ---------- state helpers ----------
    @property
    def R(self):
        return self.rooms[self.room] if self.room else None

    def my_stack(self):
        return self.R["mine"] if self.room else self.solo

    def total_counts(self):
        if not self.room:
            return tally(self.solo)
        total = tally(self.R["mine"])
        for o in self.R["others"].values():
            if o.get("epoch", 0) == self.R["epoch"]:
                for m, n in o.get("c", {}).items():
                    total[m] = total.get(m, 0) + n
        return total

    @staticmethod
    def topic(code):
        return TOPIC_PREFIX + code.lower()

    # ---------- resize ----------
    def on_resize(self, event):
        if event.widget is not self.root:
            return
        scale = max(0.6, round(min(event.width / self.base_w, event.height / self.base_h), 2))
        if abs(scale - self._scale) < 0.03:
            return
        self._scale = scale
        for k, f in self.fonts.items():
            f.configure(size=max(7, int(self.base_sizes[k] * scale)))

    # ---------- input ----------
    def on_key(self, key):
        if key == keyboard.Key.up:
            self.root.after(0, self.add)
        elif key == keyboard.Key.down:
            self.root.after(0, self.undo)

    def changed(self):
        if self.room:
            self.dirty = True
            self.schedule_send()
        self.refresh(); self.save()

    def add(self):
        if getattr(self, "updating", False):
            return
        self.my_stack().append(MODES[self.mode.get()])
        self.changed()

    def undo(self):
        if getattr(self, "updating", False):
            return
        if self.my_stack():
            self.my_stack().pop()
            self.changed()

    def reset(self):
        msg = "Reset the duo count to 0 for BOTH of you?" if self.room else "Reset your chest count to 0?"
        if not mb.askyesno("Reset", msg, parent=self.root):
            return
        if self.room:
            self.R["epoch"] += 1
            self.R["mine"].clear()
            self.R["others"].clear()
            self.dirty = True
            self.schedule_send(force=True)
        else:
            self.solo.clear()
        self.refresh(); self.save()

    # ---------- rooms ----------
    def new_code(self):
        if not self.room:
            self.room_var.set("".join(random.choices(CODE_CHARS, k=5)))

    def toggle_room(self):
        if self.room:   # leave
            if self.dirty:
                self.send_now()
            self.room = None
            self._stream_gen += 1
            self.connected = False
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
        self.rooms.setdefault(code, {"mine": [], "others": {}, "epoch": 0, "seq": 0, "last_id": ""})
        self.room = code
        if is_new and self.solo and mb.askyesno(
                "Bring your chests?", f"You have {len(self.solo):,} solo chests counted.\n"
                                      f"Add them to your count in this duo room?", parent=self.root):
            self.R["mine"].extend(self.solo)
        self.start_stream()
        self.dirty = True
        self.schedule_send(force=True)
        self.refresh(); self.save()

    # ---------- sending (rate-limited, never loses chests) ----------
    def schedule_send(self, force=False):
        if not self.room:
            return
        if force:
            self.last_send = 0.0
            self.dirty = True
        if self.send_scheduled:
            if force:
                self.send_now()
            return
        wait = max(0.0, self.last_send + SEND_EVERY - time.time())
        self.send_scheduled = True
        self.root.after(int(wait * 1000), self._send_tick)

    def _send_tick(self):
        self.send_scheduled = False
        if self.room and self.dirty:
            self.send_now()

    def send_now(self):
        if not self.room:
            return
        R = self.R
        R["seq"] += 1
        payload = {"v": 2, "cid": self.cid, "seq": R["seq"], "epoch": R["epoch"], "c": tally(R["mine"])}
        topic = self.topic(self.room)
        self.dirty = False
        self.last_send = time.time()
        self.save()

        def worker():
            try:
                req = urllib.request.Request(f"{RELAY}/{topic}", data=json.dumps(payload).encode(), method="POST")
                urllib.request.urlopen(req, timeout=15).read()
                self.root.after(0, self._send_ok)
            except Exception:
                self.root.after(0, self._send_failed)
        threading.Thread(target=worker, daemon=True).start()

    def _send_ok(self):
        self.send_error = False
        self.refresh()

    def _send_failed(self):
        self.send_error = True
        self.dirty = True          # try again next round; nothing is lost
        self.schedule_send()
        self.refresh()

    # ---------- receiving ----------
    def start_stream(self):
        self._stream_gen += 1
        gen, code = self._stream_gen, self.room
        threading.Thread(target=self.stream_loop, args=(gen, code), daemon=True).start()

    def stream_loop(self, gen, code):
        topic = self.topic(code)
        while gen == self._stream_gen:
            since = self.rooms.get(code, {}).get("last_id") or "all"
            try:
                url = f"{RELAY}/{topic}/json?since={urllib.parse.quote(since)}"
                with urllib.request.urlopen(url, timeout=90) as resp:
                    self.root.after(0, lambda: self.set_connected(True))
                    for raw in resp:
                        if gen != self._stream_gen:
                            return
                        try:
                            msg = json.loads(raw)
                        except ValueError:
                            continue
                        if msg.get("event") == "message":
                            self.root.after(0, lambda m=msg: self.apply_remote(code, m))
            except Exception:
                if gen != self._stream_gen:
                    return
                self.root.after(0, lambda: self.set_connected(False))
                time.sleep(5)

    def apply_remote(self, code, msg):
        R = self.rooms.get(code)
        if R is None:
            return
        R["last_id"] = msg.get("id", R["last_id"])
        try:
            ev = json.loads(msg.get("message", ""))
            cid, seq, epoch = ev["cid"], int(ev["seq"]), int(ev["epoch"])
            counts = {str(float(m)): max(0, int(n)) for m, n in ev.get("c", {}).items()}
        except (ValueError, KeyError, TypeError):
            return
        if epoch > R["epoch"]:          # someone pressed Reset
            R["epoch"] = epoch
            R["mine"].clear()
            R["others"].clear()
            if cid != self.cid:
                self.dirty = True
                self.schedule_send()
        if cid != self.cid and epoch == R["epoch"]:
            old = R["others"].get(cid)
            if not old or seq >= old.get("seq", 0) or old.get("epoch", 0) < epoch:
                R["others"][cid] = {"c": counts, "seq": seq, "epoch": epoch}
        if code == self.room:
            self.refresh()
        self.save()

    def set_connected(self, ok):
        if self.room:
            self.connected = ok
            self.refresh()


    # ---------- forced updates ----------
    def check_for_update(self):
        if not UPDATE_BASE or "GITHUB_USERNAME" in UPDATE_BASE or getattr(sys, "frozen", False):
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

    def start_update(self, latest):
        if self.updating:
            return
        self.updating = True
        if self.room and self.dirty:
            self.send_now()          # share your latest count before restarting
        self.save()
        win = tk.Toplevel(self.root)
        win.title("Update required")
        win.configure(bg=BG)
        win.attributes("-topmost", True)
        win.protocol("WM_DELETE_WINDOW", lambda: None)   # can't be closed
        win.transient(self.root)
        self.upd_lbl = tk.Label(win, text=f"Updating to v{latest}…\nYour chest count is saved.",
                                bg=BG, fg=GOLD, font=("Segoe UI", 12, "bold"), padx=30, pady=24)
        self.upd_lbl.pack()
        win.grab_set()

        def worker():
            try:
                req = urllib.request.Request(UPDATE_BASE + "pirate_token_tracker.pyw?t=" + str(int(time.time())),
                                             headers={"Cache-Control": "no-cache"})
                code = urllib.request.urlopen(req, timeout=30).read()
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
            partners = [sum(o["c"].values()) for o in self.R["others"].values() if o.get("epoch", 0) == self.R["epoch"]]
            split = f"You: {mine:,}"
            if partners:
                split += "   ·   Duo: " + "  +  ".join(f"{p:,}" for p in partners)
            else:
                split += "   ·   Duo: waiting for them to join…"
            self.split_lbl.config(text=split)
            self.join_btn.config(text="Leave")
            self.code_btn.pack_forget()
            self.sync_btn.pack(side="left", padx=2)
            self.room_entry.config(state="disabled", disabledbackground=CARD, disabledforeground=GOLD)
            if self.send_error:
                self.status_lbl.config(text="⚠ Couldn't share your count — retrying automatically (no chests lost)", fg=RED)
            elif self.connected:
                self.status_lbl.config(text=f"● Room {self.room} — your count shares every 2 min (or press Sync now)", fg=GREEN)
            else:
                self.status_lbl.config(text=f"○ Connecting to room {self.room}…", fg=DIM)
        else:
            self.split_lbl.config(text="")
            self.join_btn.config(text="Join")
            self.sync_btn.pack_forget()
            self.code_btn.pack(side="left", padx=2)
            self.room_entry.config(state="normal")
            self.status_lbl.config(text="Solo mode — join a room to share chests with your duo", fg=DIM)

    # ---------- save / load ----------
    def save(self):
        try:
            with open(SAVE_FILE, "w") as f:
                json.dump({"v": 2, "cid": self.cid, "solo": self.solo, "mode": self.mode.get(), "room": self.room,
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
        if data.get("v") == 2:
            self.cid = data.get("cid") or self.cid
            self.solo = [float(m) for m in data.get("solo", [])]
            self.rooms = data.get("rooms", {}) or {}
            room = data.get("room")
            self.room = room if room in self.rooms else None
            return
        # ---- upgrade from the old version: keep whatever count was on screen ----
        self.solo = [float(m) for m in data.get("history", [])]
        old_room = data.get("room")
        old_rooms = data.get("rooms", {}) or {}
        if old_room in old_rooms:
            # Bring the duo count over as solo chests; you'll be asked to add them when you join a room
            self.solo = [float(m) for m in old_rooms[old_room].get("history", [])]

    def close(self):
        if self.room and self.dirty:
            self.send_now()
            time.sleep(0.8)        # give the last share a moment to go out
        self._stream_gen += 1
        self.save()
        self.root.destroy()


if __name__ == "__main__":
    root = tk.Tk()
    Tracker(root)
    root.mainloop()

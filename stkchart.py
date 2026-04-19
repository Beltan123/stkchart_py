#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Stable stock chart desktop UI using Tkinter + Matplotlib.
Node apiserver version:
- Data is loaded through node apiserver.cjs
- Default:
    http://127.0.0.1:3080/twnew/day1/z1101.sma
    http://127.0.0.1:3080/twnew/day1/bmwpid.txt

Display:
- default ticks = 60
- indicators are calculated on a larger window first
- then only the last ticks bars are shown
- so MA5 / MA12 / MA24 do not leave a long empty section on the left
"""

import struct
import argparse
import subprocess
import sys
import os
import webbrowser
from dataclasses import dataclass
from typing import List, Optional, Tuple
from urllib.parse import urljoin
from urllib.request import urlopen, Request

import tkinter as tk
from tkinter import messagebox

import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.patches import Rectangle
from matplotlib.ticker import FuncFormatter


# ----------------------------
# Theme
# ----------------------------
C_BG = "#111111"
C_AX = "#151515"
C_PANEL = "#1a1a1a"
C_GRID = "#333333"
C_TEXT = "#DDDDDD"
C_UP = "#ff4d4f"
C_DN = "#00c853"
C_WICK = "#AAAAAA"
C_TITLE = "#FFFFFF"
C_STATUS = "#BBBBBB"
C_ENTRY_BG = "#222222"

C_MA5 = "#ffd54f"
C_MA12 = "#4fc3f7"
C_MA24 = "#ff8a65"

C_K = "#ffd54f"
C_D = "#4fc3f7"

C_RSI = "#ab47bc"

C_DIF = "#ffd54f"
C_DEA = "#4fc3f7"
C_MACD_POS = "#ff4d4f"
C_MACD_NEG = "#00c853"

C_BUY = "#ffff66"
C_SELL = "#ff66ff"

TOP_BAR_H = 48

MARKET_PATHS = {
    "tw": "twnew/day1",
    "nsd": "nsd/day1",
    "nyse": "nyse/day1",
    "cn": "cn/day1",
    "hk": "hk/day1",
    "jpn": "jpn/day1",
}

MARKET_NAMES = {
    "tw": "Taiwan",
    "nsd": "Nasdaq",
    "nyse": "Nyse",
    "cn": "China",
    "hk": "Hong Kong",
    "jpn": "Japan",
}

DISPLAY_TO_KEY = {v: k for k, v in MARKET_NAMES.items()}
MARKET_ORDER = ["tw", "nsd", "nyse", "cn", "hk", "jpn"]
TICKS_CHOICES = [30, 60, 120, 240]
LOWER_CHOICES = ["vol", "kd", "rsi", "macd"]

PRICE_SCALE = 100.0
DEFAULT_TIMEOUT = 15
DEFAULT_BASE_URL = "http://aitradebook.com:3080"
USER_AGENT = "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/124.0 Safari/537.36"


@dataclass
class Rec:
    date: int
    open: int
    high: int
    low: int
    close: int
    vol: int
    loan1: int = 0
    loan2: int = 0
    sid: str = ""


def normalize_market_code(code: str) -> str:
    c = (code or "").strip().lower()
    if c == "jp":
        return "jpn"
    if c in MARKET_PATHS:
        return c
    return "tw"


def fetch_url_bytes(url: str, timeout: int = DEFAULT_TIMEOUT) -> bytes:
    req = Request(url, headers={"User-Agent": USER_AGENT})
    with urlopen(req, timeout=timeout) as resp:
        return resp.read()


def parse_sma_bytes(data: bytes) -> List[Rec]:
    size = 36
    out: List[Rec] = []
    n = len(data) // size
    for i in range(n):
        chunk = data[i * size:(i + 1) * size]
        if len(chunk) < size:
            continue
        try:
            s_date, s_open, s_high, s_low, s_close, s_vol, s_loan1, s_loan2, s_id = struct.unpack("<6I2h8s", chunk)
        except struct.error:
            continue
        sid = s_id.split(b"\x00")[0].decode("ascii", errors="ignore")
        out.append(Rec(s_date, s_open, s_high, s_low, s_close, s_vol, s_loan1, s_loan2, sid))
    return out


def format_date(v: int) -> str:
    s = str(v)
    if len(s) == 8:
        return f"{s[:4]}/{s[4:6]}/{s[6:8]}"
    return s


def fmt_price(v: int) -> str:
    return f"{v / PRICE_SCALE:.2f}"


def decode_text_fallback(data: bytes) -> str:
    for enc in ("utf-8", "cp950", "big5", "utf-8-sig", "latin1"):
        try:
            return data.decode(enc)
        except Exception:
            pass
    return data.decode("latin1", errors="ignore")


def first_stock_id_from_bmwpid_url(url: str) -> Optional[str]:
    txt = decode_text_fallback(fetch_url_bytes(url))
    for raw in txt.splitlines():
        line = raw.strip()
        if not line:
            continue
        parts = line.replace(",", " ").split()
        if not parts:
            continue
        token = parts[0].strip().replace("\ufeff", "")
        if token:
            return token
    return None


def load_stock_list_from_bmwpid_url(url: str) -> List[str]:
    out: List[str] = []
    txt = decode_text_fallback(fetch_url_bytes(url))
    for raw in txt.splitlines():
        line = raw.strip()
        if not line:
            continue
        parts = line.replace(",", " ").split()
        if not parts:
            continue
        token = parts[0].strip().replace("\ufeff", "")
        if token:
            out.append(token)
    return out


def calc_sma(values: List[float], period: int) -> List[Optional[float]]:
    out: List[Optional[float]] = [None] * len(values)
    if period <= 0:
        return out
    s = 0.0
    for i, v in enumerate(values):
        s += v
        if i >= period:
            s -= values[i - period]
        if i >= period - 1:
            out[i] = s / period
    return out


def calc_ema(values: List[float], period: int) -> List[Optional[float]]:
    out: List[Optional[float]] = [None] * len(values)
    if not values or period <= 0:
        return out

    alpha = 2.0 / (period + 1.0)
    ema = values[0]
    out[0] = ema

    for i in range(1, len(values)):
        ema = alpha * values[i] + (1.0 - alpha) * ema
        out[i] = ema
    return out


def calc_kd(records: List[Rec], period: int = 9) -> Tuple[List[Optional[float]], List[Optional[float]]]:
    n = len(records)
    k_list: List[Optional[float]] = [None] * n
    d_list: List[Optional[float]] = [None] * n

    prev_k = 50.0
    prev_d = 50.0

    for i in range(n):
        start = max(0, i - period + 1)
        window = records[start:i + 1]
        hh = max(r.high for r in window)
        ll = min(r.low for r in window)

        if hh == ll:
            rsv = 50.0
        else:
            rsv = (records[i].close - ll) * 100.0 / (hh - ll)

        k = (2.0 / 3.0) * prev_k + (1.0 / 3.0) * rsv
        d = (2.0 / 3.0) * prev_d + (1.0 / 3.0) * k

        k_list[i] = k
        d_list[i] = d
        prev_k = k
        prev_d = d

    return k_list, d_list


def calc_rsi(values: List[float], period: int = 14) -> List[Optional[float]]:
    n = len(values)
    out: List[Optional[float]] = [None] * n
    if n < 2 or period <= 0:
        return out

    gains = [0.0] * n
    losses = [0.0] * n
    for i in range(1, n):
        diff = values[i] - values[i - 1]
        gains[i] = max(diff, 0.0)
        losses[i] = max(-diff, 0.0)

    if n <= period:
        return out

    avg_gain = sum(gains[1:period + 1]) / period
    avg_loss = sum(losses[1:period + 1]) / period

    if avg_loss == 0:
        out[period] = 100.0
    else:
        rs = avg_gain / avg_loss
        out[period] = 100.0 - (100.0 / (1.0 + rs))

    for i in range(period + 1, n):
        avg_gain = ((avg_gain * (period - 1)) + gains[i]) / period
        avg_loss = ((avg_loss * (period - 1)) + losses[i]) / period
        if avg_loss == 0:
            out[i] = 100.0
        else:
            rs = avg_gain / avg_loss
            out[i] = 100.0 - (100.0 / (1.0 + rs))

    return out


def calc_macd(values: List[float], fast: int = 12, slow: int = 26, signal: int = 9) -> Tuple[List[Optional[float]], List[Optional[float]], List[Optional[float]]]:
    ema_fast = calc_ema(values, fast)
    ema_slow = calc_ema(values, slow)

    dif: List[Optional[float]] = [None] * len(values)
    dif_base: List[float] = [0.0] * len(values)

    for i in range(len(values)):
        if ema_fast[i] is not None and ema_slow[i] is not None:
            dif[i] = ema_fast[i] - ema_slow[i]
            dif_base[i] = dif[i]
        else:
            dif[i] = None
            dif_base[i] = 0.0

    dea = calc_ema(dif_base, signal)
    hist: List[Optional[float]] = [None] * len(values)

    for i in range(len(values)):
        if dif[i] is not None and dea[i] is not None:
            hist[i] = dif[i] - dea[i]
        else:
            hist[i] = None

    return dif, dea, hist


def calc_mv(values: List[float], period: int) -> List[Optional[float]]:
    out: List[Optional[float]] = [None] * len(values)
    if period <= 0:
        return out

    s = 0.0
    for i, v in enumerate(values):
        s += v
        if i >= period:
            s -= values[i - period]
        if i >= period - 1:
            out[i] = s / period
    return out


def calc_signals(
    k_vals: List[Optional[float]],
    d_vals: List[Optional[float]],
    vols: List[float],
    mv9: List[Optional[float]],
) -> Tuple[List[bool], List[bool], str]:
    n = len(k_vals)
    buy = [False] * n
    sell = [False] * n
    last_signal = "NEUTRAL"

    for i in range(1, n):
        k0 = k_vals[i - 1]
        d0 = d_vals[i - 1]
        k1 = k_vals[i]
        d1 = d_vals[i]
        if k0 is None or d0 is None or k1 is None or d1 is None:
            continue

        if k0 <= d0 and k1 > d1 and k1 > 30:
            if mv9[i] is None or vols[i] > mv9[i]:
                buy[i] = True
                last_signal = "BUY"

        elif k0 >= d0 and k1 < d1 and k1 > 20:
            sell[i] = True
            last_signal = "SELL"

    return buy, sell, last_signal


def calc_confirmed_peaks(
    highs: List[float],
    confirm_bars: int = 14,
) -> List[Tuple[int, float]]:
    peaks: List[Tuple[int, float]] = []
    if not highs:
        return peaks

    candidate_idx = 0
    candidate_high = highs[0]

    for i in range(1, len(highs)):
        h = highs[i]

        if h > candidate_high:
            candidate_idx = i
            candidate_high = h

        if i - candidate_idx >= confirm_bars:
            peaks.append((candidate_idx, candidate_high))
            candidate_idx = i
            candidate_high = h

    return peaks


def calc_confirmed_lows(
    lows: List[float],
    confirm_bars: int = 14,
) -> List[Tuple[int, float]]:
    results: List[Tuple[int, float]] = []
    if not lows:
        return results

    candidate_idx = 0
    candidate_low = lows[0]

    for i in range(1, len(lows)):
        l = lows[i]

        if l < candidate_low:
            candidate_idx = i
            candidate_low = l

        if i - candidate_idx >= confirm_bars:
            results.append((candidate_idx, candidate_low))
            candidate_idx = i
            candidate_low = l

    return results


def display_signal_text(internal_signal: str) -> str:
    if internal_signal == "BUY":
        return "S"
    if internal_signal == "SELL":
        return "B"
    return "N"


class StockChartApp:
    def __init__(self, args):
        self.base_url = args.base_url.rstrip("/") + "/"
        self.market = normalize_market_code(args.code if args.code else args.market)
        self.data_dir = MARKET_PATHS.get(self.market, args.data_dir)
        self.stock_id = (args.sid or args.id).strip()
        self.window_script = args.window_script
        self.ticks = 60
        self.lower_mode = "vol"
        self.records: List[Rec] = []
        self.stock_list: List[str] = []
        self.stock_index: int = 0
        self.site_url = "http://aitradebook.com"
        self.logo_image = None

        self.root = tk.Tk()
        self.root.title("Stock Chart Simulator")
        self.root.configure(bg=C_BG)
        self.root.geometry("1400x860")
        self.root.minsize(960, 640)

        self._build_ui()
        self.init_stock_list()
        self.load_current_stock(use_bmwpid_fallback=False)

    def _style_optionmenu(self, menu_widget: tk.OptionMenu, width: int):
        menu_widget.config(
            bg=C_ENTRY_BG,
            fg=C_TEXT,
            activebackground="#333333",
            activeforeground=C_TEXT,
            relief=tk.FLAT,
            highlightthickness=0,
            width=width,
            bd=0,
            anchor="w",
        )
        try:
            menu = menu_widget["menu"]
            menu.config(
                bg=C_ENTRY_BG,
                fg=C_TEXT,
                activebackground="#333333",
                activeforeground=C_TEXT,
                bd=0,
            )
        except Exception:
            pass

    def get_window_script_path(self) -> str:
        script = self.window_script.strip()
        if os.path.isabs(script):
            return script
        base_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
        return os.path.join(base_dir, script)

    def get_logo_path(self) -> str:
        base_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
        return os.path.join(base_dir, "img", "aistock.png")

    def open_site(self, event=None):
        try:
            webbrowser.open(self.site_url)
            self.status_var.set(f"Opened {self.site_url}")
        except Exception as e:
            messagebox.showerror("Open URL failed", f"Failed to open:\n{self.site_url}\n\n{e}")

    def open_window_scanner(self):
        script_path = self.get_window_script_path()

        if not os.path.exists(script_path):
            messagebox.showerror(
                "Script not found",
                f"Cannot find window script:\n{script_path}"
            )
            return

        cmd = [sys.executable, script_path]

        try:
            subprocess.Popen(cmd)
            self.status_var.set("Opened stkchart_win.py")
        except Exception as e:
            messagebox.showerror("Launch failed", f"Failed to launch:\n{e}")

    def _build_site_logo(self, parent: tk.Widget):
        logo_path = self.get_logo_path()

        if os.path.exists(logo_path):
            try:
                self.logo_image = tk.PhotoImage(file=logo_path)
                self.logo_image = self.logo_image.subsample(3, 2)
                logo_btn = tk.Button(
                    parent,
                    image=self.logo_image,
                    command=self.open_site,
                    bg=C_PANEL,
                    activebackground=C_PANEL,
                    relief=tk.FLAT,
                    bd=0,
                    highlightthickness=0,
                    cursor="hand2",
                )
                logo_btn.pack(side=tk.LEFT, padx=(8, 8), pady=-4)
                return
            except Exception:
                pass

        fallback = tk.Label(
            parent,
            text="AIStock",
            fg=C_TITLE,
            bg=C_PANEL,
            cursor="hand2",
            font=("Arial", 11, "bold"),
        )
        fallback.pack(side=tk.LEFT, padx=(10, 10), pady=8)
        fallback.bind("<Button-1>", self.open_site)

    def _build_ui(self):
        top = tk.Frame(self.root, bg=C_PANEL, height=TOP_BAR_H)
        top.pack(side=tk.TOP, fill=tk.X)
        top.pack_propagate(False)

        self._build_site_logo(top)

        tk.Label(top, text="Market", fg=C_TEXT, bg=C_PANEL).pack(side=tk.LEFT, padx=(4, 4), pady=8)
        self.market_var = tk.StringVar(value=MARKET_NAMES[self.market])
        self.market_menu = tk.OptionMenu(
            top,
            self.market_var,
            *[MARKET_NAMES[k] for k in MARKET_ORDER],
            command=self.on_market_change,
        )
        self._style_optionmenu(self.market_menu, width=10)
        self.market_menu.pack(side=tk.LEFT, padx=(0, 10), pady=8)

        tk.Label(top, text="Stock", fg=C_TEXT, bg=C_PANEL).pack(side=tk.LEFT, padx=(4, 4), pady=8)
        self.stock_var = tk.StringVar(value=self.stock_id)
        self.stock_entry = tk.Entry(
            top,
            textvariable=self.stock_var,
            width=12,
            bg=C_ENTRY_BG,
            fg=C_TEXT,
            insertbackground=C_TEXT,
            relief=tk.FLAT,
        )
        self.stock_entry.pack(side=tk.LEFT, padx=(0, 8), pady=8)
        self.stock_entry.bind("<Return>", self.on_load)

        self.load_btn = tk.Button(
            top,
            text="Load",
            command=self.on_load,
            bg=C_ENTRY_BG,
            fg=C_TEXT,
            activebackground="#333333",
            activeforeground=C_TEXT,
            relief=tk.FLAT,
        )
        self.load_btn.pack(side=tk.LEFT, padx=(0, 8), pady=8)

        tk.Label(top, text="Ticks", fg=C_TEXT, bg=C_PANEL).pack(side=tk.LEFT, padx=(8, 4), pady=8)
        self.ticks_var = tk.StringVar(value=str(self.ticks))
        self.ticks_menu = tk.OptionMenu(
            top,
            self.ticks_var,
            *[str(v) for v in TICKS_CHOICES],
            command=self.on_ticks_change,
        )
        self._style_optionmenu(self.ticks_menu, width=4)
        self.ticks_menu.pack(side=tk.LEFT, padx=(0, 8), pady=8)

        tk.Label(top, text="Lower", fg=C_TEXT, bg=C_PANEL).pack(side=tk.LEFT, padx=(8, 4), pady=8)
        self.lower_var = tk.StringVar(value=self.lower_mode)
        self.lower_menu = tk.OptionMenu(
            top,
            self.lower_var,
            *LOWER_CHOICES,
            command=self.on_lower_change,
        )
        self._style_optionmenu(self.lower_menu, width=5)
        self.lower_menu.pack(side=tk.LEFT, padx=(0, 8), pady=8)

        self.status_var = tk.StringVar(value="Ready")
        self.status_label = tk.Label(top, textvariable=self.status_var, fg=C_STATUS, bg=C_PANEL, anchor="w")
        self.status_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(18, 12), pady=8)

        self.window_btn = tk.Button(
            top,
            text="Window",
            command=self.open_window_scanner,
            bg=C_ENTRY_BG,
            fg=C_TEXT,
            activebackground="#333333",
            activeforeground=C_TEXT,
            relief=tk.FLAT,
            width=8,
        )
        self.window_btn.pack(side=tk.RIGHT, padx=(8, 12), pady=8)

        self.fig = plt.Figure(figsize=(14, 8), facecolor=C_BG)
        self.fig.subplots_adjust(left=0.052, right=0.98, top=0.96, bottom=0.08, hspace=0.03)

        gs = self.fig.add_gridspec(5, 1, hspace=0.03)
        self.ax_price = self.fig.add_subplot(gs[:4, 0])
        self.ax_lower = self.fig.add_subplot(gs[4, 0], sharex=self.ax_price)

        self.ax_price.set_facecolor(C_AX)
        self.ax_lower.set_facecolor(C_AX)

        self.canvas = FigureCanvasTkAgg(self.fig, master=self.root)
        self.canvas_widget = self.canvas.get_tk_widget()
        self.canvas_widget.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=0, pady=0)

        self.root.bind("<Next>", self.on_page_down)
        self.root.bind("<Prior>", self.on_page_up)

    def current_market_base_url(self) -> str:
        return urljoin(self.base_url, self.data_dir.strip("/") + "/")

    def current_sma_url(self, stock_id: Optional[str] = None) -> str:
        sid = (stock_id or self.stock_var.get().strip() or self.stock_id)
        return urljoin(self.current_market_base_url(), f"z{sid}.sma")

    def current_bmwpid_url(self) -> str:
        return urljoin(self.current_market_base_url(), "bmwpid.txt")

    def init_stock_list(self):
        bmwpid_url = self.current_bmwpid_url()
        try:
            self.stock_list = load_stock_list_from_bmwpid_url(bmwpid_url)
        except Exception:
            self.stock_list = []

        if self.stock_list:
            if self.stock_id in self.stock_list:
                self.stock_index = self.stock_list.index(self.stock_id)
            else:
                self.stock_index = 0
                self.stock_id = self.stock_list[0]
                self.stock_var.set(self.stock_id)

    def on_market_change(self, value=None):
        display = (value or self.market_var.get()).strip()
        key = DISPLAY_TO_KEY.get(display, self.market)
        self.market = key
        self.data_dir = MARKET_PATHS[self.market]

        bmwpid_url = self.current_bmwpid_url()
        try:
            self.stock_list = load_stock_list_from_bmwpid_url(bmwpid_url)
            if self.stock_list:
                self.stock_index = 0
                first_id = self.stock_list[0]
                self.stock_id = first_id
                self.stock_var.set(first_id)
                self.status_var.set(f"{MARKET_NAMES[self.market]}  {first_id}")
            else:
                self.status_var.set(f"{MARKET_NAMES[self.market]}  empty")
        except Exception as e:
            self.stock_list = []
            self.stock_index = 0
            self.status_var.set(f"{MARKET_NAMES[self.market]}  bmwpid load failed: {e}")

        self.load_current_stock(use_bmwpid_fallback=False)

    def on_ticks_change(self, value=None):
        val = (value or self.ticks_var.get()).strip()
        try:
            self.ticks = int(val)
        except Exception:
            self.ticks = 60
            self.ticks_var.set("60")
        self.draw_chart()

    def on_lower_change(self, value=None):
        self.lower_mode = (value or self.lower_var.get()).strip().lower()
        if self.lower_mode not in LOWER_CHOICES:
            self.lower_mode = "vol"
            self.lower_var.set("vol")
        self.draw_chart()

    def on_load(self, event=None):
        self.stock_id = self.stock_var.get().strip() or self.stock_id
        if self.stock_list and self.stock_id in self.stock_list:
            self.stock_index = self.stock_list.index(self.stock_id)
        self.load_current_stock(use_bmwpid_fallback=False)

    def on_page_down(self, event=None):
        if not self.stock_list:
            return
        self.stock_index = (self.stock_index + 1) % len(self.stock_list)
        sid = self.stock_list[self.stock_index]
        self.stock_id = sid
        self.stock_var.set(sid)
        self.load_current_stock(False)

    def on_page_up(self, event=None):
        if not self.stock_list:
            return
        self.stock_index = (self.stock_index - 1) % len(self.stock_list)
        sid = self.stock_list[self.stock_index]
        self.stock_id = sid
        self.stock_var.set(sid)
        self.load_current_stock(False)

    def load_current_stock(self, use_bmwpid_fallback: bool):
        self.stock_id = self.stock_var.get().strip() or self.stock_id
        sma_url = self.current_sma_url(self.stock_id)

        try:
            raw = fetch_url_bytes(sma_url)
        except Exception as first_err:
            if use_bmwpid_fallback:
                try:
                    first_id = first_stock_id_from_bmwpid_url(self.current_bmwpid_url())
                    if first_id:
                        self.stock_id = first_id
                        self.stock_var.set(first_id)
                        sma_url = self.current_sma_url(first_id)
                        raw = fetch_url_bytes(sma_url)
                    else:
                        raise first_err
                except Exception:
                    self.records = []
                    self.status_var.set(f"Load failed: {self.stock_id} | {first_err}")
                    self.draw_chart()
                    return
            else:
                self.records = []
                self.status_var.set(f"Load failed: {self.stock_id} | {first_err}")
                self.draw_chart()
                return

        try:
            self.records = parse_sma_bytes(raw)
           # self.status_var.set(f"{self.stock_id}  {len(self.records)} bars  [{self.base_url.rstrip('/')}]")
        except Exception as e:
            self.records = []
            self.status_var.set(f"Parse failed: {self.stock_id} | {e}")
        self.draw_chart()

    def draw_chart(self):
        self.ax_price.clear()
        self.ax_lower.clear()

        self.ax_price.set_facecolor(C_AX)
        self.ax_lower.set_facecolor(C_AX)

        title_text = f"{MARKET_NAMES.get(self.market, self.market)} - {self.stock_var.get().strip()}"

        if not self.records:
            self.ax_price.text(0.5, 0.5, "No data", color=C_TEXT, ha="center", va="center", fontsize=16)
            self.ax_price.set_xticks([])
            self.ax_price.set_yticks([])
            self.ax_lower.set_xticks([])
            self.ax_lower.set_yticks([])
            self.ax_price.set_title(title_text, color=C_TITLE, fontsize=14, loc="left")
            self.canvas.draw_idle()
            return

        calc_bars = max(self.ticks, 120)
        work_data = self.records[-calc_bars:] if len(self.records) > calc_bars else self.records[:]

        highs_all = [r.high / PRICE_SCALE for r in work_data]
        lows_all = [r.low / PRICE_SCALE for r in work_data]
        closes_all = [r.close / PRICE_SCALE for r in work_data]
        vols_all = [float(r.vol) for r in work_data]

        ma5_all = calc_sma(closes_all, 5)
        ma12_all = calc_sma(closes_all, 12)
        ma24_all = calc_sma(closes_all, 24)
        mv9_all = calc_sma(vols_all, 9)

        k_vals_all, d_vals_all = calc_kd(work_data, 9)
        rsi14_all = calc_rsi(closes_all, 14)
        dif_all, dea_all, hist_all = calc_macd(closes_all, 12, 26, 9)
        buy_flags_all, sell_flags_all, last_signal = calc_signals(k_vals_all, d_vals_all, vols_all, mv9_all)
        confirmed_peaks_all = calc_confirmed_peaks(highs_all, 14)
        confirmed_lows_all = calc_confirmed_lows(lows_all, 14)

        show_n = min(self.ticks, len(work_data))
        data = work_data[-show_n:]
        highs = highs_all[-show_n:]
        lows = lows_all[-show_n:]
        closes = closes_all[-show_n:]
        vols = vols_all[-show_n:]

        ma5 = ma5_all[-show_n:]
        ma12 = ma12_all[-show_n:]
        ma24 = ma24_all[-show_n:]
        mv9 = mv9_all[-show_n:]

        k_vals = k_vals_all[-show_n:]
        d_vals = d_vals_all[-show_n:]
        rsi14 = rsi14_all[-show_n:]
        dif = dif_all[-show_n:]
        dea = dea_all[-show_n:]
        hist = hist_all[-show_n:]
        buy_flags = buy_flags_all[-show_n:]
        sell_flags = sell_flags_all[-show_n:]

        offset = len(work_data) - show_n
        confirmed_peaks = [
            (idx - offset, price)
            for idx, price in confirmed_peaks_all
            if offset <= idx < len(work_data)
        ]
        confirmed_lows = [
            (idx - offset, price)
            for idx, price in confirmed_lows_all
            if offset <= idx < len(work_data)
        ]

        x = list(range(len(data)))

        max_h = max(highs)
        min_l = min(lows)
        rng = max(max_h - min_l, 0.01)

        self.ax_price.grid(True, color=C_GRID, linestyle="--", linewidth=0.5, alpha=0.6)
        self.ax_lower.grid(True, color=C_GRID, linestyle="--", linewidth=0.5, alpha=0.4)

        self.ax_price.set_title(title_text, color=C_TITLE, fontsize=14, loc="left")
        self.ax_price.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:.2f}"))

        width = 0.6
        lower_colors = []

        for i, r in enumerate(data):
            o = r.open / PRICE_SCALE
            h = r.high / PRICE_SCALE
            l = r.low / PRICE_SCALE
            c = r.close / PRICE_SCALE
            color = C_UP if c >= o else C_DN
            lower_colors.append(color)

            self.ax_price.plot([i, i], [l, h], color=C_WICK, linewidth=1.0, zorder=2)

            bottom = min(o, c)
            height = abs(c - o)
            if height == 0:
                self.ax_price.plot([i - width / 2, i + width / 2], [c, c], color=color, linewidth=2.0, zorder=3)
            else:
                rect = Rectangle(
                    (i - width / 2, bottom),
                    width,
                    height,
                    facecolor=color,
                    edgecolor=color,
                    linewidth=1.0,
                    zorder=3,
                )
                self.ax_price.add_patch(rect)

        self.ax_price.plot(x, ma5, color=C_MA5, linewidth=1.2, label="MA5")
        self.ax_price.plot(x, ma12, color=C_MA12, linewidth=1.2, label="MA12")
        self.ax_price.plot(x, ma24, color=C_MA24, linewidth=1.2, label="MA24")

        marker_pad = rng * 0.03
        text_dx = 0.18

        for i, flag in enumerate(buy_flags):
            if flag:
                yv = lows[i] - marker_pad
                self.ax_price.text(
                    i,
                    yv,
                    "▼",
                    color=C_SELL,
                    fontsize=12,
                    ha="center",
                    va="top",
                    zorder=5,
                    fontweight="bold",
                )
                self.ax_price.text(
                    i + text_dx,
                    yv,
                    "B",
                    color=C_SELL,
                    fontsize=10,
                    ha="left",
                    va="top",
                    zorder=6,
                    fontweight="bold",
                )

        for i, flag in enumerate(sell_flags):
            if flag:
                yv = highs[i] + marker_pad
                self.ax_price.text(
                    i,
                    yv,
                    "▲",
                    color=C_BUY,
                    fontsize=12,
                    ha="center",
                    va="bottom",
                    zorder=5,
                    fontweight="bold",
                )
                self.ax_price.text(
                    i + text_dx,
                    yv,
                    "S",
                    color=C_BUY,
                    fontsize=10,
                    ha="left",
                    va="bottom",
                    zorder=6,
                    fontweight="bold",
                )

        for px, py in confirmed_peaks:
            pyv = float(py)
            self.ax_price.plot(
                [px],
                [pyv],
                marker="o",
                markersize=3.5,
                color=C_TITLE,
                zorder=7,
            )
            self.ax_price.annotate(
                f"{pyv:.2f}",
                xy=(px, pyv),
                xytext=(-20, 10),
                textcoords="offset pixels",
                color=C_TITLE,
                fontsize=8,
                ha="left",
                va="top",
                zorder=8,
                fontweight="bold",
            )

        for px, py in confirmed_lows:
            pyv = float(py)
            self.ax_price.plot(
                [px],
                [pyv],
                marker="o",
                markersize=3.5,
                color="#00ffff",
                zorder=7,
            )
            self.ax_price.annotate(
                f"{pyv:.2f}",
                xy=(px, pyv),
                xytext=(-20, -20),
                textcoords="offset pixels",
                color="#00ffff",
                fontsize=8,
                ha="left",
                va="top",
                zorder=8,
                fontweight="bold",
            )

        if self.lower_mode == "vol":
            self.ax_lower.bar(x, vols, width=0.6, color=lower_colors, edgecolor=lower_colors, linewidth=0.5)
            self.ax_lower.plot(x, mv9, color=C_MA12, linewidth=1.2, label="MV9")
            vmax = max(vols) if vols else 0
            self.ax_lower.set_ylim(0, vmax * 1.15 if vmax > 0 else 1)
            self.ax_lower.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{int(y):,}"))
            self.ax_lower.set_ylabel("Vol", color=C_TEXT, fontsize=9)
            self.ax_lower.legend(loc="upper left", fontsize=8, facecolor=C_AX, edgecolor="#444444", labelcolor=C_TEXT)

        elif self.lower_mode == "kd":
            self.ax_lower.plot(x, k_vals, color=C_K, linewidth=1.2, label="K")
            self.ax_lower.plot(x, d_vals, color=C_D, linewidth=1.2, label="D")
            self.ax_lower.axhline(80, color="#666666", linestyle="--", linewidth=0.8)
            self.ax_lower.axhline(20, color="#666666", linestyle="--", linewidth=0.8)
            self.ax_lower.set_ylim(0, 100)
            self.ax_lower.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:.0f}"))
            self.ax_lower.set_ylabel("KD", color=C_TEXT, fontsize=9)
            self.ax_lower.legend(loc="upper left", fontsize=8, facecolor=C_AX, edgecolor="#444444", labelcolor=C_TEXT)

        elif self.lower_mode == "rsi":
            self.ax_lower.plot(x, rsi14, color=C_RSI, linewidth=1.2, label="RSI14")
            self.ax_lower.axhline(70, color="#666666", linestyle="--", linewidth=0.8)
            self.ax_lower.axhline(30, color="#666666", linestyle="--", linewidth=0.8)
            self.ax_lower.set_ylim(0, 100)
            self.ax_lower.yaxis.set_major_formatter(FuncFormatter(lambda y, _: f"{y:.0f}"))
            self.ax_lower.set_ylabel("RSI", color=C_TEXT, fontsize=9)
            self.ax_lower.legend(loc="upper left", fontsize=8, facecolor=C_AX, edgecolor="#444444", labelcolor=C_TEXT)

        else:
            hist_vals = [0.0 if v is None else v for v in hist]
            hist_colors = [C_MACD_POS if v >= 0 else C_MACD_NEG for v in hist_vals]
            self.ax_lower.bar(x, hist_vals, width=0.6, color=hist_colors, edgecolor=hist_colors, linewidth=0.5, alpha=0.8)
            self.ax_lower.plot(x, dif, color=C_DIF, linewidth=1.2, label="DIF")
            self.ax_lower.plot(x, dea, color=C_DEA, linewidth=1.2, label="DEA")
            self.ax_lower.axhline(0, color="#666666", linestyle="--", linewidth=0.8)
            self.ax_lower.set_ylabel("MACD", color=C_TEXT, fontsize=9)
            self.ax_lower.legend(loc="upper left", fontsize=8, facecolor=C_AX, edgecolor="#444444", labelcolor=C_TEXT)

        self.ax_price.set_xlim(-1, len(data))
        pad = rng * 0.08
        self.ax_price.set_ylim(min_l - pad, max_h + pad)

        xticks = list(range(0, len(data), max(1, len(data) // 8)))
        xlabels = [format_date(data[i].date) for i in xticks]

        self.ax_price.set_xticks(xticks)
        self.ax_price.tick_params(axis="x", labelbottom=False)

        self.ax_lower.set_xticks(xticks)
        self.ax_lower.set_xticklabels(xlabels, rotation=0, color=C_TEXT, fontsize=9)

        self.ax_price.tick_params(axis="y", colors=C_TEXT, labelsize=9)
        self.ax_lower.tick_params(axis="y", colors=C_TEXT, labelsize=9)
        self.ax_lower.tick_params(axis="x", colors=C_TEXT, labelsize=9)

        for s in self.ax_price.spines.values():
            s.set_color("#444444")
        for s in self.ax_lower.spines.values():
            s.set_color("#444444")

        last = data[-1]
        last_ma5 = ma5[-1]
        last_ma12 = ma12[-1]
        last_ma24 = ma24[-1]
        last_mv9 = mv9[-1]
        last_k = k_vals[-1]
        last_d = d_vals[-1]

        ma5_txt = f"{last_ma5:.2f}" if last_ma5 is not None else "--"
        ma12_txt = f"{last_ma12:.2f}" if last_ma12 is not None else "--"
        ma24_txt = f"{last_ma24:.2f}" if last_ma24 is not None else "--"
        mv9_txt = f"{last_mv9:.0f}" if last_mv9 is not None else "--"
        k_txt = f"{last_k:.1f}" if last_k is not None else "--"
        d_txt = f"{last_d:.1f}" if last_d is not None else "--"
        shown_signal = display_signal_text(last_signal)

        info = (
            f"Date {format_date(last.date)}  "
            f"O {fmt_price(last.open)}  "
            f"H {fmt_price(last.high)}  "
            f"L {fmt_price(last.low)}  "
            f"C {fmt_price(last.close)}  "
            f"V {last.vol}  "
            f"MV9 {mv9_txt}  "
            f"MA5 {ma5_txt}  "
            f"MA12 {ma12_txt}  "
            f"MA24 {ma24_txt}  "
            f"K {k_txt}  "
            f"D {d_txt}  "
            f"Signal {shown_signal}  "
            f"Peaks {len(confirmed_peaks)}  "
            f"Lows {len(confirmed_lows)}"
        )

        self.ax_price.text(
            0.01,
            0.98,
            info,
            transform=self.ax_price.transAxes,
            color=C_TEXT,
            ha="left",
            va="top",
            fontsize=10,
        )

        self.ax_price.legend(
            loc="upper right",
            fontsize=8,
            facecolor=C_AX,
            edgecolor="#444444",
            labelcolor=C_TEXT,
        )

        self.canvas.draw_idle()

    def run(self):
        self.root.mainloop()


def build_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base-url", default=DEFAULT_BASE_URL, help="base site url")
    parser.add_argument("--data-dir", default="twnew/day1", help="data directory relative to base url")

    parser.add_argument("--market", default="tw", choices=MARKET_ORDER, help="default market")
    parser.add_argument("--id", default="1101", help="default stock id")

    parser.add_argument("--code", default="", help="market code: tw/nsd/nyse/cn/hk/jp")
    parser.add_argument("--sid", default="", help="stock id")

    parser.add_argument("--window-script", default="stkchart_win.py", help="window scanner program path")

    return parser


def main():
    args = build_parser().parse_args()
    app = StockChartApp(args)
    app.run()


if __name__ == "__main__":
    main()
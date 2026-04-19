#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import struct
import argparse
import subprocess
import sys
import os
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


def decode_text_fallback(data: bytes) -> str:
    for enc in ("utf-8", "cp950", "big5", "utf-8-sig", "latin1"):
        try:
            return data.decode(enc)
        except Exception:
            pass
    return data.decode("latin1", errors="ignore")


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


def calc_mv(values: List[float], period: int) -> List[Optional[float]]:
    return calc_sma(values, period)


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


def calc_signals(
    k_vals: List[Optional[float]],
    d_vals: List[Optional[float]],
    vols: List[float],
    mv9: List[Optional[float]],
) -> Tuple[List[bool], List[bool]]:
    n = len(k_vals)
    buy = [False] * n
    sell = [False] * n

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
        elif k0 >= d0 and k1 < d1 and k1 > 20:
            sell[i] = True

    return buy, sell


class StockChartGridApp:
    def __init__(self, args):
        self.base_url = args.base_url.rstrip("/") + "/"
        self.market = args.market
        self.data_dir = MARKET_PATHS.get(self.market, args.data_dir)
        self.ticks = 60
        self.grid_n = 3
        self.page_size = self.grid_n * self.grid_n
        self.page_index = 0
        self.stock_list: List[str] = []
        self.detail_script = args.detail_script
        self.ax_stock_map = {}

        self.root = tk.Tk()
        self.root.title("Stock Chart Grid Scanner")
        self.root.configure(bg=C_BG)
        self.root.geometry("1500x980")
        self.root.minsize(1000, 700)

        self._build_ui()
        self.init_stock_list()
        self.draw_page()

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

    def rebuild_axes(self):
        self.fig.clf()
        self.axes = []
        self.ax_stock_map = {}
        n = self.grid_n

        if n <= 3:
            hspace, wspace = 0.16, 0.10
        elif n <= 5:
            hspace, wspace = 0.10, 0.06
        else:
            hspace, wspace = 0.06, 0.04

        self.fig.subplots_adjust(
            left=0.02, right=0.995,
            top=0.97, bottom=0.03,
            hspace=hspace, wspace=wspace
        )

        for i in range(n * n):
            ax = self.fig.add_subplot(n, n, i + 1)
            ax.set_facecolor(C_AX)
            self.axes.append(ax)

    def _build_ui(self):
        top = tk.Frame(self.root, bg=C_PANEL, height=TOP_BAR_H)
        top.pack(side=tk.TOP, fill=tk.X)
        top.pack_propagate(False)

        tk.Label(top, text="Market", fg=C_TEXT, bg=C_PANEL).pack(side=tk.LEFT, padx=(12, 4), pady=8)
        self.market_var = tk.StringVar(value=MARKET_NAMES[self.market])
        self.market_menu = tk.OptionMenu(
            top,
            self.market_var,
            *[MARKET_NAMES[k] for k in MARKET_ORDER],
            command=self.on_market_change,
        )
        self._style_optionmenu(self.market_menu, width=10)
        self.market_menu.pack(side=tk.LEFT, padx=(0, 10), pady=8)

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

        self.status_var = tk.StringVar(value="Ready")
        self.status_label = tk.Label(top, textvariable=self.status_var, fg=C_STATUS, bg=C_PANEL, anchor="w")
        self.status_label.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=(18, 12), pady=8)

        self.fig = plt.Figure(figsize=(15, 10), facecolor=C_BG)
        self.axes = []
        self.rebuild_axes()

        self.canvas = FigureCanvasTkAgg(self.fig, master=self.root)
        self.canvas_widget = self.canvas.get_tk_widget()
        self.canvas_widget.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=0, pady=0)

        self.canvas.mpl_connect("button_press_event", self.on_chart_click)

        self.root.bind("<Next>", self.on_page_down)
        self.root.bind("<Prior>", self.on_page_up)
        self.root.bind("[", self.on_grid_down)
        self.root.bind("]", self.on_grid_up)

    def current_market_base_url(self) -> str:
        return urljoin(self.base_url, self.data_dir.strip("/") + "/")

    def current_sma_url(self, stock_id: str) -> str:
        return urljoin(self.current_market_base_url(), f"z{stock_id}.sma")

    def current_bmwpid_url(self) -> str:
        return urljoin(self.current_market_base_url(), "bmwpid.txt")

    def get_launch_market_code(self) -> str:
        if self.market == "jpn":
            return "jp"
        return self.market

    def get_detail_script_path(self) -> str:
        script = self.detail_script.strip()
        if os.path.isabs(script):
            return script
        base_dir = os.path.dirname(os.path.abspath(sys.argv[0]))
        return os.path.join(base_dir, script)

    def launch_detail_chart(self, stock_id: str):
        script_path = self.get_detail_script_path()
        market_code = self.get_launch_market_code()

        if not os.path.exists(script_path):
            messagebox.showerror(
                "Script not found",
                f"Cannot find detail script:\n{script_path}"
            )
            return

        cmd = [
            sys.executable,
            script_path,
            "--sid", stock_id,
            "--code", market_code,
            "--base-url", self.base_url.rstrip("/"),
        ]

        try:
            subprocess.Popen(cmd)
            self.status_var.set(f"Open detail: {stock_id} ({market_code}) via {self.base_url.rstrip('/')}")
        except Exception as e:
            messagebox.showerror("Launch failed", f"Failed to launch:\n{e}")

    def init_stock_list(self):
        try:
            self.stock_list = load_stock_list_from_bmwpid_url(self.current_bmwpid_url())
            self.page_index = 0
        except Exception as e:
            self.stock_list = []
            self.status_var.set(f"bmwpid load failed: {e}")

    def on_market_change(self, value=None):
        display = (value or self.market_var.get()).strip()
        key = self.market
        for k, v in MARKET_NAMES.items():
            if v == display:
                key = k
                break
        self.market = key
        self.data_dir = MARKET_PATHS[self.market]
        self.init_stock_list()
        self.draw_page()

    def on_ticks_change(self, value=None):
        val = (value or self.ticks_var.get()).strip()
        try:
            self.ticks = int(val)
        except Exception:
            self.ticks = 60
            self.ticks_var.set("60")
        self.draw_page()

    def on_page_down(self, event=None):
        if not self.stock_list:
            return
        max_page = max(0, (len(self.stock_list) - 1) // self.page_size)
        self.page_index = min(self.page_index + 1, max_page)
        self.draw_page()

    def on_page_up(self, event=None):
        if not self.stock_list:
            return
        self.page_index = max(self.page_index - 1, 0)
        self.draw_page()

    def on_grid_down(self, event=None):
        if self.grid_n > 1:
            old_start = self.page_index * self.page_size
            self.grid_n -= 1
            self.page_size = self.grid_n * self.grid_n
            self.page_index = old_start // self.page_size
            self.rebuild_axes()
            self.draw_page()

    def on_grid_up(self, event=None):
        if self.grid_n < 8:
            old_start = self.page_index * self.page_size
            self.grid_n += 1
            self.page_size = self.grid_n * self.grid_n
            self.page_index = old_start // self.page_size
            self.rebuild_axes()
            self.draw_page()

    def on_chart_click(self, event):
        if event.inaxes is None:
            return
        stock_id = self.ax_stock_map.get(event.inaxes)
        if not stock_id:
            return
        self.launch_detail_chart(stock_id)

    def fetch_stock_records(self, stock_id: str) -> List[Rec]:
        raw = fetch_url_bytes(self.current_sma_url(stock_id))
        return parse_sma_bytes(raw)

    def draw_single_chart(self, ax, stock_id: str):
        ax.clear()
        ax.set_facecolor(C_AX)
        self.ax_stock_map[ax] = stock_id

        try:
            records = self.fetch_stock_records(stock_id)
        except Exception:
            ax.text(0.5, 0.5, f"{stock_id}\nload fail", color=C_TEXT, ha="center", va="center", fontsize=max(6, 14 - self.grid_n))
            ax.set_xticks([])
            ax.set_yticks([])
            for s in ax.spines.values():
                s.set_color("#444444")
            return

        if not records:
            ax.text(0.5, 0.5, f"{stock_id}\nno data", color=C_TEXT, ha="center", va="center", fontsize=max(6, 14 - self.grid_n))
            ax.set_xticks([])
            ax.set_yticks([])
            for s in ax.spines.values():
                s.set_color("#444444")
            return

        calc_bars = max(self.ticks, 120)
        work_data = records[-calc_bars:] if len(records) > calc_bars else records[:]

        highs_all = [r.high / PRICE_SCALE for r in work_data]
        lows_all = [r.low / PRICE_SCALE for r in work_data]
        closes_all = [r.close / PRICE_SCALE for r in work_data]
        vols_all = [float(r.vol) for r in work_data]

        ma5_all = calc_sma(closes_all, 5)
        ma12_all = calc_sma(closes_all, 12)
        ma24_all = calc_sma(closes_all, 24)
        mv9_all = calc_mv(vols_all, 9)
        k_vals_all, d_vals_all = calc_kd(work_data, 9)
        buy_flags_all, sell_flags_all = calc_signals(k_vals_all, d_vals_all, vols_all, mv9_all)

        show_n = min(self.ticks, len(work_data))
        data = work_data[-show_n:]
        highs = highs_all[-show_n:]
        lows = lows_all[-show_n:]
        ma5 = ma5_all[-show_n:]
        ma12 = ma12_all[-show_n:]
        ma24 = ma24_all[-show_n:]
        buy_flags = buy_flags_all[-show_n:]
        sell_flags = sell_flags_all[-show_n:]
        x = list(range(len(data)))

        width = 0.55
        max_h = max(highs)
        min_l = min(lows)
        rng = max(max_h - min_l, 0.01)
        marker_pad = rng * 0.03

        for i, r in enumerate(data):
            o = r.open / PRICE_SCALE
            h = r.high / PRICE_SCALE
            l = r.low / PRICE_SCALE
            c = r.close / PRICE_SCALE
            color = C_UP if c >= o else C_DN

            ax.plot([i, i], [l, h], color=C_WICK, linewidth=0.7, zorder=2)

            bottom = min(o, c)
            height = abs(c - o)
            if height == 0:
                ax.plot([i - width / 2, i + width / 2], [c, c], color=color, linewidth=1.2, zorder=3)
            else:
                rect = Rectangle(
                    (i - width / 2, bottom),
                    width,
                    height,
                    facecolor=color,
                    edgecolor=color,
                    linewidth=0.7,
                    zorder=3,
                )
                ax.add_patch(rect)

        ax.plot(x, ma5, color=C_MA5, linewidth=0.8)
        ax.plot(x, ma12, color=C_MA12, linewidth=0.8)
        ax.plot(x, ma24, color=C_MA24, linewidth=0.8)

        bs_font = max(4, 10 - self.grid_n)
        title_font = max(5, 12 - self.grid_n)

        for i, flag in enumerate(buy_flags):
            if flag:
                ax.text(i, lows[i] - marker_pad, "B", color=C_SELL, fontsize=bs_font, ha="center", va="top", fontweight="bold")

        for i, flag in enumerate(sell_flags):
            if flag:
                ax.text(i, highs[i] + marker_pad, "S", color=C_BUY, fontsize=bs_font, ha="center", va="bottom", fontweight="bold")

        last = data[-1]
        last_close = last.close / PRICE_SCALE
        title = f"{stock_id} C {last_close:.2f}"
        ax.set_title(title, color=C_TITLE, fontsize=title_font, pad=2, loc="left")

        ax.grid(True, color=C_GRID, linestyle="--", linewidth=0.35, alpha=0.30)
        ax.set_xlim(-1, len(data))
        pad = rng * 0.10
        ax.set_ylim(min_l - pad, max_h + pad)

        ax.set_xticks([])
        ax.set_yticks([])

        for s in ax.spines.values():
            s.set_color("#444444")

    def draw_page(self):
        self.ax_stock_map = {}

        for ax in self.axes:
            ax.clear()
            ax.set_facecolor(C_AX)

        if not self.stock_list:
            for ax in self.axes:
                ax.text(0.5, 0.5, "No stock list", color=C_TEXT, ha="center", va="center", fontsize=12)
                ax.set_xticks([])
                ax.set_yticks([])
                for s in ax.spines.values():
                    s.set_color("#444444")
            self.canvas.draw_idle()
            return

        start = self.page_index * self.page_size
        end = min(start + self.page_size, len(self.stock_list))
        page_stocks = self.stock_list[start:end]

        for i, ax in enumerate(self.axes):
            if i < len(page_stocks):
                self.draw_single_chart(ax, page_stocks[i])
            else:
                ax.text(0.5, 0.5, "", color=C_TEXT, ha="center", va="center")
                ax.set_xticks([])
                ax.set_yticks([])
                for s in ax.spines.values():
                    s.set_color("#444444")

        total_pages = max(1, (len(self.stock_list) + self.page_size - 1) // self.page_size)
        page_no = self.page_index + 1
        first_sid = page_stocks[0] if page_stocks else "--"
        last_sid = page_stocks[-1] if page_stocks else "--"
        self.status_var.set(
            f"{MARKET_NAMES[self.market]}  {self.grid_n}x{self.grid_n}  page {page_no}/{total_pages}  stocks {start+1}-{end}/{len(self.stock_list)}  {first_sid} ~ {last_sid}  | click chart to open detail"
        )

        self.canvas.draw_idle()

    def run(self):
        self.root.mainloop()


def build_parser():
    parser = argparse.ArgumentParser()
    parser.add_argument("--base-url", default=DEFAULT_BASE_URL, help="base site url")
    parser.add_argument("--data-dir", default="twnew/day1", help="data directory relative to base url")
    parser.add_argument("--market", default="tw", choices=MARKET_ORDER, help="default market")
    parser.add_argument("--id", default="1101", help="unused in grid mode")
    parser.add_argument("--detail-script", default="stkchart.py", help="detail chart program path")
    return parser


def main():
    args = build_parser().parse_args()
    app = StockChartGridApp(args)
    app.run()


if __name__ == "__main__":
    main()
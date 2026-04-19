# 📊 stkchart_py

Open-source stock chart tools written in Python.

This project provides two practical tools:

* `stkchart.py` → single stock chart viewer
* `stkchart_win.py` → multi-stock grid scanner (Tkinter + Matplotlib)

Designed for fast visualization, technical analysis, and real trading usage.

---

## 🚀 Features

### stkchart.py

* Single stock candlestick chart
* Moving averages (MA5 / MA12 / MA24)
* KD indicator + signal detection
* Multi-market support (TW / US / CN / HK / JP)
* Lightweight and fast

### stkchart_win.py

* Grid view: **1x1 → 8x8 dynamic layout**
* Scan multiple stocks at once
* Click chart → open detailed chart
* Page navigation (PageUp / PageDown)
* Clean UI (optimized for dense data display)
* No Y-axis scale (prevents layout shift for large grids)

---

## 🌍 Supported Markets

* Taiwan (TW)
* Nasdaq (NSD)
* NYSE
* China (CN)
* Hong Kong (HK)
* Japan (JP)

---

## 📦 Requirements

* Python 3.x
* matplotlib
* tkinter (usually built-in)

Install matplotlib if needed:

```bash
pip install matplotlib
```

---

## ▶️ Usage

### Run grid scanner

```bash
python stkchart_win.py
```

### Run single chart

```bash
python stkchart.py
```

---

## 🎮 Controls (stkchart_win.py)

| Key         | Action                    |
| ----------- | ------------------------- |
| PageDown    | Next page                 |
| PageUp      | Previous page             |
| `[`         | Decrease grid (8x8 → 1x1) |
| `]`         | Increase grid (1x1 → 8x8) |
| Mouse click | Open detail chart         |

---

## ⚙️ Data Source

The system loads stock data from:

```
http://aitradebook.com
```

Data format:

* `.sma` binary files
* `bmwpid.txt` for stock list

You can modify the base URL:

```bash
python stkchart_win.py --base-url http://your-server
```

---

## 🧠 Design Philosophy

This project follows a **CS-style architecture**:

* Python version → client-side tool (download & run)
* Web version → browser-based system

### Goal

* Provide real usable tools, not demo code
* Keep system fast, simple, and scalable
* Enable integration with:

  * AITrader
  * MobileMeet
  * AIShop ecosystem

---

## 📸 Screenshot

*(Add screenshot.png here later for better presentation)*

---

## 🔓 License

MIT License

You are free to:

* use
* modify
* distribute

---

## 👤 Author

beltan lee

---

## ⭐ Notes

This project is part of a larger system including:

* Trading tools
* AI-assisted analysis
* Distributed video + data systems

---

## 🚧 Future Work

* Web version integration (stkchart.html)
* Ranking system (rank.html)
* Advanced screening (bmwgrep.html)
* AI-based trading signals
* Movie / visualization integration (experimental)

---

## 🤝 Contributions

Contributions are welcome, but keep it simple and practical.

---

## 🧩 Final Note

This is not just a chart.

It is a **working tool**.

from __future__ import annotations

import os
import re
import shutil
import subprocess
import threading
import time
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
import tkinter as tk
from tkinter import filedialog, messagebox, ttk

APP_NAME = "LUIGI IPTV PLAYLIST MAKER"
VERSION = "0.3.0"


@dataclass
class Channel:
    extinf: str
    url: str
    name: str


def read_text(path: Path) -> str:
    for enc in ("utf-8-sig", "utf-8", "cp1250", "latin-1"):
        try:
            return path.read_text(encoding=enc)
        except UnicodeDecodeError:
            pass
    return path.read_text(encoding="utf-8", errors="replace")


def parse(path: Path) -> list[Channel]:
    out: list[Channel] = []
    ext = ""
    for raw in read_text(path).splitlines():
        s = raw.strip()
        if not s:
            continue
        if s.startswith("#EXTINF"):
            ext = s
        elif s.startswith("#"):
            continue
        elif "://" in s:
            name = ext.rsplit(",", 1)[-1].strip() if "," in ext else s
            out.append(Channel(ext or f"#EXTINF:-1,{name}", s, name))
            ext = ""
    return out


def dedupe(items: list[Channel]) -> tuple[list[Channel], list[tuple[Channel, str]]]:
    keep: list[Channel] = []
    removed: list[tuple[Channel, str]] = []
    urls: set[str] = set()
    names: set[str] = set()

    for c in items:
        u = c.url.casefold().strip()
        n = re.sub(r"\s+", " ", c.name).casefold().strip()

        if u in urls:
            removed.append((c, "DUPLICATE_URL"))
            continue
        if n and n in names:
            removed.append((c, "DUPLICATE_NAME"))
            continue

        urls.add(u)
        if n:
            names.add(n)
        keep.append(c)

    return keep, removed


def ffprobe_path() -> str | None:
    for p in (
        shutil.which("ffprobe"),
        r"C:\ffmpeg-8.1.2-essentials_build\bin\ffprobe.exe",
        str(Path.cwd() / "ffprobe.exe"),
    ):
        if p and Path(p).is_file():
            return p
    return None


def classify(text: str) -> str:
    t = text.casefold()
    if any(x in t for x in ("401", "403", "unauthorized", "forbidden")):
        return "AUTH_OR_GEO"
    if "404" in t or "not found" in t:
        return "NOT_FOUND"
    if "timeout" in t or "timed out" in t:
        return "TIMEOUT"
    if any(x in t for x in ("resolve", "no such host", "name or service not known")):
        return "DNS_ERROR"
    if "connection refused" in t:
        return "CONNECTION_REFUSED"
    return "DEAD"


def test(
    c: Channel,
    timeout: int,
    ffprobe: str | None,
    stop: threading.Event,
) -> tuple[Channel, str, str, float]:
    start = time.monotonic()

    if stop.is_set():
        return c, "STOPPED", "Přerušeno", 0.0

    if ffprobe:
        cmd = [
            ffprobe,
            "-v", "error",
            "-user_agent", "Mozilla/5.0",
            "-rw_timeout", str(timeout * 1_000_000),
            "-show_entries", "format=format_name",
            "-of", "default=noprint_wrappers=1:nokey=1",
            c.url,
        ]
        try:
            r = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout + 3,
                creationflags=subprocess.CREATE_NO_WINDOW if os.name == "nt" else 0,
            )
            elapsed = time.monotonic() - start

            if r.returncode == 0:
                return c, ("SLOW" if elapsed >= timeout * 0.75 else "OK"), f"{elapsed:.1f}s", elapsed

            reason = (r.stderr or "ffprobe error").strip().splitlines()[-1][:240]
            return c, classify(reason), reason, elapsed

        except subprocess.TimeoutExpired:
            return c, "TIMEOUT", f"Timeout {timeout}s", time.monotonic() - start
        except Exception as ex:
            return c, classify(str(ex)), str(ex)[:240], time.monotonic() - start

    req = urllib.request.Request(c.url, headers={"User-Agent": "Mozilla/5.0"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as r:
            r.read(256)
            elapsed = time.monotonic() - start
            return c, ("SLOW" if elapsed >= timeout * 0.75 else "OK"), f"HTTP {getattr(r, 'status', 200)}", elapsed
    except Exception as ex:
        return c, classify(str(ex)), str(ex)[:240], time.monotonic() - start


def save_m3u(path: Path, items: list[Channel]) -> None:
    lines = ["#EXTM3U"]
    for c in items:
        lines += [c.extinf, c.url]
    path.write_text("\n".join(lines) + "\n", encoding="utf-8-sig")


def fmt_time(seconds: float) -> str:
    total = max(0, int(seconds))
    mins, secs = divmod(total, 60)
    hours, mins = divmod(mins, 60)
    return f"{hours:02d}:{mins:02d}:{secs:02d}" if hours else f"{mins:02d}:{secs:02d}"


class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title(f"{APP_NAME} {VERSION}")
        self.geometry("1050x760")
        self.minsize(900, 650)

        self.file: Path | None = None
        self.last_output: Path | None = None
        self.running = False
        self.stop_event = threading.Event()

        self.file_var = tk.StringVar(value="Není vybrán playlist")
        self.status = tk.StringVar(value="Připraveno")
        self.detail = tk.StringVar(value="Vyber playlist a spusť SMART FIX")
        self.progress = tk.DoubleVar(value=0)
        self.test_var = tk.BooleanVar(value=True)
        self.timeout = tk.IntVar(value=8)
        self.workers = tk.IntVar(value=15)
        self.autoscroll = tk.BooleanVar(value=True)

        self.stats = {
            "TOTAL": tk.StringVar(value="0"),
            "TESTED": tk.StringVar(value="0"),
            "OK": tk.StringVar(value="0"),
            "SLOW": tk.StringVar(value="0"),
            "TIMEOUT": tk.StringVar(value="0"),
            "AUTH_OR_GEO": tk.StringVar(value="0"),
            "NOT_FOUND": tk.StringVar(value="0"),
            "REMOVED": tk.StringVar(value="0"),
            "SPEED": tk.StringVar(value="0,00/s"),
            "ETA": tk.StringVar(value="00:00"),
        }

        self.configure_style()
        self.build_gui()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def configure_style(self) -> None:
        style = ttk.Style(self)
        try:
            style.theme_use("vista")
        except tk.TclError:
            pass

        style.configure("Title.TLabel", font=("Segoe UI", 22, "bold"))
        style.configure("StatTitle.TLabel", font=("Segoe UI", 9))
        style.configure("StatValue.TLabel", font=("Segoe UI", 16, "bold"))
        style.configure("Primary.TButton", font=("Segoe UI", 11, "bold"))
        style.configure("TProgressbar", thickness=18)

    def build_gui(self) -> None:
        header = ttk.Frame(self, padding=(24, 16, 24, 8))
        header.pack(fill="x")

        left = ttk.Frame(header)
        left.pack(side="left", fill="x", expand=True)
        ttk.Label(left, text=APP_NAME, style="Title.TLabel").pack(anchor="w")
        ttk.Label(left, text=f"Stabilní vývojová verze {VERSION}").pack(anchor="w")
        ttk.Label(header, text=f"v{VERSION}", font=("Segoe UI", 12, "bold")).pack(side="right", anchor="n")

        file_box = ttk.LabelFrame(self, text="Playlist", padding=12)
        file_box.pack(fill="x", padx=24, pady=(4, 10))
        ttk.Button(file_box, text="Vybrat playlist", command=self.choose).pack(side="left")
        ttk.Label(file_box, textvariable=self.file_var).pack(side="left", fill="x", expand=True, padx=12)

        options = ttk.LabelFrame(self, text="Nastavení kontroly", padding=12)
        options.pack(fill="x", padx=24, pady=(0, 10))
        ttk.Checkbutton(options, text="Testovat dostupnost streamů", variable=self.test_var).grid(row=0, column=0, padx=(0, 18))
        ttk.Label(options, text="Timeout:").grid(row=0, column=1)
        ttk.Spinbox(options, from_=3, to=30, width=6, textvariable=self.timeout).grid(row=0, column=2, padx=(5, 18))
        ttk.Label(options, text="Současné testy:").grid(row=0, column=3)
        ttk.Spinbox(options, from_=1, to=40, width=6, textvariable=self.workers).grid(row=0, column=4, padx=(5, 18))
        ttk.Checkbutton(options, text="Automaticky posouvat log", variable=self.autoscroll).grid(row=0, column=5)

        buttons = ttk.Frame(self)
        buttons.pack(fill="x", padx=24, pady=(0, 10))
        self.start_btn = ttk.Button(buttons, text="SMART FIX – SPUSTIT", command=self.start, style="Primary.TButton")
        self.start_btn.pack(side="left", ipadx=22, ipady=7)
        self.stop_btn = ttk.Button(buttons, text="ZASTAVIT", command=self.stop, state="disabled")
        self.stop_btn.pack(side="left", padx=8, ipadx=12, ipady=7)
        ttk.Button(buttons, text="Otevřít výstupní složku", command=self.open_output).pack(side="right")

        stats_box = ttk.LabelFrame(self, text="Živé výsledky", padding=10)
        stats_box.pack(fill="x", padx=24, pady=(0, 10))

        definitions = [
            ("Celkem", "TOTAL"), ("Testováno", "TESTED"), ("OK", "OK"),
            ("Pomalé", "SLOW"), ("Timeout", "TIMEOUT"), ("Auth / GEO", "AUTH_OR_GEO"),
            ("404", "NOT_FOUND"), ("Odstraněno", "REMOVED"), ("Rychlost", "SPEED"), ("ETA", "ETA"),
        ]

        for i, (label, key) in enumerate(definitions):
            frame = ttk.Frame(stats_box, padding=(7, 3))
            frame.grid(row=0, column=i, sticky="nsew")
            stats_box.columnconfigure(i, weight=1)
            ttk.Label(frame, text=label, style="StatTitle.TLabel").pack()
            ttk.Label(frame, textvariable=self.stats[key], style="StatValue.TLabel").pack()

        ttk.Progressbar(self, variable=self.progress, maximum=100).pack(fill="x", padx=24)

        status_row = ttk.Frame(self)
        status_row.pack(fill="x", padx=24, pady=(6, 10))
        ttk.Label(status_row, textvariable=self.status, font=("Segoe UI", 10, "bold")).pack(side="left")
        ttk.Label(status_row, textvariable=self.detail).pack(side="right")

        log_box = ttk.LabelFrame(self, text="Průběh kontroly", padding=8)
        log_box.pack(fill="both", expand=True, padx=24, pady=(0, 10))
        scroll = ttk.Scrollbar(log_box)
        scroll.pack(side="right", fill="y")
        self.log = tk.Text(log_box, state="disabled", wrap="word", yscrollcommand=scroll.set, font=("Consolas", 10), borderwidth=0)
        self.log.pack(fill="both", expand=True)
        scroll.config(command=self.log.yview)

        self.log.tag_configure("ok", foreground="#1f7a1f")
        self.log.tag_configure("slow", foreground="#a66a00")
        self.log.tag_configure("error", foreground="#b22222")
        self.log.tag_configure("info", foreground="#245a9a")
        self.log.tag_configure("title", font=("Consolas", 10, "bold"))

        footer = ttk.Frame(self, padding=(24, 0, 24, 10))
        footer.pack(fill="x")
        ttk.Label(footer, text=f"{APP_NAME} – Verze {VERSION} – © 2026 Luigis.cz").pack(side="left")
        ttk.Label(footer, text="Připraveno pro modul Playlist Maker").pack(side="right")

    def choose(self) -> None:
        p = filedialog.askopenfilename(
            filetypes=[("M3U playlist", "*.m3u *.m3u8"), ("Všechny soubory", "*.*")]
        )
        if p:
            self.file = Path(p)
            self.file_var.set(p)
            self.write(f"Vybrán: {p}", "info")

    def write(self, text: str, tag: str = "info") -> None:
        self.log.config(state="normal")
        self.log.insert("end", text + "\n", tag)
        if self.autoscroll.get():
            self.log.see("end")
        self.log.config(state="disabled")

    def clear_log(self) -> None:
        self.log.config(state="normal")
        self.log.delete("1.0", "end")
        self.log.config(state="disabled")

    def ui(self, func, *args) -> None:
        self.after(0, lambda: func(*args))

    def stop(self) -> None:
        if self.running:
            self.stop_event.set()
            self.status.set("Zastavuji…")
            self.write("Zastavuji po dokončení právě běžících testů…", "info")

    def start(self) -> None:
        if self.running:
            return
        if not self.file:
            messagebox.showwarning("Chybí playlist", "Nejprve vyber playlist.")
            return

        self.running = True
        self.stop_event.clear()
        self.clear_log()
        self.reset_stats()
        self.start_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        threading.Thread(target=self.process, daemon=True).start()

    def reset_stats(self) -> None:
        for key, var in self.stats.items():
            var.set("0,00/s" if key == "SPEED" else "00:00" if key == "ETA" else "0")
        self.progress.set(0)
        self.status.set("Připravuji kontrolu…")
        self.detail.set("Načítání playlistu")

    def update_stats(self, done: int, total: int, counts: Counter, removed: int, speed: float, eta: float) -> None:
        self.progress.set(done / total * 100 if total else 0)
        self.stats["TESTED"].set(str(done))
        self.stats["OK"].set(str(counts["OK"]))
        self.stats["SLOW"].set(str(counts["SLOW"]))
        self.stats["TIMEOUT"].set(str(counts["TIMEOUT"]))
        self.stats["AUTH_OR_GEO"].set(str(counts["AUTH_OR_GEO"]))
        self.stats["NOT_FOUND"].set(str(counts["NOT_FOUND"]))
        self.stats["REMOVED"].set(str(removed))
        self.stats["SPEED"].set(f"{speed:.2f}/s".replace(".", ","))
        self.stats["ETA"].set(fmt_time(eta))
        self.status.set(f"Testování: {done} z {total}")
        self.detail.set(f"Ponecháno: {counts['OK'] + counts['SLOW']}")

    def process(self) -> None:
        started_total = time.monotonic()

        try:
            assert self.file is not None

            stamp = datetime.now().strftime("%Y%m%d_%H-%M-%S")
            src = self.file
            out = src.parent / f"LUIGI_OUTPUT_{stamp}"
            out.mkdir(exist_ok=True)
            self.last_output = out

            backup = out / f"{src.stem}_backup_{stamp}{src.suffix}"
            shutil.copy2(src, backup)

            items = parse(src)
            unique, dups = dedupe(items)

            self.ui(self.stats["TOTAL"].set, str(len(items)))
            self.ui(self.write, f"Načteno: {len(items)} streamů", "title")
            self.ui(self.write, f"Záloha vytvořena: {backup.name}", "info")
            self.ui(self.write, f"Duplicity odstraněny: {len(dups)}", "info")

            results: list[tuple[Channel, str, str, float]] = []
            working: list[Channel] = []
            counts: Counter[str] = Counter()

            if self.test_var.get():
                ff = ffprobe_path()
                workers = max(1, min(40, self.workers.get()))
                timeout = max(3, self.timeout.get())
                self.ui(self.write, f"Metoda: {'ffprobe' if ff else 'HTTP'} | Současně: {workers} | Timeout: {timeout}s", "info")

                started = time.monotonic()
                with ThreadPoolExecutor(max_workers=workers) as ex:
                    futures = [ex.submit(test, c, timeout, ff, self.stop_event) for c in unique]

                    for i, future in enumerate(as_completed(futures), 1):
                        c, status, reason, elapsed = future.result()
                        results.append((c, status, reason, elapsed))
                        counts[status] += 1

                        if status in ("OK", "SLOW"):
                            working.append(c)

                        elapsed_all = max(0.01, time.monotonic() - started)
                        speed = i / elapsed_all
                        eta = (len(unique) - i) / speed if speed else 0

                        removed = sum(counts[x] for x in (
                            "TIMEOUT", "AUTH_OR_GEO", "NOT_FOUND",
                            "DNS_ERROR", "CONNECTION_REFUSED", "DEAD"
                        ))

                        self.ui(self.update_stats, i, len(unique), counts, removed, speed, eta)

                        symbol = {
                            "OK": "✔", "SLOW": "⚠", "TIMEOUT": "⏳",
                            "AUTH_OR_GEO": "🔒", "NOT_FOUND": "404",
                            "DNS_ERROR": "🌐", "CONNECTION_REFUSED": "🚫",
                            "DEAD": "✖", "STOPPED": "■"
                        }.get(status, "•")
                        label = {
                            "OK": "OK", "SLOW": "Pomalé", "TIMEOUT": "Timeout",
                            "AUTH_OR_GEO": "Auth/GEO", "NOT_FOUND": "404",
                            "DNS_ERROR": "DNS chyba", "CONNECTION_REFUSED": "Connection refused",
                            "DEAD": "Mrtvé", "STOPPED": "Přerušeno"
                        }.get(status, status)
                        tag = "ok" if status == "OK" else "slow" if status == "SLOW" else "info" if status == "STOPPED" else "error"
                        self.ui(self.write, f"{symbol} {c.name} | {label} | {reason}", tag)

                        if self.stop_event.is_set():
                            for pending in futures:
                                pending.cancel()
                            break
            else:
                working = unique
                self.ui(self.progress.set, 100)
                self.ui(self.stats["TESTED"].set, str(len(unique)))

            clean = out / f"{src.stem}_LUIGI_OK_{stamp}.m3u"
            save_m3u(clean, working)

            (out / f"{src.stem}_duplicates_{stamp}.txt").write_text(
                "\n\n".join(f"[{reason}] {c.name}\n{c.url}" for c, reason in dups),
                encoding="utf-8-sig",
            )

            (out / f"{src.stem}_working_{stamp}.txt").write_text(
                "\n\n".join(
                    f"[{status}] {c.name}\n{c.url}\n{reason}"
                    for c, status, reason, _ in results
                    if status in ("OK", "SLOW")
                ) if results else "\n\n".join(
                    f"[NOT_TESTED] {c.name}\n{c.url}" for c in working
                ),
                encoding="utf-8-sig",
            )

            (out / f"{src.stem}_removed_{stamp}.txt").write_text(
                "\n\n".join(
                    f"[{status}] {c.name}\n{c.url}\n{reason}"
                    for c, status, reason, _ in results
                    if status not in ("OK", "SLOW", "STOPPED")
                ),
                encoding="utf-8-sig",
            )

            duration = time.monotonic() - started_total
            removed_total = len(dups) + sum(counts[x] for x in (
                "TIMEOUT", "AUTH_OR_GEO", "NOT_FOUND",
                "DNS_ERROR", "CONNECTION_REFUSED", "DEAD"
            ))
            success = (len(working) / len(items) * 100) if items else 0

            summary = (
                f"{APP_NAME} {VERSION}\n"
                f"{'=' * 48}\n\n"
                f"Celkem načteno: {len(items)}\n"
                f"Duplicity: {len(dups)}\n"
                f"OK: {counts['OK']}\n"
                f"Pomalé: {counts['SLOW']}\n"
                f"Timeout: {counts['TIMEOUT']}\n"
                f"Autentizace nebo GEO: {counts['AUTH_OR_GEO']}\n"
                f"404: {counts['NOT_FOUND']}\n"
                f"DNS chyba: {counts['DNS_ERROR']}\n"
                f"Connection refused: {counts['CONNECTION_REFUSED']}\n"
                f"Mrtvé ostatní: {counts['DEAD']}\n"
                f"Ponecháno: {len(working)}\n"
                f"Odstraněno celkem: {removed_total}\n"
                f"Úspěšnost: {success:.2f} %\n"
                f"Doba: {fmt_time(duration)}\n"
                f"Výstup: {clean}\n"
            )
            (out / "summary.txt").write_text(summary, encoding="utf-8-sig")

            self.ui(self.progress.set, 100)
            self.ui(self.status.set, "Dokončeno")
            self.ui(self.detail.set, f"Ponecháno: {len(working)} | Odstraněno: {removed_total}")
            self.ui(self.write, f"Výstup: {clean.name}", "title")
            self.ui(
                messagebox.showinfo,
                "Kontrola dokončena",
                f"Celkem: {len(items)}\n"
                f"Funkční: {counts['OK']}\n"
                f"Pomalé: {counts['SLOW']}\n"
                f"Odstraněno: {removed_total}\n"
                f"Úspěšnost: {success:.2f} %\n"
                f"Doba: {fmt_time(duration)}\n\n"
                f"Výsledky:\n{out}",
            )

        except Exception as exc:
            self.ui(messagebox.showerror, "Chyba", str(exc))
            self.ui(self.write, f"CHYBA: {exc}", "error")
            self.ui(self.status.set, "Chyba")
        finally:
            self.running = False
            self.ui(self.start_btn.config, state="normal")
            self.ui(self.stop_btn.config, state="disabled")

    def open_output(self) -> None:
        if not self.last_output or not self.last_output.exists():
            messagebox.showinfo("Výstupní složka", "Zatím nebyla vytvořena žádná výstupní složka.")
            return
        os.startfile(self.last_output)

    def on_close(self) -> None:
        if self.running:
            if not messagebox.askyesno("Ukončit program", "Kontrola stále běží. Opravdu ukončit program?"):
                return
            self.stop_event.set()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()

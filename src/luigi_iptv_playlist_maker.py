from __future__ import annotations

import logging
import os
import re
import shutil
import subprocess
import sys
import threading
import time
import unicodedata
import json
import urllib.error
import urllib.parse
import urllib.request
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass
from datetime import datetime
from pathlib import Path
from typing import Protocol
import tkinter as tk
import tkinter.font as tkfont
from tkinter import filedialog, messagebox, simpledialog, ttk

APP_NAME = "LUIGI IPTV PLAYLIST MAKER"
VERSION = "0.4.0"

# Placeholder URL for temporarily unavailable channels (information stream placeholder).
UNAVAILABLE_STREAM_URL = ""

# ---------------------------------------------------------------------------
# Logging
# ---------------------------------------------------------------------------

if getattr(sys, "frozen", False):
    _BASE_DIR = Path(sys.executable).parent
else:
    _BASE_DIR = Path(__file__).resolve().parent.parent

_LOG_DIR = _BASE_DIR / "logs"
_REPLACEMENT_SOURCES_DIR = _BASE_DIR / "replacement_sources"
_OUTPUT_DIR = _BASE_DIR / "output"
_SOURCES_CONFIG_PATH = _BASE_DIR / "playlist_sources.json"
_WINDOW_STATE_PATH = _BASE_DIR / "window_state.json"

# Statuses that classify a tested stream as non-working and subject to removal.
_DEAD_STATUSES: frozenset[str] = frozenset({
    "TIMEOUT", "AUTH_REQUIRED", "GEO_BLOCKED", "HTTP_404",
    "DNS_ERROR", "CONNECTION_REFUSED", "OTHER_ERROR",
})

# Unicode categories stripped from names during comparison (never from display names).
_STRIP_CATEGORIES: frozenset[str] = frozenset({"Cf", "Cc"})

# Explicit decorative symbols stripped during comparison only.
# Only characters that carry no channel-identity meaning are listed here.
_DECORATIVE_CHARS: frozenset[str] = frozenset("★☆•●◆◇■□▶▸")


# ---------------------------------------------------------------------------
# Replacement architecture
# ---------------------------------------------------------------------------

def parse_extinf_attrs(extinf: str) -> dict[str, str]:
    """Extract key=\"value\" attributes from an #EXTINF line.

    Returns a dict with keys such as 'tvg-id', 'tvg-name', 'group-title'.
    Returns an empty dict for empty or malformed input.
    """
    return dict(re.findall(r'([\w-]+)\s*=\s*"([^"]*)"', extinf))


@dataclass
class ReplacementResult:
    """Records one successful dead-stream replacement event."""

    original: Channel           # the dead channel
    replacement: Channel        # the substitute channel
    match_type: str             # "tvg-id" | "name" | "name+group"
    provider_name: str          # which provider supplied the replacement
    dead_status: str            # e.g. "TIMEOUT", "DEAD" — why the original failed
    source_filename: str        # source M3U filename
    test_status: str            # "OK" or "SLOW" — replacement test result


class ReplacementProvider(Protocol):
    """Interface contract for all replacement source providers.

    Any class that implements `name` and `find()` with the correct
    signatures is automatically a valid provider (structural subtyping).
    """

    name: str

    def find(
        self,
        dead: Channel,
        working_urls: frozenset[str],
    ) -> tuple[Channel, str] | None:
        """Return (replacement_channel, match_type) or None.

        Matching priority:
          1. tvg-id      — exact attribute match (casefolded)
          2. name        — normalize_name() match
          3. name+group  — normalize_name() AND group-title both match

        A valid candidate must:
          - have a non-empty URL
          - not use a URL already present in working_urls
          - not use the same URL as the dead channel
          - preserve its own original EXTINF metadata unchanged
        """
        ...


class LocalFileProvider:
    """Loads replacement candidates from all *.m3u / *.m3u8 files in source_dir,
    builds three lookup indexes, and live-tests each candidate before accepting it.

    Matching priority (group-title alone is never sufficient):
      1. tvg-id      — exact attribute match (casefolded)
      2. name        — normalize_name() match
      3. name+group  — normalize_name() AND group-title both match
    """

    name: str = "LocalFile"

    def __init__(
        self,
        source_dir: Path | None = None,
        timeout: int = 8,
        ffprobe: str | None = None,
        stop_event: threading.Event | None = None,
    ) -> None:
        self._timeout = timeout
        self._ffprobe = ffprobe
        self._stop_event = stop_event if stop_event is not None else threading.Event()
        self._test_cache:    dict[str, str]                  = {}  # norm_url → status
        self._used_urls:     set[str]                        = set()  # norm_urls already used
        self._channel_source: dict[str, str]                 = {}  # norm_url → filename
        self._by_tvg_id:     dict[str, list[Channel]]        = {}
        self._by_name:       dict[str, list[Channel]]        = {}
        self._by_name_group: dict[tuple[str, str], list[Channel]] = {}

        if source_dir is not None:
            self._load(source_dir)

    def _load(self, source_dir: Path) -> None:
        """Create source_dir if absent, then index every *.m3u and *.m3u8 file."""
        try:
            source_dir.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            logger.error("LocalFileProvider: Nelze vytvořit '%s': %s", source_dir, exc)
            return

        files = list(source_dir.glob("*.m3u")) + list(source_dir.glob("*.m3u8"))
        if not files:
            logger.info("LocalFileProvider: Žádné zdrojové soubory v '%s'", source_dir)
            return

        for path in files:
            try:
                channels = parse(path)
                for c in channels:
                    attrs = parse_extinf_attrs(c.extinf)
                    norm = normalize_url(c.url)
                    self._channel_source[norm] = path.name

                    tvg_id = attrs.get("tvg-id", "").strip().casefold()
                    if tvg_id:
                        self._by_tvg_id.setdefault(tvg_id, []).append(c)

                    norm_name = normalize_name(c.name)
                    if norm_name:
                        self._by_name.setdefault(norm_name, []).append(c)

                    group = attrs.get("group-title", "").strip().casefold()
                    if norm_name and group:
                        self._by_name_group.setdefault((norm_name, group), []).append(c)

                logger.info(
                    "LocalFileProvider: Načteno %d kanálů z '%s'", len(channels), path.name
                )
            except Exception as exc:
                logger.error(
                    "LocalFileProvider: Chyba při čtení '%s': %s", path.name, exc
                )

    def _test_url(self, c: Channel) -> str:
        """Return the test status for a candidate URL, using a cache to avoid retesting."""
        key = normalize_url(c.url)
        if key not in self._test_cache:
            _, status, _, _ = test(c, self._timeout, self._ffprobe, self._stop_event)
            self._test_cache[key] = status
        return self._test_cache[key]

    def _detect_resolution(self, c: Channel) -> int:
        """Extract resolution from EXTINF or channel name. Higher is better.

        Returns: 2160 (4K), 1080, 720, 480, 360, or 0 (unknown).
        """
        text = (c.extinf + " " + c.name).casefold()
        if "2160" in text or "4k" in text:
            return 2160
        if "1080" in text:
            return 1080
        if "720" in text:
            return 720
        if "480" in text:
            return 480
        if "360" in text:
            return 360
        return 0

    def _rank_candidates(
        self,
        candidates: list[Channel],
        dead: Channel,
        working_urls: frozenset[str],
        match_type: str,
    ) -> tuple[Channel, str, str, str] | None:
        """Evaluate all valid candidates and return the best ranked one.

        Returns: (channel, match_type, source_filename, test_status) or None.

        Ranking within the same match type:
          1. OK before SLOW
                    1b. SLOW before REDIRECT
          2. HTTPS before HTTP
          3. higher resolution before lower
          4. preserve source order for ties
        """
        dead_norm = normalize_url(dead.url)
        valid_with_status: list[tuple[Channel, str, str]] = []

        for candidate in candidates:
            if not candidate.url:
                continue
            norm = normalize_url(candidate.url)
            if norm == dead_norm:
                continue
            if norm in working_urls:
                continue
            if norm in self._used_urls:
                continue

            status = self._test_url(candidate)
            if status not in ("OK", "SLOW", "REDIRECT"):
                logger.debug(
                    "LocalFileProvider: Kandidát zamítnut '%s' | test=%s",
                    candidate.name, status,
                )
                continue

            source = self._channel_source.get(norm, "?")
            valid_with_status.append((candidate, status, source))

        if not valid_with_status:
            return None

        # Sort by ranking criteria
        def rank_key(item: tuple[Channel, str, str]) -> tuple:
            candidate, status, _ = item
            status_rank = 0 if status == "OK" else 1 if status == "SLOW" else 2
            https_rank = 0 if candidate.url.startswith("https://") else 1
            resolution = -self._detect_resolution(candidate)  # negative for reverse sort
            return (status_rank, https_rank, resolution)

        best = min(valid_with_status, key=rank_key)
        best_channel, best_status, best_source = best
        self._used_urls.add(normalize_url(best_channel.url))
        logger.info(
            "LocalFileProvider [%s]: '%s' → '%s' | test=%s | zdroj=%s",
            match_type, dead.name, best_channel.name, best_status, best_source,
        )
        return best_channel, match_type, best_source, best_status

    def find(
        self,
        dead: Channel,
        working_urls: frozenset[str],
    ) -> tuple[Channel, str, str, str] | None:
        """Return (replacement, match_type, source_filename, test_status) or None."""
        attrs = parse_extinf_attrs(dead.extinf)

        # Priority 1: tvg-id
        tvg_id = attrs.get("tvg-id", "").strip().casefold()
        if tvg_id:
            result = self._rank_candidates(
                self._by_tvg_id.get(tvg_id, []), dead, working_urls, "tvg-id"
            )
            if result:
                return result

        # Priority 2: normalized name + group-title (name+group)
        norm_name = normalize_name(dead.name)
        group = attrs.get("group-title", "").strip().casefold()
        if norm_name and group:
            result = self._rank_candidates(
                self._by_name_group.get((norm_name, group), []), dead, working_urls, "name+group"
            )
            if result:
                return result

        # Priority 3: normalized name only
        if norm_name:
            result = self._rank_candidates(
                self._by_name.get(norm_name, []), dead, working_urls, "name"
            )
            if result:
                return result

        return None


class ReplacementService:
    """Iterates registered providers in order and returns the first match found.

    To add a new provider, append it to the list passed to __init__.
    """

    def __init__(self, providers: list) -> None:
        self._providers = providers

    def find(
        self,
        dead: Channel,
        working_urls: frozenset[str],
    ) -> tuple[Channel, str, str, str] | None:
        """Return (replacement, match_type, provider_name, unused) or None.

        LocalFileProvider returns 4 elements to transport source filename
        and test status; see process() where these are extracted and used.
        """
        for provider in self._providers:
            result = provider.find(dead, working_urls)
            if result is not None:
                # Expect LocalFileProvider to return 4-tuple:
                # (replacement_channel, match_type, source_filename, test_status)
                if len(result) == 4:
                    replacement, match_type, source_filename, test_status = result
                    return replacement, match_type, provider.name, (source_filename, test_status)
                # Legacy 2-tuple support (for other providers)
                else:
                    replacement, match_type = result
                    return replacement, match_type, provider.name, None


def setup_logging() -> None:
    """Configure base logging without creating extra run log files."""
    logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")


def enable_windows_dpi_awareness() -> None:
    """Enable process DPI awareness on Windows before Tk root creation."""
    if os.name != "nt":
        return

    try:
        import ctypes

        user32 = ctypes.windll.user32
        shcore = ctypes.windll.shcore

        # Windows 10+ per-monitor v2 awareness.
        try:
            DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2 = ctypes.c_void_p(-4)
            if user32.SetProcessDpiAwarenessContext(DPI_AWARENESS_CONTEXT_PER_MONITOR_AWARE_V2):
                return
        except Exception:
            pass

        # Windows 8.1 per-monitor awareness.
        try:
            if shcore.SetProcessDpiAwareness(2) == 0:
                return
        except Exception:
            pass

        # Legacy system DPI awareness.
        try:
            user32.SetProcessDPIAware()
        except Exception:
            pass
    except Exception as exc:
        logger.debug("DPI awareness setup skipped: %s", exc)


logger = logging.getLogger(__name__)


@dataclass
class Channel:
    extinf: str
    url: str
    name: str


def read_text(path: Path) -> str:
    """Read a text file trying common encodings. Raises OSError on I/O failure."""
    try:
        for enc in ("utf-8-sig", "utf-8", "cp1250", "iso-8859-2", "latin-1"):
            try:
                text = path.read_text(encoding=enc)
                logger.info("FILE_OK: Načteno '%s' s kódováním %s", path.name, enc)
                return text
            except UnicodeDecodeError:
                pass
        return path.read_text(encoding="utf-8", errors="replace")
    except OSError as exc:
        logger.error("FILE_ERROR: Nelze číst '%s': %s", path, exc)
        raise


def parse(path: Path) -> list[Channel]:
    """Parse an M3U/M3U8 file into a list of Channel entries."""
    out: list[Channel] = []
    ext = ""
    for raw in read_text(path).splitlines():
        s = raw.strip()
        if not s:
            continue
        if s.startswith("#EXTINF"):
            if ext:
                logger.warning("INVALID_ENTRY: #EXTINF bez URL – přeskočeno: '%s'", ext[:80])
            ext = s
        elif s.startswith("#"):
            continue
        elif "://" in s:
            name = ext.rsplit(",", 1)[-1].strip() if "," in ext else s
            out.append(Channel(ext or f"#EXTINF:-1,{name}", s, name))
            ext = ""
    if ext:
        logger.warning("INVALID_ENTRY: #EXTINF na konci souboru bez URL: '%s'", ext[:80])
    return out


def normalize_name(name: str) -> str:
    """Return a normalized channel name used only for duplicate comparison.

    The original Channel.name is never modified; this result is used only
    for set-membership checks inside dedupe().
    """
    s = unicodedata.normalize("NFKC", name)
    # Accent-insensitive comparison only (display names remain unchanged).
    s = "".join(ch for ch in unicodedata.normalize("NFKD", s) if not unicodedata.combining(ch))
    # Remove invisible control/format characters and explicit decorative symbols.
    s = "".join(
        ch for ch in s
        if unicodedata.category(ch) not in _STRIP_CATEGORIES and ch not in _DECORATIVE_CHARS
    )
    s = re.sub(r"\s+", " ", s).strip().casefold()
    # Strip common quality suffixes so e.g. "CNN HD" and "CNN" deduplicate.
    s = re.sub(r"\b(hd|fhd|uhd|4k|sd|hevc|h265|h264)\b", "", s)
    return re.sub(r"\s+", " ", s).strip()


def normalize_url(url: str) -> str:
    """Return a normalized URL used only for duplicate comparison."""
    return url.casefold().strip().rstrip("/")


def dedupe(items: list[Channel]) -> tuple[list[Channel], list[tuple[Channel, str]]]:
    keep: list[Channel] = []
    removed: list[tuple[Channel, str]] = []
    seen_urls: set[str] = set()
    seen_names: set[str] = set()

    for c in items:
        norm_url = normalize_url(c.url)
        norm_name = normalize_name(c.name)

        if norm_url in seen_urls:
            removed.append((c, "DUPLICATE_URL"))
            logger.debug("DUPLICATE_URL: '%s' | %s", c.name, c.url)
            continue
        if norm_name and norm_name in seen_names:
            removed.append((c, "DUPLICATE_NAME"))
            logger.debug("DUPLICATE_NAME: '%s' | %s", c.name, c.url)
            continue

        seen_urls.add(norm_url)
        if norm_name:
            seen_names.add(norm_name)
        keep.append(c)

    return keep, removed


def ffprobe_path() -> str | None:
    candidates = [
        shutil.which("ffprobe"),
        r"C:\ffmpeg-8.1.2-essentials_build\bin\ffprobe.exe",
        str(Path(os.environ.get("LOCALAPPDATA", "")) / "ffmpeg" / "bin" / "ffprobe.exe"),
        str(Path(os.environ.get("ProgramFiles", "")) / "ffmpeg" / "bin" / "ffprobe.exe"),
        str(Path(os.environ.get("ProgramFiles(x86)", "")) / "ffmpeg" / "bin" / "ffprobe.exe"),
        str(Path.cwd() / "ffprobe.exe"),
    ]
    for p in candidates:
        if p and Path(p).is_file():
            return p
    return None


def classify(text: str) -> str:
    t = text.casefold()
    if any(x in t for x in ("401", "unauthorized", "authentication required")):
        return "AUTH_REQUIRED"
    if any(x in t for x in ("geo", "geoblock", "geo-block", "region", "country is not supported")):
        return "GEO_BLOCKED"
    if any(x in t for x in ("403", "forbidden")):
        return "AUTH_REQUIRED"
    if "404" in t or "not found" in t:
        return "HTTP_404"
    if "timeout" in t or "timed out" in t:
        return "TIMEOUT"
    if any(x in t for x in ("resolve", "no such host", "name or service not known")):
        return "DNS_ERROR"
    if "connection refused" in t:
        return "CONNECTION_REFUSED"
    return "OTHER_ERROR"


def test(
    c: Channel,
    timeout: int,
    ffprobe: str | None,
    stop: threading.Event,
) -> tuple[Channel, str, str, float]:
    start = time.monotonic()

    if stop.is_set():
        return c, "STOPPED", "Přerušeno", 0.0

    def _http_check(method: str) -> tuple[str, str, float]:
        req = urllib.request.Request(c.url, headers={"User-Agent": "Mozilla/5.0"}, method=method)
        with urllib.request.urlopen(req, timeout=timeout) as r:
            if method == "GET":
                r.read(256)
            elapsed_local = time.monotonic() - start
            final_url = getattr(r, "geturl", lambda: c.url)()
            status_code = int(getattr(r, "status", 200))

            if final_url and normalize_url(final_url) != normalize_url(c.url):
                return "REDIRECT", f"HTTP {status_code} -> {final_url}", elapsed_local
            return ("SLOW" if elapsed_local >= timeout * 0.75 else "OK"), f"HTTP {status_code}", elapsed_local

    # Primary method: HTTP HEAD. Fallback to GET when HEAD is unsupported.
    try:
        status, reason, elapsed = _http_check("HEAD")
        return c, status, reason, elapsed
    except urllib.error.HTTPError as ex:
        if ex.code in (405, 501):
            try:
                status, reason, elapsed = _http_check("GET")
                return c, status, reason, elapsed
            except urllib.error.HTTPError as ex_get:
                return c, classify(str(ex_get)), str(ex_get)[:240], time.monotonic() - start
            except urllib.error.URLError as ex_get:
                reason = str(ex_get.reason) if hasattr(ex_get, "reason") else str(ex_get)
                return c, classify(reason), reason[:240], time.monotonic() - start
            except Exception as ex_get:
                return c, classify(str(ex_get)), str(ex_get)[:240], time.monotonic() - start
        return c, classify(str(ex)), str(ex)[:240], time.monotonic() - start
    except urllib.error.URLError as ex:
        reason = str(ex.reason) if hasattr(ex, "reason") else str(ex)
        logger.debug("HTTP URLError for %s: %s", c.url, reason)
        # Keep ffprobe path as optional fallback for compatibility.
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
                    return c, ("SLOW" if elapsed >= timeout * 0.75 else "OK"), f"ffprobe {elapsed:.1f}s", elapsed
                ff_reason = (r.stderr or "ffprobe error").strip().splitlines()[-1][:240]
                return c, classify(ff_reason), ff_reason, elapsed
            except subprocess.TimeoutExpired:
                return c, "TIMEOUT", f"Timeout {timeout}s", time.monotonic() - start
            except Exception as ex_ff:
                return c, classify(str(ex_ff)), str(ex_ff)[:240], time.monotonic() - start
        return c, classify(reason), reason[:240], time.monotonic() - start
    except Exception as ex:
        logger.debug("HTTP error for %s: %s", c.url, ex)
        return c, classify(str(ex)), str(ex)[:240], time.monotonic() - start


def save_m3u(path: Path, items: list[Channel]) -> None:
    """Write channels to an M3U file. Raises OSError on write failure."""
    try:
        lines = ["#EXTM3U"]
        for c in items:
            lines += [c.extinf, c.url]
        path.write_text("\n".join(lines) + "\n", encoding="utf-8-sig")
        logger.info("FILE_OK: Uloženo %d streamů → %s", len(items), path.name)
    except OSError as exc:
        logger.error("FILE_ERROR: Nelze zapsat '%s': %s", path, exc)
        raise


def fmt_time(seconds: float) -> str:
    total = max(0, int(seconds))
    mins, secs = divmod(total, 60)
    hours, mins = divmod(mins, 60)
    return f"{hours:02d}:{mins:02d}:{secs:02d}" if hours else f"{mins:02d}:{secs:02d}"


class App(tk.Tk):
    def __init__(self) -> None:
        super().__init__()
        self.title(f"{APP_NAME} {VERSION}")
        self.minsize(620, 480)

        self.file: Path | None = None
        self.last_output: Path | None = None
        self.last_protocol: Path | None = None
        self.final_playlist: Path | None = None
        self.final_channels: int = 0
        self.running = False
        self.stop_event = threading.Event()
        self.stopped_by_user = False
        self.run_mode: str = "single"
        self.sources: list[dict[str, str | bool]] = []

        self.file_var = tk.StringVar(value="Není vybrán playlist")
        self.status = tk.StringVar(value="Připraveno")
        self.detail = tk.StringVar(value="Vyber playlist a spusť SMART FIX")
        self.status_display = tk.StringVar(value="Připraveno")
        self.detail_display = tk.StringVar(value="Vyber playlist a spusť SMART FIX")
        self.progress = tk.DoubleVar(value=0)
        self.test_var = tk.BooleanVar(value=True)
        self.timeout = tk.IntVar(value=8)
        self.workers = tk.IntVar(value=15)
        self.autoscroll = tk.BooleanVar(value=True)
        self.final_path_var = tk.StringVar(value="-")
        self.final_name_var = tk.StringVar(value="-")
        self.final_count_var = tk.StringVar(value="0")
        self.channel_search_var = tk.StringVar(value="")
        self.channel_group_filter_var = tk.StringVar(value="Vše")
        self.channel_source_filter_var = tk.StringVar(value="Vše")
        self.loaded_channels_var = tk.StringVar(value="0")
        self.selected_channels_var = tk.StringVar(value="0")
        self.disabled_channels_var = tk.StringVar(value="0")
        self.selected_sources_var = tk.StringVar(value="0")

        self.channel_rows: list[dict[str, object]] = []
        self.channel_mode: str = "batch"
        self.channel_preview_error: str = ""
        self._channel_groups: list[str] = []
        self._channel_sources: list[str] = []
        self._selected_channel_id: str | None = None

        self.channel_center_name_var = tk.StringVar(value="-")
        self.channel_center_group_var = tk.StringVar(value="-")
        self.channel_center_country_var = tk.StringVar(value="-")
        self.channel_center_url_var = tk.StringVar(value="-")
        self.channel_center_state_var = tk.StringVar(value="⚫ Netestováno")
        self.channel_center_recommendation_var = tk.StringVar(value="Kanál nebyl dosud otestován.")
        self.channel_center_last_test_var = tk.StringVar(value="-")
        self.channel_center_last_reason_var = tk.StringVar(value="-")

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
        self.load_sources()
        self.refresh_sources_table()
        self.refresh_channel_selection("batch")
        self._apply_start_geometry()
        self.status.trace_add("write", self._on_status_text_changed)
        self.detail.trace_add("write", self._on_status_text_changed)
        self._refresh_statusbar_text()
        self.protocol("WM_DELETE_WINDOW", self.on_close)

    def configure_style(self) -> None:
        style = ttk.Style(self)
        try:
            style.theme_use("vista")
        except tk.TclError:
            pass
        self._ttk_theme_name = style.theme_use()

        default_font = tkfont.nametofont("TkDefaultFont")
        base_size = abs(int(default_font.cget("size")))

        title_font = default_font.copy()
        title_font.configure(size=base_size + 2, weight="bold")

        stat_value_font = default_font.copy()
        stat_value_font.configure(weight="bold")

        style.configure("Title.TLabel", font=title_font)
        style.configure("StatTitle.TLabel")
        style.configure("StatValue.TLabel", font=stat_value_font)
        style.configure("TNotebook.Tab", padding=(8, 4))
        style.configure("TProgressbar", thickness=12)

    def _get_work_area(self) -> tuple[int, int, int, int]:
        """Return usable desktop work area (x, y, width, height)."""
        if os.name == "nt":
            try:
                import ctypes

                class RECT(ctypes.Structure):
                    _fields_ = [("left", ctypes.c_long), ("top", ctypes.c_long), ("right", ctypes.c_long), ("bottom", ctypes.c_long)]

                SPI_GETWORKAREA = 0x0030
                rect = RECT()
                if ctypes.windll.user32.SystemParametersInfoW(SPI_GETWORKAREA, 0, ctypes.byref(rect), 0):
                    return rect.left, rect.top, rect.right - rect.left, rect.bottom - rect.top
            except Exception:
                pass

        return 0, 0, self.winfo_screenwidth(), self.winfo_screenheight()

    def _parse_geometry(self, geometry: str) -> tuple[int, int, int, int] | None:
        m = re.match(r"^(\d+)x(\d+)\+(-?\d+)\+(-?\d+)$", geometry.strip())
        if not m:
            return None
        return int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4))

    def _geometry_is_on_screen(self, geometry: str) -> bool:
        parsed = self._parse_geometry(geometry)
        if parsed is None:
            return False
        w, h, x, y = parsed
        wx, wy, ww, wh = self._get_work_area()
        if w < 620 or h < 480:
            return False
        if x + 80 > wx + ww or y + 80 > wy + wh:
            return False
        if x + w < wx + 80 or y + h < wy + 80:
            return False
        return True

    def _save_window_geometry(self) -> None:
        try:
            if self.state() != "normal":
                return
        except tk.TclError:
            return

        geom = self.geometry()
        if not self._geometry_is_on_screen(geom):
            return

        try:
            payload = {"normal_geometry": geom}
            _WINDOW_STATE_PATH.write_text(json.dumps(payload, ensure_ascii=False, indent=2), encoding="utf-8")
        except OSError as exc:
            logger.debug("WINDOW_STATE_SAVE_FAILED: %s", exc)

    def _apply_start_geometry(self) -> None:
        """Start in a centered normal window (~70%x75%) or restore saved normal geometry."""
        try:
            if _WINDOW_STATE_PATH.exists():
                data = json.loads(_WINDOW_STATE_PATH.read_text(encoding="utf-8"))
                if isinstance(data, dict):
                    saved = str(data.get("normal_geometry", "")).strip()
                    if saved and self._geometry_is_on_screen(saved):
                        self.geometry(saved)
                        return
        except Exception as exc:
            logger.debug("WINDOW_STATE_RESTORE_FAILED: %s", exc)

        x, y, w, h = self._get_work_area()
        tw = min(w, max(620, int(w * 0.70)))
        th = min(h, max(480, int(h * 0.75)))
        tx = x + max(0, (w - tw) // 2)
        ty = y + max(0, (h - th) // 2)
        self.geometry(f"{tw}x{th}+{tx}+{ty}")

    def _ellipsize_for_label(self, text: str, label: ttk.Label) -> str:
        try:
            max_px = max(40, label.winfo_width() - 6)
            font_name = str(label.cget("font"))
            fnt = tkfont.nametofont(font_name)
            if fnt.measure(text) <= max_px:
                return text
            ell = "..."
            lo, hi = 0, len(text)
            while lo < hi:
                mid = (lo + hi + 1) // 2
                candidate = text[:mid] + ell
                if fnt.measure(candidate) <= max_px:
                    lo = mid
                else:
                    hi = mid - 1
            return text[:lo] + ell
        except Exception:
            return text

    def _on_status_text_changed(self, *_args) -> None:
        self._refresh_statusbar_text()

    def _refresh_statusbar_text(self) -> None:
        if not hasattr(self, "status_label") or not hasattr(self, "detail_label"):
            return
        self.update_idletasks()
        self.status_display.set(self._ellipsize_for_label(self.status.get(), self.status_label))
        self.detail_display.set(self._ellipsize_for_label(self.detail.get(), self.detail_label))

    def build_gui(self) -> None:
        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(0, weight=1)
        use_tk_primary_buttons = getattr(self, "_ttk_theme_name", "") in {"vista", "xpnative"}
        primary_button_font = ("Segoe UI", 9, "bold")

        root_wrap = ttk.Frame(self, padding=6)
        root_wrap.grid(row=0, column=0, sticky="nsew")
        root_wrap.grid_columnconfigure(0, weight=1)
        root_wrap.grid_rowconfigure(1, weight=1)
        root_wrap.grid_rowconfigure(2, weight=0)

        header = ttk.Frame(root_wrap, padding=(4, 2))
        header.grid(row=0, column=0, sticky="ew")
        header.columnconfigure(0, weight=1)

        left = ttk.Frame(header)
        left.grid(row=0, column=0, sticky="ew")
        ttk.Label(left, text=APP_NAME, style="Title.TLabel").pack(anchor="w")
        ttk.Label(left, text=f"Stabilní vývojová verze {VERSION}").pack(anchor="w")
        ttk.Label(header, text=f"v{VERSION}").grid(row=0, column=1, sticky="ne")

        self.tabs = ttk.Notebook(root_wrap)
        self.tabs.grid(row=1, column=0, sticky="nsew", pady=(4, 0))

        tab1 = ttk.Frame(self.tabs, padding=6)
        tab2 = ttk.Frame(self.tabs, padding=6)
        tab3 = ttk.Frame(self.tabs, padding=6)
        tab4 = ttk.Frame(self.tabs, padding=6)
        self.tabs.add(tab1, text="1. Zdroj a kanály")
        self.tabs.add(tab2, text="2. SMART FIX")
        self.tabs.add(tab3, text="3. Výsledek")
        self.tabs.add(tab4, text="4. Protokol")

        for tab in (tab1, tab2, tab3, tab4):
            tab.grid_columnconfigure(0, weight=1)

        tab1.grid_rowconfigure(1, weight=1)
        tab2.grid_rowconfigure(3, weight=1)
        tab4.grid_rowconfigure(1, weight=1)

        file_box = ttk.LabelFrame(tab1, text="Playlist", padding=6)
        file_box.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        file_box.columnconfigure(1, weight=1)
        if use_tk_primary_buttons:
            self.choose_btn = tk.Button(file_box, text="Vybrat playlist", command=self.choose, font=primary_button_font)
        else:
            self.choose_btn = ttk.Button(file_box, text="Vybrat playlist", command=self.choose)
        self.choose_btn.grid(row=0, column=0, sticky="w")
        ttk.Label(file_box, textvariable=self.file_var).grid(row=0, column=1, sticky="ew", padx=(6, 0))

        self.sources_channels_paned = ttk.Panedwindow(tab1, orient="vertical")
        self.sources_channels_paned.grid(row=1, column=0, sticky="nsew")

        sources_box = ttk.LabelFrame(self.sources_channels_paned, text="Playlist Sources", padding=6)
        sources_box.columnconfigure(0, weight=1)
        cols = ("enabled", "name", "type", "location", "last_update", "status")

        sources_table_wrap = ttk.Frame(sources_box)
        sources_table_wrap.grid(row=0, column=0, sticky="ew")
        sources_table_wrap.columnconfigure(0, weight=1)
        sources_table_wrap.rowconfigure(0, weight=1)

        self.sources_table = ttk.Treeview(sources_table_wrap, columns=cols, show="headings", height=4)
        self.sources_table.heading("enabled", text="Enabled")
        self.sources_table.heading("name", text="Name")
        self.sources_table.heading("type", text="Type (Local / URL)")
        self.sources_table.heading("location", text="Location")
        self.sources_table.heading("last_update", text="Last Update")
        self.sources_table.heading("status", text="Status")
        self.sources_table.column("enabled", width=70, anchor="center", stretch=False)
        self.sources_table.column("name", width=140, anchor="w", stretch=True)
        self.sources_table.column("type", width=100, anchor="center", stretch=False)
        self.sources_table.column("location", width=220, anchor="w", stretch=True)
        self.sources_table.column("last_update", width=120, anchor="center", stretch=False)
        self.sources_table.column("status", width=120, anchor="center", stretch=False)

        sources_vscroll = ttk.Scrollbar(sources_table_wrap, orient="vertical", command=self.sources_table.yview)
        self.sources_table.configure(yscrollcommand=sources_vscroll.set)

        self.sources_table.grid(row=0, column=0, sticky="ew")
        sources_vscroll.grid(row=0, column=1, sticky="ns")

        self.src_btns = ttk.Frame(sources_box)
        self.src_btns.grid(row=1, column=0, sticky="ew", pady=(4, 0))
        self.src_btn_add_local = ttk.Button(self.src_btns, text="Přidat", command=self.add_local_source)
        self.src_btn_add_url = ttk.Button(self.src_btns, text="Přidat URL", command=self.add_url_source)
        self.src_btn_remove = ttk.Button(self.src_btns, text="Odebrat", command=self.remove_source)
        self.src_btn_toggle = ttk.Button(self.src_btns, text="Zapnout / vypnout", command=self.toggle_source)
        self.src_btn_up = ttk.Button(self.src_btns, text="Move Up", command=self.move_source_up)
        self.src_btn_down = ttk.Button(self.src_btns, text="Move Down", command=self.move_source_down)
        self.src_btn_open = ttk.Button(self.src_btns, text="Open Sources Folder", command=self.open_sources_folder)
        self.src_more_btn = ttk.Menubutton(self.src_btns, text="Další...")
        self.src_more_menu = tk.Menu(self.src_more_btn, tearoff=False)
        self.src_more_menu.add_command(label="Přidat URL", command=self.add_url_source)
        self.src_more_menu.add_separator()
        self.src_more_menu.add_command(label="Posunout nahoru", command=self.move_source_up)
        self.src_more_menu.add_command(label="Posunout dolů", command=self.move_source_down)
        self.src_more_menu.add_separator()
        self.src_more_menu.add_command(label="Otevřít složku zdrojů", command=self.open_sources_folder)
        self.src_more_btn.configure(menu=self.src_more_menu)
        self._source_buttons = [
            self.src_btn_add_local,
            self.src_btn_toggle,
            self.src_btn_remove,
        ]

        channels_box = ttk.LabelFrame(self.sources_channels_paned, text="Kanály", padding=6)
        channels_box.columnconfigure(0, weight=1)
        channels_box.rowconfigure(2, weight=1)

        self.channel_controls_top = ttk.Frame(channels_box)
        self.channel_controls_top.grid(row=0, column=0, sticky="ew", pady=(0, 4))
        if use_tk_primary_buttons:
            self.ch_btn_reload = tk.Button(self.channel_controls_top, text="Načíst kanály", command=self.refresh_channel_selection_auto, font=primary_button_font)
        else:
            self.ch_btn_reload = ttk.Button(self.channel_controls_top, text="Načíst kanály", command=self.refresh_channel_selection_auto)
        self.ch_btn_all = ttk.Button(self.channel_controls_top, text="Vybrat vše", command=self.select_all_channels)
        self.ch_btn_none = ttk.Button(self.channel_controls_top, text="Zrušit vše", command=self.deselect_all_channels)
        self.ch_btn_inv = ttk.Button(self.channel_controls_top, text="Obrátit výběr", command=self.invert_channel_selection)
        self.ch_more_btn = ttk.Menubutton(self.channel_controls_top, text="Další...")
        self.ch_more_menu = tk.Menu(self.ch_more_btn, tearoff=False)
        self.ch_more_menu.add_command(label="Obrátit výběr", command=self.invert_channel_selection)
        self.ch_more_btn.configure(menu=self.ch_more_menu)
        self._channel_action_buttons = [self.ch_btn_reload, self.ch_btn_all, self.ch_btn_none]

        self.channel_filters = ttk.Frame(channels_box)
        self.channel_filters.grid(row=1, column=0, sticky="ew", pady=(0, 4))
        self.channel_filters.columnconfigure(1, weight=1)
        self.channel_filters.columnconfigure(3, weight=1)
        self.channel_filters.columnconfigure(5, weight=1)
        self.channel_search_lbl = ttk.Label(self.channel_filters, text="Hledat název:")
        self.channel_search_lbl.grid(row=0, column=0, sticky="w")
        self.channel_search_entry = ttk.Entry(self.channel_filters, textvariable=self.channel_search_var)
        self.channel_search_entry.grid(row=0, column=1, sticky="ew", padx=(4, 8))
        self.channel_group_lbl = ttk.Label(self.channel_filters, text="Skupina:")
        self.channel_group_lbl.grid(row=0, column=2, sticky="w")
        self.channel_group_filter = ttk.Combobox(self.channel_filters, textvariable=self.channel_group_filter_var, state="readonly")
        self.channel_group_filter.grid(row=0, column=3, sticky="ew", padx=(4, 8))
        self.channel_source_lbl = ttk.Label(self.channel_filters, text="Zdroj:")
        self.channel_source_lbl.grid(row=0, column=4, sticky="w")
        self.channel_source_filter = ttk.Combobox(self.channel_filters, textvariable=self.channel_source_filter_var, state="readonly")
        self.channel_source_filter.grid(row=0, column=5, sticky="ew", padx=(4, 0))
        self.filters_toggle_btn = ttk.Button(self.channel_filters, text="Filtry", command=self._toggle_extra_filters)
        self.filters_extra_frame = ttk.Frame(self.channel_filters)
        self.filters_expanded = False

        self.channel_center_paned = ttk.Panedwindow(channels_box, orient="horizontal")
        self.channel_center_paned.grid(row=2, column=0, sticky="nsew")

        channel_table_wrap = ttk.Frame(self.channel_center_paned)
        channel_cols = ("enabled", "name", "group", "source", "url")
        self.channels_table = ttk.Treeview(channel_table_wrap, columns=channel_cols, show="headings", height=7)
        self.channels_table.heading("enabled", text="Enabled")
        self.channels_table.heading("name", text="Název")
        self.channels_table.heading("group", text="Skupina")
        self.channels_table.heading("source", text="Zdroj")
        self.channels_table.heading("url", text="URL")
        self.channels_table.column("enabled", width=70, anchor="center", stretch=False)
        self.channels_table.column("name", width=180, anchor="w", stretch=True)
        self.channels_table.column("group", width=140, anchor="w", stretch=True)
        self.channels_table.column("source", width=160, anchor="w", stretch=True)
        self.channels_table.column("url", width=240, anchor="w", stretch=True)
        channels_y = ttk.Scrollbar(channel_table_wrap, orient="vertical", command=self.channels_table.yview)
        channels_x = ttk.Scrollbar(channel_table_wrap, orient="horizontal", command=self.channels_table.xview)
        self.channels_table.configure(yscrollcommand=channels_y.set, xscrollcommand=channels_x.set)
        self.channels_table.grid(row=0, column=0, sticky="nsew")
        channels_y.grid(row=0, column=1, sticky="ns")
        channels_x.grid(row=1, column=0, sticky="ew")
        channel_table_wrap.rowconfigure(0, weight=1)
        channel_table_wrap.columnconfigure(0, weight=1)
        self.channel_context_menu = tk.Menu(self.channels_table, tearoff=False)
        self.channel_context_menu.add_command(label="▶ Test přehrávání", command=self.action_play_test_selected_channel)
        self.channel_context_menu.add_command(label="▶ Přehrát", command=self.action_play_selected_channel)
        self.channel_context_menu.add_command(label="▶ Přehrát ve VLC", command=self.action_play_selected_channel_vlc)
        self.channel_context_menu.add_command(label="🔧 Opravit kanál", command=self.action_repair_selected_channel)
        self.channel_context_menu.add_command(label="📋 Kopírovat URL", command=self.action_copy_selected_channel_url)

        self.channel_center_panel = ttk.LabelFrame(self.channel_center_paned, text="Vybraný kanál", padding=6)
        self.channel_center_panel.columnconfigure(0, minsize=132)
        self.channel_center_panel.columnconfigure(1, weight=1)

        row = 0
        ttk.Label(self.channel_center_panel, text="Název:").grid(row=row, column=0, sticky="e", padx=(0, 8), pady=3)
        ttk.Label(self.channel_center_panel, textvariable=self.channel_center_name_var).grid(row=row, column=1, sticky="ew", pady=3)
        row += 1
        ttk.Label(self.channel_center_panel, text="Skupina:").grid(row=row, column=0, sticky="e", padx=(0, 8), pady=3)
        ttk.Label(self.channel_center_panel, textvariable=self.channel_center_group_var).grid(row=row, column=1, sticky="ew", pady=3)
        row += 1
        ttk.Label(self.channel_center_panel, text="Země:").grid(row=row, column=0, sticky="e", padx=(0, 8), pady=3)
        ttk.Label(self.channel_center_panel, textvariable=self.channel_center_country_var).grid(row=row, column=1, sticky="ew", pady=3)
        row += 1
        ttk.Label(self.channel_center_panel, text="URL streamu:").grid(row=row, column=0, sticky="e", padx=(0, 8), pady=3)
        self.channel_center_url_entry = ttk.Entry(self.channel_center_panel, textvariable=self.channel_center_url_var, state="readonly")
        self.channel_center_url_entry.grid(row=row, column=1, sticky="ew", pady=3)
        self.channel_center_url_scroll = ttk.Scrollbar(self.channel_center_panel, orient="horizontal", command=self.channel_center_url_entry.xview)
        self.channel_center_url_entry.configure(xscrollcommand=self.channel_center_url_scroll.set)
        self.channel_center_url_scroll.grid(row=row + 1, column=1, sticky="ew", pady=(0, 3))
        row += 2
        self.channel_center_status_box = ttk.LabelFrame(self.channel_center_panel, text="Stav kanálu", padding=6)
        self.channel_center_status_box.grid(row=row, column=0, columnspan=2, sticky="ew", pady=(4, 3))
        self.channel_center_status_box.columnconfigure(0, minsize=132)
        self.channel_center_status_box.columnconfigure(1, weight=1)
        ttk.Label(self.channel_center_status_box, text="Stav:").grid(row=0, column=0, sticky="e", padx=(0, 8), pady=2)
        ttk.Label(self.channel_center_status_box, textvariable=self.channel_center_state_var).grid(row=0, column=1, sticky="ew", pady=2)
        ttk.Label(self.channel_center_status_box, text="Doporučení:").grid(row=1, column=0, sticky="e", padx=(0, 8), pady=2)
        ttk.Label(self.channel_center_status_box, textvariable=self.channel_center_recommendation_var, wraplength=380, justify="left").grid(row=1, column=1, sticky="ew", pady=2)
        row += 1
        ttk.Label(self.channel_center_panel, text="Poslední test:").grid(row=row, column=0, sticky="e", padx=(0, 8), pady=3)
        ttk.Label(self.channel_center_panel, textvariable=self.channel_center_last_test_var).grid(row=row, column=1, sticky="ew", pady=3)
        row += 1
        ttk.Label(self.channel_center_panel, text="Poslední chyba/důvod:").grid(row=row, column=0, sticky="e", padx=(0, 8), pady=3)
        ttk.Label(self.channel_center_panel, textvariable=self.channel_center_last_reason_var, wraplength=380, justify="left").grid(row=row, column=1, sticky="ew", pady=3)
        row += 1

        actions_box = ttk.LabelFrame(self.channel_center_panel, text="Akce", padding=6)
        actions_box.grid(row=row, column=0, columnspan=2, sticky="ew", pady=(8, 4))
        for col in range(2):
            actions_box.columnconfigure(col, weight=1)
        button_width = 20
        self.cc_btn_play = ttk.Button(actions_box, text="Přehrát", command=self.action_play_selected_channel, width=button_width)
        self.cc_btn_play_vlc = ttk.Button(actions_box, text="Přehrát ve VLC", command=self.action_play_selected_channel_vlc, width=button_width)
        self.cc_btn_play_test = ttk.Button(actions_box, text="▶ Test přehrávání", command=self.action_play_test_selected_channel, width=button_width)
        self.cc_btn_retest = ttk.Button(actions_box, text="Retest streamu", command=self.action_retest_selected_channel, width=button_width)
        self.cc_btn_replace = ttk.Button(actions_box, text="🔧 Opravit kanál", command=self.action_repair_selected_channel, width=button_width)
        self.cc_btn_copy = ttk.Button(actions_box, text="Kopírovat URL", command=self.action_copy_selected_channel_url, width=button_width)
        self.cc_btn_play.grid(row=0, column=0, sticky="ew", padx=2, pady=2)
        self.cc_btn_play_vlc.grid(row=0, column=1, sticky="ew", padx=2, pady=2)
        self.cc_btn_play_test.grid(row=1, column=0, sticky="ew", padx=2, pady=2)
        self.cc_btn_retest.grid(row=1, column=1, sticky="ew", padx=2, pady=2)
        self.cc_btn_replace.grid(row=2, column=0, sticky="ew", padx=2, pady=2)
        self.cc_btn_copy.grid(row=2, column=1, sticky="ew", padx=2, pady=2)
        row += 1

        future_box = ttk.Frame(self.channel_center_panel, padding=6, height=76)
        future_box.grid(row=row, column=0, columnspan=2, sticky="ew")
        future_box.grid_propagate(False)

        self.channel_center_paned.add(channel_table_wrap, weight=3)
        self.channel_center_paned.add(self.channel_center_panel, weight=2)

        self.channel_summary = ttk.Frame(channels_box)
        self.channel_summary.grid(row=3, column=0, sticky="ew", pady=(4, 0))
        self.sum_loaded_lbl = ttk.Label(self.channel_summary, text="Loaded:")
        self.sum_loaded_val = ttk.Label(self.channel_summary, textvariable=self.loaded_channels_var)
        self.sum_selected_lbl = ttk.Label(self.channel_summary, text="Selected:")
        self.sum_selected_val = ttk.Label(self.channel_summary, textvariable=self.selected_channels_var)
        self.sum_disabled_lbl = ttk.Label(self.channel_summary, text="Disabled:")
        self.sum_disabled_val = ttk.Label(self.channel_summary, textvariable=self.disabled_channels_var)
        self.sum_sources_lbl = ttk.Label(self.channel_summary, text="Selected sources:")
        self.sum_sources_val = ttk.Label(self.channel_summary, textvariable=self.selected_sources_var)
        self._summary_widgets = [
            self.sum_loaded_lbl, self.sum_loaded_val,
            self.sum_selected_lbl, self.sum_selected_val,
            self.sum_disabled_lbl, self.sum_disabled_val,
            self.sum_sources_lbl, self.sum_sources_val,
        ]

        self.sources_channels_paned.add(sources_box, weight=1)
        self.sources_channels_paned.add(channels_box, weight=3)

        self.options = ttk.LabelFrame(tab2, text="Nastavení kontroly", padding=6)
        self.options.grid(row=0, column=0, sticky="ew", pady=(0, 6))
        self.opt_test = ttk.Checkbutton(self.options, text="Testovat dostupnost streamů", variable=self.test_var)
        self.opt_timeout_lbl = ttk.Label(self.options, text="Timeout:")
        self.opt_timeout_sp = ttk.Spinbox(self.options, from_=3, to=30, width=5, textvariable=self.timeout)
        self.opt_workers_lbl = ttk.Label(self.options, text="Současné testy:")
        self.opt_workers_sp = ttk.Spinbox(self.options, from_=1, to=40, width=5, textvariable=self.workers)
        self.opt_autoscroll = ttk.Checkbutton(self.options, text="Automaticky posouvat log", variable=self.autoscroll)

        self.run_buttons = ttk.Frame(tab2)
        self.run_buttons.grid(row=1, column=0, sticky="ew", pady=(0, 6))
        if use_tk_primary_buttons:
            self.start_btn = tk.Button(self.run_buttons, text="SMART FIX – SPUSTIT", command=self.start_single, font=primary_button_font)
            self.stop_btn = tk.Button(self.run_buttons, text="ZASTAVIT", command=self.stop, state="disabled", font=primary_button_font)
        else:
            self.start_btn = ttk.Button(self.run_buttons, text="SMART FIX – SPUSTIT", command=self.start_single)
            self.stop_btn = ttk.Button(self.run_buttons, text="ZASTAVIT", command=self.stop, state="disabled")
        self.batch_btn = ttk.Button(self.run_buttons, text="Dávkové zpracování", command=self.start_batch)
        self.return_btn = ttk.Button(self.run_buttons, text="Vrátit", command=self.reset_gui)
        self.run_more_btn = ttk.Menubutton(self.run_buttons, text="Další...")
        self.run_more_menu = tk.Menu(self.run_more_btn, tearoff=False)
        self.run_more_menu.add_command(label="Dávkové zpracování", command=self.start_batch)
        self.run_more_btn.configure(menu=self.run_more_menu)
        self._run_buttons = [self.start_btn, self.stop_btn]
        self.open_protocol_btn = ttk.Button(tab4, text="Otevřít protokol", command=self.open_protocol, state="disabled")
        self.open_protocol_btn.grid(row=0, column=0, sticky="e", pady=(0, 6))

        stats_box = ttk.LabelFrame(tab2, text="Živé výsledky", padding=6)
        stats_box.grid(row=2, column=0, sticky="nsew", pady=(0, 6))
        tab2.grid_rowconfigure(2, weight=1)

        definitions = [
            ("Celkem", "TOTAL"), ("Testováno", "TESTED"), ("OK", "OK"),
            ("Pomalé", "SLOW"), ("Timeout", "TIMEOUT"), ("Auth / GEO", "AUTH_OR_GEO"),
            ("404", "NOT_FOUND"), ("Odstraněno", "REMOVED"), ("Rychlost", "SPEED"), ("ETA", "ETA"),
        ]

        self.stat_cells: list[ttk.Frame] = []

        for i, (label, key) in enumerate(definitions):
            frame = ttk.Frame(stats_box, padding=(3, 1))
            frame.grid(row=0, column=i, sticky="nsew", padx=1, pady=1)
            ttk.Label(frame, text=label, style="StatTitle.TLabel").pack()
            ttk.Label(frame, textvariable=self.stats[key], style="StatValue.TLabel").pack()
            self.stat_cells.append(frame)
        self.stats_box = stats_box

        ttk.Progressbar(tab2, variable=self.progress, maximum=100).grid(row=3, column=0, sticky="ew", pady=(0, 6))

        result_box = ttk.LabelFrame(tab3, text="Výsledek", padding=6)
        result_box.grid(row=0, column=0, sticky="nsew")
        tab3.grid_rowconfigure(0, weight=1)

        info_grid = ttk.Frame(result_box)
        info_grid.pack(fill="x", pady=(0, 6))
        info_grid.columnconfigure(1, weight=1)
        ttk.Label(info_grid, text="Finální playlist:").grid(row=0, column=0, sticky="w", padx=(0, 8))
        ttk.Label(info_grid, textvariable=self.final_name_var).grid(row=0, column=1, sticky="w")
        ttk.Label(info_grid, text="Počet kanálů:").grid(row=1, column=0, sticky="w", padx=(0, 8))
        ttk.Label(info_grid, textvariable=self.final_count_var).grid(row=1, column=1, sticky="w")
        ttk.Label(info_grid, text="Plná cesta:").grid(row=2, column=0, sticky="w", padx=(0, 8))
        self.final_path_entry = ttk.Entry(info_grid, textvariable=self.final_path_var, state="readonly")
        self.final_path_entry.grid(row=2, column=1, sticky="ew")
        self.final_path_scroll = ttk.Scrollbar(info_grid, orient="horizontal", command=self.final_path_entry.xview)
        self.final_path_entry.configure(xscrollcommand=self.final_path_scroll.set)
        self.final_path_scroll.grid(row=3, column=1, sticky="ew", pady=(2, 0))

        self.result_buttons = ttk.Frame(result_box)
        self.result_buttons.pack(fill="x")
        if use_tk_primary_buttons:
            self.open_final_btn = tk.Button(self.result_buttons, text="Otevřít hotový playlist", command=self.open_final_playlist, state="disabled", font=primary_button_font)
        else:
            self.open_final_btn = ttk.Button(self.result_buttons, text="Otevřít hotový playlist", command=self.open_final_playlist, state="disabled")
        self.open_final_folder_btn = ttk.Button(self.result_buttons, text="Otevřít složku", command=self.open_final_playlist_folder, state="disabled")
        self.save_final_as_btn = ttk.Button(self.result_buttons, text="Uložit playlist jako...", command=self.save_final_playlist_as, state="disabled")
        self.open_output_btn = ttk.Button(self.result_buttons, text="Otevřít výstupní složku", command=self.open_output)
        self._result_buttons = [self.open_final_btn, self.open_final_folder_btn, self.save_final_as_btn, self.open_output_btn]

        self.channel_group_filter["values"] = ("Vše",)
        self.channel_source_filter["values"] = ("Vše",)
        self.channel_group_filter.current(0)
        self.channel_source_filter.current(0)
        self.channel_search_var.trace_add("write", self._on_channel_filter_change)
        self.channel_group_filter.bind("<<ComboboxSelected>>", self._on_channel_filter_change)
        self.channel_source_filter.bind("<<ComboboxSelected>>", self._on_channel_filter_change)
        self.channels_table.bind("<<TreeviewSelect>>", self._on_channel_selection_changed)
        self.channels_table.bind("<Button-1>", self._on_channels_table_click)
        self.channels_table.bind("<Button-3>", self._on_channels_table_context_menu)
        self.channels_table.bind("<Double-1>", self._on_channels_table_double_click)
        self.channels_table.bind("<space>", self._toggle_selected_channel)
        self._set_channel_center_actions_state(False)

        log_box = ttk.LabelFrame(tab4, text="Průběh kontroly", padding=6)
        log_box.grid(row=1, column=0, sticky="nsew")
        log_box.columnconfigure(0, weight=1)
        log_box.rowconfigure(0, weight=1)
        scroll = ttk.Scrollbar(log_box)
        scroll.grid(row=0, column=1, sticky="ns")
        self.log = tk.Text(log_box, state="disabled", wrap="word", yscrollcommand=scroll.set, borderwidth=0)
        self.log.grid(row=0, column=0, sticky="nsew")
        scroll.config(command=self.log.yview)

        self.log.tag_configure("ok", foreground="#1f7a1f")
        self.log.tag_configure("slow", foreground="#a66a00")
        self.log.tag_configure("error", foreground="#b22222")
        self.log.tag_configure("info", foreground="#245a9a")
        log_font = tkfont.nametofont("TkFixedFont")
        self.log.configure(font=log_font)
        log_title_font = log_font.copy()
        log_title_font.configure(weight="bold")
        self.log.tag_configure("title", font=log_title_font)

        status_bar = ttk.Frame(root_wrap, padding=(2, 2))
        status_bar.grid(row=2, column=0, sticky="ew")
        status_bar.columnconfigure(0, weight=1)
        status_bar.columnconfigure(1, weight=2)
        self.status_label = ttk.Label(status_bar, textvariable=self.status_display)
        self.status_label.grid(row=0, column=0, sticky="w")
        self.detail_label = ttk.Label(status_bar, textvariable=self.detail_display)
        self.detail_label.grid(row=0, column=1, sticky="e")

        self._layout_mode: str | None = None
        self._layout_after_id: str | None = None
        self.bind("<Configure>", self._on_window_configure)
        self.after(0, self._apply_responsive_layout)
        self.return_btn.grid_remove()

    def _on_window_configure(self, _event=None) -> None:
        self._refresh_statusbar_text()
        if self._layout_after_id is not None:
            try:
                self.after_cancel(self._layout_after_id)
            except Exception:
                pass
        self._layout_after_id = self.after(120, self._apply_responsive_layout)

    def _determine_layout_mode(self, width: int) -> str:
        if width < 820:
            return "very_narrow"
        if width < 1280:
            return "narrow"
        return "wide"

    def _grid_button_row(self, frame: ttk.Frame, buttons: list[tk.Widget], columns: int) -> None:
        for child in frame.winfo_children():
            child.grid_forget()
        columns = max(1, columns)
        for col in range(columns):
            frame.columnconfigure(col, weight=1)
        for i, btn in enumerate(buttons):
            row = i // columns
            col = i % columns
            btn.grid(row=row, column=col, sticky="ew", padx=2, pady=2)

    def _layout_summary(self, mode: str) -> None:
        for child in self.channel_summary.winfo_children():
            child.grid_forget()
        pairs = [
            (self.sum_loaded_lbl, self.sum_loaded_val),
            (self.sum_selected_lbl, self.sum_selected_val),
            (self.sum_disabled_lbl, self.sum_disabled_val),
            (self.sum_sources_lbl, self.sum_sources_val),
        ]
        if mode == "wide":
            for i in range(8):
                self.channel_summary.columnconfigure(i, weight=0)
            col = 0
            for lbl, val in pairs:
                lbl.grid(row=0, column=col, sticky="w")
                val.grid(row=0, column=col + 1, sticky="w", padx=(4, 10))
                col += 2
        elif mode == "narrow":
            for i in range(4):
                self.channel_summary.columnconfigure(i, weight=1 if i % 2 else 0)
            for r, (lbl, val) in enumerate(pairs[:2]):
                lbl.grid(row=r, column=0, sticky="w")
                val.grid(row=r, column=1, sticky="w", padx=(4, 10))
            for r, (lbl, val) in enumerate(pairs[2:]):
                lbl.grid(row=r, column=2, sticky="w")
                val.grid(row=r, column=3, sticky="w", padx=(4, 10))
        else:
            self.sum_loaded_lbl.configure(text="Load:")
            self.sum_selected_lbl.configure(text="Sel:")
            self.sum_disabled_lbl.configure(text="Dis:")
            self.sum_sources_lbl.configure(text="Src:")
            self.channel_summary.columnconfigure(0, weight=0)
            self.channel_summary.columnconfigure(1, weight=1)
            self.channel_summary.columnconfigure(2, weight=0)
            self.channel_summary.columnconfigure(3, weight=1)
            for r, (lbl, val) in enumerate(pairs[:2]):
                lbl.grid(row=r, column=0, sticky="w")
                val.grid(row=r, column=1, sticky="w", padx=(4, 8))
            for r, (lbl, val) in enumerate(pairs[2:]):
                lbl.grid(row=r, column=2, sticky="w")
                val.grid(row=r, column=3, sticky="w", padx=(4, 0))
            return

        self.sum_loaded_lbl.configure(text="Loaded:")
        self.sum_selected_lbl.configure(text="Selected:")
        self.sum_disabled_lbl.configure(text="Disabled:")
        self.sum_sources_lbl.configure(text="Selected sources:")

    def _update_treeview_columns(self, mode: str) -> None:
        sw = max(320, self.sources_table.winfo_width())
        cw = max(320, self.channels_table.winfo_width())

        if mode == "wide":
            s_fixed = 70 + 120 + 120
            s_extra = max(0, sw - s_fixed)
            s_name = max(140, int(s_extra * 0.28))
            s_type = max(100, int(s_extra * 0.2))
            s_location = max(220, s_extra - s_name - s_type)
        elif mode == "narrow":
            s_fixed = 60 + 110 + 100
            s_extra = max(0, sw - s_fixed)
            s_name = max(120, int(s_extra * 0.30))
            s_type = max(90, int(s_extra * 0.18))
            s_location = max(160, s_extra - s_name - s_type)
        else:
            s_fixed = 55 + 95 + 95
            s_extra = max(0, sw - s_fixed)
            s_name = max(100, int(s_extra * 0.33))
            s_type = max(80, int(s_extra * 0.17))
            s_location = max(130, s_extra - s_name - s_type)

        self.sources_table.column("enabled", width=55 if mode == "very_narrow" else 70, stretch=False)
        self.sources_table.column("name", width=s_name, stretch=True)
        self.sources_table.column("type", width=s_type, stretch=False)
        self.sources_table.column("location", width=s_location, stretch=True)
        self.sources_table.column("last_update", width=95 if mode == "very_narrow" else 120, stretch=False)
        self.sources_table.column("status", width=95 if mode == "very_narrow" else 120, stretch=False)
        if mode in ("narrow", "very_narrow"):
            self.sources_table["displaycolumns"] = ("enabled", "name", "status")
        else:
            self.sources_table["displaycolumns"] = ("enabled", "name", "type", "location", "last_update", "status")

        if mode == "wide":
            c_fixed = 70
            c_extra = max(0, cw - c_fixed)
            c_name = max(160, int(c_extra * 0.23))
            c_group = max(120, int(c_extra * 0.16))
            c_source = max(130, int(c_extra * 0.16))
        elif mode == "narrow":
            c_fixed = 65
            c_extra = max(0, cw - c_fixed)
            c_name = max(130, int(c_extra * 0.24))
            c_group = max(100, int(c_extra * 0.15))
            c_source = max(110, int(c_extra * 0.15))
        else:
            c_fixed = 60
            c_extra = max(0, cw - c_fixed)
            c_name = max(110, int(c_extra * 0.23))
            c_group = max(90, int(c_extra * 0.14))
            c_source = max(95, int(c_extra * 0.14))
        c_url = max(120, c_extra - c_name - c_group - c_source)

        self.channels_table.column("enabled", width=60 if mode == "very_narrow" else 70, stretch=False)
        self.channels_table.column("name", width=c_name, stretch=True)
        self.channels_table.column("group", width=c_group, stretch=True)
        self.channels_table.column("source", width=c_source, stretch=True)
        self.channels_table.column("url", width=c_url, stretch=True)
        if mode in ("narrow", "very_narrow"):
            self.channels_table["displaycolumns"] = ("enabled", "name", "group")
        else:
            self.channels_table["displaycolumns"] = ("enabled", "name", "group", "source", "url")

    def _layout_stats_grid(self, mode: str) -> None:
        if mode == "wide":
            cols = 5
        elif mode == "narrow":
            cols = 4
        else:
            cols = 2
        for i in range(cols):
            self.stats_box.columnconfigure(i, weight=1)
        for idx, frame in enumerate(self.stat_cells):
            frame.grid_forget()
            r = idx // cols
            c = idx % cols
            frame.grid(row=r, column=c, sticky="nsew", padx=1, pady=1)

    def _layout_options(self, mode: str) -> None:
        for child in self.options.winfo_children():
            child.grid_forget()
        if mode == "wide":
            self.opt_test.grid(row=0, column=0, sticky="w", padx=(0, 8), pady=2)
            self.opt_timeout_lbl.grid(row=0, column=1, sticky="w", pady=2)
            self.opt_timeout_sp.grid(row=0, column=2, sticky="w", padx=(4, 8), pady=2)
            self.opt_workers_lbl.grid(row=0, column=3, sticky="w", pady=2)
            self.opt_workers_sp.grid(row=0, column=4, sticky="w", padx=(4, 8), pady=2)
            self.opt_autoscroll.grid(row=0, column=5, sticky="w", pady=2)
        elif mode == "narrow":
            self.opt_test.grid(row=0, column=0, sticky="w", padx=(0, 8), pady=2)
            self.opt_autoscroll.grid(row=0, column=1, sticky="w", pady=2)
            self.opt_timeout_lbl.grid(row=1, column=0, sticky="w", pady=2)
            self.opt_timeout_sp.grid(row=1, column=1, sticky="w", padx=(4, 8), pady=2)
            self.opt_workers_lbl.grid(row=2, column=0, sticky="w", pady=2)
            self.opt_workers_sp.grid(row=2, column=1, sticky="w", padx=(4, 8), pady=2)
        else:
            self.opt_test.grid(row=0, column=0, sticky="w", pady=2)
            self.opt_autoscroll.grid(row=0, column=1, sticky="w", padx=(8, 0), pady=2)
            self.opt_timeout_lbl.grid(row=1, column=0, sticky="w", pady=2)
            self.opt_timeout_sp.grid(row=1, column=1, sticky="w", pady=2)
            self.opt_workers_lbl.grid(row=2, column=0, sticky="w", pady=2)
            self.opt_workers_sp.grid(row=2, column=1, sticky="w", pady=2)

    def _toggle_extra_filters(self) -> None:
        self.filters_expanded = not self.filters_expanded
        self._layout_channel_filters(self._layout_mode or self._determine_layout_mode(self.winfo_width()))

    def _layout_channel_filters(self, mode: str) -> None:
        parent = self.channel_search_entry.master
        for child in parent.winfo_children():
            child.grid_forget()
        if mode == "very_narrow":
            parent.columnconfigure(1, weight=1)
            self.channel_search_lbl.grid(row=0, column=0, sticky="w")
            self.channel_search_entry.grid(row=0, column=1, sticky="ew", padx=(4, 4))
            self.filters_toggle_btn.grid(row=0, column=2, sticky="e")
            self.filters_toggle_btn.configure(text="Filtry ▼" if self.filters_expanded else "Filtry")
            if self.filters_expanded:
                self.channel_group_lbl.grid(row=1, column=0, sticky="w", pady=(2, 0))
                self.channel_group_filter.grid(row=1, column=1, columnspan=2, sticky="ew", padx=(4, 0), pady=(2, 0))
                self.channel_source_lbl.grid(row=2, column=0, sticky="w", pady=(2, 0))
                self.channel_source_filter.grid(row=2, column=1, columnspan=2, sticky="ew", padx=(4, 0), pady=(2, 0))
        else:
            self.filters_expanded = False
            parent.columnconfigure(1, weight=1)
            parent.columnconfigure(3, weight=1)
            parent.columnconfigure(5, weight=1)
            self.channel_search_lbl.grid(row=0, column=0, sticky="w")
            self.channel_search_entry.grid(row=0, column=1, sticky="ew", padx=(4, 8))
            if mode == "narrow":
                self.channel_group_lbl.grid(row=1, column=0, sticky="w", pady=(2, 0))
                self.channel_group_filter.grid(row=1, column=1, sticky="ew", padx=(4, 8), pady=(2, 0))
                self.channel_source_lbl.grid(row=1, column=2, sticky="w", pady=(2, 0))
                self.channel_source_filter.grid(row=1, column=3, sticky="ew", padx=(4, 0), pady=(2, 0))
            else:
                self.channel_group_lbl.grid(row=0, column=2, sticky="w")
                self.channel_group_filter.grid(row=0, column=3, sticky="ew", padx=(4, 8))
                self.channel_source_lbl.grid(row=0, column=4, sticky="w")
                self.channel_source_filter.grid(row=0, column=5, sticky="ew", padx=(4, 0))

    def _apply_responsive_layout(self) -> None:
        self._layout_after_id = None
        width = max(320, self.winfo_width())
        mode = self._determine_layout_mode(width)
        if mode == self._layout_mode:
            self._update_treeview_columns(mode)
            return

        self._layout_mode = mode
        run_buttons = self._run_buttons + ([self.return_btn] if self.stopped_by_user else [])
        if mode == "wide":
            self._grid_button_row(self.src_btns, self._source_buttons + [self.src_btn_add_url, self.src_btn_up, self.src_btn_down, self.src_btn_open], 4)
            self._grid_button_row(self.channel_controls_top, self._channel_action_buttons + [self.ch_btn_inv], 4)
            self._grid_button_row(self.run_buttons, [self.start_btn, self.batch_btn, self.stop_btn] + ([self.return_btn] if self.stopped_by_user else []), 4)
            self._grid_button_row(self.result_buttons, self._result_buttons, 4)
        elif mode == "narrow":
            self._grid_button_row(self.src_btns, self._source_buttons + [self.src_btn_add_url, self.src_btn_up, self.src_btn_down, self.src_btn_open], 4)
            self._grid_button_row(self.channel_controls_top, self._channel_action_buttons + [self.ch_btn_inv], 2)
            self._grid_button_row(self.run_buttons, [self.start_btn, self.batch_btn, self.stop_btn] + ([self.return_btn] if self.stopped_by_user else []), 2)
            self._grid_button_row(self.result_buttons, self._result_buttons, 2)
        else:
            self._grid_button_row(self.src_btns, self._source_buttons + [self.src_more_btn], 2)
            self._grid_button_row(self.channel_controls_top, self._channel_action_buttons + [self.ch_more_btn], 2)
            self._grid_button_row(self.run_buttons, run_buttons + [self.run_more_btn], 2)
            self._grid_button_row(self.result_buttons, self._result_buttons, 2)

        self._layout_options(mode)
        self._layout_stats_grid(mode)
        self._layout_channel_filters(mode)
        self._layout_summary(mode)
        self._update_treeview_columns(mode)
        try:
            total_w = self.channel_center_paned.winfo_width()
            if total_w > 500:
                if mode == "wide":
                    target = int(total_w * 0.64)
                elif mode == "narrow":
                    target = int(total_w * 0.70)
                else:
                    target = int(total_w * 0.78)
                self.channel_center_paned.sashpos(0, max(380, min(target, total_w - 280)))
        except Exception:
            pass
        try:
            total_h = self.sources_channels_paned.winfo_height()
            if total_h > 200:
                top_h = max(105, min(int(total_h * 0.32), total_h - 150))
                self.sources_channels_paned.sashpos(0, top_h)
        except Exception:
            pass
        self._refresh_statusbar_text()

    def choose(self) -> None:
        p = filedialog.askopenfilename(
            filetypes=[("M3U playlist", "*.m3u *.m3u8"), ("Všechny soubory", "*.*")]
        )
        if p:
            self.file = Path(p)
            self.file_var.set(p)
            self.return_btn.grid_remove()
            self.stopped_by_user = False
            self.write(f"Vybrán: {p}", "info")
            self.refresh_channel_selection("single")

    def _source_exists(self, source_type: str, location: str) -> bool:
        key = self._source_key(source_type, location)
        for src in self.sources:
            src_type = str(src.get("type", ""))
            src_location = str(src.get("location", ""))
            if self._source_key(src_type, src_location) == key:
                return True
        return False

    def _source_key(self, source_type: str, location: str) -> str:
        stype = source_type.strip().casefold()
        loc = location.strip()
        if stype == "local":
            try:
                loc = str(Path(loc).expanduser().resolve(strict=False))
            except Exception:
                pass
            return f"local::{loc.casefold()}"
        if stype == "url":
            parsed = urllib.parse.urlsplit(loc)
            scheme = parsed.scheme.casefold()
            netloc = parsed.netloc.casefold()
            path = parsed.path.rstrip("/")
            normalized = urllib.parse.urlunsplit((scheme, netloc, path, parsed.query, ""))
            return f"url::{normalized}"
        return f"{stype}::{loc.casefold()}"

    def _validate_source(self, source_type: str, location: str) -> tuple[bool, str, str]:
        stype = source_type.strip()
        loc = location.strip()
        if not loc:
            return False, "", "Umístění zdroje je prázdné."

        if stype == "Local":
            try:
                path = Path(loc).expanduser().resolve(strict=False)
            except Exception:
                path = Path(loc).expanduser()
            if not path.exists():
                return False, str(path), f"Lokální soubor neexistuje: {path}"
            if not path.is_file():
                return False, str(path), f"Lokální cesta není soubor: {path}"
            if path.suffix.casefold() not in {".m3u", ".m3u8"}:
                return False, str(path), "Podporované jsou pouze soubory .m3u nebo .m3u8."
            return True, str(path), ""

        if stype == "URL":
            parsed = urllib.parse.urlsplit(loc)
            if parsed.scheme.casefold() not in {"http", "https"}:
                return False, loc, "URL musí začínat http:// nebo https://"
            if not parsed.netloc:
                return False, loc, "URL neobsahuje doménu (hostitele)."
            return True, loc, ""

        return False, loc, f"Neznámý typ zdroje: {stype}"

    def _new_source(self, name: str, source_type: str, location: str) -> dict[str, str | bool]:
        return {
            "enabled": True,
            "name": name,
            "type": source_type,
            "location": location,
            "last_update": "-",
            "status": "Ready",
        }

    def _persist_sources(self, refresh: bool = True, reload_channels: bool = True) -> None:
        self.save_sources()
        if refresh:
            self.refresh_sources_table()
        if reload_channels:
            self.refresh_channel_selection("batch")

    def save_sources(self) -> None:
        try:
            _SOURCES_CONFIG_PATH.write_text(json.dumps(self.sources, ensure_ascii=False, indent=2), encoding="utf-8")
        except OSError as exc:
            logger.error("FILE_ERROR: Nelze zapsat konfiguraci zdrojů '%s': %s", _SOURCES_CONFIG_PATH, exc)

    def sync_replacement_sources(self) -> None:
        try:
            _REPLACEMENT_SOURCES_DIR.mkdir(parents=True, exist_ok=True)
        except OSError as exc:
            logger.error("FILE_ERROR: Nelze vytvořit replacement_sources '%s': %s", _REPLACEMENT_SOURCES_DIR, exc)
            return

        changed = False
        for path in sorted(list(_REPLACEMENT_SOURCES_DIR.glob("*.m3u")) + list(_REPLACEMENT_SOURCES_DIR.glob("*.m3u8"))):
            loc = str(path.resolve())
            if not self._source_exists("Local", loc):
                self.sources.append(self._new_source(path.stem, "Local", loc))
                changed = True
        if changed:
            self.save_sources()

    def load_sources(self) -> None:
        loaded: list[dict[str, str | bool]] = []
        seen_keys: set[str] = set()
        if _SOURCES_CONFIG_PATH.exists():
            try:
                data = json.loads(_SOURCES_CONFIG_PATH.read_text(encoding="utf-8"))
                if isinstance(data, list):
                    for item in data:
                        if not isinstance(item, dict):
                            continue
                        source_type_raw = str(item.get("type", "Local"))
                        source_type = "URL" if source_type_raw.strip().casefold() == "url" else "Local"
                        location = str(item.get("location", "")).strip()
                        is_valid, normalized_location, err = self._validate_source(source_type, location)

                        source_entry = {
                            "enabled": bool(item.get("enabled", True)),
                            "name": str(item.get("name", "Unnamed")),
                            "type": source_type,
                            "location": normalized_location if is_valid else location,
                            "last_update": str(item.get("last_update", "-")),
                            "status": str(item.get("status", "Ready")),
                        }

                        if not is_valid:
                            source_entry["enabled"] = False
                            source_entry["status"] = f"Error: {err}"

                        key = self._source_key(source_type, str(source_entry.get("location", "")))
                        if key in seen_keys:
                            logger.warning("DUPLICATE_SOURCE: Přeskakuji duplicitní zdroj '%s'", source_entry["location"])
                            continue

                        seen_keys.add(key)
                        loaded.append(source_entry)
            except Exception as exc:
                logger.error("FILE_ERROR: Nelze načíst konfiguraci zdrojů '%s': %s", _SOURCES_CONFIG_PATH, exc)

        self.sources = loaded
        self.sync_replacement_sources()
        self._persist_sources(refresh=False, reload_channels=False)

    def refresh_sources_table(self) -> None:
        for iid in self.sources_table.get_children():
            self.sources_table.delete(iid)
        for idx, src in enumerate(self.sources):
            enabled = "Yes" if bool(src.get("enabled", True)) else "No"
            self.sources_table.insert(
                "",
                "end",
                iid=str(idx),
                values=(
                    enabled,
                    str(src.get("name", "")),
                    str(src.get("type", "")),
                    str(src.get("location", "")),
                    str(src.get("last_update", "-")),
                    str(src.get("status", "Ready")),
                ),
            )

    def _selected_source_index(self) -> int | None:
        sel = self.sources_table.selection()
        if not sel:
            return None
        try:
            idx = int(sel[0])
        except ValueError:
            return None
        if 0 <= idx < len(self.sources):
            return idx
        return None

    def add_local_source(self) -> None:
        p = filedialog.askopenfilename(filetypes=[("M3U playlist", "*.m3u *.m3u8"), ("Všechny soubory", "*.*")])
        if not p:
            return
        is_valid, normalized_location, err = self._validate_source("Local", p)
        if not is_valid:
            messagebox.showerror("Neplatný lokální zdroj", err)
            return
        path = Path(normalized_location)
        if self._source_exists("Local", normalized_location):
            messagebox.showinfo("Playlist Sources", "Tento lokální zdroj už existuje.")
            return
        self.sources.append(self._new_source(path.stem, "Local", normalized_location))
        self._persist_sources()

    def add_url_source(self) -> None:
        url = simpledialog.askstring("Add URL Playlist", "Zadejte URL playlistu (.m3u/.m3u8):", parent=self)
        if not url:
            return
        url = url.strip()
        is_valid, normalized_url, err = self._validate_source("URL", url)
        if not is_valid:
            messagebox.showerror("Neplatná URL", err)
            return
        if self._source_exists("URL", normalized_url):
            messagebox.showinfo("Playlist Sources", "Tento URL zdroj už existuje.")
            return
        parsed = urllib.parse.urlsplit(normalized_url)
        name = Path(parsed.path).stem or parsed.netloc or "URL Source"
        self.sources.append(self._new_source(name, "URL", normalized_url))
        self._persist_sources()

    def remove_source(self) -> None:
        idx = self._selected_source_index()
        if idx is None:
            return
        self.sources.pop(idx)
        self._persist_sources()

    def toggle_source(self) -> None:
        idx = self._selected_source_index()
        if idx is None:
            return
        self.sources[idx]["enabled"] = not bool(self.sources[idx].get("enabled", True))
        self._persist_sources()

    def move_source_up(self) -> None:
        idx = self._selected_source_index()
        if idx is None or idx == 0:
            return
        self.sources[idx - 1], self.sources[idx] = self.sources[idx], self.sources[idx - 1]
        self._persist_sources()
        self.sources_table.selection_set(str(idx - 1))

    def move_source_down(self) -> None:
        idx = self._selected_source_index()
        if idx is None or idx >= len(self.sources) - 1:
            return
        self.sources[idx + 1], self.sources[idx] = self.sources[idx], self.sources[idx + 1]
        self._persist_sources()
        self.sources_table.selection_set(str(idx + 1))

    def open_sources_folder(self) -> None:
        try:
            _REPLACEMENT_SOURCES_DIR.mkdir(parents=True, exist_ok=True)
            os.startfile(_REPLACEMENT_SOURCES_DIR)
        except OSError as exc:
            logger.error("FILE_ERROR: Nelze otevřít složku zdrojů '%s': %s", _REPLACEMENT_SOURCES_DIR, exc)
            messagebox.showerror("Playlist Sources", f"Nelze otevřít složku zdrojů:\n{_REPLACEMENT_SOURCES_DIR}\n\n{exc}")

    def _set_source_state(self, source: dict[str, str | bool], status: str, touch_update: bool = False) -> None:
        source["status"] = status
        if touch_update:
            source["last_update"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    def _resolve_source_to_path(self, source: dict[str, str | bool], stamp: str) -> Path:
        source_type = str(source.get("type", "Local"))
        location = str(source.get("location", "")).strip()
        is_valid, normalized_location, err = self._validate_source(source_type, location)
        if not is_valid:
            raise RuntimeError(f"Neplatný zdroj '{source.get('name', 'Unnamed source')}': {err}")

        if source_type == "Local":
            return Path(normalized_location)

        # URL source: download to replacement_sources and process as local file.
        _REPLACEMENT_SOURCES_DIR.mkdir(parents=True, exist_ok=True)
        name = re.sub(r"[^a-zA-Z0-9_-]+", "_", str(source.get("name", "url_source"))).strip("_") or "url_source"
        target = _REPLACEMENT_SOURCES_DIR / f"{name}_{stamp}.m3u"
        req = urllib.request.Request(normalized_location, headers={"User-Agent": "Mozilla/5.0"})
        try:
            with urllib.request.urlopen(req, timeout=20) as resp:
                data = resp.read()
            target.write_bytes(data)
        except Exception as exc:
            raise RuntimeError(f"Nelze stáhnout URL zdroj '{source.get('name', 'Unnamed source')}' ({normalized_location}): {exc}") from exc
        return target

    def _enabled_batch_sources(self) -> list[dict[str, str | bool]]:
        self.sync_replacement_sources()
        self.refresh_sources_table()
        return [s for s in self.sources if bool(s.get("enabled", True))]

    def refresh_channel_selection_auto(self) -> None:
        mode = "single" if self.file else "batch"
        self.refresh_channel_selection(mode)

    def _channel_preview_inputs(self, mode: str) -> list[tuple[str, str, Path]]:
        stamp = datetime.now().strftime("%Y%m%d_%H-%M-%S")
        out: list[tuple[str, str, Path]] = []

        if mode == "single":
            if self.file is None:
                return []
            src_path = Path(self.file)
            src_name = src_path.stem
            src_id = self._source_key("Local", str(src_path))
            out.append((src_id, src_name, src_path))
            return out

        enabled_sources = self._enabled_batch_sources()
        for idx, source in enumerate(enabled_sources, 1):
            src_name = str(source.get("name", "Unnamed source"))
            src_id = self._source_key(str(source.get("type", "Local")), str(source.get("location", "")))
            src_path = self._resolve_source_to_path(source, f"preview_{stamp}_{idx:03d}")
            out.append((src_id, src_name, src_path))
        return out

    def refresh_channel_selection(self, mode: str) -> None:
        self.channel_mode = mode
        previous_state: dict[tuple[str, str], bool] = {
            (str(row["source_id"]), str(row["norm_url"])): bool(row["enabled"])
            for row in self.channel_rows
        }
        self.channel_rows = []
        self.channel_preview_error = ""
        self._channel_groups = []
        self._channel_sources = []

        seen_urls: set[str] = set()
        seen_names: set[str] = set()
        row_index = 0
        source_count = 0

        try:
            inputs = self._channel_preview_inputs(mode)
            source_count = len(inputs)
            for src_id, src_name, src_path in inputs:
                channels = parse(src_path)
                for c in channels:
                    norm_url = normalize_url(c.url)
                    norm_name = normalize_name(c.name)
                    if norm_url in seen_urls:
                        continue
                    if norm_name and norm_name in seen_names:
                        continue

                    attrs = parse_extinf_attrs(c.extinf)
                    group = attrs.get("group-title", "").strip() or "Bez skupiny"
                    country = (
                        attrs.get("tvg-country", "").strip()
                        or attrs.get("country", "").strip()
                        or attrs.get("tvg-language", "").strip()
                        or "-"
                    )
                    row_index += 1
                    row_key = (src_id, norm_url)
                    self.channel_rows.append({
                        "id": f"ch_{row_index}",
                        "enabled": previous_state.get(row_key, True),
                        "name": c.name,
                        "group": group,
                        "country": country,
                        "source": src_name,
                        "source_id": src_id,
                        "extinf": c.extinf,
                        "url": c.url,
                        "norm_url": norm_url,
                        "norm_name": norm_name,
                        "current_status": "-",
                        "last_test_elapsed": None,
                        "last_test_time": "-",
                        "last_error_reason": "-",
                    })
                    seen_urls.add(norm_url)
                    if norm_name:
                        seen_names.add(norm_name)
        except Exception as exc:
            self.channel_preview_error = str(exc)
            logger.error("CHANNEL_PREVIEW_ERROR: %s", exc)

        self._channel_groups = sorted({str(r["group"]) for r in self.channel_rows})
        self._channel_sources = sorted({str(r["source"]) for r in self.channel_rows})
        self.channel_group_filter["values"] = tuple(["Vše"] + self._channel_groups)
        self.channel_source_filter["values"] = tuple(["Vše"] + self._channel_sources)
        if self.channel_group_filter_var.get() not in self.channel_group_filter["values"]:
            self.channel_group_filter_var.set("Vše")
        if self.channel_source_filter_var.get() not in self.channel_source_filter["values"]:
            self.channel_source_filter_var.set("Vše")

        if self.channel_preview_error:
            self.write(f"Načtení kanálů selhalo: {self.channel_preview_error}", "error")

        self.selected_sources_var.set(str(source_count))
        self._render_channel_rows()
        self._update_channel_summary()
        self._clear_channel_center()

    def _on_channel_filter_change(self, *_args) -> None:
        self._render_channel_rows()

    def _row_visible(self, row: dict[str, object]) -> bool:
        search = self.channel_search_var.get().strip().casefold()
        if search and search not in str(row["name"]).casefold():
            return False

        group_filter = self.channel_group_filter_var.get().strip()
        if group_filter and group_filter != "Vše" and str(row["group"]) != group_filter:
            return False

        source_filter = self.channel_source_filter_var.get().strip()
        if source_filter and source_filter != "Vše" and str(row["source"]) != source_filter:
            return False

        return True

    def _render_channel_rows(self) -> None:
        selected_before = self._selected_channel_id
        for iid in self.channels_table.get_children():
            self.channels_table.delete(iid)
        for row in self.channel_rows:
            if not self._row_visible(row):
                continue
            self.channels_table.insert(
                "",
                "end",
                iid=str(row["id"]),
                values=(
                    "Yes" if bool(row["enabled"]) else "No",
                    str(row["name"]),
                    str(row["group"]),
                    str(row["source"]),
                    str(row["url"]),
                ),
            )
        if selected_before and self.channels_table.exists(selected_before):
            self.channels_table.selection_set(selected_before)
            self.channels_table.focus(selected_before)
            self._selected_channel_id = selected_before
        else:
            sel = self.channels_table.selection()
            self._selected_channel_id = str(sel[0]) if sel else None
        self._update_channel_summary()
        self._refresh_channel_center()

    def _update_channel_summary(self) -> None:
        loaded = len(self.channel_rows)
        selected = sum(1 for row in self.channel_rows if bool(row["enabled"]))
        disabled = loaded - selected
        self.loaded_channels_var.set(str(loaded))
        self.selected_channels_var.set(str(selected))
        self.disabled_channels_var.set(str(disabled))
        if not self.channel_rows:
            if self.channel_mode == "single":
                self.selected_sources_var.set("1" if self.file else "0")
            else:
                self.selected_sources_var.set(str(len(self._enabled_batch_sources())))

    def _toggle_selected_channel(self, _event=None):
        selected_items = self.channels_table.selection()
        if not selected_items:
            return "break"
        selected_ids = {str(iid) for iid in selected_items}
        for row in self.channel_rows:
            if str(row["id"]) in selected_ids:
                row["enabled"] = not bool(row["enabled"])
        self._render_channel_rows()
        return "break"

    def _toggle_single_channel(self, row_id: str) -> None:
        for row in self.channel_rows:
            if str(row["id"]) == row_id:
                row["enabled"] = not bool(row["enabled"])
                break
        self._render_channel_rows()
        if self.channels_table.exists(row_id):
            self.channels_table.selection_set(row_id)
            self.channels_table.focus(row_id)

    def _on_channels_table_click(self, event) -> str | None:
        try:
            row_id = self.channels_table.identify_row(event.y)
            col = self.channels_table.identify_column(event.x)
            region = self.channels_table.identify("region", event.x, event.y)
            if not row_id:
                return None
            if region == "cell" and col == "#1":
                self.channels_table.selection_set(row_id)
                self.channels_table.focus(row_id)
                self._toggle_single_channel(row_id)
                return "break"
        except Exception as exc:
            logger.debug("TABLE_CLICK_ERROR: %s", exc)
        return None

    def _on_channels_table_double_click(self, event=None):
        try:
            if event is not None:
                row_id = self.channels_table.identify_row(event.y)
                if row_id:
                    self.channels_table.selection_set(row_id)
                    self.channels_table.focus(row_id)
                    self._selected_channel_id = str(row_id)
                    self._refresh_channel_center()
            self.action_play_selected_channel()
        except Exception as exc:
            logger.debug("TABLE_DOUBLE_CLICK_ERROR: %s", exc)
        return "break"

    def _on_channels_table_context_menu(self, event=None):
        try:
            if event is None:
                return None
            row_id = self.channels_table.identify_row(event.y)
            if not row_id:
                return None
            self.channels_table.selection_set(row_id)
            self.channels_table.focus(row_id)
            self._selected_channel_id = str(row_id)
            self._refresh_channel_center()
            if self._selected_channel_row() is None:
                return None
            self.channel_context_menu.tk_popup(event.x_root, event.y_root)
            return "break"
        except Exception as exc:
            logger.debug("TABLE_CONTEXT_MENU_ERROR: %s", exc)
            return None
        finally:
            try:
                self.channel_context_menu.grab_release()
            except Exception:
                pass

    def _on_channel_selection_changed(self, _event=None) -> None:
        sel = self.channels_table.selection()
        self._selected_channel_id = str(sel[0]) if sel else None
        self._refresh_channel_center()

    def _set_channel_center_actions_state(self, enabled: bool) -> None:
        state = "normal" if enabled else "disabled"
        self.cc_btn_play.config(state=state)
        self.cc_btn_play_vlc.config(state=state)
        self.cc_btn_play_test.config(state=state)
        self.cc_btn_retest.config(state=state)
        self.cc_btn_replace.config(state=state)
        self.cc_btn_copy.config(state=state)

    def _channel_health_from_test(self, status: str, elapsed: float | None = None) -> tuple[str, str]:
        state = str(status or "").strip().upper()
        if not state or state in {"-", "NA", "N/A", "STOPPED"}:
            return "⚫ Netestováno", "Kanál nebyl dosud otestován."
        if state in _DEAD_STATUSES:
            return "🔴 Vyžaduje opravu", "Doporučujeme spustit opravu kanálu."
        if state == "SLOW":
            return "🟠 Doporučena oprava", "Doporučujeme spustit opravu kanálu."
        if state in {"OK", "REDIRECT"}:
            if elapsed is not None and elapsed <= max(1.0, float(self.timeout.get()) * 0.35):
                return "🟢 Výborný", "Není potřeba žádná akce."
            return "🟡 Dobrý", "Není potřeba žádná akce."
        return "🔴 Vyžaduje opravu", "Doporučujeme spustit opravu kanálu."

    def _channel_health_rank(self, status: str, elapsed: float | None = None) -> int:
        state, _ = self._channel_health_from_test(status, elapsed)
        return {
            "⚫ Netestováno": 0,
            "🔴 Vyžaduje opravu": 1,
            "🟠 Doporučena oprava": 2,
            "🟡 Dobrý": 3,
            "🟢 Výborný": 4,
        }.get(state, 0)

    def _channel_health_from_row(self, row: dict[str, object]) -> tuple[str, str]:
        elapsed = row.get("last_test_elapsed") if isinstance(row.get("last_test_elapsed"), (int, float)) else None
        return self._channel_health_from_test(str(row.get("current_status", "-")), elapsed)

    def _selected_channel_snapshot(self, row: dict[str, object]) -> dict[str, object]:
        return {
            "id": str(row.get("id", "")),
            "name": str(row.get("name", "-")) or "-",
            "url": str(row.get("url", "-")) or "-",
            "norm_url": str(row.get("norm_url", "")),
            "extinf": str(row.get("extinf", "")),
            "group": str(row.get("group", "-")) or "-",
            "country": str(row.get("country", "-")) or "-",
            "current_status": str(row.get("current_status", "-")) or "-",
            "last_test_elapsed": row.get("last_test_elapsed"),
            "last_test_time": str(row.get("last_test_time", "-")) or "-",
            "last_error_reason": str(row.get("last_error_reason", "-")) or "-",
        }

    def _set_repair_button_busy(self, busy: bool) -> None:
        if busy:
            self.cc_btn_replace.config(state="disabled")
            return
        row = self._selected_channel_row()
        self.cc_btn_replace.config(state="normal" if row is not None else "disabled")

    def _format_response_time(self, elapsed: float | None) -> str:
        if elapsed is None:
            return "nezměřeno"
        return f"{elapsed:.2f} s".replace(".", ",")

    def _is_replacement_measurably_better(
        self,
        original_status: str,
        original_elapsed: float | None,
        replacement_status: str,
        replacement_elapsed: float | None,
    ) -> bool:
        original_rank = self._channel_health_rank(original_status, original_elapsed)
        replacement_rank = self._channel_health_rank(replacement_status, replacement_elapsed)
        if replacement_rank > original_rank:
            return True
        if replacement_rank < original_rank:
            return False
        if original_elapsed is None or replacement_elapsed is None:
            return False
        threshold = max(0.75, original_elapsed * 0.15)
        return replacement_elapsed <= (original_elapsed - threshold)

    def _restore_original_channel_url(self, row_id: str, original_snapshot: dict[str, object]) -> None:
        row = next((r for r in self.channel_rows if str(r["id"]) == row_id), None)
        if row is None:
            return
        row["url"] = str(original_snapshot.get("url", ""))
        row["norm_url"] = normalize_url(str(original_snapshot.get("url", "")))
        self._render_channel_rows()
        if self.channels_table.exists(row_id):
            self.channels_table.selection_set(row_id)
            self.channels_table.focus(row_id)
            self._selected_channel_id = row_id
            self._refresh_channel_center()

    def _selected_channel_row(self) -> dict[str, object] | None:
        sel = self.channels_table.selection()
        if not sel:
            return None
        sel_id = str(sel[0])
        for row in self.channel_rows:
            if str(row["id"]) == sel_id:
                return row
        return None

    def _clear_channel_center(self) -> None:
        self.channel_center_name_var.set("-")
        self.channel_center_group_var.set("-")
        self.channel_center_country_var.set("-")
        self.channel_center_url_var.set("-")
        self.channel_center_state_var.set("⚫ Netestováno")
        self.channel_center_recommendation_var.set("Kanál nebyl dosud otestován.")
        self.channel_center_last_test_var.set("-")
        self.channel_center_last_reason_var.set("-")
        self._set_channel_center_actions_state(False)

    def _refresh_channel_center(self) -> None:
        row = self._selected_channel_row()
        if row is None:
            self._clear_channel_center()
            return
        self.channel_center_name_var.set(str(row.get("name", "-")) or "-")
        self.channel_center_group_var.set(str(row.get("group", "-")) or "-")
        self.channel_center_country_var.set(str(row.get("country", "-")) or "-")
        self.channel_center_url_var.set(str(row.get("url", "-")) or "-")
        state, recommendation = self._channel_health_from_row(row)
        self.channel_center_state_var.set(state)
        self.channel_center_recommendation_var.set(recommendation)
        self.channel_center_last_test_var.set(str(row.get("last_test_time", "-")) or "-")
        self.channel_center_last_reason_var.set(str(row.get("last_error_reason", "-")) or "-")
        self._set_channel_center_actions_state(True)

    def _run_url_with_default_app(self, url: str) -> None:
        try:
            os.startfile(url)
        except Exception as exc:
            logger.error("PLAY_DEFAULT_FAILED: %s", exc)
            self.ui(messagebox.showerror, "Přehrání", f"Nepodařilo se spustit přehrání streamu.\n\n{exc}")

    def action_play_selected_channel(self) -> None:
        row = self._selected_channel_row()
        if row is None:
            messagebox.showinfo("Vybraný kanál", "Nejprve vyberte kanál.")
            return
        url = str(row.get("url", "")).strip()
        if not url:
            messagebox.showwarning("Přehrání", "Vybraný kanál nemá platnou URL streamu.")
            return
        threading.Thread(target=self._run_url_with_default_app, args=(url,), daemon=True).start()

    def _find_vlc_executable(self) -> str | None:
        path = shutil.which("vlc")
        if path:
            return path
        candidates = [
            str(Path(os.environ.get("ProgramFiles", "")) / "VideoLAN" / "VLC" / "vlc.exe"),
            str(Path(os.environ.get("ProgramFiles(x86)", "")) / "VideoLAN" / "VLC" / "vlc.exe"),
            str(Path.home() / "AppData" / "Local" / "Programs" / "VideoLAN" / "VLC" / "vlc.exe"),
        ]
        for p in candidates:
            if p and Path(p).is_file():
                return p
        return None

    def _run_vlc(self, vlc_path: str, url: str) -> None:
        try:
            subprocess.Popen([vlc_path, url], shell=False)
        except Exception as exc:
            logger.error("PLAY_VLC_FAILED: %s", exc)
            self.ui(messagebox.showerror, "Přehrání ve VLC", f"Nepodařilo se spustit VLC.\n\n{exc}")

    def action_play_selected_channel_vlc(self) -> None:
        row = self._selected_channel_row()
        if row is None:
            messagebox.showinfo("Vybraný kanál", "Nejprve vyberte kanál.")
            return
        url = str(row.get("url", "")).strip()
        if not url:
            messagebox.showwarning("Přehrání ve VLC", "Vybraný kanál nemá platnou URL streamu.")
            return
        vlc_path = self._find_vlc_executable()
        if not vlc_path:
            messagebox.showwarning(
                "Přehrání ve VLC",
                "VLC Media Player nebyl nalezen.\nNainstalujte VLC nebo přidejte 'vlc' do PATH.",
            )
            return
        threading.Thread(target=self._run_vlc, args=(vlc_path, url), daemon=True).start()

    def _play_test_selected_channel_worker(self, row_id: str, channel: Channel) -> None:
        try:
            timeout = max(3, min(5, self.timeout.get()))
            ff = ffprobe_path()
            _, status, reason, elapsed = test(channel, timeout, ff, threading.Event())
            if status not in {"OK", "SLOW", "REDIRECT"}:
                self.ui(self._apply_retest_result, row_id, status, reason, elapsed)
                self.ui(
                    messagebox.showwarning,
                    "Test přehrávání",
                    f"Vybraný kanál nyní není dostupný.\n\nStav: {status}\nDůvod: {reason}",
                )
                self.ui(self.status.set, f"Test přehrávání selhal: {status}")
                self.ui(self.detail.set, channel.name)
                return

            self._run_url_with_default_app(channel.url)
            self.ui(self._apply_retest_result, row_id, status, reason, elapsed)
            self.ui(self.status.set, "Test přehrávání spuštěn")
            self.ui(self.detail.set, channel.name)
        except Exception as exc:
            logger.error("PLAY_TEST_FAILED: %s", exc)
            self.ui(messagebox.showerror, "Test přehrávání", f"Test přehrávání vybraného kanálu selhal.\n\n{exc}")

    def action_play_test_selected_channel(self) -> None:
        row = self._selected_channel_row()
        if row is None:
            messagebox.showinfo("Vybraný kanál", "Nejprve vyberte kanál.")
            return
        url = str(row.get("url", "")).strip()
        if not url:
            messagebox.showwarning("Test přehrávání", "Vybraný kanál nemá platnou URL streamu.")
            return

        channel = Channel(
            extinf=str(row.get("extinf", f"#EXTINF:-1,{row.get('name', 'Unknown')}")),
            url=url,
            name=str(row.get("name", "Unknown")),
        )
        row_id = str(row["id"])
        self.status.set("Test přehrávání: ověřuji dostupnost streamu…")
        self.detail.set(channel.name)
        threading.Thread(target=self._play_test_selected_channel_worker, args=(row_id, channel), daemon=True).start()

    def _apply_retest_result(self, row_id: str, status: str, reason: str, elapsed: float | None) -> None:
        row = next((r for r in self.channel_rows if str(r["id"]) == row_id), None)
        if row is None:
            return
        row["current_status"] = status
        row["last_test_elapsed"] = elapsed
        row["last_test_time"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        row["last_error_reason"] = reason if reason else "-"
        self._render_channel_rows()
        if self.channels_table.exists(row_id):
            self.channels_table.selection_set(row_id)
            self.channels_table.focus(row_id)
            self._selected_channel_id = row_id
            self._refresh_channel_center()

    def _retest_selected_channel_worker(self, row_id: str, channel: Channel) -> None:
        try:
            timeout = max(3, self.timeout.get())
            ff = ffprobe_path()
            _, status, reason, elapsed = test(channel, timeout, ff, threading.Event())
            self.ui(self._apply_retest_result, row_id, status, reason, elapsed)
            self.ui(self.status.set, f"Retest dokončen: {status}")
            self.ui(self.detail.set, channel.name)
        except Exception as exc:
            logger.error("RETEST_FAILED: %s", exc)
            self.ui(messagebox.showerror, "Retest streamu", f"Retest vybraného kanálu selhal.\n\n{exc}")

    def action_retest_selected_channel(self) -> None:
        row = self._selected_channel_row()
        if row is None:
            messagebox.showinfo("Vybraný kanál", "Nejprve vyberte kanál.")
            return
        url = str(row.get("url", "")).strip()
        if not url:
            messagebox.showwarning("Retest streamu", "Vybraný kanál nemá platnou URL streamu.")
            return
        channel = Channel(
            extinf=str(row.get("extinf", f"#EXTINF:-1,{row.get('name', 'Unknown')}")),
            url=url,
            name=str(row.get("name", "Unknown")),
        )
        row_id = str(row["id"])
        self.status.set("Retest vybraného kanálu…")
        self.detail.set(str(row.get("name", "")))
        threading.Thread(target=self._retest_selected_channel_worker, args=(row_id, channel), daemon=True).start()

    def _apply_replacement_to_row(
        self,
        row_id: str,
        replacement: Channel,
        match_type: str,
        provider_name: str,
        test_status: str | None = None,
        elapsed: float | None = None,
        reason: str | None = None,
    ) -> None:
        row = next((r for r in self.channel_rows if str(r["id"]) == row_id), None)
        if row is None:
            return

        new_norm_url = normalize_url(replacement.url)
        for other in self.channel_rows:
            if str(other["id"]) == row_id:
                continue
            if str(other.get("norm_url", "")) == new_norm_url:
                messagebox.showwarning("Oprava kanálu", "Navržená náhrada má duplicitní URL v seznamu kanálů.")
                return
        row["url"] = replacement.url
        row["norm_url"] = normalize_url(replacement.url)
        row["current_status"] = test_status or "OK"
        row["last_test_elapsed"] = elapsed
        row["last_test_time"] = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        row["last_error_reason"] = reason or f"Oprava ({match_type}, {provider_name})"

        self._render_channel_rows()
        if self.channels_table.exists(row_id):
            self.channels_table.selection_set(row_id)
            self.channels_table.focus(row_id)
            self._selected_channel_id = row_id
            self._refresh_channel_center()
        self.status.set("Oprava kanálu provedena")
        self.detail.set(replacement.name)

    def _repair_result_dialog(self, row_id: str, original_snapshot: dict[str, object], comparison: dict[str, object] | None) -> None:
        if comparison is None:
            messagebox.showinfo("Oprava kanálu", "Pro vybraný kanál nebyla nalezena vhodnější náhrada.")
            self.status.set("Oprava kanálu dokončena bez změny")
            self.detail.set(str(original_snapshot.get("name", "")))
            self._set_repair_button_busy(False)
            return

        replacement = comparison["replacement"]
        match_type = str(comparison["match_type"])
        provider_name = str(comparison["provider_name"])
        source_filename = str(comparison["source_filename"])
        original_state = str(comparison["original_state"])
        replacement_state = str(comparison["replacement_state"])
        original_status = str(comparison["original_status"])
        replacement_status = str(comparison["replacement_status"])
        original_elapsed = comparison["original_elapsed"] if isinstance(comparison.get("original_elapsed"), (int, float)) else None
        replacement_elapsed = comparison["replacement_elapsed"] if isinstance(comparison.get("replacement_elapsed"), (int, float)) else None

        confirm = messagebox.askyesno(
            "Oprava kanálu",
            f"Vybraný kanál: {original_snapshot.get('name', '-')}\n"
            f"Původní stav: {original_state} ({original_status})\n"
            f"Původní odezva: {self._format_response_time(original_elapsed)}\n"
            f"Původní URL: {original_snapshot.get('url', '-')}\n\n"
            f"Návrh náhrady: {replacement.name}\n"
            f"Stav náhrady: {replacement_state} ({replacement_status})\n"
            f"Odezva náhrady: {self._format_response_time(replacement_elapsed)}\n"
            f"Nová URL: {replacement.url}\n"
            f"Shoda: {match_type}\n"
            f"Zdroj: {source_filename}\n"
            f"Provider: {provider_name}\n\n"
            "Chcete změnit URL vybraného kanálu?",
        )
        if not confirm:
            self.status.set("Oprava kanálu zrušena")
            self.detail.set(str(original_snapshot.get("name", "")))
            self._set_repair_button_busy(False)
            return

        self.status.set("Oprava kanálu: ověřuji novou URL…")
        self.detail.set(replacement.name)
        threading.Thread(
            target=self._finalize_repair_selected_channel_worker,
            args=(row_id, original_snapshot, comparison),
            daemon=True,
        ).start()

    def _finalize_repair_selected_channel_worker(self, row_id: str, original_snapshot: dict[str, object], comparison: dict[str, object]) -> None:
        try:
            replacement = comparison["replacement"]
            match_type = str(comparison["match_type"])
            provider_name = str(comparison["provider_name"])
            timeout = max(3, self.timeout.get())
            ff = ffprobe_path()

            self.ui(
                self._apply_replacement_to_row,
                row_id,
                replacement,
                match_type,
                provider_name,
                "TESTUJI",
                None,
                f"Ověření nové URL ({match_type}, {provider_name})",
            )

            _, final_status, final_reason, final_elapsed = test(replacement, timeout, ff, threading.Event())
            if final_status not in {"OK", "SLOW", "REDIRECT"}:
                self.ui(self._restore_original_channel_url, row_id, original_snapshot)
                self.ui(
                    self._apply_retest_result,
                    row_id,
                    str(original_snapshot.get("current_status", "-")),
                    str(original_snapshot.get("last_error_reason", "-")),
                    original_snapshot.get("last_test_elapsed") if isinstance(original_snapshot.get("last_test_elapsed"), (int, float)) else None,
                )
                self.ui(
                    messagebox.showerror,
                    "Oprava kanálu",
                    "Nová URL po finálním ověření neprošla testem.\nPůvodní URL byla automaticky obnovena.\n\n"
                    f"Výsledek nové URL: {final_status}\n"
                    f"Důvod: {final_reason}",
                )
                self.ui(self.status.set, "Oprava kanálu selhala, původní URL byla obnovena")
                self.ui(self.detail.set, str(original_snapshot.get("name", "")))
                return

            self.ui(
                self._apply_retest_result,
                row_id,
                final_status,
                final_reason if final_reason else f"Oprava ({match_type}, {provider_name})",
                final_elapsed,
            )
            self.ui(self.status.set, "Oprava kanálu úspěšně dokončena")
            self.ui(self.detail.set, replacement.name)
        except Exception as exc:
            logger.error("REPAIR_FINALIZE_FAILED: %s", exc)
            self.ui(self._restore_original_channel_url, row_id, original_snapshot)
            self.ui(
                self._apply_retest_result,
                row_id,
                str(original_snapshot.get("current_status", "-")),
                str(original_snapshot.get("last_error_reason", "-")),
                original_snapshot.get("last_test_elapsed") if isinstance(original_snapshot.get("last_test_elapsed"), (int, float)) else None,
            )
            self.ui(
                messagebox.showerror,
                "Oprava kanálu",
                f"Při finálním ověření nové URL došlo k chybě.\nPůvodní URL byla obnovena.\n\n{exc}",
            )
            self.ui(self.status.set, "Oprava kanálu selhala")
            self.ui(self.detail.set, str(original_snapshot.get("name", "")))
        finally:
            self.ui(self._set_repair_button_busy, False)

    def _repair_selected_channel_worker(self, row_id: str, channel: Channel, working_urls: frozenset[str], original_snapshot: dict[str, object]) -> None:
        handoff_to_dialog = False
        try:
            timeout = max(3, self.timeout.get())
            ff = ffprobe_path()
            _, original_status, original_reason, original_elapsed = test(channel, timeout, ff, threading.Event())
            original_snapshot["current_status"] = original_status
            original_snapshot["last_test_elapsed"] = original_elapsed
            original_snapshot["last_error_reason"] = original_reason if original_reason else "-"
            self.ui(self._apply_retest_result, row_id, original_status, original_reason, original_elapsed)
            if self._channel_health_rank(original_status, original_elapsed) >= 3:
                self.ui(
                    messagebox.showinfo,
                    "Oprava kanálu",
                    f"Původní stream je v pořádku.\n\nStav: {self._channel_health_from_test(original_status, original_elapsed)[0]}\nDůvod: {original_reason}",
                )
                self.ui(self.status.set, "Kanál je v pořádku, oprava není potřeba")
                self.ui(self.detail.set, channel.name)
                return
            self.ui(self.status.set, "Oprava kanálu: hledám vhodnou náhradu…")
            self.ui(self.detail.set, channel.name)
            replacement_service = ReplacementService(providers=[
                LocalFileProvider(
                    source_dir=_REPLACEMENT_SOURCES_DIR,
                    timeout=timeout,
                    ffprobe=ff,
                    stop_event=threading.Event(),
                )
            ])
            result = replacement_service.find(channel, working_urls)
            if result is None:
                self.ui(self._repair_result_dialog, row_id, original_snapshot, None)
                return

            replacement, match_type, provider_name, metadata = result
            source_filename = metadata[0] if metadata else "-"
            self.ui(self.status.set, "Oprava kanálu: porovnávám původní a novou URL…")
            self.ui(self.detail.set, replacement.name)
            _, replacement_status, replacement_reason, replacement_elapsed = test(replacement, timeout, ff, threading.Event())

            if replacement_status not in {"OK", "SLOW", "REDIRECT"}:
                self.ui(
                    messagebox.showwarning,
                    "Oprava kanálu",
                    "Navržená náhrada při ověření selhala.\nPůvodní kanál zůstal beze změny.",
                )
                self.ui(self.status.set, "Oprava kanálu dokončena bez změny")
                self.ui(self.detail.set, channel.name)
                return

            if not self._is_replacement_measurably_better(
                original_status,
                original_elapsed,
                replacement_status,
                replacement_elapsed,
            ):
                self.ui(
                    messagebox.showinfo,
                    "Oprava kanálu",
                    "Nebyla nalezena měřitelně lepší náhrada.\nPůvodní URL zůstává zachována.",
                )
                self.ui(self.status.set, "Oprava kanálu dokončena bez změny")
                self.ui(self.detail.set, channel.name)
                return

            handoff_to_dialog = True
            self.ui(
                self._repair_result_dialog,
                row_id,
                original_snapshot,
                {
                    "replacement": replacement,
                    "match_type": match_type,
                    "provider_name": provider_name,
                    "source_filename": source_filename,
                    "original_status": original_status,
                    "original_reason": original_reason,
                    "original_elapsed": original_elapsed,
                    "original_state": self._channel_health_from_test(original_status, original_elapsed)[0],
                    "replacement_status": replacement_status,
                    "replacement_reason": replacement_reason,
                    "replacement_elapsed": replacement_elapsed,
                    "replacement_state": self._channel_health_from_test(replacement_status, replacement_elapsed)[0],
                },
            )
        except Exception as exc:
            logger.error("REPAIR_FAILED: %s", exc)
            self.ui(messagebox.showerror, "Oprava kanálu", f"Oprava vybraného kanálu selhala.\n\n{exc}")
            self.ui(self.status.set, "Oprava kanálu selhala")
            self.ui(self.detail.set, channel.name)
        finally:
            if not handoff_to_dialog:
                self.ui(self._set_repair_button_busy, False)

    def action_repair_selected_channel(self) -> None:
        row = self._selected_channel_row()
        if row is None:
            messagebox.showinfo("Vybraný kanál", "Nejprve vyberte kanál.")
            return
        url = str(row.get("url", "")).strip()
        if not url:
            messagebox.showwarning("Oprava kanálu", "Vybraný kanál nemá platnou URL streamu.")
            return

        channel = Channel(
            extinf=str(row.get("extinf", f"#EXTINF:-1,{row.get('name', 'Unknown')}")),
            url=url,
            name=str(row.get("name", "Unknown")),
        )
        row_id = str(row["id"])
        working_urls: set[str] = {
            str(r.get("norm_url", ""))
            for r in self.channel_rows
            if bool(r.get("enabled", True)) and str(r.get("id")) != row_id
        }

        self._set_repair_button_busy(True)
        self.status.set("Oprava kanálu: testuji původní stream…")
        self.detail.set(channel.name)
        threading.Thread(
            target=self._repair_selected_channel_worker,
            args=(row_id, channel, frozenset(working_urls), self._selected_channel_snapshot(row)),
            daemon=True,
        ).start()

    def action_find_replacement_selected_channel(self) -> None:
        self.action_repair_selected_channel()

    def action_copy_selected_channel_url(self) -> None:
        row = self._selected_channel_row()
        if row is None:
            messagebox.showinfo("Vybraný kanál", "Nejprve vyberte kanál.")
            return
        url = str(row.get("url", "")).strip()
        if not url:
            messagebox.showwarning("Kopírovat URL", "Vybraný kanál nemá platnou URL streamu.")
            return
        try:
            self.clipboard_clear()
            self.clipboard_append(url)
            self.update_idletasks()
            self.status.set("URL zkopírována do schránky")
            self.detail.set(str(row.get("name", "")))
        except Exception as exc:
            logger.error("CLIPBOARD_COPY_FAILED: %s", exc)
            messagebox.showerror("Kopírovat URL", f"Nepodařilo se zkopírovat URL.\n\n{exc}")

    def _set_channels_enabled(self, enabled: bool) -> None:
        for row in self.channel_rows:
            row["enabled"] = enabled
        self._render_channel_rows()

    def select_all_channels(self) -> None:
        self._set_channels_enabled(True)

    def deselect_all_channels(self) -> None:
        self._set_channels_enabled(False)

    def invert_channel_selection(self) -> None:
        for row in self.channel_rows:
            row["enabled"] = not bool(row["enabled"])
        self._render_channel_rows()

    def _selected_channels_for_source(self, source_id: str, channels: list[Channel]) -> list[Channel]:
        if not self.channel_rows:
            return channels

        selected_urls = {
            str(row["norm_url"])
            for row in self.channel_rows
            if bool(row["enabled"]) and str(row["source_id"]) == source_id
        }
        if not selected_urls:
            return []
        return [c for c in channels if normalize_url(c.url) in selected_urls]

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

    def ui(self, func, *args, **kwargs) -> None:
        self.after(0, lambda: func(*args, **kwargs))

    def stop(self) -> None:
        if self.running:
            self.stopped_by_user = True
            self.stop_event.set()
            self.status.set("Zastavuji…")
            self.write("Zastavuji po dokončení právě běžících testů…", "info")
            logger.info("Uživatel požádal o zastavení testu.")

    def _begin_run(self, mode: str) -> None:
        if self.running:
            return
        if mode == "single" and not self.file:
            messagebox.showwarning("Chybí playlist", "Nejprve vyber playlist.")
            return
        if mode == "batch":
            enabled_sources = self._enabled_batch_sources()
            if not enabled_sources:
                messagebox.showwarning("Chybí zdroje", "Nejsou žádné povolené zdroje v Playlist Sources.")
                return

        self.refresh_channel_selection(mode)
        if self.channel_preview_error:
            messagebox.showerror("Načtení kanálů", f"Nelze načíst kanály:\n{self.channel_preview_error}")
            return

        selected_count = sum(1 for row in self.channel_rows if bool(row["enabled"]))
        if selected_count == 0:
            messagebox.showwarning("Výběr kanálů", "Není vybrán žádný kanál pro zpracování.")
            return

        self.run_mode = mode
        self.stopped_by_user = False
        self.return_btn.grid_remove()
        self.running = True
        self.stop_event.clear()
        self.clear_log()
        self.reset_stats()
        self._set_final_playlist_result(None, 0)
        self.last_protocol = None
        self.start_btn.config(state="disabled")
        self.batch_btn.config(state="disabled")
        self.stop_btn.config(state="normal")
        self.open_protocol_btn.config(state="disabled")
        self._apply_responsive_layout()
        threading.Thread(target=self.process, daemon=True).start()

    def start_single(self) -> None:
        self._begin_run("single")

    def start_batch(self) -> None:
        self._begin_run("batch")

    def start(self) -> None:
        """Backward-compatible entrypoint used by older launch flows."""
        self.start_single()

    def reset_stats(self) -> None:
        for key, var in self.stats.items():
            var.set("0,00/s" if key == "SPEED" else "00:00" if key == "ETA" else "0")
        self.progress.set(0)
        self.status.set("Připravuji kontrolu…")
        self.detail.set("Načítání playlistu")

    def reset_gui(self) -> None:
        """Return to idle state after a user-initiated STOP."""
        self.return_btn.grid_remove()
        self.clear_log()
        self.reset_stats()
        self.stopped_by_user = False
        self.write(f"Připraveno: {self.file.name if self.file else 'Není vybrán playlist'}", "info")
        logger.info("Vráceno do výchozího stavu.")

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
        self.detail.set(f"Ponecháno: {counts['OK'] + counts['SLOW'] + counts['REDIRECT']}")

    def process(self) -> None:
        started_total = time.monotonic()
        global_summary_path: Path | None = None
        merged_final_channels: list[Channel] = []

        try:
            stamp = datetime.now().strftime("%Y%m%d_%H-%M-%S")
            _OUTPUT_DIR.mkdir(parents=True, exist_ok=True)
            if self.run_mode == "batch":
                enabled_sources = self._enabled_batch_sources()
                if not enabled_sources:
                    raise RuntimeError("Nejsou žádné povolené zdroje v Playlist Sources.")
                inputs = enabled_sources
                output_root = _OUTPUT_DIR / f"LUIGI_BATCH_OUTPUT_{stamp}"
                playlists_dir = output_root / "playlists"
                logs_dir = output_root / "logs"
                output_root.mkdir(parents=True, exist_ok=True)
                playlists_dir.mkdir(parents=True, exist_ok=True)
                logs_dir.mkdir(parents=True, exist_ok=True)
                self.last_output = output_root
                global_summary_path = output_root / "global_summary.log"
                self.last_protocol = global_summary_path
            else:
                if self.file is None:
                    raise RuntimeError("Není vybrán žádný playlist.")
                inputs = [self.file]
                output_root = _OUTPUT_DIR / f"LUIGI_SINGLE_OUTPUT_{stamp}"
                output_root.mkdir(parents=True, exist_ok=True)
                playlists_dir = output_root
                logs_dir = output_root
                self.last_output = output_root

            total_files = len(inputs)

            def append_global(msg: str) -> None:
                if global_summary_path is None:
                    return
                with global_summary_path.open("a", encoding="utf-8") as fh:
                    fh.write(msg + "\n")

            if self.run_mode == "batch":
                append_global(f"{APP_NAME} {VERSION}")
                append_global(f"Batch started: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")
                append_global(f"Input files: {total_files}")
                append_global("-" * 64)

            done_files = 0
            failed_files = 0

            for file_index, source_item in enumerate(inputs, 1):
                if self.stop_event.is_set():
                    append_global("Batch stopped by user.")
                    break

                run_handler: logging.Handler | None = None
                try:
                    file_stamp = f"{stamp}_{file_index:03d}"
                    playlist_stamp = datetime.now().strftime("%Y%m%d_%H-%M-%S")
                    if self.run_mode == "batch":
                        src_def = source_item
                        src_name = str(src_def.get("name", "Unnamed source"))
                        src_id = self._source_key(str(src_def.get("type", "Local")), str(src_def.get("location", "")))
                        src = self._resolve_source_to_path(src_def, file_stamp)
                        self._set_source_state(src_def, "Running")
                        self.save_sources()
                        self.ui(self.refresh_sources_table)
                    else:
                        src = source_item
                        src_name = src.name
                        src_id = self._source_key("Local", str(src))

                    run_log = logs_dir / f"{src.stem}.log"
                    if run_log.exists():
                        n = 2
                        while True:
                            candidate = logs_dir / f"{src.stem}_{n}.log"
                            if not candidate.exists():
                                run_log = candidate
                                break
                            n += 1
                    run_handler = logging.FileHandler(run_log, encoding="utf-8")
                    run_handler.setLevel(logging.DEBUG)
                    run_handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
                    logging.getLogger().addHandler(run_handler)
                    self.last_protocol = run_log
                    logger.info("FILE_OK: Detailní log spuštění → %s", run_log)

                    remaining_files = max(0, total_files - file_index)
                    self.ui(self.status.set, f"Soubor {file_index}/{total_files} | Playlist: {src_name} | Zbývá souborů: {remaining_files}")
                    self.ui(self.detail.set, f"Celkový čas: {fmt_time(time.monotonic() - started_total)}")
                    self.ui(self.write, f"[{file_index}/{total_files}] Zpracování: {src_name}", "title")

                    backup = playlists_dir / f"{src.stem}_backup_{file_stamp}.m3u"
                    shutil.copy2(src, backup)
                    logger.info("Záloha vytvořena: %s", backup)

                    items = parse(src)
                    unique, dups = dedupe(items)
                    selected_unique = self._selected_channels_for_source(src_id, unique)
                    logger.info("Načteno: %d streamů z '%s'; duplicity: %d", len(items), src_name, len(dups))
                    logger.info("Výběr kanálů: %d z %d", len(selected_unique), len(unique))

                    unique = selected_unique

                    self.ui(self.stats["TOTAL"].set, str(len(items)))
                    self.ui(self.write, f"Načteno: {len(items)} streamů", "title")
                    self.ui(self.write, f"Záloha vytvořena: {backup.name}", "info")
                    self.ui(self.write, f"Duplicity odstraněny: {len(dups)}", "info")
                    self.ui(self.write, f"Vybráno kanálů: {len(unique)}", "info")

                    results: list[tuple[Channel, str, str, float]] = []
                    working: list[Channel] = []
                    counts: Counter[str] = Counter()
                    replacements: list[ReplacementResult] = []

                    if self.test_var.get():
                        ff = ffprobe_path()
                        workers = max(1, min(40, self.workers.get()))
                        timeout = max(3, self.timeout.get())
                        logger.info("Spouštím testy: metoda=%s workers=%d timeout=%ds", 'ffprobe' if ff else 'HTTP', workers, timeout)
                        self.ui(self.write, f"Metoda: {'ffprobe' if ff else 'HTTP'} | Současně: {workers} | Timeout: {timeout}s", "info")

                        started = time.monotonic()
                        with ThreadPoolExecutor(max_workers=workers) as ex:
                            futures = [ex.submit(test, c, timeout, ff, self.stop_event) for c in unique]

                            for i, future in enumerate(as_completed(futures), 1):
                                c, status, reason, elapsed = future.result()
                                results.append((c, status, reason, elapsed))
                                counts[status] += 1
                                if status in ("AUTH_REQUIRED", "GEO_BLOCKED"):
                                    counts["AUTH_OR_GEO"] += 1
                                if status == "HTTP_404":
                                    counts["NOT_FOUND"] += 1

                                if status in ("OK", "SLOW", "REDIRECT"):
                                    working.append(c)
                                elif status != "STOPPED":
                                    logger.debug("STREAM_ERROR [%s]: '%s' | %s | %s", status, c.name, c.url, reason)

                                elapsed_all = max(0.01, time.monotonic() - started)
                                speed = i / elapsed_all
                                eta = (len(unique) - i) / speed if speed else 0
                                removed = sum(counts[x] for x in _DEAD_STATUSES)

                                self.ui(self.update_stats, i, len(unique), counts, removed, speed, eta)
                                overall_progress = ((file_index - 1) + (i / max(1, len(unique)))) / max(1, total_files) * 100
                                self.ui(self.progress.set, overall_progress)
                                remaining_files = max(0, total_files - file_index)
                                self.ui(self.status.set, f"Soubor {file_index}/{total_files} | Playlist: {src_name} | Kanál {i}/{len(unique)}")
                                self.ui(self.detail.set, f"Celkový čas: {fmt_time(time.monotonic() - started_total)} | Zbývá souborů: {remaining_files}")

                                symbol = {
                                    "OK": "✔", "SLOW": "⚠", "TIMEOUT": "⏳",
                                    "REDIRECT": "↪", "AUTH_OR_GEO": "🔒", "AUTH_REQUIRED": "🔒", "GEO_BLOCKED": "🌍",
                                    "NOT_FOUND": "404", "HTTP_404": "404",
                                    "DNS_ERROR": "🌐", "CONNECTION_REFUSED": "🚫",
                                    "OTHER_ERROR": "✖", "STOPPED": "■"
                                }.get(status, "•")
                                label = {
                                    "OK": "OK", "SLOW": "Pomalé", "TIMEOUT": "Timeout",
                                    "REDIRECT": "Redirect", "AUTH_OR_GEO": "Auth/GEO", "AUTH_REQUIRED": "Authentication required",
                                    "GEO_BLOCKED": "Geo blocked", "NOT_FOUND": "404", "HTTP_404": "HTTP 404",
                                    "DNS_ERROR": "DNS chyba", "CONNECTION_REFUSED": "Connection refused",
                                    "OTHER_ERROR": "Other errors", "STOPPED": "Přerušeno"
                                }.get(status, status)
                                tag = "ok" if status in ("OK", "REDIRECT") else "slow" if status == "SLOW" else "info" if status == "STOPPED" else "error"
                                self.ui(self.write, f"{symbol} {c.name} | {label} | {reason}", tag)

                                if self.stop_event.is_set():
                                    for pending in futures:
                                        pending.cancel()
                                    break
                    else:
                        working = unique
                        overall_progress = (file_index / max(1, total_files)) * 100
                        self.ui(self.progress.set, overall_progress)
                        self.ui(self.stats["TESTED"].set, str(len(unique)))
                        remaining_files = max(0, total_files - file_index)
                        self.ui(self.status.set, f"Soubor {file_index}/{total_files} | Playlist: {src_name} | Test vypnut")
                        self.ui(self.detail.set, f"Celkový čas: {fmt_time(time.monotonic() - started_total)} | Zbývá souborů: {remaining_files}")

                    if self.test_var.get() and results:
                        replacement_service = ReplacementService(providers=[
                            LocalFileProvider(
                                source_dir=_REPLACEMENT_SOURCES_DIR,
                                timeout=timeout,
                                ffprobe=ff,
                                stop_event=self.stop_event,
                            )
                        ])
                        working_urls: set[str] = {normalize_url(c.url) for c in working}
                        for c, status, reason, _ in results:
                            if status not in _DEAD_STATUSES:
                                continue
                            res = replacement_service.find(c, frozenset(working_urls))
                            if res is not None:
                                repl_channel, match_type, provider_name, metadata = res
                                source_filename = metadata[0] if metadata else "unknown"
                                test_status = metadata[1] if metadata else "unknown"
                                rr = ReplacementResult(
                                    original=c,
                                    replacement=repl_channel,
                                    match_type=match_type,
                                    provider_name=provider_name,
                                    dead_status=status,
                                    source_filename=source_filename,
                                    test_status=test_status,
                                )
                                working.append(repl_channel)
                                working_urls.add(normalize_url(repl_channel.url))
                                replacements.append(rr)
                                logger.info(
                                    "REPLACED: '%s' → '%s' [%s via %s]",
                                    c.name, repl_channel.name, match_type, provider_name,
                                )
                                self.ui(self.write, f"♻ {c.name} → {repl_channel.name} [{match_type}]", "slow")

                    temporarily_unavailable: list[tuple[Channel, str, str, str]] = []
                    replaced_urls = {normalize_url(rr.original.url) for rr in replacements}
                    for c, status, reason, _ in results:
                        if status not in _DEAD_STATUSES:
                            continue
                        if normalize_url(c.url) in replaced_urls:
                            continue
                        modified_name = f"{c.name} 🔶 Dočasně nedostupný"
                        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                        attrs_dict = parse_extinf_attrs(c.extinf)
                        attrs_str = " ".join(f'{k}="{v}"' for k, v in attrs_dict.items())
                        if attrs_str:
                            new_extinf = f"#EXTINF:-1,{attrs_str},{modified_name}\n# LUIGI_STATUS=TEMPORARILY_UNAVAILABLE\n# LAST_TEST={timestamp}\n# LAST_REASON={status}"
                        else:
                            new_extinf = f"#EXTINF:-1,{modified_name}\n# LUIGI_STATUS=TEMPORARILY_UNAVAILABLE\n# LAST_TEST={timestamp}\n# LAST_REASON={status}"
                        modified_channel = Channel(extinf=new_extinf, url=UNAVAILABLE_STREAM_URL, name=modified_name)
                        working.append(modified_channel)
                        temporarily_unavailable.append((c, status, reason, timestamp))
                        logger.info("TEMPORARILY_UNAVAILABLE: '%s' [%s]", c.name, status)

                    clean = playlists_dir / f"{src.stem}_LUIGI_OK_{playlist_stamp}.m3u"
                    save_m3u(clean, working)
                    merged_final_channels.extend(working)

                    duration = time.monotonic() - started_total
                    output_channels = len(working) if not results else (
                        counts['OK'] + counts['SLOW'] + counts['REDIRECT'] + len(replacements) + len(temporarily_unavailable)
                    )
                    really_removed = len(unique) - output_channels if unique else 0
                    success = (output_channels / len(unique) * 100) if unique else 0
                    tested_total = sum(1 for _, st, _, _ in results if st != "STOPPED")

                    dead_channels = sum(counts[x] for x in _DEAD_STATUSES)
                    auth_geo = counts["AUTH_REQUIRED"] + counts["GEO_BLOCKED"]
                    logger.info("=" * 64)
                    logger.info("PLAYLIST REPORT")
                    logger.info("Playlist information: %s", src_name)
                    logger.info("Processing date and time: %s", datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
                    logger.info("Total channels: %d", len(items))
                    logger.info("Tested channels: %d", tested_total)
                    logger.info("Working channels: %d", counts["OK"] + counts["REDIRECT"])
                    logger.info("Slow channels: %d", counts["SLOW"])
                    logger.info("Timeout channels: %d", counts["TIMEOUT"])
                    logger.info("Authentication / Geo blocked: %d", auth_geo)
                    logger.info("Dead channels: %d", dead_channels)
                    logger.info("Removed duplicates: %d", len(dups))
                    if replacements:
                        logger.info("Replacement information: %d", len(replacements))
                        for rr in replacements:
                            logger.info(
                                "REPLACED | %s -> %s | match=%s | source=%s | dead=%s | repl=%s",
                                rr.original.name,
                                rr.replacement.name,
                                rr.match_type,
                                rr.source_filename,
                                rr.dead_status,
                                rr.test_status,
                            )
                    else:
                        logger.info("Replacement information: 0")
                    logger.info("Removed channels: %d", really_removed)
                    logger.info("Temporarily unavailable channels: %d", len(temporarily_unavailable))
                    logger.info(
                        "Final statistics: output=%d retained=%.2f%% replacements=%d temp_unavailable=%d",
                        output_channels,
                        success,
                        len(replacements),
                        len(temporarily_unavailable),
                    )
                    logger.info("Processing duration: %s", fmt_time(duration))
                    logger.info("Backup playlist: %s", backup)
                    logger.info("Cleaned playlist: %s", clean)
                    logger.info("=" * 64)

                    if self.run_mode == "batch":
                        self._set_source_state(src_def, "OK", touch_update=True)
                        self.save_sources()
                        self.ui(self.refresh_sources_table)

                    if self.run_mode == "batch":
                        append_global(
                            f"OK {file_index}/{total_files} | {src_name} | loaded={len(items)} tested={tested_total} "
                            f"ok={counts['OK']} slow={counts['SLOW']} redirect={counts['REDIRECT']} exported={len(working)} out={clean}"
                        )
                    done_files += 1

                    self.ui(self.write, f"Výstup: {clean.name}", "title")

                except Exception as per_file_exc:
                    failed_files += 1
                    if self.run_mode == "batch" and isinstance(source_item, dict):
                        self._set_source_state(source_item, f"ERROR: {per_file_exc}")
                        self.save_sources()
                        self.ui(self.refresh_sources_table)
                        src_name = str(source_item.get("name", "Unknown"))
                    else:
                        src_name = str(source_item)
                    logger.exception("Chyba při zpracování souboru '%s'", src_name)
                    if self.run_mode == "batch":
                        append_global(f"FAIL {file_index}/{total_files} | {src_name} | {per_file_exc}")
                    self.ui(self.write, f"CHYBA v souboru {src_name}: {per_file_exc}", "error")
                    continue
                finally:
                    if run_handler is not None:
                        logging.getLogger().removeHandler(run_handler)
                        run_handler.close()

            batch_elapsed = fmt_time(time.monotonic() - started_total)
            if self.run_mode == "batch":
                append_global("-" * 64)
                append_global(
                    f"Batch finished: processed={done_files} failed={failed_files} total={total_files} elapsed={batch_elapsed}"
                )

            final_playlist_path: Path | None = None
            final_channels = 0
            if merged_final_channels:
                merged_unique, _ = dedupe(merged_final_channels)
                final_playlist_path = output_root / f"FINAL_LUIGI_PLAYLIST_{stamp}.m3u"
                save_m3u(final_playlist_path, merged_unique)
                final_channels = len(merged_unique)
                logger.info("FINÁLNÍ PLAYLIST: %s | kanálů=%d", final_playlist_path, final_channels)
                if self.run_mode == "batch":
                    append_global(f"Final merged playlist: {final_playlist_path} | channels={final_channels}")
                self.ui(self.write, f"Finální playlist: {final_playlist_path.name}", "title")
                self.ui(self.write, f"Cesta: {final_playlist_path}", "info")
                self.ui(self.write, f"Počet kanálů: {final_channels}", "info")

            self.last_output = output_root
            self.final_playlist = final_playlist_path
            self.final_channels = final_channels
            self.ui(self._set_final_playlist_result, final_playlist_path, final_channels)
            self.ui(self.progress.set, 100)
            self.ui(self.status.set, "Dokončeno")
            self.ui(self.detail.set, f"Soubory: {done_files}/{total_files} | Chyby: {failed_files} | Čas: {batch_elapsed}")
            if self.last_protocol and self.last_protocol.exists():
                self.ui(self.open_protocol_btn.config, state="normal")
            if self.run_mode == "batch":
                self.ui(
                    messagebox.showinfo,
                    "Kontrola dokončena",
                    f"Zpracováno souborů: {done_files}/{total_files}\n"
                    f"Souborů s chybou: {failed_files}\n"
                    f"Doba: {batch_elapsed}\n\n"
                    f"Finální playlist:\n{final_playlist_path if final_playlist_path else 'Nevytvořen'}\n"
                    f"Počet kanálů: {final_channels}\n\n"
                    f"Batch výstup:\n{output_root}\n\n"
                    f"Global log:\n{global_summary_path}",
                )
            else:
                self.ui(
                    messagebox.showinfo,
                    "Kontrola dokončena",
                    f"Playlist: {inputs[0].name}\n"
                    f"Doba: {batch_elapsed}\n"
                    f"Finální playlist:\n{final_playlist_path if final_playlist_path else 'Nevytvořen'}\n"
                    f"Počet kanálů: {final_channels}\n\n"
                    f"Výstup:\n{output_root}",
                )

        except Exception as exc:
            logger.exception("Neočekávaná chyba při zpracování")
            self.ui(messagebox.showerror, "Chyba", str(exc))
            self.ui(self.write, f"CHYBA: {exc}", "error")
            self.ui(self.status.set, "Chyba")
        finally:
            self.running = False
            self.ui(self.start_btn.config, state="normal")
            self.ui(self.batch_btn.config, state="normal")
            self.ui(self.stop_btn.config, state="disabled")
            if self.stopped_by_user:
                self.ui(self.return_btn.grid)
                self.ui(self._apply_responsive_layout)
                self.ui(self.status.set, "Zastaveno uživatelem")
                self.ui(self.write, "Stiskněte 'Vrátit' pro návrat do výchozího stavu.", "info")
                logger.info("Čekám na potvrzení od uživatele (Vrátit).")

    def open_output(self) -> None:
        if not self.last_output or not self.last_output.exists():
            messagebox.showinfo("Výstupní složka", "Zatím nebyla vytvořena žádná výstupní složka.")
            return
        os.startfile(self.last_output)

    def _set_final_playlist_result(self, path: Path | None, channels: int) -> None:
        self.final_playlist = path
        self.final_channels = channels
        if path is None:
            self.final_name_var.set("-")
            self.final_path_var.set("-")
            self.final_count_var.set("0")
            self.open_final_btn.config(state="disabled")
            self.open_final_folder_btn.config(state="disabled")
            self.save_final_as_btn.config(state="disabled")
            return

        self.final_name_var.set(path.name)
        self.final_path_var.set(str(path))
        self.final_count_var.set(str(channels))
        state = "normal" if path.exists() else "disabled"
        self.open_final_btn.config(state=state)
        self.open_final_folder_btn.config(state=state)
        self.save_final_as_btn.config(state=state)

    def open_protocol(self) -> None:
        if not self.last_protocol or not self.last_protocol.exists():
            messagebox.showinfo("Protokol", "Zatím nebyl vytvořen žádný protokol.")
            return
        os.startfile(self.last_protocol)

    def open_final_playlist(self) -> None:
        if not self.final_playlist or not self.final_playlist.exists():
            messagebox.showinfo("Hotový playlist", "Finální playlist zatím není k dispozici.")
            return
        os.startfile(self.final_playlist)

    def open_final_playlist_folder(self) -> None:
        if not self.final_playlist or not self.final_playlist.exists():
            messagebox.showinfo("Otevřít složku", "Finální playlist zatím není k dispozici.")
            return
        try:
            subprocess.run(["explorer.exe", "/select,", str(self.final_playlist)], check=False)
        except Exception:
            os.startfile(self.final_playlist.parent)

    def save_final_playlist_as(self) -> None:
        if not self.final_playlist or not self.final_playlist.exists():
            messagebox.showinfo("Uložit playlist jako", "Finální playlist zatím není k dispozici.")
            return

        target = filedialog.asksaveasfilename(
            title="Uložit playlist jako...",
            defaultextension=".m3u",
            initialfile=self.final_playlist.name,
            filetypes=[("M3U playlist", "*.m3u"), ("M3U8 playlist", "*.m3u8"), ("Všechny soubory", "*.*")],
        )
        if not target:
            return

        target_path = Path(target)
        try:
            target_path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(self.final_playlist, target_path)
            self.write(f"Playlist uložen jako: {target_path}", "ok")
            messagebox.showinfo("Uložit playlist jako", f"Playlist byl uložen:\n{target_path}")
        except OSError as exc:
            logger.error("FILE_ERROR: Nelze uložit playlist jako '%s': %s", target_path, exc)
            messagebox.showerror("Uložit playlist jako", f"Nelze uložit playlist:\n{target_path}\n\n{exc}")

    def on_close(self) -> None:
        if self.running:
            if not messagebox.askyesno("Ukončit program", "Kontrola stále běží. Opravdu ukončit program?"):
                return
            self.stop_event.set()
        self._save_window_geometry()
        self.destroy()


if __name__ == "__main__":
    setup_logging()
    enable_windows_dpi_awareness()
    App().mainloop()

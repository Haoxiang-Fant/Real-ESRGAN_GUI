"""Real-ESRGAN GUI — Bauhaus reconstruction.

The interface is drawn on a single Tk canvas in the design sheet's own coordinate
space (4400 x 3027) and scaled uniformly to the window, so every panel, stroke and
glyph keeps the layout ratio of 页面设计/*.png.

Typography: one Chinese family and one Latin family, selectable in 个性化设置.
The bundled OPPO Sans files are the default; users may add font files of their
own, and files sharing one typographic family (multiple weights) are treated as
a single set from which each text role picks the nearest weight. Both families
are registered process-privately, so the shipped app never depends on the
registry.

The engine pipeline (`App._run_batches`) is the verified one: one engine process
per folder, round-robin output polling, and the two progress bars keep their
meaning — overall = finished images / total, item = percent of the image in
flight.
"""
import ctypes
import json
import os
import platform
import queue
import re
import shutil
import subprocess
import sys
import threading
import time
import tkinter as tk
import tkinter.font as tkfont
from pathlib import Path
from tkinter import filedialog

# --------------------------------------------------------------------------- #
# Bundled fonts and per-script roles
# --------------------------------------------------------------------------- #
FONT_FILES = {
    "cn_bold": "OPPOSans-B.ttf",
    "cn_heavy": "OPPOSans-H.ttf",
    "cn_regular": "OPPOSans-R.ttf",
}
DEFAULT_FONT_FILE = "OPPOSans-R.ttf"

# Each role draws with the selected file of its script, unmodified (never Tk
# synthetic bold). When that file is a regular weight and its own family ships
# a real bold face (bundled OPPO R/B/H do), bold/heavy roles borrow it — that
# is exactly how the design sheet was typeset.
ROLE_SCRIPT = {"cn_bold": "cn", "cn_heavy": "cn", "cn_regular": "cn",
               "en_bold": "en", "en_light": "en"}
ROLE_WEIGHT = {"cn_regular": 400, "cn_bold": 700, "cn_heavy": 900,
               "en_light": 300, "en_bold": 700}
WEIGHT_BY_NAME = {"thin": 100, "extralight": 200, "light": 300, "regular": 400,
                  "medium": 500, "semibold": 600, "demibold": 600, "bold": 700,
                  "extrabold": 800, "black": 900, "heavy": 900}


def font_dir():
    if getattr(sys, "frozen", False):
        base = Path(getattr(sys, "_MEIPASS", Path(sys.executable).parent))
        if (base / "fonts").is_dir():
            return base / "fonts"
        return Path(sys.executable).parent / "fonts"
    return Path(__file__).resolve().parent / "fonts"


def register_fonts():
    """Register the bundled faces for this process only (FR_PRIVATE)."""
    directory = font_dir()
    loaded = []
    for name in FONT_FILES.values():
        path = directory / name
        if path.is_file() and ctypes.windll.gdi32.AddFontResourceExW(str(path), 0x10, 0):
            loaded.append(name)
    return loaded


def _u16(data, offset):
    return (data[offset] << 8) | data[offset + 1]


def _u32(data, offset):
    return int.from_bytes(data[offset:offset + 4], "big")


def read_font_faces(path):
    """(family, weight, tk_name) declared by a ttf/otf/ttc, or None.

    family = typographic family (name ID 16) when present, else ID 1.
    tk_name = ID 1, the name Tk/GDI actually enumerate per weight file.
    Weight comes from the subfamily keyword because some vendors ship a bogus
    OS/2 usWeightClass (bundled OPPO files all say 400). Windows UTF-16 name
    records are preferred; Macintosh/symbolic records are a fallback so user
    uploads that only carry those still resolve.
    # ponytail: ttc collections read the first face only; split them if a
    # multi-family collection ever shows up in user uploads.
    """
    try:
        data = path.read_bytes()
        base = _u32(data, 12) if data[:4] == b"ttcf" else 0
        tables = {}
        for index in range(_u16(data, base + 4)):
            entry = base + 12 + 16 * index
            tables[data[entry:entry + 4]] = _u32(data, entry + 8)
        name_off = tables.get(b"name")
        if not name_off:
            return None
        records = {}
        count, storage = _u16(data, name_off + 2), name_off + _u16(data, name_off + 4)
        for index in range(count):
            record = name_off + 6 + 12 * index
            platform, encoding, name_id = (_u16(data, record), _u16(data, record + 2),
                                           _u16(data, record + 6))
            length, offset = _u16(data, record + 8), _u16(data, record + 10)
            raw = data[storage + offset:storage + offset + length]
            records.setdefault(name_id, []).append((platform, encoding, raw))

        def pick(name_id):
            for platform, encoding, raw in records.get(name_id, []):
                if (platform, encoding) in ((3, 1), (3, 10)):
                    return raw.decode("utf-16-be", "ignore").strip()
            for platform, encoding, raw in records.get(name_id, []):
                if (platform, encoding) in ((1, 0), (3, 0)):
                    return raw.decode("latin-1", "ignore").strip()
            return None

        family = pick(16) or pick(1)
        if not family:
            return None
        keyword = (pick(17) or pick(2) or "").lower().replace(" ", "")
        weight = WEIGHT_BY_NAME.get(keyword) or (
            _u16(data, tables[b"OS/2"] + 4) if b"OS/2" in tables else 0) or 400
        return family, weight, pick(1) or family
    except Exception:  # any malformed or unreadable file
        return None


def cjk_capable(tk_name, cache):
    """True if the face has a glyph for 中 (GDI marks missing glyphs 0xFFFF)."""
    if tk_name not in cache:
        try:
            user32, gdi32 = ctypes.windll.user32, ctypes.windll.gdi32
            hdc = user32.GetDC(0)
            handle = gdi32.CreateFontW(40, 0, 0, 0, 400, 0, 0, 0, 1, 0, 0, 0, 0, tk_name)
            previous = gdi32.SelectObject(hdc, handle)
            index = (ctypes.c_ushort * 1)()
            gdi32.GetGlyphIndicesW(hdc, "中", 1, index, 1)
            gdi32.SelectObject(hdc, previous)
            gdi32.DeleteObject(handle)
            user32.ReleaseDC(0, hdc)
            cache[tk_name] = index[0] != 0xFFFF
        except Exception:
            cache[tk_name] = True  # permissive: better to offer a font than hide it
    return cache[tk_name]


# --------------------------------------------------------------------------- #
# Engine locations and history
# --------------------------------------------------------------------------- #
def app_root():
    # FULL build: the whole engine folder ships inside this onefile exe and is
    # unpacked to _MEIPASS at launch, so it is the first place to look.
    meipass = getattr(sys, "_MEIPASS", "")
    if meipass and (Path(meipass) / "Real ESRGAN" / "realesrgan-ncnn-vulkan.exe").is_file():
        return Path(meipass)
    here = Path(sys.executable if getattr(sys, "frozen", False) else __file__).resolve().parent
    for base in (here, *here.parents):
        # Repo layout keeps the shared engine in dev\Real ESRGAN; a shipped copy
        # is expected to have Real ESRGAN next to the exe instead.
        for engine_dir in (base / "Real ESRGAN", base / "dev" / "Real ESRGAN"):
            if (engine_dir / "realesrgan-ncnn-vulkan.exe").is_file():
                return engine_dir.parent
    return here


ROOT = app_root()
ENGINE_DIR = ROOT / "Real ESRGAN"
ENGINE = ENGINE_DIR / "realesrgan-ncnn-vulkan.exe"
MODEL_DIR = ENGINE_DIR / "models"
IMAGE_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".bmp"}
FORMATS = ("png", "jpg", "webp")
HISTORY_FILE = Path(os.environ.get("APPDATA", Path.home())) / "RealESRGAN_GUI" / "folders.json"
SETTINGS_FILE = Path(os.environ.get("APPDATA", Path.home())) / "RealESRGAN_GUI" / "settings.json"
USER_FONT_DIR = Path(os.environ.get("APPDATA", Path.home())) / "RealESRGAN_GUI" / "fonts"


def load_history():
    try:
        data = json.loads(HISTORY_FILE.read_text(encoding="utf-8"))
        return {key: [p for p in data.get(key, []) if Path(p).is_dir()][:10] for key in ("input", "output")}
    except (OSError, ValueError, TypeError):
        return {"input": [], "output": []}


def save_history(history):
    try:
        HISTORY_FILE.parent.mkdir(parents=True, exist_ok=True)
        HISTORY_FILE.write_text(json.dumps(history, ensure_ascii=False, indent=2), encoding="utf-8")
    except OSError:
        pass


def remember(history, kind, value):
    value = str(Path(value).resolve())
    history[kind] = [value] + [p for p in history[kind] if p != value]
    history[kind] = history[kind][:10]
    save_history(history)


def available_models():
    """Read model files each time; adding/removing models needs no GUI rebuild."""
    names = set()
    for param in MODEL_DIR.glob("*.param"):
        stem = param.stem
        for suffix in ("-x2", "-x3", "-x4"):
            if stem.endswith(suffix):
                stem = stem[:-len(suffix)]
                break
        names.add(stem)
    return sorted(names)


def model_scales(name):
    scales = [value for value in (2, 3, 4) if (MODEL_DIR / f"{name}-x{value}.param").is_file()]
    if (MODEL_DIR / f"{name}.param").is_file() and not scales:
        scales.append(4)
    return tuple(scales) or (4,)


def gpu_names():
    """Display adapter names straight from the driver registry (no process spawn)."""
    try:
        import winreg
    except ImportError:
        return []
    key_path = r"SYSTEM\CurrentControlSet\Control\Class\{4d36e968-e325-11ce-bfc1-08002be10318}"
    names = []
    try:
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, key_path) as root:
            index = 0
            while True:
                try:
                    sub = winreg.EnumKey(root, index)
                except OSError:
                    break
                index += 1
                if not sub.isdigit():
                    continue
                try:
                    with winreg.OpenKey(root, sub) as device:
                        desc, _ = winreg.QueryValueEx(device, "DriverDesc")
                        if isinstance(desc, str) and desc.strip():
                            names.append(desc.strip())
                except OSError:
                    continue
    except OSError:
        return []
    return names


def windows_version():
    """Product name plus the marketing release, e.g. 'Windows 10 24H2'."""
    try:
        import winreg
        with winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE,
                            r"SOFTWARE\Microsoft\Windows NT\CurrentVersion") as key:
            product, _ = winreg.QueryValueEx(key, "ProductName")
            try:
                build, _ = winreg.QueryValueEx(key, "CurrentBuildNumber")
                # Win11's registry still says "Windows 10 ..."; build 22000+ is 11.
                if int(build) >= 22000 and str(product).startswith("Windows 10"):
                    product = "Windows 11"
            except (OSError, ValueError):
                pass
            try:
                display, _ = winreg.QueryValueEx(key, "DisplayVersion")
            except OSError:
                display = ""
        return f"{product} {display}".strip()
    except (OSError, ImportError, FileNotFoundError):
        return platform.system()


def _tray_balloon(hwnd, title, body, remove=False):
    """Raise a shell notification (the OS notification framework) on Windows.

    Returns True when the shell accepted it; any failure means this system has
    no usable notification framework and the caller stays silent. No-op off
    Windows: there is nothing here to fall back to (a message box is not a
    notification, and adding a dependency just for this is a bug farm)."""
    if sys.platform != "win32":
        return False

    class NOTIFYICONDATAW(ctypes.Structure):
        _fields_ = [
            ("cbSize", ctypes.c_uint32), ("hWnd", ctypes.c_void_p),
            ("uID", ctypes.c_uint32), ("uFlags", ctypes.c_uint32),
            ("uCallbackMessage", ctypes.c_uint32), ("hIcon", ctypes.c_void_p),
            ("szTip", ctypes.c_wchar * 128), ("dwState", ctypes.c_uint32),
            ("dwStateMask", ctypes.c_uint32), ("szInfo", ctypes.c_wchar * 256),
            ("uTimeout", ctypes.c_uint32), ("szInfoTitle", ctypes.c_wchar * 64),
            ("dwInfoFlags", ctypes.c_uint32), ("guidItem", ctypes.c_ubyte * 16),
            ("hBalloonIcon", ctypes.c_void_p),
        ]

    data = NOTIFYICONDATAW()
    data.cbSize = ctypes.sizeof(NOTIFYICONDATAW)
    data.hWnd = hwnd
    data.uID = 1
    shell32 = ctypes.windll.shell32
    if remove:
        return bool(shell32.Shell_NotifyIconW(2, ctypes.byref(data)))  # NIM_DELETE
    data.uFlags = 0x1 | 0x2 | 0x10  # NIF_MESSAGE | NIF_ICON | NIF_INFO
    data.uCallbackMessage = 0x0400 + 1
    user32 = ctypes.windll.user32
    user32.LoadIconW.restype = ctypes.c_void_p
    data.hIcon = user32.LoadIconW(None, ctypes.cast(ctypes.c_void_p(32512), ctypes.c_wchar_p))
    data.szInfo = body[:255]
    data.szInfoTitle = title[:63]
    data.dwInfoFlags = 0x1  # NIIF_INFO
    return bool(shell32.Shell_NotifyIconW(0, ctypes.byref(data)))  # NIM_ADD


def disk_line(path):
    try:
        usage = shutil.disk_usage(str(path))
    except OSError:
        return ""
    # 1024-based, same as Task Manager (用户核对基准).
    total_gb = usage.total / (1024 ** 3)
    free_gb = usage.free / (1024 ** 3)
    percent = 100.0 * usage.free / usage.total if usage.total else 0.0
    return f"{free_gb:.2f}GB / {total_gb:.0f}GB ({percent:.2f}%可用)"


# --------------------------------------------------------------------------- #
# Design sheet constants (all coordinates are the sheet's own pixels)
# --------------------------------------------------------------------------- #
DW, DH = 4400, 3027
CREAM, WHITE, BLACK, NAVY = "#f5f0e6", "#ffffff", "#111111", "#172c51"
INK, YELLOW, RED, BLUE = "#080808", "#ffd100", "#e30613", "#0066cc"
HOVER_FILL, DISABLED_INK = "#fff4c2", "#9a9488"
DROP_HOVER_GRAY = "#e5e5e5"  # 设计稿悬停底纹实测色
DROP_ROW_SCALE = 1.2         # 用户要求：下拉行距与字号 = 原稿 120%

B_PANEL, B_FIELD, B_BAR, B_ICON = 21, 14, 10, 8

PANEL_PATH = (173, 625, 4227, 1241)
PATH_ROWS = ((741, 919), (945, 1123))
FIELD_X0, FIELD_X1 = 638, 3547
ARROW_W = 96
BROWSE_X0, BROWSE_X1 = 3595, 4152
PATH_LABEL_X = 285
PATH_TEXT_X = 678
DROP_ROW = 132

PANEL_MODEL = (173, 1298, 1327, 2073)
MODEL_TITLE_CY = 1417
COMBO_MODEL = (269, 1479, 1230, 1657)
COMBO_SCALE = (269, 1794, 718, 1972)
COMBO_FORMAT = (781, 1794, 1230, 1972)
SCALE_LABEL_CY, SCALE_LABEL_X = 1731, 250
FORMAT_LABEL_CY, FORMAT_LABEL_X = 1731, 777

PANEL_SYS = (173, 2131, 1327, 2906)
SYS_TITLE_CY = 2249
SYS_BODY_X, SYS_BODY_CY0, SYS_PITCH = 308, 2337, 60.5
SYS_NAME_COL = 70  # 设计稿 GPU 名称列起点 378 ≈ 308+70（序号列右对齐到它）

PANEL_PROG = (1379, 1298, 4227, 1915)
BAR1 = (1496, 1491, 4107, 1591)
BAR2 = (1496, 1712, 4107, 1813)
PROG_LABEL1_CY, PROG_LABEL2_CY = 1436, 1657
PROG_LABEL_X, PROG_VALUE_RIGHT = 1517, 4066

PANEL_FAIL = (1379, 1971, 3385, 2906)
FAIL_TITLE_CY = 2089
FAIL_LIST_X, FAIL_LIST_CY0, FAIL_PITCH, FAIL_COL_PITCH, FAIL_ROWS = 1548, 2201, 66, 516, 6
RETRY_BTN = (2075, 2655, 2632, 2833)
EXPORT_BTN = (2700, 2655, 3257, 2833)

PANEL_ACTIONS = (3440, 1971, 4227, 2906)
ACTION_BTNS = ((3555, 2089, 4112, 2266), (3555, 2349, 4112, 2526), (3555, 2609, 4112, 2786))
ICON_X, ICON_SIZE = 3606, 96
ACTION_TEXT_RIGHT = 4069

LOCK_TAG = (1067, 1319, 1306, 1423)
OVERLAY = (1095, 1368, 3090, 1989)
OVERLAY_BORDER = 26

# 个性化设置 — header button measured on 页面设计/细节修改/个性化设置按钮位置.png,
# and the settings sheet it opens.
PERSONAL_BTN = (3595, 368, 4152, 545)
PANEL_SETTINGS = (1140, 870, 3260, 2210)
SET_TITLE_XY = (1236, 1024)
SET_CN_LABEL_CY, SET_EN_LABEL_CY = 1130, 1450
SET_CN_COMBO = (1236, 1180, 3164, 1360)
SET_EN_COMBO = (1236, 1500, 3164, 1680)
SET_PREVIEW_XY = (1236, 1850)
SET_UPLOAD_BTN = (1236, 1960, 1900, 2140)
SET_CLOSE_BTN = (1988, 1960, 2652, 2140)

# Logo drawn as stacked FILLED shapes (no outlines: Tk's oval/polygon stroke
# alignment varies per quadrant/scale). Black bodies first, colour insets on
# top; per the design sheet the circle overlaps the square, the triangle
# overlaps both, and the red apex shows over the ring's right side.
LOGO_SQUARE = (289, 303, 497, 537)
LOGO_SQUARE_FILL = (315, 329, 471, 511)
LOGO_CIRCLE = (475, 277, 104)
LOGO_CIRCLE_FILL_R = 77
LOGO_TRIANGLE = ((568, 231), (415, 537), (722, 537))
LOGO_TRIANGLE_FILL = ((568, 289), (458, 510), (679, 510))
TITLE_CN_XY = (778, 274)
TITLE_EN_XY = (790, 452)

FS = {
    "title_cn": 146, "title_en": 146, "label": 63, "value": 61, "path": 54,
    "button": 71, "sys_body": 50, "fail_item": 53, "lock": 46,
    "overlay": 244, "overlay_sub": 62, "prog_value": 66,
}

STATE_LABELS = {
    "idle": ("开始任务", True),
    "running": ("执行中…", False),
    "paused": ("暂停中…", False),
    "done": ("开始任务", True),
    "done_failed": ("忽略失败", True),
    "error": ("暂停中…", False),
}


def is_cjk(char):
    point = ord(char)
    return (
        0x2E80 <= point <= 0x9FFF
        or 0x3000 <= point <= 0x303F
        or 0xFF00 <= point <= 0xFFEF
        or 0x2010 <= point <= 0x206F
    )


def split_runs(text):
    """Group a string into CJK and Latin runs so each uses its own family."""
    runs = []
    for char in text:
        cjk = is_cjk(char)
        if runs and runs[-1][0] == cjk:
            runs[-1][1] += char
        else:
            runs.append([cjk, char])
    return [(cjk, run) for cjk, run in runs]


class App(tk.Tk):
    def __init__(self):
        if sys.platform == "win32":
            try:
                ctypes.windll.shcore.SetProcessDpiAwareness(2)
            except (AttributeError, OSError):
                try:
                    ctypes.windll.user32.SetProcessDPIAware()
                except (AttributeError, OSError):
                    pass
        super().__init__()
        register_fonts()
        self.title("Real-ESRGAN GUI")
        self.configure(bg=CREAM)
        self.minsize(1000, 688)

        self.events = queue.Queue()
        self.history = load_history()
        self.running = False
        self.cancel = False
        self.paused = False
        self.pause_requested = threading.Event()
        self.failed = []
        self.images = []
        self.task_snapshot = {}
        self.hardware_info = ""
        self.process = None
        self.exporting = False
        self.state_name = "idle"
        self.status_var = tk.StringVar(value="等待开始…")

        self._fonts = {}
        self._scale = 1.0
        self._extra = 0  # design units added to the sheet by _refit()
        self._ox = self._oy = 0.0
        self._bar_total = self._bar_item = 0.0
        self._bar_total_target = self._bar_item_target = 0.0
        self._pressed = None
        self._hover = None
        self._hover_t = {}
        self._drop = None
        self._drop_t = 0.0
        self._hover_row = None
        self._suppress_click = False
        self._overlay_t = 0.0
        self._overlay_want = 0.0
        self._overlay_title = "错误"
        self._overlay_sub = ""
        self._list_offset = 0
        self._btn_items = {}
        self._arrow_items = {}
        self._field_items = {}
        self._done = 0
        self._total = 0
        self._item_percent = 0
        self._models = []
        self._scales = []
        self._settings_open = False
        self._font_faces = []
        self._face_meta = {}
        self._default_font = ""
        self.font_settings = {"cn": "", "en": ""}
        self._cjk_cache = {}
        self._drop_offset = 0
        self._hw_ready = False
        self._hw_system = platform.system()
        self._hw_gpus = []
        self._hw_disk = ""
        self._disk_clock = 0

        self.vars = {
            "input": tk.StringVar(), "output": tk.StringVar(),
            "model": tk.StringVar(), "scale": tk.StringVar(), "format": tk.StringVar(value="png"),
        }
        if self.history["input"]:
            self.vars["input"].set(self.history["input"][0])
        if self.history["output"]:
            self.vars["output"].set(self.history["output"][0])

        self.canvas = tk.Canvas(self, bg=CREAM, highlightthickness=0, bd=0, takefocus=0)
        self.canvas.pack(fill="both", expand=True)
        self._entries = {}
        self._editing = None
        for key in ("input", "output"):
            entry = tk.Entry(self.canvas, textvariable=self.vars[key], relief="flat", bd=0,
                             bg=WHITE, fg=INK, insertbackground=INK, highlightthickness=0)
            entry.bind("<FocusIn>", lambda _e: self._close_dropdown())
            entry.bind("<FocusOut>", lambda _e, k=key: self._end_edit(k))
            entry.bind("<Return>", lambda _e, k=key: self._end_edit(k))
            entry.bind("<Escape>", lambda _e, k=key: self._end_edit(k))
            self._entries[key] = entry

        # Font combos in 个性化设置 float this one entry (only one edits at a time).
        self._editing_font = None
        self._font_query = ""  # typed filter; empty until the user actually types
        self._font_entry = tk.Entry(self.canvas, relief="flat", bd=0, bg=WHITE, fg=INK,
                                    insertbackground=INK, highlightthickness=0)
        self._font_entry.bind("<KeyRelease>", self._on_font_type)
        self._font_entry.bind("<Return>", self._end_font_edit)
        self._font_entry.bind("<Escape>", lambda _e: self._end_font_edit(commit=False))
        self._font_entry.bind("<FocusOut>", self._end_font_edit)

        self._refresh_models()
        self._build_font_faces()
        self._load_settings()
        self.canvas.bind("<Configure>", self._on_resize)
        self.canvas.bind("<Motion>", self._on_motion)
        self.canvas.bind("<Leave>", lambda _e: self._set_hover(None))
        self.canvas.bind("<Button-1>", self._on_press)
        self.canvas.bind("<Button-3>", self._on_right_press)
        self.canvas.bind("<ButtonRelease-1>", self._on_release)
        self.canvas.bind("<MouseWheel>", self._on_wheel)
        self.bind("<Escape>", self._on_escape)

        self._refit(center=True)
        self.after(60, self._bootstrap)
        self.after(16, self._tick)

    # ------------------------------------------------------------------ fonts #
    def _font(self, role, px):
        px = max(6, int(round(px)))
        key = (role, px)
        found = self._fonts.get(key)
        if found is None:
            # Real face files only, always weight="normal": the design's bold
            # is the actual OPPO Sans B file, not synthetic thickening.
            found = tkfont.Font(self, family=self._face_for(role), size=-px, weight="normal")
            self._fonts[key] = found
        return found

    def _face_for(self, role):
        face = self.font_settings[ROLE_SCRIPT[role]] or self._default_font
        family, weight = self._face_meta.get(face, (face, 400))
        if weight < 600 and ROLE_WEIGHT[role] >= 600:
            mates = [(abs(w - ROLE_WEIGHT[role]), n) for n, (f, w) in self._face_meta.items()
                     if f == family and w >= 600]
            if mates:
                face = min(mates)[1]
        return face

    def _build_font_faces(self):
        """One flat entry per font FILE — no family/weight merging — then every
        system family not already covered. An uploaded file therefore always
        shows up as its own row. Keys must be names Tk/GDI actually enumerate,
        otherwise the selection silently falls back and "doesn't take effect".
        """
        families = set(tkfont.families(self))
        faces = []
        meta = {}

        def add(name, family, weight):
            if name and name in families and name not in meta:
                meta[name] = (family or name, weight)
                faces.append(name)

        for path in sorted(p for folder in (font_dir(), USER_FONT_DIR)
                           if folder.is_dir()
                           for p in folder.iterdir() if p.suffix.lower() in (".ttf", ".otf", ".ttc")):
            parsed = read_font_faces(path)
            if parsed:
                add(parsed[2], parsed[0], parsed[1])  # ID 1: per-weight name GDI enumerates
                add(parsed[0], parsed[0], parsed[1])  # ID 16 family, for fonts GDI lists only as such
        for name in sorted(families):
            if not name.startswith("@"):
                add(name, name, 400)
        self._font_faces = faces
        self._face_meta = meta
        default = read_font_faces(font_dir() / DEFAULT_FONT_FILE)
        self._default_font = (default[2] if default and default[2] in faces
                              else next(iter(faces), "Arial"))

    def _load_settings(self):
        try:
            data = json.loads(SETTINGS_FILE.read_text(encoding="utf-8"))
        except (OSError, ValueError):
            data = {}
        for script in ("cn", "en"):
            face = data.get(script)
            self.font_settings[script] = face if face in self._font_faces else self._default_font

    def _save_settings(self):
        try:
            SETTINGS_FILE.parent.mkdir(parents=True, exist_ok=True)
            SETTINGS_FILE.write_text(json.dumps(self.font_settings, ensure_ascii=False),
                                     encoding="utf-8")
        except OSError:
            pass

    # --------------------------------------------------------------- geometry #
    def _relayout(self):
        width = max(1, self.canvas.winfo_width())
        height = max(1, self.canvas.winfo_height())
        dw = DW + self._extra
        self._scale = min(width / dw, height / DH)
        self._ox = (width - dw * self._scale) / 2
        self._oy = (height - DH * self._scale) / 2

    def sx(self, value):
        # Rounded: whole-pixel coords keep Tk's damage regions exact, so deleting
        # a floating panel (settings/dropdown/overlay) can't leave a 1px sliver
        # of its border behind.
        return int(round(self._ox + value * self._scale))

    def sy(self, value):
        return int(round(self._oy + value * self._scale))

    def sw(self, value):
        return value * self._scale

    def box(self, rect):
        x0, y0, x1, y1 = rect
        return self.sx(x0), self.sy(y0), self.sx(x1), self.sy(y1)

    def _in(self, x, y, rect):
        x0, y0, x1, y1 = self.box(rect)
        return x0 <= x <= x1 and y0 <= y <= y1

    # ------------------------------------------------------------------ text #
    def text(self, x, y, value, role, size, fill=INK, anchor="w", latin=None, tag=None):
        """Draw mixed-script text sharing one baseline inside a single line box."""
        fonts = []
        for cjk, run in split_runs(value):
            fonts.append((self._font(role if cjk else (latin or role), self.sw(size)), run))
        total = sum(font.measure(run) for font, run in fonts)
        if anchor == "w":
            cursor = x
        elif anchor == "e":
            cursor = x - total
        else:
            cursor = x - total / 2
        first = fonts[0][0]
        baseline = y + (first.metrics("ascent") + first.metrics("descent")) / 2 - first.metrics("descent")
        for font, run in fonts:
            self.canvas.create_text(cursor, baseline + font.metrics("descent"), text=run,
                                    font=font, fill=fill, anchor="sw", tags=tag)
            cursor += font.measure(run)
        return total

    def text_width(self, value, role, size, latin=None):
        total = 0
        for cjk, run in split_runs(value):
            total += self._font(role if cjk else (latin or role), self.sw(size)).measure(run)
        return total

    def _fit(self, value, role, size, limit, latin=None):
        if self.text_width(value, role, size, latin) <= limit:
            return value
        trimmed = value
        while trimmed and self.text_width(trimmed + "…", role, size, latin) > limit:
            trimmed = trimmed[:-1]
        return trimmed + "…"

    def _design_width(self, value, role, size, latin=None):
        """Text width in design units (measured at font size = design size, so
        independent of the current window scale)."""
        return sum(self._font(role if cjk else (latin or role), size).measure(run)
                   for cjk, run in split_runs(value))

    def _extra_needed(self):
        """Design units to add so the longest static texts fit their boxes under
        the current fonts: the path rows and the model combo / GPU names drive
        it. Live strings (disk line, counters) never widen the window — those
        _fit instead, or the 2s disk poll would resize the window all day."""
        need = 0
        for kind in ("input", "output"):
            value = self.vars[kind].get() or ""
            role = "cn_regular" if any(is_cjk(c) for c in value) else "en_light"
            need = max(need, PATH_TEXT_X + self._design_width(value, role, FS["path"], "en_light")
                       + 40 + ARROW_W - FIELD_X1)
        model = self.vars["model"].get() or "未找到模型"
        need = max(need, COMBO_MODEL[0] + 44
                   + self._design_width(model, "cn_regular", FS["value"], "en_light")
                   + 40 + ARROW_W - COMBO_MODEL[2])
        for col, line in [(0, self._hw_system)] + [(1, name) for name in self._hw_gpus[:2]]:
            role = "cn_regular" if any(is_cjk(c) for c in line) else "en_light"
            need = max(need, SYS_BODY_X + SYS_NAME_COL * col
                       + self._design_width(line, role, FS["sys_body"], "en_light") + 60 - PANEL_SYS[2])
        return max(0, int(round(need)))

    def _stretch_rects(self):
        """Rebuild the sheet's x geometry with `extra` added: the path panel and
        the left column grow to the right, the whole right region rides along,
        so every panel gap and outer margin stays exactly as drawn (连带加宽)."""
        e = self._extra
        self.PANEL_PATH = (173, 625, 4227 + e, 1241)
        self.FIELD_X1 = FIELD_X1 + e
        self.BROWSE_X0, self.BROWSE_X1 = BROWSE_X0 + e, BROWSE_X1 + e
        self.PANEL_MODEL = (173, 1298, 1327 + e, 2073)
        self.COMBO_MODEL = (269, 1479, 1230 + e, 1657)
        self.COMBO_FORMAT = (781, 1794, 1230 + e, 1972)
        self.PANEL_SYS = (173, 2131, 1327 + e, 2906)
        self.LOCK_TAG = (1067 + e, 1319, 1306 + e, 1423)
        self.PANEL_PROG = (1379 + e, 1298, 4227 + e, 1915)
        self.BAR1 = (1496 + e, 1491, 4107 + e, 1591)
        self.BAR2 = (1496 + e, 1712, 4107 + e, 1813)
        self.PROG_LABEL_X, self.PROG_VALUE_RIGHT = PROG_LABEL_X + e, PROG_VALUE_RIGHT + e
        self.PANEL_FAIL = (1379 + e, 1971, 3385 + e, 2906)
        self.FAIL_TITLE_X, self.FAIL_LIST_X = 1489 + e, FAIL_LIST_X + e
        self.RETRY_BTN = (2075 + e, 2655, 2632 + e, 2833)
        self.EXPORT_BTN = (2700 + e, 2655, 3257 + e, 2833)
        self.PANEL_ACTIONS = (3440 + e, 1971, 4227 + e, 2906)
        self.ACTION_BTNS = tuple((x0 + e, y0, x1 + e, y1) for x0, y0, x1, y1 in ACTION_BTNS)
        self.ICON_X, self.ACTION_TEXT_RIGHT = ICON_X + e, ACTION_TEXT_RIGHT + e

    def _refit(self, center=False):
        """Measure text overflow under the current fonts, widen the sheet and
        the window to fit, redraw. The screen caps the widening; `_fit` ellipsis
        takes whatever is left."""
        ref = min(1440, self.winfo_screenwidth() - 60) / DW
        room = max(0, int((self.winfo_screenwidth() - 60) / ref) - DW)
        self._extra = min(self._extra_needed(), room)
        self._stretch_rects()
        width = round((DW + self._extra) * ref)
        height = round(DH * ref)
        if height > self.winfo_screenheight() - 80:
            height = self.winfo_screenheight() - 80
            width = int(height * (DW + self._extra) / DH)
        if (width, height) != getattr(self, "_last_fit", None):
            self._last_fit = (width, height)
            if center:
                self.geometry(f"{width}x{height}+{max(0, (self.winfo_screenwidth() - width) // 2)}"
                              f"+{max(0, (self.winfo_screenheight() - height) // 3)}")
            else:
                self.geometry(f"{width}x{height}")
        self._relayout()
        self._draw()

    # ---------------------------------------------------------------- panels #
    def _panel(self, rect, tag):
        self._frame(rect, tag, WHITE, BLACK, B_PANEL)

    def _frame(self, rect, tag, fill, outline, stroke):
        """Stroke drawn fully inside the given bounds, like the design sheets."""
        x0, y0, x1, y1 = self.box(rect)
        width = max(1, self.sw(stroke))
        return self.canvas.create_rectangle(x0 + width / 2, y0 + width / 2, x1 - width / 2, y1 - width / 2,
                                            fill=fill, outline=outline, width=width, tags=tag)

    def _arrow(self, rect, tag, key):
        """Solid black square with a white triangle, as in the design's combos.
        The fill is tucked half a stroke-width into the ring band (top/right/
        bottom): a Tk fill rect paints its first row while the stroke band
        renders 1px lower, which left the square peeking above the button's
        top edge. Tucked, it is always covered by (or the same colour as) the
        band at any scale. The triangle stays centred on the full bounds."""
        x0, y0, x1, y1 = self.box(rect)
        t = max(1, round(self.sw(B_FIELD))) / 2
        square = self.canvas.create_rectangle(x0, y0 + t, x1 - t, y1 - t, fill=BLACK, outline=BLACK, width=0, tags=tag)
        cx, cy = (x0 + x1) / 2, (y0 + y1) / 2
        half_w, half_h = self.sw(23), self.sw(12)
        triangle = self.canvas.create_polygon(cx - half_w, cy - half_h, cx + half_w, cy - half_h, cx, cy + half_h,
                                              fill=WHITE, outline=WHITE, tags=tag)
        self._arrow_items[key] = (square, triangle)

    def _field(self, rect, tag, key):
        """White base + arrow + ring on top. Edit state tints ring and square
        yellow TOGETHER (`_set_field_color`), so the layers are same-colour and
        no white seam can show between them at any window scale."""
        x0, y0, x1, y1 = self.box(rect)
        self.canvas.create_rectangle(x0, y0, x1, y1, fill=WHITE, outline=WHITE, width=0, tags=tag)
        self._arrow((rect[2] - ARROW_W, rect[1], rect[2], rect[3]), tag, key)
        width = max(1, round(self.sw(B_FIELD)))
        ring = self.canvas.create_rectangle(x0 + width / 2, y0 + width / 2, x1 - width / 2, y1 - width / 2,
                                            fill="", outline=BLACK, width=width, tags=tag)
        return ring, self._arrow_items[key][0]

    # ---------------------------------------------------------------- header #
    def _draw_header(self):
        tag = "g_header"
        self.canvas.delete(tag)
        self.canvas.create_rectangle(*self.box(LOGO_SQUARE), fill=BLACK, outline=BLACK,
                                     width=0, tags=tag)
        self.canvas.create_rectangle(*self.box(LOGO_SQUARE_FILL), fill=BLUE, outline=BLUE,
                                     width=0, tags=tag)
        cx, cy, radius = LOGO_CIRCLE
        for r, colour in ((radius, BLACK), (LOGO_CIRCLE_FILL_R, YELLOW)):
            r = self.sw(r)
            self.canvas.create_oval(self.sx(cx) - r, self.sy(cy) - r,
                                    self.sx(cx) + r, self.sy(cy) + r,
                                    fill=colour, outline=colour, width=0, tags=tag)
        for pts, colour in ((LOGO_TRIANGLE, BLACK), (LOGO_TRIANGLE_FILL, RED)):
            points = []
            for px, py in pts:
                points.extend((self.sx(px), self.sy(py)))
            self.canvas.create_polygon(*points, fill=colour, outline=colour, width=0,
                                       joinstyle="miter", tags=tag)
        self.text(self.sx(TITLE_CN_XY[0]), self.sy(TITLE_CN_XY[1]), "欢迎使用", "cn_heavy",
                  FS["title_cn"], INK, tag=tag)
        self.text(self.sx(TITLE_EN_XY[0]), self.sy(TITLE_EN_XY[1]), "Real-ESRGAN GUI", "en_bold",
                  FS["title_en"], INK, tag=tag, latin="en_bold")
        self._button("personalize", PERSONAL_BTN, "个性化设置", None, WHITE, INK, BLACK, True,
                     centered=True, tag=tag)

    # ----------------------------------------------------------------- paths #
    def _path_text_x(self):
        return PATH_TEXT_X

    def _draw_paths(self):
        tag = "g_paths"
        self.canvas.delete(tag)
        self._panel(self.PANEL_PATH, tag)
        for (top, bottom), (label, kind) in zip(PATH_ROWS, (("输入文件夹", "input"), ("输出文件夹", "output"))):
            self._field_items[kind] = self._field((FIELD_X0, top, self.FIELD_X1, bottom), tag, f"drop:{kind}")
            self.text(self.sx(PATH_LABEL_X), self.sy((top + bottom) / 2), label, "cn_bold",
                      FS["label"], INK, tag=tag)
            value = self.vars[kind].get() or "（未选择文件夹）"
            role = "cn_regular" if any(is_cjk(c) for c in value) else "en_light"
            limit = self.sw(self.FIELD_X1 - ARROW_W - PATH_TEXT_X - 40)
            self.text(self.sx(PATH_TEXT_X), self.sy((top + bottom) / 2),
                      self._fit(value, role, FS["path"], limit, latin="en_light"),
                      role, FS["path"], INK, tag=tag, latin="en_light")
            self._button(f"browse_{kind}", (self.BROWSE_X0, top, self.BROWSE_X1, bottom), "浏览", None,
                         BLACK, WHITE, BLACK, self._editable(), centered=True, tag=tag)
        self._raise_frames()

    # ----------------------------------------------------------------- model #
    def _draw_model_panel(self):
        tag = "g_model"
        self.canvas.delete(tag)
        self._panel(self.PANEL_MODEL, tag)
        self.text(self.sx(265), self.sy(MODEL_TITLE_CY), "模型选择", "cn_bold", FS["label"], INK, tag=tag)
        self.text(self.sx(SCALE_LABEL_X), self.sy(SCALE_LABEL_CY), "放大倍率", "cn_bold", FS["label"], INK, tag=tag)
        self.text(self.sx(FORMAT_LABEL_X), self.sy(FORMAT_LABEL_CY), "输出格式", "cn_bold", FS["label"], INK, tag=tag)
        for rect, key in ((self.COMBO_MODEL, "drop:model"), (COMBO_SCALE, "drop:scale"),
                          (self.COMBO_FORMAT, "drop:format")):
            self._frame(rect, tag, WHITE, BLACK, B_FIELD)
            self._arrow((rect[2] - ARROW_W, rect[1], rect[2], rect[3]), tag, key)
        limit = self.sw(self.COMBO_MODEL[2] - ARROW_W - (self.COMBO_MODEL[0] + 44) - 40)
        self.text(self.sx(self.COMBO_MODEL[0] + 44), self.sy((self.COMBO_MODEL[1] + self.COMBO_MODEL[3]) / 2),
                  self._fit(self.vars["model"].get() or "未找到模型", "cn_regular", FS["value"], limit,
                            latin="en_light"),
                  "cn_regular", FS["value"], INK, tag=tag, latin="en_light")
        self.text(self.sx(COMBO_SCALE[0] + 44), self.sy((COMBO_SCALE[1] + COMBO_SCALE[3]) / 2),
                  self.vars["scale"].get(), "cn_regular", FS["value"], INK, tag=tag, latin="en_light")
        self.text(self.sx(self.COMBO_FORMAT[0] + 44), self.sy((self.COMBO_FORMAT[1] + self.COMBO_FORMAT[3]) / 2),
                  self.vars["format"].get(), "cn_regular", FS["value"], INK, tag=tag, latin="en_light")

    # -------------------------------------------------------------- sysinfo #
    def _hardware_lines(self):
        # Each line is a list of (column, text) runs; GPU rows split index and
        # name so the name column starts at a fixed x — the sheet draws both
        # names at one aligned edge, which a single proportional-font run
        # cannot keep.
        lines = [[(0, "系统")], [(0, self._hw_system)], [(0, "后端")], [(0, "Vulkan(NCNN)")], [(0, "显卡")]]
        if not self._hw_ready:
            lines.append([(0, "检测中…")])
        elif self._hw_gpus:
            for index, name in enumerate(self._hw_gpus[:2]):
                lines.append([(0, str(index)), (1, name)])
        else:
            lines.append([(0, "未检测到")])
        lines.append([(0, "硬盘使用状况")])
        lines.append([(0, self._hw_disk or "无法读取")])
        return lines

    def _draw_sysinfo(self):
        tag = "g_sys"
        self.canvas.delete(tag)
        self._panel(self.PANEL_SYS, tag)
        self.text(self.sx(266), self.sy(SYS_TITLE_CY), "系统信息", "cn_bold", FS["label"], INK, tag=tag)
        for index, runs in enumerate(self._hardware_lines()):
            for col, line in runs:
                role = "cn_bold" if line in ("系统", "后端", "显卡", "硬盘使用状况") else "cn_regular"
                x = SYS_BODY_X + SYS_NAME_COL * col
                limit = self.sw(self.PANEL_SYS[2] - x - 60)
                self.text(self.sx(x), self.sy(SYS_BODY_CY0 + SYS_PITCH * index),
                          self._fit(line, role, FS["sys_body"], limit, latin="en_light"),
                          role, FS["sys_body"], INK, tag=tag, latin="en_light")

    # ------------------------------------------------------------- progress #
    def _draw_progress_panel(self):
        tag = "g_prog"
        self.canvas.delete(tag)
        self._panel(self.PANEL_PROG, tag)
        self.text(self.sx(self.PROG_LABEL_X), self.sy(PROG_LABEL1_CY), "总进度", "cn_bold", FS["label"], INK, tag=tag)
        self.text(self.sx(self.PROG_LABEL_X), self.sy(PROG_LABEL2_CY), "单张进度", "cn_bold", FS["label"], INK, tag=tag)
        self._bar_fill_items = {}
        for name, rect in (("bar1", self.BAR1), ("bar2", self.BAR2)):
            x0, y0, x1, y1 = self.box(rect)
            inset = max(1, self.sw(B_BAR))
            item = self.canvas.create_rectangle(x0 + inset, y0 + inset, x0 + inset, y1 - inset,
                                                fill=YELLOW, outline=YELLOW, width=0, tags="bar")
            # Ring drawn last with a transparent interior: the fill lives
            # underneath, so the border can never be covered by the fill's
            # edge rows (Tk stroke band renders 1px lower than its rect).
            self._frame(rect, tag, "", NAVY, B_BAR)
            self._bar_fill_items[name] = (item, x0 + inset, y0 + inset, x1 - inset, y1 - inset)
        self._sync_bar_text()
        self._apply_bars()

    def _sync_bar_text(self):
        self.canvas.delete("bar_text")
        if self.state_name in ("idle", "error"):
            total_text = "等待开始…"
        else:
            total_text = f"{self._done:,}/{self._total:,}" if self._total else "0/0"
        total_role = "cn_bold" if any(is_cjk(c) for c in total_text) else "en_light"
        self.text(self.sx(self.PROG_VALUE_RIGHT), self.sy(PROG_LABEL1_CY), total_text, total_role,
                  FS["prog_value"], INK, anchor="e", tag="bar_text",
                  latin=None if total_role == "cn_bold" else "en_light")
        self.text(self.sx(self.PROG_VALUE_RIGHT), self.sy(PROG_LABEL2_CY), f"{round(self._item_percent)}%",
                  "en_light", FS["prog_value"], INK, anchor="e", tag="bar_text", latin="en_light")
        self._raise_frames()

    def _apply_bars(self):
        if not getattr(self, "_bar_fill_items", None):
            return
        for name, value in (("bar1", self._bar_total), ("bar2", self._bar_item)):
            item, x0, y0, x1, y1 = self._bar_fill_items[name]
            self.canvas.coords(item, x0, y0, x0 + (x1 - x0) * max(0.0, min(1.0, value)), y1)

    # --------------------------------------------------------------- failed #
    def _visible_failed(self):
        capacity = FAIL_ROWS * 3
        items = self.failed[self._list_offset:self._list_offset + capacity]
        slots = list(items)
        if len(self.failed) - self._list_offset - len(items) > 0:
            slots = slots[:capacity - 1]
            slots.append(None)
        return slots

    def _draw_failed_list(self):
        self.canvas.delete("list")
        if not self.failed:
            return
        for index, path in enumerate(self._visible_failed()):
            column, row = divmod(index, FAIL_ROWS)
            x = self.FAIL_LIST_X + FAIL_COL_PITCH * column
            y = FAIL_LIST_CY0 + FAIL_PITCH * row
            limit = (self.FAIL_LIST_X + FAIL_COL_PITCH * (column + 1) - x - 30 if column < 2
                     else self.PANEL_FAIL[2] - x - 90)
            label = f"等 {len(self.failed)} 个文件" if path is None else path.name
            label = self._fit(label, "cn_regular", FS["fail_item"], self.sw(limit), latin="en_light")
            self.text(self.sx(x), self.sy(y), label, "cn_regular", FS["fail_item"], INK,
                      tag="list", latin="en_light")
        self._raise_frames()

    def _draw_failed_panel(self):
        tag = "g_fail"
        self.canvas.delete(tag)
        self._panel(self.PANEL_FAIL, tag)
        self.text(self.sx(self.FAIL_TITLE_X), self.sy(FAIL_TITLE_CY), "以下文件处理失败", "cn_bold", FS["label"], INK, tag=tag)
        if self.state_name == "done_failed" and self.failed:
            self._button("retry", self.RETRY_BTN, "重试", None, WHITE, INK, BLACK, True, centered=True, tag=tag)
            self._button("export", self.EXPORT_BTN, "导出失败图片", None, WHITE, INK, BLACK, True,
                         centered=True, tag=tag)
        self._draw_failed_list()

    # -------------------------------------------------------------- actions #
    def _button(self, name, rect, label, icon, fill, ink, border, enabled, centered=False, tag="g_act"):
        self.canvas.delete(f"btn_{name}")
        x0, y0, x1, y1 = self.box(rect)
        width = max(1, self.sw(B_FIELD))
        tags = (tag, f"btn_{name}")
        hover = self._hover_t.get(name, 0.0) if enabled else 0.0
        bg = self.canvas.create_rectangle(x0 + width / 2, y0 + width / 2, x1 - width / 2, y1 - width / 2,
                                          fill=fill, outline=border, width=width, tags=tags)
        if hover > 0:
            target = HOVER_FILL if fill == WHITE else "#3a3a3a"
            self.canvas.itemconfigure(bg, fill=self._mix(fill, target, hover))
        dx = self.sw(2) if self._pressed == name else 0
        dy = dx
        if icon:
            cx = self.sx(self.ICON_X + ICON_SIZE / 2) + dx
            cy = self.sy((rect[1] + rect[3]) / 2) + dy
            half = self.sw(ICON_SIZE / 2) * (1.0 + 0.05 * hover)
            stroke = max(1, self.sw(B_ICON))
            # The sheets keep every geometric icon at full strength; only the label
            # and the hover behaviour change with availability.
            if icon == "circle":
                self.canvas.create_oval(cx - half, cy - half, cx + half, cy + half,
                                        fill=YELLOW, outline=BLACK, width=stroke, tags=tags)
            elif icon == "triangle":
                self.canvas.create_polygon(cx, cy - half + self.sw(6), cx - half, cy + half, cx + half, cy + half,
                                           fill=RED, outline=BLACK, width=stroke, joinstyle="miter", tags=tags)
            else:
                pad = self.sw(4)
                self.canvas.create_rectangle(cx - half + pad, cy - half + pad, cx + half - pad, cy + half - pad,
                                             fill=BLUE, outline=BLACK, width=stroke, tags=tags)
        ink_colour = ink
        if centered:
            self.text((x0 + x1) / 2 + dx, (y0 + y1) / 2 + dy, label, "cn_bold", FS["button"], ink_colour,
                      anchor="center", tag=tags)
        else:
            self.text(self.sx(self.ACTION_TEXT_RIGHT) + dx, (y0 + y1) / 2 + dy, label, "cn_bold", FS["button"],
                      ink_colour, anchor="e", tag=tags)
        self._btn_items[name] = {"bg": bg, "fill": fill, "enabled": enabled}

    def _draw_action_panel(self):
        tag = "g_act"
        self.canvas.delete(tag)
        self._panel(self.PANEL_ACTIONS, tag)
        label, enabled = STATE_LABELS[self.state_name]
        self._button("start", self.ACTION_BTNS[0], label, "circle", WHITE, INK, BLACK, enabled, tag=tag)
        self._button("pause", self.ACTION_BTNS[1], "暂停/继续", "triangle", WHITE, INK, BLACK,
                     self.state_name in ("running", "paused"), tag=tag)
        self._button("cancel", self.ACTION_BTNS[2], "取消", "square", WHITE, INK, BLACK,
                     self.state_name in ("running", "paused"), tag=tag)

    def _draw_lock(self):
        self.canvas.delete("lock")
        if self._editable():
            return
        self.canvas.create_rectangle(*self.box(self.LOCK_TAG), fill=RED, outline=RED, width=0, tags="lock")
        self.text(self.sx((self.LOCK_TAG[0] + self.LOCK_TAG[2]) / 2), self.sy((self.LOCK_TAG[1] + self.LOCK_TAG[3]) / 2),
                  "锁定", "cn_bold", FS["lock"], WHITE, anchor="center", tag="lock")

    # ------------------------------------------------------------- dropdown #
    def _dropdown_items(self):
        if self._drop == "input":
            return list(self.history["input"]) or ["（暂无历史记录）"]
        if self._drop == "output":
            return list(self.history["output"]) or ["（暂无历史记录）"]
        if self._drop == "model":
            return list(self._models) or ["（未找到模型）"]
        if self._drop == "scale":
            return list(self._scales) or ["4"]
        if self._drop == "format":
            return list(FORMATS)
        if self._drop in ("setcn", "seten"):
            items = [name for name in self._font_faces
                     if self._drop == "seten" or cjk_capable(name, self._cjk_cache)]
            if self._editing_font and self._font_query:
                query = self._font_query.lower()
                items = [family for family in items if query in family.lower()] or ["（无匹配字体）"]
            return items or ["（未找到中文字体）" if self._drop == "setcn" else "（未找到字体）"]
        return []

    def _dropdown_geometry(self):
        """(x0, x1, top, row_height) in design units."""
        row_h = DROP_ROW * DROP_ROW_SCALE
        if self._drop in ("input", "output"):
            index = 0 if self._drop == "input" else 1
            top, bottom = PATH_ROWS[index]
            return FIELD_X0, self.FIELD_X1, bottom, row_h
        if self._drop == "setcn":
            return SET_CN_COMBO[0], SET_CN_COMBO[2], SET_CN_COMBO[3], row_h
        if self._drop == "seten":
            return SET_EN_COMBO[0], SET_EN_COMBO[2], SET_EN_COMBO[3], row_h
        rect = {"model": self.COMBO_MODEL, "scale": COMBO_SCALE, "format": self.COMBO_FORMAT}.get(self._drop)
        if rect is None:
            return None
        return rect[0], rect[2], rect[3], row_h

    def _dropdown_visible(self):
        return min(len(self._dropdown_items()), 6)

    def _dropdown_first(self):
        return max(0, min(self._drop_offset, len(self._dropdown_items()) - self._dropdown_visible()))

    def _draw_dropdown(self):
        self.canvas.delete("drop")
        if not self._drop or self._drop_t <= 0.01:
            return
        geometry = self._dropdown_geometry()
        items = self._dropdown_items()
        if geometry is None or not items:
            return
        x0, x1, top, row_h = geometry
        visible = self._dropdown_visible()
        height = row_h * visible * self._drop_t
        bf = self.sw(B_FIELD)
        sx0, sx1, stop = self.sx(x0), self.sx(x1), self.sy(top)
        # White base without outline, then the hover shading, then the border
        # ring on top with a transparent interior (§18 pattern): the shading
        # runs underneath the border band, so it can never cover the stroke —
        # the round-2 bug that got the grey hover rect deleted.
        self.canvas.create_rectangle(sx0 + bf / 2, stop + bf / 2,
                                     sx1 - bf / 2, stop + self.sw(height) - bf / 2,
                                     fill=WHITE, outline="", width=0, tags="drop")
        first = self._dropdown_first()
        if self._hover_row is not None and first <= self._hover_row < first + visible:
            row_top = stop + self.sw(row_h * (self._hover_row - first))
            gx0, gy0, gx1, gy1 = sx0 + bf / 2, stop + bf / 2, sx1 - bf / 2, stop + self.sw(height) - bf / 2
            self.canvas.create_rectangle(gx0, max(row_top, gy0), gx1,
                                         min(row_top + self.sw(row_h), gy1),
                                         fill=DROP_HOVER_GRAY, outline="", width=0, tags="drop")
        size = round(FS["fail_item"] * DROP_ROW_SCALE)
        for offset, index in enumerate(range(first, first + visible)):
            row_top = stop + self.sw(row_h * offset)
            row_bottom = row_top + self.sw(row_h)
            if row_bottom > stop + self.sw(height) + 1:
                break
            label = self._fit(items[index], "cn_regular", size, sx1 - sx0 - self.sw(60), latin="en_light")
            self.text(sx0 + self.sw(30), (row_top + row_bottom) / 2, label, "cn_regular",
                      size, INK, tag="drop", latin="en_light")
        self.canvas.create_rectangle(sx0 + bf / 2, stop + bf / 2,
                                     sx1 - bf / 2, stop + self.sw(height) - bf / 2,
                                     fill="", outline=BLACK, width=max(1, bf), tags="drop")
        self._raise_frames()

    def _open_dropdown(self, name):
        if name in ("setcn", "seten"):
            self._begin_font_edit("cn" if name == "setcn" else "en")
            return
        self._drop = name
        self._drop_t = 0.0
        self._drop_offset = 0
        self._hover_row = None
        self._draw_dropdown()

    def _close_dropdown(self):
        if self._drop:
            self._drop = None
            self._drop_t = 0.0
            self._drop_offset = 0
            self._hover_row = None
            self.canvas.delete("drop")
            # Tk skips the outermost pixel column when repainting a deleted
            # floating panel, leaving a ghost 1px border behind; a full redraw
            # repaints it (same remedy in _close_settings).
            self._draw()

    def _choose_dropdown(self, index):
        items = self._dropdown_items()
        if not items or index >= len(items) or items[index].startswith("（"):
            self._close_dropdown()
            return
        value = items[index]
        if self._drop in ("input", "output"):
            self.vars[self._drop].set(value)
            remember(self.history, self._drop, value)
            self._refit()
            if self._drop == "output":
                self._load_hardware()
        elif self._drop == "model":
            self.vars["model"].set(value)
            self._model_changed()
            self._refit()
        elif self._drop == "scale":
            self.vars["scale"].set(value)
            self._draw_model_panel()
        elif self._drop == "format":
            self.vars["format"].set(value)
            self._draw_model_panel()
        elif self._drop in ("setcn", "seten"):
            self.font_settings["cn" if self._drop == "setcn" else "en"] = value
            self._save_settings()
            self._fonts.clear()
            self._refit()
            self._end_font_edit(commit=False)
        self._close_dropdown()

    # ------------------------------------------------------------- settings #
    def _draw_settings(self):
        self.canvas.delete("settings")
        if not self._settings_open:
            return
        tag = "settings"
        self._panel(PANEL_SETTINGS, tag)
        self.text(self.sx(SET_TITLE_XY[0]), self.sy(SET_TITLE_XY[1]), "个性化设置", "cn_bold",
                  FS["label"], INK, tag=tag)
        for label, key, rect, script in (("中文字体", "setcn", SET_CN_COMBO, "cn"),
                                         ("西文字体", "seten", SET_EN_COMBO, "en")):
            self.text(self.sx(rect[0]), self.sy(SET_CN_LABEL_CY if key == "setcn" else SET_EN_LABEL_CY),
                      label, "cn_bold", FS["value"], INK, tag=tag)
            self._field_items[key] = self._field(rect, tag, f"drop:{key}")
            current = self.font_settings[script] or "（系统默认）"
            self.text(self.sx(rect[0] + 44), self.sy((rect[1] + rect[3]) / 2),
                      self._fit(current, "cn_regular", FS["value"], self.sw(rect[2] - rect[0] - ARROW_W - 100),
                                latin="en_light"),
                      "cn_regular", FS["value"], INK, tag=tag, latin="en_light")
        self.text(self.sx(SET_PREVIEW_XY[0]), self.sy(SET_PREVIEW_XY[1]),
                  "预览 AaBb 0123 欢迎使用 Real-ESRGAN", "cn_regular", FS["path"], INK,
                  tag=tag, latin="en_light")
        self._button("upload", SET_UPLOAD_BTN, "上传字体", None, WHITE, INK, BLACK, True,
                     centered=True, tag=tag)
        self._button("close_set", SET_CLOSE_BTN, "关闭", None, BLACK, WHITE, BLACK, True,
                     centered=True, tag=tag)
        self._raise_frames()

    def _open_settings(self):
        self._end_edit()
        self._close_dropdown()
        self._settings_open = True
        self._draw_settings()

    def _close_settings(self):
        if self._settings_open:
            self._settings_open = False
            self.canvas.delete("settings")
            self._draw()

    def _on_escape(self, _event=None):
        if self._editing_font:
            self._end_font_edit(commit=False)
        elif self._drop:
            self._close_dropdown()
        elif self._overlay_t > 0.5 and not self.running:
            self._hide_overlay()
            self._set_state("idle")
        elif self._settings_open:
            self._close_settings()

    def _upload_fonts(self):
        files = filedialog.askopenfilenames(
            title="选择字体文件（每个文件单独出现在字体列表中）", parent=self,
            filetypes=[("字体文件", "*.ttf *.otf *.ttc"), ("所有文件", "*.*")])
        self._import_font_files(files)

    def _import_font_files(self, files):
        """Copy font files into the user dir, register them, rebuild the list."""
        files = [name for name in files if Path(name).suffix.lower() in (".ttf", ".otf", ".ttc")]
        if not files:
            return
        USER_FONT_DIR.mkdir(parents=True, exist_ok=True)
        added = 0
        for name in files:
            source = Path(name)
            target = USER_FONT_DIR / source.name
            try:
                if source.resolve() != target.resolve():
                    shutil.copy2(source, target)
                ctypes.windll.gdi32.AddFontResourceExW(str(target), 0x10, 0)
                added += 1
            except OSError:
                pass
        if added:
            ctypes.windll.user32.SendMessageTimeoutW(0xFFFF, 0x001D, 0, 0, 0, 1000, None)  # WM_FONTCHANGE
            self._build_font_faces()
            for script in ("cn", "en"):
                if self.font_settings[script] not in self._font_faces:
                    self.font_settings[script] = self._default_font
            self._fonts.clear()
            self._refit()

    # -------------------------------------------------------------- overlay #
    def _draw_overlay(self):
        self.canvas.delete("over")
        if self._overlay_t <= 0.01:
            return
        t = self._overlay_t
        x0, y0, x1, y1 = OVERLAY
        shrink_w = (x1 - x0) * (1 - t) * 0.12
        shrink_h = (y1 - y0) * (1 - t) * 0.12
        rect = (x0 + shrink_w, y0 + shrink_h, x1 - shrink_w, y1 - shrink_h)
        self._frame(rect, "over", RED, BLACK, OVERLAY_BORDER)
        cx = (rect[0] + rect[2]) / 2
        cy = (rect[1] + rect[3]) / 2
        if self._overlay_sub:
            self.text(self.sx(cx), self.sy(cy - 110), self._overlay_title, "cn_bold", FS["overlay"], WHITE,
                      anchor="center", tag="over")
            limit = self.sw(OVERLAY[2] - OVERLAY[0] - 200)
            self.text(self.sx(cx), self.sy(cy + 190),
                      self._fit(self._overlay_sub, "cn_regular", FS["overlay_sub"], limit, latin="en_light"),
                      "cn_regular", FS["overlay_sub"], WHITE, anchor="center", tag="over", latin="en_light")
        else:
            self.text(self.sx(cx), self.sy(cy), self._overlay_title, "cn_bold", FS["overlay"], WHITE,
                      anchor="center", tag="over")
        self._raise_frames()

    def _show_overlay(self, title, sub=""):
        self._overlay_title, self._overlay_sub = title, sub
        self._overlay_want = 1.0
        self._draw_overlay()

    def _hide_overlay(self):
        self._overlay_want = 0.0

    # -------------------------------------------------------------- entries #
    def _sync_entry_font(self):
        """Floating entries keep the px font from when editing began; re-derive
        it from the CURRENT scale (resize) and text script. Shared by the path
        entries and the settings font entry."""
        if self._editing:
            value = self.vars[self._editing].get()
            role = "cn_regular" if any(is_cjk(c) for c in value) else "en_light"
            self._entries[self._editing].configure(font=self._font(role, self.sw(FS["path"])))
        if self._editing_font:
            self._font_entry.configure(font=self._font("cn_regular", self.sw(FS["value"])))

    def _begin_edit(self, kind):
        """Float a real entry over the drawn field; the canvas keeps the resting text."""
        if not self._editable() or self._editing == kind:
            return
        previous = self._editing
        self._editing = kind  # first: the old entry's FocusOut must become a no-op
        if previous:
            self._entries[previous].place_forget()
            self._draw_paths()  # its drawn text back, ring black, before the new one
        entry = self._entries[kind]
        entry.configure(state="normal", bg=WHITE, fg=INK,
                        disabledbackground=WHITE, disabledforeground=INK)
        self._sync_entry_font()
        self._place_entry(kind)
        entry.focus_set()
        entry.icursor(tk.END)

    def _place_entry(self, kind):
        """Position the floating entry flush against the ring's inner edge.

        The ring width is the same rounded value `_field` draws with, so the
        entry's white background starts exactly at the band's bottom pixel and
        can never shave the tinted ring (the 白色矩形遮挡 bug)."""
        index = 0 if kind == "input" else 1
        top, bottom = PATH_ROWS[index]
        x0, y0, x1, y1 = self.box((FIELD_X0, top, self.FIELD_X1, bottom))
        width = max(1, round(self.sw(B_FIELD)))
        left = int(x0 + self.sw(PATH_TEXT_X - FIELD_X0 - 6))
        right = int(x1 - self.sw(ARROW_W + 20))
        self._entries[kind].place(x=left, y=y0 + width + 1,
                                  width=max(20, right - left),
                                  height=max(10, y1 - y0 - 2 * width - 1))
        self._set_field_color(kind, YELLOW)

    def _set_field_color(self, key, color):
        """Edit state tints the field's ring AND the arrow square together —
        same-colour layers cannot show a seam at any scale."""
        items = self._field_items.get(key)
        if items:
            ring, square = items
            self.canvas.itemconfigure(ring, outline=color)
            self.canvas.itemconfigure(square, fill=color)

    def _begin_font_edit(self, key):
        """Float a real entry over the font combo; typing filters the dropdown."""
        if self._editing_font == key:
            return
        self._end_font_edit(commit=False)
        self._editing_font = key
        self._font_query = ""
        self._drop, self._drop_t, self._drop_offset = f"set{key}", 0.0, 0
        entry = self._font_entry
        entry.delete(0, tk.END)
        entry.insert(0, self.font_settings[key] or "")
        self._sync_entry_font()
        self._place_font_entry()
        entry.focus_set()
        entry.icursor(tk.END)
        self._draw_dropdown()

    def _place_font_entry(self):
        rect = SET_CN_COMBO if self._editing_font == "cn" else SET_EN_COMBO
        # +15 sits just inside the ring's 14px band so the entry never shaves it
        x0, y0, x1, y1 = self.box((rect[0] + 30, rect[1] + 15, rect[2] - ARROW_W, rect[3] - 15))
        self._font_entry.place(x=int(x0), y=int(y0), width=int(x1 - x0), height=int(y1 - y0))
        self._set_field_color(f"set{self._editing_font}", YELLOW)

    def _end_font_edit(self, _event=None, commit=True):
        key = self._editing_font
        if not key:
            return
        self._editing_font = None
        self._font_entry.place_forget()
        if commit:
            typed = self._font_entry.get().strip()
            match = next((name for name in self._font_faces
                          if (key == "en" or cjk_capable(name, self._cjk_cache))
                          and name.lower() == typed.lower()), None)
            if match and match != self.font_settings[key]:
                self.font_settings[key] = match
                self._save_settings()
                self._fonts.clear()
        self._close_dropdown()
        self._refit()

    def _on_font_type(self, _event=None):
        self._font_query = self._font_entry.get().strip()
        self._drop_offset = 0
        self._draw_dropdown()

    def _end_edit(self, kind=None, _event=None):
        if kind is not None and kind != self._editing:
            return  # stale FocusOut from the other entry while switching fields
        kind = self._editing
        if not kind:
            return
        self._editing = None
        self._entries[kind].place_forget()
        value = self.vars[kind].get().strip()
        if value and Path(value).is_dir():
            remember(self.history, kind, value)
            if kind == "output":
                self._load_hardware()
        self._refit()

    def _raise_frames(self):
        self.canvas.tag_raise("list")
        self.canvas.tag_raise("bar_text")
        self.canvas.tag_raise("lock")
        self.canvas.tag_raise("settings")
        self.canvas.tag_raise("drop")
        self.canvas.tag_raise("over")

    # ------------------------------------------------------------------ run #
    def _refresh_models(self):
        models = available_models()
        current = self.vars["model"].get()
        self._models = models
        self.vars["model"].set(current if current in models else (models[0] if models else ""))
        self._scales = [str(value) for value in model_scales(self.vars["model"].get())] if models else []
        if self._scales and self.vars["scale"].get() not in self._scales:
            self.vars["scale"].set(self._scales[0])

    def _model_changed(self):
        self._scales = [str(value) for value in model_scales(self.vars["model"].get())]
        if self._scales and self.vars["scale"].get() not in self._scales:
            self.vars["scale"].set(self._scales[0])

    def _bootstrap(self):
        self._relayout()
        self._draw()
        self._load_hardware()

    def _load_hardware(self):
        target = self.vars["output"].get().strip() or self.vars["input"].get().strip() or str(ROOT)

        def work():
            self.events.put(("hardware", {"system": windows_version(), "gpus": gpu_names(),
                                          "disk": disk_line(target)}))

        threading.Thread(target=work, daemon=True).start()

    def _refresh_disk(self):
        # Live disk line: tasks keep writing, so poll every ~2s from _tick and
        # only pay a redraw when the string actually moved.
        target = self.vars["output"].get().strip() or self.vars["input"].get().strip() or str(ROOT)
        line = disk_line(target)
        if line and line != self._hw_disk:
            self._hw_disk = line
            self._hw_ready = True
            self._draw_sysinfo()

    def _draw(self):
        self._btn_items = {}
        self._arrow_items = {}
        self._field_items = {}
        self._draw_header()
        self._draw_paths()
        self._draw_model_panel()
        self._draw_sysinfo()
        self._draw_progress_panel()
        self._draw_failed_panel()
        self._draw_action_panel()
        self._draw_lock()
        self._draw_settings()
        self._draw_dropdown()
        self._draw_overlay()

    def _on_resize(self, _event=None):
        self._relayout()
        self._draw()
        if self._editing:
            self._place_entry(self._editing)
        if self._editing_font:
            self._place_font_entry()
        self._sync_entry_font()

    def _set_state(self, name):
        if self._editing and name not in ("idle", "done"):
            self._end_edit()
        self.state_name = name
        if name == "paused":
            self._show_overlay("暂停中…")
        elif name in ("idle", "done", "done_failed", "running"):
            self._hide_overlay()
        self._draw_paths()
        self._draw_model_panel()
        self._draw_failed_panel()
        self._draw_action_panel()
        self._draw_lock()
        self._sync_bar_text()
        self._raise_frames()

    def _editable(self):
        """States where the input controls accept changes (no 锁定 tag in the sheets)."""
        return self.state_name in ("idle", "done")

    # ------------------------------------------------------------- controls #
    def _start(self):
        if self.running or self.state_name not in ("idle", "done"):
            return
        source = Path(self.vars["input"].get().strip())
        target = Path(self.vars["output"].get().strip())
        if not source.is_dir() or not target.is_dir():
            self._error("请选择有效的输入文件夹和输出文件夹")
            return
        for kind, path in (("input", source), ("output", target)):
            remember(self.history, kind, path)
        model, scale = self.vars["model"].get().strip(), self.vars["scale"].get().strip()
        if not model or not scale:
            self._error(f"模型文件夹为空：{MODEL_DIR}")
            return
        if not ENGINE.is_file():
            self._error(f"未找到 Real-ESRGAN 引擎：{ENGINE}")
            return
        self.images = sorted(p for p in source.rglob("*") if p.is_file() and p.suffix.lower() in IMAGE_EXTS)
        if not self.images:
            self._error("输入文件夹中没有支持的图片")
            return
        self.task_snapshot = {"input": str(source), "output": str(target), "model": model,
                              "scale": scale, "format": self.vars["format"].get()}
        self._begin_run(self.images)

    def _begin_run(self, images):
        self.failed = []
        self._list_offset = 0
        self.running, self.cancel, self.paused = True, False, False
        self.pause_requested.clear()
        self._done, self._total, self._item_percent = 0, len(images), 0
        self._bar_total = self._bar_item = 0.0
        self._bar_total_target = self._bar_item_target = 0.0
        self._set_state("running")
        source = Path(self.task_snapshot["input"])
        target = Path(self.task_snapshot["output"])
        threading.Thread(target=self._worker,
                         args=(images, source, target, self.task_snapshot["model"], self.task_snapshot["scale"]),
                         daemon=True).start()

    def _worker(self, images, source, target, model, scale):
        self.events.put(("done", self._run_batches(images, source, target, model, scale), self.cancel))

    def _retry_failed(self):
        if self.running or not self.failed or self.state_name != "done_failed":
            return
        self._begin_run(list(self.failed))

    def _run_batches(self, images, source, target, model, scale):
        fmt = getattr(self, "task_snapshot", {}).get("format", "png")
        # Only outputs written by THIS run count: re-running onto a folder with
        # leftover outputs must not pop the whole queue in the first engine
        # lines (total bar showed 100% while the engine was still working).
        run_started = time.time()

        def fresh(path):
            # ponytail: FAT mtime granularity (2s) is the ceiling — NTFS (the
            # shipped target) is 100ns; one stat() per call, same budget as is_file.
            try:
                return path.stat().st_mtime >= run_started
            except OSError:
                return False

        failed = []
        folders = sorted({image.parent for image in images})
        completed = 0
        total = len(images)
        for folder in folders:
            batch = [image for image in images if image.parent == folder and image.suffix.lower() in IMAGE_EXTS]
            if not batch:
                continue
            if self.cancel:
                failed.extend(batch)
                break
            names = [f"{(target / image.relative_to(source)).with_suffix('').name}.{fmt}" for image in batch]
            output_dir = target / folder.relative_to(source)
            output_dir.mkdir(parents=True, exist_ok=True)
            command = [str(ENGINE), "-i", str(folder), "-o", str(output_dir), "-n", model,
                       "-s", scale, "-m", str(MODEL_DIR), "-f", fmt]
            finished = 0
            current = 0.0
            pending = list(range(len(names)))
            cursor = 0
            try:
                process = subprocess.Popen(command, cwd=ENGINE_DIR, stdout=subprocess.PIPE,
                                           stderr=subprocess.STDOUT,
                                           creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0),
                                           text=True, bufsize=1)
                self.process = process
                for line in process.stdout:
                    if self.cancel:
                        process.kill()
                        break
                    pause_requested = getattr(self, "pause_requested", None)
                    while pause_requested is not None and pause_requested.is_set() and not self.cancel:
                        self.events.put(("status", "暂停中…"))
                        threading.Event().wait(0.15)
                    match = re.search(r"(\d+(?:\.\d+)?)%", line)
                    if match:
                        # ponytail: the engine prints one line per tile (~24us per is_file
                        # on Windows, thousands of lines per run), so walk the outputs we
                        # have not seen yet round-robin: one stat per line instead of a
                        # whole-batch scan, which starved the engine and idled the GPU.
                        while pending:
                            candidate = names[pending[cursor]]
                            found = fresh(output_dir / candidate)
                            # Non-png output of an alpha input gains a trailing .png; only
                            # that case needs a second stat, so the png path stays at one.
                            if not found and fmt != "png":
                                found = fresh(output_dir / f"{candidate}.png")
                            if found:
                                pending.pop(cursor)
                                finished += 1
                                if cursor >= len(pending):
                                    cursor = 0
                            else:
                                cursor = (cursor + 1) % len(pending)
                                break
                        # Every image starts over at 0.00%, so a 0.00 line means a fresh
                        # image: the item bar tracks the image in flight, not the batch.
                        percent = float(match.group(1))
                        current = percent if percent == 0 else max(current, percent)
                        self.events.put(("progress", completed + finished, total, round(current),
                                         f"处理中：{folder.name}（{finished}/{len(batch)} 张，当前 {round(current)}%）"))
                    if "gpu" in line.lower() or "vulkan" in line.lower() or "device" in line.lower():
                        self.hardware_info = line.strip()
                result = process.wait(timeout=3600)
                # Same freshness rule for the failure audit: a leftover output
                # the engine never overwrote was NOT produced by this run.
                present = {item.name for item in output_dir.iterdir() if fresh(item)}
                missing = [image for image, name in zip(batch, names)
                           if name not in present and f"{name}.png" not in present]
                failed.extend(batch if result != 0 else missing)
            except (OSError, subprocess.SubprocessError):
                failed.extend(batch)
            self.process = None
            if self.cancel:
                break
            completed += len(batch)
            self.events.put(("progress", completed, total, 100.0, f"完成：{folder.name}"))
        return failed

    def _toggle_pause(self):
        pause_requested = getattr(self, "pause_requested", None)
        if pause_requested is None:
            return
        if self.state_name == "running":
            self.paused = True
            pause_requested.set()
            self._set_state("paused")
        elif self.state_name == "paused":
            self.paused = False
            pause_requested.clear()
            self._set_state("running")

    def _stop(self):
        self.cancel = True
        self.paused = False
        pause_requested = getattr(self, "pause_requested", None)
        if pause_requested is not None:
            pause_requested.clear()
        process = self.process
        if process and process.poll() is None:
            process.kill()

    def _error(self, detail):
        self._done = self._total = self._item_percent = 0
        self._bar_total = self._bar_item = 0.0
        self._bar_total_target = self._bar_item_target = 0.0
        self.state_name = "error"
        self._apply_bars()
        self._set_state("error")
        self._show_overlay("错误", detail)

    def _ignore_failed(self):
        self.failed = []
        self._list_offset = 0
        self._set_state("idle")

    def _export_failed(self):
        if not self.failed or self.exporting:
            return
        destination = filedialog.askdirectory(title="选择失败原图导出的文件夹", parent=self)
        if not destination:
            return
        destination = Path(destination)
        images = list(self.failed)
        self.exporting = True
        self._show_overlay("导出中…", f"0/{len(images)}")

        def work():
            copied = 0
            for index, image in enumerate(images, start=1):
                try:
                    shutil.copy2(image, destination / image.name)
                    copied += 1
                except OSError:
                    pass
                self.events.put(("export", index, len(images), copied))
            self.events.put(("export_done", copied, len(images)))

        threading.Thread(target=work, daemon=True).start()

    # -------------------------------------------------------------- pointer #
    def _hit(self, x, y):
        # Only the popup box itself blocks; buttons behind the 暂停中… overlay
        # stay clickable. Mid-export keeps the old blanket (a retry started
        # under a running export would race it).
        if self._overlay_t > 0.5 and (self.exporting or self._in(x, y, OVERLAY)):
            return ("overlay", None)
        if self._drop and self._drop_t > 0.5:
            geometry = self._dropdown_geometry()
            if geometry:
                gx0, gx1, top, grow_h = geometry
                stop = self.sy(top)
                bottom = stop + self.sw(grow_h * self._dropdown_visible())
                if self.sx(gx0) <= x <= self.sx(gx1) and stop <= y <= bottom:
                    row = max(0, min(int((y - stop) / self.sw(grow_h)), self._dropdown_visible() - 1))
                    return ("drop_item", self._dropdown_first() + row)
        if self._settings_open:
            for rect, key in ((SET_CN_COMBO, "setcn"), (SET_EN_COMBO, "seten")):
                if self._in(x, y, rect):
                    return ("drop_open", key)
            if self._in(x, y, SET_UPLOAD_BTN):
                return ("button", "upload")
            if self._in(x, y, SET_CLOSE_BTN):
                return ("button", "close_set")
            px0, py0, px1, py1 = self.box(PANEL_SETTINGS)
            if px0 <= x <= px1 and py0 <= y <= py1:
                return ("settings", None)
            return ("settings_close", None)
        if self._in(x, y, PERSONAL_BTN):
            return ("button", "personalize")
        if self._editable():
            for kind, (top, bottom) in zip(("input", "output"), PATH_ROWS):
                if self._in(x, y, (self.FIELD_X1 - ARROW_W, top, self.FIELD_X1, bottom)):
                    return ("drop_open", kind)
                if self._in(x, y, (FIELD_X0, top, self.FIELD_X1 - ARROW_W, bottom)):
                    return ("edit", kind)
                if self._in(x, y, (self.BROWSE_X0, top, self.BROWSE_X1, bottom)):
                    return ("button", f"browse_{kind}")
            for name, rect in (("model", self.COMBO_MODEL), ("scale", COMBO_SCALE), ("format", self.COMBO_FORMAT)):
                if self._in(x, y, rect):
                    return ("drop_open", name)
        for index, name in enumerate(("start", "pause", "cancel")):
            if self._btn_items.get(name, {}).get("enabled") and self._in(x, y, self.ACTION_BTNS[index]):
                return ("button", name)
        if self.state_name == "done_failed":
            if self._in(x, y, self.RETRY_BTN):
                return ("button", "retry")
            if self._in(x, y, self.EXPORT_BTN):
                return ("button", "export")
        return (None, None)

    def _set_hover(self, name):
        if self._hover != name:
            was_row = self._hover == "drop_row"
            self._hover = name
            self.canvas.configure(cursor="hand2" if name else "")
            if self._drop and (was_row or name == "drop_row"):
                if name != "drop_row":
                    self._hover_row = None
                self._draw_dropdown()

    def _on_motion(self, event):
        kind, value = self._hit(event.x, event.y)
        if kind == "drop_item":
            self._set_hover("drop_row")
            if self._hover_row != value:
                self._hover_row = value
                self._draw_dropdown()
        elif kind == "button":
            self._set_hover(value)
        elif kind == "drop_open":
            self._set_hover(f"drop_open:{value}")
        else:
            self._set_hover(None)

    def _on_wheel(self, event):
        if self._drop:
            count = len(self._dropdown_items())
            if count > self._dropdown_visible():
                step = -3 if event.delta > 0 else 3
                self._drop_offset = max(0, min(count - self._dropdown_visible(),
                                               self._drop_offset + step))
                self._draw_dropdown()
            return
        if self.state_name == "done_failed" and self.failed:
            capacity = FAIL_ROWS * 3
            maximum = max(0, len(self.failed) - capacity)
            step = -FAIL_ROWS if event.delta > 0 else FAIL_ROWS
            self._list_offset = max(0, min(maximum, self._list_offset + step))
            self._draw_failed_list()

    def _on_press(self, event):
        kind, value = self._hit(event.x, event.y)
        if self._editing_font and not (self._drop and kind == "drop_item"):
            toggle = kind == "drop_open" and value == f"set{self._editing_font}"
            self._end_font_edit()
            if toggle:
                self._suppress_click = True
                return
        if self._drop:
            if kind == "drop_item":
                self._choose_dropdown(value)
            else:
                self._close_dropdown()
            self._suppress_click = True
            return
        if self._settings_open:
            if kind == "settings_close":
                self._close_settings()
            elif kind == "button":
                self._pressed = value
                self._redraw_button(value)
            elif kind != "drop_open":
                self._suppress_click = True
                return
            return
        if kind == "button":
            self._pressed = value
            self._redraw_button(value)

    def _on_release(self, event):
        if self._suppress_click:
            self._suppress_click = False
            return
        if self._pressed:
            name = self._pressed
            self._pressed = None
            self._redraw_button(name)
            kind, value = self._hit(event.x, event.y)
            if kind == "button" and value == name:
                self._dispatch(value)
            return
        kind, value = self._hit(event.x, event.y)
        if kind == "overlay":
            if not self.running:
                self._hide_overlay()
                self._set_state("idle")
                self.status_var.set("等待开始…")
        elif kind == "drop_open":
            self._open_dropdown(value)
        elif kind == "edit":
            self._begin_edit(value)
        else:
            self._close_dropdown()

    def _redraw_button(self, name):
        if name in ("retry", "export"):
            self._draw_failed_panel()
        elif name in ("upload", "close_set"):
            self._draw_settings()
        elif name == "personalize":
            self._draw_header()
        elif name.startswith("browse_"):
            self._draw_paths()
        else:
            self._draw_action_panel()

    def _dispatch(self, name):
        if name == "start":
            self._ignore_failed() if self.state_name == "done_failed" else self._start()
        elif name == "pause":
            self._toggle_pause()
        elif name == "cancel":
            self._stop()
        elif name == "retry":
            self._retry_failed()
        elif name == "export":
            self._export_failed()
        elif name == "personalize":
            self._open_settings()
        elif name == "upload":
            self._upload_fonts()
        elif name == "close_set":
            self._close_settings()
        elif name.startswith("browse_"):
            self._browse(name.split("_", 1)[1])

    def _on_right_press(self, event):
        kind, value = self._hit(event.x, event.y)
        if kind == "button" and value.startswith("browse_"):
            path = Path(self.vars[value.split("_", 1)[1]].get().strip())
            if path.is_dir():
                os.startfile(str(path))

    def _browse(self, kind):
        title = "选择输入文件夹" if kind == "input" else "选择输出文件夹"
        value = filedialog.askdirectory(title=title, parent=self)
        if value:
            self.vars[kind].set(value)
            remember(self.history, kind, value)
            self._refit()
            if kind == "output":
                self._load_hardware()

    # ----------------------------------------------------------------- tick #
    def _tick(self):
        try:
            while True:
                self._handle_event(self.events.get_nowait())
        except queue.Empty:
            pass

        self._disk_clock += 1
        if self._disk_clock >= 120:  # ~2s at 16ms
            self._disk_clock = 0
            self._refresh_disk()

        dirty = False
        for name in ("start", "pause", "cancel", "retry", "export",
                     "personalize", "upload", "close_set"):
            target = 1.0 if self._hover == name else 0.0
            current = self._hover_t.get(name, 0.0)
            if abs(current - target) > 0.004:
                self._hover_t[name] = current + (target - current) * 0.28
                self._tint_button(name, self._hover_t[name])
            elif current != target:
                self._hover_t[name] = target
                self._tint_button(name, target)

        for kind in ("input", "output", "model", "scale", "format"):
            key = f"drop:{kind}"
            target = 1.0 if self._hover == key else 0.0
            current = self._hover_t.get(key, 0.0)
            if abs(current - target) > 0.004:
                self._hover_t[key] = current + (target - current) * 0.28
                self._tint_arrow(key, self._hover_t[key])
            elif current != target:
                self._hover_t[key] = target
                self._tint_arrow(key, target)

        # Rise: exponential chase (target itself creeps with the engine, so
        # this reads as a smooth climb). Per-image fall: hard cut — a paced
        # sweep while the next image's target already climbs again reads as
        # the bar jumping (乱跳).
        for attr, target_attr in (("_bar_total", "_bar_total_target"),
                                  ("_bar_item", "_bar_item_target")):
            current, target = getattr(self, attr), getattr(self, target_attr)
            delta = target - current
            if attr == "_bar_item" and delta < 0:
                setattr(self, attr, target)
                dirty = True
            elif abs(delta) > 0.0008:
                step = delta * 0.2 if delta > 0 else max(delta, -0.04)
                setattr(self, attr, current + step)
                dirty = True
            elif delta:
                setattr(self, attr, target)
                dirty = True
        if dirty:
            self._apply_bars()

        if self._drop and self._drop_t < 1.0:
            self._drop_t = min(1.0, self._drop_t + 0.22)
            self._draw_dropdown()

        if abs(self._overlay_t - self._overlay_want) > 0.01:
            self._overlay_t += (self._overlay_want - self._overlay_t) * 0.24
            self._draw_overlay()
        elif self._overlay_t != self._overlay_want:
            self._overlay_t = self._overlay_want
            self._draw_overlay()

        self.after(16, self._tick)

    def _tint_button(self, name, value):
        data = self._btn_items.get(name)
        if not data or not data["enabled"]:
            return
        fill = data["fill"]
        self.canvas.itemconfigure(data["bg"], fill=self._mix(fill, HOVER_FILL if fill == WHITE else "#3a3a3a", value))

    def _arrow_editing(self, key):
        name = key.split(":", 1)[-1]
        if name in ("input", "output"):
            return self._editing == name
        if name in ("setcn", "seten"):
            return self._editing_font == ("cn" if name == "setcn" else "en")
        return False

    def _tint_arrow(self, key, value):
        items = self._arrow_items.get(key)
        if not items:
            return
        square, triangle = items
        base = YELLOW if self._arrow_editing(key) else BLACK
        self.canvas.itemconfigure(square, fill=self._mix(base, YELLOW, value))
        self.canvas.itemconfigure(triangle, fill=self._mix(WHITE, BLACK, value))

    @staticmethod
    def _mix(first, second, ratio):
        ratio = max(0.0, min(1.0, ratio))
        a = tuple(int(first[index:index + 2], 16) for index in (1, 3, 5))
        b = tuple(int(second[index:index + 2], 16) for index in (1, 3, 5))
        return "#%02x%02x%02x" % tuple(int(a[index] + (b[index] - a[index]) * ratio) for index in range(3))

    # -------------------------------------------------------------- events #
    def _notify(self, body):
        """Completion ping through the OS notification framework; silently
        nothing where the system has none (non-Windows, or shell refusal)."""
        if sys.platform != "win32":
            return
        try:
            hwnd = self.winfo_id()
            if _tray_balloon(hwnd, "Real-ESRGAN GUI", body):
                self.after(10000, lambda: _tray_balloon(hwnd, "", "", remove=True))
        except Exception:
            pass  # best-effort by definition: no framework, no notification

    def _handle_event(self, event):
        kind = event[0]
        if kind == "progress":
            _, done, total, percent, text = event
            self._done, self._total, self._item_percent = done, total, percent
            self._bar_total_target = done / total if total else 0.0
            self._bar_item_target = percent / 100.0
            self.status_var.set(text)
            self.title(f"Real-ESRGAN GUI — {text}")
            self._sync_bar_text()
        elif kind == "status":
            self.status_var.set(event[1])
        elif kind == "hardware":
            info = event[1]
            self._hw_system = info.get("system", platform.system())
            self._hw_gpus = info.get("gpus", [])
            self._hw_disk = info.get("disk", "")
            self._hw_ready = True
            self._refit()
        elif kind == "export":
            _, index, total, copied = event
            self._show_overlay("导出中…", f"{index}/{total}（成功 {copied}）")
        elif kind == "export_done":
            _, copied, total = event
            self.exporting = False
            self._show_overlay("导出完成", f"成功 {copied}/{total} 张")
            self.after(1400, self._hide_overlay)
        else:
            _, failed, cancelled = event
            self.running = False
            self.failed = [Path(item) for item in failed]
            self._list_offset = 0
            self._item_percent = 100 if not cancelled else 0
            if cancelled:
                self._bar_item_target = 0.0
                self.status_var.set("已取消")
                self.title("Real-ESRGAN GUI — 已取消")
                self._set_state("idle")
            elif self.failed:
                self.status_var.set(f"完成，{len(self.failed)} 张失败")
                self.title(f"Real-ESRGAN GUI — 完成（{len(self.failed)} 张失败）")
                self._set_state("done_failed")
            else:
                self._bar_item_target = 1.0
                self.status_var.set("处理完成")
                self.title("Real-ESRGAN GUI — 处理完成")
                self._set_state("done")
            self._sync_bar_text()
            if not cancelled:
                self._notify(self.status_var.get())


if __name__ == "__main__":
    if "--check" in sys.argv:  # layout self-check: python gui.py --check
        app = App()
        app.update()
        base = app._last_fit[0]
        assert app.PANEL_PROG[0] - app.PANEL_MODEL[2] == 52, "column gap as drawn"
        assert app.PANEL_ACTIONS[0] - app.PANEL_FAIL[2] == 55
        app.vars["input"].set("D:\\数据\\" + "很长很长的文件夹名称" * 15)
        app._refit()
        assert app._extra > 0, "long text must widen the sheet"
        assert app._last_fit[0] > base, "window must grow with the sheet"
        assert app.PANEL_PROG[0] - app.PANEL_MODEL[2] == 52, "gaps survive widening"
        assert app.PANEL_ACTIONS[0] - app.PANEL_FAIL[2] == 55
        assert app.PANEL_PATH[2] == app.PANEL_ACTIONS[2], "outer edges stay aligned"
        print(f"refit OK: window {base} -> {app._last_fit[0]} px, extra {app._extra}")
        app.destroy()
    else:
        App().mainloop()

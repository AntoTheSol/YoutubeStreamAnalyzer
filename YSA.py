import sys
import os
import tkinter as tk
from tkinter import ttk, messagebox, scrolledtext, filedialog

import threading
import webbrowser
import re
import subprocess
# requests costs ~110 ms of import time - a third of the app's total and
# ~70% of the frozen exe's - paid before the window can begin, for a
# library used only by thumbnails and the updater. Imported on first use.
_http_session = None
_http_session_lock = threading.Lock()


def _get_http_session():
    """Shared HTTP session with connection pooling, built on first use.

    Double-checked creation: thumbnail fetches arrive from several
    precache workers at once, and two racing here must come away with
    the SAME session. The session is published only after its adapters
    are mounted, so an unlocked reader can never observe a half-built
    one. Once built, requests.Session is thread-safe for independent
    requests (shared connection pool, no shared per-request state).
    """
    global _http_session
    s = _http_session
    if s is None:
        with _http_session_lock:
            if _http_session is None:
                import requests
                from requests.adapters import HTTPAdapter
                _s = requests.Session()
                _adapter = HTTPAdapter(pool_connections=4, pool_maxsize=8,
                                       max_retries=2)
                _s.mount('https://', _adapter)
                _s.mount('http://', _adapter)
                _http_session = _s
            s = _http_session
    return s
import tempfile
import shutil
import time
import json
import atexit
import socket
import struct
import datetime
import ctypes
import ctypes.wintypes
from concurrent.futures import ThreadPoolExecutor
import select
import errno as _errno

# Suppress console windows for subprocesses on Windows
if sys.platform == 'win32':
    CREATE_NO_WINDOW = 0x08000000
else:
    CREATE_NO_WINDOW = 0

# Pre-compiled YouTube URL patterns (avoids recompiling on every validation call)
_YT_URL_PATTERNS = [
    re.compile(r'(https?://)?(www\.)?(youtube\.com/watch\?v=|youtu\.be/)[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube\.com/embed/[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube\.com/e/[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube\.com/v/[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube\.com/shorts/[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube\.com/live/[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube\.com/clip/[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube-nocookie\.com/embed/[\w-]+'),
    re.compile(r'(https?://)?(www\.)?youtube-nocookie\.com/v/[\w-]+'),
    re.compile(r'(https?://)?youtube\.googleapis\.com/v/[\w-]+'),
    re.compile(r'(https?://)?m\.youtube\.com/watch\?v=[\w-]+'),
    re.compile(r'(https?://)?music\.youtube\.com/watch\?v=[\w-]+'),
]

# ---------------------------------------------------------------------------
# Custom DNS resolver - redirects YouTube domains through Google Public DNS
# ---------------------------------------------------------------------------
YOUTUBE_DOMAINS = [
    "www.youtube.com",
    "m.youtube.com",
    "music.youtube.com",
    "youtubei.googleapis.com",
    "youtube.googleapis.com",
    "www.youtube-nocookie.com",
    "youtube-nocookie.com",
    "ytimg.com",
    "googlevideo.com",
    "content.youtube.com",
    "apis.youtube.com",
    "s.youtube.com",
    "m.youtube-nocookie.com",
]

_original_getaddrinfo = socket.getaddrinfo

def _custom_getaddrinfo(host, port, family=0, type=0, proto=0, flags=0):
    """Python-side socket patch: resolves YouTube domains via Google DNS.
    Covers requests/urllib calls (thumbnail download etc) - not yt-dlp subprocess."""
    use_custom = _custom_dns_active and isinstance(host, str) and any(
        host == d or host.endswith("." + d) for d in YOUTUBE_DOMAINS
    )
    if use_custom:
        try:
            with _dns_cache_lock:
                cached = _resolved_cache.get(host)
            if cached is None or time.monotonic() >= cached[1]:
                ip, ttl = _dns_query(host, _primary_dns)
                if not ip:
                    ip, ttl = _dns_query(host, _secondary_dns)
                if ip:
                    with _dns_cache_lock:
                        _resolved_cache[host] = (ip, time.monotonic() + ttl)
                    cached = (ip, time.monotonic() + ttl)
            if cached:
                host = cached[0]
        except Exception:
            pass
    return _original_getaddrinfo(host, port, family, type, proto, flags)

def _dns_query(hostname, dns_server, port=53, timeout=1):
    """Send a minimal DNS A-record query and return (ip, ttl) or (None, 0)."""
    tx_id = os.urandom(2)
    flags = b'\x01\x00'
    counts = b'\x00\x01\x00\x00\x00\x00\x00\x00'
    question = b''
    for part in hostname.encode().split(b'.'):
        question += bytes([len(part)]) + part
    question += b'\x00'
    question += b'\x00\x01'
    question += b'\x00\x01'
    packet = tx_id + flags + counts + question
    sock = None
    try:
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        sock.settimeout(timeout)
        sock.sendto(packet, (dns_server, port))
        data, _ = sock.recvfrom(512)
    except Exception:
        return None, 0
    finally:
        if sock is not None:
            try:
                sock.close()
            except Exception:
                pass
    offset = 12
    while offset < len(data):
        length = data[offset]
        offset += 1
        if length == 0:
            break
        if length & 0xC0 == 0xC0:
            offset += 1
            break
        offset += length
    offset += 4
    ancount = struct.unpack('>H', data[6:8])[0]
    for _ in range(ancount):
        if offset + 12 > len(data):
            break
        if data[offset] & 0xC0 == 0xC0:
            offset += 2
        else:
            while offset < len(data) and data[offset] != 0:
                offset += data[offset] + 1
            offset += 1
        if offset + 10 > len(data):
            break
        rtype = struct.unpack('>H', data[offset:offset + 2])[0]
        rttl  = struct.unpack('>I', data[offset + 4:offset + 8])[0]
        rdlen = struct.unpack('>H', data[offset + 8:offset + 10])[0]
        offset += 10
        if rtype == 1 and rdlen == 4:
            ip = '.'.join(str(b) for b in data[offset:offset + 4])
            # Clamp TTL: honour the server's value but never cache shorter than
            # 60 s (avoids thrashing) or longer than 300 s (avoids stale IPs).
            ttl = max(60, min(rttl, 300))
            return ip, ttl
        offset += rdlen
    return None, 0

_custom_dns_active = False
_primary_dns = "8.8.8.8"
_secondary_dns = "8.8.4.4"

# Cache of resolved IPs used by the proxy: {hostname: (ip, expiry_time)}
# expiry_time is time.monotonic() + TTL so stale entries are re-resolved.
_resolved_cache = {}
_dns_cache_lock = __import__("threading").Lock()

# Local proxy state
_proxy_server = None
_proxy_port = None
_proxy_lock = __import__("threading").Lock()

def _pre_resolve_all():
    """Pre-resolve all YouTube domains via Google DNS in parallel and cache results."""
    with _dns_cache_lock:
        _resolved_cache.clear()

    def _resolve_one(domain):
        try:
            ip, ttl = _dns_query(domain, _primary_dns)
            if not ip:
                ip, ttl = _dns_query(domain, _secondary_dns)
            if ip:
                return domain, (ip, time.monotonic() + ttl)
        except Exception:
            pass
        return domain, None

    with ThreadPoolExecutor(max_workers=len(YOUTUBE_DOMAINS)) as pool:
        for domain, entry in pool.map(_resolve_one, YOUTUBE_DOMAINS):
            if entry:
                with _dns_cache_lock:
                    _resolved_cache[domain] = entry

    with _dns_cache_lock:
        return {h: v[0] for h, v in _resolved_cache.items()}

def _resolve_for_proxy(hostname):
    """Resolve hostname via Google DNS, bypassing the system hosts file."""
    with _dns_cache_lock:
        cached = _resolved_cache.get(hostname)
    if cached and time.monotonic() < cached[1]:
        return cached[0]
    ip, ttl = _dns_query(hostname, _primary_dns)
    if not ip:
        ip, ttl = _dns_query(hostname, _secondary_dns)
    if ip:
        with _dns_cache_lock:
            _resolved_cache[hostname] = (ip, time.monotonic() + ttl)
    return ip

class _ProxyHandler(__import__("socketserver").StreamRequestHandler):
    """Minimal HTTP CONNECT proxy that resolves DNS via Google DNS.
    yt-dlp sends: CONNECT www.youtube.com:443 HTTP/1.1
    We resolve www.youtube.com using Google DNS (bypassing hosts file),
    open a raw TCP tunnel to the real IP, then relay bytes both ways."""

    def handle(self):
        remote = None
        try:
            first_line = self.rfile.readline(4096).decode("utf-8", errors="replace").strip()
            if not first_line.startswith("CONNECT "):
                return
            # Consume remaining headers
            while True:
                line = self.rfile.readline(4096)
                if line in (b"\r\n", b"\n", b""):
                    break

            target = first_line.split(" ")[1]
            if ":" in target:
                host, port_str = target.rsplit(":", 1)
                port = int(port_str)
            else:
                host = target
                port = 443

            # Resolve via Google DNS to bypass hosts file block
            ip = _resolve_for_proxy(host)
            connect_host = ip if ip else host

            remote = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            # Large timeout for initial connect only - removed after tunnel is up
            remote.settimeout(30)
            try:
                remote.connect((connect_host, port))
            except Exception:
                try:
                    self.wfile.write(b"HTTP/1.1 502 Bad Gateway\r\n\r\n")
                    self.wfile.flush()
                except Exception:
                    pass
                return

            self.wfile.write(b"HTTP/1.1 200 Connection established\r\n\r\n")
            self.wfile.flush()

            # Use select() only for reads - send sockets stay blocking so
            # sendall() does the right thing without per-chunk mode toggling.
            client_sock = self.connection
            client_sock.setblocking(False)
            remote.setblocking(False)

            sockets = [client_sock, remote]
            # Long idle timeout - large DASH fragments can pause between chunks
            IDLE_TIMEOUT = 300

            while True:
                try:
                    readable, _, exceptional = select.select(sockets, [], sockets, IDLE_TIMEOUT)
                except Exception:
                    break

                if exceptional or not readable:
                    break

                tunnel_alive = True
                for s in readable:
                    other = remote if s is client_sock else client_sock
                    try:
                        data = s.recv(131072)
                        if not data:
                            tunnel_alive = False
                            break
                        # other stays blocking - sendall blocks until data is sent
                        other.setblocking(True)
                        other.sendall(data)
                        other.setblocking(False)
                    except socket.error as sock_err:
                        err_code = sock_err.args[0]
                        if err_code in (_errno.EAGAIN, _errno.EWOULDBLOCK, 10035):
                            continue
                        tunnel_alive = False
                        break
                    except Exception:
                        tunnel_alive = False
                        break

                if not tunnel_alive:
                    break

        except Exception:
            pass
        finally:
            if remote is not None:
                try:
                    remote.close()
                except Exception:
                    pass

def _start_proxy():
    """Start the local CONNECT proxy on a random port. Returns port number."""
    global _proxy_server, _proxy_port
    import socketserver, threading

    class _TCPServer(socketserver.ThreadingTCPServer):
        allow_reuse_address = True
        daemon_threads = True

    server = _TCPServer(("127.0.0.1", 0), _ProxyHandler)
    port = server.server_address[1]
    t = threading.Thread(target=server.serve_forever, daemon=True)
    t.start()
    _proxy_server = server
    _proxy_port = port
    return port

def _stop_proxy():
    global _proxy_server, _proxy_port
    if _proxy_server:
        try:
            _proxy_server.shutdown()
        except Exception:
            pass
        _proxy_server = None
        _proxy_port = None

def _dns_probe_and_warm():
    """Reachability test + parallel pre-resolve of the YouTube domains.

    This is the slow half of enabling custom DNS: a UDP round trip that can
    wait out its full timeout, followed by a resolve of every YouTube domain
    (each with a secondary-DNS fallback). Safe to run off the main thread -
    _custom_getaddrinfo falls through to normal resolution on a cache miss,
    so nothing breaks while the warm-up is still in flight.

    Returns True if Google DNS answered.
    """
    try:
        _test_ip, _ = _dns_query('www.youtube.com', _primary_dns, timeout=1)
    except Exception:
        _test_ip = None
    try:
        _pre_resolve_all()
    except Exception:
        pass
    return bool(_test_ip)


def enable_custom_dns(probe=True):
    """Turn on custom DNS.

    The hook + proxy are installed immediately (a socket bind and a thread
    start - microseconds). With probe=False the network warm-up is skipped
    so the caller can run _dns_probe_and_warm() in the background; this is
    what startup does, because the old version blocked the main thread for
    up to several seconds BEFORE the window was even built.
    """
    global _custom_dns_active
    _custom_dns_active = True
    socket.getaddrinfo = _custom_getaddrinfo
    with _proxy_lock:
        if _proxy_server is None:
            _start_proxy()
    if not probe:
        return True
    return _dns_probe_and_warm()  # caller can warn user if DNS is unreachable

def disable_custom_dns():
    global _custom_dns_active
    _custom_dns_active = False
    with _dns_cache_lock:
        _resolved_cache.clear()
    socket.getaddrinfo = _original_getaddrinfo
    with _proxy_lock:
        _stop_proxy()

def is_custom_dns_active():
    return _custom_dns_active

def get_proxy_url():
    """Return the local proxy URL to pass to yt-dlp, or None."""
    if _custom_dns_active and _proxy_port:
        return "http://127.0.0.1:" + str(_proxy_port)
    return None
# ---------------------------------------------------------------------------

# Fix working directory and path issues
def fix_paths():
    """Fix working directory and path issues for PyInstaller and double-click execution"""
    if getattr(sys, 'frozen', False):
        # Running as PyInstaller executable
        application_path = os.path.dirname(sys.executable)
        script_dir = application_path
    else:
        # Running as Python script
        script_dir = os.path.dirname(os.path.abspath(__file__))
    
    # Change working directory to script directory
    os.chdir(script_dir)
    
    # Add script directory to Python path
    if script_dir not in sys.path:
        sys.path.insert(0, script_dir)
    
    return script_dir

# Call fix_paths immediately
SCRIPT_DIR = fix_paths()

# ═══════════════════════════════════════════════════════════════════════════
# === BEGIN DEV TOOLS ===  (delete this block + ysa_devtest.py for a
# non-developer build; nothing outside these markers depends on it)
#
# Set to True to expose Settings > Diagnostics, which runs scripted
# end-to-end scenarios from a JSON file. Also switches on automatically
# when a file named 'ysa_dev.flag' sits next to the script/exe, so one
# build can serve both purposes.
DEV_MODE = False
try:
    if os.path.exists(os.path.join(SCRIPT_DIR, 'ysa_dev.flag')):
        DEV_MODE = True
except Exception:
    pass
# === END DEV TOOLS ===
# ═══════════════════════════════════════════════════════════════════════════

# YouTube audio format ID → codec lookup.
# Used to determine AAC vs Opus without spawning an FFmpeg probe process.
# AAC formats: 139 (48kbps), 140 (128kbps), 141 (256kbps), 256/258 (AAC-LC HE)
# Opus formats: 249 (50kbps), 250 (70kbps), 251 (160kbps)
# WebM Vorbis: 171 (128kbps)
# Any unlisted format_id is treated as unknown (probe fallback used).
# Errors that no amount of client-switching will fix. A terminated channel,
# a deleted video or a private one returns the same answer from every player
# client, so grinding through the full cascade wastes ~7 requests per entry
# and looks exactly like the automated hammering YouTube's bot checks target.
_YT_TERMINAL_ERRORS = (
    'account associated with this video has been terminated',
    'this video has been removed',
    'removed by the uploader',
    'video unavailable',
    'this video is private',
    'private video',
    'this video is no longer available',
    'video has been removed for violating',
    'does not exist',
    'available in your country',      # 'The uploader has not made this
                                      #  video available in your country'
    'blocked it in your country',
    'video is unavailable in your country',
    'this video is unavailable',
    # Not yet released. Every client returns the same answer, so the cascade
    # is pure waste - observed as 7 attempts per analysis on a premiere.
    'premieres in',
    'this live event will begin in',
    'this live stream will begin in',
    'this video will be available',
)

_YT_AUDIO_AAC_IDS  = {'139', '140', '141', '256', '258', '327'}
_YT_AUDIO_OPUS_IDS = {'249', '250', '251', '338'}
_YT_AUDIO_VORBIS_IDS = {'171', '172'}

def find_ytdlp_executable():
    """Find yt-dlp executable in order of preference"""
    # Test override: point the app at a stub yt-dlp so failure paths (416,
    # 403, crash-at-exit, disk-full) can be provoked offline and on demand.
    # Purely additive - when YSA_YTDLP_PATH is unset nothing below changes.
    try:
        _override = (os.environ.get('YSA_YTDLP_PATH') or '').strip().strip('"')
        if _override and os.path.exists(_override):
            print('Using yt-dlp override from YSA_YTDLP_PATH: ' + _override)
            return _override
    except Exception:
        pass

    # Method 1: Check in bundle/script directory
    if getattr(sys, 'frozen', False):
        # Running as PyInstaller executable
        bundle_dir = getattr(sys, '_MEIPASS', os.path.dirname(sys.executable))
        local_ytdlp = os.path.join(bundle_dir, "yt-dlp.exe")
    else:
        # Running as Python script
        local_ytdlp = os.path.join(SCRIPT_DIR, "yt-dlp.exe")
    
    if os.path.exists(local_ytdlp):
        print(f"Found yt-dlp.exe in bundle/script directory: {local_ytdlp}")
        return local_ytdlp

    # Method 2: Check environment variable path
    env_ytdlp = r"C:\yt-dlp\yt-dlp.exe"
    if os.path.exists(env_ytdlp):
        print(f"Found yt-dlp.exe in environment path: {env_ytdlp}")
        return env_ytdlp
    
    # Method 3: Check if yt-dlp is in system PATH
    try:
        result = subprocess.run(['yt-dlp', '--version'],
                              capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=5,
                              creationflags=CREATE_NO_WINDOW)
        if result.returncode == 0:
            print("Found yt-dlp in system PATH")
            return 'yt-dlp'
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    
    # Method 4: Try yt-dlp.exe in PATH
    try:
        result = subprocess.run(['yt-dlp.exe', '--version'],
                              capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=5,
                              creationflags=CREATE_NO_WINDOW)
        if result.returncode == 0:
            print("Found yt-dlp.exe in system PATH")
            return 'yt-dlp.exe'
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    
    print("yt-dlp executable not found")
    return None

# Find yt-dlp executable
YTDLP_PATH = find_ytdlp_executable()
YTDLP_AVAILABLE = YTDLP_PATH is not None

# If yt-dlp is not available, show error and exit
if not YTDLP_AVAILABLE:
    error_msg = "yt-dlp executable not found.\n\n"
    error_msg += "Please ensure yt-dlp.exe is available in one of these locations:\n"
    error_msg += "1. Script directory: " + str(SCRIPT_DIR) + "\n"
    error_msg += "2. Environment path: C:\\yt-dlp\\yt-dlp.exe\n"
    error_msg += "3. System PATH\n\n"
    error_msg += "Download yt-dlp.exe from: https://github.com/yt-dlp/yt-dlp/releases"
    
    print(error_msg)
    # Try to show error dialog
    try:
        import tkinter.messagebox as mb
        mb.showerror("Missing Dependency", error_msg)
    except:
        pass
    sys.exit(1)

print(f"Using yt-dlp executable: {YTDLP_PATH}")

# ── bgutil yt-dlp plugin files (embedded) ─────────────────────────────────
# These are written to disk by the Install Plugin button in Settings > bgutil.
_BGUTIL_PLUGIN_VERSION = "1.3.1"
_BGUTIL_PLUGIN_FILES = {
    'getpot_bgutil.py': '''from __future__ import annotations

__version__ = '1.3.1'

import abc
import json
import os
from typing import TypeVar

from yt_dlp.extractor.youtube.pot.provider import (
    ExternalRequestFeature,
    PoTokenContext,
    PoTokenProvider,
    PoTokenProviderRejectedRequest,
)
from yt_dlp.extractor.youtube.pot.utils import WEBPO_CLIENTS
from yt_dlp.utils import js_to_json
from yt_dlp.utils.traversal import traverse_obj

T = TypeVar('T')


class BgUtilPTPBase(PoTokenProvider, abc.ABC):
    PROVIDER_VERSION = __version__
    BUG_REPORT_LOCATION = 'https://github.com/Brainicism/bgutil-ytdlp-pot-provider/issues'
    _SUPPORTED_EXTERNAL_REQUEST_FEATURES = (
        ExternalRequestFeature.PROXY_SCHEME_HTTP,
        ExternalRequestFeature.PROXY_SCHEME_HTTPS,
        ExternalRequestFeature.PROXY_SCHEME_SOCKS4,
        ExternalRequestFeature.PROXY_SCHEME_SOCKS4A,
        ExternalRequestFeature.PROXY_SCHEME_SOCKS5,
        ExternalRequestFeature.PROXY_SCHEME_SOCKS5H,
        ExternalRequestFeature.SOURCE_ADDRESS,
        ExternalRequestFeature.DISABLE_TLS_VERIFICATION,
    )
    _SUPPORTED_CLIENTS = WEBPO_CLIENTS
    _SUPPORTED_CONTEXTS = (
        PoTokenContext.GVS,
        PoTokenContext.PLAYER,
        PoTokenContext.SUBS,
    )
    _GETPOT_TIMEOUT = 20.0

    def _info_and_raise(self, msg, raise_from=None):
        self.logger.info(msg)
        raise PoTokenProviderRejectedRequest(msg) from raise_from

    def _warn_and_raise(self, msg, once=True, raise_from=None):
        self.logger.warning(msg, once=once)
        raise PoTokenProviderRejectedRequest(msg) from raise_from

    def _script_config_arg(self, key: str, default: T = None, *, casesense=True) -> str | T:
        return self.ie._configuration_arg(
            ie_key='youtubepot-bgutilscript', key=key, default=[default], casesense=casesense)[0]

    @staticmethod
    def _resolve_script_path(*ps: str):
        # realpath resolves symlinks and internally calls abspath
        return os.path.realpath(
            os.path.expanduser(os.path.expandvars(os.path.join(*ps))))

    def _script_path_provided(self) -> str | None:
        if server_home := self._script_config_arg('server_home'):
            return self._resolve_script_path(server_home)

        if script_path := self._script_config_arg('script_path'):
            return self._resolve_script_path(script_path, os.pardir, os.pardir)

        return None

    def _check_version(self, got_version, *, default='unknown', name):
        def _major(version):
            return version.split('.', 1)[0]

        if got_version != self.PROVIDER_VERSION:
            self.logger.warning(
                f'The provider plugin and the {name} are on different versions, '
                f'this may cause compatibility issues. '
                f'Please ensure they are on the same version. '
                f'Otherwise, help will NOT be provided for any issues that arise. '
                f'(plugin: {self.PROVIDER_VERSION}, {name}: {got_version or default})',
                once=True)

        if not got_version or _major(got_version) != _major(self.PROVIDER_VERSION):
            self._warn_and_raise(
                f'Plugin and {name} major versions are mismatched. '
                f'Update both the plugin and the {name} to the same version to proceed.')

    def _get_attestation(self, webpage: str | None):
        if not webpage:
            return None
        raw_cd = (
            traverse_obj(
                self.ie._search_regex(
                    r\'\'\'(?sx)window\\s*\\.\\s*ytAtN\\s*\\(\\s*
                        (?P<js>\\{.+?}\\s*)
                    \\s*\\)\\s*;\'\'\', webpage, 'ytAtP challenge', default=None),
                ({js_to_json}, {json.loads}, 'R'))
            or traverse_obj(
                self.ie._search_regex(
                    r\'\'\'(?sx)window\\.ytAtR\\s*=\\s*(?P<raw_cd>(?P<q>['"])
                        (?:
                            \\\\.|
                            (?!(?P=q)).
                        )*
                    (?P=q))\\s*;\'\'\', webpage, 'ytAtR challenge', default=None),
                ({js_to_json}, {json.loads})))

        if att_txt := traverse_obj(raw_cd, ({json.loads}, 'bgChallenge')):
            return att_txt
        self.logger.warning('Failed to extract initial attestation from the webpage')
        return None


__all__ = ['__version__']
''',
    'getpot_bgutil_http.py': '''from __future__ import annotations

import functools
import json
import time

from yt_dlp.extractor.youtube.pot.provider import (
    PoTokenProviderError,
    PoTokenProviderRejectedRequest,
    PoTokenRequest,
    PoTokenResponse,
    register_preference,
    register_provider,
)
from yt_dlp.extractor.youtube.pot.utils import get_webpo_content_binding
from yt_dlp.networking.common import Request
from yt_dlp.networking.exceptions import HTTPError, TransportError

from yt_dlp_plugins.extractor.getpot_bgutil import BgUtilPTPBase


@register_provider
class BgUtilHTTPPTP(BgUtilPTPBase):
    PROVIDER_NAME = 'bgutil:http'
    DEFAULT_BASE_URL = 'http://127.0.0.1:4416'
    _GET_SERVER_VSN_TIMEOUT = 5.0

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._last_server_check = 0
        self._server_available = True

    @functools.cached_property
    def _base_url(self):
        base_url = self._configuration_arg('base_url', default=[None])[0]

        if base_url:
            return base_url

        # check deprecated arg
        deprecated_base_url = self.ie._configuration_arg(
            ie_key='youtube', key='getpot_bgutil_baseurl', default=[None])[0]
        if deprecated_base_url:
            self._warn_and_raise(
                "'youtube:getpot_bgutil_baseurl' extractor arg is deprecated, use 'youtubepot-bgutilhttp:base_url' instead")

        # default if no arg was passed
        self.logger.debug(
            f'No base_url provided, defaulting to {self.DEFAULT_BASE_URL}')
        return self.DEFAULT_BASE_URL

    def _check_server_availability(self, ctx: PoTokenRequest):
        if self._last_server_check + 60 > time.time():
            return self._server_available

        self._server_available = False
        try:
            self.logger.trace(
                f'Checking server availability at {self._base_url}/ping')
            response = json.load(self._request_webpage(Request(
                f'{self._base_url}/ping', extensions={'timeout': self._GET_SERVER_VSN_TIMEOUT}, proxies={'all': None}),
                note=False))
        except TransportError as e:
            # the server may be down
            warning_base = f'Error reaching GET {self._base_url}/ping (caused by {e.__class__.__name__}). '
            if self._script_path_provided() is not None:  # server down is expected, log info
                self._info_and_raise(
                    warning_base + 'This is expected if you are using the script method.')
            else:
                self._warn_and_raise(
                    warning_base + f'Please make sure that the server is reachable at {self._base_url}.')

            return
        except HTTPError as e:
            # may be an old server, don't raise
            self.logger.warning(
                f'HTTP Error reaching GET /ping (caused by {e!r})', once=True)
            return
        except json.JSONDecodeError as e:
            # invalid server
            self._warn_and_raise(
                f'Error parsing ping response JSON (caused by {e!r})')
            return
        except Exception as e:
            self._warn_and_raise(
                f'Unknown error reaching GET /ping (caused by {e!r})', raise_from=e)
            return
        else:
            self._check_version(response.get('version', ''), name='HTTP server')
            self._server_available = True
            return True
        finally:
            self._last_server_check = time.time()

    def is_available(self):
        return self._server_available or self._last_server_check + 60 < int(time.time())

    def _real_request_pot(
        self,
        request: PoTokenRequest,
    ) -> PoTokenResponse:
        if not self._check_server_availability(request):
            raise PoTokenProviderRejectedRequest(
                f'{self.PROVIDER_NAME} server is not available')

        # used for CI check
        self.logger.trace('Generating POT via HTTP server')

        if self._configuration_arg('disable_innertube', default=[None])[0] is not None:
            self._warn_and_raise(
                "'youtubepot-bgutilhttp:disable_innertube' extractor arg is deprecated")

        challenge = self._get_attestation(request.video_webpage)
        # The challenge is falsy when the webpage and the challenge are unavailable
        # In this case, we need to disable /att/get since it's broken for web_music
        if not challenge and request.internal_client_name == 'web_music':
            self._warn_and_raise(
                'BotGuard challenges could not be obtained from the webpage, '
                'a PO Token cannot be generated because InnerTube challenges '
                'are currently broken for the web_music client. ')

        try:
            response = self._request_webpage(
                request=Request(
                    f'{self._base_url}/get_pot', data=json.dumps({
                        'bypass_cache': request.bypass_cache,
                        'challenge': challenge,
                        'content_binding': get_webpo_content_binding(request)[0],
                        'disable_tls_verification': not request.request_verify_tls,
                        'proxy': request.request_proxy,
                        'innertube_context': request.innertube_context,
                        'source_address': request.request_source_address,
                    }).encode(), headers={'Content-Type': 'application/json'},
                    extensions={'timeout': self._GETPOT_TIMEOUT}, proxies={'all': None}),
                note=f'Generating a {request.context.value} PO Token for '
                f'{request.internal_client_name} client via bgutil HTTP server',
            )
        except Exception as e:
            raise PoTokenProviderError(
                f'Error reaching POST /get_pot (caused by {e!r})') from e

        try:
            response_json = json.load(response)
        except Exception as e:
            raise PoTokenProviderError(
                f'Error parsing response JSON (caused by {e!r}). response = {response.read().decode()}') from e

        if error_msg := response_json.get('error'):
            raise PoTokenProviderError(error_msg)
        if 'poToken' not in response_json:
            raise PoTokenProviderError(
                f'Server did not respond with a poToken. Received response: {response}')

        po_token = response_json['poToken']
        self.logger.trace(f'Generated POT: {po_token}')
        return PoTokenResponse(po_token=po_token)


@register_preference(BgUtilHTTPPTP)
def bgutil_HTTP_getpot_preference(provider, request):
    return 130


__all__ = [BgUtilHTTPPTP.__name__,
           bgutil_HTTP_getpot_preference.__name__]
''',
    'getpot_bgutil_script.py': '''from __future__ import annotations

import abc
import functools
import json
import os
import re
import subprocess
import sys
import sysconfig
from typing import Iterable

from yt_dlp.extractor.youtube.pot.provider import (
    PoTokenProviderError,
    PoTokenRequest,
    PoTokenResponse,
    register_preference,
    register_provider,
)
from yt_dlp.extractor.youtube.pot.utils import get_webpo_content_binding
from yt_dlp.utils import Popen, int_or_none, shell_quote
from yt_dlp.utils.traversal import traverse_obj

from yt_dlp_plugins.extractor.getpot_bgutil import BgUtilPTPBase

_FALLBACK_PATHEXT = ('.COM', '.EXE', '.BAT', '.CMD')


# Copied from https://github.com/yt-dlp/yt-dlp/blob/891613b098b2b315d983c2ae16901f5de344ca56/yt_dlp/utils/_jsruntime.py#L16-L64
# NOTE: keep in sync with upstream
def _find_exe(basename: str) -> str:
    # Check in Python "scripts" path, e.g. for pipx-installed binaries
    binary = os.path.join(
        sysconfig.get_path('scripts'),
        basename + sysconfig.get_config_var('EXE'))
    if os.access(binary, os.F_OK | os.X_OK) and not os.path.isdir(binary):
        return binary

    if os.name != 'nt':
        return basename

    paths: list[str] = []

    # binary dir
    if getattr(sys, 'frozen', False):
        paths.append(os.path.dirname(sys.executable))
    # cwd
    paths.append(os.getcwd())
    # PATH items
    if path := os.environ.get('PATH'):
        paths.extend(filter(None, path.split(os.path.pathsep)))

    pathext = os.environ.get('PATHEXT')
    if pathext is None:
        exts = _FALLBACK_PATHEXT
    else:
        exts = tuple(ext for ext in pathext.split(os.pathsep) if ext)

    visited = []
    for path in map(os.path.realpath, paths):
        normed = os.path.normcase(path)
        if normed in visited:
            continue
        visited.append(normed)

        for ext in exts:
            binary = os.path.join(path, f'{basename}{ext}')
            if os.access(binary, os.F_OK | os.X_OK) and not os.path.isdir(binary):
                return binary

    return basename


def _determine_runtime_path(path, basename):
    if not path:
        return _find_exe(basename)
    if os.path.isdir(path):
        return os.path.join(path, basename)
    return path


class BgUtilScriptPTPBase(BgUtilPTPBase, abc.ABC):
    _GET_SCRIPT_VSN_TIMEOUT = 15.0

    @staticmethod
    def _jsrt_vsn_tup(v: str):
        return tuple(int_or_none(x, default=0) for x in v.split('.'))

    def __init_subclass__(cls):
        super().__init_subclass__()
        pref = cls._JSRT_PREF
        register_preference(cls)(lambda provider, request: pref)

    _SCRIPT_BASENAME: str
    _JSRT_NAME: str  # Name of the JS Runtime shown in logs
    _JSRT_EXEC: str  # Name of the executable, and the name used in yt-dlp
    _JSRT_VSN_REGEX: str
    _JSRT_MIN_VER: tuple[int, ...]
    _JSRT_PREF: int

    @abc.abstractmethod
    def _script_path_impl(self) -> str:
        raise NotImplementedError

    def _jsrt_args(self) -> Iterable[str]:
        return ()

    def _jsrt_envs(self) -> dict:
        return os.environ.copy()

    def _jsrt_path_impl(self) -> str | None:
        jsrt_path = _determine_runtime_path(
            traverse_obj(self.ie.get_param('js_runtimes'), (self._JSRT_EXEC, 'path')),
            self._JSRT_EXEC)
        try:
            output, _, returncode = Popen.run(
                [jsrt_path, '--version'], env=self._jsrt_envs(), timeout=5.0,
                text=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            output = output.strip()
        except subprocess.TimeoutExpired:
            self.logger.debug(
                f'Failed to check {self._JSRT_NAME} version: {self._JSRT_NAME} process '
                'did not finish in 5.0 seconds', once=True)
            return None
        except FileNotFoundError:
            self.logger.debug(
                f'{self._JSRT_NAME} executable not found. Please ensure {self._JSRT_NAME} is '
                'installed and available in PATH or passed to yt-dlp with --js-runtimes.', once=True)
            return None
        mobj = re.search(self._JSRT_VSN_REGEX, output)
        if returncode or not mobj:
            self.logger.debug(
                f'Failed to check {self._JSRT_NAME} version. '
                f'{self._JSRT_NAME} returned {returncode} exit status. '
                f'Process output:\\n{output}', once=True)
            return None
        if self._jsrt_has_support(mobj.group(1)):
            return jsrt_path

    def _jsrt_has_support(self, v: str) -> bool:
        if self._jsrt_vsn_tup(v) >= self._JSRT_MIN_VER:
            self.logger.trace(f'{self._JSRT_NAME} version: {v}')
            return True
        else:
            min_vsn_str = '.'.join(map(str, self._JSRT_MIN_VER))
            self.logger.debug(
                f'{self._JSRT_NAME} version too low. '
                f'(got {v}, but at least {min_vsn_str} is required)', once=True)
            return False

    @functools.cached_property
    def _script_path(self) -> str:
        return self._script_path_impl()

    @functools.cached_property
    def _jsrt_path(self) -> str | None:
        return self._jsrt_path_impl()

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self._check_script = functools.cache(self._check_script_impl)

    @functools.cached_property
    def _server_home(self) -> str:
        if path := self._script_path_provided():
            return path

        # default if no arg was passed
        default_home = self._resolve_script_path('~', 'bgutil-ytdlp-pot-provider', 'server')
        self.logger.debug(
            f'No server_home or script_path passed, defaulting to {default_home}', once=True)
        return default_home

    @functools.cached_property
    def _script_cache_dir(self) -> str:
        # don't use _HOMEDIR as the server is coded this way and accepts HOME and USERPROFILE regardless of the OS
        home_dir = os.getenv('HOME') or os.getenv('USERPROFILE')
        if (xdg_cache := os.getenv('XDG_CACHE_HOME')) is not None:
            return os.path.abspath(os.path.join(xdg_cache, 'bgutil-ytdlp-pot-provider'))
        elif home_dir:
            return os.path.abspath(os.path.join(home_dir, '.cache', 'bgutil-ytdlp-pot-provider'))
        else:
            return self._server_home

    def is_available(self) -> bool:
        return self._check_script(self._script_path)

    def _check_script_impl(self, script_path) -> bool:
        if not os.path.isfile(script_path):
            self.logger.debug(
                f"Script path doesn't exist: {script_path}", once=True)
            return False
        if os.path.basename(script_path) != self._SCRIPT_BASENAME:
            self.logger.warning(
                f'The script path passed in the extractor argument '
                f'has a wrong base name, expected {self._SCRIPT_BASENAME}.', once=True)
            return False
        if not self._jsrt_path:
            return False
        stdout, _, returncode = Popen.run(
            [self._jsrt_path, *self._jsrt_args(), script_path, '--version'],
            env=self._jsrt_envs(), timeout=self._GET_SCRIPT_VSN_TIMEOUT,
            text=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE)
        stdout = stdout.strip()
        if returncode:
            self.logger.warning(
                f'Failed to check script version. '
                f'Script returned {returncode} exit status. '
                f'Script stdout:\\n{stdout}',
                once=True)
            return False
        else:
            self._check_version(stdout, name='script')
            return True

    def _real_request_pot(
        self,
        request: PoTokenRequest,
    ) -> PoTokenResponse:
        # used for CI check
        self.logger.trace(
            f'Generating POT via script: {self._script_path}')

        command_args = [self._jsrt_path, *self._jsrt_args(), self._script_path]
        if proxy := request.request_proxy:
            command_args.extend(['-p', proxy])
        command_args.extend(['-c', get_webpo_content_binding(request)[0]])
        command_args.extend(['--innertube-context', json.dumps(request.innertube_context)])
        if request.bypass_cache:
            command_args.append('--bypass-cache')
        if request.request_source_address:
            command_args.extend(
                ['--source-address', request.request_source_address])
        if request.request_verify_tls is False:
            command_args.append('--disable-tls-verification')

        self.logger.info(
            f'Generating a {request.context.value} PO Token for '
            f'{request.internal_client_name} client via bgutil script',
        )
        self.logger.debug(
            f'Executing command to get POT via script: {" ".join(map(shell_quote, command_args))}')

        try:
            stdout, _, returncode = Popen.run(
                command_args, env=self._jsrt_envs(), timeout=self._GETPOT_TIMEOUT,
                text=True, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE)
            stdout_lines = stdout.strip().splitlines()
            json_resp = stdout_lines.pop()
        except subprocess.TimeoutExpired as e:
            raise PoTokenProviderError(
                f'_get_pot_via_script failed: Timeout expired when trying to run script (caused by {e!r})')
        except Exception as e:
            raise PoTokenProviderError(
                f'_get_pot_via_script failed: Unable to run script (caused by {e!r})') from e

        if stdout_extra := '\\n'.join(stdout_lines):
            self.logger.debug(f'script stdout:\\n{stdout_extra}')
        if returncode:
            raise PoTokenProviderError(
                f'_get_pot_via_script failed with returncode {returncode}')

        try:
            self.logger.trace(f'JSON response:\\n{json_resp}')
            # The JSON response is always the last line
            script_data_resp = json.loads(json_resp)
        except json.JSONDecodeError as e:
            raise PoTokenProviderError(
                f'Error parsing JSON response from _get_pot_via_script (caused by {e!r})') from e
        if 'poToken' not in script_data_resp:
            raise PoTokenProviderError(
                'The script did not respond with a po_token')
        return PoTokenResponse(po_token=script_data_resp['poToken'])


@register_provider
class BgUtilScriptNodePTP(BgUtilScriptPTPBase):
    PROVIDER_NAME = 'bgutil:script-node'
    _SCRIPT_BASENAME = 'generate_once.js'
    _JSRT_NAME = 'Node.js'
    _JSRT_EXEC = 'node'
    _JSRT_VSN_REGEX = r'^v(\\S+)'
    _JSRT_MIN_VER = (20, 0, 0)
    _JSRT_PREF = 10

    def _script_path_impl(self) -> str:
        return os.path.join(
            self._server_home, 'build', self._SCRIPT_BASENAME)


@register_provider
class BgUtilScriptDenoPTP(BgUtilScriptPTPBase):
    PROVIDER_NAME = 'bgutil:script-deno'
    _SCRIPT_BASENAME = 'generate_once.ts'
    _JSRT_NAME = 'Deno'
    _JSRT_EXEC = 'deno'
    _JSRT_VSN_REGEX = r'^deno (\\S+)'
    _JSRT_MIN_VER = (2, 0, 0)
    _JSRT_PREF = 20

    def _script_path_impl(self) -> str:
        return os.path.join(
            self._server_home, 'src', self._SCRIPT_BASENAME)

    def _jsrt_args(self) -> Iterable[str]:
        def escpath(*strs: str):
            return ','.join(s.replace(',', ',,') for s in strs)
        node_mods_path = os.path.join(self._server_home, 'node_modules')
        return (
            'run', '--allow-env', '--allow-net',
            f'--allow-ffi={escpath(node_mods_path)}',
            f'--allow-write={escpath(self._script_cache_dir)}',
            f'--allow-read={escpath(self._script_cache_dir, node_mods_path)}',
        )

    def _jsrt_envs(self) -> dict:
        process_env = os.environ.copy()
        process_env['DENO_NO_PROMPT'] = '1'
        process_env['DENO_NO_UPDATE_CHECK'] = '1'
        process_env['FORCE_COLOR'] = 'false'
        return process_env


__all__ = [
    BgUtilScriptNodePTP.__name__,
    BgUtilScriptDenoPTP.__name__,
]
''',
}

class _DownloadStoppedError(Exception):
    """Raised when the user clicks Stop - workers should exit without retrying."""

class _DownloadPausedError(Exception):
    """Raised when the user clicks Pause - workers should exit without retrying."""

# Pre-compiled regex patterns for yt-dlp progress parsing (hot path ~10x/sec)
_RE_PROGRESS_PCT = re.compile(r"([\d.]+)%")
_RE_PROGRESS_SPD = re.compile(r"at\s+(\S+)")
_RE_PROGRESS_ETA = re.compile(r"ETA\s+(\S+)")

class YouTubeStreamAnalyzerGUI:
    def __init__(self, root):
        self.root = root
        self.root.title("YouTube Stream Analyzer")
        self.root.geometry("1000x1100")   # provisional; saved box applied after _load_config
        self.root.minsize(800, 600)
        
        # Configure style
        style = ttk.Style()
        style.theme_use('clam')
        # Register subtitle combo styles with light-mode defaults so they exist
        # immediately - before _apply_dark_mode fires via root.after(50).
        # Without this, _update_subtitle_combo_states sets a style name that
        # doesn't exist yet and the combos fall back to plain TCombobox rendering.
        style.configure('SubtitleActive.TCombobox',
            fieldbackground='SystemWindow', foreground='SystemWindowText',
            background='SystemButtonFace', selectbackground='SystemHighlight',
            selectforeground='SystemHighlightText')
        style.map('SubtitleActive.TCombobox',
            fieldbackground=[('readonly', 'SystemWindow')],
            foreground=[('readonly', 'SystemWindowText')])
        style.configure('SubtitleDisabled.TCombobox',
            fieldbackground='#d0d0d0', foreground='#888888',
            background='#d0d0d0', selectbackground='#d0d0d0',
            selectforeground='#888888', arrowcolor='#aaaaaa')
        style.map('SubtitleDisabled.TCombobox',
            fieldbackground=[('readonly', '#d0d0d0'), ('disabled', '#d0d0d0')],
            foreground=[('readonly', '#888888'), ('disabled', '#888888')])
        # Auto-download combo: white when enabled, grey when disabled
        style.configure('Disabled.TCombobox',
            fieldbackground='#d0d0d0', foreground='#888888',
            background='#d0d0d0', arrowcolor='#aaaaaa')
        style.map('Disabled.TCombobox',
            fieldbackground=[('disabled', '#d0d0d0'), ('readonly', '#d0d0d0')],
            foreground=[('disabled', '#888888'), ('readonly', '#888888')])
        # Variables
        self.current_video_info = {}
        self.current_formats = []
        self.download_history = []   # [{url, channel, title, quality, timestamp, file_path}]
        self._precache_progress = {}  # {video_id: 'progress string'} - live progress from precache

        # Config defaults (overridden by _load_config below)
        self.download_path = os.path.expanduser("~/Downloads")
        self.default_quality = "1080p"
        self.dark_mode = False
        self.persistent_cache = False
        self.max_cache_mb = 0
        self.auto_update_tools = True
        # 'nightly' | 'stable'. Upstream's README calls nightly the recommended
        # channel for regular users and warns that the latest stable release is
        # often stale and prone to breakage when sites change. Nightly also
        # ended a run of extraction failures here, so it is the default.
        self.ytdlp_channel = 'nightly'
        # Resolution size-limit settings
        self.size_limit_enabled = False      # Enable size-based quality cap
        self.size_limit_mb = 500             # Max MB for preferred quality video stream
        self.size_limit_fallback = '1080p'   # Resolution to fall back to if over limit
        self.size_upgrade_enabled = False    # Upgrade to higher res if under limit
        self.size_upgrade_to = '2160p'       # Max resolution to try when upgrading
        self.preferred_language = "en"
        self.player_client = "default"       # yt-dlp player client for downloads
        self.prewarm_enabled = True          # Pre-warm next queued stream before download starts
        self.parallel_hardsub = False        # When True, queue continues while hardsub runs
        self._hardsub_probe_lock = threading.Lock()  # hardsub encoder probe (batch 1a)
        # 'libx264' (default) | 'auto'. Software WINS for burn-in on this
        # class of machine: the subtitles filter is CPU-only, so hardware
        # decode/encode adds a GPU->RAM->GPU round trip per frame. Measured
        # on an Intel iGPU, same video, cached streams, power saving:
        # 360p 4.3s software vs 12.4-13.7s QSV; 720p AV1 9.2s vs 18.2s.
        # 'auto' stays available for a discrete GPU, where it may pay off.
        self.hardsub_encoder = 'libx264'
        self.advance_queue_on_streams_done = False  # Advance queue as soon as streams cached, before post-processing
        self.precache_concurrent_count = 1   # Number of queue items to precache simultaneously
        self.batch_concurrent_fetches = 3    # Parallel info-fetch workers during batch analysis
        self.clipboard_watch = False
        self.clear_cache_on_exit = False   # wipe every cache folder at exit         # Auto-paste YouTube URLs detected in clipboard
        self.batch_start_immediately = True  # Start downloading immediately when batch runs
        self.terminal_expanded = True        # Terminal visible on startup
        self.custom_dns = True               # Use Google DNS proxy by default
        # Output filename options
        self.filename_include_date = False   # Prepend upload date to output filename
        # filename_format controls the order of components in the output filename.
        # Options: 'channel - title', 'title - channel', 'date - channel - title',
        #          'date - title - channel', 'title', 'date - title'
        self.filename_format = 'channel - title'
        # Cookies browser for age-restricted / login-required videos
        # Options: 'none', 'firefox', 'chrome', 'edge', 'brave', 'chromium', 'opera', 'safari', 'vivaldi'
        self.cookies_browser = 'none'
        # Path to a Netscape-format cookies.txt file (takes priority over
        # cookies_browser when set). Auto-detected from SCRIPT_DIR on startup.
        self.cookies_file = ''
        self.cookies_enabled = True  # Toolbar toggle - persisted in config.json
        # bgutil PO token provider settings
        # URL of the bgutil HTTP server (default port 4416)
        self.bgutil_server_url = 'http://127.0.0.1:4416'
        # Path to the bgutil server directory (for auto-start)
        self.bgutil_server_path = ''
        # Whether bgutil server was detected running at last check
        self._bgutil_running = False
        self._bgutil_process = None  # subprocess handle if YSA started it
        self.bgutil_autostart = False  # auto-start server on YSA launch
        self.bgutil_keep_running = True  # keep server running when YSA closes
        self.extended_client_cascade = True  # Try multiple player clients on failure
        # Metadata field toggles (all on by default, individually saveable)
        self.embed_metadata = True           # Master metadata toggle (persisted)
        self.meta_embed_title = True
        self.meta_embed_artist = True
        self.meta_embed_date = True
        self.meta_embed_comment = True
        self.meta_embed_synopsis = True
        # Subtitle embedding
        self.embed_subtitles = False         # legacy - kept for config migration
        self.subtitle_source = "off"         # "off" / "manual" / "auto"
        self.subtitle_last_source = "manual" # Remembers combo selection when toggle is off
        self.subtitle_mode   = "S"           # "S" / "SD" / "HS"
        self.subtitle_lang   = "en"          # Preferred subtitle language code
        # Audio stream preference
        self.preferred_audio_bitrate = 0     # 0 = highest available
        self.preferred_video_bitrate = 0     # 0 = highest available per resolution
        # HLS/m3u8 video streams are hidden from Recommended by default. Their
        # FILESIZE/TBR are advertised manifest figures, not measured: yt-dlp
        # prints them with '~' and marks them Untested, and they can overstate
        # badly (a 2.03GiB row delivered 447MB here; upstream reports 5.06GB ->
        # 1.8GB). Every resolution they offer already has a DASH stream with an
        # EXACT byte count, so nothing is lost. This is NOT about Premium -
        # yt-dlp labels those 'Premium' explicitly and they are unaffected.
        self.include_hls_streams = False
        # Hand the already-fetched analysis to the download legs with
        # --load-info-json instead of making each leg extract again. Stream
        # URLs were measured at a 6-hour lifetime, so this is safe with a
        # wide margin; any failure falls back automatically.
        self.reuse_info_json = True
        self._info_json_disabled = False
        self.audio_only_mode_default = False  # Persisted across sessions via config
        self.audio_only_format = 'm4a_native'         # 'm4a_native', 'm4a_aac', or 'mp3'
        # ── Audio behaviour settings (Settings > Audio) ──────────────────
        self.audio_opus_naming     = 'codec'         # codec|m4a|remux|prefer_aac
        self.audio_bitrate_policy  = 'match_source'  # match_source|match_pref|fixed|max
        self.audio_fixed_bitrate   = 128             # used when policy == 'fixed'
        self.audio_drc_pref        = 'avoid'         # avoid|allow|prefer
        self.audio_quality_tag     = 'audio'         # audio|video|none
        self.audio_no_aac_action   = 'transcode'     # transcode|keep_opus|skip
        self.audio_cache_streams   = True            # cache raw audio-only streams
        self.audio_output_folder   = ''              # '' = same as download_path
        self.audio_duplicate_action = 'number'       # number|overwrite|skip
        # Indirection so the dev test runner can sandbox itself onto a
        # separate config and cache without touching the real ones.
        self.config_filename = 'ysa_config.json'
        self.cache_dirname   = 'ysa_cache' 
        self.state_dirname   = 'ysa_state'  # logs + yt-dlp cache: survives cache clears
        # Clear Cache Now is scorched earth by design; these say what it
        # spares. Logs default to PRESERVED - they are the flight recorder
        # this project debugs from. Clear-on-EXIT ignores all three.
        self.preserve_logs_on_clear    = True
        self.preserve_ytdlp_on_clear   = False
        self.preserve_history_on_clear = False
        # ── Interface ────────────────────────────────────────────────────
        self.history_enabled  = True    # record finished downloads in History
        self.remember_window  = True    # restore window size/position
        self.window_geometry  = ''      # 'WxH+X+Y' from the last clean exit
        self.window_maximized = False
        self.devtest_scenario_file = ''  # dev tools: last scenario file used
        self.devtest_selected = []       # dev tools: scenario names to run ([] = all)
        self.stub_enabled = False        # dev tools: fake yt-dlp active
        self.stub_mode = 'ok'            # dev tools: which failure to simulate
        self.stub_fail_times = 0         # dev tools: fail N times, then succeed
        self._real_ytdlp_path = None     # remembered so the stub can be undone
        self._real_cache_dirname = None  # ditto for the cache + output folder
        self._real_state_dirname = None  # ditto for the state folder (logs + yt-dlp)
        self._real_download_path = None

        # Load persistent configuration (overrides defaults above)
        self._load_config()
        # Saved window box can only be applied AFTER the config is read -
        # the earlier geometry() call above runs before window_geometry
        # exists, so restoring there silently did nothing.
        self._apply_saved_geometry("1000x1100")
        # Auto-detect cookies.txt in the same directory as the exe/script.
        # Only sets the path if the user has not already configured one.
        if not self.cookies_file:
            _auto_cookies = os.path.join(SCRIPT_DIR, 'cookies.txt')
            if os.path.isfile(_auto_cookies):
                self.cookies_file = _auto_cookies

        self.ffmpeg_path = self.find_ffmpeg()
        self.download_start_time = None
        self._session_download_counter = 0  # Increments for each download, used by Queue Index slot
        self.ytdlp_path = YTDLP_PATH

        # Feature toggles
        self.audio_only_mode = tk.BooleanVar(value=self.audio_only_mode_default)
        self.embed_metadata_enabled = tk.BooleanVar(value=self.embed_metadata)
        self.custom_dns_enabled = tk.BooleanVar(value=self.custom_dns)
        # Thread-safe mirrors (M3): workers read these plain attributes
        # instead of touching Tk variables off the main thread.
        self._mk_var_mirror(self.audio_only_mode, '_m_audio_only', bool)
        self._mk_var_mirror(self.embed_metadata_enabled, '_m_embed', bool)
        self._mk_var_mirror(self.custom_dns_enabled, '_m_dns', bool)

        # Auto-enqueue guard (True = disabled; reset to False on each fresh analyze)
        self._auto_enqueue_done = True

        # Initialize progress tracking
        self.current_progress_line = None
        self._terminal_line_count = 0      # Counter for terminal buffer trimming (avoids full read)
        self._progress_line_index = None   # Tkinter text index of the current progress line

        # Download control
        self._download_process = None   # Currently running yt-dlp subprocess
        self._ffmpeg_process   = None   # Currently running FFmpeg subprocess (merge phase)
        self._audio_bg_process = None   # Background audio download subprocess (concurrent path)
        self._download_paused = False   # True while paused (process killed, file kept)
        self._download_stopped = False  # True if user hit Stop
        self._resume_target = None      # Worker function to call on Resume
        self._resume_args = ()          # Args to pass to that worker
        self._download_active = False   # True from thread-start until complete/error/stop;
                                        # fills the gap before _download_process is set

        # Download queue  {worker_fn, args, label} dicts waiting to run
        self._download_queue = []
        self._queue_lock = threading.Lock()

        # URL analysis queue - URLs waiting to be analyzed sequentially so that
        # rapidly copying multiple links never drops or races against each other.
        self._url_analysis_queue    = []
        self._url_analysis_busy     = False
        self._currently_analyzing_url   = ''   # URL whose analysis is in-flight
        self._currently_downloading_url = ''   # URL whose download thread is active
        # Controls whether the _update_video_info finally block advances the
        # analysis queue.  'pending' = advance normally; 'deferred' = a re-fetch
        # thread owns the signal; 'done' should never appear in finally (safety).
        self._analysis_done_mode = 'pending'
        # Set by _on_url_analysis_done to unblock the batch worker when a re-fetch
        # completes.  None when no batch is running.
        self._batch_item_done_evt = None
        # Prefetched video info for the next URL in the analysis queue.
        # Written by the current worker thread after posting its result,
        # read by the next worker thread to skip the yt-dlp call.
        self._prefetched_info = {}  # {url: info_dict}
        self._prefetch_in_progress = set()  # URLs currently being prefetched
        
        # Initialize cache tracking BEFORE setting up cache directories
        self._output_listeners = []                # dev test runner taps terminal output
        self._cache_inuse = set()                  # cached paths a live download is reading
        self._ck_reap_lock = threading.Lock()       # only one cookie reaper at a time
        self._precache_lock = threading.Lock()     # created here, not lazily (first-use race)
        self._cache_lock = threading.RLock()       # C1: protects cached_videos and thumbnail set
        self._thumbnail_cached_ids = set()         # C2: avoids os.path.exists per precache item
        self.cached_videos = {}  # {video_id: {format_id: file_path}}  -- video AND audio streams
        self.cached_subtitles = {}  # {video_id: {cache_key: file_path}}
        self.subtitle_cache_dir = None   # Set in setup_cache_directories
        self.thumbnail_cache_dir = None  # Set in setup_cache_directories
        self.premuxed_cache_dir = None   # Set in setup_cache_directories
        self.cached_premuxed = {}        # {video_id: {format_id: file_path}}
        self._cache_size_bytes = 0  # Running total updated incrementally - avoids os.walk on hot path
        self.audio_cache_dir = None  # Set properly in setup_cache_directories
        self.cache_metadata = {}  # Store cache info for cleanup
        
        # Video cache system - store in system temp directory
        self.setup_cache_directories()
        
        # Register cleanup on exit
        atexit.register(self.cleanup_on_exit)

        # Enable/disable custom DNS based on loaded config
        if self.custom_dns:
            # Install the hook + proxy now (microseconds), then warm up the
            # DNS cache off-thread. Previously the probe and the pre-resolve
            # of every YouTube domain ran here on the main thread, before
            # setup_ui(), so the window could not appear until they finished.
            enable_custom_dns(probe=False)

            def _dns_warmup():
                _ok = _dns_probe_and_warm()
                if not _ok:
                    self.root.after(0, lambda: self.append_terminal_output(
                        "WARNING: Custom DNS is ON but Google DNS (8.8.8.8) is unreachable\n"
                        "on this network. Downloads will stall. Go to Settings and\n"
                        "turn OFF Custom DNS to fix this.\n", "warning"))
            threading.Thread(target=_dns_warmup, daemon=True).start()
        else:
            disable_custom_dns()
        
        self.setup_ui()

        # Register window close handler so X button triggers clean shutdown
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self.persistent_cache_var = tk.BooleanVar(value=self.persistent_cache)
        self.dark_mode_var = tk.BooleanVar(value=self.dark_mode)

        # Apply dark mode if configured
        if self.dark_mode:
            self.root.after(50, self._apply_dark_mode)

        # Restore queue from previous session after widgets are ready
        self.root.after(1200, self._restore_queue)

        # Start clipboard watch if it was enabled last session
        if self.clipboard_watch:
            self.root.after(1500, self._start_clipboard_watch)

        # Show startup path information on first run
        self.show_startup_paths()

    def show_startup_paths(self):
        """Show executable paths on startup for debugging"""
        # Only show if either executable is missing
        missing_executables = []
        if not self.ytdlp_path:
            missing_executables.append("yt-dlp")
        if not self.ffmpeg_path:
            missing_executables.append("FFmpeg")
        
        # Always show path info in console for debugging
        print("\n" + "="*60)
        print("YSA EXECUTABLE STATUS")
        print("="*60)
        print(f"Script Directory: {SCRIPT_DIR}")
        print(f"yt-dlp Path: {self.ytdlp_path or 'NOT FOUND'}")
        print(f"FFmpeg Path: {self.ffmpeg_path or 'NOT FOUND'}")
        
        print("\nSEARCH LOCATIONS:")
        print("yt-dlp:")
        if getattr(sys, 'frozen', False):
            bundle_dir = getattr(sys, '_MEIPASS', os.path.dirname(sys.executable))
            bundled_ytdlp = os.path.join(bundle_dir, 'yt-dlp.exe')
        else:
            bundled_ytdlp = os.path.join(SCRIPT_DIR, 'yt-dlp.exe')
        
        env_ytdlp = r'C:\yt-dlp\yt-dlp.exe'
        print(f"  1. Bundled: {bundled_ytdlp} {'✓' if os.path.exists(bundled_ytdlp) else '✗'}")
        print(f"  2. Environment: {env_ytdlp} {'✓' if os.path.exists(env_ytdlp) else '✗'}")
        print(f"  3. System PATH: {'✓' if self.ytdlp_path in ['yt-dlp', 'yt-dlp.exe'] else '✗'}")
        
        print("FFmpeg:")
        if getattr(sys, 'frozen', False):
            bundle_dir = getattr(sys, '_MEIPASS', os.path.dirname(sys.executable))
            bundled_ffmpeg = os.path.join(bundle_dir, 'ffmpeg.exe')
        else:
            bundled_ffmpeg = os.path.join(SCRIPT_DIR, 'ffmpeg.exe')
        
        standard_ffmpeg = r'C:\ffmpeg\bin\ffmpeg.exe'
        print(f"  1. Bundled: {bundled_ffmpeg} {'✓' if os.path.exists(bundled_ffmpeg) else '✗'}")
        print(f"  2. Standard: {standard_ffmpeg} {'✓' if os.path.exists(standard_ffmpeg) else '✗'}")
        print(f"  3. System PATH: {'✓' if self.ffmpeg_path == 'ffmpeg' else '✗'}")
        print("="*60 + "\n")
        self.root.after(500, self._show_dns_status_in_terminal)
        # Check for tool updates in background after startup (2s delay)
        self.root.after(2000, lambda: threading.Thread(target=self._startup_update_check, daemon=True).start())
        
        # Only show dialog if executables are missing AND GUI is ready
        if missing_executables:
            # Add delay to ensure GUI is fully initialized
            self.root.after(3000, lambda: self.show_missing_executables_dialog(missing_executables))

    def show_missing_executables_dialog(self, missing_executables):
        """Show dialog for missing executables with error handling"""
        try:
            if not self.root.winfo_exists():
                return

            dialog = tk.Toplevel(self.root)
            dialog.title("Executable Status")
            dialog.geometry("700x500")
            dialog.transient(self.root)

            # Title
            title_text = f"Missing Executables: {', '.join(missing_executables)}"
            title_label = ttk.Label(dialog, text=title_text, font=('Arial', 12, 'bold'), foreground="orange")
            title_label.pack(pady=10)

            # Status text
            status_text = scrolledtext.ScrolledText(dialog, wrap=tk.WORD, font=('Consolas', 9), height=20)
            status_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

            # --- Prepare safe paths and checks ---
            # Use the module-level SCRIPT_DIR (already resolved correctly for
            # both frozen PyInstaller EXE and plain script) rather than __file__.

            yt_dlp_bundled = os.path.join(SCRIPT_DIR, 'yt-dlp.exe')
            yt_dlp_env = os.path.join('C:\\', 'yt-dlp', 'yt-dlp.exe')
            ffmpeg_bundled = os.path.join(SCRIPT_DIR, 'ffmpeg.exe')
            ffmpeg_standard = os.path.join('C:\\', 'ffmpeg', 'bin', 'ffmpeg.exe')

            yt_dlp_bundled_status = '✓' if os.path.exists(yt_dlp_bundled) else '✗'
            yt_dlp_env_status = '✓' if os.path.exists(yt_dlp_env) else '✗'
            yt_dlp_path_status = '✓' if self.ytdlp_path in ['yt-dlp', 'yt-dlp.exe'] else '✗'

            ffmpeg_bundled_status = '✓' if os.path.exists(ffmpeg_bundled) else '✗'
            ffmpeg_standard_status = '✓' if os.path.exists(ffmpeg_standard) else '✗'
            ffmpeg_path_status = '✓' if self.ffmpeg_path == 'ffmpeg' else '✗'

            # Status information
            status_info = f"""EXECUTABLE SEARCH RESULTS:

    Script Directory: {SCRIPT_DIR}

    yt-dlp Status: {'✅ FOUND' if self.ytdlp_path else '❌ NOT FOUND'}
    Current Path: {self.ytdlp_path or 'None'}

    Search Locations Checked:
    1. Bundled: {yt_dlp_bundled} {yt_dlp_bundled_status}
    2. Environment: {yt_dlp_env} {yt_dlp_env_status}
    3. System PATH: {yt_dlp_path_status}

    FFmpeg Status: {'✅ FOUND' if self.ffmpeg_path else '❌ NOT FOUND'}
    Current Path: {self.ffmpeg_path or 'None'}

    Search Locations Checked:
    1. Bundled: {ffmpeg_bundled} {ffmpeg_bundled_status}
    2. Standard: {ffmpeg_standard} {ffmpeg_standard_status}
    3. System PATH: {ffmpeg_path_status}

    FOR BUNDLING WITH PYINSTALLER:
    Place these files in your script directory:
    {yt_dlp_bundled}
    {ffmpeg_bundled}

    Then build with:
    pyinstaller --onefile --add-binary "yt-dlp.exe;." --add-binary "ffmpeg.exe;." --name "YSA" YSA.py

    DOWNLOAD LOCATIONS:
    yt-dlp: https://github.com/yt-dlp/yt-dlp/releases
    FFmpeg: https://github.com/GyanD/codexffmpeg/releases (Windows builds)

    {'⚠️ NOTE: Some features may not work without FFmpeg (video+audio merging)' if not self.ffmpeg_path else ''}
    """

            status_text.insert('1.0', status_info)
            status_text.config(state='normal')  # Keep editable for copying

            # Buttons
            btn_frame = ttk.Frame(dialog)
            btn_frame.pack(pady=10)

            def copy_status():
                self.root.clipboard_clear()
                self.root.clipboard_append(status_info)
                copy_btn.config(text="Copied!")
                self.root.after(2000, lambda: copy_btn.config(text="Copy Status"))

            def open_settings():
                dialog.destroy()
                self.show_settings()

            copy_btn = ttk.Button(btn_frame, text="Copy Status", command=copy_status)
            copy_btn.pack(side=tk.LEFT, padx=5)

            settings_btn = ttk.Button(btn_frame, text="Open Settings", command=open_settings)
            settings_btn.pack(side=tk.LEFT, padx=5)

            close_btn = ttk.Button(btn_frame, text="Continue Anyway", command=dialog.destroy)
            close_btn.pack(side=tk.LEFT, padx=5)

        except Exception as e:
            print(f"Could not show missing executables dialog: {e}")

    def setup_terminal_output(self, parent_frame):
        """Set up embedded terminal output widget.
        Creates _bottom_container (a 2-col frame at row 7): terminal on the left,
        queue panel on the right.  Queue panel is built separately by _setup_queue_panel."""

        # 2-column container: terminal (weight=3 left) + queue (fixed right)
        self._bottom_container = ttk.Frame(parent_frame)
        self._bottom_container.grid(row=9, column=0, columnspan=3,
                                    sticky=(tk.W, tk.E, tk.N, tk.S), pady=(5, 0))
        self._bottom_container.columnconfigure(0, weight=1)  # terminal stretches
        self._bottom_container.columnconfigure(1, weight=0)  # queue is fixed-width
        self._bottom_container.rowconfigure(0, weight=1)
        # Keep ref to parent so toggle_terminal can adjust row weights
        self._main_frame_ref = parent_frame

        # Terminal frame lives in left column of _bottom_container
        self.terminal_frame = ttk.LabelFrame(self._bottom_container, text="Download Progress", padding="5")
        self.terminal_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S), padx=(0, 4))
        self.terminal_frame.columnconfigure(0, weight=1)
        self.terminal_frame.rowconfigure(1, weight=1)
        
        # Terminal controls (Copy, Clear, Network Test, Debug, Auto-scroll)
        terminal_controls = ttk.Frame(self.terminal_frame)
        terminal_controls.grid(row=0, column=0, sticky=(tk.W, tk.E), pady=(0, 5))
        
        # Copy button
        self.copy_terminal_btn = ttk.Button(terminal_controls, text="Copy",
                                            command=self.copy_terminal)
        self.copy_terminal_btn.pack(side=tk.LEFT, padx=(0, 5))

        # Clear button
        self.clear_terminal_btn = ttk.Button(terminal_controls, text="Clear",
                                            command=self.clear_terminal)
        self.clear_terminal_btn.pack(side=tk.LEFT, padx=(5, 0))

        # Network Test button
        self.net_test_btn = ttk.Button(
            terminal_controls, text="Network Test",
            command=lambda: __import__("threading").Thread(
                target=self.test_network_connectivity, daemon=True).start())
        self.net_test_btn.pack(side=tk.LEFT, padx=(5, 0))

        # Debug Info button
        self.debug_btn = ttk.Button(terminal_controls, text="Debug Info",
                                    command=self.show_debug_info, state='disabled')
        self.debug_btn.pack(side=tk.LEFT, padx=(5, 0))

        # === BEGIN DEV TOOLS ===
        if DEV_MODE:
            try:
                ttk.Style().configure('Stub.TButton', foreground='#b03030')
            except Exception:
                pass
            self.stub_btn = ttk.Button(terminal_controls, text="\U0001f9ea Stub",
                                       command=self._show_stub_menu)
            self.stub_btn.pack(side=tk.LEFT, padx=(5, 0))
            # restore whatever was left enabled last session
            self.root.after(300, lambda: self._apply_stub_state(announce=True))
        # === END DEV TOOLS ===

        # Auto-scroll checkbox
        self.auto_scroll = tk.BooleanVar(value=True)
        auto_scroll_cb = ttk.Checkbutton(terminal_controls, text="Auto-scroll", 
                                        variable=self.auto_scroll)
        auto_scroll_cb.pack(side=tk.RIGHT)
        
        # Terminal output widget
        self.terminal_text = scrolledtext.ScrolledText(
            self.terminal_frame, 
            height=17, 
            font=('Consolas', 9),
            background='#1e1e1e',
            foreground='#d4d4d4',
            insertbackground='white',
            wrap=tk.WORD
        )
        self.terminal_text.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        # Configure text tags for different message types
        self.terminal_text.tag_configure('info', foreground='#74b8d4')
        self.terminal_text.tag_configure('success', foreground='#4caf50')
        self.terminal_text.tag_configure('warning', foreground='#ff9800')
        self.terminal_text.tag_configure('error', foreground='#f44336')
        self.terminal_text.tag_configure('progress', foreground='#00e676')
        self.terminal_text.tag_configure('cache', foreground='#ffeb3b')

    def _apply_terminal_collapsed(self):
        """Collapse terminal only on startup restore."""
        self._bottom_container.grid_remove()
        self._main_frame_ref.rowconfigure(6, weight=1)
        self._main_frame_ref.rowconfigure(8, weight=0)
        self._toggle_terminal_strip_btn.config(text="▼ Show Terminal")

    def toggle_terminal(self):
        """Toggle terminal visibility only. Button row always stays visible."""
        if self.terminal_expanded:
            # Collapse terminal - remove container and give its row no weight
            self._bottom_container.grid_remove()
            self._main_frame_ref.rowconfigure(6, weight=1)  # notebook expands
            self._main_frame_ref.rowconfigure(8, weight=0)  # terminal row shrinks away
            self._toggle_terminal_strip_btn.config(text="▼ Show Terminal")
            self.terminal_expanded = False
        else:
            # Expand terminal - restore container and share weight with notebook
            self._bottom_container.grid(row=9, column=0, columnspan=3,
                                        sticky=(tk.W, tk.E, tk.N, tk.S), pady=(5, 0))
            self._main_frame_ref.rowconfigure(6, weight=1)  # notebook
            self._main_frame_ref.rowconfigure(8, weight=1)  # terminal
            self._toggle_terminal_strip_btn.config(text="▲ Hide Terminal")
            self.terminal_expanded = True
        self._save_config()

    def copy_terminal(self):
        """Copy all terminal output to clipboard"""
        content = self.terminal_text.get('1.0', tk.END).strip()
        if content:
            self.root.clipboard_clear()
            self.root.clipboard_append(content)
            self.copy_terminal_btn.config(text="Copied!")
            self.root.after(2000, lambda: self.copy_terminal_btn.config(text="Copy"))
        else:
            self.copy_terminal_btn.config(text="Empty")
            self.root.after(2000, lambda: self.copy_terminal_btn.config(text="Copy"))

    def clear_terminal(self):
        """Clear terminal output"""
        self.terminal_text.delete('1.0', tk.END)
        self.append_terminal_output("Terminal cleared.\n", 'info')

    def _emit_dev_event(self, kind, **fields):
        """Emit a machine-readable event to output listeners only (DEV_MODE).

        yt-dlp's own guidance is that wrappers should never parse its
        human-readable stdout, and the same argument applies one level up:
        the dev test runner was detecting completion by string-matching
        terminal text, which is brittle and - because a concurrent queued or
        pre-cache download emits the identical strings - could mark the
        wrong scenario complete.

        This app is not observing yt-dlp from outside; it KNOWS when a
        download finished and exactly which file it produced. Emitting that
        ground truth as a JSON line, keyed by video id, removes the guessing
        entirely. Goes to listeners only, never to the visible terminal.
        """
        if not DEV_MODE:
            return
        try:
            payload = {'ev': kind}
            payload.update(fields)
            line = '@@YSAEV@@' + json.dumps(payload, default=str) + '\n'
        except Exception:
            return
        for _cb in list(getattr(self, '_output_listeners', ())):
            try:
                _cb(line, 'devevent')
            except Exception:
                pass

    def _notify(self, title, message, kind='info'):
        """Modal notice that closes on any click or key press, centred on the app.

        Replaces the OK-only messagebox dialogs, which open wherever the OS
        decides and force a trip to the OK button. Blocks exactly like the
        original (wait_window), so callers that assume the dialog is gone
        before the next statement keep working.

        Safety: never touches Tk off the main thread, and falls back to the
        original messagebox on ANY failure - a broken notice must never take
        down the operation that raised it.
        """
        _fb = {'info': messagebox.showinfo,
               'warning': messagebox.showwarning,
               'error': messagebox.showerror}.get(kind, messagebox.showinfo)
        try:
            if threading.current_thread() is not threading.main_thread():
                # Tk is main-thread only. Show it there and do NOT block the
                # worker, which is safer than the original behaviour.
                self.root.after(0, lambda: self._notify(title, message, kind))
                return 'ok'
            if not self.root.winfo_exists():
                return 'ok'
        except Exception:
            try:
                return _fb(title, message)
            except Exception:
                return 'ok'

        win = None
        try:
            win = tk.Toplevel(self.root)
            win.withdraw()                      # position it before it is seen
            win.title(str(title or ''))
            win.transient(self.root)
            win.resizable(False, False)

            _accent = {'info': '#2d7d46', 'warning': '#b8860b',
                       'error': '#b03030'}.get(kind, '#2d7d46')
            _sym = {'info': 'i', 'warning': '!', 'error': '!'}.get(kind, 'i')
            _frame = ttk.Frame(win, padding=(18, 14, 18, 12))
            _frame.pack(fill=tk.BOTH, expand=True)
            tk.Label(_frame, text=_sym, font=('Arial', 15, 'bold'),
                     fg=_accent).grid(row=0, column=0, sticky=tk.N, padx=(0, 12))
            tk.Label(_frame, text=str(message), justify=tk.LEFT,
                     wraplength=460).grid(row=0, column=1, sticky=tk.W)
            tk.Label(_frame, text='Click anywhere or press any key to close',
                     font=('Arial', 8), fg='gray').grid(
                row=1, column=0, columnspan=2, sticky=tk.W, pady=(12, 0))

            _done = {'v': False}

            def _close(_e=None):
                if _done['v']:
                    return
                _done['v'] = True
                try:
                    win.grab_release()
                except Exception:
                    pass
                try:
                    win.destroy()
                except Exception:
                    pass

            def _bind_dismiss(w):
                # bind on every descendant: a click on the label would not
                # reach a handler bound only to the Toplevel
                try:
                    w.bind('<Button-1>', _close)
                    w.bind('<Key>', _close)
                    for _c in w.winfo_children():
                        _bind_dismiss(_c)
                except Exception:
                    pass
            _bind_dismiss(win)
            win.protocol('WM_DELETE_WINDOW', _close)

            win.update_idletasks()
            _ww, _wh = win.winfo_reqwidth(), win.winfo_reqheight()
            try:
                _px, _py = self.root.winfo_rootx(), self.root.winfo_rooty()
                _pw, _ph = self.root.winfo_width(), self.root.winfo_height()
            except Exception:
                _px = _py = _pw = _ph = 0
            if _pw > 1 and _ph > 1:
                _x = _px + max(0, (_pw - _ww) // 2)
                _y = _py + max(0, (_ph - _wh) // 2)
            else:
                _x = max(0, (win.winfo_screenwidth() - _ww) // 2)
                _y = max(0, (win.winfo_screenheight() - _wh) // 2)
            win.geometry('+' + str(int(_x)) + '+' + str(int(_y)))
            win.deiconify()
            win.lift()
            try:
                win.focus_force()
                win.grab_set()
            except Exception:
                pass
            self.root.wait_window(win)
            return 'ok'
        except Exception:
            try:
                if win is not None:
                    win.destroy()
            except Exception:
                pass
            try:
                return _fb(title, message)
            except Exception:
                return 'ok'

    def _notify_info(self, title, message):
        return self._notify(title, message, 'info')

    def _notify_warning(self, title, message):
        return self._notify(title, message, 'warning')

    def _notify_error(self, title, message):
        return self._notify(title, message, 'error')

    def _mk_var_mirror(self, var, attr, cast=bool):
        """Mirror a Tk variable into a plain attribute via a write-trace (M3).

        Tkinter variables are not thread-safe, but download/batch workers
        need these toggle values. The trace fires on the main thread on
        every write, so the plain attribute is always fresh and safe to
        read from any thread."""
        def _sync(*_a):
            try:
                setattr(self, attr, cast(var.get()))
            except Exception:
                pass
        try:
            var.trace_add('write', _sync)
        except Exception:
            pass
        _sync()

    def _version_key(self, v):
        """Sortable key for dotted version strings ('2026.06.09', '8.1').

        Plain string >= comparison breaks as soon as widths differ
        ('2026.10.01' < '2026.6.9' as strings). Numeric tokens compare as
        ints; oddball tokens fall back to string compare, tagged so mixed
        tuples never raise."""
        parts = []
        for tok in str(v).strip().split('.'):
            tok = tok.strip()
            if tok.isdigit():
                parts.append((0, int(tok), ''))
            else:
                parts.append((1, 0, tok))
        return parts

    def _open_session_log(self):
        """Open a per-session log under <ysa_cache>/logs (terminal mirror).

        QoL: every line shown in the terminal is also written to disk, so
        reporting an issue becomes 'grab the newest file in ysa_cache/logs'
        instead of hand-copying terminal text. Keeps the 30 newest logs.
        Safe to call repeatedly (Clear Cache recreates the folder): any
        previous handle is closed first."""
        _old = getattr(self, '_session_log_fh', None)
        if _old is not None:
            try:
                _old.close()
            except Exception:
                pass
        self._session_log_fh = None
        try:
            base = getattr(self, 'ysa_logs_dir', None)
            if not base:
                return
            os.makedirs(base, exist_ok=True)
            self._session_log_path = os.path.join(
                base, 'YSA_' + time.strftime('%Y%m%d_%H%M%S') + '.log')
            self._session_log_fh = open(self._session_log_path, 'a',
                                        encoding='utf-8', errors='replace')
            # Clock for the per-line elapsed prefix written by
            # _write_session_log. Anchored at log open, so every log
            # file starts at 0.000 and is read without arithmetic.
            self._session_log_t0 = time.monotonic()
            self._log_at_line_start = True
            logs = sorted(f for f in os.listdir(base) if f.endswith('.log'))
            for _stale in logs[:-30]:
                try:
                    os.remove(os.path.join(base, _stale))
                except Exception:
                    pass
        except Exception:
            self._session_log_fh = None

    def _write_session_log(self, text):
        """Append one terminal chunk to the session log (best-effort).

        Each line is prefixed with seconds elapsed since the log was
        opened, so a log is self-profiling: the gap between the info
        fetch, the JS challenge, the transfer and the FFmpeg merge is
        readable directly instead of inferred from a total.

        Prefix goes on the LOG ONLY - the terminal widget and the
        _output_listeners fan-out both receive the unmodified text.

        Chunks are not guaranteed to be whole lines, so a line-start
        flag carries across calls; a chunk arriving mid-line is not
        prefixed. Blank lines stay blank. Single-threaded: the only
        caller is append_terminal_output, past its main-thread guard.
        """
        fh = getattr(self, '_session_log_fh', None)
        if fh is None:
            return
        try:
            t0 = getattr(self, '_session_log_t0', None)
            if t0 is None:
                t0 = time.monotonic()
                self._session_log_t0 = t0
            prefix = '[' + ('%9.3f' % (time.monotonic() - t0)) + '] '

            at_start = getattr(self, '_log_at_line_start', True)
            parts = text.split('\n')
            last = len(parts) - 1
            buf = []
            for i, part in enumerate(parts):
                if part:
                    if at_start:
                        buf.append(prefix)
                        at_start = False
                    buf.append(part)
                if i != last:
                    buf.append('\n')
                    at_start = True
            self._log_at_line_start = at_start

            fh.write(''.join(buf))
            fh.flush()
        except Exception:
            # Disk full / folder removed mid-session: disable quietly.
            self._session_log_fh = None

    def _close_session_log(self):
        fh = getattr(self, '_session_log_fh', None)
        self._session_log_fh = None
        if fh is not None:
            try:
                fh.close()
            except Exception:
                pass

    def append_terminal_output(self, text, tag='info'):
        """Append text to terminal output with color coding"""
        try:
            if threading.current_thread() != threading.main_thread():
                self.root.after(0, lambda: self.append_terminal_output(text, tag))
                return

            self.terminal_text.insert(tk.END, text, tag)

            # Mirror every terminal line to the on-disk session log (QoL:
            # issue reports = attach the newest file in ysa_cache/logs).
            self._write_session_log(text)

            # Fan out to any registered listeners (the dev test runner taps
            # this to follow progress and detect completion). Never let a
            # listener break the UI.
            for _cb in list(getattr(self, '_output_listeners', ())):
                try:
                    _cb(text, tag)
                except Exception:
                    pass

            # Count newlines added and maintain a running total
            added = text.count('\n')
            self._terminal_line_count += added

            # Trim oldest 4000 lines once buffer exceeds 5000 lines.
            # Trimming in larger chunks reduces how often the expensive
            # Text.delete operation runs.
            if self._terminal_line_count > 5000:
                self.terminal_text.delete('1.0', '4001.0')
                # Re-sync from the widget rather than assuming exactly -200,
                # because partial lines without a trailing newline cause drift.
                actual = int(self.terminal_text.index(tk.END).split('.')[0]) - 1
                self._terminal_line_count = max(0, actual)
                # Progress line index is now invalid - clear it so next progress
                # update appends a fresh line rather than editing a wrong position
                self._progress_line_index = None

            if self.auto_scroll.get():
                self.terminal_text.see(tk.END)

        except Exception as e:
            print("Error appending terminal output: " + str(e))

    def run_ytdlp_command_with_terminal(self, args, capture_output=False, timeout=30):
        """Run yt-dlp command with terminal output"""
        cmd = self._ytdlp_head() + args

        try:
            if capture_output:
                result = subprocess.run(cmd, capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=timeout,
                                      creationflags=CREATE_NO_WINDOW)
                return result
            else:
                self.append_terminal_output("Running: " + " ".join(cmd[:3]) + "...\n", 'info')
                # The visible line is truncated to three tokens; the dev
                # runner needs the whole vector to reproduce a failure.
                self._emit_dev_event('spawn', argv=list(cmd))

                process = subprocess.Popen(
                    cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True, encoding='utf-8', errors='replace',
                    bufsize=65536,
                    universal_newlines=True,
                    creationflags=CREATE_NO_WINDOW,
                )

                # Store process reference so pause/stop buttons can reach it
                self._download_process = process
                self._download_stopped = False

                # Enable pause and stop buttons
                self.root.after(0, lambda: self.pause_btn.config(state='normal', text='Pause'))
                self.root.after(0, lambda: self.stop_btn.config(state='normal'))

                # Read output line by line, checking for user interruption on every line
                last_error_lines = []
                for line in iter(process.stdout.readline, ''):
                    # Check BEFORE processing the line so we exit as soon as possible
                    if self._download_stopped or self._download_paused:
                        # Close stdout immediately to unblock any pending reads
                        try:
                            process.stdout.close()
                        except Exception:
                            pass
                        break
                    if line.strip():
                        self.process_ytdlp_output(line)
                        if line.strip().startswith('ERROR:'):
                            last_error_lines.append(line.strip())

                # Wait for the process to fully exit (it was already killed by _kill_process)
                try:
                    process.wait(timeout=5)
                except Exception:
                    pass

                self._download_process = None

                # If user stopped or paused, raise a distinct exception so workers
                # do NOT retry - they just exit cleanly
                if self._download_stopped:
                    raise _DownloadStoppedError("stopped")
                if self._download_paused:
                    raise _DownloadPausedError("paused")

                if process.returncode not in (0, None):
                    base_msg = "yt-dlp failed with return code " + str(process.returncode)
                    error_detail = ' | '.join(last_error_lines) if last_error_lines else ''
                    raise Exception(base_msg + (': ' + error_detail if error_detail else ''))

                return process

        except (_DownloadStoppedError, _DownloadPausedError):
            # Re-raise as-is so workers can detect and exit without retrying
            raise
        except subprocess.TimeoutExpired:
            self.append_terminal_output("Command timed out after " + str(timeout) + " seconds\n", 'error')
            raise Exception("yt-dlp command timed out after " + str(timeout) + " seconds")
        except Exception as e:
            raise Exception("Failed to run yt-dlp: " + str(e))
        finally:
            # cookie copies are reclaimed only by the process-guarded reap
            pass
            self._download_process = None
            self.root.after(0, self._reset_download_buttons)

    def _update_subtitle_combo_states(self):
        """Grey out subtitle combos visually when the subtitle toggle is off,
        when download is active (settings locked), or when subtitle source is
        External (mode irrelevant).  Uses a SubtitleDisabled style with explicit
        grey fieldbackground so the effect is visible in both light and dark
        themes regardless of the OS disabled-state rendering."""
        if not hasattr(self, '_sq_src_combo'):
            return
        # If the master toggle is off, disable all three combos
        toggle_off = not getattr(self, '_subtitle_enabled_var', tk.BooleanVar(value=True)).get()
        if toggle_off:
            _dis = 'SubtitleDisabled.TCombobox'
            self._sq_src_combo.config(style=_dis, state='disabled')
            self._sq_mode_combo.config(style=_dis, state='disabled')
            self._sq_lang_combo.config(style=_dis, state='disabled')
            return
        src_external = (self._sq_src_var.get() == 'External')
        # Mode (S/SD/HS) is only relevant when subtitles are embedded.
        # Disable it when External is selected.
        mode_disabled = src_external
        dep_style  = 'SubtitleDisabled.TCombobox' if mode_disabled else 'SubtitleActive.TCombobox'
        dep_state  = 'disabled' if mode_disabled else 'readonly'
        self._sq_src_combo.config(style='SubtitleActive.TCombobox', state='readonly')
        self._sq_mode_combo.config(style=dep_style, state=dep_state)
        self._sq_lang_combo.config(style='SubtitleActive.TCombobox', state='readonly')

    def _on_subtitle_toggle_changed(self, src_opts, src_values, disp_to_code, mode_opts):
        """Handle the subtitle on/off toggle checkbutton."""
        enabled = self._subtitle_enabled_var.get()
        if enabled:
            # Restore subtitle_source from the combo value
            src_disp = self._sq_src_var.get()
            if src_disp in src_opts:
                self.subtitle_source = src_values[src_opts.index(src_disp)]
            else:
                self.subtitle_source = self.subtitle_last_source or 'manual'
        else:
            # Save current combo selection before setting source to 'off'
            src_disp = self._sq_src_var.get()
            if src_disp in src_opts:
                self.subtitle_last_source = src_values[src_opts.index(src_disp)]
            self.subtitle_source = 'off'
        self._update_subtitle_combo_states()
        self._save_config()

    # === BEGIN DEV TOOLS ===
    def _setup_diagnostics_panel(self, outer):
        """Scenario runner UI. Lives on the main window so a run survives
        tab switching and does not depend on a dialog staying open.

        The content sits in a scrollable canvas: shrinking the window
        vertically used to clip the panel with no way to reach the rest."""
        outer.columnconfigure(0, weight=1)
        outer.rowconfigure(0, weight=1)
        _canvas = tk.Canvas(outer, highlightthickness=0, height=300)
        _canvas.grid(row=0, column=0, sticky=(tk.N, tk.S, tk.W, tk.E))
        _vsb = ttk.Scrollbar(outer, orient=tk.VERTICAL, command=_canvas.yview)
        _vsb.grid(row=0, column=1, sticky=(tk.N, tk.S))
        _canvas.configure(yscrollcommand=_vsb.set)
        parent = ttk.Frame(_canvas)
        _win = _canvas.create_window((0, 0), window=parent, anchor='nw')

        def _on_frame(_e=None):
            _canvas.configure(scrollregion=_canvas.bbox('all'))

        def _on_canvas(e):
            _canvas.itemconfigure(_win, width=e.width)
        parent.bind('<Configure>', _on_frame)
        _canvas.bind('<Configure>', _on_canvas)

        def _wheel(e):
            try:
                _canvas.yview_scroll(int(-1 * (e.delta / 120)), 'units')
            except Exception:
                pass
        _canvas.bind('<Enter>', lambda _e: _canvas.bind_all('<MouseWheel>', _wheel))
        _canvas.bind('<Leave>', lambda _e: _canvas.unbind_all('<MouseWheel>'))

        parent.columnconfigure(1, weight=1)

        ttk.Label(parent, text="Scenario file:").grid(
            row=0, column=0, sticky=tk.W, padx=10, pady=(12, 2))
        self._diag_file_lbl = ttk.Label(
            parent,
            text=(getattr(self, 'devtest_scenario_file', '') or "(none selected)"),
            foreground='gray')
        self._diag_file_lbl.grid(row=0, column=1, sticky=tk.W, padx=10, pady=(12, 2))

        def _pick():
            _f = filedialog.askopenfilename(
                title="Choose scenario file",
                filetypes=[("Scenario JSON", "*.json"), ("All files", "*.*")])
            if _f:
                self.devtest_scenario_file = _f
                self._diag_file_lbl.config(text=_f)
                self.devtest_selected = []          # new file - select all
                self._diag_rebuild_list()
                self._save_devtest_state()

        _btns = ttk.Frame(parent)
        _btns.grid(row=1, column=0, columnspan=3, sticky=tk.W, padx=10, pady=(2, 0))
        ttk.Button(_btns, text="Browse...", command=_pick).pack(side=tk.LEFT)
        self._diag_run_btn = ttk.Button(_btns, text="Run scenarios",
                                        command=self._diag_run)
        self._diag_run_btn.pack(side=tk.LEFT, padx=(8, 0))
        self._diag_stop_btn = ttk.Button(_btns, text="Stop",
                                         command=self._diag_stop, state='disabled')
        self._diag_stop_btn.pack(side=tk.LEFT, padx=(8, 0))

        # ── scenario picker ──────────────────────────────────────────────
        # Running all 19 to check one thing wastes time and requests, so the
        # set is selectable and remembered between sessions.
        _pick = ttk.LabelFrame(parent, text="Scenarios to run")
        _pick.grid(row=2, column=0, columnspan=3, sticky=(tk.W, tk.E),
                   padx=10, pady=(10, 2))
        _pick.columnconfigure(0, weight=1)
        self._diag_list = ttk.Frame(_pick)
        self._diag_list.grid(row=0, column=0, sticky=(tk.W, tk.E), padx=6, pady=4)
        _selbtns = ttk.Frame(_pick)
        _selbtns.grid(row=1, column=0, sticky=tk.W, padx=6, pady=(0, 4))
        ttk.Button(_selbtns, text="All",
                   command=lambda: self._diag_select('all')).pack(side=tk.LEFT)
        ttk.Button(_selbtns, text="None",
                   command=lambda: self._diag_select('none')).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(_selbtns, text="Quick only",
                   command=lambda: self._diag_select('quick')).pack(side=tk.LEFT, padx=(6, 0))
        ttk.Button(_selbtns, text="Invert",
                   command=lambda: self._diag_select('invert')).pack(side=tk.LEFT, padx=(6, 0))
        self._diag_estimate = ttk.Label(_selbtns, text="", font=('Arial', 8),
                                        foreground='gray')
        self._diag_estimate.pack(side=tk.LEFT, padx=(12, 0))
        self._diag_sel_vars = {}
        self._load_devtest_state()
        try:
            self._diag_file_lbl.config(
                text=(getattr(self, 'devtest_scenario_file', '') or "(none selected)"))
        except Exception:
            pass
        self._diag_rebuild_list()

        self._diag_status = ttk.Label(parent, text="Idle", font=('Arial', 9))
        self._diag_status.grid(row=3, column=0, columnspan=3, sticky=tk.W,
                               padx=10, pady=(12, 2))
        self._diag_bar = ttk.Progressbar(parent, mode='determinate', maximum=100)
        self._diag_bar.grid(row=4, column=0, columnspan=3, sticky=(tk.W, tk.E),
                            padx=10, pady=(0, 6))

        ttk.Label(parent, text="Progress log", font=('Arial', 9, 'bold')).grid(
            row=5, column=0, sticky=tk.W, padx=10, pady=(6, 0))
        _wrap = ttk.Frame(parent)
        _wrap.grid(row=7, column=0, columnspan=3, sticky=(tk.N, tk.S, tk.W, tk.E),
                   padx=10, pady=(2, 10))
        _wrap.columnconfigure(0, weight=1)
        _wrap.rowconfigure(0, weight=1)
        # height=6, not 14: a Notebook sizes itself to its TALLEST tab, so a
        # deep Text here raised the notebook's minimum and squeezed the
        # terminal below it. The log scrolls, so visible lines cost nothing.
        self._diag_text = tk.Text(_wrap, height=6, wrap=tk.WORD,
                                  font=('Consolas', 9))
        self._diag_text.grid(row=0, column=0, sticky=(tk.N, tk.S, tk.W, tk.E))
        _sb = ttk.Scrollbar(_wrap, orient=tk.VERTICAL,
                            command=self._diag_text.yview)
        _sb.grid(row=0, column=1, sticky=(tk.N, tk.S))
        self._diag_text.config(yscrollcommand=_sb.set, state='disabled')

        ttk.Label(
            parent,
            text="Sandboxed run (ysa_dev_config.json + ysa_cache_dev); your real"
                 " settings and cache are never written to. Keeps running while"
                 " you use other tabs.",
            font=('Arial', 8), foreground='gray', justify=tk.LEFT,
            wraplength=700).grid(row=6, column=0, columnspan=3, sticky=tk.W,
                                 padx=12, pady=(0, 4))

    def _devtest_state_path(self):
        return os.path.join(SCRIPT_DIR, 'ysa_devtest_state.json')

    def _load_devtest_state(self):
        """Diagnostics settings live in their own file.

        They are developer state, not app configuration - keeping them out of
        ysa_config.json means a non-developer build never carries them and the
        dev tools can be deleted without leaving orphan keys behind.
        """
        try:
            _p = self._devtest_state_path()
            if not os.path.isfile(_p):
                return
            _st = json.load(open(_p, encoding='utf-8'))
            self.devtest_scenario_file = str(_st.get('scenario_file', '') or '')
            _sel = _st.get('selected', [])
            self.devtest_selected = list(_sel) if isinstance(_sel, list) else []
            self.stub_enabled = bool(_st.get('stub_enabled', False))
            self.stub_mode = str(_st.get('stub_mode', 'ok') or 'ok')
            try:
                self.stub_fail_times = int(_st.get('stub_fail_times', 0) or 0)
            except Exception:
                self.stub_fail_times = 0
            # The state file existing means the user HAS made a choice, so an
            # empty list means "none selected" - not "never chosen". Without
            # this flag, unticking everything read as untouched and every box
            # came back ticked on the next launch.
            self._devtest_state_loaded = True
        except Exception as e:
            print('Could not read dev test state: ' + str(e))

    def _save_devtest_state(self):
        self._devtest_state_loaded = True
        try:
            json.dump({'scenario_file': getattr(self, 'devtest_scenario_file', ''),
                       'selected': list(getattr(self, 'devtest_selected', []) or []),
                       'stub_enabled': bool(getattr(self, 'stub_enabled', False)),
                       'stub_mode': str(getattr(self, 'stub_mode', 'ok')),
                       'stub_fail_times': int(getattr(self, 'stub_fail_times', 0) or 0)},
                      open(self._devtest_state_path(), 'w', encoding='utf-8'),
                      indent=2)
        except Exception as e:
            print('Could not save dev test state: ' + str(e))

    def _diag_rebuild_list(self):
        """(Re)build the scenario checklist from the chosen file."""
        try:
            for w in self._diag_list.winfo_children():
                w.destroy()
        except Exception:
            return
        self._diag_sel_vars = {}
        self._diag_scenarios = []
        _f = getattr(self, 'devtest_scenario_file', '')
        if not _f or not os.path.isfile(_f):
            # Default to the one shipped next to the app - SCRIPT_DIR resolves
            # to the folder holding the .py or the .exe, so this works either
            # way and saves browsing for it on a fresh install.
            _default = os.path.join(SCRIPT_DIR, 'ysa_scenarios.json')
            if os.path.isfile(_default):
                _f = _default
                self.devtest_scenario_file = _f
                try:
                    self._diag_file_lbl.config(text=_f)
                except Exception:
                    pass
        if not _f or not os.path.isfile(_f):
            ttk.Label(self._diag_list,
                      text="(no ysa_scenarios.json beside the app - choose one)",
                      foreground='gray').grid(row=0, column=0, sticky=tk.W)
            self._diag_update_estimate()
            return
        try:
            _spec = json.load(open(_f, encoding='utf-8'))
            _scn = _spec.get('scenarios', []) or []
            _ph = _spec.get('placeholders', {}) or {}
        except Exception as e:
            ttk.Label(self._diag_list, text="Unreadable: " + str(e)[:60],
                      foreground='red').grid(row=0, column=0, sticky=tk.W)
            self._diag_update_estimate()
            return
        _saved = set(getattr(self, 'devtest_selected', []) or [])
        # Two columns, filled downward, height driven by the count. A fixed
        # 10 per column meant 31 scenarios needed four columns, and columns
        # three and four ran off the right edge with no horizontal scrollbar -
        # so only the first 20 were reachable. Vertical overflow scrolls.
        _per_col = max(1, (len(_scn) + 1) // 2)
        for i, sc in enumerate(_scn):
            _name = sc.get('name', 'scenario ' + str(i + 1))
            _url = sc.get('url', '')
            _unset = (_url.startswith('@')
                      and str(_ph.get(_url[1:], '@')).startswith('@'))
            _est = int(sc.get('est_sec', 0) or 0)
            _label = str(i + 1) + '. ' + _name[:40]
            if _est:
                _label += '  (~' + (str(_est) + 's' if _est < 90
                                    else str(round(_est / 60.0, 1)) + 'm') + ')'
            if _unset:
                _label += '  [no URL]'
            # default: everything selected the first time
            _chosen = getattr(self, '_devtest_state_loaded', False)
            _var = tk.BooleanVar(value=(_name in _saved) if _chosen else True)
            self._diag_sel_vars[_name] = _var
            self._diag_scenarios.append((_name, _est, _unset))
            _cb = ttk.Checkbutton(self._diag_list, text=_label, variable=_var,
                                  command=self._diag_selection_changed)
            _cb.grid(row=i % _per_col, column=i // _per_col,
                     sticky=tk.W, padx=(0, 14))
            if _unset:
                _var.set(False)
        self._diag_update_estimate()

    def _diag_select(self, mode):
        for _name, _est, _unset in getattr(self, '_diag_scenarios', []):
            _v = self._diag_sel_vars.get(_name)
            if _v is None:
                continue
            if mode == 'all':
                _v.set(not _unset)
            elif mode == 'none':
                _v.set(False)
            elif mode == 'invert':
                _v.set(bool(not _v.get()) and not _unset)
            elif mode == 'quick':
                # anything under a minute; the long ones are the 20-hour
                # source, the playlist and the stress run
                _v.set((0 < _est <= 60) and not _unset)
        self._diag_selection_changed()

    def _diag_selection_changed(self):
        self.devtest_selected = [n for n, v in self._diag_sel_vars.items() if v.get()]
        self._diag_update_estimate()
        self._save_devtest_state()

    def _diag_update_estimate(self):
        try:
            _sel = [(n, e) for n, e, _u in getattr(self, '_diag_scenarios', [])
                    if self._diag_sel_vars.get(n) is not None
                    and self._diag_sel_vars[n].get()]
            _tot = sum(e for _n, e in _sel)
            _txt = str(len(_sel)) + ' selected'
            if _tot:
                _txt += '  -  roughly ' + (str(_tot) + 's' if _tot < 90
                                           else str(round(_tot / 60.0)) + ' min')
            self._diag_estimate.config(text=_txt)
        except Exception:
            pass

    def _diag_progress(self, msg):
        """Progress sink for the scenario runner (called from its thread).

        Guarded against the widgets being gone: the panel is a main-window
        tab now, but the app can still be closing mid-run.
        """
        def _apply():
            try:
                if not self._diag_status.winfo_exists():
                    return
                self._diag_status.config(text=msg)
                self._diag_text.config(state='normal')
                self._diag_text.insert(tk.END, time.strftime('%H:%M:%S ') + msg + '\n')
                self._diag_text.see(tk.END)
                self._diag_text.config(state='disabled')
                _m = re.match(r'^\[(\d+)/(\d+)\]', msg)
                if _m:
                    self._diag_bar['value'] = (int(_m.group(1)) - 1) * 100.0 / max(1, int(_m.group(2)))
                elif msg.startswith('Done:'):
                    self._diag_bar['value'] = 100
                    self._diag_run_btn.config(state='normal')
                    self._diag_stop_btn.config(state='disabled')
            except Exception:
                pass
        try:
            self.root.after(0, _apply)
        except Exception:
            pass

    def _diag_run(self):
        _f = getattr(self, 'devtest_scenario_file', '')
        if not _f or not os.path.isfile(_f):
            self._notify_warning("Diagnostics", "Choose a scenario file first.")
            return
        try:
            import ysa_devtest
        except Exception as _e:
            self._notify_error("Diagnostics",
                                 "ysa_devtest.py could not be imported:\n" + str(_e))
            return
        _r = getattr(self, '_devtest_runner', None)
        if _r is not None and _r.is_running():
            self._notify_info("Diagnostics", "A run is already in progress.")
            return
        try:
            self._diag_text.config(state='normal')
            self._diag_text.delete('1.0', tk.END)
            self._diag_text.config(state='disabled')
            self._diag_bar['value'] = 0
            self._diag_run_btn.config(state='disabled')
            self._diag_stop_btn.config(state='normal')
        except Exception:
            pass
        _only = [n for n, v in getattr(self, '_diag_sel_vars', {}).items() if v.get()]
        if not _only:
            self._notify_warning("Diagnostics", "No scenarios are selected.")
            try:
                self._diag_run_btn.config(state='normal')
                self._diag_stop_btn.config(state='disabled')
            except Exception:
                pass
            return
        self._devtest_runner = ysa_devtest.DevTestRunner(
            self, _f, progress=self._diag_progress, only=_only)
        self._devtest_runner.start()

    def _diag_stop(self):
        _r = getattr(self, '_devtest_runner', None)
        if _r is not None:
            _r.stop()
            self._diag_progress("Stop requested - finishing current scenario...")
    # === END DEV TOOLS ===

    # ── Download history panel ─────────────────────────────────────────────

    def _setup_history_panel(self, parent):
        """Build the download history tab with search, treeview, and controls."""
        top_bar = ttk.Frame(parent)
        top_bar.pack(fill=tk.X, padx=4, pady=(4, 2))

        ttk.Label(top_bar, text='Search:').pack(side=tk.LEFT, padx=(0, 4))
        self._history_search_var = tk.StringVar()
        search_entry = ttk.Entry(top_bar, textvariable=self._history_search_var, width=30)
        search_entry.pack(side=tk.LEFT, padx=(0, 4))
        self._history_search_var.trace_add('write', lambda *_: self._refresh_history_panel())

        ttk.Label(top_bar, text='Filter:').pack(side=tk.LEFT, padx=(8, 4))
        self._history_filter_var = tk.StringVar(value='All')
        filter_combo = ttk.Combobox(top_bar, textvariable=self._history_filter_var,
                                    values=['All', 'Failed only', 'By Channel',
                                            'By URL', 'By Title'],
                                    # 'Failed only' needs no search text - it
                                    # filters on status, not on the query box.
                                    state='readonly', width=12)
        filter_combo.pack(side=tk.LEFT, padx=(0, 4))
        self._history_filter_var.trace_add('write', lambda *_: self._refresh_history_panel())

        # Recording toggle: OFF stops new entries being recorded; existing
        # history is kept and stays searchable (use Clear History to remove).
        self._history_enabled_var = tk.BooleanVar(
            value=bool(getattr(self, 'history_enabled', True)))

        def _on_history_toggle():
            self.history_enabled = bool(self._history_enabled_var.get())
            self._save_config_now()
            self.append_terminal_output(
                'History recording ' + ('enabled' if self.history_enabled
                                        else 'disabled') + '.\n', 'info')
        ttk.Checkbutton(top_bar, text='Record history',
                        variable=self._history_enabled_var,
                        command=_on_history_toggle).pack(side=tk.LEFT, padx=(12, 4))

        ttk.Button(top_bar, text='Clear History',
                   command=self._clear_download_history).pack(side=tk.RIGHT, padx=(4, 0))
        ttk.Button(top_bar, text='Open URL',
                   command=self._open_history_url_in_browser).pack(side=tk.RIGHT, padx=(4, 0))
        ttk.Button(top_bar, text='Copy URL',
                   command=self._copy_history_url).pack(side=tk.RIGHT, padx=(4, 0))

        cols = ('timestamp', 'upload_date', 'channel', 'title', 'url')
        self._history_tree = ttk.Treeview(parent, columns=cols, show='headings', height=12)

        # Column display names and data keys for sorting
        _col_config = {
            'timestamp':   ('Downloaded', 130),
            'upload_date': ('Uploaded',    90),
            'channel':     ('Channel',    140),
            'title':       ('Video Title', 280),
            'url':         ('URL',        200),
        }
        for col_id, (label, width) in _col_config.items():
            self._history_tree.heading(
                col_id, text=label + ' \u25BC',  # default indicator on all
                command=lambda c=col_id: self._sort_history_by(c))
            self._history_tree.column(col_id, width=width, minwidth=70)

        # Sort state: column key and direction (True = descending)
        self._history_sort_col = 'timestamp'
        self._history_sort_desc = True

        hsb = ttk.Scrollbar(parent, orient=tk.VERTICAL, command=self._history_tree.yview)
        self._history_tree.configure(yscrollcommand=hsb.set)
        self._history_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(4, 0), pady=(0, 4))
        hsb.pack(side=tk.RIGHT, fill=tk.Y, pady=(0, 4), padx=(0, 4))

        # Double-click sends URL to be analyzed
        self._history_tree.bind('<Double-1>', lambda e: self._analyze_history_url())
        self._refresh_history_panel()

    def _sort_history_by(self, col):
        """Toggle sort direction for a history column, then refresh."""
        if self._history_sort_col == col:
            self._history_sort_desc = not self._history_sort_desc
        else:
            self._history_sort_col = col
            # Default direction: descending for dates, ascending for text
            self._history_sort_desc = col in ('timestamp', 'upload_date')
        self._refresh_history_panel()

    def _refresh_history_panel(self):
        """Repopulate the history treeview with optional search/filter and sorting."""
        tree = getattr(self, '_history_tree', None)
        if tree is None:
            return
        tree.delete(*tree.get_children())
        # With nothing downloading, a still-'pending' entry is one that never
        # finished - promote it to failed here so failures surface without
        # waiting for a restart. Guarded on _download_active so a running
        # download is never mislabelled mid-flight.
        if not getattr(self, '_download_active', False):
            self._sweep_pending_attempts('did not finish')
        query = self._history_search_var.get().strip().lower()
        filt = self._history_filter_var.get()

        # Filter entries
        filtered = []
        for entry in self.download_history:
            ts = entry.get('timestamp', '')
            ud = entry.get('upload_date', '')
            ch = entry.get('channel', '')
            ti = entry.get('title', '')
            ur = entry.get('url', '')
            # Entries written before this feature have no status; they are
            # completed downloads, so they read as ok.
            _st = entry.get('status') or 'ok'
            if filt == 'Failed only' and _st != 'failed':
                continue
            if query:
                if filt == 'By Channel':
                    if query not in ch.lower():
                        continue
                elif filt == 'By URL':
                    if query not in ur.lower():
                        continue
                elif filt == 'By Title':
                    if query not in ti.lower():
                        continue
                else:
                    combined = (ch + ' ' + ti + ' ' + ur).lower()
                    if query not in combined:
                        continue
            filtered.append((ts, ud, ch, ti, ur, _st))

        # Sort
        _col_idx = {'timestamp': 0, 'upload_date': 1, 'channel': 2, 'title': 3, 'url': 4}
        _idx = _col_idx.get(self._history_sort_col, 0)
        filtered.sort(key=lambda row: row[_idx].lower() if row[_idx] else '',
                      reverse=self._history_sort_desc)

        # Row 5 is the status; it is not a column, only a tag source.
        tree.tag_configure('failed', foreground='#B3261E')
        for row in filtered:
            tree.insert('', tk.END, values=row[:5],
                        tags=('failed',) if row[5] == 'failed' else ())

        # Update heading arrows to show current sort
        _labels = {'timestamp': 'Downloaded', 'upload_date': 'Uploaded',
                   'channel': 'Channel', 'title': 'Video Title', 'url': 'URL'}
        for col_id, label in _labels.items():
            if col_id == self._history_sort_col:
                arrow = ' \u25BC' if self._history_sort_desc else ' \u25B2'
                tree.heading(col_id, text=label + arrow)
            else:
                tree.heading(col_id, text=label)

    def _copy_history_url(self):
        """Copy the URL of the selected history entry to clipboard."""
        tree = getattr(self, '_history_tree', None)
        if not tree:
            return
        sel = tree.selection()
        if not sel:
            return
        values = tree.item(sel[0], 'values')
        if values and len(values) >= 5:
            self.root.clipboard_clear()
            self.root.clipboard_append(values[4])

    def _analyze_history_url(self):
        """Send the selected history entry's URL to the analyzer."""
        tree = getattr(self, '_history_tree', None)
        if not tree:
            return
        sel = tree.selection()
        if not sel:
            return
        values = tree.item(sel[0], 'values')
        if values and len(values) >= 5:
            url = values[4]
            if url:
                self.url_var.set(url)
                self._enqueue_url_for_analysis(url)

    def _open_history_url_in_browser(self):
        """Open the selected history entry's URL in the default browser."""
        tree = getattr(self, '_history_tree', None)
        if not tree:
            return
        sel = tree.selection()
        if not sel:
            return
        values = tree.item(sel[0], 'values')
        if values and len(values) >= 5:
            url = values[4]
            if url:
                webbrowser.open(url)

    def _clear_download_history(self):
        """Clear all download history after confirmation."""
        if not self.download_history:
            return
        if messagebox.askyesno('Clear History',
                               'Delete all download history (' +
                               str(len(self.download_history)) + ' entries)?'):
            self.download_history.clear()
            self._save_download_history()
            self._refresh_history_panel()

    def _reset_download_buttons(self):
        """Reset pause/stop buttons after a download finishes or is interrupted.
        If the download was paused, leave the Pause button showing Resume."""
        if self._download_paused:
            # Keep Resume button visible and enabled so user can click it
            self.pause_btn.config(state='normal', text='Resume', command=self.resume_download)
            self.stop_btn.config(state='normal')
        else:
            # Idle - disable pause/stop.  Do NOT touch _download_active here;
            # _download_complete and _download_error are the sole owners of that flag.
            # Clearing it here fires between every yt-dlp subprocess call inside a
            # multi-step worker (video stream → audio stream) and causes a false
            # "idle" window that lets the queue start a second concurrent download.
            self.pause_btn.config(state='disabled', text='Pause', command=self.pause_download)
            self.stop_btn.config(state='disabled')
        self._update_subtitle_combo_states()

    def _kill_process(self, process):
        """Kill a subprocess and its entire process tree, then close its stdout
        pipe so any blocked readline() call in the worker thread returns immediately."""
        if process is None:
            return
        # Close stdout first - this unblocks readline() in the worker thread instantly
        try:
            process.stdout.close()
        except Exception:
            pass
        # Now kill the actual OS process tree
        try:
            pid = process.pid
            if sys.platform == 'win32':
                # taskkill /F /T kills the process AND all child processes (including yt-dlp)
                subprocess.run(
                    ['taskkill', '/F', '/T', '/PID', str(pid)],
                    capture_output=True,
                    creationflags=CREATE_NO_WINDOW
                )
            else:
                import signal
                import os as _os
                try:
                    _os.killpg(_os.getpgid(pid), signal.SIGTERM)
                except Exception:
                    process.terminate()
        except Exception:
            try:
                process.kill()
            except Exception:
                pass

    def _kill_all_ffmpeg(self):
        """Kill every ffmpeg.exe process on the system so Windows releases any file
        handles it holds on cached stream files.  Called before clearing the cache.
        Safe for personal-use / single-user machines - no other application should
        be running FFmpeg at the same time as YSA.
        Returns True if the taskkill command ran without error (even if no processes
        were found - exit code 128 means 'no matching processes', which is fine)."""
        if sys.platform != 'win32':
            return False
        try:
            result = subprocess.run(
                ['taskkill', '/F', '/IM', 'ffmpeg.exe'],
                capture_output=True,
                creationflags=CREATE_NO_WINDOW,
            )
            # Exit code 0 = processes killed, 128 = no matching processes found.
            # Both are acceptable - anything else is a genuine error.
            return result.returncode in (0, 128)
        except Exception:
            return False

    def pause_download(self):
        """Pause the current download. Kills the process tree so yt-dlp actually stops.
        The partial file is kept on disk so -c (continue) can resume it."""
        if self._download_paused:
            self.resume_download()
            return
        if self._download_process and self._download_process.poll() is None:
            self._download_paused = True
            self._download_stopped = False
            self._kill_process(self._download_process)
            # C2 fix: also stop the concurrent background AUDIO download.
            # Without this, "paused" keeps burning bandwidth and Resume
            # spawns a second yt-dlp writing to the same audio temp file
            # (-c --no-part) while the first may still hold it.
            _abg = getattr(self, '_audio_bg_process', None)
            if _abg is not None and _abg.poll() is None:
                try:
                    if sys.platform == 'win32':
                        subprocess.run(
                            ['taskkill', '/F', '/T', '/PID', str(_abg.pid)],
                            capture_output=True, timeout=10,
                            creationflags=CREATE_NO_WINDOW)
                    else:
                        _abg.kill()
                except Exception:
                    pass
                self.append_terminal_output(
                    "Background audio download paused too (partial kept).\n", 'warning')
            self._audio_bg_process = None
            self.pause_btn.config(text='Resume', command=self.resume_download)
            self.stop_btn.config(state='normal')
            self.append_terminal_output(
                "\nDownload PAUSED. Partial file kept. Click Resume to continue.\n", 'warning')
            self.status_var.set("Download paused - click Resume to continue")
            self.progress_bar.stop()

    def resume_download(self):
        """Resume a paused download by replaying the exact same worker+args.
        yt-dlp -c flag is already in the worker args so it picks up the partial file."""
        if not self._download_paused:
            return
        if self._resume_target is None:
            # No saved context - fall back to fresh download
            self._download_paused = False
            self._reset_download_buttons()
            self.download_and_merge()
            return

        self._download_paused = False
        self._download_stopped = False
        self.pause_btn.config(text='Pause', command=self.pause_download, state='disabled')
        self.stop_btn.config(state='disabled')
        self.append_terminal_output("\nResuming download (continuing from partial file)...\n", 'info')
        self.status_var.set("Resuming download...")

        # Replay the exact same worker with the exact same args - no UI re-read
        thread = threading.Thread(target=self._resume_target, args=self._resume_args)
        thread.daemon = True
        thread.start()

    def stop_download(self):
        """Stop the current download entirely."""
        # If there are queued items, ask whether to clear them too
        with self._queue_lock:
            q_len = len(self._download_queue)
        if q_len:
            clear_q = messagebox.askyesno(
                "Stop Download",
                str(q_len) + " download(s) are queued.\n\n"
                "Clear the queue as well?")
            if clear_q:
                with self._queue_lock:
                    self._download_queue.clear()
                self._refresh_queue_panel()

        # Set the flag first - the readline loop checks this and will break immediately
        self._download_stopped = True
        self._download_active = False
        self._download_paused = False
        # Clear resume context so a stopped download cannot be accidentally resumed
        self._resume_target = None
        self._resume_args = ()

        # Kill the process tree regardless of whether our reference is still valid
        if self._download_process is not None:
            self._kill_process(self._download_process)
            self._download_process = None

        # Kill FFmpeg if it is in the middle of a merge.
        # Do NOT call _kill_process here - that closes process.stdout, which
        # deadlocks with communicate() in the worker thread that already owns
        # the pipe.  Instead kill by PID only and let communicate() return
        # naturally once the process is dead.
        if self._ffmpeg_process is not None:
            try:
                pid = self._ffmpeg_process.pid
                if sys.platform == 'win32':
                    subprocess.run(
                        ['taskkill', '/F', '/T', '/PID', str(pid)],
                        capture_output=True,
                        creationflags=CREATE_NO_WINDOW,
                    )
                else:
                    self._ffmpeg_process.kill()
            except Exception:
                pass
            self._ffmpeg_process = None

        # Kill the background audio subprocess if it is running concurrently.
        # Same PID-only approach - communicate() in _download_audio_bg owns
        # the pipe so we must not close stdout from here.
        if self._audio_bg_process is not None:
            try:
                pid = self._audio_bg_process.pid
                if sys.platform == 'win32':
                    subprocess.run(
                        ['taskkill', '/F', '/T', '/PID', str(pid)],
                        capture_output=True,
                        creationflags=CREATE_NO_WINDOW,
                    )
                else:
                    self._audio_bg_process.kill()
            except Exception:
                pass
            self._audio_bg_process = None

        self._reset_download_buttons()
        self.append_terminal_output("\nDownload STOPPED by user.\n", 'error')
        self.download_status_var.set("Download stopped")
        self.status_var.set("Download stopped")
        self.progress_bar.stop()
        self.progress_var.set("Ready")

        # If the user kept the queue, start the next item after a short delay
        # (_download_stopped is reset inside _start_next_queued before the thread starts)
        with self._queue_lock:
            _has_queue = bool(self._download_queue)
            _q_len = len(self._download_queue)
        if _has_queue:
            self.append_terminal_output(
                str(_q_len) + ' item(s) remaining in queue - continuing...\n', 'info')
            self.root.after(500, self._start_next_queued)
        
    def process_ytdlp_output(self, line):
        """Process and format yt-dlp output for terminal display with dynamic progress"""
        line = line.strip()
        if not line:
            return

        line_lower = line.lower()

        if '[download]' in line_lower and '%' in line:
            self.update_progress_line(line)
            return

        # Any non-progress output invalidates the stored progress line position
        self._progress_line_index = None

        if '[download]' in line_lower:
            if 'destination:' in line_lower:
                self.append_terminal_output("File: " + line + "\n", 'info')
            else:
                self.append_terminal_output("Download: " + line + "\n", 'info')
        elif 'error' in line_lower:
            self.append_terminal_output("ERROR: " + line + "\n", 'error')
        elif 'warning' in line_lower:
            self.append_terminal_output("WARNING: " + line + "\n", 'warning')
        elif 'extracting' in line_lower or 'downloading' in line_lower:
            self.append_terminal_output("Process: " + line + "\n", 'info')
        elif 'finished' in line_lower or 'completed' in line_lower:
            self.append_terminal_output("SUCCESS: " + line + "\n", 'success')
        elif 'cache' in line_lower or 'cached' in line_lower:
            self.append_terminal_output("CACHE: " + line + "\n", 'cache')
        else:
            self.append_terminal_output(line + "\n", 'info')

    def update_progress_line(self, progress_line):
        """Update the current progress line in-place using a stored index.
        When called from a background thread, dispatches to the main thread
        at most once every 100 ms to avoid flooding Tkinter's event queue."""
        # Fan out BEFORE the throttle and the main-thread hop: progress is
        # written in place by stored index rather than through
        # append_terminal_output, so listeners never saw it - which left the
        # dev runner unable to observe download progress at all.
        for _cb in list(getattr(self, '_output_listeners', ())):
            try:
                _cb("Progress: " + progress_line + "\n", 'progress')
            except Exception:
                pass
        try:
            if threading.current_thread() != threading.main_thread():
                now = time.monotonic()
                if now - getattr(self, '_last_progress_dispatch', 0) < 0.1:
                    return  # drop this update - UI refreshed recently enough
                self._last_progress_dispatch = now
                self.root.after(0, lambda: self.update_progress_line(progress_line))
                return

            formatted_progress = "Progress: " + progress_line

            # Parse progress for status bar: "45.3% | 8.23MiB/s | ETA 00:03"
            # Uses module-level pre-compiled patterns - no re.compile() overhead per tick
            try:
                _pct_m = _RE_PROGRESS_PCT.search(progress_line)
                _spd_m = _RE_PROGRESS_SPD.search(progress_line)
                _eta_m = _RE_PROGRESS_ETA.search(progress_line)
                if _pct_m:
                    _sb = "Downloading: " + _pct_m.group(1) + "%"
                    if _spd_m:
                        _sb += " | " + _spd_m.group(1)
                    if _eta_m:
                        _sb += " | ETA " + _eta_m.group(1)
                    self.status_var.set(_sb)
            except Exception:
                pass

            if self._progress_line_index is not None:
                # Delete the old progress line wherever it sits, then re-append at
                # the bottom so the progress bar is always the last visible line
                end_of_line = self._progress_line_index + " lineend +1c"
                self.terminal_text.delete(self._progress_line_index, end_of_line)
            # Append fresh at the end and record the new position
            self._progress_line_index = self.terminal_text.index("end -1c linestart")
            self.terminal_text.insert(tk.END, formatted_progress + '\n', 'progress')

            if self.auto_scroll.get():
                self.terminal_text.see(tk.END)

        except Exception as e:
            print("Error updating progress line: " + str(e))
            self._progress_line_index = None
            self.append_terminal_output("Progress: " + progress_line + "\n", 'progress')

    def setup_cache_directories(self):
        """Setup the ysa_cache folder NEXT TO THE EXE (user requirement).

        Everything the app produces internally lives in this one folder:
        cached streams, premuxed files, in-flight temp work, preview builds,
        per-invocation cookie copies, and session logs. The old location was
        %TEMP%/YSA_Cache, which Windows Disk Cleanup / Storage Sense is
        allowed to purge at any time - a persistent cache does not belong
        there. Final downloaded videos still go to the user's download
        folder; they must never live inside the folder Clear Cache nukes."""
        try:
            # Cache root beside YSA.exe (SCRIPT_DIR handles frozen/script)
            self.ysa_cache_root = os.path.join(
                SCRIPT_DIR, getattr(self, "cache_dirname", "ysa_cache"))
            os.makedirs(self.ysa_cache_root, exist_ok=True)

            # ── State root: survives routine cache clears BY LOCATION ──
            # Session logs and the yt-dlp player/nsig cache are
            # operational state, not cache: clear-cache-on-exit used to
            # wipe both, costing diagnostics and forcing the player-JS
            # re-solve on the first video of every session. Survival is
            # structural now - the delete paths need no new logic.
            self.ysa_state_root = os.path.join(
                SCRIPT_DIR, getattr(self, "state_dirname", "ysa_state"))
            os.makedirs(self.ysa_state_root, exist_ok=True)

            # Single home for ALL temporary operations
            self.ysa_tmp_dir = os.path.join(self.ysa_cache_root, "tmp")
            os.makedirs(self.ysa_tmp_dir, exist_ok=True)

            # Session logs (terminal output mirrored to disk)
            self.ysa_logs_dir = os.path.join(self.ysa_state_root, "logs")
            os.makedirs(self.ysa_logs_dir, exist_ok=True)

            # One-time migration: the old %TEMP% cache is rebuildable stream
            # data - remove it in the background so it stops wasting disk.
            _old_root = os.path.join(tempfile.gettempdir(), "YSA_Cache")
            if os.path.isdir(_old_root):
                threading.Thread(target=shutil.rmtree, args=(_old_root,),
                                 kwargs={'ignore_errors': True},
                                 daemon=True).start()
            
            # Video cache directory
            self.video_cache_dir = os.path.join(self.ysa_cache_root, "video_streams")
            os.makedirs(self.video_cache_dir, exist_ok=True)

            # Audio cache directory
            self.audio_cache_dir = os.path.join(self.ysa_cache_root, "audio_streams")
            os.makedirs(self.audio_cache_dir, exist_ok=True)

            # Subtitle cache directory
            self.subtitle_cache_dir = os.path.join(self.ysa_cache_root, "subtitle_tracks")
            os.makedirs(self.subtitle_cache_dir, exist_ok=True)

            # Thumbnail cache directory
            self.thumbnail_cache_dir = os.path.join(self.ysa_cache_root, "thumbnails")
            os.makedirs(self.thumbnail_cache_dir, exist_ok=True)

            # Premuxed stream cache directory (complete format-18 style files, fully processed)
            self.premuxed_cache_dir = os.path.join(self.ysa_cache_root, "premuxed_streams")
            os.makedirs(self.premuxed_cache_dir, exist_ok=True)

            # MP3 cache directory (fully-converted, metadata-embedded MP3 files)
            self.mp3_cache_dir = os.path.join(self.ysa_cache_root, "mp3_streams")
            os.makedirs(self.mp3_cache_dir, exist_ok=True)

            # yt-dlp cache directory
            self.yt_dlp_cache_dir = os.path.join(self.ysa_state_root, "yt-dlp")
            os.makedirs(self.yt_dlp_cache_dir, exist_ok=True)
            
            # Cache metadata file
            self.cache_metadata_file = os.path.join(self.ysa_cache_root, "cache_metadata.json")
            self.load_cache_metadata()

            # Session log (terminal mirror) lives under <ysa_cache>/logs.
            self._open_session_log()

            # Cookie copies left by a previous run (or a crash) are dead once
            # no yt-dlp is alive - reap them with the same guarded rule.
            def _startup_sweep():
                self._reap_cookie_copies(threshold=1)
                _n = self._reap_ytdlp_meipass()
                if _n:
                    try:
                        self.root.after(0, lambda: self.append_terminal_output(
                            'Reclaimed ' + str(_n) + " abandoned yt-dlp temp"
                            " folder(s) from the Windows temp directory.\n",
                            'cache'))
                    except Exception:
                        pass
            threading.Thread(target=_startup_sweep, daemon=True).start()
            
        except (PermissionError, OSError) as e:
            # Fallback - disable caching
            self.ysa_cache_root = None
            self.ysa_state_root = None
            self.ysa_tmp_dir = None
            self.ysa_logs_dir = None
            self.video_cache_dir = None
            self.audio_cache_dir = None
            self.subtitle_cache_dir = None
            self.thumbnail_cache_dir = None
            self.premuxed_cache_dir = None
            self.mp3_cache_dir = None
            self.yt_dlp_cache_dir = None
            self.cache_metadata_file = None
            print(f"Warning: Could not setup cache directories: {e}")
    
    def _ensure_cache_dirs(self):
        """Recreate the cache folder if it is missing.

        Clear Cache deletes the folder outright rather than leaving an empty
        shell behind, so the structure is rebuilt lazily the next time
        something actually needs it.
        """
        try:
            root = getattr(self, 'ysa_cache_root', None)
            if root and not os.path.isdir(root):
                self.setup_cache_directories()
        except Exception:
            pass

    def _make_temp_dir(self, prefix):
        """Create a temp working directory under <ysa_cache>/tmp.

        One temp home means: the app produces files in exactly one folder,
        moves into the cache are always same-volume (os.replace safe), and
        Windows temp cleaners can't eat partial downloads. Falls back to the
        system temp folder only if the cache root is unavailable."""
        self._ensure_cache_dirs()
        base = getattr(self, 'ysa_tmp_dir', None)
        if base:
            try:
                os.makedirs(base, exist_ok=True)
                return tempfile.mkdtemp(prefix=prefix, dir=base)
            except Exception:
                pass
        return tempfile.mkdtemp(prefix=prefix)

    def load_cache_metadata(self):
        """Load cache metadata from file"""
        if not self.cache_metadata_file or not os.path.exists(self.cache_metadata_file):
            return
        
        try:
            with open(self.cache_metadata_file, 'r') as f:
                self.cache_metadata = json.load(f)
                
            # Update cached_videos from metadata and seed the running cache size total
            total_bytes = 0
            for video_id, video_data in self.cache_metadata.get('videos', {}).items():
                if video_id not in self.cached_videos:
                    self.cached_videos[video_id] = {}
                
                for format_id, file_info in video_data.get('formats', {}).items():
                    file_path = file_info.get('path')
                    if file_path and os.path.exists(file_path):
                        self.cached_videos[video_id][format_id] = file_path
                        total_bytes += file_info.get('file_size', 0)
                    else:
                        # Remove invalid cache entry
                        if video_id in self.cache_metadata.get('videos', {}):
                            self.cache_metadata['videos'][video_id]['formats'].pop(format_id, None)
            self._cache_size_bytes = total_bytes

            # Restore subtitle cache index from metadata
            for video_id, sub_data in self.cache_metadata.get('subtitles', {}).items():
                for cache_key, file_path in sub_data.items():
                    if file_path and os.path.exists(file_path):
                        if video_id not in self.cached_subtitles:
                            self.cached_subtitles[video_id] = {}
                        self.cached_subtitles[video_id][cache_key] = file_path
                        self._cache_size_bytes += os.path.getsize(file_path)
                    else:
                        # Stale entry - remove from metadata
                        self.cache_metadata.setdefault('subtitles', {}).get(video_id, {}).pop(cache_key, None)

            # Orphan-file accounting (below) walks whole cache directories
            # and stats every file. That is pure size bookkeeping - nothing
            # downstream needs it to be correct immediately - so it runs in
            # the background and the size label refreshes when it lands.
            # The metadata-driven index above stays synchronous because
            # cache lookups depend on it.
            def _scan_orphan_sizes():
              try:
                self._scan_orphan_cache_sizes()
              except Exception:
                pass
              try:
                self.root.after(0, self._update_cache_size_label)
              except Exception:
                pass
            threading.Thread(target=_scan_orphan_sizes, daemon=True).start()

        except Exception as e:
            print("Warning: Could not load cache metadata: " + str(e))

    def _scan_orphan_cache_sizes(self):
        """Add on-disk files that metadata does not track to the size total.

        Runs on a background thread, so the running total is accumulated
        locally and applied once under _cache_lock - "+=" on a shared int is
        not atomic, and downloads writing to the cache can overlap this.

        The root is captured up front and re-checked before the total is
        applied: setup_cache_directories can REPOINT ysa_cache_root while
        this thread is still walking (the dev stub swaps in ysa_cache_dev),
        and the total would then land on a counter that now means a
        different folder. A scenario run caught exactly that - 1585 MB
        counted against an empty sandbox. A stale total is discarded
        rather than corrected: the new root reloads its own metadata, so
        the only cost is that its orphan files go uncounted until the
        next scan."""
        _root_at_start = getattr(self, 'ysa_cache_root', None)
        _orphan_total = 0
        try:
            if self.subtitle_cache_dir and os.path.isdir(self.subtitle_cache_dir):
                tracked = {
                    fp for subs in self.cached_subtitles.values() for fp in subs.values()
                }
                for fname in os.listdir(self.subtitle_cache_dir):
                    fpath = os.path.join(self.subtitle_cache_dir, fname)
                    if os.path.isfile(fpath) and fpath not in tracked:
                        try:
                            _orphan_total += os.path.getsize(fpath)
                        except Exception:
                            pass

            # Count thumbnail cache files - thumbnails are not tracked in metadata,
            # just sized on disk at startup.
            if self.thumbnail_cache_dir and os.path.isdir(self.thumbnail_cache_dir):
                for fname in os.listdir(self.thumbnail_cache_dir):
                    fpath = os.path.join(self.thumbnail_cache_dir, fname)
                    if os.path.isfile(fpath):
                        try:
                            _orphan_total += os.path.getsize(fpath)
                        except Exception:
                            pass

            # Count premuxed cache files and rebuild in-memory index.
            if self.premuxed_cache_dir and os.path.isdir(self.premuxed_cache_dir):
                for fname in os.listdir(self.premuxed_cache_dir):
                    fpath = os.path.join(self.premuxed_cache_dir, fname)
                    if os.path.isfile(fpath):
                        try:
                            _orphan_total += os.path.getsize(fpath)
                            # Filename pattern: {video_id}_premuxed_{format_id}{ext}
                            stem = os.path.splitext(fname)[0]
                            if '_premuxed_' in stem:
                                parts = stem.split('_premuxed_', 1)
                                vid = parts[0]
                                fmt = parts[1]
                                if vid not in self.cached_premuxed:
                                    self.cached_premuxed[vid] = {}
                                self.cached_premuxed[vid][fmt] = fpath
                        except Exception:
                            pass

            # Count MP3 cache files and rebuild in-memory index.
            # MP3 entries are stored in cache_metadata['videos'] under 'mp3_*' keys,
            # so they were already counted in the main format loop above.  Only add
            # size here for files that are NOT yet tracked (e.g. metadata was lost).
            if self.mp3_cache_dir and os.path.isdir(self.mp3_cache_dir):
                already_tracked = {
                    fpath
                    for fmts in self.cached_videos.values()
                    for key, fpath in fmts.items()
                    if key.startswith('mp3_')
                }
                for fname in os.listdir(self.mp3_cache_dir):
                    fpath = os.path.join(self.mp3_cache_dir, fname)
                    if os.path.isfile(fpath):
                        try:
                            stem = os.path.splitext(fname)[0]
                            if '_mp3_' in stem:
                                parts = stem.split('_mp3_', 1)
                                vid = parts[0]
                                fmt_id = parts[1]
                                key = 'mp3_' + fmt_id
                                if vid not in self.cached_videos:
                                    self.cached_videos[vid] = {}
                                self.cached_videos[vid][key] = fpath
                                # Only add size if this file was not in metadata
                                if fpath not in already_tracked:
                                    _orphan_total += os.path.getsize(fpath)
                        except Exception:
                            pass

        except Exception as e:
            # Size bookkeeping only - never touch cache_metadata here.
            print("Warning: orphan cache size scan failed: " + str(e))
    
        if getattr(self, 'ysa_cache_root', None) != _root_at_start:
            # The cache root moved under this scan - the total belongs to
            # a folder this counter no longer describes.
            return
        try:
            with self._cache_lock:
                self._cache_size_bytes += _orphan_total
        except Exception:
            self._cache_size_bytes += _orphan_total

    def _post_download_cache_maintenance(self):
        """Flush cache metadata to disk and run eviction AFTER download completes.
        This is intentionally deferred so it never runs mid-download or mid-stream."""
        try:
            self._evict_cache_if_needed()   # evict first (may trim metadata)
            self.save_cache_metadata()      # then flush to disk once
        except Exception as e:
            print("Warning: post-download cache maintenance failed: " + str(e))
        self.root.after(0, self._update_cache_size_label)

    def save_cache_metadata(self):
        """Persist in-memory cache dict to disk atomically.
        Writes to a .tmp file first, then os.replace() swaps it in so a crash
        mid-write never corrupts the existing metadata file."""
        if not self.cache_metadata_file:
            return
        try:
            if 'videos' not in self.cache_metadata:
                self.cache_metadata['videos'] = {}
            tmp_path = self.cache_metadata_file + '.tmp'
            with open(tmp_path, 'w') as f:
                json.dump(self.cache_metadata, f, indent=2)
            os.replace(tmp_path, self.cache_metadata_file)
        except Exception as e:
            print("Warning: Could not save cache metadata: " + str(e))
            try:
                if os.path.exists(tmp_path):
                    os.remove(tmp_path)
            except Exception:
                pass
    
    def _on_close(self):
        """Handle window close (X button). Stops any active download cleanly,
        then runs cleanup and destroys the window."""
        # Prevent double-firing (atexit + explicit call)
        if getattr(self, '_cleanup_done', False):
            self.root.destroy()
            return

        # Kill active download process without showing queue dialogs
        if getattr(self, '_download_active', False) or getattr(self, '_download_process', None):
            self._download_stopped = True
            self._download_active = False
            self._download_paused = False
            proc = getattr(self, '_download_process', None)
            if proc is not None:
                try:
                    self._kill_process(proc)
                except Exception:
                    pass
            self._download_process = None

        # If a download was in progress, push it back to the front of the queue
        # so _save_queue will persist it alongside any remaining items.
        resume_target = getattr(self, '_resume_target', None)
        resume_args   = getattr(self, '_resume_args', ())
        if resume_target and resume_args:
            # Use __func__ comparison so bound-method identity is stable
            merge_fn  = self._download_and_merge_worker_with_terminal.__func__
            direct_fn = self._download_direct_worker_with_terminal.__func__
            audio_fn  = self._download_audio_only_worker.__func__
            rt_fn     = getattr(resume_target, '__func__', None)
            if rt_fn is merge_fn:
                worker_name = 'merge'
            elif rt_fn is direct_fn:
                worker_name = 'direct'
            elif rt_fn is audio_fn:
                worker_name = 'audio'
            else:
                worker_name = None
            if worker_name:
                label = 'Interrupted download'
                try:
                    if worker_name == 'merge':
                        vi = resume_args[9] if len(resume_args) > 9 else {}
                    elif worker_name == 'direct':
                        vi = resume_args[4] if len(resume_args) > 4 else {}
                    else:  # audio
                        vi = resume_args[3] if len(resume_args) > 3 else {}
                    if isinstance(vi, dict) and vi.get('title'):
                        label = vi['title']
                except Exception:
                    pass
                self._download_queue.insert(0, {
                    'worker':      resume_target,
                    'worker_name': worker_name,
                    'args':        resume_args,
                    'label':       label,
                    'is_audio':    worker_name == 'audio',
                })

        # If batch analysis was mid-run, cancel it and save remaining URLs
        if getattr(self, '_batch_running', False):
            self._batch_cancelled = True
            self._batch_running = False
            # C4: reconstruct slice only when _on_close actually needs it
            _bref = getattr(self, '_batch_pending_urls_ref', None)
            _bidx = getattr(self, '_batch_pending_start_idx', 0)
            if _bref:
                pending = list(_bref[_bidx:])
            else:
                pending = list(getattr(self, '_batch_pending_urls', []))
            if pending:
                # Build set of URLs already accounted for by the queue/active
                # download so we don't write duplicates into the batch file.
                url_index = {'merge': 7, 'direct': 3, 'audio': 2}
                accounted = set()
                r_target = getattr(self, '_resume_target', None)
                r_args   = getattr(self, '_resume_args', ())
                if r_target and r_args:
                    merge_fn  = self._download_and_merge_worker_with_terminal.__func__
                    direct_fn = self._download_direct_worker_with_terminal.__func__
                    audio_fn  = self._download_audio_only_worker.__func__
                    rt_fn     = getattr(r_target, '__func__', None)
                    if rt_fn is merge_fn:
                        wn = 'merge'
                    elif rt_fn is direct_fn:
                        wn = 'direct'
                    elif rt_fn is audio_fn:
                        wn = 'audio'
                    else:
                        wn = None
                    if wn:
                        idx = url_index[wn]
                        if len(r_args) > idx:
                            accounted.add(str(r_args[idx]))
                for qe in self._download_queue:
                    wn = qe.get('worker_name', '')
                    idx = url_index.get(wn)
                    if idx is not None:
                        qargs = qe.get('args', ())
                        if len(qargs) > idx:
                            accounted.add(str(qargs[idx]))
                pending = [u for u in pending if u not in accounted]
                if pending:
                    try:
                        batch_file = os.path.join(SCRIPT_DIR, 'ysa_batch_pending.json')
                        tmp = batch_file + '.tmp'
                        with open(tmp, 'w') as f:
                            json.dump(pending, f, indent=2)
                        os.replace(tmp, batch_file)
                    except Exception as e:
                        print('Warning: Could not save pending batch: ' + str(e))

        self.cleanup_on_exit()
        self.root.destroy()

    def cleanup_on_exit(self):
        """Cleanup cache on program exit"""
        # Guard against double-execution (atexit + explicit _on_close call)
        if getattr(self, '_cleanup_done', False):
            return
        self._cleanup_done = True

        # Capture the window box BEFORE anything is torn down, then persist.
        self._capture_window_geometry()
        try:
            self._save_config_now()
        except Exception:
            pass

        self._close_session_log()

        _stop_proxy()

        # Stop bgutil server on exit — unless "Keep running" is enabled,
        # in which case the server stays alive for the next YSA session.
        if getattr(self, '_bgutil_process', None) is not None:
            if not getattr(self, 'bgutil_keep_running', True):
                try:
                    self._bgutil_stop_server()
                except Exception:
                    pass

        # Save persistent config and queue before anything else
        # M2 fix: call the synchronous writer. The debounced _save_config()
        # only schedules root.after(500), which never fires during shutdown,
        # so settings changed in the final moments were silently lost.
        try:
            self._save_config_now()
        except Exception as e:
            print("Warning: Could not save config: " + str(e))
        try:
            self._save_queue()
        except Exception as e:
            print("Warning: Could not save queue: " + str(e))

        # Check persistent cache setting (use getattr in case GUI never fully initialized)
        keep_cache = False
        try:
            pvar = getattr(self, 'persistent_cache_var', None)
            keep_cache = pvar.get() if pvar else self.persistent_cache
        except Exception:
            pass

        if keep_cache:
            print("Persistent cache enabled - skipping cache cleanup.")
            # Still clean up temp directories even with persistent cache
            self._cleanup_ysa_temp_dirs(silent=True)
            return

        try:
            # Clean all ysa_* temp directories first
            self._cleanup_ysa_temp_dirs(silent=True)
            if self.ysa_cache_root and os.path.exists(self.ysa_cache_root):
                print("Cleaning up video cache...")

                # Only clean up video/audio streams, keep yt-dlp cache for future sessions
                if self.video_cache_dir and os.path.exists(self.video_cache_dir):
                    shutil.rmtree(self.video_cache_dir)
                if self.audio_cache_dir and os.path.exists(self.audio_cache_dir):
                    shutil.rmtree(self.audio_cache_dir)
                if self.subtitle_cache_dir and os.path.exists(self.subtitle_cache_dir):
                    shutil.rmtree(self.subtitle_cache_dir)
                if self.mp3_cache_dir and os.path.exists(self.mp3_cache_dir):
                    shutil.rmtree(self.mp3_cache_dir)

                # Clear stream cache from metadata
                if 'videos' in self.cache_metadata:
                    self.cache_metadata['videos'] = {}
                if 'subtitles' in self.cache_metadata:
                    self.cache_metadata['subtitles'] = {}
                self.cached_subtitles = {}
                self.save_cache_metadata()
                self._cache_size_bytes = 0

                print("Cache cleanup complete.")

            # Runs last and unconditionally when enabled: the per-category
            # cleanup above is skipped entirely when "keep cache between
            # sessions" is on, and this setting deliberately overrides it.
            # Safe here because the session log handle is already closed.
            if getattr(self, 'clear_cache_on_exit', False):
                _rm, _left = self._delete_all_cache_folders()
                print("Clear-on-exit removed: "
                      + (", ".join(_rm) if _rm else "nothing")
                      + (" (some files were locked)" if _left else ""))
        except Exception as e:
            print("Warning: Cache cleanup failed: " + str(e))

    def _cleanup_ysa_temp_dirs(self, silent=False):
        """Remove all ysa_* temporary directories from the system temp folder.
        Covers: ysa_download_, ysa_precache_, ysa_preview_, ysa_audio_,
        ysa_sub_, ysa_c3_ - anything left behind by crashes or previews.
        silent=True suppresses terminal output (used during exit cleanup)."""
        _removed = 0
        try:
            # Primary: everything under <ysa_cache>/tmp (the single temp home)
            base = getattr(self, 'ysa_tmp_dir', None)
            if base and os.path.isdir(base):
                for name in os.listdir(base):
                    p = os.path.join(base, name)
                    try:
                        if os.path.isdir(p):
                            shutil.rmtree(p, ignore_errors=True)
                        else:
                            os.remove(p)
                        _removed += 1
                    except Exception:
                        pass
        except Exception:
            pass
        try:
            # Legacy: ysa_* leftovers in the system temp from older builds
            tmp_root = tempfile.gettempdir()
            for name in os.listdir(tmp_root):
                if name.startswith('ysa_') and os.path.isdir(os.path.join(tmp_root, name)):
                    try:
                        shutil.rmtree(os.path.join(tmp_root, name), ignore_errors=True)
                        _removed += 1
                    except Exception:
                        pass
            if _removed > 0 and not silent:
                self.append_terminal_output(
                    'Cleaned up ' + str(_removed) + ' temporary directory(s).\n', 'success')
        except Exception as e:
            if not silent:
                self.append_terminal_output(
                    'Temp cleanup warning: ' + str(e) + '\n', 'warning')
    
    def get_video_cache_key(self, video_id, format_id):
        """Generate cache key for video stream"""
        return f"{video_id}_{format_id}"
    
    def get_cached_video_path(self, video_id, format_id):
        """Check if video stream is cached and return path (C1: lock protected)"""
        if not self.video_cache_dir:
            return None
        with self._cache_lock:
            if video_id in self.cached_videos and format_id in self.cached_videos[video_id]:
                file_path = self.cached_videos[video_id][format_id]
                if os.path.exists(file_path):
                    return file_path
                else:
                    del self.cached_videos[video_id][format_id]
                    if not self.cached_videos[video_id]:
                        del self.cached_videos[video_id]
        return None
    
    def cache_video_stream(self, video_id, format_id, source_path):
        """Cache a video stream for future use"""
        self._ensure_cache_dirs()   # Clear Cache may have removed it
        if not self.video_cache_dir or not os.path.exists(source_path):
            return None
        
        try:
            file_ext = os.path.splitext(source_path)[1] or '.mp4'
            cache_filename = self.get_video_cache_key(video_id, format_id) + file_ext
            cache_path = os.path.join(self.video_cache_dir, cache_filename)

            # Move instead of copy - zero extra I/O when src and dst share a filesystem
            try:
                os.replace(source_path, cache_path)
            except OSError:
                # Cross-device move (rare) - fall back to copy+delete
                shutil.copy2(source_path, cache_path)

            file_bytes = os.path.getsize(cache_path)
            with self._cache_lock:
                if video_id not in self.cached_videos:
                    self.cached_videos[video_id] = {}
                self.cached_videos[video_id][format_id] = cache_path
                self._cache_size_bytes += file_bytes

            # Keep metadata dict in sync (in-memory only - flushed to disk post-download)
            if 'videos' not in self.cache_metadata:
                self.cache_metadata['videos'] = {}
            if video_id not in self.cache_metadata['videos']:
                self.cache_metadata['videos'][video_id] = {'formats': {}}
            self.cache_metadata['videos'][video_id]['formats'][format_id] = {
                'path': cache_path,
                'cached_at': time.time(),
                'file_size': file_bytes,
            }
            # NOTE: save_cache_metadata and eviction are intentionally deferred to
            # _post_download_cache_maintenance() - never called mid-download.

            print("Cached video stream: " + cache_filename)
            return cache_path

        except Exception as e:
            print("Warning: Could not cache video stream: " + str(e))
            return None
    
    def get_cached_audio_path(self, video_id, format_id):
        """Check if audio stream is cached and return path (C1: lock protected)."""
        if not self.audio_cache_dir:
            return None
        key = "audio_" + format_id
        with self._cache_lock:
            if video_id in self.cached_videos and key in self.cached_videos[video_id]:
                file_path = self.cached_videos[video_id][key]
                if os.path.exists(file_path):
                    return file_path
                else:
                    del self.cached_videos[video_id][key]
                    if not self.cached_videos[video_id]:
                        del self.cached_videos[video_id]
        return None

    def cache_audio_stream(self, video_id, format_id, source_path):
        """Cache an audio stream for future use."""
        self._ensure_cache_dirs()   # Clear Cache may have removed it
        if not self.audio_cache_dir or not os.path.exists(source_path):
            return None
        try:
            file_ext = os.path.splitext(source_path)[1] or '.m4a'
            cache_filename = video_id + "_audio_" + format_id + file_ext
            cache_path = os.path.join(self.audio_cache_dir, cache_filename)

            # Move instead of copy - zero extra I/O when src and dst share a filesystem
            try:
                os.replace(source_path, cache_path)
            except OSError:
                shutil.copy2(source_path, cache_path)

            file_bytes = os.path.getsize(cache_path)
            with self._cache_lock:
                if video_id not in self.cached_videos:
                    self.cached_videos[video_id] = {}
                self.cached_videos[video_id]["audio_" + format_id] = cache_path
                self._cache_size_bytes += file_bytes

            # Keep metadata dict in sync (in-memory only - flushed to disk post-download)
            if 'videos' not in self.cache_metadata:
                self.cache_metadata['videos'] = {}
            if video_id not in self.cache_metadata['videos']:
                self.cache_metadata['videos'][video_id] = {'formats': {}}
            self.cache_metadata['videos'][video_id]['formats']["audio_" + format_id] = {
                'path': cache_path,
                'cached_at': time.time(),
                'file_size': file_bytes,
            }
            # NOTE: save_cache_metadata and eviction are intentionally deferred to
            # _post_download_cache_maintenance() - never called mid-download.

            print("Cached audio stream: " + cache_filename)
            return cache_path
        except Exception as e:
            print("Warning: Could not cache audio stream: " + str(e))
            return None

    def get_cached_mp3_path(self, video_id, audio_format_id):
        """Return path to a cached MP3 (fully converted, metadata embedded), or None."""
        if not self.mp3_cache_dir or not video_id or not audio_format_id:
            return None
        key = "mp3_" + audio_format_id
        # _cache_lock: lookups can race caching/eviction mutating these
        # dicts from other threads (queue advance vs. audio worker).
        with self._cache_lock:
            if video_id in self.cached_videos and key in self.cached_videos[video_id]:
                file_path = self.cached_videos[video_id][key]
                if os.path.exists(file_path):
                    return file_path
                # Stale entry - prune it
                del self.cached_videos[video_id][key]
                if not self.cached_videos[video_id]:
                    del self.cached_videos[video_id]
        return None

    def cache_mp3_stream(self, video_id, audio_format_id, source_path):
        """Copy a fully-processed MP3 into the MP3 cache for instant reuse.

        Unlike raw audio streams (which are moved), the source MP3 stays in
        the downloads folder so we always copy rather than move.
        """
        if not self.mp3_cache_dir or not video_id or not audio_format_id:
            return None
        if not os.path.exists(source_path):
            return None
        self._ensure_cache_dirs()
        try:
            cache_filename = video_id + "_mp3_" + audio_format_id + ".mp3"
            cache_path = os.path.join(self.mp3_cache_dir, cache_filename)
            shutil.copy2(source_path, cache_path)
            file_bytes = os.path.getsize(cache_path)
            # _cache_lock: dict + size-counter + metadata mutations must not
            # interleave with save_cache_metadata iterating them.
            with self._cache_lock:
                if video_id not in self.cached_videos:
                    self.cached_videos[video_id] = {}
                self.cached_videos[video_id]["mp3_" + audio_format_id] = cache_path
                self._cache_size_bytes += file_bytes
                if 'videos' not in self.cache_metadata:
                    self.cache_metadata['videos'] = {}
                if video_id not in self.cache_metadata['videos']:
                    self.cache_metadata['videos'][video_id] = {'formats': {}}
                self.cache_metadata['videos'][video_id]['formats']["mp3_" + audio_format_id] = {
                    'path': cache_path,
                    'cached_at': time.time(),
                    'file_size': file_bytes,
                }
            print("Cached MP3 stream: " + cache_filename)
            return cache_path
        except Exception as e:
            print("Warning: Could not cache MP3 stream: " + str(e))
            return None

    def _subtitle_cache_key(self, lang, is_auto):
        """Stable dict key for a subtitle entry: 'auto_en' or 'manual_en'."""
        prefix = 'auto' if is_auto else 'manual'
        return prefix + '_' + (lang or 'en')

    def get_cached_subtitle_path(self, video_id, lang, is_auto):
        """Return path to a cached subtitle file, or None if not cached.

        Checks in-memory index first (fast), then validates the file still
        exists on disk.  Stale entries are pruned from both the index and the
        metadata dict so they don't accumulate.
        """
        if not self.subtitle_cache_dir:
            return None
        cache_key = self._subtitle_cache_key(lang, is_auto)
        vid_subs = self.cached_subtitles.get(video_id, {})
        file_path = vid_subs.get(cache_key)
        if not file_path:
            return None
        if os.path.exists(file_path):
            return file_path
        # File missing - prune stale entry
        vid_subs.pop(cache_key, None)
        if not vid_subs:
            self.cached_subtitles.pop(video_id, None)
        self.cache_metadata.setdefault('subtitles', {}).get(video_id, {}).pop(cache_key, None)
        return None

    def cache_subtitle(self, video_id, lang, is_auto, source_path):
        """Copy a freshly-downloaded subtitle into the subtitle cache.

        Uses copy (not move) because the source file is still needed by the
        current merge.  Writes to a temp file first then renames atomically so
        a concurrent reader never sees a half-written file.

        In-memory index and metadata dict are updated immediately.
        Flush to disk is deferred to _post_download_cache_maintenance() so it
        never races with a parallel download writing the same metadata file.
        """
        self._ensure_cache_dirs()   # Clear Cache may have removed it
        if not self.subtitle_cache_dir or not os.path.exists(source_path):
            return None
        try:
            cache_key = self._subtitle_cache_key(lang, is_auto)
            file_ext = os.path.splitext(source_path)[1] or '.srt'
            cache_filename = video_id + '_' + cache_key + file_ext
            cache_path = os.path.join(self.subtitle_cache_dir, cache_filename)

            # Atomic write: copy to temp file then rename into place.
            # This means a concurrent reader either gets the old file or the
            # complete new file - never a partial write.
            tmp_path = cache_path + '.tmp'
            shutil.copy2(source_path, tmp_path)
            os.replace(tmp_path, cache_path)

            # Update in-memory index
            if video_id not in self.cached_subtitles:
                self.cached_subtitles[video_id] = {}
            self.cached_subtitles[video_id][cache_key] = cache_path

            # Track size contribution so eviction sees subtitle files too
            try:
                self._cache_size_bytes += os.path.getsize(cache_path)
            except Exception:
                pass

            # Keep metadata dict in sync (flushed to disk post-download only)
            self.cache_metadata.setdefault('subtitles', {})
            if video_id not in self.cache_metadata['subtitles']:
                self.cache_metadata['subtitles'][video_id] = {}
            self.cache_metadata['subtitles'][video_id][cache_key] = cache_path

            print('Cached subtitle: ' + cache_filename)
            return cache_path
        except Exception as e:
            print('Warning: Could not cache subtitle: ' + str(e))
            return None

    def cache_thumbnail(self, video_id, thumb_url, video_info=None):
        """Return a path to a cached thumbnail for video_id, downloading from
        the highest-resolution URL available.  Falls back to thumb_url if the
        thumbnails array is unavailable.

        Thumbnails are cached as <video_id>.jpg.  Once cached they are reused
        for every subsequent download of the same video at any resolution,
        saving a network round-trip and making repeat downloads faster.
        The file is included in the cache size counter and cleared by
        clear_video_cache alongside video, audio, and subtitle files."""
        if not self.thumbnail_cache_dir or not video_id or not thumb_url:
            return None
        cache_path = os.path.join(self.thumbnail_cache_dir, video_id + '.jpg')
        # C2: check in-memory set before hitting the filesystem
        with self._cache_lock:
            _in_set = video_id in self._thumbnail_cached_ids
        if _in_set or os.path.exists(cache_path):
            with self._cache_lock:
                self._thumbnail_cached_ids.add(video_id)
            self.append_terminal_output('Thumbnail from cache.\n', 'info')
            return cache_path
        try:
            # Prefer the highest-resolution thumbnail from the thumbnails array.
            # Use the explicitly passed video_info - never self.current_video_info,
            # which may already point to a different video if the user pasted a new
            # URL while this download was running.
            best_url = thumb_url
            try:
                _vid_info = video_info or {}
                _thumbs = _vid_info.get('thumbnails') or []
                if _thumbs:
                    _best = max(
                        (t for t in _thumbs if t.get('url')),
                        key=lambda t: (t.get('width') or 0, t.get('preference') or 0),
                        default=None)
                    if _best:
                        best_url = _best['url']
            except Exception:
                pass
            r = _get_http_session().get(best_url, timeout=15)
            r.raise_for_status()
            tmp_path = cache_path + '.tmp'
            with open(tmp_path, 'wb') as tf:
                tf.write(r.content)
            os.replace(tmp_path, cache_path)
            try:
                self._cache_size_bytes += os.path.getsize(cache_path)
            except Exception:
                pass
            with self._cache_lock:
                self._thumbnail_cached_ids.add(video_id)
            self.append_terminal_output('Thumbnail downloaded.\n', 'info')
            return cache_path
        except Exception as te:
            self.append_terminal_output(
                'Thumbnail download failed: ' + str(te) + '\n', 'warning')
            return None

    @staticmethod
    def _premuxed_cache_key(format_id, sub_settings=None):
        """Return the cache key for a premuxed base file.
        The base file contains video + audio + metadata + thumbnail only -
        subtitles are never baked in, so the key is just the format_id.
        sub_settings is accepted for signature compatibility but ignored."""
        return format_id

    def get_cached_premuxed_path(self, video_id, variant_key):
        """Return path to a cached fully-processed premuxed file, or None if not cached."""
        if not self.premuxed_cache_dir:
            return None
        if video_id in self.cached_premuxed and variant_key in self.cached_premuxed[video_id]:
            path = self.cached_premuxed[video_id][variant_key]
            if os.path.exists(path):
                return path
            # Stale entry
            del self.cached_premuxed[video_id][variant_key]
            if not self.cached_premuxed[video_id]:
                del self.cached_premuxed[video_id]
        return None

    def cache_premuxed_stream(self, video_id, variant_key, source_path):
        """Copy a fully-processed premuxed file into the premuxed cache.
        Unlike video/audio streams we copy (not move) because source_path is the
        user's final output file in their Downloads folder.
        Returns the cache path on success, None on failure."""
        if not self.premuxed_cache_dir or not os.path.exists(source_path):
            return None
        try:
            ext = os.path.splitext(source_path)[1] or '.mp4'
            cache_filename = video_id + '_premuxed_' + variant_key + ext
            cache_path = os.path.join(self.premuxed_cache_dir, cache_filename)
            shutil.copy2(source_path, cache_path)
            file_bytes = os.path.getsize(cache_path)
            if video_id not in self.cached_premuxed:
                self.cached_premuxed[video_id] = {}
            self.cached_premuxed[video_id][variant_key] = cache_path
            self._cache_size_bytes += file_bytes
            self.append_terminal_output('Premuxed stream cached.\n', 'cache')
            return cache_path
        except Exception as e:
            self.append_terminal_output(
                'Warning: could not cache premuxed stream: ' + str(e) + '\n', 'warning')
            return None

    def _patch_mp4_subtitle_flag(self, mp4_path, enabled):
        """Patch the Track_Enabled bit in the subtitle track's tkhd box.

        enabled=False  ->  S / AS  modes: clear the bit so players do NOT
                           auto-show the track (user must select manually).
        enabled=True   ->  SD / ASD modes: set the bit so players DO auto-show
                           the track by default.

        FFmpeg's MP4 muxer unconditionally sets this bit regardless of the
        -disposition flag passed on the command line, so both directions need
        this correction to be reliable.

        Efficiency: because -movflags +faststart is always used, the moov box
        is guaranteed to be at the very start of the file.  We read only the
        moov box (typically 100-500 KB regardless of video length), navigate
        it entirely in memory, then seek to the exact 3-byte flags field and
        write only those bytes.  The video/audio payload (potentially several
        GB) is never read or written.

        Returns True if the patch was applied."""
        import struct as _struct
        try:
            with open(mp4_path, 'r+b') as _f:

                # Step 1: scan leading boxes to find moov.
                # With faststart, moov always precedes mdat, but ftyp (and
                # occasionally free/wide/skip boxes) come before moov.
                # We scan only the small leading boxes until moov is found -
                # we never read past moov so the multi-GB mdat is untouched.
                moov_body = None
                moov_file_offset = 0   # absolute file offset where moov starts
                MAX_SCAN = 64 * 1024   # stop scanning after 64 KB - moov is always within this
                scanned = 0

                while scanned < MAX_SCAN:
                    header = _f.read(8)
                    if len(header) < 8:
                        break
                    box_size = _struct.unpack('>I', header[:4])[0]
                    box_name = header[4:8]
                    if box_size < 8:
                        break
                    if box_name == b'moov':
                        moov_file_offset = scanned
                        moov_body = header + _f.read(box_size - 8)
                        break
                    # Skip this non-moov box entirely
                    scanned += box_size
                    _f.seek(scanned)

                if moov_body is None:
                    self.append_terminal_output(
                        'Warning: subtitle flag patch - moov box not found '
                        'in first 64 KB of file.\n', 'warning')
                    return False

                # Step 2: navigate moov in memory.
                # Offsets within moov_body are relative to the start of moov_body.
                # To get the absolute file offset we add moov_file_offset.
                patch_file_offset = None
                pos = 8   # skip the moov box header

                while pos < len(moov_body) - 8:
                    trak_size = _struct.unpack('>I', moov_body[pos:pos+4])[0]
                    trak_name = moov_body[pos+4:pos+8]
                    if trak_size < 8:
                        break
                    if trak_name == b'trak':
                        trak_end = pos + trak_size
                        tkhd_off  = None
                        hdlr_type = None   # reset per-track - never bleed between tracks
                        inner = pos + 8
                        while inner < trak_end - 8:
                            i_size = _struct.unpack('>I', moov_body[inner:inner+4])[0]
                            i_name = moov_body[inner+4:inner+8]
                            if i_size < 8:
                                break
                            if i_name == b'tkhd':
                                tkhd_off = inner
                            elif i_name == b'mdia':
                                mdia_end   = inner + i_size
                                mdia_inner = inner + 8
                                while mdia_inner < mdia_end - 8:
                                    m_size = _struct.unpack('>I', moov_body[mdia_inner:mdia_inner+4])[0]
                                    m_name = moov_body[mdia_inner+4:mdia_inner+8]
                                    if m_size < 8:
                                        break
                                    if m_name == b'hdlr':
                                        hdlr_type = moov_body[mdia_inner+16:mdia_inner+20]
                                        break
                                    mdia_inner += m_size
                            inner += i_size

                        if (tkhd_off is not None and
                                hdlr_type in (b'text', b'sbtl', b'subt', b'subp')):
                            # tkhd layout: 4 size + 4 name + 1 version + 3 flags
                            # Bit 0 of the 3-byte flags field is Track_Enabled.
                            patch_file_offset = moov_file_offset + tkhd_off + 9
                            break   # found the subtitle track - stop searching

                    pos += trak_size

                if patch_file_offset is None:
                    self.append_terminal_output(
                        'Warning: subtitle flag patch - subtitle tkhd not found.\n', 'warning')
                    return False

                # Step 3: read the current 3-byte flags value.
                _f.seek(patch_file_offset)
                raw = _f.read(3)
                if len(raw) < 3:
                    self.append_terminal_output(
                        'Warning: subtitle flag patch - could not read flags bytes.\n', 'warning')
                    return False

                flags   = _struct.unpack('>I', b'\x00' + raw)[0]
                bit_set = bool(flags & 1)

                if bit_set == enabled:
                    # Already the correct value - nothing to write
                    mode_label = 'SD/ASD' if enabled else 'S/AS'
                    self.append_terminal_output(
                        'Subtitle flag already correct for ' + mode_label + ' mode.\n', 'info')
                    return True

                # Step 4: write only the 3 changed bytes.
                new_flags = (flags | 1) if enabled else (flags & ~1)
                _f.seek(patch_file_offset)
                _f.write(_struct.pack('>I', new_flags)[1:])   # 3 bytes only

            mode_label = 'SD/ASD (auto-show)' if enabled else 'S/AS (user-select)'
            self.append_terminal_output(
                'Subtitle flag patched for ' + mode_label + ' mode.\n', 'info')
            return True

        except Exception as _e:
            self.append_terminal_output(
                'Warning: could not patch subtitle flag: ' + str(_e) + '\n', 'warning')
            return False

    # === BEGIN DEV TOOLS ===
    STUB_MODES = ('ok', 'http416', 'crash_at_exit', 'bot_check', 'http403',
                  'terminated', 'format_expired', 'partial', 'disk_full', 'slow')

    def _stub_path(self):
        """Locate the fake yt-dlp beside the app.

        Prefers the compiled .exe - it is directly executable, needs no
        cmd.exe (which may be blocked by policy) and no Python, and keeps the
        real subprocess boundary so Pause can still kill it.
        """
        for name in ('ysa_fake_ytdlp.exe', 'ysa_fake_ytdlp.py'):
            p = os.path.join(SCRIPT_DIR, name)
            if os.path.isfile(p):
                return p
        return None

    def _apply_stub_state(self, announce=True):
        """Point the app at the stub (or back at the real yt-dlp).

        Mode changes need no restart: the stub reads YSA_FAKE_MODE when it is
        spawned, and a child process inherits this one's environment.
        """
        try:
            if self._real_ytdlp_path is None:
                self._real_ytdlp_path = self.ytdlp_path
            _r = getattr(self, '_devtest_runner', None)
            if _r is not None and _r.is_running():
                self.append_terminal_output(
                    "Cannot change the stub while a scenario run is in"
                    " progress - it manages the cache sandbox itself.\n",
                    "warning")
                self.stub_enabled = not self.stub_enabled   # undo the toggle
                self._refresh_stub_button()
                return
            _p = self._stub_path()
            if self.stub_enabled and _p:
                os.environ['YSA_YTDLP_PATH'] = _p
                os.environ['YSA_FAKE_MODE'] = str(self.stub_mode or 'ok')
                os.environ['YSA_FAKE_STATE'] = SCRIPT_DIR
                if int(self.stub_fail_times or 0) > 0:
                    os.environ['YSA_FAKE_FAIL_TIMES'] = str(int(self.stub_fail_times))
                else:
                    os.environ.pop('YSA_FAKE_FAIL_TIMES', None)
                # the invocation counter is per-session; start each enable
                # from scratch so "fail the first N" means what it says
                try:
                    _c = os.path.join(SCRIPT_DIR, '.ysa_fake_count')
                    if os.path.isfile(_c):
                        os.remove(_c)          # legacy single-file counter
                    shutil.rmtree(os.path.join(SCRIPT_DIR, '.ysa_fake_calls'),
                                  ignore_errors=True)
                except Exception:
                    pass
                self.ytdlp_path = _p

                # Fake streams must never reach the real cache or the real
                # download folder. A stubbed download is cached under the
                # video's genuine id and format, so without this a later
                # REAL download of that video would be served 1.8 MB of
                # zeros - and the output lands in the user's library.
                if self._real_cache_dirname is None:
                    self._real_cache_dirname = getattr(self, 'cache_dirname',
                                                       'ysa_cache')
                    self._real_state_dirname = getattr(self, 'state_dirname',
                                                       'ysa_state')
                    self._real_download_path = self.download_path
                # Dev sandbox mirrors the real split: ysa_cache_dev for
                # cache, ysa_state_dev for logs + the yt-dlp cache - the
                # stub can never touch either real folder.
                self.cache_dirname = 'ysa_cache_dev'
                self.state_dirname = 'ysa_state_dev'
                self.setup_cache_directories()
                try:
                    _so = os.path.join(SCRIPT_DIR, 'selftest_output')
                    os.makedirs(_so, exist_ok=True)
                    self.download_path = _so
                except Exception:
                    pass
            else:
                if self.stub_enabled and not _p:
                    self.stub_enabled = False
                for _k in ('YSA_YTDLP_PATH', 'YSA_FAKE_MODE',
                           'YSA_FAKE_FAIL_TIMES', 'YSA_FAKE_STATE'):
                    os.environ.pop(_k, None)
                if self._real_ytdlp_path:
                    self.ytdlp_path = self._real_ytdlp_path
                # put the real cache and download folder back
                if self._real_cache_dirname is not None:
                    self.cache_dirname = self._real_cache_dirname
                    if self._real_state_dirname is not None:
                        self.state_dirname = self._real_state_dirname
                        self._real_state_dirname = None
                    self.setup_cache_directories()
                    if self._real_download_path:
                        self.download_path = self._real_download_path
                    self._real_cache_dirname = None
                    self._real_download_path = None
            self._refresh_stub_button()
            if announce:
                if self.stub_enabled:
                    self.append_terminal_output(
                        "*** TEST STUB ENABLED *** downloads are FAKE - mode: "
                        + str(self.stub_mode)
                        + (", failing first " + str(self.stub_fail_times)
                           if int(self.stub_fail_times or 0) > 0 else "")
                        + "\n    cache -> ysa_cache_dev   output -> selftest_output"
                        + "   (your real cache and library are untouched)\n",
                        "warning")
                else:
                    self.append_terminal_output(
                        "Test stub disabled - using the real yt-dlp: "
                        + str(self.ytdlp_path) + "\n    cache -> "
                        + str(getattr(self, 'cache_dirname', 'ysa_cache'))
                        + "   output -> " + str(self.download_path) + "\n",
                        "success")
        except Exception as e:
            print('stub state error: ' + str(e))

    def _refresh_stub_button(self):
        try:
            if not hasattr(self, 'stub_btn') or not self.stub_btn.winfo_exists():
                return
            if getattr(self, 'stub_enabled', False):
                # Loud on purpose: forgetting the stub is on and then
                # debugging a "broken" 1.8 MB download is the real hazard.
                self.stub_btn.config(text="\U0001f9ea STUB: " + str(self.stub_mode),
                                     style='Stub.TButton')
            else:
                self.stub_btn.config(text="\U0001f9ea Stub", style='TButton')
        except Exception:
            pass

    def _show_stub_menu(self):
        try:
            _p = self._stub_path()
            m = tk.Menu(self.root, tearoff=0)
            if not _p:
                m.add_command(label="ysa_fake_ytdlp.exe / .py not found beside the app",
                              state='disabled')
                m.add_separator()
                m.add_command(label="(build it with the GitHub workflow, or copy the .py here)",
                              state='disabled')
            else:
                self._stub_on_var = tk.BooleanVar(value=bool(self.stub_enabled))
                m.add_checkbutton(label="Use fake yt-dlp  (" + os.path.basename(_p) + ")",
                                  variable=self._stub_on_var,
                                  command=self._toggle_stub)
                m.add_separator()
                self._stub_mode_var = tk.StringVar(value=str(self.stub_mode))
                for _mode in self.STUB_MODES:
                    m.add_radiobutton(label=_mode, value=_mode,
                                      variable=self._stub_mode_var,
                                      command=self._set_stub_mode)
                m.add_separator()
                _sub = tk.Menu(m, tearoff=0)
                self._stub_fail_var = tk.IntVar(value=int(self.stub_fail_times or 0))
                for _n in (0, 1, 2, 3, 5):
                    _sub.add_radiobutton(
                        label=("off" if _n == 0 else "fail " + str(_n) + ", then succeed"),
                        value=_n, variable=self._stub_fail_var,
                        command=self._set_stub_fail)
                m.add_cascade(label="Retry behaviour", menu=_sub)
                m.add_separator()
                m.add_command(label="Real yt-dlp: " + str(self._real_ytdlp_path
                                                         or self.ytdlp_path),
                              state='disabled')
            _x = self.stub_btn.winfo_rootx()
            _y = self.stub_btn.winfo_rooty() + self.stub_btn.winfo_height()
            m.tk_popup(_x, _y)
            try:
                m.grab_release()
            except Exception:
                pass
        except Exception as e:
            print('stub menu error: ' + str(e))

    def _toggle_stub(self):
        self.stub_enabled = bool(self._stub_on_var.get())
        self._apply_stub_state()
        self._save_devtest_state()

    def _set_stub_mode(self):
        self.stub_mode = str(self._stub_mode_var.get())
        self._apply_stub_state()
        self._save_devtest_state()

    def _set_stub_fail(self):
        self.stub_fail_times = int(self._stub_fail_var.get())
        self._apply_stub_state()
        self._save_devtest_state()
    # === END DEV TOOLS ===

    def _ytdlp_head(self):
        """The leading element(s) of a yt-dlp command line.

        Normally just the executable. If the resolved path is a .py - which
        happens when the developer stub is used while running from source -
        the interpreter has to come first, because Windows cannot execute a
        .py file as a subprocess and a .cmd shim needs cmd.exe, which may be
        blocked by policy.
        """
        p = str(self.ytdlp_path or '')
        if p.lower().endswith('.py'):
            return [sys.executable, p]
        return [p]

    def run_ytdlp_command(self, args, capture_output=True, timeout=30):
        """Run yt-dlp command with the executable"""
        cmd = self._ytdlp_head() + args
        try:
            result = subprocess.run(cmd, capture_output=capture_output, text=True, encoding='utf-8', errors='replace', timeout=timeout,
                                           creationflags=CREATE_NO_WINDOW)
            return result
        except subprocess.TimeoutExpired:
            raise Exception(f"yt-dlp command timed out after {timeout} seconds")
        except Exception as e:
            raise Exception(f"Failed to run yt-dlp: {str(e)}")
        finally:
            # The info cascade runs through here, not through the terminal
            # runner - without this its per-invocation cookie copies were
            # never reclaimed and piled up in <cache>/tmp all session.
            # cookie copies are reclaimed only by the process-guarded reap
            pass
    

    # ── bgutil PO Token provider ────────────────────────────────────────────

    @staticmethod
    def _find_node_exe():
        """Find node.exe on Windows or Unix. Returns full path or bare name."""
        if sys.platform != 'win32':
            return 'node'
        import shutil
        found = shutil.which('node.exe') or shutil.which('node')
        if found:
            return found
        pf   = os.environ.get('ProgramFiles',      r'C:\Program Files')
        pf86 = os.environ.get('ProgramFiles(x86)', r'C:\Program Files (x86)')
        lad  = os.environ.get('LOCALAPPDATA', '')
        apd  = os.environ.get('APPDATA', '')
        for base in [pf, pf86, lad, apd]:
            if base:
                c = os.path.join(base, 'nodejs', 'node.exe')
                if os.path.isfile(c):
                    return c
        nvm_home = os.environ.get('NVM_HOME', '')
        if nvm_home and os.path.isdir(nvm_home):
            for subdir in os.listdir(nvm_home):
                c = os.path.join(nvm_home, subdir, 'node.exe')
                if os.path.isfile(c):
                    return c
        return 'node'

    @staticmethod
    def _get_npm_script(node_exe):
        """Return path to npm-cli.js bundled with Node.js.

        Running  node npm-cli.js ci  instead of  npm.cmd ci  avoids invoking
        cmd.exe, which is blocked on systems where Command Prompt is disabled
        by Group Policy (causes WinError 5 on any .cmd file execution).
        """
        node_dir = os.path.dirname(os.path.abspath(node_exe))
        candidate = os.path.join(node_dir, 'node_modules', 'npm', 'bin', 'npm-cli.js')
        if os.path.isfile(candidate):
            return candidate
        for base in [
            os.environ.get('ProgramFiles', r'C:\Program Files'),
            os.environ.get('ProgramFiles(x86)', r'C:\Program Files (x86)'),
            os.environ.get('APPDATA', ''),
        ]:
            if base:
                c = os.path.join(base, 'nodejs', 'node_modules', 'npm', 'bin', 'npm-cli.js')
                if os.path.isfile(c):
                    return c
        return None

    def _bgutil_check_server(self):
        """Return True if the bgutil HTTP server is reachable at self.bgutil_server_url.

        Also reads the 'version' field from the /ping JSON response (bgutil 1.x+)
        and stores it in self._bgutil_server_version so _bgutil_refresh_status()
        can detect major-version mismatches before yt-dlp silently rejects tokens.
        """
        try:
            import urllib.request as _ur
            import json as _json
            url = (getattr(self, 'bgutil_server_url', '') or 'http://127.0.0.1:4416').rstrip('/')
            req = _ur.Request(url + '/ping', method='GET')
            with _ur.urlopen(req, timeout=0.6) as resp:
                if resp.status != 200:
                    self._bgutil_server_version = None
                    return False
                try:
                    data = _json.loads(resp.read())
                    self._bgutil_server_version = data.get('version', '')
                except Exception:
                    self._bgutil_server_version = ''  # old server, no JSON body
                return True
        except Exception:
            self._bgutil_server_version = None
            try:
                # Some bgutil versions have no /ping - just check TCP connection
                import socket as _sock
                host = '127.0.0.1'
                port = 4416
                url = getattr(self, 'bgutil_server_url', 'http://127.0.0.1:4416')
                if ':' in url.split('//')[-1]:
                    _h, _p = url.split('//')[-1].rsplit(':', 1)
                    host = _h.strip('/')
                    port = int(_p.strip('/'))
                s = _sock.create_connection((host, port), timeout=0.6)
                s.close()
                return True
            except Exception:
                return False

    def _bgutil_check_plugin(self):
        """Return True if all three bgutil plugin .py files are present next to yt-dlp.exe."""
        extractor_dir = self._bgutil_plugin_extractor_dir()
        for fname in _BGUTIL_PLUGIN_FILES:
            if not os.path.isfile(os.path.join(extractor_dir, fname)):
                return False
        return True

    def _bgutil_plugin_extractor_dir(self):
        """Return the path where plugin .py files should live."""
        if getattr(sys, 'frozen', False):
            base = os.path.dirname(sys.executable)
        else:
            base = SCRIPT_DIR
        return os.path.join(base, 'yt-dlp-plugins',
                            'bgutil-ytdlp-pot-provider', 'yt_dlp_plugins', 'extractor')

    def _bgutil_install_plugin(self):
        """Write the embedded plugin files to the yt-dlp-plugins directory.
        Returns (True, '') on success or (False, error_message) on failure."""
        extractor_dir = self._bgutil_plugin_extractor_dir()
        try:
            os.makedirs(extractor_dir, exist_ok=True)
            # yt-dlp requires yt_dlp_plugins (and its sub-packages) to be
            # implicit namespace packages — i.e. directories WITHOUT __init__.py.
            # A previous version of YSA incorrectly created one, which prevented
            # yt-dlp from merging the plugin namespace with its own internal one,
            # causing "Plugin directories: none" in --verbose output.
            # Clean up any stale __init__.py files so plugins are discovered.
            for bad_init in [
                os.path.join(os.path.dirname(extractor_dir), '__init__.py'),
                os.path.join(extractor_dir, '__init__.py'),
            ]:
                if os.path.exists(bad_init):
                    try:
                        os.remove(bad_init)
                    except Exception:
                        pass
            for fname, content in _BGUTIL_PLUGIN_FILES.items():
                dest = os.path.join(extractor_dir, fname)
                with open(dest, 'w', encoding='utf-8') as f:
                    f.write(content)
            return True, extractor_dir
        except Exception as e:
            return False, str(e)

    def _bgutil_bundled_dir(self):
        """Return path to the ncc-bundled bgutil server directory.

        Checks multiple locations so the server is found both when running as
        a PyInstaller exe and when running directly from the .py source:

          1. User-configured bgutil_server_path (from Settings, persisted)
          2. PyInstaller _MEIPASS/bgutil_bundle  (frozen exe)
          3. SCRIPT_DIR/_internal/bgutil_bundle  (onedir exe structure / dev)
          4. SCRIPT_DIR/bgutil_bundle            (bundle placed next to script)
          5. SCRIPT_DIR/bgutil_extracted          (previously extracted by YSA)

        The bundle must contain build/main.js to be considered valid.
        """
        candidates = []
        # User-configured path takes priority
        _user_path = getattr(self, 'bgutil_server_path', '') or ''
        if _user_path:
            candidates.append(_user_path)
        if getattr(sys, 'frozen', False):
            meipass = getattr(sys, '_MEIPASS', '')
            if meipass:
                candidates.append(os.path.join(meipass, 'bgutil_bundle'))
        # Also check paths relative to SCRIPT_DIR (works for both frozen and source)
        candidates.append(os.path.join(SCRIPT_DIR, '_internal', 'bgutil_bundle'))
        candidates.append(os.path.join(SCRIPT_DIR, 'bgutil_bundle'))
        candidates.append(os.path.join(SCRIPT_DIR, 'bgutil_extracted'))
        for candidate in candidates:
            if (os.path.isdir(candidate)
                    and os.path.isfile(os.path.join(candidate, 'build', 'main.js'))):
                return candidate
        return None

    def _bgutil_extract_bundle(self):
        """Ensure the bgutil server bundle is at a persistent, runnable location.

        If the bundle lives inside PyInstaller's _MEIPASS temp folder it must
        be copied to SCRIPT_DIR/bgutil_extracted/ so it survives across launches.
        If the bundle is already at a persistent location (e.g. SCRIPT_DIR/
        _internal/bgutil_bundle when running from source), just return the
        main.js path directly — no copy needed.

        Returns the path to build/main.js, or None on failure.
        """
        bundled_dir = self._bgutil_bundled_dir()
        if not bundled_dir:
            return None

        main_js = os.path.join(bundled_dir, 'build', 'main.js')

        # If the bundle is NOT inside the PyInstaller temp dir, it is already
        # persistent on disk — run from it directly, no extraction needed.
        meipass = getattr(sys, '_MEIPASS', '') or ''
        if not meipass or not bundled_dir.startswith(meipass):
            return main_js

        # ── Bundle is inside _MEIPASS: extract to a persistent location ──────
        dest_dir = os.path.join(SCRIPT_DIR, 'bgutil_extracted')
        dest_js  = os.path.join(dest_dir, 'build', 'main.js')
        ver_file = os.path.join(dest_dir, '.bgutil_version')
        version  = _BGUTIL_PLUGIN_VERSION  # reuse the plugin version as a build tag

        # Skip if already extracted at same version
        if os.path.isfile(dest_js) and os.path.isfile(ver_file):
            try:
                with open(ver_file, 'r') as _vf:
                    if _vf.read().strip() == version:
                        return dest_js
            except Exception:
                pass

        try:
            import shutil as _shutil
            # Remove stale extraction before re-copying
            if os.path.exists(dest_dir):
                _shutil.rmtree(dest_dir)
            # Copy entire bundle directory tree (build/ + node_modules/ + package.json)
            self.append_terminal_output(
                'bgutil: extracting bundled server (first run only)...\n', 'info')
            _shutil.copytree(bundled_dir, dest_dir)
            with open(ver_file, 'w') as vf:
                vf.write(version)
            self.append_terminal_output(
                'bgutil: extracted bundled server to ' + dest_dir + '\n', 'info')
            return dest_js
        except Exception as e:
            self.append_terminal_output(
                'bgutil: failed to extract bundled server: ' + str(e) + '\n', 'warning')
            return None

    def _bgutil_start_server(self):
        """Try to start the bgutil server.  Prefers the ncc-bundled server baked into
        the exe over a manually configured server path, so no npm/npx is needed at runtime.
        Returns True if the server started successfully."""
        node_exe = self._find_node_exe()

        # ── Prefer ncc-bundled server (baked into exe at build time) ──────
        main_js = self._bgutil_extract_bundle()
        if main_js:
            # cwd must be parent of build/ so node finds node_modules/
            run_dir = os.path.dirname(os.path.dirname(main_js))
            self.append_terminal_output(
                'bgutil: using bundled server (pre-compiled, no npm needed).\n', 'info')
        else:
            # ── Fall back to manually configured server path ────────────
            server_path = getattr(self, 'bgutil_server_path', '') or ''
            if not server_path or not os.path.isdir(server_path):
                self.append_terminal_output(
                    'bgutil: no bundled server and no server path configured.\n', 'warning')
                return False
            main_js = os.path.join(server_path, 'build', 'main.js')
            run_dir = server_path
            if not os.path.isfile(main_js):
                self.append_terminal_output(
                    'bgutil: build\\main.js not found.\n'
                    'bgutil: Build the exe via GitHub Actions to get the bundled server.\n',
                    'warning')
                return False

        try:
            proc = subprocess.Popen(
                [node_exe, main_js],
                cwd=run_dir,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                creationflags=CREATE_NO_WINDOW)
            self._bgutil_process = proc
            time.sleep(2)
            if self._bgutil_check_server():
                self.append_terminal_output(
                    'bgutil: server started (PID ' + str(proc.pid) + ').\n', 'success')
                self._bgutil_running = True
                return True
            else:
                self.append_terminal_output(
                    'bgutil: server launched but not reachable.\n'
                    'bgutil: Is Node.js 20+ installed? (nodejs.org)\n', 'warning')
                return False
        except FileNotFoundError:
            self.append_terminal_output(
                'bgutil: Node.js not found - install from nodejs.org\n', 'warning')
            return False
        except Exception as e:
            self.append_terminal_output('bgutil: start failed: ' + str(e) + '\n', 'warning')
            return False

    def _bgutil_stop_server(self):
        """Stop the bgutil server using multiple strategies.

        Tries in order (most reliable first):
          1. Stored Popen handle → proc.terminate() / proc.kill()
             (works without admin because YSA owns the child process)
          2. Find PID by port (netstat) → os.kill(SIGTERM)
          3. Find node.exe by command line (wmic) → taskkill /PID
        Returns True if a process was killed.
        """
        killed = False

        # ── Strategy 1: stored Popen handle ──────────────────────────────────
        proc = getattr(self, '_bgutil_process', None)
        if proc is not None:
            try:
                proc.terminate()
                try:
                    proc.wait(timeout=3)
                except subprocess.TimeoutExpired:
                    proc.kill()
                    proc.wait(timeout=2)
                killed = True
                self.append_terminal_output(
                    'bgutil: server stopped (PID ' + str(proc.pid) + ').\n', 'success')
            except Exception as e:
                self.append_terminal_output(
                    'bgutil: terminate via handle failed: ' + str(e) + '\n', 'warning')
            self._bgutil_process = None

        # ── Strategy 2: find PID by listening port (netstat) ─────────────────
        if not killed:
            _port_pid = self._bgutil_find_pid_by_port()
            if _port_pid:
                try:
                    os.kill(_port_pid, 9)  # SIGKILL on Windows = TerminateProcess
                    killed = True
                    self.append_terminal_output(
                        'bgutil: killed process on port (PID ' + str(_port_pid) + ').\n', 'success')
                except OSError as e:
                    self.append_terminal_output(
                        'bgutil: os.kill failed for PID ' + str(_port_pid) + ': ' + str(e) + '\n', 'warning')

        # ── Strategy 3: find node.exe running main.js via wmic ───────────────
        if not killed:
            _wmic_pid = self._bgutil_find_pid_by_cmdline()
            if _wmic_pid:
                try:
                    os.kill(_wmic_pid, 9)
                    killed = True
                    self.append_terminal_output(
                        'bgutil: killed node process (PID ' + str(_wmic_pid) + ').\n', 'success')
                except OSError as e:
                    # Last resort: taskkill without /T (avoids Access Denied from tree kill)
                    try:
                        subprocess.run(
                            ['taskkill', '/F', '/PID', str(_wmic_pid)],
                            capture_output=True, creationflags=CREATE_NO_WINDOW)
                        killed = True
                        self.append_terminal_output(
                            'bgutil: taskkill PID ' + str(_wmic_pid) + '.\n', 'success')
                    except Exception as e2:
                        self.append_terminal_output(
                            'bgutil: all stop methods failed: ' + str(e2) + '\n', 'warning')

        self._bgutil_running = False
        if not killed:
            self.append_terminal_output(
                'bgutil: no running server found.\n', 'info')
        return killed

    def _bgutil_find_pid_by_port(self):
        """Find PID listening on the bgutil port via netstat. Returns int or None."""
        try:
            url = getattr(self, 'bgutil_server_url', 'http://127.0.0.1:4416') or 'http://127.0.0.1:4416'
            port = url.rstrip('/').rsplit(':', 1)[-1].split('/')[0]
            r = subprocess.run(
                ['netstat', '-ano'],
                capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                creationflags=CREATE_NO_WINDOW)
            for line in (r.stdout or '').splitlines():
                if ':' + port + ' ' in line and 'LISTENING' in line:
                    parts = line.split()
                    if parts:
                        try:
                            return int(parts[-1])
                        except ValueError:
                            pass
        except Exception:
            pass
        return None

    def _bgutil_find_pid_by_cmdline(self):
        """Find a node.exe process running main.js (bgutil) via wmic. Returns int or None."""
        try:
            r = subprocess.run(
                ['wmic', 'process', 'where',
                 "Name='node.exe' and CommandLine like '%main.js%'",
                 'get', 'ProcessId', '/format:list'],
                capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                creationflags=CREATE_NO_WINDOW)
            for line in (r.stdout or '').splitlines():
                line = line.strip()
                if line.startswith('ProcessId='):
                    try:
                        return int(line.split('=')[1])
                    except ValueError:
                        pass
        except Exception:
            pass
        return None

    def _bgutil_refresh_status(self, update_ui=True):
        """Check server + plugin, update self._bgutil_running, optionally refresh UI label.

        Also detects major-version mismatches between the running server and the
        embedded plugin (1.3.1).  A mismatch means yt-dlp's plugin will call
        /ping, read the version, and raise PoTokenProviderRejectedRequest - so no
        PO token is ever generated even though both indicators appear green.
        """
        self._bgutil_running = self._bgutil_check_server()
        if update_ui and hasattr(self, '_bgutil_status_label'):
            plugin_ok = self._bgutil_check_plugin()
            server_vsn = getattr(self, '_bgutil_server_version', None)

            # Detect major-version mismatch: plugin will reject the server at
            # token-request time, giving a silent failure visible only in yt-dlp --verbose.
            vsn_mismatch = False
            if self._bgutil_running and server_vsn:
                plugin_major = _BGUTIL_PLUGIN_VERSION.split('.')[0]
                server_major = server_vsn.split('.')[0]
                if server_major != plugin_major:
                    vsn_mismatch = True

            if self._bgutil_running and plugin_ok and vsn_mismatch:
                txt = ('Server: v' + server_vsn +
                       '  Plugin: v' + _BGUTIL_PLUGIN_VERSION +
                       '  VERSION MISMATCH - tokens will fail')
                col = 'red'
            elif self._bgutil_running and plugin_ok:
                vsn_str = ('  v' + server_vsn) if server_vsn else ''
                txt = 'Server: RUNNING' + vsn_str + '   Plugin: INSTALLED'
                col = 'green'
            elif self._bgutil_running and not plugin_ok:
                txt = 'Server: RUNNING   Plugin: NOT FOUND'
                col = 'orange'
            elif not self._bgutil_running and plugin_ok:
                txt = 'Server: STOPPED   Plugin: INSTALLED'
                col = 'orange'
            else:
                txt = 'Server: STOPPED   Plugin: NOT FOUND'
                col = 'gray'
            try:
                self._bgutil_status_label.config(text=txt, foreground=col)
            except Exception:
                pass
        return self._bgutil_running

    def get_bgutil_extractor_args(self):
        """Return --extractor-args for bgutil if server is running and URL is non-default.
        When server is at default URL, no args needed - yt-dlp plugin uses it automatically."""
        if not getattr(self, '_bgutil_running', False):
            return []
        url = getattr(self, 'bgutil_server_url', 'http://127.0.0.1:4416') or 'http://127.0.0.1:4416'
        if url.rstrip('/') == 'http://127.0.0.1:4416':
            return []  # plugin default - no arg needed
        return ['--extractor-args', 'youtubepot-bgutilhttp:base_url=' + url]

    def get_bgutil_plugin_dirs_args(self):
        """Return --plugin-dirs pointing at the plugin search directory.

        --plugin-dirs tells yt-dlp where to SEARCH for plugin packages.
        yt-dlp then looks inside that directory for sub-folders that contain
        a yt_dlp_plugins/ namespace package.  So the value must be the
        directory that *contains* the package folder — NOT the package
        folder itself.

        Directory layout written by _bgutil_install_plugin():

            {base}/yt-dlp-plugins/                                   ← search dir (--plugin-dirs value)
              bgutil-ytdlp-pot-provider/                             ← package dir (yt-dlp finds this)
                yt_dlp_plugins/                                      ← namespace package (no __init__.py)
                  extractor/                                         ← namespace package (no __init__.py)
                    getpot_bgutil.py
                    getpot_bgutil_http.py
        """
        if not self._bgutil_check_plugin():
            return []
        extractor_dir = self._bgutil_plugin_extractor_dir()
        # extractor_dir = {base}/yt-dlp-plugins/bgutil-ytdlp-pot-provider/yt_dlp_plugins/extractor
        package_dir = os.path.dirname(os.path.dirname(extractor_dir))
        # package_dir  = {base}/yt-dlp-plugins/bgutil-ytdlp-pot-provider
        search_dir = os.path.dirname(package_dir)
        # search_dir   = {base}/yt-dlp-plugins

        # ── One-time cleanup: remove stale __init__.py that breaks the
        #    yt_dlp_plugins namespace package.  A previous version of YSA
        #    created this file, which converts the namespace package into a
        #    regular package and prevents yt-dlp from discovering plugins.
        #    Run once per session, not on every call.
        if not getattr(self, '_plugin_init_cleaned', False):
            self._plugin_init_cleaned = True
            for bad_init in [
                os.path.join(package_dir, 'yt_dlp_plugins', '__init__.py'),
                os.path.join(extractor_dir, '__init__.py'),
            ]:
                if os.path.exists(bad_init):
                    try:
                        os.remove(bad_init)
                    except Exception:
                        pass

        return ['--plugin-dirs', search_dir]

    def get_jsruntime_args(self):
        """Return --js-runtimes args so yt-dlp can use Node.js for JS challenges.

        Since yt-dlp 2025.11.12, an external JavaScript runtime is required for
        full YouTube support.  Only deno is enabled by default; node must be
        explicitly enabled via --js-runtimes.  YSA already requires Node.js for
        the bgutil HTTP server, so we reuse _find_node_exe() to locate it and
        pass the path to yt-dlp.
        """
        node_exe = self._find_node_exe()
        if not node_exe:
            return []
        if node_exe == 'node':
            # Bare name - let yt-dlp search PATH
            return ['--js-runtimes', 'node']
        # Explicit path so yt-dlp finds node even if it is not on PATH
        return ['--js-runtimes', 'node:' + node_exe]

    def _diagnose_ytdlp_environment(self):
        """Run a fast yt-dlp --verbose probe and display whether the plugin
        directory and JS runtime are actually being recognised by yt-dlp.

        This catches the common case where YSA's own file-existence check says
        'Plugin INSTALLED' but yt-dlp silently ignores the directory (e.g.
        because a stale __init__.py converts the namespace package into a
        regular package).

        Uses a dummy URL (ysa://probe) that triggers YoutubeDL initialisation
        (which prints the debug lines) but fails immediately with 'Unsupported
        URL' - no network call, very fast.  --version cannot be used here
        because it exits before YoutubeDL is instantiated.
        """
        try:
            probe_args = ['--verbose', '--dump-json', '--no-check-formats']
            probe_args += self.get_bgutil_plugin_dirs_args()
            probe_args += self.get_jsruntime_args()
            probe_args.append('ysa://probe')
            cmd = self._ytdlp_head() + probe_args
            result = subprocess.run(
                cmd, capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                creationflags=CREATE_NO_WINDOW)
            stderr = result.stderr or ''

            # Parse key diagnostic lines from yt-dlp verbose output
            plugin_line = ''
            jsrt_line = ''
            for line in stderr.splitlines():
                if 'Plugin directories:' in line:
                    plugin_line = line.split('Plugin directories:')[-1].strip()
                elif 'JS runtimes:' in line:
                    jsrt_line = line.split('JS runtimes:')[-1].strip()

            # Display results - only if we successfully parsed the debug output
            if plugin_line:
                if plugin_line.lower() != 'none':
                    self.append_terminal_output(
                        'yt-dlp verify: Plugin dirs OK\n', 'success')
                else:
                    self.append_terminal_output(
                        'yt-dlp verify: Plugin dirs = NONE '
                        '(yt-dlp cannot see the plugin!)\n'
                        '  Try: Settings > bgutil > Install Plugin, '
                        'or manually delete any __init__.py\n'
                        '  inside yt-dlp-plugins/.../yt_dlp_plugins/\n',
                        'error')

            if jsrt_line:
                if 'none' not in jsrt_line.lower():
                    self.append_terminal_output(
                        'yt-dlp verify: JS runtime OK (' + jsrt_line + ')\n',
                        'success')
                else:
                    self.append_terminal_output(
                        'yt-dlp verify: JS runtime = NONE '
                        '(install Node.js 20+ or Deno)\n', 'warning')
        except Exception:
            pass  # non-critical diagnostic - don't block startup

    def get_ytdlp_dns_args(self):
        """Return extra yt-dlp args for DNS proxy, cookies, bgutil, and JS runtime.
        Combines all so every download path stays in sync with a single call."""
        result = []
        if getattr(self, '_m_dns', False):
            proxy = get_proxy_url()
            if proxy:
                result += ['--proxy', proxy]
        result += self.get_ytdlp_cookies_args()
        result += self.get_bgutil_extractor_args()
        result += self.get_bgutil_plugin_dirs_args()
        result += self.get_jsruntime_args()
        return result

    def _cookies_copy_for_invocation(self, master_path):
        """Return a per-invocation throwaway copy of a cookies file.

        yt-dlp ALWAYS writes the cookie jar back to the --cookies file on
        exit - verified against 2026.06.09: the flag is documented as the
        file to 'read cookies from and dump cookie jar in', and there is no
        read-only mode. With several yt-dlp processes running at once
        (video+audio legs, pre-cache slots, info probes) all pointed at one
        master file, two exiting simultaneously collide on that write and
        one dies with PermissionError - the PYI-8728/12108 crashes in the
        field logs, which then poisoned retries into 416 loops.

        Every invocation gets its own copy in <ysa_cache>/tmp: rotated
        cookies land in the throwaway and the master is never opened for
        write by anyone. Falls back to the master path if copying fails."""
        try:
            # Reap BEFORE making the new copy. Reaping afterwards deleted the
            # copy that had just been created: the yt-dlp process it belongs
            # to has not spawned yet, so the "is anything running?" probe
            # answers no and every copy looks dead. Field symptom was
            # 'Reclaimed N finished cookie copies' immediately followed by
            # FileNotFoundError on the copy for the command about to run.
            self._reap_cookie_copies()
            _dst = os.path.join(self._make_temp_dir('ysa_ck_'), 'cookies.txt')
            shutil.copy2(master_path, _dst)
            return _dst
        except Exception:
            return master_path

    def _any_ytdlp_running(self):
        """True if any yt-dlp process is alive - or if we cannot tell.

        Deliberately fails CLOSED: any error, any unknown platform, any
        ambiguity answers True, because the cost of a wrong 'no' is deleting
        a cookie file out from under a running download.
        """
        try:
            # normalise separators so the image name is correct however
            # the path was written (and so this is testable off-Windows)
            _img = os.path.basename(
                str(self.ytdlp_path or 'yt-dlp.exe').replace('\\', '/'))
            if sys.platform == 'win32':
                _r = subprocess.run(
                    ['tasklist', '/FI', 'IMAGENAME eq ' + _img, '/NH'],
                    capture_output=True, text=True, encoding='utf-8',
                    errors='replace', timeout=10,
                    creationflags=CREATE_NO_WINDOW)
                if _r.returncode != 0:
                    return True
                return _img.lower() in (_r.stdout or '').lower()
            _r = subprocess.run(['pgrep', '-f', _img], capture_output=True,
                                text=True, encoding='utf-8', errors='replace',
                                timeout=10)
            return _r.returncode == 0
        except Exception:
            return True

    def _reap_ytdlp_meipass(self):
        """Remove yt-dlp's abandoned PyInstaller extraction folders.

        yt-dlp.exe is a onefile build: it unpacks itself to %TEMP%\\_MEInnnnn
        on every run and removes it on exit - unless it crashes, which is
        exactly what the 416/cookie failures cause. They accumulate at ~25 MB
        each.

        Deliberately narrow: _MEI folders belong to ANY PyInstaller onefile
        program, so deleting one owned by another running application would
        break it. Only folders containing yt-dlp's own marker are touched,
        and only while no yt-dlp process is alive.
        """
        try:
            base = tempfile.gettempdir()
            if not os.path.isdir(base):
                return 0
            cand = []
            for d in os.listdir(base):
                if not d.startswith('_MEI'):
                    continue
                p = os.path.join(base, d)
                if not os.path.isdir(p):
                    continue
                try:
                    names = set(os.listdir(p))
                except Exception:
                    continue
                # provably yt-dlp's: its embedded JS runtime package
                if 'yt_dlp_ejs' in names or 'yt_dlp' in names:
                    cand.append(p)
            if not cand or self._any_ytdlp_running():
                return 0
            _n = 0
            for p in cand:
                shutil.rmtree(p, ignore_errors=True)
                if not os.path.isdir(p):
                    _n += 1
            return _n
        except Exception:
            return 0

    def _reap_cookie_copies(self, threshold=25):
        """Remove throwaway cookie folders, but ONLY when nothing can be using them.

        An earlier version kept the newest N folders and deleted the rest on
        every new copy. That assumed at most a handful of concurrent yt-dlp
        processes; a real batch run (queue + four pre-cache slots + clipboard
        analyses) blows past that, and a LONG download's folder ages out of
        the window while still in use. The result was
        'FileNotFoundError: ...ysa_ck_XXXX/cookies.txt' mid-run - recoverable,
        because the retry logic caught it, but self-inflicted.

        Deleting on a timer is unsafe for the same reason, so the only sound
        rule is to ask the OS: if no yt-dlp process exists, every copy is
        dead and all of them can go. If one exists, nothing is touched.
        """
        # Only one reaper at a time: two threads both passed the idle check
        # and both deleted the same set ("Reclaimed 27..." printed twice).
        if not self._ck_reap_lock.acquire(blocking=False):
            return
        try:
            base = getattr(self, 'ysa_tmp_dir', None)
            if not base or not os.path.isdir(base):
                return
            dirs = [os.path.join(base, d) for d in os.listdir(base)
                    if d.startswith('ysa_ck_')]
            dirs = [d for d in dirs if os.path.isdir(d)]
            if len(dirs) < threshold:
                return
            # A copy younger than this may belong to a command that has been
            # built but whose process has not started yet - invisible to the
            # process probe. Never touch those.
            _now = time.time()
            dirs = [d for d in dirs
                    if (_now - os.path.getmtime(d)) > 120]
            if not dirs:
                return
            if self._any_ytdlp_running():
                return
            for _d in dirs:
                shutil.rmtree(_d, ignore_errors=True)
            self.append_terminal_output(
                'Reclaimed ' + str(len(dirs)) + ' finished cookie copies.\n',
                'cache')
        except Exception:
            pass
        finally:
            try:
                self._ck_reap_lock.release()
            except Exception:
                pass

    def _warn_pot_combo_once(self, combo_active):
        """One LOUD warning per episode of cookies-without-PoT.

        Sending logged-in cookies while no PO-token server answers is
        the traffic signature that gets ACCOUNTS flagged (SABR-only /
        360p): fully identifiable requests wearing the automation-shaped
        token-less fallback. It cost this project's account once.

        Fires on the first fetch of each such episode; any fetch that
        sees the combo absent (server up, or cookies off) re-arms it,
        so a server dying mid-session warns again exactly once.
        Concurrent analysis workers can race the flag - worst case the
        warning prints twice, never once per fetch (same trade as the
        cookie staleness gate).
        """
        if combo_active:
            if not getattr(self, '_pot_combo_warned', False):
                self._pot_combo_warned = True
                self.root.after(0, lambda: self.append_terminal_output(
                    'RISK: cookies are being sent WITHOUT the bgutil PO-token server.\n'
                    '      Logged-in + token-less is the pattern that gets accounts\n'
                    '      flagged (SABR / 360p-only). Start the server in Settings >\n'
                    '      bgutil, or turn Cookies off in the toolbar.\n', 'warning'))
        else:
            self._pot_combo_warned = False

    def get_ytdlp_cookies_args(self):
        """Return cookie args for yt-dlp.

        Priority order:
          1. cookies_file (Netscape .txt exported from incognito) - most reliable,
             works while Firefox is running, no SQLite lock issues.
          2. cookies_browser - fallback for other browsers via yt-dlp's built-in
             extractor (Firefox is unreliable while running due to WAL lock).

        Returns [] when neither is configured or when the toolbar Cookies
        toggle is unchecked.
        """
        # Quick-toggle in the toolbar lets user disable cookies without
        # removing the configured file/browser in Settings.
        if not getattr(self, '_m_cookies_on', True):
            return []
        # Priority 1: explicit cookie file
        cookie_file = getattr(self, 'cookies_file', '') or ''
        if cookie_file:
            if os.path.isfile(cookie_file):
                try:
                    _ck_mtime = os.path.getmtime(cookie_file)
                    age_days = (time.time() - _ck_mtime) / 86400
                    # Warn once per cookie-file VERSION, not per invocation:
                    # a queued session builds this arg list dozens of times
                    # and the repeated warning drowned the log. Re-exporting
                    # the file (new mtime) re-arms the warning. Workers can
                    # race here; the worst case is the warning printing
                    # twice instead of once, so no lock is taken.
                    if age_days > 7 and _ck_mtime != getattr(
                            self, '_ck_stale_warned_mtime', None):
                        self._ck_stale_warned_mtime = _ck_mtime
                        self.root.after(0, lambda d=int(age_days): self.append_terminal_output(
                            'Warning: cookies.txt is ' + str(d) + ' days old - '
                            'consider re-exporting from a fresh incognito session.\n', 'warning'))
                except Exception:
                    pass
                return ['--cookies', self._cookies_copy_for_invocation(cookie_file)]
            else:
                # File was configured but no longer exists - warn clearly
                self.root.after(0, lambda p=cookie_file: self.append_terminal_output(
                    'Warning: cookies.txt path is set but file not found: ' + p + '\n'
                    'Falling back to browser cookies. Re-select the file in Settings.\n',
                    'warning'))

        # Priority 2: browser cookie extraction
        browser = getattr(self, 'cookies_browser', 'none') or 'none'
        if browser and browser != 'none':
            if browser == 'firefox':
                # Firefox locks cookies.sqlite while running - try to copy and export first
                try:
                    exported = self._export_firefox_cookies_to_file()
                    if exported:
                        return ['--cookies', self._cookies_copy_for_invocation(exported)]
                    if not getattr(self, '_ff_export_warned', False):
                        self._ff_export_warned = True
                        self.append_terminal_output(
                            "Firefox cookie export failed - modern Firefox keeps"
                            " its cookie store locked/encrypted while running.\n"
                            "Use the 'cookies.txt' browser add-on instead:"
                            " open a private window, sign in to YouTube, export"
                            " cookies.txt, then point Settings > Cookies at that"
                            " file.\n", 'warning')
                except Exception:
                    pass
            return ['--cookies-from-browser', browser]

        return []

    def _export_firefox_cookies_to_file(self):
        """Find Firefox's cookies.sqlite, copy it (bypassing the WAL lock),
        export to Netscape cookie format using Python's sqlite3, save to a
        temp file, and return its path.  Returns None on any failure.

        The temp file is placed in self.yt_dlp_cache_dir (or system temp) and
        named ysa_ff_cookies.txt.  It is overwritten on each call so it stays
        fresh across multiple downloads in the same session.
        """
        import sqlite3 as _sqlite3
        import glob as _glob

        # Locate the Firefox profiles directory on Windows
        appdata = os.environ.get('APPDATA', '')
        if not appdata:
            return None
        profiles_root = os.path.join(appdata, 'Mozilla', 'Firefox', 'Profiles')
        if not os.path.isdir(profiles_root):
            return None

        # Pick the profile with the newest cookies.sqlite
        candidates = _glob.glob(os.path.join(profiles_root, '*', 'cookies.sqlite'))
        if not candidates:
            return None
        candidates.sort(key=lambda p: os.path.getmtime(p), reverse=True)
        src_db = candidates[0]
        src_dir = os.path.dirname(src_db)

        # Copy cookies.sqlite + WAL/SHM sidecar files to a temp dir so we can
        # open the copy even while Firefox holds a write lock on the original.
        tmp_dir = self._make_temp_dir('ysa_ffcookies_')
        tmp_db  = os.path.join(tmp_dir, 'cookies.sqlite')
        try:
            shutil.copy2(src_db, tmp_db)
            for ext in ('-wal', '-shm'):
                src_side = src_db + ext
                if os.path.exists(src_side):
                    shutil.copy2(src_side, tmp_db + ext)
        except Exception:
            shutil.rmtree(tmp_dir, ignore_errors=True)
            return None

        # Export to Netscape cookie format that yt-dlp understands
        # Keep this inside the app's own folder - falling back to the Windows
        # temp dir scattered cookie exports outside ysa_cache.
        self._ensure_cache_dirs()
        out_dir = (self.yt_dlp_cache_dir or getattr(self, 'ysa_tmp_dir', None)
                   or tempfile.gettempdir())
        out_path = os.path.join(out_dir, 'ysa_ff_cookies.txt')
        try:
            con = _sqlite3.connect('file:' + tmp_db + '?mode=ro&immutable=1',
                                   uri=True, timeout=3)
            con.row_factory = _sqlite3.Row
            cur = con.execute(
                'SELECT host, path, isSecure, expiry, name, value '
                'FROM moz_cookies WHERE host LIKE "%youtube%" '
                '   OR host LIKE "%google%"'
            )
            rows = cur.fetchall()
            con.close()

            with open(out_path, 'w', encoding='utf-8') as f:
                f.write('# Netscape HTTP Cookie File\n')
                for row in rows:
                    host    = row['host']
                    flag    = 'TRUE' if host.startswith('.') else 'FALSE'
                    path    = row['path']
                    secure  = 'TRUE' if row['isSecure'] else 'FALSE'
                    expiry  = str(row['expiry'])
                    name    = row['name']
                    value   = row['value']
                    f.write('\t'.join([host, flag, path, secure, expiry, name, value]) + '\n')

            return out_path if os.path.getsize(out_path) > 30 else None
        except Exception:
            return None
        finally:
            shutil.rmtree(tmp_dir, ignore_errors=True)

    def get_video_info(self, url):
        """Get video information using yt-dlp executable.

        Strategy: let yt-dlp's own client negotiation run first (it is
        updated by maintainers and handles PO-token enforcement better than
        any fixed client list we could hardcode), then fall back to specific
        clients only if the default logic fails.

        Attempt 1 - yt-dlp default behaviour + cookies, no extractor-args
            yt-dlp tries its own optimised client order.  This is the most
            likely to work because it reflects the current state of YouTube's
            enforcement, not our best guess from months ago.

        Attempt 2 - tv_downgraded + cookies
            The client yt-dlp itself pairs with logged-in cookies in current
            releases (2026); tv_embedded was removed from yt-dlp.

        Attempt 3 - android_vr + no cookies (no PO token per official docs)
            Android VR client; listed as not requiring a PO token and works
            without authentication for public content.

        Attempt 4 - web_embedded + no cookies
            No GVS PO token required per the PO Token Guide; limited to
            embeddable videos, so android_vr is tried first.

        Attempt 5 - yt-dlp default behaviour, no cookies
            Last resort: let yt-dlp choose the client without any auth.

        --no-check-formats is applied to every attempt so that yt-dlp does
        not pre-validate stream URLs (which generates false "Requested format
        is not available" errors when YouTube returns neutered URLs).
        """
        def _has_formats(result):
            if result.returncode != 0 or not result.stdout.strip():
                return False
            try:
                return bool(json.loads(result.stdout).get('formats'))
            except Exception:
                return False

        base_flags = ['--dump-json', '--no-warnings', '--no-check-formats']

        def _proxy_args():
            proxy = get_proxy_url()
            return ['--proxy', proxy] if proxy else []

        def _cache_args():
            return ['--cache-dir', self.yt_dlp_cache_dir] if self.yt_dlp_cache_dir else []

        def _cookie_args():
            return self.get_ytdlp_cookies_args()

        def _plugin_dirs_args():
            # Explicitly tell yt-dlp where to find the bgutil plugin package.
            # yt-dlp searches for plugins relative to its own executable, not YSA's
            # directory, so without this the plugin is invisible in the EXE build.
            return self.get_bgutil_plugin_dirs_args()

        def _jsruntime_args():
            # Tell yt-dlp to use Node.js for YouTube JS challenge solving.
            return self.get_jsruntime_args()

        # Show cookie status - distinguish cookie file from Firefox export
        _ck = self.get_ytdlp_cookies_args()
        if _ck:
            _cookie_path = _ck[1] if len(_ck) > 1 and _ck[0] == '--cookies' else ''
            _is_file = bool(_cookie_path and os.path.isfile(_cookie_path))
            _is_ff_export = bool(_cookie_path and 'ysa_ff_cookies' in _cookie_path)
            if _is_file and not _is_ff_export:
                _basename = os.path.basename(_cookie_path)
                self.root.after(0, lambda b=_basename: self.append_terminal_output(
                    'Cookies: using file ' + b + '\n', 'success'))
            elif _is_ff_export:
                self.root.after(0, lambda: self.append_terminal_output(
                    'Cookies: Firefox profile copied to temp file.\n', 'info'))
            else:
                _browser = _ck[1] if len(_ck) > 1 else '?'
                self.root.after(0, lambda b=_browser: self.append_terminal_output(
                    'Cookies: --cookies-from-browser ' + b + '\n', 'info'))
        else:
            self.root.after(0, lambda: self.append_terminal_output(
                'Cookies: none - add cookies.txt in Settings to avoid bot-check errors.\n', 'warning'))

        # When bgutil server is running + plugin installed: yt-dlp handles PO tokens
        # automatically. Use a simple single attempt - no client juggling needed.
        _bgutil_ok = self._bgutil_refresh_status(update_ui=True)

        _use_cascade = getattr(self, 'extended_client_cascade', True)
        if _bgutil_ok:
            self.root.after(0, lambda: self.append_terminal_output(
                'bgutil: PO token provider ACTIVE' +
                (' - extended cascade ON.' if _use_cascade else ' - single attempt.') + '\n', 'success'))
            self._warn_pot_combo_once(False)
            if _use_cascade:
                # Multiple clients: default web (PO token via bgutil) + no-PO-token clients as fallback
                attempts = [
                    # ── With cookies ─────────────────────────────────────────────
                    ('yt-dlp default + bgutil', [],                                                            True),
                    ('tv_downgraded + bgutil',  ['--extractor-args', 'youtube:player_client=tv_downgraded'],   True),
                    ('tv + bgutil',             ['--extractor-args', 'youtube:player_client=tv'],              True),
                    # ── Without cookies ──────────────────────────────────────────
                    ('yt-dlp default + bgutil', [],                                                            False),
                    ('web_embedded',            ['--extractor-args', 'youtube:player_client=web_embedded'],    False),
                    ('android_vr',              ['--extractor-args', 'youtube:player_client=android_vr'],      False),
                    ('tv_simply',               ['--extractor-args', 'youtube:player_client=tv_simply'],       False),
                ]
            else:
                # Truly single attempt - use cookies if available, otherwise no-cookies
                _ck_available = bool(_cookie_args())
                attempts = [
                    ('yt-dlp default + bgutil', [], _ck_available),
                ]
        else:
            self.root.after(0, lambda: self.append_terminal_output(
                'bgutil: not running - ' +
                ('extended client cascade.' if _use_cascade else 'single attempt (cascade OFF).') + '\n', 'info'))
            self._warn_pot_combo_once(bool(_ck))
            # Each entry: (label, extra_args, with_cookies)
            # Clients not requiring a GVS PO token per the yt-dlp PO Token
            # Guide (verified 2026-06 against yt-dlp 2026.06.09):
            #   android_vr, web_embedded (embeddable videos only)
            # tv_simply now REQUIRES a GVS token (useless without bgutil) and
            # tv_embedded was removed from yt-dlp entirely.
            if _use_cascade:
                attempts = [
                    # ── With cookies ─────────────────────────────────────────
                    ('yt-dlp default',  [],                                                            True),
                    ('tv_downgraded',   ['--extractor-args', 'youtube:player_client=tv_downgraded'],   True),
                    ('tv',              ['--extractor-args', 'youtube:player_client=tv'],              True),
                    # ── Without cookies ──────────────────────────────────────
                    ('android_vr',      ['--extractor-args', 'youtube:player_client=android_vr'],      False),
                    ('web_embedded',    ['--extractor-args', 'youtube:player_client=web_embedded'],    False),
                    ('tv',              ['--extractor-args', 'youtube:player_client=tv'],              False),
                    ('yt-dlp default',  [],                                                            False),
                ]
            else:
                _ck_available = bool(_cookie_args())
                attempts = [
                    ('yt-dlp default', [], _ck_available),
                ]

        last_result = None
        n_total = len(attempts)
        for attempt_num, (label, extra, with_cookies) in enumerate(attempts, 1):
            cookie_label = '+cookies' if with_cookies else 'no-cookies'
            self.root.after(0, lambda n=attempt_num, t=n_total, lb=label, cl=cookie_label:
                self.append_terminal_output(
                    'Info attempt ' + str(n) + '/' + str(t) + ': ' + lb +
                    ' (' + cl + ')...\n', 'info'))

            a = list(base_flags)
            a += extra
            a += _proxy_args()
            a += _plugin_dirs_args()
            a += _jsruntime_args()
            if with_cookies:
                a += _cookie_args()
            a += _cache_args()
            a.append(url)

            r = self.run_ytdlp_command(a)
            last_result = r
            if _has_formats(r):
                self.root.after(0, lambda n=attempt_num, lb=label:
                    self.append_terminal_output(
                        'Info OK on attempt ' + str(n) + ' (' + lb + ').\n', 'success'))
                _info = json.loads(r.stdout)
                self.root.after(0, lambda i=_info: self._log_stream_url_lifetime(i))
                return _info

            stderr = (r.stderr or '').strip()
            # If 'Requested format is not available', retry with explicit format
            # selector - yt-dlp's default selection can fail on some videos
            # even when valid formats exist (e.g. live streams, VP9-only videos).
            if 'Requested format is not available' in stderr and '-f' not in a:
                a2 = list(base_flags) + ['-f', 'bestvideo+bestaudio/best']
                a2 += extra + _proxy_args() + _plugin_dirs_args() + _jsruntime_args()
                if with_cookies:
                    a2 += _cookie_args()
                a2 += _cache_args()
                a2.append(url)
                r2 = self.run_ytdlp_command(a2)
                if _has_formats(r2):
                    self.root.after(0, lambda n=attempt_num, lb=label:
                        self.append_terminal_output(
                            'Info OK on attempt ' + str(n) + ' (' + lb + ', explicit format).\n', 'success'))
                    return json.loads(r2.stdout)
                last_result = r2
                stderr = (r2.stderr or stderr).strip()

            err_short = stderr.splitlines()[0] if stderr else 'no output'
            self.root.after(0, lambda e=err_short:
                self.append_terminal_output('  -> ' + e + '\n', 'warning'))

            # Stop immediately when the video is gone for good. Every client
            # gets the same answer, so the remaining attempts only burn
            # requests - noticeable on a playlist where several entries
            # belong to a terminated channel.
            _low = stderr.lower()
            _terminal = next((t for t in _YT_TERMINAL_ERRORS if t in _low), None)
            if _terminal:
                self.root.after(0, lambda:
                    self.append_terminal_output(
                        '  -> video is permanently unavailable - skipping the'
                        ' remaining ' + str(len(attempts) - attempt_num)
                        + ' attempt(s).\n', 'warning'))
                raise Exception('Video unavailable: ' + err_short)

        # All attempts failed - raise with the most informative error
        for r in ([last_result] if last_result else []):
            detail = (r.stderr or '').strip() or (r.stdout or '').strip()
            if detail:
                raise Exception('yt-dlp failed (code ' + str(r.returncode) + '):\n' + detail)
        raise Exception('yt-dlp returned no data. The video may be unavailable or blocked.')
    
    def setup_ui(self):
        """Set up the user interface"""
        # Main container
        main_frame = ttk.Frame(self.root, padding="10")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        
        # Configure grid weights
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main_frame.columnconfigure(1, weight=1)
        main_frame.rowconfigure(6, weight=1)
        main_frame.rowconfigure(9, weight=1, minsize=180)   # terminal floor:
        # a Notebook sizes to its tallest tab, so without this any new
        # tab can squeeze the terminal down to nothing.
        
        # Bind keyboard shortcuts
        self.root.bind('<Control-v>', lambda e: self.paste_and_analyze())
        self.root.bind('<Control-V>', lambda e: self.paste_and_analyze())
        
        # Title
        title_label = ttk.Label(main_frame, text="🎬 YouTube Stream Analyzer", 
                               font=('Arial', 16, 'bold'))
        title_label.grid(row=0, column=0, columnspan=3, pady=(0, 6))
        
        # URL Input Section
        url_frame = ttk.LabelFrame(main_frame, text="Video URL", padding="10")
        url_frame.grid(row=1, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 4))
        url_frame.columnconfigure(1, weight=1)
        
        ttk.Label(url_frame, text="YouTube URL:").grid(row=0, column=0, sticky=tk.W, padx=(0, 5))
        
        self.url_var = tk.StringVar()
        self.url_entry = ttk.Entry(url_frame, textvariable=self.url_var, width=60)
        self.url_entry.grid(row=0, column=1, sticky=(tk.W, tk.E), padx=(0, 5))
        self.url_entry.bind('<Return>', lambda e: self.paste_and_analyze() if not self.url_var.get().strip() else self.analyze_video())
        self.url_entry.bind('<Control-v>', self.on_paste_to_entry)
        self.url_entry.bind('<Button-3>', self.show_context_menu)  # Right-click menu
        
        self.paste_btn = ttk.Button(url_frame, text="Paste & Download", command=self.paste_and_analyze)
        self.paste_btn.grid(row=0, column=2, sticky=tk.W)

        self._batch_panel_visible = False
        self._batch_toggle_btn = ttk.Button(url_frame, text="Batch ▼",
                                            command=self._toggle_batch_panel)
        self._batch_toggle_btn.grid(row=0, column=3, sticky=tk.W, padx=(6, 0))

        # ── Row 1: Auto-Download Quality (left) + Clipboard watch (right) ──
        # Auto-download is an ON/OFF toggle (checkbox) + quality selector,
        # mirroring the "Watch clipboard" control.  "None" is no longer an option
        # in the quality list - the checkbox is the enable/disable mechanism.
        _aq_opts = ["2160p", "1440p", "1080p", "720p", "480p", "360p", "240p", "144p", "Premuxed"]
        _aq_enabled_init = bool(self.default_quality and self.default_quality != "None")
        _aq_quality_init = self.default_quality if (self.default_quality and self.default_quality != "None") else "1080p"
        self._aq_enabled_var = tk.BooleanVar(value=_aq_enabled_init)
        self._aq_var = tk.StringVar(value=_aq_quality_init)

        def _on_aq_toggle():
            if self._aq_enabled_var.get():
                self.default_quality = self._aq_var.get()
                _aq_combo.config(state='readonly')
                _aq_combo.config(style='TCombobox')
            else:
                self.default_quality = ""
                _aq_combo.config(state='disabled')
                _aq_combo.config(style='Disabled.TCombobox')
            # Persist immediately (synchronous): the debounced save is lost
            # if the app closes or crashes within its 500 ms window.
            self._save_config_now()

        def _on_aq_quality_change(event=None):
            if self._aq_enabled_var.get():
                self.default_quality = self._aq_var.get()
                self._save_config_now()

        ttk.Checkbutton(url_frame, text="Auto-Download:",
                        variable=self._aq_enabled_var,
                        command=_on_aq_toggle).grid(
            row=1, column=0, sticky=tk.W, padx=(0, 4), pady=(6, 0))
        _aq_combo = ttk.Combobox(url_frame, textvariable=self._aq_var,
                                 values=_aq_opts,
                                 state='readonly' if _aq_enabled_init else 'disabled',
                                 style='TCombobox' if _aq_enabled_init else 'Disabled.TCombobox',
                                 width=8)
        _aq_combo.grid(row=1, column=1, sticky=tk.W, pady=(6, 0))
        _aq_combo.bind('<<ComboboxSelected>>', _on_aq_quality_change)

        self._clipboard_watch_var = tk.BooleanVar(value=self.clipboard_watch)
        def _toggle_clipboard_watch():
            self.clipboard_watch = self._clipboard_watch_var.get()
            self._save_config()
            if self.clipboard_watch:
                self._start_clipboard_watch()
            else:
                self._clipboard_watch_active = False
        ttk.Checkbutton(url_frame, text="Watch clipboard for YouTube URLs",
                        variable=self._clipboard_watch_var,
                        command=_toggle_clipboard_watch).grid(
            row=1, column=2, columnspan=2, sticky=tk.E, pady=(6, 0))

        # ── Batch panel (hidden until toggled) ────────────────────────────
        self._batch_frame = ttk.Frame(url_frame)
        self._batch_frame.columnconfigure(0, weight=1)
        # Not gridded yet - shown on toggle

        ttk.Label(self._batch_frame,
                  text="Paste URLs below (one per line) or load from a .txt file:").grid(
            row=0, column=0, columnspan=4, sticky=tk.W, pady=(8, 2))

        self._batch_text = scrolledtext.ScrolledText(
            self._batch_frame, height=6, wrap=tk.WORD, font=('Consolas', 9))
        self._batch_text.grid(row=1, column=0, columnspan=4,
                              sticky=(tk.W, tk.E), pady=(0, 4))

        def _batch_load_file():
            fp = filedialog.askopenfilename(
                title="Select URL list",
                filetypes=[("Text files", "*.txt"), ("All files", "*.*")])
            if not fp:
                return
            try:
                with open(fp, 'r', encoding='utf-8', errors='ignore') as fh:
                    content = fh.read()
                self._batch_text.delete('1.0', tk.END)
                self._batch_text.insert('1.0', content)
            except Exception as ex:
                self._notify_error("Load File", "Could not read file:\n" + str(ex))

        def _batch_clear():
            self._batch_text.delete('1.0', tk.END)

        def _batch_start():
            raw = self._batch_text.get('1.0', tk.END)
            urls = [ln.strip() for ln in raw.splitlines()
                    if ln.strip() and not ln.strip().startswith('#')]
            valid = [u for u in urls
                     if self.is_valid_youtube_url(u) or self.is_playlist_url(u)]
            if not valid:
                self._notify_warning("Batch", "No valid YouTube URLs found.\n"
                                       "Add one URL per line.")
                return
            if not self.default_quality:
                self._notify_warning("Batch",
                    "Auto-Download is disabled.\n"
                    "Enable it and select a quality so each video knows what to queue.")
                return
            self._batch_queue_btn.config(state='disabled', text='Running...')
            self._batch_cancel_btn.config(state='normal')
            self._batch_cancelled = False
            t = threading.Thread(target=self._batch_analyze_worker, args=(valid,), daemon=True)
            t.start()

        def _batch_cancel():
            """Signal the running batch worker to stop after the current item."""
            self._batch_cancelled = True
            self._batch_cancel_btn.config(state='disabled')
            self.append_terminal_output('Batch cancellation requested - stopping after current item.\n', 'warning')

        self._batch_queue_btn = ttk.Button(self._batch_frame, text="Analyze & Queue All",
                                           command=_batch_start)
        self._batch_queue_btn.grid(row=2, column=0, sticky=tk.W, pady=(2, 0))
        ttk.Button(self._batch_frame, text="Load from file",
                   command=_batch_load_file).grid(row=2, column=1, sticky=tk.W,
                                                  padx=(6, 0), pady=(2, 0))
        ttk.Button(self._batch_frame, text="Clear",
                   command=_batch_clear).grid(row=2, column=2, sticky=tk.W,
                                              padx=(6, 0), pady=(2, 0))
        self._batch_cancel_btn = ttk.Button(self._batch_frame, text="Stop",
                                            command=_batch_cancel, state='disabled')
        self._batch_cancel_btn.grid(row=2, column=3, sticky=tk.W,
                                    padx=(6, 0), pady=(2, 0))
        self._batch_start_immediately = tk.BooleanVar(value=self.batch_start_immediately)
        def _on_batch_immed_toggle():
            self.batch_start_immediately = self._batch_start_immediately.get()
            self._save_config()
        ttk.Checkbutton(self._batch_frame, text="Start downloading immediately",
                        variable=self._batch_start_immediately,
                        command=_on_batch_immed_toggle).grid(
            row=3, column=0, columnspan=2, sticky=tk.W, pady=(4, 0))
        ttk.Label(self._batch_frame,
                  text="Each URL is analyzed and queued at your Auto-Download quality setting.",
                  font=('Arial', 8), foreground='gray').grid(
            row=4, column=0, columnspan=4, sticky=tk.W, pady=(2, 2))

        # Progress container - label on top, bar below, no overlap
        _prog_frame = ttk.Frame(main_frame)
        _prog_frame.grid(row=2, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 4))
        _prog_frame.columnconfigure(0, weight=1)

        self.progress_var = tk.StringVar(value="Ready")
        self.progress_label = ttk.Label(_prog_frame, textvariable=self.progress_var)
        self.progress_label.grid(row=0, column=0, sticky=tk.W, pady=(0, 2))

        self.progress_bar = ttk.Progressbar(_prog_frame, mode='indeterminate')
        self.progress_bar.grid(row=1, column=0, sticky=(tk.W, tk.E))

        # Video Info Section
        info_frame = ttk.LabelFrame(main_frame, text="Video Information", padding="10")
        info_frame.grid(row=3, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 4))
        info_frame.columnconfigure(1, weight=1)
        
        # Video info labels
        self.info_labels = {}
        self._themed_labels = {'blue': [], 'green': [], 'orange': [], 'gray': [], 'red': []}
        info_fields = [
            ("Title:", "title"),
            ("Uploader:", "uploader"),
            ("Duration:", "duration"),
            ("Views:", "views"),
            ("Upload Date:", "upload_date")
        ]
        
        for i, (label_text, key) in enumerate(info_fields):
            ttk.Label(info_frame, text=label_text).grid(row=i, column=0, sticky=tk.W, padx=(0, 5))
            self.info_labels[key] = ttk.Label(info_frame, text="-", foreground="gray")
            self.info_labels[key].grid(row=i, column=1, sticky=tk.W)
        
        # Download Directory Section
        download_frame = ttk.LabelFrame(main_frame, text="Download Settings", padding="10")
        download_frame.grid(row=4, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 4))
        download_frame.columnconfigure(1, weight=1)
        
        # Download folder row
        ttk.Label(download_frame, text="Download Folder:").grid(row=0, column=0, sticky=tk.W, padx=(0, 5))
        
        self.download_path_var = tk.StringVar(value=self.download_path)
        self.download_path_entry = ttk.Entry(download_frame, textvariable=self.download_path_var, state='readonly')
        self.download_path_entry.grid(row=0, column=1, sticky=(tk.W, tk.E), padx=(0, 5))
        
        def browse_download_folder():
            folder = filedialog.askdirectory(initialdir=self.download_path)
            if folder:
                self.download_path = folder
                self.download_path_var.set(folder)
        
        self.browse_btn = ttk.Button(download_frame, text="Browse", command=browse_download_folder)
        self.browse_btn.grid(row=0, column=2, sticky=tk.W, padx=(0, 5))
        
        def open_download_folder():
            try:
                if os.name == 'nt':  # Windows
                    os.startfile(self.download_path)
                elif os.name == 'posix':  # macOS and Linux
                    subprocess.run(['open' if sys.platform == 'darwin' else 'xdg-open', self.download_path])
            except Exception as e:
                self._notify_error("Error", f"Could not open folder: {str(e)}")
        
        self.open_folder_btn = ttk.Button(download_frame, text="Open Folder", command=open_download_folder)
        self.open_folder_btn.grid(row=0, column=3, sticky=tk.W)
        
        # Audio language selection row
        ttk.Label(download_frame, text="Audio Language:").grid(row=1, column=0, sticky=tk.W, padx=(0, 5), pady=(5, 0))
        
        language_frame = ttk.Frame(download_frame)
        language_frame.grid(row=1, column=1, columnspan=2, sticky=(tk.W, tk.E), pady=(5, 0))
        
        self.language_var = tk.StringVar(value="auto (Auto-detect English)")
        self.language_combo = ttk.Combobox(language_frame, textvariable=self.language_var, state='readonly', width=35)
        self.language_combo.grid(row=0, column=0, sticky=tk.W, padx=(0, 5))
        
        # Default options (will be updated when video is analyzed)
        self.language_combo['values'] = [
            "auto (Auto-detect English)",
            "en (Force English)",
            "best (Highest Quality)"
        ]
        
        def on_language_change(event=None):
            selected = self.language_var.get()

            # Ignore separator and "not available" placeholder items - don't change preference
            if selected.startswith('---') or 'not available' in selected:
                # Revert the visual selection to match current preference without changing it
                return

            if selected.startswith('id:'):
                self.preferred_language = selected.split(' ')[0]  # "id:251"
            elif ' (' in selected:
                self.preferred_language = selected.split(' (')[0]  # "en", "zh", etc.
            # (no else - unrecognised formats leave preference unchanged)

            # Refresh recommendations with new language preference
            if self.current_formats:
                self._populate_recommended_combinations(suppress_auto_download=True)
        
        self.language_combo.bind('<<ComboboxSelected>>', on_language_change)
        
        ttk.Label(language_frame, text="(for merged videos)", font=('Arial', 8), foreground="gray").grid(row=0, column=1, sticky=tk.W, padx=(5, 0))
        
        # Download status with cache status
        self.download_status_var = tk.StringVar(value="No downloads yet")
        download_status_label = ttk.Label(download_frame, textvariable=self.download_status_var, foreground="gray")
        download_status_label.grid(row=2, column=0, columnspan=2, sticky=tk.W, pady=(5, 0))
        
        # Cache status indicator
        cache_status = "🗂️ Video cache: Enabled" if self.video_cache_dir else "⚠️ Video cache: Disabled"
        cache_status_label = ttk.Label(download_frame, text=cache_status,
                                     foreground="green" if self.video_cache_dir else "orange",
                                     font=('Arial', 8))
        cache_status_label.grid(row=2, column=2, columnspan=2, sticky=tk.E, pady=(5, 0))


        
        # ── Smart Quality (row 3, replaces old multi-button cache row) ───────
        def _open_cache_dir(path):
            if not path or not os.path.isdir(path):
                self._notify_warning("Open Folder",
                    "Folder does not exist:\n" + (path or "Not set"))
                return
            try:
                if sys.platform == 'win32':
                    os.startfile(path)
                elif sys.platform == 'darwin':
                    subprocess.Popen(['open', path], close_fds=True)
                else:
                    subprocess.Popen(['xdg-open', path], close_fds=True)
            except Exception as e:
                self._notify_error("Open Folder", "Could not open folder:\n" + str(e))

        ttk.Label(download_frame, text="Smart Quality:", font=('Arial', 9, 'bold')).grid(
            row=3, column=0, sticky=tk.W, pady=(6, 2))

        # Cap row
        self._sl_en_var = tk.BooleanVar(value=self.size_limit_enabled)
        self._sl_mb_var = tk.StringVar(value=str(self.size_limit_mb))
        self._sl_fb_var = tk.StringVar(value=self.size_limit_fallback)
        def _on_smart_quality_save(*_):
            if not hasattr(self, '_su_en_var'):
                return
            # Debounce - cancel any pending save and reschedule 150ms out
            if getattr(self, '_sq_save_after_id', None):
                self.root.after_cancel(self._sq_save_after_id)
            def _do_save():
                self.size_limit_enabled = self._sl_en_var.get()
                try:
                    self.size_limit_mb = max(1, int(self._sl_mb_var.get()))
                except ValueError:
                    self.size_limit_mb = 500
                self.size_limit_fallback = self._sl_fb_var.get()
                self.size_upgrade_enabled = self._su_en_var.get()
                self.size_upgrade_to = self._su_to_var.get()
                self._save_config()
            self._sq_save_after_id = self.root.after(150, _do_save)
        cap_frame = ttk.Frame(download_frame)
        cap_frame.grid(row=3, column=1, columnspan=3, sticky=tk.W, pady=(6, 2))
        ttk.Checkbutton(cap_frame, text="Cap if over",
                        variable=self._sl_en_var,
                        command=_on_smart_quality_save).pack(side=tk.LEFT)
        ttk.Entry(cap_frame, textvariable=self._sl_mb_var, width=6).pack(side=tk.LEFT, padx=(4, 2))
        self._sl_mb_var.trace_add('write', _on_smart_quality_save)
        ttk.Label(cap_frame, text="MB → fall back to").pack(side=tk.LEFT, padx=(2, 4))
        _q_opts = ["2160p", "1440p", "1080p", "720p", "480p", "360p", "240p", "144p"]
        ttk.Combobox(cap_frame, textvariable=self._sl_fb_var,
                     values=_q_opts, state='readonly', width=7).pack(side=tk.LEFT)
        self._sl_fb_var.trace_add('write', _on_smart_quality_save)

        # Upgrade row
        self._su_en_var = tk.BooleanVar(value=self.size_upgrade_enabled)
        self._su_to_var = tk.StringVar(value=self.size_upgrade_to)
        upg_frame = ttk.Frame(download_frame)
        upg_frame.grid(row=4, column=1, columnspan=3, sticky=tk.W, pady=(2, 4))
        ttk.Checkbutton(upg_frame, text="Upgrade if under limit, up to",
                        variable=self._su_en_var,
                        command=_on_smart_quality_save).pack(side=tk.LEFT)
        ttk.Combobox(upg_frame, textvariable=self._su_to_var,
                     values=_q_opts, state='readonly', width=7).pack(side=tk.LEFT, padx=(4, 0))
        self._su_to_var.trace_add('write', _on_smart_quality_save)

        # ── Subtitle quick-select (row 5) ────────────────────────────────────
        _SQ_SRC_OPTS   = ["Manual", "Manual+Auto", "External"]
        _SQ_SRC_VALUES = ["manual", "auto", "external"]
        _SQ_MODE_OPTS   = ["S", "SD", "HS"]
        _SQ_LANG_OPTS = [
            ("English", "en"), ("Spanish", "es"), ("French", "fr"),
            ("German", "de"), ("Italian", "it"), ("Portuguese", "pt"),
            ("Russian", "ru"), ("Japanese", "ja"), ("Korean", "ko"),
            ("Chinese", "zh"), ("Arabic", "ar"), ("Hindi", "hi"),
        ]
        _SQ_LANG_DISPLAY  = [n + " (" + c + ")" for n, c in _SQ_LANG_OPTS]
        _SQ_CODE_TO_DISP  = {c: n + " (" + c + ")" for n, c in _SQ_LANG_OPTS}
        _SQ_DISP_TO_CODE  = {n + " (" + c + ")": c for n, c in _SQ_LANG_OPTS}

        # Toggle on/off - when off, subtitle_source is 'off'; when on, use combo value
        _sub_is_enabled = (self.subtitle_source != 'off')
        self._subtitle_enabled_var = tk.BooleanVar(value=_sub_is_enabled)
        # Always restore the combo from subtitle_last_source so the selection
        # persists across sessions even when the toggle was off.
        _last_src = getattr(self, 'subtitle_last_source', 'manual')
        if _last_src in _SQ_SRC_VALUES:
            _sq_src_init = _SQ_SRC_OPTS[_SQ_SRC_VALUES.index(_last_src)]
        else:
            _sq_src_init = "Manual"
        _sq_mode_init = self.subtitle_mode if self.subtitle_mode in _SQ_MODE_OPTS else "S"
        _sq_lang_init = _SQ_CODE_TO_DISP.get(self.subtitle_lang, "English (en)")

        self._sq_src_var  = tk.StringVar(value=_sq_src_init)
        self._sq_mode_var = tk.StringVar(value=_sq_mode_init)
        self._sq_lang_var = tk.StringVar(value=_sq_lang_init)

        sub_row_frame = ttk.Frame(download_frame)
        sub_row_frame.grid(row=5, column=0, columnspan=4, sticky=tk.W, pady=(2, 2))

        ttk.Label(sub_row_frame, text="Subtitles:", font=('Arial', 9, 'bold')).pack(side=tk.LEFT, padx=(0, 4))

        # On/Off toggle checkbutton
        self._subtitle_toggle_cb = ttk.Checkbutton(
            sub_row_frame, variable=self._subtitle_enabled_var,
            command=lambda: self._on_subtitle_toggle_changed(
                _SQ_SRC_OPTS, _SQ_SRC_VALUES, _SQ_DISP_TO_CODE, _SQ_MODE_OPTS))
        self._subtitle_toggle_cb.pack(side=tk.LEFT, padx=(0, 4))

        self._sq_src_combo = ttk.Combobox(sub_row_frame, textvariable=self._sq_src_var,
                                          values=_SQ_SRC_OPTS, style='SubtitleActive.TCombobox',
                                          state='readonly', width=15)
        self._sq_src_combo.pack(side=tk.LEFT, padx=(0, 4))

        self._sq_mode_combo = ttk.Combobox(sub_row_frame, textvariable=self._sq_mode_var,
                                           values=_SQ_MODE_OPTS, style='SubtitleActive.TCombobox',
                                           state='readonly', width=4)
        self._sq_mode_combo.pack(side=tk.LEFT, padx=(0, 4))

        self._sq_lang_combo = ttk.Combobox(sub_row_frame, textvariable=self._sq_lang_var,
                                           values=_SQ_LANG_DISPLAY, style='SubtitleActive.TCombobox',
                                           state='readonly', width=14)
        self._sq_lang_combo.pack(side=tk.LEFT, padx=(0, 6))
        ttk.Label(sub_row_frame, text="S=soft  SD=auto-show  HS=burn-in  External=save .srt only",
                  font=('Arial', 8), foreground="gray").pack(side=tk.LEFT)

        def _sq_update_mode_state(*_):
            self._update_subtitle_combo_states()
        self._sq_src_var.trace_add('write', _sq_update_mode_state)
        _sq_update_mode_state()

        def _sq_save(*_):
            # Always remember the combo selection regardless of toggle state
            src_val = _SQ_SRC_VALUES[_SQ_SRC_OPTS.index(self._sq_src_var.get())] if self._sq_src_var.get() in _SQ_SRC_OPTS else 'manual'
            self.subtitle_last_source = src_val
            if not self._subtitle_enabled_var.get():
                self.subtitle_source = 'off'
            else:
                self.subtitle_source = src_val
            mode_val = self._sq_mode_var.get() if self._sq_mode_var.get() in _SQ_MODE_OPTS else 'S'
            lang_val = _SQ_DISP_TO_CODE.get(self._sq_lang_var.get(), 'en')
            self.subtitle_mode   = mode_val
            self.subtitle_lang   = lang_val
            self._save_config()
        self._sq_src_var.trace_add('write',  _sq_save)
        self._sq_mode_var.trace_add('write', _sq_save)
        self._sq_lang_var.trace_add('write', _sq_save)

        # yt-dlp and FFmpeg status indicators - click-to-dismiss path popup
        def _show_path_popup(widget, text):
            """Show a borderless popup right-aligned to widget, clamped to screen."""
            popup = tk.Toplevel(self.root)
            popup.overrideredirect(True)
            popup.attributes('-topmost', True)
            lbl = tk.Label(popup, text=text, bg='#ffffc0', relief=tk.SOLID,
                           borderwidth=1, font=('Consolas', 8), padx=6, pady=4)
            lbl.pack()
            # Measure popup after layout
            popup.update_idletasks()
            pw = popup.winfo_reqwidth()
            ph = popup.winfo_reqheight()
            # Right-align popup to widget's right edge, appear above it
            wx_right = widget.winfo_rootx() + widget.winfo_width()
            x = wx_right - pw
            y = widget.winfo_rooty() - ph - 4
            # Clamp so popup never goes off the left or top of screen
            sw = self.root.winfo_screenwidth()
            x = max(0, min(x, sw - pw))
            y = max(0, y)
            popup.geometry(str(pw) + 'x' + str(ph) + '+' + str(x) + '+' + str(y))
            popup.bind('<Button-1>', lambda e: popup.destroy())
            lbl.bind('<Button-1>', lambda e: popup.destroy())
            popup.bind('<FocusOut>', lambda e: popup.destroy())
            popup.focus_set()

        ytdlp_display = "yt-dlp: " + (os.path.basename(self.ytdlp_path) if self.ytdlp_path else "Not found")
        ytdlp_status_label = ttk.Label(download_frame, text="✅ " + ytdlp_display,
                                     foreground="green", font=('Arial', 8))
        ytdlp_status_label.grid(row=3, column=2, columnspan=2, sticky=tk.E, pady=(6, 0))
        self._themed_labels['green'].append(ytdlp_status_label)

        def show_ytdlp_path(event):
            path_text = self.ytdlp_path if self.ytdlp_path else "yt-dlp not found"
            _show_path_popup(ytdlp_status_label, path_text)
        ytdlp_status_label.bind("<Button-1>", show_ytdlp_path)
        ytdlp_status_label.config(cursor="hand2")

        ffmpeg_display = "FFmpeg: " + (os.path.basename(self.ffmpeg_path) if self.ffmpeg_path else "Not found")
        ffmpeg_status_label = ttk.Label(download_frame,
                                       text=("✅ " if self.ffmpeg_path else "⚠️ ") + ffmpeg_display,
                                       foreground="green" if self.ffmpeg_path else "orange",
                                       font=('Arial', 8))
        ffmpeg_status_label.grid(row=4, column=2, columnspan=2, sticky=tk.E, pady=(2, 4))
        _ff_color = 'green' if self.ffmpeg_path else 'orange'
        self._themed_labels[_ff_color].append(ffmpeg_status_label)

        def show_ffmpeg_path(event):
            if self.ffmpeg_path:
                path_text = self.ffmpeg_path
            else:
                path_text = ("FFmpeg not found.\nLooked in:\n"
                             "  " + os.path.join(SCRIPT_DIR, 'ffmpeg.exe') + "\n"
                             "  C:\\ffmpeg\\bin\\ffmpeg.exe\n"
                             "  System PATH")
            _show_path_popup(ffmpeg_status_label, path_text)
        ffmpeg_status_label.bind("<Button-1>", show_ffmpeg_path)
        ffmpeg_status_label.config(cursor="hand2")

        # Cache size indicator
        self.cache_size_var = tk.StringVar(value="Cache: 0.0 MB")
        self.cache_size_label = ttk.Label(download_frame, textvariable=self.cache_size_var,
                                          foreground="gray", font=('Arial', 8))
        self.cache_size_label.grid(row=4, column=0, columnspan=2, sticky=tk.W, pady=(2, 0))
        self._themed_labels['gray'].append(self.cache_size_label)

        # Notebook for different stream types
        self.notebook = ttk.Notebook(main_frame)
        self.notebook.grid(row=6, column=0, columnspan=3, sticky=(tk.W, tk.E, tk.N, tk.S), pady=(0, 4))
        
        # Recommended combinations tab (FIRST)
        self.recommended_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.recommended_frame, text="🎯 Recommended")
        self.setup_recommended_treeview(self.recommended_frame)
        
        # Combined streams tab
        self.combined_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.combined_frame, text="🎬 Combined (Video+Audio)")
        self.setup_stream_treeview(self.combined_frame, "combined")
        
        # Video-only streams tab
        self.video_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.video_frame, text="🎥 Video Only")
        self.setup_stream_treeview(self.video_frame, "video")
        
        # Audio-only streams tab
        self.audio_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.audio_frame, text="🎵 Audio Only")
        self.setup_stream_treeview(self.audio_frame, "audio")
        
        # All streams tab
        self.all_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.all_frame, text="📋 All Streams")
        self.setup_stream_treeview(self.all_frame, "all")
        
        # Download history tab
        self.history_frame = ttk.Frame(self.notebook)
        self.notebook.add(self.history_frame, text="📜 History")
        self._setup_history_panel(self.history_frame)

        # === BEGIN DEV TOOLS ===
        # Diagnostics lives on the MAIN notebook rather than inside Settings:
        # a run takes many minutes, and the Settings dialog is modal-ish and
        # disposable - closing it left the progress callback writing to a
        # destroyed label. As a tab it can be left running in the background
        # while other tabs are used, and switching back shows live progress.
        if DEV_MODE:
            self.diag_frame = ttk.Frame(self.notebook)
            self.notebook.add(self.diag_frame, text="🧪 Diagnostics")
            self._setup_diagnostics_panel(self.diag_frame)
        # === END DEV TOOLS ===

        # ── Button row 1: action buttons ─────────────────────────────────────
        button_frame = ttk.Frame(main_frame)
        button_frame.grid(row=7, column=0, columnspan=3, sticky=(tk.W, tk.E), pady=(0, 2))

        self.download_merge_btn = ttk.Button(button_frame, text="⬇ Merge",
                                           command=self.download_and_merge, state='disabled')
        self.download_merge_btn.pack(side=tk.LEFT, padx=(0, 3))

        self.preview_btn = ttk.Button(button_frame, text="Preview",
                                      command=self._show_preview,
                                      state='disabled')
        self.preview_btn.pack(side=tk.LEFT, padx=(0, 3))

        self.pause_btn = ttk.Button(button_frame, text="⏸ Pause",
                                    command=self.pause_download, state='disabled')
        self.pause_btn.pack(side=tk.LEFT, padx=(0, 3))

        self.stop_btn = ttk.Button(button_frame, text="⏹ Stop",
                                   command=self.stop_download, state='disabled')
        self.stop_btn.pack(side=tk.LEFT, padx=(0, 3))

        self.copy_info_btn = ttk.Button(button_frame, text="Copy Info",
                                       command=self.copy_video_info, state='disabled')
        self.copy_info_btn.pack(side=tk.LEFT, padx=(0, 3))

        self.settings_btn = ttk.Button(button_frame, text="Settings", command=self.show_settings)
        self.settings_btn.pack(side=tk.LEFT, padx=(0, 3))

        self.clear_cache_btn = ttk.Button(button_frame, text="Clear Cache", command=self.clear_video_cache)
        self.clear_cache_btn.pack(side=tk.LEFT, padx=(0, 3))

        ttk.Button(button_frame, text="Open Cache",
                   command=lambda: _open_cache_dir(
                       getattr(self, 'ysa_cache_root', None))
                   ).pack(side=tk.LEFT, padx=(0, 3))

        self.clear_btn = ttk.Button(button_frame, text="Clear", command=self.clear_all)
        self.clear_btn.pack(side=tk.LEFT, padx=(0, 8))

        # Second row: Audio Only + format selector | Metadata | Custom DNS
        # All on one line so none of them get clipped at narrow window widths.
        toggle_frame = ttk.Frame(main_frame)
        toggle_frame.grid(row=8, column=0, columnspan=3, sticky=tk.W, pady=(0, 2))

        self.audio_only_cb = ttk.Checkbutton(
            toggle_frame, text="Audio Only",
            variable=self.audio_only_mode,
            command=self._on_audio_only_toggle)
        self.audio_only_cb.pack(side=tk.LEFT, padx=(0, 2))

        # Format selector: M4A Native, M4A AAC, or MP3
        self._audio_format_var = tk.StringVar(
            value=getattr(self, 'audio_only_format', 'm4a_native').upper().replace('_', ' '))
        self._audio_fmt_combo = ttk.Combobox(
            toggle_frame, textvariable=self._audio_format_var,
            values=['M4A NATIVE', 'M4A AAC', 'MP3'], state='readonly', width=12)
        self._audio_fmt_combo.pack(side=tk.LEFT, padx=(0, 12))
        self._audio_fmt_combo.bind('<<ComboboxSelected>>',
                                   lambda e: self._on_audio_format_changed())

        self.embed_meta_cb = ttk.Checkbutton(
            toggle_frame, text="Metadata",
            variable=self.embed_metadata_enabled,
            command=self._save_config)
        self.embed_meta_cb.pack(side=tk.LEFT, padx=(0, 8))

        self.dns_cb = ttk.Checkbutton(
            toggle_frame, text="Custom DNS",
            variable=self.custom_dns_enabled,
            command=self._on_dns_toggle)
        self.dns_cb.pack(side=tk.LEFT)

        # ── Cookies on/off toggle ────────────────────────────────────────────
        # Lets the user quickly disable cookie sending without removing the
        # configured cookie file/browser in Settings.
        self._cookies_enabled_var = tk.BooleanVar(value=getattr(self, 'cookies_enabled', True))
        self._mk_var_mirror(self._cookies_enabled_var, '_m_cookies_on', bool)
        if hasattr(self, '_history_enabled_var'):
            self._mk_var_mirror(self._history_enabled_var, '_m_history_on', bool)
        self.cookies_cb = ttk.Checkbutton(
            toggle_frame, text="Cookies",
            variable=self._cookies_enabled_var,
            command=self._save_config)
        self.cookies_cb.pack(side=tk.LEFT, padx=(8, 0))

        # ── Clip / section download time fields ──────────────────────────────
        # Revealed by the "Clip" checkbox.  Start/End accept HH:MM:SS, MM:SS,
        # raw seconds, or decimal seconds (e.g. 00:00:01.5).
        self._clip_enabled_var = tk.BooleanVar(value=False)
        self._clip_start_var   = tk.StringVar(value='00:00:00.00')
        self._clip_end_var     = tk.StringVar(value='00:00:00.00')
        self._mk_var_mirror(self._clip_enabled_var, '_m_clip_on', bool)
        self._mk_var_mirror(self._clip_start_var, '_m_clip_start', str)
        self._mk_var_mirror(self._clip_end_var, '_m_clip_end', str)

        def _on_clip_toggle():
            _state = 'normal' if self._clip_enabled_var.get() else 'disabled'
            self._clip_start_entry_w.config(state=_state)
            self._clip_end_entry_w.config(state=_state)
            if not self._clip_enabled_var.get():
                self._clip_start_var.set('00:00:00.00')
                self._clip_end_var.set('00:00:00.00')
        # Store so preview can call it from root.after
        self._on_clip_toggle_fn = _on_clip_toggle

        ttk.Checkbutton(toggle_frame, text='Clip',
                        variable=self._clip_enabled_var,
                        command=_on_clip_toggle).pack(side=tk.LEFT, padx=(12, 2))

        ttk.Label(toggle_frame, text='Start:').pack(side=tk.LEFT, padx=(2, 1))
        self._clip_start_entry_w = ttk.Entry(toggle_frame, textvariable=self._clip_start_var,
                                      width=13, state='disabled')
        self._clip_start_entry_w.pack(side=tk.LEFT, padx=(0, 6))
        ttk.Label(toggle_frame, text='End:').pack(side=tk.LEFT, padx=(0, 1))
        self._clip_end_entry_w = ttk.Entry(toggle_frame, textvariable=self._clip_end_var,
                                    width=13, state='disabled')
        self._clip_end_entry_w.pack(side=tk.LEFT, padx=(0, 2))

        def _normalise_clip_field(var):
            """Reformat a clip field to HH:MM:SS.ss when focus leaves it, so
            '90.5' or '1:30' become the canonical form and the precision the
            downloader will actually use is what the user sees."""
            def _handler(_e=None):
                _v = self._parse_time_to_hhmmss(var.get())
                if _v:
                    var.set(_v)
            return _handler
        self._clip_start_entry_w.bind('<FocusOut>', _normalise_clip_field(self._clip_start_var))
        self._clip_end_entry_w.bind('<FocusOut>', _normalise_clip_field(self._clip_end_var))
        self._clip_start_entry_w.bind('<Return>', _normalise_clip_field(self._clip_start_var))
        self._clip_end_entry_w.bind('<Return>', _normalise_clip_field(self._clip_end_var))

        # Terminal + queue share a 2-col bottom container.
        # setup_terminal_output creates _bottom_container first;
        # _setup_queue_panel then places the queue in its right column.
        self.setup_terminal_output(main_frame)
        self._setup_queue_panel(main_frame)
        
        # Status bar
        self.status_var = tk.StringVar()
        
        # Set initial status based on setup
        initial_status = "Ready"
        if not self.ffmpeg_path:
            initial_status += " - FFmpeg not found"
        if not self.video_cache_dir:
            initial_status += " - Video caching disabled"
        
        self.status_var.set(initial_status)
        
        # ── Update notification banner (hidden by default, shown when updates are found) ──
        self._update_banner_frame = tk.Frame(main_frame, background='#FF8C00', relief=tk.FLAT)
        # Don't grid it yet - shown only when updates are available via _show_update_banner()
        self._update_banner_lbl = tk.Label(
            self._update_banner_frame,
            text='', background='#FF8C00', foreground='white',
            font=('Arial', 9, 'bold'), anchor='w')
        self._update_banner_lbl.pack(side=tk.LEFT, padx=10, pady=4, fill=tk.X, expand=True)
        tk.Button(
            self._update_banner_frame,
            text='Update Now', background='white', foreground='#FF8C00',
            font=('Arial', 8, 'bold'), relief=tk.FLAT, cursor='hand2',
            command=self._run_pending_updates).pack(side=tk.RIGHT, padx=8, pady=3)
        tk.Button(
            self._update_banner_frame,
            text='x', background='#FF8C00', foreground='white',
            font=('Arial', 8), relief=tk.FLAT, cursor='hand2',
            command=self._dismiss_update_banner).pack(side=tk.RIGHT, padx=(0, 4), pady=3)

        # Bottom strip: toggle terminal button (left) + status bar (right)
        bottom_strip = ttk.Frame(main_frame)
        bottom_strip.grid(row=10, column=0, columnspan=3, sticky=(tk.W, tk.E))
        bottom_strip.columnconfigure(1, weight=1)

        self._toggle_terminal_strip_btn = ttk.Button(
            bottom_strip, text="▲ Hide Terminal", width=16,
            command=self.toggle_terminal)
        self._toggle_terminal_strip_btn.grid(row=0, column=0, sticky=tk.W, padx=(0, 6))

        status_bar = ttk.Label(bottom_strip, textvariable=self.status_var,
                               relief=tk.SUNKEN, padding="5")
        status_bar.grid(row=0, column=1, sticky=(tk.W, tk.E))

        # Store button_frame ref - no longer needed for hide/show but kept for theming
        self._button_frame = button_frame

        # Restore terminal state from config
        if not self.terminal_expanded:
            self.root.after(100, self._apply_terminal_collapsed)

    
    def _state_subdir_targets(self, leaf):
        """Both state roots' copies of one subfolder (real + dev sandbox).

        Named explicitly rather than derived from ysa_state_root because
        with the stub engaged that attribute points at ysa_state_dev -
        the same trap _delete_all_cache_folders documents for the cache.
        """
        return [os.path.join(SCRIPT_DIR, _n, leaf)
                for _n in ('ysa_state', 'ysa_state_dev')]

    def _delete_ytdlp_cache_folders(self):
        """Remove the yt-dlp player/nsig cache wholesale. Returns
        (removed_names, anything_left_behind). Shared by the dedicated
        Clear yt-dlp Cache button and by Clear Cache Now, so the two
        cannot drift apart."""
        _targets = self._state_subdir_targets('yt-dlp')
        _removed = []
        for _t in _targets:
            if os.path.isdir(_t):
                shutil.rmtree(_t, ignore_errors=True)
                if not os.path.isdir(_t):
                    _removed.append(os.path.basename(os.path.dirname(_t))
                                    + '/yt-dlp')
        return _removed, any(os.path.isdir(_t) for _t in _targets)

    def _delete_state_and_history_on_clear(self):
        """The non-cache leftovers Clear Cache Now also removes.

        Scorched earth minus whatever the Settings > Cache 'Preserve'
        boxes protect. Every target is removed WHOLESALE - a whole
        folder, or the whole history file - never a per-file walk with a
        counter, which is the shape that once early-returned and left
        categories behind (see clear_video_cache's docstring).

        Clear-cache-on-EXIT never calls this: on-exit stays hardwired to
        the cache roots, so a stray checkbox can never cost a log.
        """
        _removed, _left = [], False
        if not getattr(self, 'preserve_logs_on_clear', True):
            _targets = self._state_subdir_targets('logs')
            for _t in _targets:
                if os.path.isdir(_t):
                    shutil.rmtree(_t, ignore_errors=True)
                    if not os.path.isdir(_t):
                        _removed.append(os.path.basename(os.path.dirname(_t))
                                        + '/logs')
            _left = _left or any(os.path.isdir(_t) for _t in _targets)
        if not getattr(self, 'preserve_ytdlp_on_clear', False):
            _r, _l = self._delete_ytdlp_cache_folders()
            _removed += _r
            _left = _left or _l
        if not getattr(self, 'preserve_history_on_clear', False):
            # Clear the in-memory list FIRST: deleting only the file would
            # be undone by the next _save_download_history().
            try:
                self.download_history.clear()
            except Exception:
                pass
            _h = os.path.join(SCRIPT_DIR, 'ysa_history.json')
            if os.path.isfile(_h):
                try:
                    os.remove(_h)
                    _removed.append('ysa_history.json')
                except OSError:
                    _left = True
            try:
                self._refresh_history_panel()
            except Exception:
                pass
        # The roots go too when nothing inside them was preserved: 'clear the
        # cache should leave nothing on disk, not an empty shell'
        # (clear_video_cache's own rule, applied to state as well). os.rmdir
        # REFUSES a non-empty directory, so a preserved logs or yt-dlp folder
        # blocks this by itself - no second condition to keep in sync, and
        # nothing unexpected can ever be swept up with the root.
        for _n in ('ysa_state', 'ysa_state_dev'):
            _r = os.path.join(SCRIPT_DIR, _n)
            if os.path.isdir(_r):
                try:
                    os.rmdir(_r)
                    _removed.append(_n)
                except OSError:
                    pass
        return _removed, _left

    def clear_ytdlp_cache(self):
        """Delete ONLY the yt-dlp player/nsig cache.

        That cache occasionally goes stale and clearing it fixes
        extraction errors, so the action exists deliberately instead of
        riding along as a side effect of Clear Cache.
        """
        if not messagebox.askyesno(
                'Clear yt-dlp Cache',
                'Delete the yt-dlp player / nsig cache?\n\n'
                'Cached streams, logs and history are NOT touched.\n'
                'The next video will re-solve the player JS once.'):
            return
        _removed, _left = self._delete_ytdlp_cache_folders()
        if _removed:
            self.append_terminal_output(
                'Cleared yt-dlp cache: ' + ', '.join(_removed) + '\n', 'success')
        else:
            self.append_terminal_output(
                'yt-dlp cache: nothing to remove.\n', 'info')
        if _left:
            self.append_terminal_output(
                'Some yt-dlp cache files were locked and remain.\n', 'warning')

    def _delete_all_cache_folders(self):
        """Remove every cache folder: the active one plus the real and dev
        sandboxes. Returns (removed_names, anything_left_behind).

        Shared by the Clear Cache button and the clear-on-exit setting so the
        two cannot drift apart - "the same as the button" has to mean the
        same code, not a copy of it. With the stub or a scenario run engaged
        ysa_cache_root points at ysa_cache_dev, so naming the real cache
        explicitly is what stops it being skipped.
        """
        _targets, _seen = [], set()
        for _t in ([getattr(self, 'ysa_cache_root', None)]
                   + [os.path.join(SCRIPT_DIR, _n) for _n in
                      ('ysa_cache', 'ysa_cache_dev', 'ysa_cache_stub')]):
            if not _t:
                continue
            _k = os.path.normcase(os.path.abspath(_t))
            if _k in _seen:
                continue
            _seen.add(_k)
            _targets.append(_t)
        _removed = []
        for _t in _targets:
            if os.path.isdir(_t):
                shutil.rmtree(_t, ignore_errors=True)
                if not os.path.isdir(_t):
                    _removed.append(os.path.basename(_t.rstrip('\\/')))
        return _removed, any(os.path.isdir(_t) for _t in _targets)

    def _preserve_summary_text(self):
        """One human line each for what Clear Cache also deletes and what
        it spares, so the confirm dialog can never misdescribe it."""
        _also, _kept = [], []
        (_kept if getattr(self, 'preserve_logs_on_clear', True)
         else _also).append('session logs')
        (_kept if getattr(self, 'preserve_ytdlp_on_clear', False)
         else _also).append('yt-dlp cache')
        (_kept if getattr(self, 'preserve_history_on_clear', False)
         else _also).append('download history')
        _t = 'Also deleted: ' + (', '.join(_also) if _also else 'nothing else')
        return _t + '\nPreserved: ' + (', '.join(_kept) if _kept else 'nothing')

    def clear_video_cache(self):
        """Clear Cache = nuke the entire ysa_cache folder and start fresh.

        Deletes every category in one shot - video/audio streams, subtitles,
        thumbnails, premuxed files, MP3s, yt-dlp caches, temp work - so no
        category can ever be missed again. (The old per-directory version
        early-returned on a counter that only knew about videos+subtitles,
        so premuxed/MP3 files survived whenever those counters were empty.)
        Refuses while a download or pre-cache is running: temp work now
        lives inside the cache folder, so deleting it mid-flight would rip
        files out from under yt-dlp/FFmpeg."""
        if not self.ysa_cache_root:
            self._notify_info("Cache", "Caching is disabled")
            return

        # Refuse while anything is actively using the folder
        _busy = bool(getattr(self, '_download_active', False)) or \
                bool(getattr(self, '_download_paused', False))
        if not _busy and hasattr(self, '_precache_lock'):
            try:
                with self._precache_lock:
                    _busy = bool(getattr(self, '_precache_active_ids', None))
            except Exception:
                pass
        if _busy:
            self._notify_warning(
                "Clear Cache",
                "A download or pre-cache is in progress.\n\n"
                "Stop or finish downloads first, then clear the cache.")
            return

        try:
            if not messagebox.askyesno(
                    "Clear Cache",
                    "Delete the ENTIRE cache folder?\n\n"
                    + self.ysa_cache_root + "\n\n"
                    + "All cached streams, premuxed files, subtitles,"
                    " thumbnails, MP3s and temp files will be removed."
                    " Future downloads will re-fetch streams as needed.\n\n"
                    + self._preserve_summary_text()):
                return

            # Release anything that may hold files inside the folder
            _srv = getattr(self, '_preview_srv', None)
            if _srv is not None:
                try:
                    _srv.shutdown()
                    _srv.server_close()
                except Exception:
                    pass
                self._preview_srv = None
            if hasattr(self, '_close_session_log'):
                try:
                    self._close_session_log()
                except Exception:
                    pass
            # Preview may have spawned a piping FFmpeg that still holds a
            # tmp file open - kill strays so Windows releases the handles.
            self._kill_all_ffmpeg()
            time.sleep(0.5)

            # Clear EVERY cache folder, not just the active one. With the
            # stub or a scenario run engaged, ysa_cache_root points at
            # ysa_cache_dev - so the old code cleared the sandbox and left the
            # real cache untouched while reporting "Cache folder deleted".
            # ysa_cache_stub is the pre-merge stub folder; still removed so an
            # upgraded install does not keep it forever.
            _removed, _leftover = self._delete_all_cache_folders()
            # Scorched earth continues past the cache roots: state folders
            # and history, minus whatever the Preserve boxes protect. The
            # on-exit path deliberately does NOT call this.
            _extra, _extra_left = self._delete_state_and_history_on_clear()
            _removed = _removed + _extra
            _leftover = _leftover or _extra_left

            # The folder is deliberately NOT recreated here: "clear the cache"
            # should leave nothing on disk, not an empty shell. The structure
            # is rebuilt by _ensure_cache_dirs the next time a download or a
            # cache write needs it.
            self.cached_videos = {}
            self.cached_subtitles = {}
            self.cached_premuxed = {}
            self._cache_size_bytes = 0
            self._thumbnail_cached_ids.clear()
            if hasattr(self, '_precache_completed_ids'):
                self._precache_completed_ids.clear()
            self.cache_metadata = {'videos': {}, 'subtitles': {}}
            self.save_cache_metadata()
            # (setup_cache_directories above already reopened the session
            # log; calling it again here created a second, empty log file.)

            if _leftover:
                self.append_terminal_output(
                    "Cache cleared, but the folder could not be fully removed"
                    " - a few files are locked and will be swept on next"
                    " exit.\n", 'warning')
            else:
                self.append_terminal_output(
                    "Deleted: " + (", ".join(_removed) if _removed else "nothing")
                    + ". Recreated automatically on the next download"
                    " (session logging resumes then).\n", 'success')
            self._notify_info("Cache", "Cache cleared")
            self.status_var.set("Cache cleared")
            self.root.after(0, self._update_cache_size_label)

        except Exception as e:
            self._notify_error("Error", "Failed to clear cache: " + str(e))

    def setup_stream_treeview(self, parent, stream_type):
        """Set up treeview for displaying streams"""
        # Create frame for treeview and scrollbars
        tree_frame = ttk.Frame(parent)
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Define columns based on stream type
        if stream_type == "combined":
            columns = ("Quality", "Container", "Size", "Video Codec", "Audio Codec", "FPS", "Format ID")
        elif stream_type == "video":
            columns = ("Quality", "Container", "Size", "Bitrate", "Codec", "FPS", "Format ID")
        elif stream_type == "audio":
            columns = ("Quality", "Container", "Size", "Bitrate", "Codec", "Sample Rate", "Format ID")
        else:  # all
            columns = ("Type", "Quality", "Container", "Size", "Video Codec", "Audio Codec", "Format ID")
        
        # Create treeview
        tree = ttk.Treeview(tree_frame, columns=columns, show='headings', height=9)
        
        # Configure column headings and widths
        for col in columns:
            tree.heading(col, text=col)
            if col == "Format ID":
                tree.column(col, width=80, anchor=tk.CENTER)
            elif col in ["Size", "Bitrate", "FPS", "Sample Rate"]:
                tree.column(col, width=80, anchor=tk.CENTER)
            elif col == "Quality":
                tree.column(col, width=70, anchor=tk.CENTER)
            elif col == "Container":
                tree.column(col, width=60, anchor=tk.CENTER)
            elif col == "Type":
                tree.column(col, width=100, anchor=tk.CENTER)
            else:
                tree.column(col, width=120)
        
        # Scrollbars
        v_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=tree.yview)
        h_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.HORIZONTAL, command=tree.xview)
        tree.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        # Pack treeview and scrollbars
        tree.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        v_scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))
        h_scrollbar.grid(row=1, column=0, sticky=(tk.W, tk.E))
        
        # Configure grid weights
        tree_frame.columnconfigure(0, weight=1)
        tree_frame.rowconfigure(0, weight=1)
        
        # Store reference to treeview
        setattr(self, f"{stream_type}_tree", tree)
        
        # Bind double-click event
        tree.bind('<Double-1>', lambda e: self.on_stream_double_click(e, tree))
    
    def setup_recommended_treeview(self, parent):
        """Set up treeview for recommended stream combinations"""
        # Create frame for treeview and scrollbars
        tree_frame = ttk.Frame(parent)
        tree_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Info label with cache info
        cache_info = " 🗂️ Video caching enabled for faster multi-language downloads." if self.video_cache_dir else ""
        info_label = ttk.Label(tree_frame, 
                              text=f"💡 Defaults to best English audio quality. Select other languages from dropdown if available.{cache_info}",
                              foreground="#5a8fbf", font=('Arial', 9, 'italic'))
        info_label.grid(row=0, column=0, columnspan=2, sticky=(tk.W, tk.E), pady=(0, 10))
        
        # Define columns for recommendations
        columns = ("Quality", "Video Format", "Audio Format", "Total Size", "Cache Status")
        
        # Create treeview
        tree = ttk.Treeview(tree_frame, columns=columns, show='headings', height=9)
        
        # Configure column headings and widths
        tree.heading("Quality", text="Quality")
        tree.heading("Video Format", text="Video Stream")
        tree.heading("Audio Format", text="Audio Stream") 
        tree.heading("Total Size", text="Est. Size")
        tree.heading("Cache Status", text="Cache/Instructions")
        
        tree.column("Quality", width=80, anchor=tk.CENTER)
        tree.column("Video Format", width=120)
        tree.column("Audio Format", width=120)
        tree.column("Total Size", width=80, anchor=tk.CENTER)
        tree.column("Cache Status", width=200)
        
        # Scrollbars
        v_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=tree.yview)
        h_scrollbar = ttk.Scrollbar(tree_frame, orient=tk.HORIZONTAL, command=tree.xview)
        tree.configure(yscrollcommand=v_scrollbar.set, xscrollcommand=h_scrollbar.set)
        
        # Grid treeview and scrollbars
        tree.grid(row=1, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))
        v_scrollbar.grid(row=1, column=1, sticky=(tk.N, tk.S))
        h_scrollbar.grid(row=2, column=0, sticky=(tk.W, tk.E))
        
        # Configure grid weights
        tree_frame.columnconfigure(0, weight=1)
        tree_frame.rowconfigure(1, weight=1)
        
        # Store reference to treeview
        self.recommended_tree = tree

        # Set row tag colours at creation time (theme methods re-apply on mode switch)
        tree.tag_configure('direct_en',               background='lightgreen',  foreground='')
        tree.tag_configure('direct_other',            background='lightblue',   foreground='')
        tree.tag_configure('direct',                  background='lightgray',   foreground='')
        tree.tag_configure('combination_both_cached', background='#90EE90',     foreground='darkgreen')
        tree.tag_configure('combination_cached',      background='lightyellow', foreground='darkgreen')
        tree.tag_configure('combination_audio_cached',background='#E0FFE0',     foreground='darkgreen')
        tree.tag_configure('combination_en',          background='lightyellow', foreground='')
        tree.tag_configure('combination_selected',    background='lightcyan',   foreground='')
        tree.tag_configure('combination_other',       background='lightcoral',  foreground='')

        # Double-click merges; the details dialog moves to right-click so
        # nothing is lost. (The earlier double-click handler patched for
        # this was on_stream_double_click, which belongs to a different
        # tree - this is the one the Recommended tab actually uses.)
        tree.bind('<Double-1>', lambda e: self.on_recommended_double_click(e))
        tree.bind('<Button-3>', lambda e: self.show_combination_details(e))

    def is_valid_youtube_url(self, url):
        """Check if the URL is a valid YouTube URL"""
        return any(p.match(url) for p in _YT_URL_PATTERNS)
    
    def format_file_size(self, size_bytes):
        """Convert bytes to human readable format."""
        if not size_bytes:
            return "Unknown"
        n = float(size_bytes)
        for unit in ('B', 'KB', 'MB', 'GB'):
            if n < 1024.0:
                return f"{n:.1f} {unit}"
            n /= 1024.0
        return f"{n:.1f} TB"
    
    def find_ffmpeg(self):
        """Find ffmpeg executable path with bundled support"""
        # C1 fix: check SCRIPT_DIR (next to the exe) BEFORE the PyInstaller
        # bundle.  _update_ffmpeg writes updates to SCRIPT_DIR because the
        # bundle (_MEIPASS/_internal) is treated as read-only, so the local
        # copy must win here or every launch re-detects the stale bundled
        # FFmpeg and the auto-updater re-downloads ~90 MB forever.
        local_ffmpeg = os.path.join(SCRIPT_DIR, "ffmpeg.exe")
        if os.path.exists(local_ffmpeg):
            print(f"Found local FFmpeg (script dir): {local_ffmpeg}")
            return local_ffmpeg

        # Check bundled location next (for PyInstaller)
        if getattr(sys, 'frozen', False):
            # Running as PyInstaller executable - check the extraction directory
            bundle_dir = getattr(sys, '_MEIPASS', os.path.dirname(sys.executable))
            bundled_ffmpeg = os.path.join(bundle_dir, "ffmpeg.exe")
            if os.path.exists(bundled_ffmpeg):
                print(f"Found bundled FFmpeg: {bundled_ffmpeg}")
                return bundled_ffmpeg
        
        # Check specific path
        specific_path = r"C:\ffmpeg\bin\ffmpeg.exe"
        if os.path.exists(specific_path):
            print(f"Found FFmpeg at specific path: {specific_path}")
            return specific_path
        
        # Check environment variable
        try:
            result = subprocess.run(['ffmpeg', '-version'],
                                capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=5,
                                creationflags=CREATE_NO_WINDOW)
            if result.returncode == 0:
                print("Found FFmpeg in system PATH")
                return 'ffmpeg'  # Available in PATH
        except (FileNotFoundError, subprocess.TimeoutExpired):
            pass
        
        print("FFmpeg not found in any location")
        return None
    
    def detect_audio_language(self, fmt):
        """Enhanced audio language detection"""
        # Check multiple possible language fields
        lang_fields = [
            'language',
            'language_preference', 
            'lang',
            'audio_lang',
            'subtitle_lang'
        ]
        
        detected_lang = None
        for field in lang_fields:
            value = fmt.get(field)
            if value and isinstance(value, str) and len(value) >= 2:
                detected_lang = value.lower()[:2]  # Get first 2 characters
                break
        
        # If no explicit language, try to infer from format info
        if not detected_lang:
            format_note = fmt.get('format_note', '').lower()
            format_id = str(fmt.get('format_id', '')).lower()
            
            # Common English indicators
            english_indicators = ['english', 'en', 'default', 'original']
            if any(indicator in format_note or indicator in format_id for indicator in english_indicators):
                detected_lang = 'en'
            
            # Check for other language indicators in format notes
            lang_map = {
                'spanish': 'es', 'español': 'es', 'esp': 'es',
                'french': 'fr', 'français': 'fr', 'fra': 'fr',
                'german': 'de', 'deutsch': 'de', 'ger': 'de',
                'italian': 'it', 'italiano': 'it', 'ita': 'it',
                'portuguese': 'pt', 'português': 'pt', 'por': 'pt',
                'russian': 'ru', 'русский': 'ru', 'rus': 'ru',
                'japanese': 'ja', '日本語': 'ja', 'jpn': 'ja',
                'korean': 'ko', '한국어': 'ko', 'kor': 'ko',
                'chinese': 'zh', '中文': 'zh', 'chi': 'zh'
            }
            
            for lang_name, lang_code in lang_map.items():
                if lang_name in format_note:
                    detected_lang = lang_code
                    break
        
        # Default fallback - assume English for common format IDs
        if not detected_lang:
            # YouTube's common English audio format IDs
            english_format_ids = ['140', '141', '171', '249', '250', '251']
            if str(fmt.get('format_id', '')) in english_format_ids:
                detected_lang = 'en'
            else:
                detected_lang = 'unknown'
        
        return detected_lang
    
    def get_audio_stream_description(self, fmt):
        """Get detailed description of audio stream"""
        lang = self.detect_audio_language(fmt)
        bitrate = fmt.get('abr', 0)
        codec = fmt.get('acodec', 'unknown')
        format_id = fmt.get('format_id', '')
        
        # Create description
        desc_parts = []
        if bitrate:
            desc_parts.append(f"{bitrate}kbps")
        if codec != 'unknown':
            desc_parts.append(codec.split('.')[0])  # Remove codec details
        if lang != 'unknown':
            desc_parts.append(f"({lang})")
        
        description = f"ID:{format_id} " + " ".join(desc_parts)
        return description, lang
    
    def format_duration(self, seconds):
        """Format duration in seconds to HH:MM:SS"""
        if not seconds:
            return "Unknown"
        
        hours = seconds // 3600
        minutes = (seconds % 3600) // 60
        seconds = seconds % 60
        
        if hours > 0:
            return f"{hours}:{minutes:02d}:{seconds:02d}"
        else:
            return f"{minutes}:{seconds:02d}"

    def _format_download_time(self, elapsed):
        """Format elapsed download time as '4.1s' or '2m 7.3s'."""
        if elapsed < 60:
            return str(round(elapsed, 1)) + "s"
        mins = int(elapsed) // 60
        secs = elapsed - mins * 60
        return str(mins) + "m " + str(round(secs, 1)) + "s"
    
    def analyze_video(self):
        """Validate the current URL entry and hand it to the analysis queue."""
        url = self.url_var.get().strip()

        if not url:
            self._notify_error("Error", "Please enter a YouTube URL")
            return

        if not self.is_valid_youtube_url(url) and not self.is_playlist_url(url):
            self._notify_error("Error", "Invalid YouTube URL format")
            return

        # Playlists use a separate worker - bypass the analysis queue entirely
        if self.is_playlist_url(url):
            thread = threading.Thread(target=self._handle_playlist_worker, args=(url,))
            thread.daemon = True
            thread.start()
            return

        # Inform user that analyzing while paused is safe - resume context is baked in
        if self._download_paused:
            proceed = messagebox.askyesno(
                "Download Paused",
                "A download is currently paused.\n\n"
                "You can analyze a new video and queue its download - "
                "the paused download will still be resumable.\n\n"
                "Analyze new video anyway?")
            if not proceed:
                return

        self._enqueue_url_for_analysis(url)

    def _toggle_batch_panel(self):
        """Show or hide the batch URL input panel."""
        if self._batch_panel_visible:
            self._batch_frame.grid_remove()
            self._batch_toggle_btn.config(text="Batch ▼")
            self._batch_panel_visible = False
        else:
            self._batch_frame.grid(row=5, column=0, columnspan=4,
                                   sticky=(tk.W, tk.E), pady=(4, 0))
            self._batch_toggle_btn.config(text="Batch ▲")
            self._batch_panel_visible = True

    def _batch_analyze_worker(self, urls):
        """Fetch video info for all URLs concurrently then process/enqueue each
        in original order on the main thread.

        Architecture:
          - A ThreadPoolExecutor fetches video info for up to
            batch_concurrent_fetches URLs in parallel (network-bound).
          - Results arrive out of order but are stored by index so that
            queue ordering is always preserved.
          - The main loop processes results in original order using the
            existing per-item done_evt handshake, leaving _update_video_info
            and the re-fetch logic completely unchanged.
        """
        total    = len(urls)
        success  = 0
        failed   = 0
        n_workers = max(1, min(8, getattr(self, 'batch_concurrent_fetches', 3)))
        self._batch_running = True

        # Pre-fetch all video infos concurrently - network-bound, safe to
        # parallelise.  results[i] = (info_dict, None) or (None, error_str).
        results    = [None] * total
        fetch_lock = threading.Lock()

        def _fetch_one(idx_url):
            idx, url = idx_url
            if getattr(self, '_batch_cancelled', False):
                return
            self.root.after(0, lambda: self.append_terminal_output(
                'Fetching video info...\n', 'info'))
            try:
                info = self.get_video_info(url)
                with fetch_lock:
                    results[idx] = (info, None)
            except Exception as ex:
                with fetch_lock:
                    results[idx] = (None, str(ex))

        self.root.after(0, lambda: self.progress_bar.start())
        with ThreadPoolExecutor(max_workers=n_workers) as pool:
            list(pool.map(_fetch_one, enumerate(urls)))
        self.root.after(0, lambda: self.progress_bar.stop())

        # Process results in original order on this (worker) thread.
        # Each item is handed to the main thread via root.after and then we
        # block on done_evt - identical to the previous sequential design so
        # all downstream logic (_update_video_info, re-fetch, etc.) is intact.
        for i, url in enumerate(urls):
            # C4: store index only - avoids O(N²) list allocation per iteration.
            # _on_close recovers the list via urls[self._batch_pending_start_idx:]
            self._batch_pending_start_idx = i
            self._batch_pending_urls_ref  = urls  # reference, not a copy

            if getattr(self, '_batch_cancelled', False):
                break

            self.root.after(0, lambda i=i, u=url:
                self.status_var.set(
                    'Batch ' + str(i + 1) + '/' + str(total) + ': ' + u[:60]))

            result = results[i]
            if result is None:
                # Cancelled before fetch completed
                failed += 1
                continue

            info, err = result
            if err is not None:
                failed += 1
                self.root.after(0, lambda e=err:
                    self.append_terminal_output(
                        'Batch error: ' + e + '\n', 'error'))
                continue

            # C3: start audio pre-fetch immediately using the resolved info dict.
            # Runs in a daemon thread so it overlaps with UI processing and the
            # remaining items in the queue. Only fires when audio mode is active
            # so it doesn't burn bandwidth on video+audio downloads that already
            # handle their own pre-caching via the pre-cache slot system.
            if getattr(self, '_m_audio_only', False):
                try:
                    _c3_fmts = info.get('formats') or []
                    _c3_vid_id = info.get('id', '')
                    # Resolve audio format using the same select_best_audio_stream
                    # logic so the bitrate preference is honoured here too.
                    _c3_audio_streams = [f for f in _c3_fmts
                                         if f.get('acodec') not in (None, 'none')
                                         and f.get('vcodec') in (None, 'none')]
                    _c3_detected_langs = {}
                    for _af in _c3_audio_streams:
                        _lang = _af.get('detected_language') or 'unknown'
                        _c3_detected_langs.setdefault(_lang, []).append(_af)
                    _c3_best = self.select_best_audio_stream(
                        _c3_audio_streams, _c3_detected_langs)
                    _c3_fmt_id = str(_c3_best.get('format_id', '')) if _c3_best else ''
                    if _c3_fmt_id and _c3_vid_id and self.audio_cache_dir:
                        if not self.get_cached_audio_path(_c3_vid_id, _c3_fmt_id):
                            def _c3_prefetch(vid_id=_c3_vid_id, fmt_id=_c3_fmt_id,
                                             _url=url):
                                try:
                                    _tmp = self._make_temp_dir('ysa_c3_')
                                    _aud_tmp = os.path.join(_tmp,
                                                            'audio_' + fmt_id + '.m4a')
                                    _aargs = [
                                        '--no-warnings', '-c',
                                        '--retries', '3', '--fragment-retries', '3',
                                        '--no-part', '-o', _aud_tmp, '-f', fmt_id,
                                    ]
                                    _aargs.extend(self.get_player_client_extractor_args())
                                    _aargs.extend(self.get_ytdlp_dns_args())
                                    if self.yt_dlp_cache_dir:
                                        _aargs.extend(['--cache-dir',
                                                        self.yt_dlp_cache_dir])
                                    _aargs.append(_url)
                                    _res = subprocess.run(
                                        self._ytdlp_head() + _aargs,
                                        capture_output=True, text=True, encoding='utf-8', errors='replace',
                                        timeout=3600,
                                        creationflags=CREATE_NO_WINDOW)
                                    if _res.returncode == 0:
                                        for _f in os.listdir(_tmp):
                                            if _f.startswith('audio_' + fmt_id):
                                                self.cache_audio_stream(
                                                    vid_id, fmt_id,
                                                    os.path.join(_tmp, _f))
                                                break
                                except Exception:
                                    pass
                                finally:
                                    shutil.rmtree(_tmp, ignore_errors=True)
                            threading.Thread(target=_c3_prefetch, daemon=True).start()
                except Exception:
                    pass

            try:
                done_evt = threading.Event()
                self._batch_item_done_evt = done_evt

                def _process(info=info, url=url, done_evt=done_evt):
                    try:
                        self.url_var.set(url)
                        self._auto_enqueue_done = False
                        self._update_video_info(info, url)
                    finally:
                        # Only unblock the batch loop immediately when no
                        # re-fetch is in flight.  If _analysis_done_mode is
                        # 'deferred' a background thread will set done_evt via
                        # _on_url_analysis_done.
                        if self._analysis_done_mode != 'deferred':
                            self._batch_item_done_evt = None
                            done_evt.set()

                self.root.after(0, _process)
                done_evt.wait(timeout=60)

                if self._auto_enqueue_done:
                    success += 1
                    if (i == 0
                            and getattr(self, '_batch_start_immediately', None)
                            and self._batch_start_immediately.get()):
                        self.root.after(0, lambda: (
                            self._start_next_queued()
                            if not self._download_active
                               and not self._download_paused
                            else None
                        ))
                else:
                    failed += 1
                    self.root.after(0, lambda u=url:
                        self.append_terminal_output(
                            'Batch skipped (no matching quality): '
                            + u + '\n', 'warning'))
            except Exception as ex:
                failed += 1
                self.root.after(0, lambda e=str(ex):
                    self.append_terminal_output(
                        'Batch error: ' + e + '\n', 'error'))

            # Small yield so root.after callbacks can drain between items
            time.sleep(0.05)

        def _finish():
            self._batch_running = False
            self._batch_pending_urls_ref  = []
            self._batch_pending_start_idx = 0
            msg = ('Batch complete: ' + str(success) + ' queued'
                   + (', ' + str(failed) + ' failed' if failed else ''))
            self.status_var.set(msg)
            self.append_terminal_output('\n' + msg + '\n', 'success')
            self._batch_queue_btn.config(state='normal',
                                         text='Analyze & Queue All')
            self._batch_cancel_btn.config(state='disabled')
            if not self._download_active and not self._download_paused:
                self._start_next_queued()

        self.root.after(0, _finish)


    def paste_and_analyze(self):
        """Paste URL from clipboard, analyze, and auto-download at the configured quality."""
        try:
            self.status_var.set("Getting URL from clipboard...")

            clipboard_content = self.root.clipboard_get().strip()

            if not clipboard_content:
                self._notify_warning("Warning", "Clipboard is empty")
                self.status_var.set("Ready")
                return

            if not self.is_valid_youtube_url(clipboard_content) and not self.is_playlist_url(clipboard_content):
                self._notify_error("Error", "Clipboard does not contain a valid YouTube URL")
                self.status_var.set("Ready")
                return

            # Set URL and analyze - auto-download fires automatically after analysis completes
            self.url_var.set(clipboard_content)
            self.status_var.set("Analyzing and preparing download...")
            self.analyze_video()
            
        except tk.TclError:
            self._notify_error("Error", "Could not access clipboard")
            self.status_var.set("Ready")
        except Exception as e:
            self._notify_error("Error", f"Error pasting URL: {str(e)}")
            self.status_var.set("Ready")
    
    def on_paste_to_entry(self, event):
        """Handle paste into URL entry - silently analyze and auto-download on paste."""
        try:
            clipboard_content = self.root.clipboard_get().strip()
            if (self.is_valid_youtube_url(clipboard_content)
                    or self.is_playlist_url(clipboard_content)):
                # Slight delay so the pasted text lands in the Entry first
                self.root.after(100, self.analyze_video)
        except Exception:
            pass  # Ignore clipboard errors
        return None  # Let the default paste happen
    
    def show_context_menu(self, event):
        """Show context menu on right-click"""
        context_menu = tk.Menu(self.root, tearoff=0)
        context_menu.add_command(label="Paste", command=lambda: self.url_entry.event_generate('<<Paste>>'))
        context_menu.add_command(label="Paste & Download", command=self.paste_and_analyze)
        context_menu.add_separator()
        context_menu.add_command(label="Clear", command=lambda: self.url_var.set(""))
        
        # Add analyze option if URL is present
        current_url = self.url_var.get().strip()
        if current_url and self.is_valid_youtube_url(current_url):
            context_menu.add_separator()
            context_menu.add_command(label="Analyze Current URL", command=self.analyze_video)
        
        try:
            context_menu.tk_popup(event.x_root, event.y_root)
        finally:
            context_menu.grab_release()
    
    def _enqueue_url_for_analysis(self, url):
        """Add a URL to the sequential analysis queue.
        If the analyser is idle the URL is processed immediately.
        If it is busy the URL is appended and a 'queued' notice is printed.
        Duplicates already in the analysis queue, currently being analyzed,
        already in the download queue, or currently being downloaded are dropped."""
        # Already waiting to be analyzed
        if url in self._url_analysis_queue:
            return
        # Currently being analyzed right now
        if url == self._currently_analyzing_url:
            return
        # Already sitting in the download queue
        with self._queue_lock:
            _in_queue = any(e.get('url', '') == url for e in self._download_queue)
        if _in_queue:
            return
        # Currently being actively downloaded (popped from queue, thread running)
        if url == self._currently_downloading_url:
            return
        if self._url_analysis_busy:
            pos = len(self._url_analysis_queue) + 1
            self.append_terminal_output(
                'Analysis queued (#' + str(pos) + '): ' + url[:60] + '\n', 'info')
            # Eagerly prefetch this URL's info in the background so it's
            # ready by the time the worker gets to it.
            if url not in self._prefetched_info and url not in self._prefetch_in_progress:
                threading.Thread(
                    target=self._prefetch_video_info,
                    args=(url,), daemon=True).start()
        self._url_analysis_queue.append(url)
        if not self._url_analysis_busy:
            self._process_next_url_analysis()

    def _process_next_url_analysis(self):
        """Pop the next URL from the analysis queue and start the worker thread.
        Must be called on the main thread only."""
        if not self._url_analysis_queue or self._url_analysis_busy:
            return
        url = self._url_analysis_queue.pop(0)
        self._url_analysis_busy = True
        self._currently_analyzing_url = url
        self.url_var.set(url)
        self.paste_btn.config(state='disabled')
        self.progress_bar.start()
        self.progress_var.set('Analyzing video...')
        self.status_var.set('Fetching video information...')
        thread = threading.Thread(target=self._analyze_video_worker, args=(url,), daemon=True)
        thread.start()

    def _on_url_analysis_done(self):
        """Called on the main thread when an analysis finishes (success or error).
        Clears the busy flag and immediately starts the next queued URL if one exists."""
        self._url_analysis_busy = False
        self._currently_analyzing_url = ''
        # Unblock the batch worker if it is waiting for a re-fetch to complete.
        if self._batch_item_done_evt is not None:
            self._batch_item_done_evt.set()
            self._batch_item_done_evt = None
        if self._url_analysis_queue:
            self._process_next_url_analysis()

    def _analyze_video_worker(self, url):
        """Worker function for video analysis. Silently retries up to 2 extra
        times if the result looks truncated (only a single 360p stream returned),
        which can happen when YouTube's CDN hasn't fully propagated a fresh upload.

        After posting the result, prefetches the next queued URL so the yt-dlp
        call overlaps with the current video's UI processing on the main thread."""
        MAX_RETRIES = 2
        try:
            self.root.after(0, lambda: self.append_terminal_output("Fetching video info...\n", "info"))

            # Check if this URL was already prefetched by a background thread
            info = self._prefetched_info.pop(url, None)
            if info is None and url in self._prefetch_in_progress:
                # Prefetch is in flight - wait briefly for it to finish
                # rather than starting a redundant yt-dlp process
                for _wait in range(25):  # up to 5 s in 200 ms ticks
                    time.sleep(0.2)
                    info = self._prefetched_info.pop(url, None)
                    if info is not None:
                        break
                    if url not in self._prefetch_in_progress:
                        # Prefetch finished but failed - fall through to fresh fetch
                        break
            if info is not None:
                self.root.after(0, lambda: self.append_terminal_output(
                    "Using prefetched analysis result.\n", "cache"))
            else:
                info = self.get_video_info(url)

            for attempt in range(MAX_RETRIES):
                formats = info.get('formats', [])
                heights = [f.get('height', 0) for f in formats if f.get('vcodec') not in (None, 'none')]
                max_height = max(heights) if heights else 0
                # Looks truncated: only one distinct resolution and it's ≤360p
                unique_heights = set(h for h in heights if h)
                if len(unique_heights) <= 1 and max_height <= 360:
                    self.root.after(0, lambda a=attempt: self.append_terminal_output(
                        "Only 360p detected - retrying (" + str(a + 1) + "/" + str(MAX_RETRIES) + ")...\n", "info"))
                    import time as _time
                    _time.sleep(2)
                    info = self.get_video_info(url)
                else:
                    break

            # Post the result to the main thread for UI processing
            self.root.after(0, lambda i=info, u=url: self._update_video_info(i, u))

            # ── Prefetch lookahead ─────────────────────────────────────────
            # While the main thread is busy processing the UI for the current
            # video, use this worker thread to fetch info for the next queued
            # URL.  This overlaps the 2-5 s yt-dlp call with UI work so the
            # next analysis starts near-instantly.
            self._prefetch_next_queued_url()

        except Exception as e:
            error_msg = str(e)
            self.root.after(0, lambda m=error_msg: self.append_terminal_output("ERROR: " + m + "\n", "error"))
            # Do not show a blocking dialog here - it would stall the analysis queue.
            # The error is visible in the terminal output above.
            self.root.after(0, self._on_url_analysis_done)

    def _prefetch_video_info(self, url):
        """Fetch video info for a URL and store in the prefetch cache.
        Safe to call from any thread.  Failures are silently ignored
        since the worker will fetch normally if no cache entry exists."""
        if url in self._prefetched_info or url in self._prefetch_in_progress:
            return
        self._prefetch_in_progress.add(url)
        try:
            info = self.get_video_info(url)
            self._prefetched_info[url] = info
        except Exception:
            pass
        finally:
            self._prefetch_in_progress.discard(url)

    def _prefetch_next_queued_url(self):
        """Prefetch the next URL in the analysis queue.
        Called from the worker thread after posting the current result."""
        if not self._url_analysis_queue:
            return
        next_url = self._url_analysis_queue[0]
        self._prefetch_video_info(next_url)
    
    def _update_video_info(self, info, url=None):
        """Update UI with video information"""
        # Reset the analysis-done mode for this analysis cycle.
        # 'pending'  → finally block calls _on_url_analysis_done normally.
        # 'deferred' → a re-fetch thread is in-flight; finally must NOT advance
        #              the queue (the thread will call _on_url_analysis_done itself).
        self._analysis_done_mode = 'pending'
        try:
            # Store the URL that was analyzed so queue entries always snapshot the
            # correct URL - clipboard watch may have already overwritten url_var by
            # the time this callback fires on the main thread.
            self.current_video_url = url or self.url_var.get().strip()

            # Store video info and formats
            self.current_video_info = info
            self.current_formats = info.get('formats', [])

            # ── One-time categorisation and language detection ──────────────
            # Store pre-split lists so _populate_streams and
            # _populate_recommended_combinations don't repeat this work.
            video_only, audio_only, combined = [], [], []
            detected_languages = {}
            for fmt in self.current_formats:
                has_video = fmt.get('vcodec') not in (None, 'none')
                has_audio = fmt.get('acodec') not in (None, 'none')
                if has_video and not has_audio:
                    video_only.append(fmt)
                elif has_audio and not has_video:
                    # Run language detection once and cache result on the dict
                    if 'detected_language' not in fmt:
                        description, lang = self.get_audio_stream_description(fmt)
                        fmt['detected_language'] = lang
                        fmt['description'] = description
                    lang = fmt['detected_language']
                    detected_languages.setdefault(lang, []).append(fmt)
                    audio_only.append(fmt)
                elif has_video and has_audio:
                    if 'detected_language' not in fmt:
                        description, lang = self.get_audio_stream_description(fmt)
                        fmt['detected_language'] = lang
                        fmt['description'] = description
                    combined.append(fmt)

            # Sort once here so _populate_streams and _populate_recommended
            # can iterate directly without re-sorting on every refresh.
            # Secondary sort by vbr so streams at the same resolution are ordered
            # highest-bitrate first - required for the video bitrate cap to work correctly.
            self._video_streams    = sorted(video_only,   key=lambda x: (x.get('height', 0), x.get('vbr', 0) or x.get('tbr', 0)), reverse=True)
            self._audio_streams    = sorted(audio_only,   key=lambda x: x.get('abr', 0),    reverse=True)
            self._combined_streams = sorted(combined,     key=lambda x: x.get('height', 0), reverse=True)
            self._detected_languages = detected_languages
            # ────────────────────────────────────────────────────────────────

            # Update video information labels
            title = info.get('title', 'Unknown Title')
            uploader = info.get('uploader', 'Unknown')
            duration = self.format_duration(info.get('duration', 0))
            view_count = "{:,}".format(info.get('view_count', 0)) if info.get('view_count') else "Unknown"
            upload_date = info.get('upload_date', 'Unknown')
            if upload_date != 'Unknown' and len(upload_date) == 8:
                upload_date = upload_date[:4] + "-" + upload_date[4:6] + "-" + upload_date[6:]

            _info_fg = '#e0e0e0' if self.dark_mode else 'black'
            self.info_labels['title'].config(text=title, foreground=_info_fg)
            self.info_labels['uploader'].config(text=uploader, foreground=_info_fg)
            self.info_labels['duration'].config(text=duration, foreground=_info_fg)
            self.info_labels['views'].config(text=view_count, foreground=_info_fg)
            self.info_labels['upload_date'].config(text=upload_date, foreground=_info_fg)

            # Populate stream tables
            self._populate_streams()

            # Initial population - don't preserve selection, default to English
            # Use pre-computed _detected_languages from above - no re-scan needed
            if self.current_formats:
                self.update_language_options(self._detected_languages, preserve_selection=False)
            
            # Reset auto-enqueue guard so the new video's default quality gets queued once
            self._auto_enqueue_done = False
            self._populate_recommended_combinations()

            # ── Report available subtitle languages in terminal ───────────────
            _avail_manual  = set(info.get('subtitles', {}).keys())
            _auto_captions = info.get('automatic_captions', {})
            # Filter out non-language keys (live_chat, etc.)
            _avail_manual = {c for c in _avail_manual if len(c) <= 5 and 'live_chat' not in c}
            _all_auto = {c for c in _auto_captions.keys() if 'live_chat' not in c}
            # Keys ending in '-orig' identify the native ASR language YouTube transcribed from speech.
            # Everything else is machine-translated from that source - downloadable but not genuine.
            _native_auto = {c.replace('-orig', '') for c in _all_auto if c.endswith('-orig')}
            if not _native_auto:
                # Fallback: use video language field if -orig key absent
                _vid_lang = (info.get('language') or '')[:2]
                if _vid_lang and _vid_lang in _all_auto:
                    _native_auto = {_vid_lang}
            _translated_count = len({c for c in _all_auto
                                      if c not in _native_auto and not c.endswith('-orig') and len(c) <= 5})
            _sub_lines = []
            if _avail_manual:
                _sub_lines.append('Manual: ' + ', '.join(sorted(_avail_manual)))
            if _native_auto:
                _sub_lines.append('Auto (native): ' + ', '.join(sorted(_native_auto)))
            if _translated_count:
                _sub_lines.append('Auto (machine-translated): ' + str(_translated_count) + ' langs - downloadable but not genuine')
            if _sub_lines:
                for _sl in _sub_lines:
                    self.append_terminal_output('Subtitles - ' + _sl + '\n', 'cache')
            else:
                self.append_terminal_output('No subtitles available for this video.\n', 'warning')
            # ────────────────────────────────────────────────────────────────

            # Enable buttons
            self.copy_info_btn.config(state='normal')
            self.debug_btn.config(state='normal')
            self.download_merge_btn.config(state='normal')
            if hasattr(self, 'preview_btn'):
                self.preview_btn.config(state='normal')
            
            self.status_var.set(f"Analysis complete. Found {len(self.current_formats)} streams.")
            
        except Exception as e:
            # Print to terminal rather than showing a blocking modal dialog.
            # A modal grabs focus and prevents the clipboard poll from firing,
            # which means URLs copied while the dialog is open are permanently lost.
            self.append_terminal_output("Error updating interface: " + str(e) + "\n", 'error')
        finally:
            self.progress_bar.stop()
            self.progress_var.set("Ready")
            self.paste_btn.config(state='normal')
            
            # Show status with cache info
            status_parts = ["Ready"]
            if not self.ffmpeg_path:
                status_parts.append("FFmpeg not found")
            if not self.video_cache_dir:
                status_parts.append("Video caching disabled")
            elif self.cached_videos:
                cached_count = sum(len(formats) for formats in self.cached_videos.values())
                status_parts.append(f"{cached_count} videos cached")
            
            self.status_var.set(" - ".join(status_parts))
            # Only advance the analysis queue here when no re-fetch thread is in-flight.
            # When _analysis_done_mode == 'deferred', _auto_download_best_quality has
            # already spawned a background re-fetch thread that will call
            # _on_url_analysis_done itself once the download is enqueued - preserving
            # the order in which URLs were copied.
            if self._analysis_done_mode != 'deferred':
                self._on_url_analysis_done()

    def _populate_streams(self):
        """Populate all stream treeviews using pre-categorised stream lists."""
        # Clear existing items
        for tree_name in ('combined_tree', 'video_tree', 'audio_tree', 'all_tree'):
            tree = getattr(self, tree_name)
            for item in tree.get_children():
                tree.delete(item)

        # Pre-sorted once in _update_video_info - use directly
        combined_streams = getattr(self, '_combined_streams', [])
        video_streams    = getattr(self, '_video_streams', [])
        audio_streams    = getattr(self, '_audio_streams', [])

        # Populate combined streams
        for fmt in combined_streams:
            quality   = (str(fmt.get('height', '?')) + "p") if fmt.get('height') else 'Audio'
            container = fmt.get('ext', 'unknown')
            size      = self.format_file_size(fmt.get('filesize'))
            vcodec    = fmt.get('vcodec', 'unknown')[:15]
            acodec    = fmt.get('acodec', 'unknown')[:15]
            fps       = str(fmt.get('fps', '?'))
            format_id = str(fmt.get('format_id', ''))
            self.combined_tree.insert('', 'end', values=(quality, container, size, vcodec, acodec, fps, format_id))

        # Populate video-only streams
        for fmt in video_streams:
            quality   = (str(fmt.get('height', '?')) + "p") if fmt.get('height') else 'Unknown'
            container = fmt.get('ext', 'unknown')
            size      = self.format_file_size(fmt.get('filesize'))
            bitrate   = (str(fmt.get('vbr', '?')) + " kbps") if fmt.get('vbr') else 'Unknown'
            codec     = fmt.get('vcodec', 'unknown')[:15]
            fps       = str(fmt.get('fps', '?'))
            format_id = str(fmt.get('format_id', ''))
            self.video_tree.insert('', 'end', values=(quality, container, size, bitrate, codec, fps, format_id))

        # Populate audio-only streams
        for fmt in audio_streams:
            quality     = (str(fmt.get('abr', '?')) + " kbps") if fmt.get('abr') else 'Unknown'
            container   = fmt.get('ext', 'unknown')
            size        = self.format_file_size(fmt.get('filesize'))
            bitrate     = (str(fmt.get('abr', '?')) + " kbps") if fmt.get('abr') else 'Unknown'
            codec       = fmt.get('acodec', 'unknown')[:15]
            sample_rate = (str(fmt.get('asr', '?')) + " Hz") if fmt.get('asr') else 'Unknown'
            format_id   = str(fmt.get('format_id', ''))
            self.audio_tree.insert('', 'end', values=(quality, container, size, bitrate, codec, sample_rate, format_id))

        # Populate all-streams tab
        for fmt in combined_streams:
            quality   = (str(fmt.get('height', '?')) + "p") if fmt.get('height') else 'Audio'
            container = fmt.get('ext', 'unknown')
            size      = self.format_file_size(fmt.get('filesize'))
            vcodec    = fmt.get('vcodec', 'none')[:15] if fmt.get('vcodec') != 'none' else 'none'
            acodec    = fmt.get('acodec', 'none')[:15] if fmt.get('acodec') != 'none' else 'none'
            format_id = str(fmt.get('format_id', ''))
            self.all_tree.insert('', 'end', values=("Combined", quality, container, size, vcodec, acodec, format_id))

        for fmt in video_streams:
            quality   = (str(fmt.get('height', '?')) + "p") if fmt.get('height') else 'Unknown'
            container = fmt.get('ext', 'unknown')
            size      = self.format_file_size(fmt.get('filesize'))
            vcodec    = fmt.get('vcodec', 'none')[:15] if fmt.get('vcodec') != 'none' else 'none'
            format_id = str(fmt.get('format_id', ''))
            self.all_tree.insert('', 'end', values=("Video", quality, container, size, vcodec, 'none', format_id))

        for fmt in audio_streams:
            quality   = (str(fmt.get('abr', '?')) + " kbps") if fmt.get('abr') else 'Unknown'
            container = fmt.get('ext', 'unknown')
            size      = self.format_file_size(fmt.get('filesize'))
            acodec    = fmt.get('acodec', 'none')[:15] if fmt.get('acodec') != 'none' else 'none'
            format_id = str(fmt.get('format_id', ''))
            self.all_tree.insert('', 'end', values=("Audio", quality, container, size, 'none', acodec, format_id))
    
    def _stream_size_bytes(self, fmt, duration=None):
        """Best available size for one stream, in bytes (0 if truly unknown).

        Three tiers, because YouTube supplies different ones per protocol:
          1. filesize        - exact; DASH/https formats carry it
          2. filesize_approx - yt-dlp's own estimate, the '~' in -F output
          3. bitrate x duration - computed here, because HLS/m3u8 formats
             frequently carry NEITHER of the above. Those are exactly the
             streams a 'highest bitrate' setting selects, so without this
             tier the best rows were the ones showing no size at all.

        kbit/s x seconds / 8 x 1000 = bytes, i.e. x125.
        """
        try:
            n = fmt.get('filesize') or fmt.get('filesize_approx')
            if n:
                return int(n)
            br = fmt.get('tbr') or fmt.get('vbr') or fmt.get('abr')
            if duration is None:
                duration = (self.current_video_info or {}).get('duration')
            if br and duration:
                return int(float(br) * float(duration) * 125.0)
        except (TypeError, ValueError, AttributeError):
            pass
        return 0

    def _populate_recommended_combinations(self, suppress_auto_download=False):
        """Populate recommended video+audio combinations with cache awareness"""
        if not hasattr(self, 'recommended_tree'):
            return
        # Guard against re-entrant calls: update_language_options calls
        # language_var.set() which on some Tk/Windows versions fires
        # <<ComboboxSelected>> → on_language_change → back here, before
        # this call has finished populating DASH rows.  The second call
        # would clear the tree and auto-download a partial (combined-only)
        # result, producing the "only 360p on first boot" symptom.
        if getattr(self, '_populating_recommended', False):
            return
        self._populating_recommended = True
        try:
            self._populate_recommended_combinations_inner(suppress_auto_download=suppress_auto_download)
        finally:
            self._populating_recommended = False

    def _populate_recommended_combinations_inner(self, suppress_auto_download=False):
        """Inner implementation - called only from _populate_recommended_combinations."""
        for item in self.recommended_tree.get_children():
            self.recommended_tree.delete(item)

        video_id = self.current_video_info.get('id', 'unknown')

        # Pre-sorted once in _update_video_info - use directly
        detected_languages = getattr(self, '_detected_languages', {})
        video_streams      = getattr(self, '_video_streams', [])
        combined_streams   = getattr(self, '_combined_streams', [])
        audio_streams      = getattr(self, '_audio_streams', [])

        # Update language dropdown (preserve current selection when called after initial load)
        self.update_language_options(detected_languages, preserve_selection=True)

        best_audio = self.select_best_audio_stream(audio_streams, detected_languages)

        # Combined streams (direct download, no merge needed)
        # Skip HLS/m3u8 streams — they are live-stream variants with unknown
        # sizes and duplicate resolutions already covered by DASH streams.
        # With the JS runtime enabled, yt-dlp's web_safari client returns
        # these HLS formats which were previously absent.
        for fmt in combined_streams:
            proto = (fmt.get('protocol') or '').lower()
            if 'm3u8' in proto:
                continue
            _h = fmt.get('height', 0) or 0
            _w = fmt.get('width', 0) or 0
            _eff = min(_h, _w) if _h and _w else (_h or _w)
            quality    = (str(_eff) + "p") if _eff else 'Audio'
            video_info = "Direct: " + fmt.get('ext', 'unknown') + " (" + str(fmt.get('format_id', '')) + ")"
            lang       = fmt.get('detected_language', 'unknown')
            audio_info = ("Built-in (" + lang + ")") if lang != 'unknown' else "Built-in"
            size       = self.format_file_size(fmt.get('filesize'))
            tag        = 'direct_en' if lang == 'en' else ('direct_other' if lang != 'unknown' else 'direct')
            self.recommended_tree.insert('', 'end',
                values=(quality, video_info, audio_info, size, "Single file - ready to use"),
                tags=(tag,))

        # Video+audio combinations for DASH quality levels.
        # Same rule the combined-stream loop above already applies: HLS
        # variants duplicate resolutions the DASH streams already cover,
        # and their sizes are manifest claims rather than measurements.
        # Guarded - if a video somehow offers ONLY HLS, keep them rather
        # than show an empty list.
        if not getattr(self, 'include_hls_streams', False):
            _dash_only = [v for v in video_streams
                          if 'm3u8' not in (v.get('protocol') or '').lower()]
            if _dash_only:
                video_streams = _dash_only
        def _eff_quality(v):
            h = v.get('height', 0) or 0
            w = v.get('width', 0) or 0
            return min(h, w) if h and w else (h or w)

        # Dynamically collect the actual unique resolutions present in the
        # video's DASH streams.  This handles non-standard encodes (e.g.
        # 1086p, 1628p, 814p) that a hardcoded list would miss entirely.
        # The tree shows the real resolution for accuracy; auto-download
        # and Smart Quality use _nearest_standard_quality to map these to
        # the closest standard tier when the user's setting is a standard
        # value like "1080p".
        _est_rows = 0   # rows whose size is a bitrate estimate, not measured
        seen_qualities = set()
        quality_order = []  # unique _eff values, highest first
        for v in sorted(video_streams, key=lambda x: _eff_quality(x), reverse=True):
            eff = _eff_quality(v)
            if eff > 0 and eff not in seen_qualities:
                seen_qualities.add(eff)
                quality_order.append(eff)

        for target_quality in quality_order:
            candidates = [v for v in video_streams if _eff_quality(v) == target_quality]
            best_video = self.select_best_video_stream(candidates)
            if not (best_video and best_audio):
                continue

            video_format_id = str(best_video.get('format_id', ''))
            audio_format_id = str(best_audio.get('format_id', ''))

            video_cached = self.get_cached_video_path(video_id, video_format_id) is not None
            audio_cached = self.get_cached_audio_path(video_id, audio_format_id) is not None
            both_cached  = video_cached and audio_cached

            cache_indicator = ("🗂️🎵 " if both_cached else
                               "🗂️ "   if video_cached else
                               "🎵 "   if audio_cached else "")

            # HLS/m3u8 formats often carry neither filesize nor
            # filesize_approx, and those are precisely the streams a
            # 'highest bitrate' setting picks - so the best rows were the
            # ones reading 'Video only' with no figure at all.
            _dur = (self.current_video_info or {}).get('duration')
            video_size  = self._stream_size_bytes(best_video, _dur)
            audio_size  = self._stream_size_bytes(best_audio, _dur)
            # A number the user cannot tell is a guess is worse than no
            # number: a row read 2.1 GB and delivered 543 MB. Only an
            # exact filesize on BOTH streams may be shown unmarked.
            _exact = bool(best_video.get('filesize')) and bool(best_audio.get('filesize'))
            _approx = '' if _exact else '~'
            if not _exact:
                _est_rows += 1
            video_info  = (best_video.get('ext', 'unknown') + " " +
                           best_video.get('vcodec', '')[:10] + " (" + video_format_id + ")")
            audio_info  = best_audio.get('ext', 'unknown') + " " + best_audio.get('description', 'unknown')

            if both_cached:
                size_str = "Fully cached"
            elif self.audio_only_mode.get():
                # Audio Only mode: show just audio stream size
                size_str = ("~" + self.format_file_size(audio_size)) if audio_size else "Audio only"
            elif video_cached:
                size_str = ("~" + self.format_file_size(audio_size)) if audio_size else "Audio only"
            elif audio_cached:
                size_str = ("~" + self.format_file_size(video_size)) if video_size else "Video only"
            else:
                total = video_size + audio_size
                size_str = ((_approx + self.format_file_size(total))
                            if total else "Unknown")

            selected_lang = best_audio.get('detected_language', 'unknown')
            lang_name     = self.get_language_name(selected_lang)
            bitrate       = best_audio.get('abr', '?')

            if both_cached:
                instructions = cache_indicator + "Both cached - merge only"
                tag = 'combination_both_cached'
            elif video_cached:
                instructions = (cache_indicator + "Video cached - audio only (" +
                                lang_name + " " + str(bitrate) + "kbps)")
                tag = 'combination_cached'
            elif audio_cached:
                instructions = cache_indicator + "Audio cached - video only"
                tag = 'combination_audio_cached'
            elif selected_lang == 'en':
                instructions = (cache_indicator + "Download + merge - English audio (" +
                                str(bitrate) + "kbps)")
                tag = 'combination_en'
            elif selected_lang == self.preferred_language:
                instructions = (cache_indicator + "Download + merge - " +
                                lang_name + " audio (" + str(bitrate) + "kbps)")
                tag = 'combination_selected'
            else:
                instructions = (cache_indicator + "Download + merge - " +
                                lang_name + " audio (" + str(bitrate) + "kbps)")
                tag = 'combination_other'

            self.recommended_tree.insert('', 'end',
                values=(str(target_quality) + "p", video_info, audio_info, size_str, instructions),
                tags=(tag,))

        # Auto-download best available quality if configured (fires once per fresh analysis)
        if not suppress_auto_download:
            self._auto_download_best_quality()

    def select_best_video_stream(self, candidates):
        """Choose the best video stream from a list of streams at the same resolution.
        Respects preferred_video_bitrate: picks the highest-bitrate stream whose vbr
        (or tbr as fallback) is at or below the cap.  When no stream qualifies, or the
        cap is 0 (disabled), returns the highest-bitrate stream in the pool."""
        if not candidates:
            return None
        limit = getattr(self, 'preferred_video_bitrate', 0)

        def _vbr(s):
            """Bitrate in kbps, or None when the source did not report one.

            This used to end in "or 0", which made an UNMEASURED stream
            look like the worst one in the pool. A cap of 1 then selected
            exactly those unmeasured formats while a cap of 0 ignored them
            entirely - which is how "maximum bitrate" ended up returning
            something smaller than "minimum bitrate". Unknown is now
            unknown: ranked last, never mistaken for lowest, and never
            excluded outright so a pool with no bitrate data still
            resolves to a real stream.
            """
            v = s.get('vbr') or s.get('tbr')
            try:
                return float(v) if v else None
            except (TypeError, ValueError):
                return None

        known = [s for s in candidates if _vbr(s) is not None]

        def _key(s):
            return _vbr(s) or 0.0

        if limit and limit > 0:
            under = [s for s in known if _vbr(s) <= limit]
            if under:
                return max(under, key=_key)
            if known:
                # Everything measured exceeds the cap - take the lowest
                # measured stream, the closest to what was asked for.
                return min(known, key=_key)
            # Nothing carries a bitrate at all: fall back rather than fail.
            return candidates[0]
        if known:
            return max(known, key=_key)
        return candidates[0]

    def select_best_audio_stream(self, audio_streams, detected_languages):
        """Select the best audio stream based on user preference.

        Fallback chain (never breaks, always returns something):
          1. Specific format id: (manual pick from main window dropdown)
          2. Preferred language  (from settings)
          3. English             (always tried next)
          4. Likely-English IDs  (YouTube well-known audio format IDs)
          5. Default/original    (format_note heuristic)
          6. Highest quality available (last resort)

        When preferred_audio_bitrate > 0, the stream whose bitrate is closest
        to (but not exceeding) that value is preferred within each step's pool.
        If no stream is at or below the limit the step falls through normally.
        """
        if not audio_streams:
            return None

        def _pick(pool):
            """Return best stream from pool, respecting bitrate preference."""
            if not pool:
                return None
            # DRC variants (format ids like '249-drc') are YouTube's
            # loudness-compressed renditions - audibly flatter than the
            # normal stream, so they are avoided unless asked for.
            _drc = getattr(self, 'audio_drc_pref', 'avoid')
            if _drc in ('avoid', 'prefer'):
                _want_plain = (_drc == 'avoid')
                _sub = [s for s in pool
                        if ('drc' not in str(s.get('format_id', '')).lower()) == _want_plain]
                if _sub:
                    pool = _sub
            limit = getattr(self, 'preferred_audio_bitrate', 0)
            if limit and limit > 0:
                under = [s for s in pool if (s.get('abr') or 0) <= limit]
                if under:
                    return max(under, key=lambda x: x.get('abr', 0))
                # All streams exceed the limit - pick the lowest available
                # (closest to what the user requested) rather than the highest.
                return min(pool, key=lambda x: x.get('abr', 0))
            return max(pool, key=lambda x: x.get('abr', 0))

        # ── Step 1: Specific format ID ────────────────────────────────────────
        if self.preferred_language.startswith("id:"):
            target_id = self.preferred_language[3:]
            for stream in audio_streams:
                if str(stream.get('format_id', '')) == target_id:
                    return stream
            # ID not found in this video - fall through silently to language matching
            self.append_terminal_output(
                'Note: saved stream id:' + target_id + ' not found for this video, '
                'falling back to preferred language.\n', 'info')

        # ── Step 2: Preferred language (if not English - English handled in step 3) ─
        if self.preferred_language not in ('en', '') and not self.preferred_language.startswith("id:"):
            preferred_streams = detected_languages.get(self.preferred_language, [])
            result = _pick(preferred_streams)
            if result:
                return result
            # Not found - fall through to English

        # ── Step 3: English ────────────────────────────────────────────────────
        english_streams = detected_languages.get('en', [])
        result = _pick(english_streams)
        if result:
            return result

        # ── Step 4 + 5: Heuristic English detection ───────────────────────────
        # YouTube common English audio format IDs, plus note-based indicators
        _known_en_ids = {'140', '141', '171', '249', '250', '251'}
        _en_notes     = ('default', 'original', 'primary')
        likely_english = [
            s for s in audio_streams
            if str(s.get('format_id', '')) in _known_en_ids
            or any(ind in s.get('format_note', '').lower() for ind in _en_notes)
        ]
        result = _pick(likely_english)
        if result:
            return result

        # ── Step 6: Last resort - highest quality regardless of language ───────
        return _pick(audio_streams)
    
    def get_language_name(self, lang_code):
        """Convert language code to readable name"""
        lang_names = {
            'en': 'English', 'es': 'Spanish', 'fr': 'French', 'de': 'German',
            'it': 'Italian', 'pt': 'Portuguese', 'ru': 'Russian', 'ja': 'Japanese',
            'ko': 'Korean', 'zh': 'Chinese', 'ar': 'Arabic', 'hi': 'Hindi',
            'th': 'Thai', 'tr': 'Turkish', 'pl': 'Polish', 'nl': 'Dutch',
            'unknown': 'Unknown'
        }
        return lang_names.get(lang_code, lang_code.upper())
    
    def update_language_options(self, detected_languages, preserve_selection=True):
        """Update language dropdown with English-first approach and manual options"""
        # Remember current selection before updating options
        current_selection = self.language_var.get() if preserve_selection else None
        current_lang = self.preferred_language if preserve_selection else "en"
        
        options = []
        
        # Always start with English as primary option
        english_streams = detected_languages.get('en', [])
        if english_streams:
            best_english_bitrate = max(stream.get('abr', 0) for stream in english_streams)
            options.append(f"en (English - Best Quality: {best_english_bitrate}kbps)")
        else:
            # No English detected, but still offer it as option
            options.append("en (English - Auto-detect)")
        
        # Add other detected languages as alternatives (only if they exist)
        lang_names = {
            'es': 'Spanish', 'fr': 'French', 'de': 'German',
            'it': 'Italian', 'pt': 'Portuguese', 'ru': 'Russian', 'ja': 'Japanese',
            'ko': 'Korean', 'zh': 'Chinese', 'ar': 'Arabic', 'hi': 'Hindi',
            'th': 'Thai', 'tr': 'Turkish', 'pl': 'Polish', 'nl': 'Dutch'
        }
        
        # Add other languages found (excluding English and unknown)
        other_langs = sorted([lang for lang in detected_languages.keys() if lang not in ['en', 'unknown']])
        for lang_code in other_langs:
            streams = detected_languages[lang_code]
            best_bitrate = max(stream.get('abr', 0) for stream in streams)
            lang_name = lang_names.get(lang_code, lang_code.upper())
            options.append(f"{lang_code} ({lang_name} - {len(streams)} streams, best: {best_bitrate}kbps)")
        
        # Add manual format ID selection for detected audio streams (advanced users)
        if detected_languages:
            options.append("--- Manual Stream Selection ---")
            all_audio = []
            for streams in detected_languages.values():
                all_audio.extend(streams)
            
            # Sort by quality (bitrate) descending, English first
            english_audio = [s for s in all_audio if s.get('detected_language') == 'en']
            other_audio = [s for s in all_audio if s.get('detected_language') != 'en']
            
            english_audio.sort(key=lambda x: x.get('abr', 0), reverse=True)
            other_audio.sort(key=lambda x: x.get('abr', 0), reverse=True)
            
            # Add English streams first
            for stream in english_audio:
                format_id = stream.get('format_id', '')
                description = stream.get('description', '')
                options.append(f"id:{format_id} ({description} - English)")
            
            # Then add other language streams
            for stream in other_audio:
                format_id = stream.get('format_id', '')
                description = stream.get('description', '')
                lang = stream.get('detected_language', 'unknown')
                lang_name = self.get_language_name(lang)
                options.append(f"id:{format_id} ({description} - {lang_name})")
        
        # Update combobox options
        self.language_combo['values'] = options

        # ── Restore / set the displayed selection ─────────────────────────────
        # IMPORTANT: self.preferred_language is the user's persistent preference.
        # We never reset it here just because the current video lacks that language.
        # The actual audio fallback is handled in select_best_audio_stream.

        if preserve_selection and current_selection and current_selection in options:
            # Exact previous display string still exists in the new option list → keep it
            self.language_var.set(current_selection)

        elif preserve_selection and current_lang not in ('en', '') and not current_lang.startswith('id:'):
            # User has a non-English language preference
            matching_option = next((opt for opt in options if opt.startswith(current_lang + ' (')), None)
            if matching_option:
                # Language is available in this video
                self.language_var.set(matching_option)
            else:
                # Language NOT in this video - show a greyed "not available" marker
                # so the user can see their preference is set but won't be used here.
                unavailable_label = (current_lang + ' ('
                    + self.get_language_name(current_lang)
                    + ' - not available in this video)')
                # Insert it at position 1 (right after English) if not already there
                extended = list(options)
                extended.insert(1, unavailable_label)
                self.language_combo['values'] = extended
                self.language_var.set(unavailable_label)
                # preferred_language stays unchanged - fallback handled by select_best_audio_stream

        elif preserve_selection and current_lang.startswith('id:'):
            # Manual format ID - show English as active display (id: was per-video),
            # but keep preferred_language so the user can see it in the combo
            id_opt = next((opt for opt in options if opt.startswith(current_lang)), None)
            if id_opt:
                self.language_var.set(id_opt)
            else:
                english_option = next((opt for opt in options if opt.startswith('en (')), options[0])
                self.language_var.set(english_option)

        else:
            # Initial setup or no preference set - default to English display
            english_option = next((opt for opt in options if opt.startswith('en (')), options[0])
            self.language_var.set(english_option)
    
    def _show_error(self, message):
        """Show error message and reset UI"""
        self._notify_error("Error", message)
        self.progress_bar.stop()
        self.progress_var.set("Ready")
        self.paste_btn.config(state='normal')
        self.status_var.set("Error occurred")
    
    def get_stream_url(self):
        """Get direct URL for selected stream using yt-dlp executable"""
        # Get current tab and selected item
        current_tab = self.notebook.select()
        tab_text = self.notebook.tab(current_tab, "text")
        
        # Determine which treeview is active
        if "Combined" in tab_text:
            tree = self.combined_tree
        elif "Video Only" in tab_text:
            tree = self.video_tree
        elif "Audio Only" in tab_text:
            tree = self.audio_tree
        else:
            tree = self.all_tree
        
        selection = tree.selection()
        if not selection:
            self._notify_warning("Warning", "Please select a stream first")
            return
        
        # Get format ID from selected item
        item = tree.item(selection[0])
        values = item['values']
        
        if not values:
            self._notify_error("Error", "No data found for selected stream")
            return
            
        format_id = values[-1]  # Format ID is always the last column
        
        # Debug information
        
        if not format_id or str(format_id).strip() == '':
            self._notify_error("Error", "No format ID found for selected stream")
            return
        
        # Get stream URL in separate thread
        thread = threading.Thread(target=self._get_stream_url_worker, args=(format_id,))
        thread.daemon = True
        thread.start()
        
        self.status_var.set(f"Getting stream URL for format {format_id}...")
    
    def _get_stream_url_worker(self, format_id):
        """Worker function to get stream URL using yt-dlp executable"""
        try:
            url = self.url_var.get().strip()
            
            # Ensure format_id is a string
            format_id = str(format_id) if format_id else None
            
                
            if not format_id or format_id == 'None':
                self.root.after(0, lambda: self._notify_error("Error", "Invalid format ID"))
                return
            
            # Use yt-dlp to get the stream URL (attempt 1: default + cookies)
            def _build_url_args(ext_args_str):
                a = [
                    '--get-url',
                    '--no-warnings',
                    '-f', format_id,
                    '--extractor-args', ext_args_str,
                ]
                a.extend(self.get_ytdlp_dns_args())
                if self.yt_dlp_cache_dir:
                    a.extend(['--cache-dir', self.yt_dlp_cache_dir])
                a.append(url)
                return a

            result = self.run_ytdlp_command(
                _build_url_args('youtube:player_client=default,-tv_simply'), timeout=15)

            if result.returncode != 0 or not result.stdout.strip():
                # Attempt 2: android_vr fallback (no GVS PO token needed;
                # 'tv_embed' was never a valid yt-dlp client name and
                # 'tv_embedded' has since been removed from yt-dlp)
                result = self.run_ytdlp_command(
                    _build_url_args('youtube:player_client=android_vr,-tv_simply'), timeout=15)

            if result.returncode != 0:
                error_msg = 'Failed to get stream URL: ' + (result.stderr or '').strip()
                self.root.after(0, lambda: self._notify_error("Error", error_msg))
                return
            
            stream_url = result.stdout.strip()
            
            if stream_url:
                    
                # Find the target format for additional info
                target_format = None
                for fmt in self.current_formats:
                    if str(fmt.get('format_id', '')) == format_id:
                        target_format = fmt
                        break
                
                self.root.after(0, lambda: self._show_stream_url(stream_url, target_format))
            else:
                self.root.after(0, lambda: self._notify_error("Error", "Could not retrieve stream URL"))
                    
        except Exception as e:
            error_msg = f"Error getting stream URL: {str(e)}"
            self.root.after(0, lambda: self._notify_error("Error", error_msg))
        finally:
            self.root.after(0, lambda: self.status_var.set("Ready"))
    
    def _show_stream_url(self, stream_url, format_info=None):
        """Show stream URL in a dialog"""
        dialog = tk.Toplevel(self.root)
        dialog.title("Stream URL")
        dialog.geometry("700x400")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # URL display
        ttk.Label(dialog, text="Direct Stream URL:", font=('Arial', 10, 'bold')).pack(pady=10)
        
        url_text = scrolledtext.ScrolledText(dialog, height=6, wrap=tk.WORD)
        url_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        url_text.insert('1.0', stream_url)
        url_text.config(state='disabled')
        
        # Format information if available
        if format_info:
            ttk.Label(dialog, text="Format Information:", font=('Arial', 10, 'bold')).pack(pady=(10, 5))
            
            info_text = scrolledtext.ScrolledText(dialog, height=4, wrap=tk.WORD)
            info_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
            
            info_str = f"""Format ID: {format_info.get('format_id', 'Unknown')}
Quality: {format_info.get('height', 'Unknown')}p
Container: {format_info.get('ext', 'Unknown')}
Video Codec: {format_info.get('vcodec', 'Unknown')}
Audio Codec: {format_info.get('acodec', 'Unknown')}
File Size: {self.format_file_size(format_info.get('filesize'))}"""
            
            info_text.insert('1.0', info_str)
            info_text.config(state='disabled')
        
        # Buttons
        btn_frame = ttk.Frame(dialog)
        btn_frame.pack(pady=10)
        
        def copy_url():
            self.root.clipboard_clear()
            self.root.clipboard_append(stream_url)
            self._notify_info("Copied", "URL copied to clipboard!")
        
        def open_url():
            webbrowser.open(stream_url)
        
        ttk.Button(btn_frame, text="Copy URL", command=copy_url).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Open in Browser", command=open_url).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Close", command=dialog.destroy).pack(side=tk.LEFT, padx=5)
        
        # Warning label
        warning_label = ttk.Label(dialog, text="⚠️ Note: Stream URLs expire after some time!", 
                                 foreground="red", font=('Arial', 9))
        warning_label.pack(pady=5)
    
    def copy_video_info(self):
        """Copy video information to clipboard"""
        if not self.current_video_info:
            self._notify_warning("Warning", "No video information available")
            return
        
        info = self.current_video_info
        
        info_text = f"""Video Information:
Title: {info.get('title', 'Unknown')}
Uploader: {info.get('uploader', 'Unknown')}
Duration: {self.format_duration(info.get('duration', 0))}
Views: {info.get('view_count', 0):,}
Upload Date: {info.get('upload_date', 'Unknown')}
URL: {self.url_var.get()}

Total Streams: {len(self.current_formats)}"""
        
        self.root.clipboard_clear()
        self.root.clipboard_append(info_text)
        self._notify_info("Copied", "Video information copied to clipboard!")
    
    def on_stream_double_click(self, event, tree):
        """Double-click a recommended stream: show its URL, then download.

        The URL still goes to the terminal (the previous behaviour of this
        handler), so nothing is lost - but the double-click now also starts
        the merge, which is what it reads as. Selecting a row and pressing
        Merge is unchanged.

        Guarded against the obvious foot-gun: if a download is already
        running, or the Merge button is disabled (nothing analysed yet),
        the double-click reports why instead of starting a second job.
        """
        if not tree.selection():
            return
        try:
            self.get_stream_url()
        except Exception:
            pass
        if getattr(self, '_download_active', False):
            self.append_terminal_output(
                'A download is already running - double-click ignored.\n',
                'info')
            return
        try:
            if str(self.download_merge_btn['state']) == 'disabled':
                self.append_terminal_output(
                    'Nothing to merge yet - analyse a video first.\n', 'info')
                return
        except Exception:
            pass
        self.download_and_merge()
    
    def clear_all(self):
        """Clear all data and reset UI"""
        self.url_var.set("")
        self.current_video_info = {}
        self.current_formats = []
        
        # Reset video info labels
        for label in self.info_labels.values():
            label.config(text="-", foreground="gray")
        
        # Reset download status
        self.download_status_var.set("No downloads yet")
        self.preferred_language = "en"
        
        # Reset language dropdown
        self.language_combo['values'] = ["en (English - Best Quality)"]
        self.language_var.set("en (English - Best Quality)")
        
        # Clear all treeviews
        tree_names = ['combined_tree', 'video_tree', 'audio_tree', 'all_tree', 'recommended_tree']
        for tree_name in tree_names:
            if hasattr(self, tree_name):
                tree = getattr(self, tree_name)
                for item in tree.get_children():
                    tree.delete(item)
        
        # Reset pre-split stream caches so stale data can't be displayed
        self._video_streams = []
        self._audio_streams = []
        self._combined_streams = []
        self._detected_languages = {}

        # Reset buttons
        self.copy_info_btn.config(state='disabled')
        self.debug_btn.config(state='disabled')
        self.download_merge_btn.config(state='disabled')
        if hasattr(self, 'preview_btn'):
            self.preview_btn.config(state='disabled')

        # Reset clip fields
        if hasattr(self, '_clip_enabled_var'):
            self._clip_enabled_var.set(False)
            self._clip_start_var.set('00:00:00.00')
            self._clip_end_var.set('00:00:00.00')
            _fn = getattr(self, '_on_clip_toggle_fn', None)
            if _fn:
                _fn()
        
        self.status_var.set("Ready")
        self.progress_var.set("Ready")
    
    def show_debug_info(self):
        """Show debug information about the current video including cache status"""
        if not self.current_video_info:
            self._notify_warning("Warning", "No video information available")
            return

        dialog = tk.Toplevel(self.root)
        dialog.title("Debug Information")
        dialog.geometry("800x600")
        dialog.transient(self.root)

        ttk.Label(dialog, text="Debug Information:", font=('Arial', 12, 'bold')).pack(pady=10)
        debug_text = scrolledtext.ScrolledText(dialog, wrap=tk.WORD)
        debug_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))

        info = self.current_video_info
        video_id = info.get('id', 'unknown')

        yt_dlp_bundled_path = os.path.join(SCRIPT_DIR, 'yt-dlp.exe')
        ffmpeg_bundled_path = os.path.join(SCRIPT_DIR, 'ffmpeg.exe')

        _nl = '\n'
        _ytdlp_found   = '[FOUND]' if os.path.exists(yt_dlp_bundled_path) else '[NOT FOUND]'
        _ytenv_found   = '[FOUND]' if os.path.exists('C:/yt-dlp/yt-dlp.exe') else '[NOT FOUND]'
        _ytpath_avail  = '[AVAILABLE]' if self.ytdlp_path == 'yt-dlp' else '[NOT CHECKED]'
        _ff_found      = '[FOUND]' if os.path.exists(ffmpeg_bundled_path) else '[NOT FOUND]'
        _ffstd_found   = '[FOUND]' if os.path.exists('C:/ffmpeg/bin/ffmpeg.exe') else '[NOT FOUND]'
        _ffpath_avail  = '[AVAILABLE]' if self.ffmpeg_path == 'ffmpeg' else '[NOT CHECKED]'

        debug_info = (
            "VIDEO INFORMATION:" + _nl +
            "Title: " + str(info.get('title', 'Unknown')) + _nl +
            "ID: " + str(video_id) + _nl +
            "Uploader: " + str(info.get('uploader', 'Unknown')) + _nl +
            "Duration: " + str(info.get('duration', 0)) + " seconds" + _nl +
            "View Count: " + str(info.get('view_count', 0)) + _nl +
            "Upload Date: " + str(info.get('upload_date', 'Unknown')) + _nl + _nl +
            "EXECUTABLE PATHS:" + _nl +
            "Script Directory: " + str(SCRIPT_DIR) + _nl +
            "yt-dlp Path: " + str(self.ytdlp_path or 'NOT FOUND') + _nl +
            "FFmpeg Path: " + str(self.ffmpeg_path or 'NOT FOUND') + _nl + _nl +
            "EXECUTABLE DETECTION DETAILS:" + _nl +
            "yt-dlp Search Order:" + _nl +
            "  1. Bundled: " + yt_dlp_bundled_path + " " + _ytdlp_found + _nl +
            "  2. Environment: C:/yt-dlp/yt-dlp.exe " + _ytenv_found + _nl +
            "  3. System PATH: " + _ytpath_avail + _nl + _nl +
            "FFmpeg Search Order:" + _nl +
            "  1. Bundled: " + ffmpeg_bundled_path + " " + _ff_found + _nl +
            "  2. Standard: C:/ffmpeg/bin/ffmpeg.exe " + _ffstd_found + _nl +
            "  3. System PATH: " + _ffpath_avail + _nl + _nl +
            "CACHE STATUS:" + _nl +
            "Video Cache Directory: " + str(self.video_cache_dir or 'Disabled') + _nl +
            "yt-dlp Cache Directory: " + str(self.yt_dlp_cache_dir or 'Disabled') + _nl
        )

        # Add cached video info
        if video_id in self.cached_videos:
            debug_info += "\nCACHED VIDEO STREAMS FOR THIS VIDEO (" + str(video_id) + "):\n"
            for format_id, file_path in self.cached_videos[video_id].items():
                if os.path.exists(file_path):
                    file_size = self.format_file_size(os.path.getsize(file_path))
                    debug_info += "  Format " + str(format_id) + ": " + str(file_path) + " (" + file_size + ")\n"
                else:
                    debug_info += "  Format " + str(format_id) + ": " + str(file_path) + " (FILE MISSING)\n"
        else:
            debug_info += "\nNo cached streams for video " + str(video_id) + "\n"

        total_cached = sum(len(formats) for formats in self.cached_videos.values())
        debug_info += "\nTOTAL CACHED STREAMS: " + str(total_cached) + "\n"

        debug_info += "\nAVAILABLE FORMATS: " + str(len(self.current_formats)) + "\n"

        for i, fmt in enumerate(self.current_formats[:10]):
            debug_info += (
                "\nFormat " + str(i+1) + ":\n"
                "  Format ID: " + str(fmt.get("format_id", "Unknown")) + "\n"
                "  Extension: " + str(fmt.get("ext", "Unknown")) + "\n"
                "  Quality: " + str(fmt.get("height", "Unknown")) + "p\n"
                "  Video Codec: " + str(fmt.get("vcodec", "Unknown")) + "\n"
                "  Audio Codec: " + str(fmt.get("acodec", "Unknown")) + "\n"
                "  File Size: " + str(fmt.get("filesize", "Unknown")) + " bytes\n"
                "  URL Available: " + ("Yes" if fmt.get("url") else "No") + "\n"
            )

        if len(self.current_formats) > 10:
            debug_info += "\n... and " + str(len(self.current_formats) - 10) + " more formats"

        debug_text.insert('1.0', debug_info)
        debug_text.config(state='readonly')

        ttk.Button(dialog, text="Close", command=dialog.destroy).pack(pady=10)
    
    def show_settings(self):
        """Show tabbed settings dialog"""
        try:
         self._show_settings_impl()
        except Exception as _se:
         import traceback as _tb
         self._notify_error("Settings Error",
             "Settings failed to open:\n\n" + _tb.format_exc())

    def _show_settings_impl(self):
        """Internal: actual settings dialog builder."""
        dialog = tk.Toplevel(self.root)
        dialog.title("Settings")
        dialog.geometry("860x1060")
        dialog.resizable(True, True)
        dialog.minsize(800, 960)
        dialog.transient(self.root)
        dialog.grab_set()

        notebook = ttk.Notebook(dialog)
        # btn_frame is packed first with side=BOTTOM so it stays pinned below
        # the notebook at all window sizes.  The actual buttons are added later.
        _settings_btn_frame = ttk.Frame(dialog)
        _settings_btn_frame.pack(side=tk.BOTTOM, fill=tk.X, padx=10, pady=8)
        notebook.pack(fill=tk.BOTH, expand=True, padx=10, pady=(10, 0))

        # ── Tab 1: Downloads (first shown) ─────────────────────────────────
        # Tab frames are created now; added to notebook in desired display order later
        tab_exe = ttk.Frame(notebook)
        tab_exe.columnconfigure(0, weight=1)

        # yt-dlp section
        ttk.Label(tab_exe, text="yt-dlp Path:", font=('Arial', 9, 'bold')).grid(
            row=0, column=0, columnspan=2, sticky=tk.W, padx=8, pady=(10, 2))

        ytdlp_frame = ttk.Frame(tab_exe)
        ytdlp_frame.grid(row=1, column=0, columnspan=2, sticky=(tk.W, tk.E), padx=8, pady=(0, 4))
        ytdlp_frame.columnconfigure(0, weight=1)

        self.ytdlp_var = tk.StringVar(value=self.ytdlp_path or "Not found")
        ytdlp_entry = ttk.Entry(ytdlp_frame, textvariable=self.ytdlp_var)
        ytdlp_entry.grid(row=0, column=0, sticky=(tk.W, tk.E), padx=(0, 5))

        def browse_ytdlp():
            fp = filedialog.askopenfilename(
                title="Select yt-dlp executable",
                filetypes=[("Executable files", "*.exe"), ("All files", "*.*")])
            if fp:
                self.ytdlp_var.set(fp)

        ttk.Button(ytdlp_frame, text="Browse", command=browse_ytdlp).grid(row=0, column=1)

        # ── yt-dlp version + update status row ────────────────────────────
        ytdlp_info_frame = ttk.Frame(tab_exe)
        ytdlp_info_frame.grid(row=2, column=0, columnspan=2, sticky=(tk.W, tk.E), padx=8, pady=(2, 0))

        ytdlp_badge_lbl = tk.Label(ytdlp_info_frame, text="  checking...  ",
                                   font=('Arial', 8, 'bold'),
                                   background='#AAAAAA', foreground='white',
                                   relief=tk.FLAT, padx=4, pady=2)
        ytdlp_badge_lbl.pack(side=tk.LEFT)

        ytdlp_ver_lbl = ttk.Label(ytdlp_info_frame, text="",
                                  foreground="gray", font=('Arial', 8))
        ytdlp_ver_lbl.pack(side=tk.LEFT, padx=(8, 0))

        ttk.Label(ytdlp_info_frame, text="Channel:",
                  font=('Arial', 8)).pack(side=tk.LEFT, padx=(12, 2))
        ytdlp_channel_var = tk.StringVar(
            value=getattr(self, 'ytdlp_channel', 'nightly'))
        ttk.Combobox(ytdlp_info_frame, textvariable=ytdlp_channel_var,
                     values=('nightly', 'stable'), state='readonly',
                     width=9).pack(side=tk.LEFT)
        # Packed BEFORE the update button on purpose: that button is
        # pack_forget()-ed and re-packed as updates appear, and side=LEFT
        # re-packing appends to the END - anything added after it would be
        # jumped over when it reappears.
        ytdlp_upd_btn = ttk.Button(ytdlp_info_frame, text="Update yt-dlp")
        # Button wired below after _do_update_ytdlp is defined
        ytdlp_upd_btn.pack(side=tk.LEFT, padx=(12, 0))
        ytdlp_upd_btn.pack_forget()  # Hidden until an update is detected

        ytdlp_test_btn_frame = ttk.Frame(tab_exe)
        ytdlp_test_btn_frame.grid(row=3, column=0, columnspan=2, sticky=tk.W, padx=8, pady=(2, 6))
        ytdlp_status_lbl = ttk.Label(ytdlp_test_btn_frame,
                                     text="Available" if self.ytdlp_path else "Not found",
                                     foreground="green" if self.ytdlp_path else "red")
        ytdlp_status_lbl.pack(side=tk.LEFT)

        def _set_ytdlp_badge(state, local_v='', latest_v=''):
            """state: 'checking'|'ok'|'update'|'unknown'"""
            cfg = {
                'checking': ('  checking...  ', '#AAAAAA'),
                'ok':        ('  Up to date  ', '#2E7D32'),
                'update':    ('  Update available  ', '#E65100'),
                'offline':   ('  Installed  ', '#1565C0'),
                'unknown':   ('  Not found  ', '#555555'),
            }
            txt, bg = cfg.get(state, cfg['unknown'])
            ytdlp_badge_lbl.config(text=txt, background=bg)
            if state == 'update' and local_v and latest_v:
                ytdlp_ver_lbl.config(text=local_v + '  ->  ' + latest_v, foreground='#E65100')
                ytdlp_upd_btn.pack(side=tk.LEFT, padx=(12, 0))
            elif state in ('ok', 'offline') and local_v:
                suffix = ''
                ytdlp_ver_lbl.config(text=local_v + suffix, foreground='gray')
                ytdlp_upd_btn.pack_forget()
            else:
                ytdlp_ver_lbl.config(text=local_v or '', foreground='gray')
                ytdlp_upd_btn.pack_forget()

        def _fetch_ytdlp_status():
            local_v = self._get_ytdlp_version()
            import requests  # deferred - see _get_http_session at module top
            try:
                resp = requests.get(
                    self._ytdlp_release_api_url(),
                    timeout=8, headers={'Accept': 'application/vnd.github+json'})
                resp.raise_for_status()
                latest_v = resp.json().get('tag_name', '').strip()
            except Exception:
                latest_v = None
            if not local_v:
                # Can't read the exe at all
                state, lv, rv = 'unknown', '', ''
            elif not latest_v:
                # Exe is fine but GitHub unreachable - show version, blue "Installed" badge
                state, lv, rv = 'offline', local_v, ''
            elif self._version_key(local_v) >= self._version_key(latest_v):
                state, lv, rv = 'ok', local_v, latest_v
            else:
                state, lv, rv = 'update', local_v, latest_v
            try:
                if dialog.winfo_exists():
                    dialog.after(0, lambda s=state, l=lv, r=rv: _set_ytdlp_badge(s, l, r))
            except Exception:
                pass

        threading.Thread(target=_fetch_ytdlp_status, daemon=True).start()

        def _do_update_ytdlp():
            ytdlp_upd_btn.config(state='disabled')
            _set_ytdlp_badge('checking')
            def _after():
                threading.Thread(target=_fetch_ytdlp_status, daemon=True).start()
            def _run():
                # Same hazard as the automatic path: replacing yt-dlp.exe
                # while an invocation is in flight corrupts it mid-read.
                # The automatic updater was gated first; this manual button
                # was not, so an update could still land during a download.
                if (getattr(self, '_download_active', False)
                        or self._any_ytdlp_running()):
                    self.append_terminal_output(
                        'yt-dlp update skipped - a download or extraction is'
                        ' running. Stop it and press Update again.\n',
                        'warning')
                else:
                    self._update_ytdlp()
                try:
                    if dialog.winfo_exists():
                        dialog.after(500, _after)
                except Exception:
                    pass
            threading.Thread(target=_run, daemon=True).start()

        ytdlp_upd_btn.config(command=_do_update_ytdlp)

        def test_ytdlp():
            ytdlp_status_lbl.config(text="Testing...", foreground="gray")
            def _test():
                ok = self.test_ytdlp_path(self.ytdlp_var.get())
                txt = "Available" if ok else "Not found or not working"
                clr = "green" if ok else "red"
                try:
                    if dialog.winfo_exists():
                        dialog.after(0, lambda: ytdlp_status_lbl.config(text=txt, foreground=clr))
                except Exception:
                    pass
            threading.Thread(target=_test, daemon=True).start()

        ttk.Button(ytdlp_test_btn_frame, text="Test",
                   command=test_ytdlp).pack(side=tk.LEFT, padx=(10, 0))

        ttk.Separator(tab_exe, orient=tk.HORIZONTAL).grid(
            row=4, column=0, columnspan=2, sticky=(tk.W, tk.E), padx=8, pady=6)

        # ── FFmpeg section ─────────────────────────────────────────────────
        ttk.Label(tab_exe, text="FFmpeg Path:", font=('Arial', 9, 'bold')).grid(
            row=6, column=0, columnspan=2, sticky=tk.W, padx=8, pady=(4, 2))

        ffmpeg_frame = ttk.Frame(tab_exe)
        ffmpeg_frame.grid(row=7, column=0, columnspan=2, sticky=(tk.W, tk.E), padx=8, pady=(0, 4))
        ffmpeg_frame.columnconfigure(0, weight=1)

        self.ffmpeg_var = tk.StringVar(value=self.ffmpeg_path or "Not found")
        ffmpeg_entry = ttk.Entry(ffmpeg_frame, textvariable=self.ffmpeg_var)
        ffmpeg_entry.grid(row=0, column=0, sticky=(tk.W, tk.E), padx=(0, 5))

        def browse_ffmpeg():
            fp = filedialog.askopenfilename(
                title="Select FFmpeg executable",
                filetypes=[("Executable files", "*.exe"), ("All files", "*.*")])
            if fp:
                self.ffmpeg_var.set(fp)

        ttk.Button(ffmpeg_frame, text="Browse", command=browse_ffmpeg).grid(row=0, column=1)

        # ── FFmpeg version + update status row ────────────────────────────
        ffmpeg_info_frame = ttk.Frame(tab_exe)
        ffmpeg_info_frame.grid(row=8, column=0, columnspan=2, sticky=(tk.W, tk.E),
                               padx=8, pady=(2, 0))

        ffmpeg_badge_lbl = tk.Label(ffmpeg_info_frame, text="  checking...  ",
                                    font=('Arial', 8, 'bold'),
                                    background='#AAAAAA', foreground='white',
                                    relief=tk.FLAT, padx=4, pady=2)
        ffmpeg_badge_lbl.pack(side=tk.LEFT)

        ffmpeg_ver_lbl = ttk.Label(ffmpeg_info_frame, text="",
                                   foreground="gray", font=('Arial', 8))
        ffmpeg_ver_lbl.pack(side=tk.LEFT, padx=(8, 0))

        ffmpeg_upd_btn = ttk.Button(ffmpeg_info_frame, text="Update FFmpeg")
        ffmpeg_upd_btn.pack(side=tk.LEFT, padx=(12, 0))
        ffmpeg_upd_btn.pack_forget()

        ffmpeg_test_btn_frame = ttk.Frame(tab_exe)
        ffmpeg_test_btn_frame.grid(row=9, column=0, columnspan=2, sticky=tk.W, padx=8, pady=(2, 6))
        ffmpeg_status_lbl = ttk.Label(ffmpeg_test_btn_frame,
                                      text="Available" if self.ffmpeg_path else "Not found",
                                      foreground="green" if self.ffmpeg_path else "red")
        ffmpeg_status_lbl.pack(side=tk.LEFT)

        def _set_ffmpeg_badge(state, local_v='', latest_v=''):
            cfg = {
                'checking': ('  checking...  ', '#AAAAAA'),
                'ok':        ('  Up to date  ', '#2E7D32'),
                'update':    ('  Update available  ', '#E65100'),
                'offline':   ('  Installed  ', '#1565C0'),
                'unknown':   ('  Not found  ', '#555555'),
            }
            txt, bg = cfg.get(state, cfg['unknown'])
            ffmpeg_badge_lbl.config(text=txt, background=bg)
            if state == 'update' and local_v and latest_v:
                ffmpeg_ver_lbl.config(
                    text=local_v + '  ->  ' + latest_v, foreground='#E65100')
                ffmpeg_upd_btn.pack(side=tk.LEFT, padx=(12, 0))
            elif state in ('ok', 'offline') and local_v:
                suffix = ''
                ffmpeg_ver_lbl.config(text=local_v + suffix, foreground='gray')
                ffmpeg_upd_btn.pack_forget()
            else:
                ffmpeg_ver_lbl.config(text=local_v or '', foreground='gray')
                ffmpeg_upd_btn.pack_forget()

        def _fetch_ffmpeg_status():
            local_v = self._get_ffmpeg_version()
            tag, _ = self._get_ffmpeg_latest_info()
            local_sv = self._parse_ffmpeg_semver(local_v)
            latest_sv = self._parse_ffmpeg_semver(tag)
            if not local_sv:
                # Can't read ffmpeg at all
                state = 'unknown'
            elif not latest_sv:
                # ffmpeg is fine but GitHub unreachable
                state = 'offline'
            elif local_sv >= latest_sv:
                state = 'ok'
            else:
                state = 'update'
            try:
                if dialog.winfo_exists():
                    dialog.after(0, lambda s=state, l=local_v or '', r=tag or '':
                                 _set_ffmpeg_badge(s, l, r))
            except Exception:
                pass

        threading.Thread(target=_fetch_ffmpeg_status, daemon=True).start()

        def _do_update_ffmpeg():
            ffmpeg_upd_btn.config(state='disabled')
            _set_ffmpeg_badge('checking')
            def _on_done(ok, msg):
                try:
                    if dialog.winfo_exists():
                        dialog.after(500, lambda:
                            threading.Thread(target=_fetch_ffmpeg_status, daemon=True).start())
                        dialog.after(0, lambda: ffmpeg_upd_btn.config(state='normal'))
                except Exception:
                    pass
            self._update_ffmpeg(on_done_callback=_on_done)

        ffmpeg_upd_btn.config(command=_do_update_ffmpeg)

        def test_ffmpeg():
            ffmpeg_status_lbl.config(text="Testing...", foreground="gray")
            def _test():
                ok = self.test_ffmpeg_path(self.ffmpeg_var.get())
                txt = "Available" if ok else "Not found or not working"
                clr = "green" if ok else "red"
                try:
                    if dialog.winfo_exists():
                        dialog.after(0, lambda: ffmpeg_status_lbl.config(text=txt, foreground=clr))
                except Exception:
                    pass
            threading.Thread(target=_test, daemon=True).start()

        ttk.Button(ffmpeg_test_btn_frame, text="Test",
                   command=test_ffmpeg).pack(side=tk.LEFT, padx=(10, 0))

        # ── Auto-update setting (below FFmpeg) ─────────────────────────────
        ttk.Separator(tab_exe, orient=tk.HORIZONTAL).grid(
            row=10, column=0, columnspan=2, sticky=(tk.W, tk.E), padx=8, pady=6)
        auto_upd_frame = ttk.Frame(tab_exe)
        auto_upd_frame.grid(row=11, column=0, columnspan=2, sticky=tk.W, padx=8, pady=(2, 6))
        auto_upd_var = tk.BooleanVar(value=self.auto_update_tools)
        ttk.Checkbutton(auto_upd_frame,
                        text="Automatically update yt-dlp and FFmpeg on startup",
                        variable=auto_upd_var).pack(side=tk.LEFT)

        # ── Tab 2: Downloads (scrollable) ──────────────────────────────────
        _tab_dl_outer = ttk.Frame(notebook)   # outer: holds canvas + scrollbar
        _dl_canvas = tk.Canvas(_tab_dl_outer, highlightthickness=0)
        _dl_vbar = ttk.Scrollbar(_tab_dl_outer, orient='vertical', command=_dl_canvas.yview)
        _dl_canvas.configure(yscrollcommand=_dl_vbar.set)
        _dl_vbar.pack(side=tk.RIGHT, fill=tk.Y)
        _dl_canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        tab_dl = ttk.Frame(_dl_canvas)        # inner: all widgets grid here
        _dl_win = _dl_canvas.create_window((0, 0), window=tab_dl, anchor='nw')
        tab_dl.bind('<Configure>',
            lambda e: _dl_canvas.configure(scrollregion=_dl_canvas.bbox('all')))
        _dl_canvas.bind('<Configure>',
            lambda e: _dl_canvas.itemconfig(_dl_win, width=e.width))
        def _dl_on_scroll(event):
            _dl_canvas.yview_scroll(int(-1 * (event.delta / 120)), 'units')
        _dl_canvas.bind('<Enter>',
            lambda e: _dl_canvas.bind_all('<MouseWheel>', _dl_on_scroll))
        _dl_canvas.bind('<Leave>',
            lambda e: _dl_canvas.unbind_all('<MouseWheel>'))
        tab_dl.columnconfigure(1, weight=1)
        tab_dl.columnconfigure(2, weight=1)

        ttk.Label(tab_dl, text="Download Folder:").grid(
            row=1, column=0, sticky=tk.W, padx=8, pady=4)
        dl_folder_lbl = ttk.Label(tab_dl, text=self.download_path,
                                  foreground="gray", font=('Arial', 8))
        dl_folder_lbl.grid(row=1, column=1, columnspan=2, sticky=tk.W, padx=8, pady=4)
        ttk.Label(tab_dl, text="(Change in main window)", font=('Arial', 8),
                  foreground="gray").grid(row=2, column=1, sticky=tk.W, padx=8)

        ttk.Separator(tab_dl, orient=tk.HORIZONTAL).grid(
            row=3, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=8)

        ttk.Label(tab_dl, text="Appearance:").grid(
            row=4, column=0, sticky=tk.W, padx=8, pady=(4, 2))
        dm_var = tk.BooleanVar(value=self.dark_mode_var.get())
        dm_cb = ttk.Checkbutton(tab_dl, text="Dark Mode",
                                variable=dm_var)
        dm_cb.grid(row=4, column=1, sticky=tk.W, padx=8, pady=(4, 2))

        ttk.Label(tab_dl, text="Preferred Language:").grid(
            row=5, column=0, sticky=tk.W, padx=8, pady=4)

        _LANG_OPTS = [
            ("English",    "en"),
            ("Spanish",    "es"),
            ("French",     "fr"),
            ("German",     "de"),
            ("Italian",    "it"),
            ("Portuguese", "pt"),
            ("Russian",    "ru"),
            ("Japanese",   "ja"),
            ("Korean",     "ko"),
            ("Chinese",    "zh"),
            ("Arabic",     "ar"),
            ("Hindi",      "hi"),
            ("Thai",       "th"),
            ("Turkish",    "tr"),
            ("Polish",     "pl"),
            ("Dutch",      "nl"),
        ]
        _LANG_DISPLAY = [name + " (" + code + ")" for name, code in _LANG_OPTS]
        _LANG_CODE_TO_DISPLAY = {code: name + " (" + code + ")" for name, code in _LANG_OPTS}
        _LANG_DISPLAY_TO_CODE = {name + " (" + code + ")": code for name, code in _LANG_OPTS}

        # If preferred_language is an id: token or unknown code, fall back to English in settings
        _cur_lang = self.preferred_language if not self.preferred_language.startswith("id:") else "en"
        _initial_display = _LANG_CODE_TO_DISPLAY.get(_cur_lang, "English (en)")

        lang_var_settings = tk.StringVar(value=_initial_display)
        lang_combo_settings = ttk.Combobox(tab_dl, textvariable=lang_var_settings,
                                            values=_LANG_DISPLAY, state='readonly', width=28)
        lang_combo_settings.grid(row=5, column=1, sticky=tk.W, padx=8, pady=4)
        ttk.Label(tab_dl, text="(default for merged audio tracks)", font=('Arial', 8),
                  foreground="gray").grid(row=5, column=2, sticky=tk.W, padx=4)

        ttk.Separator(tab_dl, orient=tk.HORIZONTAL).grid(
            row=6, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=8)

        # ── Filename options ───────────────────────────────────────────────
        _FN_OPTS   = ['Channel', 'Title', 'Upload Date', 'Download Date',
                       'Quality Tag', 'Video ID', 'Duration', 'Queue Index', '(none)']
        _FN_DEFAULT = ['Channel', 'Title', 'Upload Date', 'Quality Tag', '(none)']
        _FN_PRESETS = {
            'Channel - Title [Quality]':                   ['Channel', 'Title', 'Quality Tag', '(none)', '(none)'],
            'Title - Channel [Quality]':                   ['Title', 'Channel', 'Quality Tag', '(none)', '(none)'],
            'Channel - Title [Upload] [Quality]':          ['Channel', 'Title', 'Upload Date', 'Quality Tag', '(none)'],
            'Upload - Channel - Title [Quality]':          ['Upload Date', 'Channel', 'Title', 'Quality Tag', '(none)'],
            'Channel - Title [Quality] [Video ID]':        ['Channel', 'Title', 'Quality Tag', 'Video ID', '(none)'],
            '#Queue - Channel - Title [Quality]':          ['Queue Index', 'Channel', 'Title', 'Quality Tag', '(none)'],
            'Channel - Title [Duration] [Quality]':        ['Channel', 'Title', 'Duration', 'Quality Tag', '(none)'],
            'Download - Channel - Title [Quality]':        ['Download Date', 'Channel', 'Title', 'Quality Tag', '(none)'],
        }

        # Parse stored format string into 4 slots
        # New format: pipe-separated e.g. "Channel|Title|Date|Quality Tag"
        # Legacy format: dash-separated e.g. "channel - title" - migrated on load
        def _parse_slots(fmt_str):
            """Convert stored format string to list of 5 slot values."""
            valid = set(_FN_OPTS)
            if '|' in fmt_str:
                parts = fmt_str.split('|')
                # Migrate legacy 'Date' → 'Upload Date'
                parts = [('Upload Date' if p == 'Date' else p) for p in parts]
                parts = (parts + ['(none)', '(none)', '(none)', '(none)', '(none)'])[:5]
                return [p if p in valid else '(none)' for p in parts]
            # Single-token new-style save (e.g. 'Channel', 'Quality Tag')
            if fmt_str in valid and fmt_str != '(none)':
                return [fmt_str, '(none)', '(none)', '(none)', '(none)']
            # Legacy dash-separated migration
            _legacy_map = {
                'channel - title':        ['Channel', 'Title', 'Quality Tag', '(none)', '(none)'],
                'title - channel':        ['Title', 'Channel', '(none)', '(none)', '(none)'],
                'channel - date - title': ['Channel', 'Upload Date', 'Title', '(none)', '(none)'],
                'date - channel - title': ['Upload Date', 'Channel', 'Title', '(none)', '(none)'],
                'date - title - channel': ['Upload Date', 'Title', 'Channel', '(none)', '(none)'],
                'title':                  ['Title', '(none)', '(none)', '(none)', '(none)'],
                'date - title':           ['Upload Date', 'Title', '(none)', '(none)', '(none)'],
            }
            return _legacy_map.get(fmt_str, _FN_DEFAULT[:])

        _cur_slots = _parse_slots(getattr(self, 'filename_format', 'channel - title'))
        _slot_vars = [tk.StringVar(value=_cur_slots[i]) for i in range(5)]

        # ── Header row: label + Presets dropdown + Restore Default ────────
        ttk.Label(tab_dl, text="Filename:", font=('Arial', 9, 'bold')).grid(
            row=7, column=0, sticky=tk.W, padx=8, pady=(2, 4))

        _fn_header_frame = ttk.Frame(tab_dl)
        _fn_header_frame.grid(row=7, column=1, columnspan=2, sticky=(tk.W, tk.E), padx=8, pady=(2, 4))
        _fn_header_frame.columnconfigure(1, weight=1)

        ttk.Label(_fn_header_frame, text="Preset:").grid(row=0, column=0, sticky=tk.W, padx=(0, 4))
        _preset_var = tk.StringVar(value='')
        _preset_combo = ttk.Combobox(_fn_header_frame, textvariable=_preset_var,
                                     values=list(_FN_PRESETS.keys()), state='readonly')
        _preset_combo.grid(row=0, column=1, sticky=(tk.W, tk.E), padx=(0, 8))

        def _apply_preset(*_):
            chosen = _preset_var.get()
            if chosen in _FN_PRESETS:
                slots = _FN_PRESETS[chosen]
                for i, sv in enumerate(_slot_vars):
                    sv.set(slots[i])
                _update_slot_options()
                _update_preview()

        _preset_combo.bind('<<ComboboxSelected>>', _apply_preset)

        def _restore_default():
            for i, sv in enumerate(_slot_vars):
                sv.set(_FN_DEFAULT[i])
            _preset_var.set('')
            _update_slot_options()
            _update_preview()

        ttk.Button(_fn_header_frame, text='Restore Default',
                   command=_restore_default).grid(row=0, column=2, sticky=tk.W, padx=(0, 4))

        # ── Four slot dropdowns ────────────────────────────────────────────
        _slots_frame = ttk.Frame(tab_dl)
        _slots_frame.grid(row=8, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(2, 2))

        # Row 0: slots 1-3  |  Row 1: slots 4-5
        # Using grid instead of pack so the row never overflows the dialog width.
        _SLOT_ROW = [0, 0, 0, 1, 1]   # which grid row each slot lives on
        _SLOT_COL = [0, 2, 4, 0, 2]   # which grid column (odd cols = separators)

        _slot_combos = []
        def _make_clear_slot(idx):
            def _clear(*_):
                _slot_vars[idx].set('(none)')
                _update_slot_options()
                _update_preview()
            return _clear

        for i in range(5):
            r, c = _SLOT_ROW[i], _SLOT_COL[i]
            # Separator before slots 2, 3 (same row) and before slot 5 (row 1)
            if i in (1, 2, 4):
                ttk.Label(_slots_frame, text='-', font=('Arial', 10)).grid(
                    row=r, column=c - 1, padx=2)
            _cell = ttk.Frame(_slots_frame)
            _cell.grid(row=r, column=c, padx=2, pady=(0, 2))
            cb = ttk.Combobox(_cell, textvariable=_slot_vars[i],
                              state='readonly', width=12)
            cb.pack(side=tk.LEFT)
            _x_btn = tk.Button(_cell, text='✕', font=('Arial', 9, 'bold'), relief='flat',
                               bd=0, padx=4, pady=2, cursor='hand2',
                               command=_make_clear_slot(i))
            _x_btn.pack(side=tk.LEFT, padx=(2, 0))
            _slot_combos.append(cb)

        # ── Live preview ──────────────────────────────────────────────────
        _preview_var = tk.StringVar()
        _preview_lbl = ttk.Label(tab_dl, textvariable=_preview_var,
                                 font=('Arial', 8), foreground='gray')
        _preview_lbl.grid(row=9, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(0, 2))

        ttk.Label(tab_dl,
                  text='Note: Title is always included - it is the only slot that identifies a file.',
                  font=('Arial', 7), foreground='gray').grid(
            row=10, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(0, 4))

        def _slots_to_fmt(slots):
            """Convert 5-slot list to pipe-separated storage string."""
            active = [s for s in slots if s != '(none)']
            return '|'.join(active) + '|' if active else 'Title|'

        def _update_preview(*_):
            slots = [sv.get() for sv in _slot_vars]
            active = [s for s in slots if s != '(none)']
            _tag_ex = '[1080p EN S]'
            _ex_map = {
                'Channel':       'Channel Name',
                'Title':         'Video Title',
                'Upload Date':   'U2025-01-21',
                'Download Date': 'D2026-04-05',
                'Quality Tag':   _tag_ex,
                'Video ID':      'mnU0f40juh8',
                'Duration':      '3m24s',
                'Queue Index':   '#01',
            }
            _parts = [_ex_map[s] for s in active if s in _ex_map]
            if 'Title' not in active:
                _parts.append('Video Title')
            preview = ' - '.join(_parts) if _parts else 'Video Title'
            _preview_var.set('Preview: ' + preview + '.mp4')
            cur_slots = [sv.get() for sv in _slot_vars]
            _preset_var.set(next(
                (k for k, v in _FN_PRESETS.items() if v == cur_slots), ''))

        # Track which slot was most recently changed so eviction knows the source
        _last_changed = [None]

        def _update_slot_options(*_):
            """All options always visible in every combo.  If a value is picked
            that already exists in another slot, evict the duplicate to (none)."""
            changed_idx = _last_changed[0]
            if changed_idx is not None:
                new_val = _slot_vars[changed_idx].get()
                if new_val != '(none)':
                    for i, sv in enumerate(_slot_vars):
                        if i != changed_idx and sv.get() == new_val:
                            sv.set('(none)')
            # All slots always show full options list
            for cb in _slot_combos:
                cb['values'] = _FN_OPTS

        def _make_slot_handler(idx):
            def _handler(*_):
                _last_changed[0] = idx
                _update_slot_options()
                _update_preview()
            return _handler

        for i, sv in enumerate(_slot_vars):
            sv.trace_add('write', _make_slot_handler(i))

        _update_slot_options()
        _update_preview()

        # fn_format_var used by save_settings - derive from slots at save time
        fn_format_var = tk.StringVar(value=_slots_to_fmt(_cur_slots))

        def _sync_fn_format_var():
            fn_format_var.set(_slots_to_fmt([sv.get() for sv in _slot_vars]))

        # Keep legacy var so save_settings can still reference it
        date_in_filename_var = tk.BooleanVar(value=self.filename_include_date)

        ttk.Separator(tab_dl, orient=tk.HORIZONTAL).grid(
            row=11, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=8)

        # ── Metadata field toggles ─────────────────────────────────────────
        ttk.Label(tab_dl, text="Embed Metadata Fields:", font=('Arial', 9, 'bold')).grid(
            row=12, column=0, sticky=tk.W, padx=8, pady=(2, 4))

        meta_title_var   = tk.BooleanVar(value=self.meta_embed_title)
        meta_artist_var  = tk.BooleanVar(value=self.meta_embed_artist)
        meta_date_var    = tk.BooleanVar(value=self.meta_embed_date)
        meta_comment_var = tk.BooleanVar(value=self.meta_embed_comment)
        meta_synopsis_var= tk.BooleanVar(value=self.meta_embed_synopsis)

        meta_cb_frame = ttk.Frame(tab_dl)
        meta_cb_frame.grid(row=13, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(0, 4))
        ttk.Checkbutton(meta_cb_frame, text="Title",   variable=meta_title_var).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Checkbutton(meta_cb_frame, text="Artist",  variable=meta_artist_var).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Checkbutton(meta_cb_frame, text="Date",    variable=meta_date_var).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Checkbutton(meta_cb_frame, text="Comment (URL)", variable=meta_comment_var).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Checkbutton(meta_cb_frame, text="Synopsis", variable=meta_synopsis_var).pack(side=tk.LEFT)

        ttk.Separator(tab_dl, orient=tk.HORIZONTAL).grid(
            row=14, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=8)

        # ── Stream bitrate preferences ────────────────────────────────────
        ttk.Label(tab_dl, text="Stream Bitrate:", font=('Arial', 9, 'bold')).grid(
            row=15, column=0, sticky=tk.W, padx=8, pady=(2, 4))
        include_hls_var = tk.BooleanVar(
            value=getattr(self, 'include_hls_streams', False))
        ttk.Checkbutton(tab_dl,
                        text="Include HLS streams (sizes are estimates, not measured)",
                        variable=include_hls_var).grid(
            row=16, column=0, columnspan=4, sticky=tk.W, padx=24, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="Off by default: HLS rows show advertised sizes that can be\n"
                       "several times the real file. Every resolution they offer is\n"
                       "already covered by a DASH stream with an exact size.",
                  font=('Arial', 8), foreground='gray').grid(
            row=17, column=0, columnspan=4, sticky=tk.W, padx=42, pady=(0, 4))

        # row 19, not 15: at 15 this label was drawn into the same cell as
        # the "Stream Bitrate:" section header (Tk stacks silently), while
        # its own entry sat four rows lower at 19 with nothing beside it.
        # Rows 16-18 hold no widgets, so they collapse to zero height.
        ttk.Label(tab_dl, text="Max audio bitrate (kbps):").grid(
            row=19, column=0, sticky=tk.W, padx=8, pady=(2, 2))
        audio_bitrate_var = tk.StringVar(value=str(getattr(self, 'preferred_audio_bitrate', 0)))
        audio_bitrate_entry = ttk.Entry(tab_dl, textvariable=audio_bitrate_var, width=8)
        audio_bitrate_entry.grid(row=19, column=1, sticky=tk.W, padx=8, pady=(2, 2))
        _abr_btn_frame = ttk.Frame(tab_dl)
        _abr_btn_frame.grid(row=19, column=2, sticky=tk.W, padx=(0, 4), pady=(2, 2))
        ttk.Button(_abr_btn_frame, text="Highest",
                   command=lambda: audio_bitrate_var.set('0')).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(_abr_btn_frame, text="Lowest",
                   command=lambda: audio_bitrate_var.set('1')).pack(side=tk.LEFT)
        ttk.Label(tab_dl, text="(0 = highest available)", font=('Arial', 8),
                  foreground="gray").grid(row=19, column=3, sticky=tk.W, padx=4)

        ttk.Label(tab_dl, text="Max video bitrate (kbps):").grid(
            row=20, column=0, sticky=tk.W, padx=8, pady=(2, 2))
        video_bitrate_var = tk.StringVar(value=str(getattr(self, 'preferred_video_bitrate', 0)))
        video_bitrate_entry = ttk.Entry(tab_dl, textvariable=video_bitrate_var, width=8)
        video_bitrate_entry.grid(row=20, column=1, sticky=tk.W, padx=8, pady=(2, 2))
        _vbr_btn_frame = ttk.Frame(tab_dl)
        _vbr_btn_frame.grid(row=20, column=2, sticky=tk.W, padx=(0, 4), pady=(2, 2))
        ttk.Button(_vbr_btn_frame, text="Highest",
                   command=lambda: video_bitrate_var.set('0')).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(_vbr_btn_frame, text="Lowest",
                   command=lambda: video_bitrate_var.set('1')).pack(side=tk.LEFT)
        ttk.Label(tab_dl, text="(0 = highest available - affects size display)", font=('Arial', 8),
                  foreground="gray").grid(row=20, column=3, sticky=tk.W, padx=4)

        ttk.Separator(tab_dl, orient=tk.HORIZONTAL).grid(
            row=21, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=8)

        # ── Network section ────────────────────────────────────────────────
        ttk.Label(tab_dl, text="Network:", font=('Arial', 9, 'bold')).grid(
            row=22, column=0, sticky=tk.W, padx=8, pady=(2, 4))

        ttk.Label(tab_dl, text="Player Client:").grid(
            row=23, column=0, sticky=tk.W, padx=8, pady=(2, 0))
        # Client list refreshed against the yt-dlp README (2026-07).
        # Ordered by cost: the no-PO-token clients first, the ones
        # that need a running bgutil server last.
        #   android_vr / visionos - no PO token, no JS challenge
        #   tv_downgraded         - what cookies force by default
        #   android / ios         - REQUIRE a GVS PO token (bgutil)
        # android_sdkless was removed from yt-dlp in Jan 2026.
        _client_opts = [
            "default",
            "android_vr",
            "android_vr,default",
            "visionos",
            "visionos,android_vr",
            "tv",
            "tv_downgraded",
            "web_embedded",
            "android",
            "ios",
            "android,default",
            "ios,android,default",
        ]
        client_var = tk.StringVar(value=self.player_client)
        client_combo = ttk.Combobox(tab_dl, textvariable=client_var,
                                    values=_client_opts, state='readonly', width=22)
        client_combo.grid(row=23, column=1, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Button(tab_dl, text="?", width=2,
                   command=self._show_player_client_help).grid(
            row=23, column=2, sticky=tk.W, padx=(2, 8), pady=(2, 0))
        ttk.Label(tab_dl,
                  text="Affects downloads, not analysis. Press ? for what each client costs.",
                  font=('Arial', 8), foreground='gray').grid(
            row=24, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        prewarm_var = tk.BooleanVar(value=self.prewarm_enabled)
        ttk.Checkbutton(tab_dl, text="Pre-warm streams before downloading",
                        variable=prewarm_var).grid(
            row=25, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="Sends a lightweight probe to YouTube's CDN before each download\n"
                       "starts. Reduces 'format not available' errors on newly uploaded videos.",
                  font=('Arial', 8), foreground='gray').grid(
            row=26, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        parallel_hardsub_var = tk.BooleanVar(value=self.parallel_hardsub)
        ttk.Checkbutton(tab_dl, text="Pre-cache streams while queue is active",
                        variable=parallel_hardsub_var).grid(
            row=27, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="When ON: while any download is running, the next N queued videos'\n"
                       "streams are downloaded and cached in the background concurrently.\n"
                       "Queue order is preserved - items only start when their turn comes.",
                  font=('Arial', 8), foreground='gray').grid(
            row=28, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        ttk.Label(tab_dl, text="Concurrent pre-cache streams:").grid(
            row=29, column=0, sticky=tk.W, padx=8, pady=(2, 0))
        precache_count_var = tk.StringVar(value=str(getattr(self, 'precache_concurrent_count', 1)))
        _pc_spin = ttk.Spinbox(tab_dl, from_=1, to=5, width=5,
                               textvariable=precache_count_var)
        _pc_spin.grid(row=29, column=1, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="Number of queued items whose streams are pre-downloaded concurrently\n"
                       "in the background. Higher values cache more ahead but share your\n"
                       "bandwidth with the active download - 1-2 is recommended.",
                  font=('Arial', 8), foreground='gray').grid(
            row=30, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        ttk.Label(tab_dl, text="Concurrent batch info fetches:").grid(
            row=31, column=0, sticky=tk.W, padx=8, pady=(2, 0))
        batch_fetch_var = tk.StringVar(value=str(getattr(self, 'batch_concurrent_fetches', 3)))
        _bf_spin = ttk.Spinbox(tab_dl, from_=1, to=8, width=5,
                               textvariable=batch_fetch_var)
        _bf_spin.grid(row=31, column=1, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="How many URLs in a batch are info-fetched simultaneously.\n"
                       "Higher = faster batch build time; lower = gentler on the API (default 3).",
                  font=('Arial', 8), foreground='gray').grid(
            row=32, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        advance_queue_var = tk.BooleanVar(value=self.advance_queue_on_streams_done)
        ttk.Checkbutton(tab_dl, text="Advance queue immediately after streams are cached",
                        variable=advance_queue_var).grid(
            row=33, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="When ON: queue advances to the next download as soon as streams are saved\n"
                       "to cache, without waiting for FFmpeg post-processing to finish.\n"
                       "Multiple FFmpeg jobs (merge, metadata, hardsub) may run concurrently.",
                  font=('Arial', 8), foreground='gray').grid(
            row=34, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        # ── Extended client fallback cascade ───────────────────────────────
        ttk.Separator(tab_dl, orient=tk.HORIZONTAL).grid(
            row=35, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=(10, 6))
        extended_cascade_var = tk.BooleanVar(value=getattr(self, 'extended_client_cascade', True))
        ttk.Checkbutton(
            tab_dl,
            text="Extended player client fallback cascade",
            variable=extended_cascade_var).grid(
            row=36, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(0, 2))
        ttk.Label(
            tab_dl,
            text="When ON: if the first download attempt fails, YSA automatically retries\n"
                 "using tv_downgraded, android_vr, web_embedded, and other player clients.\n"
                 "Recommended ON. Turn OFF for fastest single-attempt downloads.",
            font=('Arial', 8), foreground='gray').grid(
            row=37, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        # ── Cookie File (takes priority over browser cookies) ──────────────
        ttk.Label(tab_dl, text="Cookie File (.txt):").grid(
            row=38, column=0, sticky=tk.W, padx=8, pady=(2, 0))
        cookies_file_var = tk.StringVar(value=getattr(self, 'cookies_file', ''))
        cookies_file_entry = ttk.Entry(tab_dl, textvariable=cookies_file_var, width=34)
        cookies_file_entry.grid(row=38, column=1, sticky=(tk.W, tk.E), padx=(8, 2), pady=(2, 0))

        def _browse_cookies_file():
            path = filedialog.askopenfilename(
                title="Select cookies.txt",
                filetypes=[("Cookie files", "*.txt"), ("All files", "*.*")],
                initialdir=SCRIPT_DIR)
            if path:
                cookies_file_var.set(path)
                _update_cookie_age_label(path)

        def _clear_cookies_file():
            cookies_file_var.set('')
            _cookie_age_label.config(text='', foreground='gray')

        _cf_btn_frame = ttk.Frame(tab_dl)
        _cf_btn_frame.grid(row=38, column=2, sticky=tk.W, padx=(0, 4), pady=(2, 0))
        ttk.Button(_cf_btn_frame, text="Browse", command=_browse_cookies_file).pack(side=tk.LEFT, padx=(0, 2))
        ttk.Button(_cf_btn_frame, text="Clear", command=_clear_cookies_file).pack(side=tk.LEFT)

        def _update_cookie_age_label(path=None):
            p = path or cookies_file_var.get()
            if p and os.path.isfile(p):
                try:
                    age_days = (time.time() - os.path.getmtime(p)) / 86400
                    if age_days < 1:
                        age_str = 'Fresh (today)'
                        col = 'green'
                    elif age_days < 7:
                        age_str = str(int(age_days)) + ' day(s) old - OK'
                        col = 'green'
                    else:
                        age_str = str(int(age_days)) + ' days old - consider re-exporting'
                        col = 'orange'
                    _cookie_age_label.config(text=age_str, foreground=col)
                except Exception:
                    _cookie_age_label.config(text='', foreground='gray')
            else:
                _cookie_age_label.config(text='No file selected', foreground='gray')

        _cookie_age_label = ttk.Label(tab_dl, text='', font=('Arial', 8))
        _cookie_age_label.grid(row=39, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 2))
        _update_cookie_age_label()

        ttk.Label(tab_dl,
                  text="Recommended: export cookies from a fresh incognito YouTube session\n"
                       "using the 'Get cookies.txt LOCALLY' extension, then select the file here.\n"
                       "This is more reliable than browser cookie extraction and works while\n"
                       "your browser is open. Place cookies.txt next to YSA.exe to auto-load it.",
                  font=('Arial', 8), foreground='gray').grid(
            row=40, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        # ── Browser Cookies (fallback) ──────────────────────────────────────
        ttk.Label(tab_dl, text="Browser Cookies (fallback):").grid(
            row=41, column=0, sticky=tk.W, padx=8, pady=(2, 0))
        _browser_opts = ['none', 'firefox', 'chrome', 'edge', 'brave', 'chromium', 'opera', 'safari', 'vivaldi']
        cookies_browser_var = tk.StringVar(value=getattr(self, 'cookies_browser', 'none'))
        cookies_browser_combo = ttk.Combobox(tab_dl, textvariable=cookies_browser_var,
                                             values=_browser_opts, state='readonly', width=20)
        cookies_browser_combo.grid(row=41, column=1, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="Only used when no cookie file is set above.\n"
                       "Firefox is unreliable while the browser is open (SQLite lock).",
                  font=('Arial', 8), foreground='gray').grid(
            row=42, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        ttk.Label(tab_dl, text="Hardsub encoder:").grid(
            row=43, column=0, sticky=tk.W, padx=8, pady=(2, 0))
        hardsub_enc_var = tk.StringVar(value=getattr(self, 'hardsub_encoder', 'libx264'))
        ttk.Combobox(tab_dl, textvariable=hardsub_enc_var,
                     values=('auto', 'libx264'), state='readonly', width=20).grid(
            row=43, column=1, sticky=tk.W, padx=8, pady=(2, 0))
        ttk.Label(tab_dl,
                  text="'libx264' (default) encodes in software - measured 2-3x\n"
                       "FASTER than hardware here, because the subtitle filter is\n"
                       "CPU-only and forces a GPU round trip per frame.\n"
                       "'auto' probes NVENC / QSV / AMF and uses the first that\n"
                       "works - worth trying on a discrete GPU. Hardware failures\n"
                       "self-demote to libx264 for the session.",
                  font=('Arial', 8), foreground='gray').grid(
            row=44, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        # ── Tab 3: Cache ───────────────────────────────────────────────────
        tab_cache = ttk.Frame(notebook)
        tab_cache.columnconfigure(1, weight=1)

        # ── Open YSA Cache root folder ─────────────────────────────────────
        def _open_ysa_root():
            p = getattr(self, 'ysa_cache_root', None)
            if not p or not os.path.isdir(p):
                self._notify_warning("Open Folder",
                    "YSA Cache folder does not exist:\n" + (p or "Not set"))
                return
            try:
                if sys.platform == 'win32':
                    os.startfile(p)
                elif sys.platform == 'darwin':
                    subprocess.Popen(['open', p], close_fds=True)
                else:
                    subprocess.Popen(['xdg-open', p], close_fds=True)
            except Exception as e:
                self._notify_error("Open Folder", "Could not open folder:\n" + str(e))

        ysa_root_frame = ttk.Frame(tab_cache)
        ysa_root_frame.grid(row=0, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(10, 4))
        ttk.Button(ysa_root_frame, text="Open YSA Cache Folder",
                   command=_open_ysa_root).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Label(ysa_root_frame,
                  text=getattr(self, 'ysa_cache_root', None) or "Not set",
                  foreground="gray", font=('Arial', 8)).pack(side=tk.LEFT)

        ttk.Separator(tab_cache, orient=tk.HORIZONTAL).grid(
            row=1, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=(0, 4))

        # Live cache size label (computed in background)
        cache_size_var = tk.StringVar(value="Calculating...")
        ttk.Label(tab_cache, text="Cache Size:").grid(
            row=2, column=0, sticky=tk.W, padx=8, pady=(4, 4))
        cache_size_lbl = ttk.Label(tab_cache, textvariable=cache_size_var,
                                   foreground="blue")
        cache_size_lbl.grid(row=2, column=1, sticky=tk.W, padx=8, pady=(4, 4))

        def _refresh_cache_size():
            try:
                mb = self._get_cache_size_mb()
                total_streams = sum(len(v) for v in self.cached_videos.values())
                cache_size_var.set("{:.1f} MB  ({} streams)".format(mb, total_streams))
            except Exception:
                cache_size_var.set("unavailable")

        dialog.after(100, _refresh_cache_size)

        ttk.Label(tab_cache, text="Max Cache (MB):").grid(
            row=3, column=0, sticky=tk.W, padx=8, pady=4)
        max_cache_var = tk.StringVar(value=str(self.max_cache_mb))
        max_cache_entry = ttk.Entry(tab_cache, textvariable=max_cache_var, width=10)
        max_cache_entry.grid(row=3, column=1, sticky=tk.W, padx=8, pady=4)
        ttk.Label(tab_cache, text="(0 = unlimited)", font=('Arial', 8),
                  foreground="gray").grid(row=3, column=2, sticky=tk.W, padx=4)

        pc_var = tk.BooleanVar(value=self.persistent_cache_var.get())
        pc_cb = ttk.Checkbutton(tab_cache, text="Keep cache between sessions",
                                variable=pc_var)
        pc_cb.grid(row=4, column=0, columnspan=3, sticky=tk.W, padx=8, pady=4)
        ttk.Label(tab_cache, text="(Cache is deleted on exit by default)",
                  font=('Arial', 8), foreground="gray").grid(
            row=5, column=0, columnspan=3, sticky=tk.W, padx=24)

        cce_var = tk.BooleanVar(value=self.clear_cache_on_exit)
        cce_cb = ttk.Checkbutton(tab_cache,
                                 text="Delete ALL cache folders when the app closes",
                                 variable=cce_var)
        cce_cb.grid(row=6, column=0, columnspan=3, sticky=tk.W, padx=8, pady=4)

        def _sync_cache_exclusive():
            """The two are opposites: keeping the cache and wiping it on exit
            cannot both apply. Grey out whichever the other rules out.

            Both OFF is still valid - that is the default, where only the
            stream folders are cleared and the yt-dlp cache is kept.
            """
            try:
                cce_cb.config(state='disabled' if pc_var.get() else 'normal')
                pc_cb.config(state='disabled' if cce_var.get() else 'normal')
            except Exception:
                pass
        # A config edited by hand could set both; the explicit destructive
        # instruction wins, otherwise BOTH would grey out and neither could
        # be changed again.
        if pc_var.get() and cce_var.get():
            pc_var.set(False)
        pc_cb.config(command=_sync_cache_exclusive)
        cce_cb.config(command=_sync_cache_exclusive)
        _sync_cache_exclusive()
        ttk.Label(tab_cache,
                  text="(Same as the Clear Cache button: removes ysa_cache and"
                       " the developer sandboxes. Overrides 'Keep cache"
                       " between sessions'.)",
                  font=('Arial', 8), foreground="gray", wraplength=520,
                  justify=tk.LEFT).grid(
            row=7, column=0, columnspan=3, sticky=tk.W, padx=24)

        def clear_cache_now():
            self.clear_video_cache()
            dialog.after(200, _refresh_cache_size)

        ttk.Button(tab_cache, text="Clear Cache Now", command=clear_cache_now).grid(
            row=8, column=0, sticky=tk.W, padx=8, pady=8)

        ttk.Separator(tab_cache, orient=tk.HORIZONTAL).grid(
            row=9, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=4)

        def _open_folder(path):
            """Open a folder in Windows Explorer (or file manager on other OS)."""
            if not path or not os.path.isdir(path):
                self._notify_warning("Cache Folder",
                    "Cache folder does not exist or is not set:\n" + (path or "None"))
                return
            try:
                if sys.platform == 'win32':
                    os.startfile(path)
                elif sys.platform == 'darwin':
                    subprocess.Popen(['open', path], close_fds=True)
                else:
                    subprocess.Popen(['xdg-open', path], close_fds=True)
            except Exception as e:
                self._notify_error("Open Folder", "Could not open folder:\n" + str(e))

        ttk.Label(tab_cache, text="Video Cache Path:", font=('Arial', 8)).grid(
            row=10, column=0, sticky=tk.W, padx=8, pady=2)
        ttk.Label(tab_cache, text=self.video_cache_dir or "Disabled",
                  foreground="gray", font=('Arial', 8)).grid(
            row=10, column=1, sticky=tk.W, padx=8, pady=2)
        ttk.Button(tab_cache, text="Open Folder",
                   command=lambda: _open_folder(self.video_cache_dir)).grid(
            row=10, column=2, sticky=tk.W, padx=4, pady=2)

        ttk.Label(tab_cache, text="Audio Cache Path:", font=('Arial', 8)).grid(
            row=11, column=0, sticky=tk.W, padx=8, pady=2)
        ttk.Label(tab_cache, text=self.audio_cache_dir or "Disabled",
                  foreground="gray", font=('Arial', 8)).grid(
            row=11, column=1, sticky=tk.W, padx=8, pady=2)
        ttk.Button(tab_cache, text="Open Folder",
                   command=lambda: _open_folder(self.audio_cache_dir)).grid(
            row=11, column=2, sticky=tk.W, padx=4, pady=2)

        ttk.Label(tab_cache, text="yt-dlp Cache Path:", font=('Arial', 8)).grid(
            row=12, column=0, sticky=tk.W, padx=8, pady=2)
        ttk.Label(tab_cache, text=self.yt_dlp_cache_dir or "Disabled",
                  foreground="gray", font=('Arial', 8)).grid(
            row=12, column=1, sticky=tk.W, padx=8, pady=2)
        ttk.Button(tab_cache, text="Open Folder",
                   command=lambda: _open_folder(self.yt_dlp_cache_dir)).grid(
            row=12, column=2, sticky=tk.W, padx=4, pady=2)

        ttk.Separator(tab_cache, orient=tk.HORIZONTAL).grid(
            row=13, column=0, columnspan=3, sticky=(tk.W, tk.E), padx=8, pady=(8, 4))

        ttk.Label(tab_cache,
                  text="Preserve when Clear Cache Now is pressed:").grid(
            row=14, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(2, 0))
        preserve_logs_var = tk.BooleanVar(value=getattr(self, 'preserve_logs_on_clear', True))
        preserve_ytdlp_var = tk.BooleanVar(value=getattr(self, 'preserve_ytdlp_on_clear', False))
        preserve_hist_var = tk.BooleanVar(value=getattr(self, 'preserve_history_on_clear', False))
        _pres_frame = ttk.Frame(tab_cache)
        _pres_frame.grid(row=15, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(2, 0))
        ttk.Checkbutton(_pres_frame, text="Session logs",
                        variable=preserve_logs_var).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Checkbutton(_pres_frame, text="yt-dlp cache",
                        variable=preserve_ytdlp_var).pack(side=tk.LEFT, padx=(0, 12))
        ttk.Checkbutton(_pres_frame, text="Download history",
                        variable=preserve_hist_var).pack(side=tk.LEFT)
        ttk.Label(tab_cache,
                  text="Clear Cache Now deletes the cache folders, the state folders\n"
                       "and the download history. Ticked items survive it.\n"
                       "Clearing the cache on EXIT only ever touches ysa_cache -\n"
                       "it ignores these boxes entirely.",
                  font=('Arial', 8), foreground='gray').grid(
            row=16, column=0, columnspan=3, sticky=tk.W, padx=24, pady=(0, 6))

        _ytc_frame = ttk.Frame(tab_cache)
        _ytc_frame.grid(row=17, column=0, columnspan=3, sticky=tk.W, padx=8, pady=(2, 10))
        ttk.Button(_ytc_frame, text="Clear yt-dlp Cache",
                   command=self.clear_ytdlp_cache).pack(side=tk.LEFT, padx=(0, 8))
        ttk.Label(_ytc_frame,
                  text="Fixes stale-extractor errors. Streams, logs and history untouched.",
                  font=('Arial', 8), foreground='gray').pack(side=tk.LEFT)

        # ── Tab 4: bgutil PO Token Provider ────────────────────────────────
        tab_bgutil = ttk.Frame(notebook)
        tab_bgutil.columnconfigure(1, weight=1)

        # Detect whether a pre-compiled bundle is available in this exe
        _has_bundle = self._bgutil_bundled_dir() is not None

        # ── Bundle notice (shown when exe was built with bundled server) ──
        if _has_bundle:
            _bundle_lbl = ttk.Label(
                tab_bgutil,
                text="Bundled server: INCLUDED in this exe (pre-compiled by GitHub Actions)",
                font=('Arial', 9, 'bold'), foreground='green')
            _bundle_lbl.grid(row=0, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(10, 2))
            ttk.Label(
                tab_bgutil,
                text="No npm, no internet, no manual setup needed.\n"
                     "Just click Install Plugin then Start Server below.",
                font=('Arial', 8), foreground='gray').grid(
                row=1, column=0, columnspan=4, sticky=tk.W, padx=24, pady=(0, 6))
        else:
            ttk.Label(
                tab_bgutil,
                text="Bundled server: NOT PRESENT (build the exe via GitHub Actions)",
                font=('Arial', 9, 'bold'), foreground='orange').grid(
                row=0, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(10, 2))
            ttk.Label(
                tab_bgutil,
                text="Running from source: trigger the GitHub Actions build to get\n"
                     "a self-contained exe with the bgutil server pre-compiled inside.",
                font=('Arial', 8), foreground='gray').grid(
                row=1, column=0, columnspan=4, sticky=tk.W, padx=24, pady=(0, 6))

        ttk.Separator(tab_bgutil, orient=tk.HORIZONTAL).grid(
            row=2, column=0, columnspan=4, sticky=(tk.W, tk.E), padx=8, pady=4)

        # ── Status row ────────────────────────────────────────────────────
        ttk.Label(tab_bgutil, text="Status:", font=('Arial', 9, 'bold')).grid(
            row=3, column=0, sticky=tk.W, padx=8, pady=(8, 2))
        self._bgutil_status_label = ttk.Label(tab_bgutil, text="Checking...", font=('Arial', 9))
        self._bgutil_status_label.grid(
            row=3, column=1, columnspan=2, sticky=tk.W, padx=8, pady=(8, 2))

        def _refresh_bgutil_status():
            # Off the main thread: this probes an HTTP endpoint and then a
            # raw TCP port. When the server is not running (the common case)
            # a firewall that DROPS rather than refuses makes both wait out
            # their timeouts, freezing the dialog as it opens.
            try:
                self._bgutil_status_label.config(text="Checking...")
            except Exception:
                pass
            threading.Thread(
                target=lambda: self._bgutil_refresh_status(update_ui=True),
                daemon=True).start()

        ttk.Button(tab_bgutil, text="Refresh", command=_refresh_bgutil_status).grid(
            row=3, column=3, sticky=tk.W, padx=4, pady=(8, 2))

        # ── Auto-start toggle ─────────────────────────────────────────────
        bgutil_autostart_var = tk.BooleanVar(value=getattr(self, 'bgutil_autostart', False))
        def _on_autostart_toggle():
            self.bgutil_autostart = bgutil_autostart_var.get()
            self._save_config()
        ttk.Checkbutton(tab_bgutil, text="Auto-start server when YSA opens",
                        variable=bgutil_autostart_var,
                        command=_on_autostart_toggle).grid(
            row=4, column=0, columnspan=2, sticky=tk.W, padx=8, pady=(4, 2))

        # ── Keep running on exit toggle ───────────────────────────────────
        bgutil_keep_running_var = tk.BooleanVar(value=getattr(self, 'bgutil_keep_running', True))
        def _on_keep_running_toggle():
            self.bgutil_keep_running = bgutil_keep_running_var.get()
            self._save_config()
        ttk.Checkbutton(tab_bgutil, text="Keep server running when YSA closes",
                        variable=bgutil_keep_running_var,
                        command=_on_keep_running_toggle).grid(
            row=4, column=2, columnspan=2, sticky=tk.W, padx=8, pady=(4, 2))

        ttk.Label(tab_bgutil,
                  text="Auto-start launches the server on open. Keep-running leaves it alive after YSA exits.",
                  font=('Arial', 8), foreground='gray').grid(
            row=5, column=0, columnspan=4, sticky=tk.W, padx=24, pady=(0, 6))

        ttk.Separator(tab_bgutil, orient=tk.HORIZONTAL).grid(
            row=6, column=0, columnspan=4, sticky=(tk.W, tk.E), padx=8, pady=6)

        # ── Server bundle location (always shown) ─────────────────────────
        # Auto-detect the bundle path if the user hasn't set one manually.
        _detected_bundle = self._bgutil_bundled_dir() or ''
        _current_path = getattr(self, 'bgutil_server_path', '') or _detected_bundle
        ttk.Label(tab_bgutil, text="Server Bundle:", font=('Arial', 9, 'bold')).grid(
            row=7, column=0, sticky=tk.W, padx=8, pady=(4, 2))
        bgutil_path_var = tk.StringVar(value=_current_path)
        ttk.Entry(tab_bgutil, textvariable=bgutil_path_var, width=34).grid(
            row=7, column=1, columnspan=2, sticky=(tk.W, tk.E), padx=(8, 2), pady=(4, 2))

        def _browse_bgutil_path():
            path = filedialog.askdirectory(
                title="Select the bgutil bundle folder (contains build/main.js)")
            if path:
                bgutil_path_var.set(path)
                self.bgutil_server_path = path
                self._save_config()

        ttk.Button(tab_bgutil, text="Browse", command=_browse_bgutil_path).grid(
            row=7, column=3, sticky=tk.W, padx=4, pady=(4, 2))
        _bundle_hint = ('Auto-detected: ' + _detected_bundle) if _detected_bundle else 'Browse to select the folder containing build/main.js'
        ttk.Label(tab_bgutil,
                  text=_bundle_hint,
                  font=('Arial', 8), foreground='gray').grid(
            row=8, column=1, columnspan=3, sticky=tk.W, padx=8, pady=(0, 6))

        ttk.Separator(tab_bgutil, orient=tk.HORIZONTAL).grid(
            row=9, column=0, columnspan=4, sticky=(tk.W, tk.E), padx=8, pady=6)

        # ── Server URL ────────────────────────────────────────────────────
        ttk.Label(tab_bgutil, text="Server URL:").grid(
            row=10, column=0, sticky=tk.W, padx=8, pady=(4, 2))
        bgutil_url_var = tk.StringVar(value=getattr(self, 'bgutil_server_url', 'http://127.0.0.1:4416'))
        ttk.Entry(tab_bgutil, textvariable=bgutil_url_var, width=30).grid(
            row=10, column=1, columnspan=2, sticky=(tk.W, tk.E), padx=8, pady=(4, 2))
        ttk.Label(tab_bgutil, text="Leave as default unless you changed the port.",
                  font=('Arial', 8), foreground='gray').grid(
            row=11, column=1, columnspan=3, sticky=tk.W, padx=8, pady=(0, 6))

        ttk.Separator(tab_bgutil, orient=tk.HORIZONTAL).grid(
            row=12, column=0, columnspan=4, sticky=(tk.W, tk.E), padx=8, pady=6)

        # ── Action buttons ────────────────────────────────────────────────
        _bgutil_btn_frame = ttk.Frame(tab_bgutil)
        _bgutil_btn_frame.grid(row=13, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(0, 4))

        # Setup progress label
        _bgutil_progress_lbl = ttk.Label(tab_bgutil, text='', font=('Arial', 8), foreground='gray')
        _bgutil_progress_lbl.grid(row=14, column=0, columnspan=4, sticky=tk.W, padx=8, pady=(2, 4))

        def _save_bgutil_settings():
            self.bgutil_server_path = bgutil_path_var.get().strip()
            self.bgutil_autostart   = bgutil_autostart_var.get()
            self.bgutil_keep_running = bgutil_keep_running_var.get()
            self.bgutil_server_url  = bgutil_url_var.get().strip() or 'http://127.0.0.1:4416'
            self._save_config()

        def _bgutil_run_setup():
            """Run npm ci + npx tsc inside the server folder - no terminal needed."""
            _save_bgutil_settings()
            server_path = self.bgutil_server_path
            if not server_path or not os.path.isdir(server_path):
                self._notify_warning("bgutil Setup",
                    "Please select the server folder first (Browse button above).")
                return
            pkg_json = os.path.join(server_path, 'package.json')
            if not os.path.isfile(pkg_json):
                self._notify_error("bgutil Setup",
                    "package.json not found in selected folder.\n"
                    "Make sure you selected the 'server' subfolder from the zip.")
                return

            # Check write permission BEFORE starting npm.
            # WinError 5 (Access Denied) happens when the folder is in a protected
            # location such as Program Files, Windows, or Desktop shortcuts.
            _test_file = os.path.join(server_path, '_ysa_write_test.tmp')
            try:
                with open(_test_file, 'w') as _tf:
                    _tf.write('test')
                os.remove(_test_file)
            except OSError:
                _safe = os.path.join(os.path.expanduser('~'), 'bgutil-server')
                self._notify_error(
                    "bgutil Setup - Access Denied",
                    "Windows is blocking write access to:\n"
                    + server_path + "\n\n"
                    "npm needs to create a node_modules folder there but can't.\n\n"
                    "Fix: move the server folder somewhere you own, e.g.:\n"
                    + _safe + "\n\n"
                    "Steps:\n"
                    "1. Copy the server folder to that path using File Explorer\n"
                    "2. Click Browse above and select the new location\n"
                    "3. Click Run Setup again\n\n"
                    "Do NOT place it inside Program Files, Windows,\n"
                    "or any other system-protected folder.")
                return

            def _run():
                # Run npm and tsc via node.exe directly - avoids .cmd wrappers
                # which fail with WinError 5 when Command Prompt is blocked by policy.
                node_exe = self._find_node_exe()
                npm_js   = self._get_npm_script(node_exe)
                if not npm_js:
                    self.append_terminal_output(
                        'bgutil setup: Cannot find npm-cli.js - is Node.js installed correctly?\n'
                        'Expected it at <nodejs>\\node_modules\\npm\\bin\\npm-cli.js\n', 'error')
                    self.root.after(0, lambda:
                        _bgutil_progress_lbl.config(
                            text='npm-cli.js not found - reinstall Node.js from nodejs.org',
                            foreground='red'))
                    return
                self.append_terminal_output(
                    'bgutil setup: node=' + node_exe + '\n'
                    'bgutil setup: npm-cli=' + npm_js + '\n', 'info')
                # Set CI=true so npm disables its TTY-dependent exit handler.
                # Without this, npm raises 'Exit handler never called!' when
                # run as a headless subprocess (no terminal attached).
                npm_env = os.environ.copy()
                npm_env['CI'] = 'true'
                npm_env['npm_config_loglevel'] = 'error'
                npm_env['npm_config_fund'] = 'false'
                npm_env['npm_config_audit'] = 'false'
                # Use a local cache dir inside the server folder.
                # The default AppData\Local\npm-cache may be blocked by Group Policy
                # (EACCES on every fetch even though packages are already cached).
                _local_cache = os.path.join(server_path, '.npm-cache')
                npm_env['npm_config_cache'] = _local_cache

                steps = [
                    ('Installing dependencies (npm ci)...',
                     [node_exe, npm_js, 'ci', '--no-fund', '--no-audit',
                      '--cache', _local_cache]),
                    # After npm ci, tsc is in node_modules - run it via node directly
                    ('Compiling TypeScript (tsc)...',
                     [node_exe,
                      os.path.join(server_path, 'node_modules', 'typescript', 'bin', 'tsc')]),
                ]
                for label, cmd in steps:
                    self.root.after(0, lambda l=label:
                        _bgutil_progress_lbl.config(text=l, foreground='gray'))
                    self.append_terminal_output('bgutil setup: ' + label + '\n', 'info')
                    try:
                        proc = subprocess.run(
                            cmd, cwd=server_path,
                            capture_output=True, text=True, encoding='utf-8', errors='replace',
                            stdin=subprocess.DEVNULL,
                            env=npm_env,
                            creationflags=CREATE_NO_WINDOW)
                        if proc.returncode != 0:
                            err = (proc.stderr or proc.stdout or 'unknown error').strip()
                            # Show last 20 lines - npm output can be very long
                            err_tail = '\n'.join(err.splitlines()[-20:])
                            self.append_terminal_output(
                                'bgutil setup FAILED:\n' + err_tail + '\n', 'error')
                            self.root.after(0, lambda e=err_tail:
                                _bgutil_progress_lbl.config(
                                    text='Setup failed - see terminal for details', foreground='red'))
                            return
                        self.append_terminal_output(
                            'bgutil setup: ' + label + ' done.\n', 'success')
                    except FileNotFoundError:
                        # If even the .cmd fallback fails, Node.js is truly not installed
                        self.append_terminal_output(
                            'bgutil setup: Node.js not found.\n'
                            'Install Node.js 20+ from nodejs.org, restart YSA, then retry.\n',
                            'error')
                        self.root.after(0, lambda:
                            _bgutil_progress_lbl.config(
                                text='Node.js not found - install from nodejs.org then restart YSA',
                                foreground='red'))
                        return
                    except Exception as exc:
                        self.append_terminal_output(
                            'bgutil setup error: ' + str(exc) + '\n', 'error')
                        self.root.after(0, lambda e=str(exc):
                            _bgutil_progress_lbl.config(
                                text='Error: ' + e[:80], foreground='red'))
                        return
                self.root.after(0, lambda:
                    _bgutil_progress_lbl.config(
                        text='Setup complete! Click Step 3: Start Server.', foreground='green'))
                self.append_terminal_output(
                    'bgutil setup complete - click Start Server.\n', 'success')

            threading.Thread(target=_run, daemon=True).start()

        def _bgutil_start():
            _save_bgutil_settings()
            self.append_terminal_output('bgutil: starting server...\n', 'info')
            def _do_start():
                # Stop any existing server first so Start also works as Restart
                if self._bgutil_check_server():
                    self.root.after(0, lambda: self.append_terminal_output(
                        'bgutil: stopping existing server...\n', 'info'))
                    self._bgutil_stop_server()
                    time.sleep(1)  # brief pause for port to be released
                ok = self._bgutil_start_server()
                self.root.after(0, _refresh_bgutil_status)
                if not ok:
                    self.root.after(0, lambda:
                        _bgutil_progress_lbl.config(
                            text='Server failed to start - run Setup first.',
                            foreground='red'))
                else:
                    self.root.after(0, lambda:
                        _bgutil_progress_lbl.config(text='', foreground='gray'))
            threading.Thread(target=_do_start, daemon=True).start()

        def _bgutil_stop():
            """Stop the bgutil server in a background thread."""
            def _do_stop():
                self._bgutil_stop_server()
                self.root.after(0, _refresh_bgutil_status)
            threading.Thread(target=_do_stop, daemon=True).start()

        def _bgutil_install():
            """Install the embedded plugin files - no zip download needed."""
            ok, result = self._bgutil_install_plugin()
            if ok:
                self.append_terminal_output(
                    'bgutil: Plugin installed to ' + result + '\n', 'success')
                self.root.after(0, lambda:
                    _bgutil_progress_lbl.config(
                        text='Plugin installed! Now run Setup then Start Server.',
                        foreground='green'))
                _refresh_bgutil_status()
            else:
                self.append_terminal_output(
                    'bgutil: Plugin install failed: ' + result + '\n', 'error')
                self.root.after(0, lambda:
                    _bgutil_progress_lbl.config(
                        text='Install failed: ' + result[:80], foreground='red'))

        ttk.Button(_bgutil_btn_frame, text="Step 1: Install Plugin",
                   command=_bgutil_install).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(_bgutil_btn_frame, text="Step 2: Run Setup",
                   command=_bgutil_run_setup).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(_bgutil_btn_frame, text="Step 3: Start Server",
                   command=_bgutil_start).pack(side=tk.LEFT, padx=(0, 4))
        ttk.Button(_bgutil_btn_frame, text="Stop Server",
                   command=_bgutil_stop).pack(side=tk.LEFT, padx=(0, 8))

        # row 15, not 12: at 12 this separator shared a cell with the one
        # above the action buttons, so Tk drew one over the other and the
        # guide divider appeared ABOVE the buttons instead of below them.
        ttk.Separator(tab_bgutil, orient=tk.HORIZONTAL).grid(
            row=15, column=0, columnspan=4, sticky=(tk.W, tk.E), padx=8, pady=6)

        # ── Plain-English setup guide (no terminal required) ──────────────
        if _has_bundle:
            guide = (
                "Quick Setup (bundled exe - no npm or internet needed):\n"
                "\n"
                "1. Make sure Node.js 20+ is installed (nodejs.org .msi installer).\n"
                "   Node.js is only needed to RUN the server, not to compile it.\n"
                "\n"
                "2. Click  Step 1: Install Plugin\n"
                "   Writes plugin files next to YSA.exe - one click, instant.\n"
                "\n"
                "3. Click  Step 3: Start Server\n"
                "   YSA extracts the pre-compiled server and starts it.\n"
                "   No npm, no compilation, no internet required.\n"
                "\n"
                "4. Click  Refresh - both should show green.\n"
                "   Tick  Auto-start  so it launches with YSA every time.\n"
                "\n"
                "   Plugin version: " + _BGUTIL_PLUGIN_VERSION + "\n"
                "   Tokens cached 6 hours - no slowdown per download."
            )
        else:
            guide = (
                "Running from source (no bundled server):\n"
                "\n"
                "The bundled server is only available in the GitHub Actions build.\n"
                "Trigger the workflow at github.com/<your-repo>/actions\n"
                "to build an exe with the bgutil server pre-compiled inside.\n"
                "\n"
                "Once you have the built exe, the setup is just 3 clicks:\n"
                "  Install Plugin → Start Server → Refresh\n"
                "\n"
                "   Plugin version: " + _BGUTIL_PLUGIN_VERSION
            )
        ttk.Label(tab_bgutil, text=guide,
                  font=('Consolas', 8), foreground='gray', justify=tk.LEFT).grid(
            row=16, column=0, columnspan=4, sticky=tk.W, padx=12, pady=(0, 8))

        # Refresh status when tab becomes visible
        tab_bgutil.bind('<Visibility>', lambda e: _refresh_bgutil_status())
        self.root.after(600, _refresh_bgutil_status)

        # ── Audio tab: how audio-only downloads are encoded and named ────
        tab_audio = ttk.Frame(notebook)
        tab_audio.columnconfigure(1, weight=1)
        _a_row = [0]

        def _a_next():
            _a_row[0] += 1
            return _a_row[0]

        def _a_hint(text):
            ttk.Label(tab_audio, text=text, font=('Arial', 8),
                      foreground='gray', justify=tk.LEFT, wraplength=560).grid(
                row=_a_next(), column=0, columnspan=3, sticky=tk.W, padx=14,
                pady=(0, 2))

        def _a_combo(label, attr, choices, default, hint=''):
            """choices: list of (display_text, stored_value)."""
            r = _a_next()
            ttk.Label(tab_audio, text=label).grid(
                row=r, column=0, sticky=tk.W, padx=10, pady=(8, 0))
            _disp = [c[0] for c in choices]
            _cur = getattr(self, attr, default)
            _sel = next((c[0] for c in choices if c[1] == _cur), _disp[0])
            _var = tk.StringVar(value=_sel)
            _cb = ttk.Combobox(tab_audio, textvariable=_var, values=_disp,
                               state='readonly', width=36)
            _cb.grid(row=r, column=1, sticky=tk.W, padx=10, pady=(8, 0))

            def _on(_e=None, a=attr, c=choices, v=_var):
                for _d, _val in c:
                    if _d == v.get():
                        setattr(self, a, _val)
                        break
                self._save_config_now()
            _cb.bind('<<ComboboxSelected>>', _on)
            if hint:
                _a_hint(hint)
            return _var

        _a_combo("When the stream is Opus:", 'audio_opus_naming', [
            ("Name by actual codec (.webm/.opus)", 'codec'),
            ("Force .m4a extension", 'm4a'),
            ("Remux into a real M4A container", 'remux'),
            ("Prefer a real AAC stream instead", 'prefer_aac'),
        ], 'codec',
            "M4A Native wrote every stream to .m4a regardless of codec, so an"
            " Opus pick became an .m4a that iTunes, iOS and many car stereos"
            " refuse to play. Naming by codec keeps the file honest.")

        _a_combo("Transcode output bitrate:", 'audio_bitrate_policy', [
            ("Match source - never upsample", 'match_source'),
            ("Match my preferred bitrate", 'match_pref'),
            ("Fixed bitrate (below)", 'fixed'),
            ("Maximum quality (old behaviour)", 'max'),
        ], 'match_source',
            "Encoders were hardcoded (AAC 128k, MP3 V0), so picking the"
            " smallest source stream then transcoding produced files about"
            " 2.5x LARGER than the stream they came from, with no quality"
            " gain. Nothing can restore detail already lost in the source.")

        _r = _a_next()
        ttk.Label(tab_audio, text="Fixed bitrate (kbps):").grid(
            row=_r, column=0, sticky=tk.W, padx=10, pady=(8, 0))
        _fb_var = tk.StringVar(value=str(getattr(self, 'audio_fixed_bitrate', 128)))

        def _on_fixed_bitrate(*_a):
            try:
                self.audio_fixed_bitrate = max(32, min(320, int(_fb_var.get())))
            except Exception:
                return
            self._save_config_now()
        _fb_spin = ttk.Spinbox(tab_audio, from_=32, to=320, increment=16,
                               textvariable=_fb_var, width=8,
                               command=_on_fixed_bitrate)
        _fb_spin.grid(row=_r, column=1, sticky=tk.W, padx=10, pady=(8, 0))
        _fb_spin.bind('<FocusOut>', _on_fixed_bitrate)

        _a_combo("Loudness-compressed (DRC) streams:", 'audio_drc_pref', [
            ("Avoid DRC variants", 'avoid'),
            ("Allow either", 'allow'),
            ("Prefer DRC variants", 'prefer'),
        ], 'avoid',
            "YouTube offers '-drc' renditions that are loudness-flattened and"
            " audibly different from the normal stream.")

        _a_combo("Quality tag on audio filenames:", 'audio_quality_tag', [
            ("Audio bitrate (e.g. 48kbps)", 'audio'),
            ("Video quality (e.g. 720p)", 'video'),
            ("No quality tag", 'none'),
        ], 'audio',
            "Audio-only downloads fetch the same stream at every video"
            " quality, so a [720p] tag implied a difference that did not"
            " exist - two identically-sized files with different names.")

        _a_combo("If no AAC stream exists (M4A AAC):", 'audio_no_aac_action', [
            ("Transcode from Opus", 'transcode'),
            ("Keep the Opus stream as-is", 'keep_opus'),
            ("Fail with a message", 'skip'),
        ], 'transcode',
            "Some videos publish no AAC audio at all, so AAC mode always"
            " transcodes for them - which costs time and enlarges the file.")

        _a_combo("Duplicate output files:", 'audio_duplicate_action', [
            ("Number them: name (2).m4a", 'number'),
            ("Overwrite the existing file", 'overwrite'),
            ("Skip - keep the existing file", 'skip'),
        ], 'number')

        _r = _a_next()
        _cache_audio_var = tk.BooleanVar(
            value=bool(getattr(self, 'audio_cache_streams', True)))

        def _on_cache_audio():
            self.audio_cache_streams = bool(_cache_audio_var.get())
            self._save_config_now()
        ttk.Checkbutton(tab_audio,
                        text="Cache audio streams from audio-only downloads",
                        variable=_cache_audio_var,
                        command=_on_cache_audio).grid(
            row=_r, column=0, columnspan=2, sticky=tk.W, padx=10, pady=(10, 0))
        _a_hint("Without this the same audio is re-fetched every time - field"
                " logs show one stream pulled eight times in a single session.")

        _r = _a_next()
        ttk.Label(tab_audio, text="Audio output folder:").grid(
            row=_r, column=0, sticky=tk.W, padx=10, pady=(10, 0))
        _af_lbl = ttk.Label(
            tab_audio,
            text=(getattr(self, 'audio_output_folder', '') or "(same as Download Folder)"),
            foreground='gray')
        _af_lbl.grid(row=_r, column=1, sticky=tk.W, padx=10, pady=(10, 0))

        def _pick_audio_folder():
            _d = filedialog.askdirectory(title="Choose audio output folder")
            if _d:
                self.audio_output_folder = _d
                _af_lbl.config(text=_d)
                self._save_config_now()

        def _clear_audio_folder():
            self.audio_output_folder = ''
            _af_lbl.config(text="(same as Download Folder)")
            self._save_config_now()
        _r2 = _a_next()
        ttk.Button(tab_audio, text="Browse...", command=_pick_audio_folder).grid(
            row=_r2, column=0, sticky=tk.W, padx=10, pady=(2, 0))
        ttk.Button(tab_audio, text="Use download folder",
                   command=_clear_audio_folder).grid(
            row=_r2, column=1, sticky=tk.W, padx=10, pady=(2, 0))

        # ── Interface tab ─────────────────────────────────────────────────
        tab_iface = ttk.Frame(notebook)
        tab_iface.columnconfigure(1, weight=1)
        _rw_var = tk.BooleanVar(value=bool(getattr(self, 'remember_window', True)))

        def _on_remember_window():
            self.remember_window = bool(_rw_var.get())
            if not self.remember_window:
                self.window_geometry = ''
                self.window_maximized = False
            self._save_config_now()
        ttk.Checkbutton(tab_iface,
                        text="Remember window size and position",
                        variable=_rw_var, command=_on_remember_window).grid(
            row=0, column=0, columnspan=2, sticky=tk.W, padx=10, pady=(12, 2))
        ttk.Label(tab_iface,
                  text="Saved when YSA closes and restored on the next start."
                       " A position that would land off-screen (for example a"
                       " monitor that is no longer connected) is re-centred"
                       " automatically.",
                  font=('Arial', 8), foreground='gray', justify=tk.LEFT,
                  wraplength=560).grid(
            row=1, column=0, columnspan=3, sticky=tk.W, padx=14)
        ttk.Button(tab_iface, text="Reset window size and position",
                   command=self._reset_window_geometry).grid(
            row=2, column=0, sticky=tk.W, padx=10, pady=(10, 0))

        ttk.Label(tab_iface,
                  text="History recording is toggled on the History tab.",
                  font=('Arial', 8), foreground='gray').grid(
            row=3, column=0, columnspan=3, sticky=tk.W, padx=14, pady=(16, 0))


        # ── Register tabs in display order ────────────────────────────────
        notebook.add(_tab_dl_outer, text="Downloads")
        notebook.add(tab_audio,  text="Audio")
        notebook.add(tab_iface,  text="Interface")
        notebook.add(tab_cache,  text="Cache")
        notebook.add(tab_exe,    text="Executables")
        notebook.add(tab_bgutil, text="bgutil (PO Token)")

        # ── Save / Cancel buttons ──────────────────────────────────────────
        # Packed BEFORE the notebook so it stays anchored at the bottom
        # regardless of how tall the content is or how small the window gets.
        btn_frame = _settings_btn_frame

        def save_settings():
            # ── Executables: only accept a changed path if it differs from current ──
            ytdlp_path = self.ytdlp_var.get()
            if ytdlp_path and ytdlp_path not in ("Not found", self.ytdlp_path or ""):
                # Path changed - accept it immediately; user can press Test to verify
                self.ytdlp_path = ytdlp_path
            ffmpeg_path = self.ffmpeg_var.get()
            if ffmpeg_path and ffmpeg_path not in ("Not found", self.ffmpeg_path or ""):
                self.ffmpeg_path = ffmpeg_path

            # ── Downloads ────────────────────────────────────────────────────
            new_dm = dm_var.get()
            if new_dm != self.dark_mode_var.get():
                self.dark_mode_var.set(new_dm)
                if new_dm:
                    self._apply_dark_mode()
                else:
                    self._apply_light_mode()
            _selected_display = lang_var_settings.get()
            new_lang = _LANG_DISPLAY_TO_CODE.get(_selected_display, _selected_display.strip())
            if new_lang:
                self.preferred_language = new_lang

            # ── Cache ─────────────────────────────────────────────────────────
            try:
                self.max_cache_mb = max(0, int(max_cache_var.get()))
            except ValueError:
                self.max_cache_mb = 0
            self.persistent_cache_var.set(pc_var.get())
            self.clear_cache_on_exit = cce_var.get()
            self.preserve_logs_on_clear = preserve_logs_var.get()
            self.preserve_ytdlp_on_clear = preserve_ytdlp_var.get()
            self.preserve_history_on_clear = preserve_hist_var.get()
            self.auto_update_tools = auto_upd_var.get()
            _new_ch = ytdlp_channel_var.get()
            if _new_ch != getattr(self, 'ytdlp_channel', 'nightly'):
                self.ytdlp_channel = _new_ch
                self.append_terminal_output(
                    'yt-dlp channel set to ' + _new_ch
                    + " - press 'Update yt-dlp' in Settings > Executables"
                    ' to switch the binary over.\n', 'info')

            self.player_client = client_var.get()
            self.prewarm_enabled = prewarm_var.get()
            self.parallel_hardsub = parallel_hardsub_var.get()
            self.hardsub_encoder = hardsub_enc_var.get()
            if self.hardsub_encoder == 'auto':
                # Re-probe on the next burn so switching back to auto after
                # a mid-session demote can rediscover the hardware.
                self._hardsub_encoder = None
            try:
                self.precache_concurrent_count = max(1, min(5, int(precache_count_var.get())))
            except ValueError:
                self.precache_concurrent_count = 1
            # Resize the slot pool immediately so the new count takes effect
            # without needing to restart the app.
            self._precache_n_slots = -1  # force _precache_init to rebuild
            self._precache_init()
            try:
                self.batch_concurrent_fetches = max(1, min(8, int(batch_fetch_var.get())))
            except ValueError:
                self.batch_concurrent_fetches = 3
            self.advance_queue_on_streams_done = advance_queue_var.get()
            self.extended_client_cascade = extended_cascade_var.get()
            self.cookies_file = cookies_file_var.get().strip()
            self.cookies_browser = cookies_browser_var.get()
            self.bgutil_server_url = bgutil_url_var.get().strip() or 'http://127.0.0.1:4416'
            self.bgutil_server_path = bgutil_path_var.get().strip()
            self.bgutil_autostart = bgutil_autostart_var.get()
            self.bgutil_keep_running = bgutil_keep_running_var.get()

            # ── Filename / Metadata / Subtitles / Audio bitrate ───────────────
            _sync_fn_format_var()
            self.filename_format = fn_format_var.get()
            self.filename_include_date = date_in_filename_var.get()
            self.meta_embed_title   = meta_title_var.get()
            self.meta_embed_artist  = meta_artist_var.get()
            self.meta_embed_date    = meta_date_var.get()
            self.meta_embed_comment = meta_comment_var.get()
            self.meta_embed_synopsis= meta_synopsis_var.get()

            try:
                self.preferred_audio_bitrate = max(0, int(audio_bitrate_var.get()))
            except ValueError:
                self.preferred_audio_bitrate = 0
            try:
                self.preferred_video_bitrate = max(0, int(video_bitrate_var.get()))
            except ValueError:
                self.preferred_video_bitrate = 0
            self.include_hls_streams = include_hls_var.get()
            # Refresh recommended combinations so sizes update immediately
            if self.current_formats:
                self._populate_recommended_combinations(suppress_auto_download=True)

            # Save and close instantly - no blocking subprocess, no popup
            self._save_config()
            dialog.destroy()
            self.status_var.set("Settings saved")

        ttk.Button(btn_frame, text="Save", command=save_settings).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Cancel", command=dialog.destroy).pack(side=tk.LEFT, padx=5)
        # Pressing Enter anywhere in the settings dialog triggers Save,
        # matching the behaviour users expect from a standard dialog.
        dialog.bind('<Return>', lambda e: save_settings())

    def _show_player_client_help(self):
        """Explain the Player Client options and name a recommendation.

        Kept as plain concatenation (no f-strings) and routed through
        the house _notify_info helper so it matches every other notice
        and inherits its main-thread guard and messagebox fallback.
        """
        _nl = "\n"
        msg = (
            "Which YouTube client yt-dlp pretends to be. This changes how"
            " much work each download costs." + _nl + _nl
            + "RECOMMENDED: default" + _nl
            + "  Lets yt-dlp choose. Most compatible. If you are passing"
            + " cookies, yt-dlp picks tv_downgraded, which downloads the"
            + " player JS and solves a challenge - roughly 3 seconds on"
            + " every yt-dlp call." + _nl + _nl
            + "FASTER, IF IT WORKS FOR YOU: android_vr" + _nl
            + "  Needs no PO token and skips the JS challenge entirely."
            + " Worth trying if you download in batches. Known caveat:"
            + " it can intermittently return only format 18 (360p"
            + " pre-muxed). If your downloads suddenly drop to 360p,"
            + " switch back to default." + _nl + _nl
            + "  visionos behaves similarly and is newer." + _nl
            + "  android_vr,default falls back automatically if"
            + " android_vr returns nothing usable - a safer middle"
            + " ground than android_vr alone." + _nl + _nl
            + "REQUIRE A BGUTIL SERVER: android, ios" + _nl
            + "  These need a GVS PO token. With no bgutil server"
            + " running, formats will be missing or downloads will"
            + " fail. Start it in Settings > bgutil before using these."
            + _nl + _nl
            + "OTHERS" + _nl
            + "  tv / tv_downgraded - no PO token, but pay the JS"
            + " challenge." + _nl
            + "  web_embedded - sometimes works around age-restricted"
            + " videos." + _nl + _nl
            + "This setting applies to downloads only. Analysis uses its"
            + " own client cascade and is unaffected."
        )
        self._notify_info("Player Client", msg)

    def get_player_client_extractor_args(self):
        """Return the --extractor-args list for the configured player client.
        Always appends android_vr as a no-PO-token fallback client and
        excludes tv_simply (slow, and now requires a GVS PO token).
        Used by all download workers; metadata/info paths use get_video_info()."""
        client = getattr(self, 'player_client', 'default') or 'default'
        # 2026-06 refresh (validated against yt-dlp 2026.06.09): tv_embedded
        # was REMOVED from yt-dlp, so appending it now just produces a
        # "Skipping unsupported client" warning on every download.
        # android_vr is the current no-PO-token fallback client per the
        # PO Token Guide, so append that instead. tv_simply now requires a
        # GVS PO token, so the exclusion below remains correct.
        if 'android_vr' not in client:
            client_str = client + ',android_vr'
        else:
            client_str = client
        return ['--extractor-args', 'youtube:player_client=' + client_str + ',-tv_simply']

    def _get_prewarm_info(self, entry):
        """Extract (url, [format_ids]) from a queue entry for pre-warm probing.
        Returns (None, []) if the entry cannot be parsed."""
        worker = entry.get('worker')
        args = entry.get('args', ())
        try:
            if worker == self._download_and_merge_worker_with_terminal:
                # args: (video_fid, audio_fid, output_path, quality,
                #        use_cache, cached_video, resume_temp, url, video_id, video_info)
                return args[7], [str(args[0]), str(args[1])]
            elif worker == self._download_direct_worker_with_terminal:
                # args: (format_id, filepath, quality, url, video_info)
                return args[3], [str(args[0])]
            elif worker == self._download_audio_only_worker:
                # args: (output_path, quality, url, video_info, audio_format_id, video_id)
                fid = str(args[4]) if len(args) > 4 and args[4] else None
                return args[2], ([fid] if fid else [])
        except Exception:
            pass
        return None, []

    def _prewarm_format(self, url, format_ids):
        """Send lightweight --get-url probes to warm up YouTube's CDN for the given
        format IDs before the download starts.  Always uses the default client since
        we only need URL resolution, not a download session.  Runs in a daemon thread
        so it never blocks the download queue.  Failures are silently ignored."""
        if not url or not format_ids or not getattr(self, 'prewarm_enabled', True):
            return
        for fid in format_ids:
            if not fid:
                continue
            try:
                probe_args = [
                    '--get-url', '--no-warnings',
                    '-f', fid,
                ]
                probe_args.extend(self.get_player_client_extractor_args())
                probe_args.extend(self.get_ytdlp_dns_args())
                if self.yt_dlp_cache_dir:
                    probe_args.extend(['--cache-dir', self.yt_dlp_cache_dir])
                probe_args.append(url)
                subprocess.run(
                    self._ytdlp_head() + probe_args,
                    capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                    creationflags=CREATE_NO_WINDOW)
            except Exception:
                pass

    # ── Pre-cache slot management ─────────────────────────────────────────
    # _precache_available_slots: set of integer slot numbers (0..n_slots-1)
    #   that are currently free to accept a new item.
    # _precache_active_ids: set of video IDs currently being downloaded.
    # Both are protected by _precache_lock.
    # A slot is "free" iff its number is in _precache_available_slots.
    # When a slot starts it removes its number; when done it adds it back
    # and immediately calls _precache_next_stream to fill the gap.

    def _precache_init(self):
        """Initialise or resize the slot pool to match precache_concurrent_count.
        Safe to call multiple times - dynamically resizes when the setting changes."""
        # _precache_lock is created in __init__ (two threads reaching a
        # lazy hasattr-check together each made their own lock)
        pass
        if not hasattr(self, '_precache_active_ids'):
            self._precache_active_ids = set()
        if not hasattr(self, '_precache_completed_ids'):
            self._precache_completed_ids = set()  # video_ids that have been fully attempted

        n = max(1, getattr(self, 'precache_concurrent_count', 1))

        if not hasattr(self, '_precache_available_slots'):
            # First call - all slots free
            self._precache_available_slots = set(range(n))
            self._precache_n_slots = n
            return

        if getattr(self, '_precache_n_slots', n) == n:
            # No change
            return

        # n_slots changed - rebuild available set preserving in-use slots.
        # in_use = slots that were assigned and not yet returned.
        # We don't store in-use slot numbers explicitly, but we know:
        #   in_use = old_all_slots - available  (slots claimed but not released)
        with self._precache_lock:
            old_n = self._precache_n_slots
            old_all = set(range(old_n))
            in_use  = old_all - self._precache_available_slots
            new_all = set(range(n))
            # Keep in-use slots that still exist in the new range;
            # any in-use slot >= n just disappears when it calls release.
            still_in_use = in_use & new_all
            self._precache_available_slots = new_all - still_in_use
            self._precache_n_slots = n

    def _precache_one_entry(self, entry, slot_index):
        """Download and cache video, audio, thumbnail, and subtitle streams
        for one queue entry.  When finished, releases the slot and calls
        _precache_next_stream so the slot is immediately reused."""
        worker_name = entry.get('worker_name', '')
        args = entry.get('args', ())
        if worker_name != 'merge' or len(args) < 10:
            self._precache_release_slot(None, slot_index)
            return False

        url        = args[7] if len(args) > 7 else None
        video_fid  = str(args[0])
        audio_fid  = str(args[1])
        video_id   = str(args[8]) if len(args) > 8 and args[8] else None
        video_info = args[9] if len(args) > 9 and args[9] else {}
        sub_snap   = args[10] if len(args) > 10 else None

        if not url or not video_id:
            self._precache_release_slot(video_id, slot_index)
            return False

        vid_cached   = self.get_cached_video_path(video_id, video_fid)
        aud_cached   = self.get_cached_audio_path(video_id, audio_fid)
        thumb_cached = (os.path.exists(os.path.join(self.thumbnail_cache_dir, video_id + '.jpg'))
                        if self.thumbnail_cache_dir else True)

        sub_lang    = ((sub_snap[2] if sub_snap and len(sub_snap) > 2 else None)
                       or getattr(self, 'subtitle_lang', 'en') or 'en')
        # Always precache subtitles regardless of current subtitle setting.
        # If the user toggles subtitles on later, the cached file is ready.
        sub_needed  = True
        sub_cached  = (self.get_cached_subtitle_path(video_id, sub_lang, False) is not None or
                       self.get_cached_subtitle_path(video_id, sub_lang, True) is not None)

        all_cached = vid_cached and aud_cached and thumb_cached and sub_cached
        if all_cached:
            self._precache_release_slot(video_id, slot_index)
            return False

        label = entry.get('label', url)
        self.append_terminal_output(
            'Pre-cache [slot ' + str(slot_index + 1) + ']: ' + label + '\n', 'cache')

        temp_dir = self._make_temp_dir('ysa_precache_')
        did_cache = False
        try:
            vid_result = [vid_cached]
            aud_result = [aud_cached]

            def _dl_video():
                if vid_result[0]:
                    return
                try:
                    vid_tmp = os.path.join(temp_dir, 'video_' + video_fid + '.mp4')
                    vargs = ['--no-warnings', '--newline', '--progress',
                             '-c', '--retries', '3', '--fragment-retries', '3',
                             '-o', vid_tmp, '-f', video_fid]
                    vargs.extend(self.get_player_client_extractor_args())
                    vargs.extend(self.get_ytdlp_dns_args())
                    if self.yt_dlp_cache_dir:
                        vargs.extend(['--cache-dir', self.yt_dlp_cache_dir])
                    vargs.append(url)
                    proc = subprocess.Popen(
                        self._ytdlp_head() + vargs,
                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                        text=True, encoding='utf-8', errors='replace', creationflags=CREATE_NO_WINDOW)
                    for line in iter(proc.stdout.readline, ''):
                        line = line.strip()
                        if not line:
                            continue
                        # Parse yt-dlp progress lines and store for the wait loop
                        if '%' in line and 'download' in line.lower():
                            _pct = _RE_PROGRESS_PCT.search(line)
                            _spd = _RE_PROGRESS_SPD.search(line)
                            _eta = _RE_PROGRESS_ETA.search(line)
                            parts = []
                            if _pct:
                                parts.append(_pct.group(1) + '%')
                            if _spd:
                                parts.append(_spd.group(1))
                            if _eta:
                                parts.append('ETA ' + _eta.group(1))
                            if parts:
                                self._precache_progress[video_id] = 'Video: ' + '  '.join(parts)
                    proc.wait(timeout=7200)
                    # Clear progress entry
                    self._precache_progress.pop(video_id, None)
                    if proc.returncode == 0:
                        for f in os.listdir(temp_dir):
                            if f.startswith('video_' + video_fid):
                                c = self.cache_video_stream(
                                    video_id, video_fid, os.path.join(temp_dir, f))
                                if c:
                                    vid_result[0] = c
                                break
                except Exception:
                    self._precache_progress.pop(video_id, None)

            def _dl_audio():
                if aud_result[0]:
                    return
                try:
                    aud_tmp = os.path.join(temp_dir, 'audio_' + audio_fid + '.m4a')
                    aargs = ['--no-warnings', '--newline', '--progress',
                             '-c', '--retries', '3', '--fragment-retries', '3',
                             '-o', aud_tmp, '-f', audio_fid]
                    aargs.extend(self.get_player_client_extractor_args())
                    aargs.extend(self.get_ytdlp_dns_args())
                    if self.yt_dlp_cache_dir:
                        aargs.extend(['--cache-dir', self.yt_dlp_cache_dir])
                    aargs.append(url)
                    proc = subprocess.Popen(
                        self._ytdlp_head() + aargs,
                        stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                        text=True, encoding='utf-8', errors='replace', creationflags=CREATE_NO_WINDOW)
                    _audio_key = video_id + '_audio'
                    for line in iter(proc.stdout.readline, ''):
                        line = line.strip()
                        if not line:
                            continue
                        if '%' in line and 'download' in line.lower():
                            _pct = _RE_PROGRESS_PCT.search(line)
                            _spd = _RE_PROGRESS_SPD.search(line)
                            _eta = _RE_PROGRESS_ETA.search(line)
                            parts = []
                            if _pct:
                                parts.append(_pct.group(1) + '%')
                            if _spd:
                                parts.append(_spd.group(1))
                            if _eta:
                                parts.append('ETA ' + _eta.group(1))
                            if parts:
                                self._precache_progress[_audio_key] = 'Audio: ' + '  '.join(parts)
                    proc.wait(timeout=7200)
                    self._precache_progress.pop(_audio_key, None)
                    if proc.returncode == 0:
                        for f in os.listdir(temp_dir):
                            if f.startswith('audio_' + audio_fid):
                                c = self.cache_audio_stream(
                                    video_id, audio_fid, os.path.join(temp_dir, f))
                                if c:
                                    aud_result[0] = c
                                break
                except Exception:
                    self._precache_progress.pop(video_id + '_audio', None)

            def _dl_thumbnail():
                if thumb_cached:
                    return
                try:
                    thumb_url = (video_info or {}).get('thumbnail')
                    if thumb_url:
                        self.cache_thumbnail(video_id, thumb_url, video_info)
                except Exception:
                    pass

            def _dl_subtitle():
                if sub_cached:
                    return
                try:
                    _known_manual = set((video_info.get('subtitles') or {}).keys())
                    _known_auto   = set((video_info.get('automatic_captions') or {}).keys())
                    _in_manual = sub_lang in _known_manual
                    _in_auto   = (sub_lang in _known_auto or
                                  any(k.startswith(sub_lang + '-') for k in _known_auto))
                    if not _in_manual and not _in_auto:
                        return
                    _sub_out = os.path.join(temp_dir, 'presub.%(ext)s')
                    if _in_manual:
                        sargs = ['--no-warnings', '--write-sub',
                                 '--sub-lang', sub_lang, '--skip-download',
                                 '--sub-format', 'srt/vtt/best', '-o', _sub_out]
                        sargs.extend(self.get_player_client_extractor_args())
                        sargs.extend(self.get_ytdlp_dns_args())
                        sargs.append(url)
                        subprocess.run(self._ytdlp_head() + sargs, capture_output=True,
                                       text=True, encoding='utf-8', errors='replace', timeout=60, creationflags=CREATE_NO_WINDOW)
                        for f in os.listdir(temp_dir):
                            if f.startswith('presub.') and f.endswith(('.srt', '.vtt', '.ass')):
                                self.cache_subtitle(video_id, sub_lang, False,
                                                    os.path.join(temp_dir, f))
                                return
                    if _in_auto:
                        aargs = ['--no-warnings', '--write-auto-subs',
                                 '--sub-lang', sub_lang, '--skip-download',
                                 '--sub-format', 'srt/vtt/best', '-o', _sub_out]
                        aargs.extend(self.get_player_client_extractor_args())
                        aargs.extend(self.get_ytdlp_dns_args())
                        aargs.append(url)
                        for f in list(os.listdir(temp_dir)):
                            if f.startswith('presub.'):
                                try: os.remove(os.path.join(temp_dir, f))
                                except Exception: pass
                        subprocess.run(self._ytdlp_head() + aargs, capture_output=True,
                                       text=True, encoding='utf-8', errors='replace', timeout=60, creationflags=CREATE_NO_WINDOW)
                        for f in os.listdir(temp_dir):
                            if f.startswith('presub.') and f.endswith(('.srt', '.vtt', '.ass')):
                                self.cache_subtitle(video_id, sub_lang, True,
                                                    os.path.join(temp_dir, f))
                except Exception:
                    pass

            vt = threading.Thread(target=_dl_video, daemon=True)
            at = threading.Thread(target=_dl_audio, daemon=True)
            tt = threading.Thread(target=_dl_thumbnail, daemon=True)
            st = threading.Thread(target=_dl_subtitle, daemon=True)
            vt.start(); at.start(); tt.start(); st.start()
            vt.join(); at.join(); tt.join(); st.join()

            # Only report "done" if something NEW was actually cached this run
            did_cache = bool((vid_result[0] and not vid_cached) or
                             (aud_result[0] and not aud_cached))
            if did_cache:
                self.append_terminal_output(
                    'Pre-cache done [slot ' + str(slot_index + 1) + ']: ' + label + '\n', 'cache')
                self.root.after(0, self._update_cache_size_label)
        except Exception:
            pass
        finally:
            shutil.rmtree(temp_dir, ignore_errors=True)

        # Mark this entry as fully attempted so the dispatcher never
        # re-dispatches it.  Prevents infinite loops when a video has no
        # subtitles (subtitle cache stays empty, but that's not retryable).
        # Key includes format IDs so the same video at different quality
        # still gets its own precache attempt.
        with self._precache_lock:
            self._precache_completed_ids.add((video_id, video_fid, audio_fid))

        self._precache_release_slot(video_id, slot_index)
        return did_cache

    def _precache_release_slot(self, video_id, slot_index):
        """Return the slot number and video ID to the pool, then immediately
        call _precache_next_stream so the freed slot picks up the next item.
        If the slot number is out of range (settings were downsized while this
        slot was running) it is simply discarded rather than re-added."""
        self._precache_init()
        with self._precache_lock:
            if video_id:
                self._precache_active_ids.discard(video_id)
            n = max(1, getattr(self, 'precache_concurrent_count', 1))
            if slot_index < n:
                self._precache_available_slots.add(slot_index)
            # else: slot was from a larger pool that has since been shrunk; drop it
        # Re-enter dispatcher - fills the now-free slot if anything is waiting
        self._precache_next_stream()

    def _precache_find_next(self, just_finished=None):
        """Kept for compatibility - not used by current dispatcher."""
        pass

    def _precache_next_stream(self):
        """Dispatcher: fill all available pre-cache slots with uncached queue items.

        Slot numbering persists across calls so the terminal shows stable
        [slot 1], [slot 2], [slot 3] labels reflecting real concurrency.
        Called at download start, on every enqueue, and after each slot finishes."""
        self._precache_init()

        with self._queue_lock:
            queue_snapshot = list(self._download_queue)
        if not queue_snapshot:
            return

        # Build candidate list: uncached merge entries not already active
        to_assign = []
        with self._precache_lock:
            free_slot_numbers = sorted(self._precache_available_slots)
            if not free_slot_numbers:
                return
            for entry in queue_snapshot:
                if len(to_assign) >= len(free_slot_numbers):
                    break
                if entry.get('worker_name') != 'merge':
                    continue
                args = entry.get('args', ())
                if len(args) < 10:
                    continue
                vid_id = str(args[8]) if len(args) > 8 and args[8] else None
                if not vid_id or vid_id in self._precache_active_ids:
                    continue
                # Skip items that have already been fully attempted - prevents
                # infinite loops when a video has no subtitles available.
                _entry_key = (vid_id, str(args[0]), str(args[1]))
                if _entry_key in self._precache_completed_ids:
                    continue
                # Check all four cacheable assets - not just video+audio.
                # If any of subtitle, thumbnail, video, or audio is uncached,
                # the item needs precaching.
                _v_ok = self.get_cached_video_path(vid_id, str(args[0]))
                _a_ok = self.get_cached_audio_path(vid_id, str(args[1]))
                _sub_lang_chk = getattr(self, 'subtitle_lang', 'en') or 'en'
                _s_ok = (self.get_cached_subtitle_path(vid_id, _sub_lang_chk, False) is not None or
                         self.get_cached_subtitle_path(vid_id, _sub_lang_chk, True) is not None)
                _t_ok = (os.path.exists(os.path.join(self.thumbnail_cache_dir, vid_id + '.jpg'))
                         if self.thumbnail_cache_dir else True)
                if not (_v_ok and _a_ok and _s_ok and _t_ok):
                    to_assign.append((free_slot_numbers[len(to_assign)], entry, vid_id))
            # Claim slots and IDs atomically
            for slot_num, entry, vid_id in to_assign:
                self._precache_available_slots.discard(slot_num)
                self._precache_active_ids.add(vid_id)

        for slot_num, entry, vid_id in to_assign:
            threading.Thread(
                target=self._precache_one_entry,
                args=(entry, slot_num),
                daemon=True).start()

    def _precache_slot_worker(self, entry, slot_idx):
        """Legacy wrapper - new code calls _precache_one_entry directly."""
        self._precache_one_entry(entry, slot_idx)


    def test_ytdlp_path(self, path):
        """Test if yt-dlp path is working"""
        if not path or path == "Not found":
            return False
        
        try:
            result = subprocess.run([path, '--version'],
                                  capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                                  creationflags=CREATE_NO_WINDOW)
            return result.returncode == 0
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return False
    
    def test_ffmpeg_path(self, path):
        """Test if FFmpeg path is working"""
        if not path or path == "Not found":
            return False
        
        try:
            result = subprocess.run([path, '-version'],
                                  capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                                  creationflags=CREATE_NO_WINDOW)
            return result.returncode == 0
        except (FileNotFoundError, subprocess.TimeoutExpired):
            return False
    
    def download_and_merge(self, _enqueue_only=False):
        """Download and merge selected streams.
        If a download is running or paused, adds the selection to the queue instead.
        _enqueue_only=True forces queuing even when idle (used internally)."""
        if not self.ffmpeg_path:
            result = messagebox.askyesno("FFmpeg Not Found", 
                                       "FFmpeg is required for merging video and audio.\n\n" +
                                       "Would you like to open the settings to configure FFmpeg?")
            if result:
                self.show_settings()
            return
        
        # Get current tab and selection
        current_tab = self.notebook.select()
        tab_text = self.notebook.tab(current_tab, "text")

        if "Recommended" not in tab_text:
            self._notify_info("Info",
                "Please select a stream from the 'Recommended' tab for download and merge.\n\n"
                "The Recommended tab shows the best video+audio combinations with caching support.")
            return

        # If a download is active or paused, queue this selection instead of blocking.
        # _download_active covers the race window between thread start and _download_process being set.
        busy = (self._download_active or
                (self._download_process is not None and self._download_process.poll() is None))
        if busy or self._download_paused or _enqueue_only:
            self._enqueue_current_selection()
            return

        # Idle - start immediately - set _download_active NOW, before any
        # call tree runs, so a second click always sees busy=True.
        self._download_active = True
        self._record_attempt(self.url_var.get().strip(),
                             self.current_video_info)
        self._download_stopped = False
        self._reset_download_buttons()
        self.download_recommended_selection()

    def download_recommended_selection(self):
        """Download and merge from recommended tab selection with caching"""
        selection = self.recommended_tree.selection()
        if not selection:
            self._notify_warning("Warning", "Please select a stream combination to download")
            # Guard: _download_active may have been set by the caller before
            # invoking this method.  Clear it so the queue is never permanently
            # locked by an early return.
            self._download_active = False
            self._start_next_queued()
            return
        
        item = self.recommended_tree.item(selection[0])
        values = item['values']
        
        if not values:
            self._download_active = False
            self._start_next_queued()
            return
        
        quality = values[0]
        video_info = values[1]
        audio_info = values[2]
        
        # Check if it's a direct download (combined stream)
        if "Direct:" in video_info:
            self.download_direct_stream(video_info, quality)
        else:
            self.download_and_merge_combination(video_info, audio_info, quality)
    
    def download_direct_stream(self, video_info, quality):
        """Download a direct combined stream"""
        try:
            # Extract format ID from video_info
            format_id = video_info.split('(')[1].split(')')[0] if '(' in video_info else ''
            
            if not format_id:
                self._notify_error("Error", "Could not extract format ID")
                # C4 fix: caller set _download_active=True before dispatch;
                # clear it or the queue is permanently locked (mirrors the
                # guard in download_recommended_selection).
                self._download_active = False
                self._start_next_queued()
                return
            
            # Snapshot URL and video_info first - before building any filename -
            # so the output path and worker args are always consistent.
            url_snap      = getattr(self, 'current_video_url', None) or self.url_var.get().strip()
            video_id_snap = self.current_video_info.get('id', 'unknown')
            vi_snap       = dict(self.current_video_info)

            # Get video info for filename - use snapshot
            video_title = vi_snap.get('title', 'video')
            safe_title = self.sanitize_filename(video_title)
            
            # Find the format
            target_format = None
            for fmt in self.current_formats:
                if str(fmt.get('format_id', '')) == format_id:
                    target_format = fmt
                    break
            
            if not target_format:
                self._notify_error("Error", "Format " + format_id + " not found")
                # C4 fix: clear the active flag so the queue can proceed.
                self._download_active = False
                self._start_next_queued()
                return
            
            ext = target_format.get('ext', 'mp4')
            # Extract language from format for combined streams (e.g. format 18)
            _dir_lang = self.detect_audio_language(target_format)
            _dir_lang_tag = (' ' + _dir_lang.upper()) if _dir_lang and _dir_lang != 'unknown' else ''
            # Include subtitle mode suffix in filename when subtitles are enabled,
            # mirroring the merge path so the file is named correctly from the start.
            _dir_sub_src  = getattr(self, 'subtitle_source', 'off')
            _dir_sub_mode = getattr(self, 'subtitle_mode', 'S')
            _dir_sub_lang = getattr(self, 'subtitle_lang', 'en') or 'en'
            # Build suffix: external = no mode tag; auto = A+mode; manual = mode only
            if _dir_sub_src == 'off' or _dir_sub_src == 'external':
                _dir_sub_suffix = ''
            elif _dir_sub_src == 'auto':
                _dir_sub_suffix = ' A' + _dir_sub_mode
            else:
                _dir_sub_suffix = ' ' + _dir_sub_mode
            _bracket_tag = quality.rstrip('p') + 'D' + _dir_lang_tag + _dir_sub_suffix
            filename = self._assemble_filename(vi_snap, _bracket_tag, '.' + ext)
            filepath = self._unique_output_path(os.path.join(self.download_path, filename), vi_snap.get('id'))
            _dir_sub_snap = (_dir_sub_src, _dir_sub_mode, _dir_sub_lang)

            # Start download in thread
            if self.audio_only_mode.get():
                mp3_filename = self._assemble_filename(vi_snap, quality, '.mp3')
                mp3_filepath = self._unique_output_path(os.path.join(self.download_path, mp3_filename), vi_snap.get('id'))
                # format_id here is a combined/direct stream - no separate audio cache key
                thread = threading.Thread(
                    target=self._download_audio_only_worker,
                    args=(mp3_filepath, quality, url_snap, vi_snap))
                self._resume_target = self._download_audio_only_worker
                self._resume_args = (mp3_filepath, quality, url_snap, vi_snap)
            else:
                thread = threading.Thread(
                    target=self._download_direct_worker_with_terminal,
                    args=(format_id, filepath, quality, url_snap, vi_snap,
                          _dir_sub_snap, video_id_snap))
                self._resume_target = self._download_direct_worker_with_terminal
                self._resume_args = (format_id, filepath, quality, url_snap, vi_snap,
                                     _dir_sub_snap, video_id_snap)
            thread.daemon = True
            thread.start()

        except Exception as e:
            # If thread never started, clear the flag so the queue is not permanently locked
            self._download_active = False
            self._notify_error("Error", "Error starting download: " + str(e))

    def download_and_merge_combination(self, video_info, audio_info, quality):
        """Download video and audio, then merge them with caching support"""
        try:
            # Extract format IDs
            video_format_id = video_info.split('(')[1].split(')')[0] if '(' in video_info else ''
            
            # Handle different audio info formats
            if "ID:" in audio_info:
                # New format: "m4a ID:140 128kbps m4a (en)"
                audio_format_id = audio_info.split('ID:')[1].split(' ')[0] if 'ID:' in audio_info else ''
            else:
                # Old format fallback
                audio_format_id = audio_info.split('(')[1].split(')')[0] if '(' in audio_info else ''
            
            if not video_format_id or not audio_format_id:
                self._notify_error("Error", "Could not extract format IDs\nVideo: " + str(video_format_id) + "\nAudio: " + str(audio_format_id))
                # C4 fix: clear the active flag so the queue can proceed.
                self._download_active = False
                self._start_next_queued()
                return
            
            # Snapshot URL, video_id, and video_info now - before any async work -
            # so the filename and worker args are always consistent with each other
            # even if the batch worker has already moved on to the next video.
            url_snap      = getattr(self, 'current_video_url', None) or self.url_var.get().strip()
            video_id_snap = self.current_video_info.get('id', 'unknown')
            vi_snap        = dict(self.current_video_info)

            # Get video info for filename - use vi_snap, not live self.current_video_info
            video_title = vi_snap.get('title', 'video')
            safe_title = self.sanitize_filename(video_title)
            video_id = video_id_snap
            
            # Include language in filename for clarity
            audio_lang = "unknown"
            if "(" in audio_info and ")" in audio_info:
                # Try to extract language from audio info
                lang_part = audio_info.split('(')[-1].split(')')[0]
                if len(lang_part) <= 3:  # Likely a language code
                    audio_lang = lang_part
            
            lang_tag = audio_lang.upper() if audio_lang and audio_lang != "unknown" else ""
            quality_tag = (quality + " " + lang_tag).strip()
            # Include subtitle tag in filename now so we never overwrite a
            # no-subtitle file with an in-progress subtitle download.
            # The tag is known at enqueue time: mode S/SD/HS (or AS/ASD/AHS for
            # auto-subs, but we don't know auto vs manual until download time so
            # we use the mode letter only here; auto prefix A is added on rename
            # if needed, which is now only a safe rename on a unique path).
            _enq_sub_src  = getattr(self, 'subtitle_source', 'off')
            _enq_sub_mode = getattr(self, 'subtitle_mode', 'S')
            _enq_sub_lang = (getattr(self, 'subtitle_lang', 'en') or 'en').upper()
            if _enq_sub_src != 'off':
                _sub_suffix = " " + _enq_sub_mode
            else:
                _sub_suffix = ""
            # Always output MP4. For S mode the MP4 muxer forces default=1
            # on the subtitle track regardless of -disposition flags - this is
            # corrected post-merge by _patch_mp4_subtitle_flag() which
            # directly patches the tkhd box in the file.
            output_filename = self._assemble_filename(vi_snap, quality_tag + _sub_suffix, '.mp4')
            output_path = self._unique_output_path(os.path.join(self.download_path, output_filename), vi_snap.get('id'))

            # Check if video is already cached
            cached_video_path = self.get_cached_video_path(video_id, video_format_id)
            use_cache = cached_video_path is not None
            if self.audio_only_mode.get():
                mp3_filename = self._assemble_filename(vi_snap, quality_tag, '.mp3')
                mp3_filepath = self._unique_output_path(os.path.join(self.download_path, mp3_filename), vi_snap.get('id'))
                thread = threading.Thread(
                    target=self._download_audio_only_worker,
                    args=(mp3_filepath, quality, url_snap, vi_snap,
                          audio_format_id, video_id_snap))
                self._resume_target = self._download_audio_only_worker
                self._resume_args = (mp3_filepath, quality, url_snap, vi_snap,
                                     audio_format_id, video_id_snap)
            else:
                _sub_snap = (_enq_sub_src, _enq_sub_mode, _enq_sub_lang.lower())
                thread = threading.Thread(
                    target=self._download_and_merge_worker_with_terminal,
                    args=(video_format_id, audio_format_id, output_path, quality, use_cache, cached_video_path, None, url_snap, video_id_snap, vi_snap, _sub_snap))
                self._resume_target = self._download_and_merge_worker_with_terminal
                self._resume_args = (video_format_id, audio_format_id, output_path, quality, use_cache, cached_video_path, None, url_snap, video_id_snap, vi_snap, _sub_snap)
            thread.daemon = True
            thread.start()

        except Exception as e:
            # If thread never started, clear the flag so the queue is not permanently locked
            self._download_active = False
            self._notify_error("Error", "Error starting download: " + str(e))
    
    def _download_direct_worker_with_terminal(self, format_id, output_path, quality, url=None, video_info=None, sub_settings=None, video_id=None):
        """Worker thread for direct download with terminal output"""
        max_retries = 5
        # Snapshot URL and video_info at entry so resume and metadata always use
        # the original video, even if the user analyzes a different video while paused.
        if url is None:
            url = self.url_var.get().strip()
        if video_info is None:
            video_info = dict(self.current_video_info)

        # Keep resume context current so pause->resume replays exactly this call
        self._resume_target = self._download_direct_worker_with_terminal
        self._resume_args = (format_id, output_path, quality, url, video_info, sub_settings, video_id)

        # ── Snapshot clip settings ────────────────────────────────────────
        _clip_on = (getattr(self, '_clip_enabled_var', None)
                    and bool(getattr(self, '_m_clip_on', False)))
        _clip_start_hms = (self._parse_time_to_hhmmss(
            getattr(self, '_m_clip_start', '')) if _clip_on else None)
        _clip_end_hms = (self._parse_time_to_hhmmss(
            getattr(self, '_m_clip_end', '')) if _clip_on else None)
        def _d_hms2sec(t):
            if not t:
                return 0.0
            parts = t.split(':')
            try:
                return int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
            except Exception:
                return 0.0
        _clip_start_sec = _d_hms2sec(_clip_start_hms)
        _clip_end_sec   = _d_hms2sec(_clip_end_hms)
        _clip_active    = (_clip_on and _clip_start_hms and _clip_end_hms
                           and _clip_end_sec > _clip_start_sec)

        # ── Premuxed cache check ──────────────────────────────────────────────
        # The cache stores the base file only (metadata+thumbnail, no subtitles).
        # On a hit we copy the base to output_path and then re-apply subtitles
        # from the subtitle cache (fast, local) - same path as a fresh download.
        _vid_id_for_cache = video_id or (video_info.get('id') if video_info else None) or 'unknown'
        _premuxed_vkey = self._premuxed_cache_key(format_id)
        _cached_base = self.get_cached_premuxed_path(_vid_id_for_cache, _premuxed_vkey)
        # premuxed reuse reads a cached file too - protect it from eviction
        self._mark_cache_inuse(_cached_base)
        _from_cache = False

        if _cached_base:
            try:
                self.download_start_time = time.time()
                self._session_download_counter += 1
                self.append_terminal_output(
                    '\nStarting download: ' + quality + ' quality\n', 'info')
                self.root.after(0, lambda: self.progress_bar.start())
                shutil.copy2(_cached_base, output_path)
                self.append_terminal_output('Using cached base stream.\n', 'cache')
                # ── Clip trim on cached file ──────────────────────────────
                if _clip_active and self.ffmpeg_path:
                    _clip_tmp = output_path + '.clip_tmp.mp4'
                    _clip_dur = _clip_end_sec - _clip_start_sec
                    self.append_terminal_output(
                        'Clip: ' + _clip_start_hms + ' to ' + _clip_end_hms +
                        ' (' + str(round(_clip_dur, 1)) + 's)\n', 'info')
                    _cr = subprocess.run(
                        [self.ffmpeg_path, '-y', '-i', output_path,
                         '-ss', _clip_start_hms, '-to', _clip_end_hms,
                         '-c', 'copy', '-movflags', '+faststart',
                         '-loglevel', 'error', _clip_tmp],
                        capture_output=True, timeout=300,
                        creationflags=CREATE_NO_WINDOW)
                    if _cr.returncode == 0 and os.path.exists(_clip_tmp):
                        os.replace(_clip_tmp, output_path)
                    else:
                        self.append_terminal_output(
                            'Clip trim failed - keeping full file.\n', 'warning')
                        if os.path.exists(_clip_tmp):
                            os.remove(_clip_tmp)
                _from_cache = True
            except Exception as _ce:
                self.append_terminal_output(
                    'Premuxed cache copy failed (' + str(_ce) + ') - downloading fresh.\n', 'warning')
                _from_cache = False

        if not _from_cache:
            _last_exc_str = ''
            for attempt in range(max_retries):
                try:
                    if attempt == 0:
                        self.download_start_time = time.time()
                        self._session_download_counter += 1

                    if attempt > 0:
                        is_format_err = 'Requested format is not available' in _last_exc_str
                        is_state_err  = is_format_err or ('HTTP Error 416' in _last_exc_str)
                        wait_secs = 0 if is_state_err else min(5 * attempt, 30)
                        retry_note = "retrying immediately" if is_state_err else ("resuming in " + str(wait_secs) + "s")
                        self.append_terminal_output(
                            "\nRetry attempt " + str(attempt + 1) + " of " + str(max_retries) +
                            " for " + quality + " (" + retry_note + ")...\n", 'warning')
                        if wait_secs:
                            time.sleep(wait_secs)
                        if 'HTTP Error 416' in _last_exc_str:
                            # Premuxed downloads had the fast classifier but no
                            # salvage, so a byte-complete file that crashed at
                            # exit looped all five attempts. Expected size is
                            # passed as 0 deliberately: this path has no second
                            # leg to protect, so deleting and refetching always
                            # converges, which matters more than saving bytes.
                            try:
                                # the direct worker writes straight to the
                                # final path, so that IS the partial
                                self._resolve_416_partial(output_path, 0, 'Stream')
                            except Exception:
                                pass
                    else:
                        self.append_terminal_output("\nStarting download: " + quality + " quality\n", 'info')
                        self.root.after(0, lambda: self.progress_bar.start())

                    args = [
                        '--no-warnings',
                        '--newline',
                        '--progress',
                        '-c',
                        '--retries', '10',
                        '--fragment-retries', '10',
                        '--retry-sleep', 'linear=1::2',
                        '--no-part',
                        '--add-headers', 'Connection:keep-alive',
                        '--buffer-size', '16K',
                        '--http-chunk-size', '10M',
                        '-o', output_path,
                        '-f', format_id
                    ]
                    args.extend(self.get_player_client_extractor_args())
                    args.extend(self.get_ytdlp_dns_args())
                    if self.yt_dlp_cache_dir:
                        args.extend(['--cache-dir', self.yt_dlp_cache_dir])
                    args.append(url)

                    self.run_ytdlp_command_with_terminal(args, capture_output=False, timeout=7200)

                    if not os.path.exists(output_path):
                        raise Exception("Download completed but file not found: " + output_path)

                    # ── Clip (section trim) if active ─────────────────────────
                    if _clip_active and self.ffmpeg_path:
                        _clip_tmp = output_path + '.clip_tmp.mp4'
                        _clip_cmd = [
                            self.ffmpeg_path, '-y',
                            '-i', output_path,
                            '-ss', _clip_start_hms,
                            '-to', _clip_end_hms,
                            '-c', 'copy',
                            '-movflags', '+faststart',
                            '-loglevel', 'error',
                            _clip_tmp,
                        ]
                        _clip_dur = _clip_end_sec - _clip_start_sec
                        self.append_terminal_output(
                            'Clip: ' + _clip_start_hms + ' to ' + _clip_end_hms +
                            ' (' + str(round(_clip_dur, 1)) + 's)\n', 'info')
                        _cr = subprocess.run(
                            _clip_cmd, capture_output=True, timeout=300,
                            creationflags=CREATE_NO_WINDOW)
                        if _cr.returncode == 0 and os.path.exists(_clip_tmp):
                            os.replace(_clip_tmp, output_path)
                        else:
                            self.append_terminal_output(
                                'Clip trim failed - keeping full file.\n', 'warning')
                            if os.path.exists(_clip_tmp):
                                os.remove(_clip_tmp)

                    # ── Embed metadata + thumbnail ────────────────────────────
                    _embed_result = self._embed_metadata(output_path, video_info)
                    if _embed_result:
                        output_path = _embed_result

                    # ── Cache the base file (no subtitles yet) ────────────────
                    # Subtitles are applied below and are NOT baked into this copy.
                    # Any future request for this format_id gets this clean base
                    # and then has subtitles re-applied from the subtitle cache.
                    self.cache_premuxed_stream(_vid_id_for_cache, _premuxed_vkey, output_path)

                    break  # success - exit retry loop

                except (_DownloadStoppedError, _DownloadPausedError):
                    raise
                except Exception as e:
                    _last_exc_str = str(e)
                    self.append_terminal_output("\nAttempt " + str(attempt + 1) + " failed: " + str(e) + "\n", 'error')
                    if os.path.exists(output_path):
                        self.append_terminal_output("Partial stream files kept in temp dir for resume.\n", 'info')

                    # On the first failure, if the format expired re-fetch fresh IDs and restart.
                    if 'Requested format is not available' in _last_exc_str and attempt == 0:
                        self.append_terminal_output(
                            "\nStream URL expired - re-fetching fresh format ID for " + quality + "...\n", 'warning')
                        try:
                            fresh_info = self.get_video_info(url)
                            fresh_vid_fid, _ = self._resolve_fresh_format_ids(
                                fresh_info, format_id, None, quality)
                            if fresh_vid_fid:
                                self.append_terminal_output(
                                    "Fresh format ID: " + fresh_vid_fid + " - restarting download.\n", 'info')
                                self._download_direct_worker_with_terminal(
                                    fresh_vid_fid, output_path, quality, url, fresh_info,
                                    sub_settings=sub_settings, video_id=video_id)
                                return
                            else:
                                self.append_terminal_output(
                                    "Could not find matching stream in fresh info - continuing retries.\n", 'warning')
                        except Exception as refresh_err:
                            self.append_terminal_output(
                                "Re-fetch failed: " + str(refresh_err) + "\n", 'error')

                    if attempt == max_retries - 1:
                        raise

        # ── Embed subtitle (format-18 post-process) ───────────────────────────
        # Runs for both fresh downloads and cache hits.
        # Format-18 is a pre-muxed stream so subtitles must be embedded via a
        # dedicated FFmpeg pass after the base file is in place.
        if sub_settings and self.ffmpeg_path:
                    _d_sub_src, _d_sub_mode, _d_sub_lang = sub_settings
                    if _d_sub_src != 'off':
                        _d_vid_id = video_id or (video_info.get('id') if video_info else None) or 'unknown'
                        # External mode still needs to fetch subtitles (to save alongside
                        # the output file).  Treat it identically to 'auto' for fetch
                        # purposes - the only difference is what happens after the file
                        # is downloaded (save vs embed).
                        _d_is_auto = (_d_sub_src in ('auto', 'external'))
                        _d_sub_file = None
                        _d_temp_dir = self._make_temp_dir('ysa_sub_')
                        try:
                            # Cache check: manual sub
                            _cached_manual = self.get_cached_subtitle_path(_d_vid_id, _d_sub_lang, False)
                            if _cached_manual:
                                _d_sub_file = os.path.join(_d_temp_dir, 'subtitle_dl.srt')
                                shutil.copy2(_cached_manual, _d_sub_file)
                                self.append_terminal_output(
                                    'Subtitle (manual) from cache: ' + os.path.basename(_cached_manual) + '\n', 'info')
                            # Cache check: auto sub
                            if not _d_sub_file and _d_is_auto:
                                _cached_auto = self.get_cached_subtitle_path(_d_vid_id, _d_sub_lang, True)
                                if _cached_auto:
                                    _d_sub_file = os.path.join(_d_temp_dir, 'subtitle_dl.srt')
                                    shutil.copy2(_cached_auto, _d_sub_file)
                                    self.append_terminal_output(
                                        'Subtitle (auto-generated) from cache: ' + os.path.basename(_cached_auto) + '\n', 'info')
                            # Network download if no cache hit
                            if not _d_sub_file:
                                _d_sub_out = os.path.join(_d_temp_dir, 'subtitle_dl.%(ext)s')
                                _known_manual = set((video_info.get('subtitles') or {}).keys()) if video_info else set()
                                _known_auto   = set((video_info.get('automatic_captions') or {}).keys()) if video_info else set()
                                _lang_in_manual = _d_sub_lang in _known_manual
                                _lang_in_auto   = (_d_sub_lang in _known_auto or
                                                   any(k.startswith(_d_sub_lang + '-') for k in _known_auto))
                                if not _lang_in_manual and not _lang_in_auto:
                                    self.append_terminal_output(
                                        'No ' + _d_sub_lang + ' subtitles for this video - skipping.\n', 'warning')
                                else:
                                    # Try manual first
                                    _d_manual_args = [
                                        '--no-warnings', '--write-sub',
                                        '--sub-lang', _d_sub_lang, '--skip-download',
                                        '--sub-format', 'srt/vtt/best',
                                        '-o', _d_sub_out,
                                    ]
                                    _d_manual_args.extend(self.get_player_client_extractor_args())
                                    _d_manual_args.extend(self.get_ytdlp_dns_args())
                                    _d_manual_args.append(url)
                                    if _lang_in_manual:
                                        self.append_terminal_output(
                                            'Fetching subtitle (' + _d_sub_lang + ', manual)...\n', 'info')
                                    try:
                                        subprocess.run(
                                            self._ytdlp_head() + _d_manual_args,
                                            capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=60,
                                            creationflags=CREATE_NO_WINDOW)
                                        for _f in os.listdir(_d_temp_dir):
                                            if _f.startswith('subtitle_dl.') and _f.endswith(('.srt', '.vtt', '.ass')):
                                                _d_sub_file = os.path.join(_d_temp_dir, _f)
                                                self.append_terminal_output(
                                                    'Subtitle (manual) downloaded: ' + _f + '\n', 'info')
                                                self.cache_subtitle(_d_vid_id, _d_sub_lang, False, _d_sub_file)
                                                break
                                    except Exception as _se:
                                        self.append_terminal_output(
                                            'Manual subtitle fetch failed: ' + str(_se) + '\n', 'warning')
                                    # Auto fallback
                                    if not _d_sub_file and _d_is_auto:
                                        _d_auto_args = [
                                            '--no-warnings', '--write-auto-subs',
                                            '--sub-lang', _d_sub_lang, '--skip-download',
                                            '--sub-format', 'srt/vtt/best',
                                            '-o', _d_sub_out,
                                        ]
                                        _d_auto_args.extend(self.get_player_client_extractor_args())
                                        _d_auto_args.extend(self.get_ytdlp_dns_args())
                                        _d_auto_args.append(url)
                                        self.append_terminal_output(
                                            'Fetching subtitle (' + _d_sub_lang + ', auto, up to 60s)...\n', 'info')
                                        try:
                                            subprocess.run(
                                                self._ytdlp_head() + _d_auto_args,
                                                capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=60,
                                                creationflags=CREATE_NO_WINDOW)
                                            for _f in os.listdir(_d_temp_dir):
                                                if _f.startswith('subtitle_dl.') and _f.endswith(('.srt', '.vtt', '.ass')):
                                                    _d_sub_file = os.path.join(_d_temp_dir, _f)
                                                    self.append_terminal_output(
                                                        'Subtitle (auto-generated) downloaded: ' + _f + '\n', 'info')
                                                    self.cache_subtitle(_d_vid_id, _d_sub_lang, True, _d_sub_file)
                                                    break
                                        except Exception as _se:
                                            self.append_terminal_output(
                                                'Auto subtitle fetch failed: ' + str(_se) + '\n', 'warning')
                            # FFmpeg embed pass - branch on hard vs soft sub
                            if _d_sub_file and os.path.exists(_d_sub_file):
                                # Write FFmpeg output to temp dir - never create an
                                # intermediate file in the downloads folder.
                                _d_sub_out = os.path.join(_d_temp_dir, 'sub_embedded.mp4')
                                # External mode: save subtitle file alongside output, no embed
                                if _d_sub_src == 'external':
                                    try:
                                        _ext_dest = os.path.splitext(output_path)[0] + '.' + _d_sub_lang + '.srt'
                                        shutil.copy2(_d_sub_file, _ext_dest)
                                        self.append_terminal_output(
                                            'Subtitle saved externally: ' + os.path.basename(_ext_dest) + '\n', 'success')
                                    except Exception as _ext_err:
                                        self.append_terminal_output(
                                            'External subtitle save failed: ' + str(_ext_err) + '\n', 'warning')
                                    _d_sub_file = None  # prevent FFmpeg embed below
                                _d_is_hs = (_d_sub_mode == 'HS') if _d_sub_file else False
                                if _d_is_hs:
                                    # Hard sub: burn subtitles into video via libx264 re-encode.
                                    # FFmpeg subtitles filter requires a relative path on Windows
                                    # (absolute paths with drive letters / spaces / brackets fail).
                                    # Copy to a plain name in the temp dir and run with cwd set.
                                    _hs_sub = os.path.join(_d_temp_dir, 'hs_sub.srt')
                                    try:
                                        shutil.copy2(_d_sub_file, _hs_sub)
                                        # Fix overlapping timecodes - identical logic to merge path
                                        try:
                                            import re as _srt_re
                                            def _srt_ms(t):
                                                h, m, s, ms = int(t[0]), int(t[1]), int(t[2]), int(t[3])
                                                return ((h * 3600 + m * 60 + s) * 1000) + ms
                                            def _ms_srt(ms):
                                                ms = max(0, ms)
                                                h = ms // 3600000; ms %= 3600000
                                                m = ms // 60000;   ms %= 60000
                                                s = ms // 1000;    ms %= 1000
                                                return '{:02d}:{:02d}:{:02d},{:03d}'.format(h, m, s, ms)
                                            _tc_pat = _srt_re.compile(
                                                r'(\d+):(\d+):(\d+),(\d+)\s*-->\s*(\d+):(\d+):(\d+),(\d+)')
                                            with open(_hs_sub, 'r', encoding='utf-8', errors='replace') as _sf:
                                                _raw = _sf.read()
                                            _entries = [e.strip() for e in _srt_re.split(r'\n\s*\n', _raw) if e.strip()]
                                            _timecodes = []
                                            for _e in _entries:
                                                _m2 = _tc_pat.search(_e)
                                                if _m2:
                                                    _timecodes.append((_srt_ms(_m2.groups()[:4]),
                                                                       _srt_ms(_m2.groups()[4:])))
                                                else:
                                                    _timecodes.append(None)
                                            _out_entries = []
                                            for _i, _e in enumerate(_entries):
                                                if _timecodes[_i] is None:
                                                    _out_entries.append(_e)
                                                    continue
                                                _start, _end = _timecodes[_i]
                                                _next_start = None
                                                for _j in range(_i + 1, len(_timecodes)):
                                                    if _timecodes[_j] is not None:
                                                        _next_start = _timecodes[_j][0]
                                                        break
                                                if _next_start is not None and _end > _next_start:
                                                    _end = _next_start - 1
                                                _fixed = _tc_pat.sub(
                                                    _ms_srt(_start) + ' --> ' + _ms_srt(_end), _e, count=1)
                                                _out_entries.append(_fixed)
                                            with open(_hs_sub, 'w', encoding='utf-8') as _sf:
                                                _sf.write('\n\n'.join(_out_entries) + '\n')
                                        except Exception:
                                            pass
                                    except Exception:
                                        _hs_sub = _d_sub_file
                                    # Determine video dimensions for subtitles filter
                                    _vid_w, _vid_h = 0, 0
                                    try:
                                        for _fmt in (video_info or {}).get('formats', []):
                                            if str(_fmt.get('format_id', '')) == str(format_id):
                                                _vid_w = _fmt.get('width') or 0
                                                _vid_h = _fmt.get('height') or 0
                                                break
                                    except Exception:
                                        pass
                                    if not (_vid_w and _vid_h):
                                        try:
                                            # quality may be '340D', '360p', '1080p' etc.
                                            # Strip trailing letters/non-digits to get the number
                                            import re as _re_dim
                                            _h_match = _re_dim.search(r'(\d+)', quality)
                                            _vid_h = int(_h_match.group(1)) if _h_match else 360
                                            _vid_w = int(round(_vid_h * 16 / 9))
                                        except Exception:
                                            _vid_w, _vid_h = 640, 360
                                    _orig_size = str(_vid_w) + 'x' + str(_vid_h)
                                    _vf = 'subtitles=hs_sub.srt:original_size=' + _orig_size
                                    _d_hs_pre = ([self.ffmpeg_path, '-y']
                                                 + self._hardsub_input_args()
                                                 + ['-i', output_path])
                                    _d_hs_post = [
                                        '-vf', _vf,
                                        '-c:a', 'copy',
                                        '-movflags', '+faststart',
                                        '-loglevel', 'error',
                                        _d_sub_out
                                    ]
                                    _d_sub_cmd = (_d_hs_pre
                                                  + self._hardsub_codec_args()
                                                  + _d_hs_post)
                                    _d_cwd = _d_temp_dir
                                elif _d_sub_file:
                                    # Soft sub: stream copy, embed as mov_text track
                                    _d_sub_cmd = [
                                        self.ffmpeg_path, '-y',
                                        '-i', output_path,
                                        '-i', _d_sub_file,
                                        '-c', 'copy',
                                        '-c:s', 'mov_text',
                                        '-movflags', '+faststart',
                                        '-loglevel', 'error',
                                        _d_sub_out
                                    ]
                                    _d_cwd = None
                                if _d_is_hs or _d_sub_file:
                                    try:
                                        _d_res = subprocess.run(
                                            _d_sub_cmd,
                                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                            text=True, encoding='utf-8', errors='replace',
                                            timeout=None if _d_is_hs else 120,
                                            cwd=_d_cwd,
                                            creationflags=CREATE_NO_WINDOW)
                                        if (_d_is_hs and _d_res.returncode != 0
                                                and _d_sub_cmd[5] != 'libx264'):
                                            # Real input defeated the hardware encoder even
                                            # though the synthetic probe passed: pin the
                                            # session to software and redo THIS burn once.
                                            self._hardsub_demote(
                                                'direct burn', _d_res.returncode)
                                            _d_sub_cmd = ([self.ffmpeg_path, '-y']
                                                          + self._hardsub_input_args()
                                                          + ['-i', output_path]
                                                          + self._hardsub_codec_args()
                                                          + _d_hs_post)
                                            _d_res = subprocess.run(
                                                _d_sub_cmd,
                                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                                text=True, encoding='utf-8', errors='replace',
                                                timeout=None, cwd=_d_cwd,
                                                creationflags=CREATE_NO_WINDOW)
                                        if _d_res.returncode == 0 and os.path.exists(_d_sub_out):
                                            # Retry loop for WinError 5 (Access Denied) -
                                            # can occur when the premuxed cache write briefly
                                            # holds a file handle on the same output path.
                                            _replaced = False
                                            for _d_attempt in range(5):
                                                try:
                                                    os.replace(_d_sub_out, output_path)
                                                    _replaced = True
                                                    break
                                                except OSError as _d_oserr:
                                                    if _d_oserr.winerror == 5 and _d_attempt < 4:
                                                        time.sleep(0.3)
                                                    else:
                                                        raise
                                            if _replaced:
                                                if not _d_is_hs:
                                                    self._patch_mp4_subtitle_flag(
                                                        output_path, enabled=(_d_sub_mode in ('SD', 'ASD')))
                                                self.append_terminal_output(
                                                    'Subtitle embedded (' + _d_sub_mode + ' mode).\n', 'success')
                                                self._direct_sub_embedded_flag = True
                                        else:
                                            self.append_terminal_output(
                                                'Subtitle embed failed - file saved without subtitles.\n', 'warning')
                                            if os.path.exists(_d_sub_out):
                                                os.remove(_d_sub_out)
                                    except Exception as _d_err:
                                        self.append_terminal_output(
                                            'Subtitle embed error: ' + str(_d_err) + '\n', 'warning')
                            else:
                                self.append_terminal_output(
                                    'Subtitle unavailable - file saved without subtitles.\n', 'warning')
                        finally:
                            shutil.rmtree(_d_temp_dir, ignore_errors=True)

        # ── Rename if subtitle tag in filename but nothing was embedded ────────
        # The output_path was named at enqueue time with the subtitle mode suffix
        # (e.g. [340D EN S]).  If no subtitle was actually embedded (not found,
        # embed failed, or external-only mode), strip the suffix from the filename
        # so it matches what was actually produced.
        if sub_settings and self.ffmpeg_path:
            _fn_sub_src = sub_settings[0] if sub_settings else 'off'
            _fn_sub_mode = sub_settings[1] if len(sub_settings) > 1 else 'S'
            _fn_lang = sub_settings[2] if len(sub_settings) > 2 else 'en'
            _sub_tag_in_name = _fn_sub_src not in ('off', 'external') and _fn_sub_mode
            if _sub_tag_in_name:
                # Check whether any subtitle was actually embedded by comparing
                # file size - if the subtitle embed ran, the output was replaced.
                # Simpler: check if the name contains the mode suffix and rewrite.
                _ext  = os.path.splitext(output_path)[1]
                # Build the clean name without the sub tag
                _lang_upper = (_fn_lang or 'en').upper()
                _clean_path = self._unique_output_path(
                    os.path.join(self.download_path,
                                 self._assemble_filename(video_info or {}, quality.rstrip('p') + 'D ' + _lang_upper, _ext)),
                    (video_info or {}).get('id'))
                # Only rename if the current name contains a subtitle tag that doesn't belong
                # We detect this by checking if _d_sub_actually_embedded is False
                # Use the flag we track below - wrap into a closure-safe variable
                pass  # flag tracking is done inline above; rename happens below

        # Determine if subtitle was actually embedded (set by the sub block above)
        _sub_was_embedded = getattr(self, '_direct_sub_embedded_flag', False)
        if hasattr(self, '_direct_sub_embedded_flag'):
            del self._direct_sub_embedded_flag

        if not _sub_was_embedded and sub_settings:
            _chk_src  = sub_settings[0] if sub_settings else 'off'
            _chk_mode = sub_settings[1] if len(sub_settings) > 1 else 'S'
            _chk_lang = (sub_settings[2] if len(sub_settings) > 2 else 'en') or 'en'
            # If sub source was on (not off/external) and nothing was embedded,
            # rebuild the filename without the subtitle suffix.
            if _chk_src not in ('off', 'external') and _chk_mode:
                _lang_tag_clean = ' ' + _chk_lang.upper()
                _clean_bracket  = quality.rstrip('p') + 'D' + _lang_tag_clean
                _clean_path = os.path.join(
                    self.download_path,
                    self._assemble_filename(video_info or {}, _clean_bracket,
                                            os.path.splitext(output_path)[1]))
                _clean_path = self._unique_output_path(_clean_path, (video_info or {}).get('id'))
                if _clean_path != output_path and os.path.exists(output_path):
                    try:
                        os.rename(output_path, _clean_path)
                        output_path = _clean_path
                        self.append_terminal_output(
                            'Renamed (no subtitle embedded): ' +
                            os.path.basename(output_path) + '\n', 'info')
                    except Exception:
                        pass  # keep original name if rename fails
        # ────────────────────────────────────────────────────────────────────

        # ── Set filesystem timestamps ─────────────────────────────────────────
        self._set_file_timestamps(output_path, video_info)

        download_time = time.time() - self.download_start_time
        file_size = self.format_file_size(os.path.getsize(output_path))

        self.append_terminal_output('\nDownload completed successfully!\n', 'success')
        self.append_terminal_output('File: ' + os.path.basename(output_path) + '\n', 'success')
        self.append_terminal_output('Size: ' + file_size + '\n', 'success')
        self.append_terminal_output('Time: ' + self._format_download_time(download_time) + '\n\n', 'success')

        self.root.after(0, lambda: self.progress_bar.stop())
        self._pending_history_meta = {'url': url, 'video_info': video_info, 'quality': quality}
        self.root.after(0, lambda: self._download_complete(output_path, 'Download', download_time))

    def _expected_stream_size(self, video_info, format_id):
        """Expected byte size of a format, from the analysis we already hold.

        Prefers the exact filesize. Falls back to filesize_approx with a 2%
        margin so formats that only report an estimate (some HLS-derived
        entries) can still have a complete partial recognised instead of
        being thrown away and re-downloaded. Returns 0 when neither is
        known, which callers treat as 'cannot verify'."""
        try:
            for f in (video_info or {}).get('formats', []):
                if str(f.get('format_id', '')) == str(format_id):
                    _exact = int(f.get('filesize') or 0)
                    if _exact:
                        return _exact
                    _approx = int(f.get('filesize_approx') or 0)
                    if _approx:
                        return int(_approx * 0.98)
                    return 0
        except Exception:
            pass
        return 0

    def _audio_source_abr(self, video_info, format_id):
        """Average bitrate (kbps) of a format from the analysis, or 0."""
        try:
            for f in (video_info or {}).get('formats', []):
                if str(f.get('format_id', '')) == str(format_id):
                    return int(float(f.get('abr') or 0))
        except Exception:
            pass
        return 0

    def _audio_output_bitrate(self, source_abr):
        """Encoder bitrate for a transcode, per the user's policy.

        The output encoders were hardcoded (AAC at 128k, MP3 at LAME V0), so
        asking for the smallest source stream and then transcoding produced
        files ~2.5x LARGER than the stream they came from, with no quality
        gain - nothing can restore detail already lost in a 48 kbps Opus
        encode. Returns 0 to mean 'encoder default' (the old behaviour,
        kept as the 'max' policy)."""
        policy = getattr(self, 'audio_bitrate_policy', 'match_source')
        pref = int(getattr(self, 'preferred_audio_bitrate', 0) or 0)
        src = int(source_abr or 0)
        if policy == 'max':
            return 0
        if policy == 'fixed':
            want = int(getattr(self, 'audio_fixed_bitrate', 128) or 128)
        elif policy == 'match_pref':
            want = pref or src or 128
        else:
            want = src or pref or 128
        if src:
            want = min(want, src)          # never upsample past the source
        return max(32, min(320, int(want)))

    def _cache_raw_audio_stream(self, video_id, format_id, src_path):
        """Copy a freshly downloaded RAW audio stream into the audio cache.

        The audio-only worker consumed the audio cache but never filled it,
        so repeat downloads of the same audio re-fetched from the network
        every time - field logs show one 11.8 MiB stream pulled eight times
        in a single session. Copies rather than moves so the caller's
        pipeline is untouched; cache_audio_stream then moves the copy into
        place, reusing its registration, metadata and size accounting.

        Must never be called for clipped or transcoded audio: a cache entry
        keyed on a format id has to be the complete, unmodified stream."""
        if not getattr(self, 'audio_cache_streams', True):
            return
        if not video_id or not format_id or not getattr(self, 'audio_cache_dir', None):
            return
        try:
            if self.get_cached_audio_path(video_id, format_id):
                return
            _ext = os.path.splitext(src_path)[1] or '.m4a'
            _stage = os.path.join(os.path.dirname(src_path), 'cachestage' + _ext)
            shutil.copy2(src_path, _stage)
            if self.cache_audio_stream(video_id, format_id, _stage):
                self.append_terminal_output(
                    'Audio stream cached for reuse.\n', 'cache')
            else:
                try:
                    os.remove(_stage)
                except Exception:
                    pass
        except Exception:
            pass

    def _cleanup_invocation_cookies(self, args):
        """Delete the throwaway cookie copy made for one yt-dlp invocation.

        Copies are created per invocation and were only swept at exit, so a
        long session left hundreds of ysa_ck_* folders behind. Deleting them
        on a timer would be unsafe (yt-dlp writes its cookie jar back at
        EXIT, so removing the file mid-run recreates the very crash the
        copies prevent), so removal is tied to the process actually being
        finished: the caller passes the args it just ran."""
        try:
            base = getattr(self, 'ysa_tmp_dir', None)
            if not base or not args:
                return
            for _i, _a in enumerate(args):
                if _a == '--cookies' and _i + 1 < len(args):
                    _d = os.path.dirname(str(args[_i + 1]))
                    if (os.path.basename(_d).startswith('ysa_ck_')
                            and os.path.dirname(_d) == base):
                        shutil.rmtree(_d, ignore_errors=True)
        except Exception:
            pass

    def _resolve_leg_file(self, path_template):
        """Turn a yt-dlp -o template (video_137.%(ext)s) into the actual file
        on disk, or return the path itself if it is already concrete."""
        try:
            if not path_template:
                return None
            if '%(' not in path_template:
                return path_template if os.path.isfile(path_template) else None
            import glob as _g
            hits = [h for h in _g.glob(path_template.replace('%(ext)s', '*'))
                    if os.path.isfile(h)]
            if not hits:
                return None
            hits.sort(key=lambda p: os.path.getsize(p), reverse=True)
            return hits[0]
        except Exception:
            return None

    def _resolve_416_partial(self, path_template, expected, label):
        """Decide the fate of a -c partial after an HTTP 416.

        Field logs showed the '416 partial' is usually a byte-COMPLETE file:
        the yt-dlp process died during exit bookkeeping (cookie-jar write
        collision) AFTER the last byte, so the retry's Range request started
        at EOF and googlevideo answered 416 forever. Salvage first: size >=
        the exact analysis filesize means the leg is done - keep it and the
        pre-spawn check will skip the download next attempt. Otherwise the
        offset really is wrong: delete so the retry starts clean."""
        try:
            actual = self._resolve_leg_file(path_template)
            if not actual:
                return
            size = os.path.getsize(actual)
            if expected and size >= expected:
                self.append_terminal_output(
                    label + ' partial verified complete ('
                    + self.format_file_size(size)
                    + ') - keeping it for the next attempt.\n', 'success')
                return
            os.remove(actual)
            self.append_terminal_output(
                label + ' partial removed after HTTP 416 (size unverifiable)'
                ' - will re-download fresh.\n', 'warning')
        except Exception:
            pass

    def _info_json_for_leg(self, video_info, temp_dir):
        """Path to a reusable info JSON for this download, or None.

        A merge costs THREE yt-dlp extractions - the analysis plus one per
        leg - each doing its own webpage fetch, player-API call and PO-token
        mint. Handing a leg the info we already have, via --load-info-json,
        skips its extraction entirely.

        Only safe while the stream URLs are still valid. Measured in the
        field: googlevideo URLs carry expire= and last SIX HOURS, with a
        spread of 0s across every format, so one check covers the whole
        dict. A 15-minute margin is kept anyway.

        Returns None - meaning 'use the URL, extract normally' - for any
        doubt at all: setting off, no formats, no expire=, too close to
        expiry, or an unwritable temp dir.
        """
        try:
            if not getattr(self, 'reuse_info_json', True):
                return None
            if getattr(self, '_info_json_disabled', False):
                return None
            if not video_info or not temp_dir:
                return None
            import re as _re
            _exp = []
            for _f in video_info.get('formats') or []:
                _m = _re.search(r'[?&]expire=(\d{9,})', _f.get('url') or '')
                if _m:
                    _exp.append(int(_m.group(1)))
            if not _exp:
                return None
            if (min(_exp) - time.time()) < 900:
                self.append_terminal_output(
                    'Stream URLs expire within 15 minutes - re-extracting'
                    ' rather than reusing the analysis.\n', 'info')
                return None
            _p = os.path.join(temp_dir, 'ysa_info.json')
            with open(_p, 'w', encoding='utf-8') as _fh:
                json.dump(video_info, _fh)
            return _p
        except Exception:
            return None

    def _log_stream_url_lifetime(self, info):
        """Report how long this analysis' stream URLs stay valid. DIAGNOSTIC.

        A merge download currently costs THREE yt-dlp extractions - the
        analysis, the video leg and the audio leg - each doing its own
        webpage fetch, player-API call and PO-token mint. Roughly 6-9
        requests where 2-3 would do, which is what produced 133 bot-check
        errors and 230s of enforced sleeps in a 109-video session.

        The fix is to hand the already-fetched info to both legs with
        --load-info-json, collapsing three extractions into one. The ONLY
        real risk is that googlevideo URLs expire: every one carries an
        'expire=<unix ts>' parameter. This logs the real window so the
        decision rests on measurement rather than an assumed six hours.

        Changes nothing. Reads the info dict already in memory, writes one
        line, and never raises.
        """
        try:
            import re as _re
            _now = time.time()
            _exp = []
            for _f in (info or {}).get('formats') or []:
                _u = _f.get('url') or ''
                _m = _re.search(r'[?&]expire=(\d{9,})', _u)
                if _m:
                    _exp.append(int(_m.group(1)))
            if not _exp:
                self.append_terminal_output(
                    'Stream URL lifetime: no expire= parameter found'
                    ' (reuse would need a different freshness test).\n', 'info')
                return
            _left = int(min(_exp) - _now)
            if _left <= 0:
                self.append_terminal_output(
                    'Stream URL lifetime: already expired at analysis time.\n',
                    'warning')
                return
            _h, _m2 = _left // 3600, (_left % 3600) // 60
            _spread = int(max(_exp) - min(_exp))
            self.append_terminal_output(
                'Stream URL lifetime: ' + str(_h) + 'h ' + str(_m2) + 'm'
                + ' (' + str(len(_exp)) + ' formats, spread '
                + str(_spread) + 's).\n', 'info')
        except Exception:
            pass

    def _log_audio_leg(self, fid, rc, out_b, err_b):
        """Replay the background audio leg's yt-dlp output into the LOG.

        The audio half of a merge already captured both streams and then
        threw stdout away, so half of every merge download was invisible:
        its format choice, its 'Sleeping N seconds' lines and its errors
        never reached the log this project debugs from.

        Log file ONLY, and marshalled to the main thread:
          - _write_session_log documents itself as single-threaded (its
            line-start flag and file handle are unguarded), so this goes
            through root.after(0, ...) like every other worker write.
          - it deliberately does NOT use append_terminal_output: that
            fans out to _output_listeners, and the scenario runner times
            pause_at_percent off that stream (tests 46 and 54). A second
            progress source there could move when a scenario pauses.
          - it runs AFTER communicate() returns, so neither the
            concurrency nor the ordering of the live video output moves.

        Repeating progress lines are dropped (a final 100% is kept), so
        this cannot drown the log the way the per-invocation cookie
        staleness warning once did. One after() call, not one per line.
        """
        try:
            if not getattr(self, '_session_log_fh', None):
                return
            _txt = ''
            for _raw in (out_b, err_b):
                if not _raw:
                    continue
                if isinstance(_raw, bytes):
                    _txt += _raw.decode('utf-8', errors='replace')
                else:
                    _txt += str(_raw)
            _keep = []
            for _l in _txt.replace('\r', '\n').split('\n'):
                _l = _l.rstrip()
                if not _l:
                    continue
                if '[download]' in _l and '%' in _l and '100%' not in _l:
                    continue
                _keep.append('[audio] ' + _l)
            _body = ('audio leg (ID ' + str(fid) + ') finished rc=' + str(rc)
                     + ', output replayed below:\n')
            if _keep:
                _body += '\n'.join(_keep) + '\n'
            self.root.after(0, lambda t=_body: self._write_session_log(t))
        except Exception:
            pass

    def _download_and_merge_worker_with_terminal(self, video_format_id, audio_format_id, output_path, quality, use_cache=False, cached_video_path=None, resume_temp_dir=None, url=None, video_id=None, video_info=None, sub_settings=None):
        """Worker thread for download and merge with terminal output.
        resume_temp_dir: if set, reuse an existing temp dir containing partial files."""
        max_retries = 5
        # Snapshot URL, video_id, and video_info at entry so resume and metadata
        # always use the original video, even if user analyzes a different video while paused.
        if url is None:
            url = self.url_var.get().strip()
        if video_id is None:
            video_id = self.current_video_info.get('id', 'unknown')
        if video_info is None:
            video_info = dict(self.current_video_info)

        # Unpack snapshotted subtitle settings (captured at enqueue time).
        # Falling back to live self values only if not provided (single direct downloads).
        if sub_settings is not None:
            _snap_sub_src, _snap_sub_mode, _snap_sub_lang = sub_settings
        else:
            _snap_sub_src  = getattr(self, 'subtitle_source', 'off')
            _snap_sub_mode = getattr(self, 'subtitle_mode', 'S')
            _snap_sub_lang = getattr(self, 'subtitle_lang', 'en') or 'en'

        # Defined before the retry loop so the 416-salvage block in the
        # retry preamble can reference them even when attempt 0 failed
        # before assignment (e.g. during the precache wait). The try/except
        # around the salvage stays as belt-and-braces.
        video_temp = None
        audio_temp = None

        # ── Snapshot clip settings from the UI (must happen on worker entry
        #    before the user can change them for a different video) ────────
        _clip_on = (getattr(self, '_clip_enabled_var', None)
                    and bool(getattr(self, '_m_clip_on', False)))
        _clip_start_hms = (self._parse_time_to_hhmmss(
            getattr(self, '_m_clip_start', '')) if _clip_on else None)
        _clip_end_hms = (self._parse_time_to_hhmmss(
            getattr(self, '_m_clip_end', '')) if _clip_on else None)
        # Convert to seconds for duration calculation
        def _hms2sec(t):
            if not t:
                return 0.0
            parts = t.split(':')
            try:
                return int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
            except Exception:
                return 0.0
        _clip_start_sec = _hms2sec(_clip_start_hms)
        _clip_end_sec   = _hms2sec(_clip_end_hms)
        _clip_active    = (_clip_on and _clip_start_hms and _clip_end_hms
                           and _clip_end_sec > _clip_start_sec)

        # Reuse existing temp dir on resume so -c can find the partial file.
        # Create a new one only on a fresh start.
        if resume_temp_dir and os.path.isdir(resume_temp_dir):
            temp_dir = resume_temp_dir
            self.append_terminal_output("Reusing temp dir from paused download: " + os.path.basename(temp_dir) + "\n", 'cache')
        else:
            temp_dir = self._make_temp_dir('ysa_download_')

        # Keep _resume_args updated with the live temp_dir so pause->resume
        # always passes the correct directory regardless of how many times it cycles.
        self._resume_target = self._download_and_merge_worker_with_terminal
        self._resume_args = (video_format_id, audio_format_id, output_path, quality, use_cache, cached_video_path, temp_dir, url, video_id, video_info)

        _last_exc_str = ''
        for attempt in range(max_retries):
            try:
                if attempt == 0:
                    self.download_start_time = time.time()
                    self._session_download_counter += 1

                if attempt > 0:
                    is_format_err = 'Requested format is not available' in _last_exc_str
                    is_state_err  = is_format_err or ('HTTP Error 416' in _last_exc_str)
                    wait_secs = 0 if is_state_err else min(5 * attempt, 30)
                    retry_note = "retrying immediately" if is_state_err else ("resuming in " + str(wait_secs) + "s")
                    self.append_terminal_output(
                        "\nRetry attempt " + str(attempt + 1) + " of " + str(max_retries) +
                        " for " + quality + " combination (" + retry_note + ")...\n", 'warning')
                    if wait_secs:
                        time.sleep(wait_secs)
                    if 'HTTP Error 416' in _last_exc_str:
                        # Keep byte-complete legs, delete unverifiable ones
                        try:
                            self._resolve_416_partial(
                                video_temp,
                                self._expected_stream_size(video_info, video_format_id),
                                'Video')
                            self._resolve_416_partial(
                                audio_temp,
                                self._expected_stream_size(video_info, audio_format_id),
                                'Audio')
                        except Exception:
                            pass
                else:
                    self.append_terminal_output("\nStarting combination download: " + quality + " quality\n", 'info')
                    self.root.after(0, lambda: self.progress_bar.start())

                self.append_terminal_output("Using temp directory: " + os.path.basename(temp_dir) + "\n", 'info')
                
                # ── Wait for in-flight precache ─────────────────────────────
                # If the precache system is currently downloading streams for
                # this video, wait for it to finish and show live progress
                # in the terminal so the user sees download speed/ETA.
                _precache_lock = getattr(self, '_precache_lock', None)
                _precache_ids  = getattr(self, '_precache_active_ids', None)
                if _precache_lock and _precache_ids:
                    _waited = False
                    _last_progress = ''
                    for _pw in range(1800):   # up to 3600 s in 2-s ticks (long videos)
                        with _precache_lock:
                            _still_active = video_id in _precache_ids
                        if not _still_active:
                            break
                        if not _waited:
                            self.append_terminal_output(
                                'Pre-caching in progress for this video - showing live progress:\n', 'cache')
                            _waited = True
                        if self._download_stopped:
                            raise _DownloadStoppedError('stopped')
                        # Read and display progress from the precache worker
                        _vid_prog = self._precache_progress.get(video_id, '')
                        _aud_prog = self._precache_progress.get(video_id + '_audio', '')
                        _combined = '  |  '.join(p for p in [_vid_prog, _aud_prog] if p)
                        if _combined and _combined != _last_progress:
                            _last_progress = _combined
                            self.append_terminal_output(
                                'Pre-cache: ' + _combined + '\n', 'progress')
                        time.sleep(2)
                    if _waited:
                        self.append_terminal_output('Pre-cache finished, checking for cached streams.\n', 'cache')

                # ── Video stream ────────────────────────────────────────────
                # Always do a live cache lookup regardless of the use_cache flag
                # that was snapshotted at enqueue time.  If another download of the
                # same stream completed while this item was waiting in the queue,
                # the cached file will be found here and the download skipped.
                _live_cached_video = self.get_cached_video_path(video_id, video_format_id)
                if _live_cached_video:
                    cached_video_path = _live_cached_video
                    use_cache = True
                video_cached = use_cache and cached_video_path and os.path.exists(cached_video_path)
                if video_cached:
                    self.append_terminal_output("Using cached video: " + os.path.basename(cached_video_path) + "\n", 'cache')
                    video_temp = cached_video_path
                else:
                    video_temp = os.path.join(temp_dir, f"video_{video_format_id}.%(ext)s")

                # ── Audio stream ────────────────────────────────────────────
                cached_audio_path = self.get_cached_audio_path(video_id, audio_format_id)
                audio_cached = cached_audio_path is not None
                if audio_cached:
                    self.append_terminal_output("Using cached audio stream (ID: " + audio_format_id + ")\n", 'cache')
                    audio_temp = cached_audio_path
                else:
                    audio_temp = os.path.join(temp_dir, "audio_" + audio_format_id + ".%(ext)s")

                # ── 416-salvage pre-check ──────────────────────────────────
                # If a previous attempt fully downloaded a leg (verified
                # against the exact filesize from the analysis) don't spawn
                # yt-dlp for it again: -c on a byte-complete file makes
                # googlevideo answer HTTP 416. Treat the leg as cached-in-
                # place; it feeds the merge directly this attempt.
                # NOTE: the download branches below are gated on
                # video_cached / audio_cached, so a salvaged leg needs its
                # own flag - setting cached_video_path alone left the video
                # leg re-spawning yt-dlp against a byte-complete file and
                # looping on 416 exactly as before the fix. The salvage
                # flags deliberately do NOT set *_cached, so the caching
                # step further down still stores the recovered stream.
                _v_salv = False
                _a_salv = False
                if not video_cached:
                    _vexp = self._expected_stream_size(video_info, video_format_id)
                    _vgot = self._resolve_leg_file(video_temp)
                    if _vgot and _vexp and os.path.getsize(_vgot) >= _vexp:
                        self.append_terminal_output(
                            'Video stream already complete from a previous'
                            ' attempt (size verified) - skipping download.\n',
                            'success')
                        video_temp = _vgot
                        _v_salv = True
                if not audio_cached:
                    _aexp = self._expected_stream_size(video_info, audio_format_id)
                    _agot = self._resolve_leg_file(audio_temp)
                    if _agot and _aexp and os.path.getsize(_agot) >= _aexp:
                        self.append_terminal_output(
                            'Audio stream already complete from a previous'
                            ' attempt (size verified) - skipping download.\n',
                            'success')
                        audio_temp = _agot
                        _a_salv = True
                _v_need = not video_cached and not _v_salv
                _a_need = not audio_cached and not _a_salv
                # Protect anything we are about to read from eviction.
                self._mark_cache_inuse(cached_video_path if video_cached else None,
                                       cached_audio_path if audio_cached else None)

                # ── Concurrent download when both streams need fetching ─────
                # Video runs with terminal output (sets self._download_process).
                # Audio runs silently in a daemon thread alongside it so both
                # transfers happen in parallel, cutting total time roughly in half.
                if _v_need and _a_need:
                    # Build audio args now so the thread captures them correctly
                    audio_args_bg = [
                        '--no-warnings', '--newline', '--progress',
                        '-c', '--retries', '10', '--fragment-retries', '10', '--retry-sleep', 'linear=1::2',
                        '--no-part',
                        '--add-headers', 'Connection:keep-alive',
                        '--buffer-size', '16K',
                        '--http-chunk-size', '10M',
                        '--concurrent-fragments', '4',
                        '-o', audio_temp, '-f', audio_format_id
                    ]
                    audio_args_bg.extend(self.get_player_client_extractor_args())
                    audio_args_bg.extend(self.get_ytdlp_dns_args())
                    if self.yt_dlp_cache_dir:
                        audio_args_bg.extend(['--cache-dir', self.yt_dlp_cache_dir])
                    # Reuse the analysis instead of re-extracting, when the
                    # stream URLs are still comfortably valid. Falls back to
                    # the URL for any doubt; a failure disables reuse for the
                    # rest of this download so the retry loop extracts afresh.
                    _aj = self._info_json_for_leg(video_info, temp_dir)
                    if _aj:
                        audio_args_bg.extend(['--load-info-json', _aj])
                    else:
                        audio_args_bg.append(url)

                    _audio_result = [None]
                    _audio_exc = [None]

                    def _download_audio_bg():
                        try:
                            cmd = self._ytdlp_head() + audio_args_bg
                            proc = subprocess.Popen(
                                cmd,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                creationflags=CREATE_NO_WINDOW,
                            )
                            self._audio_bg_process = proc
                            stdout_b, stderr_b = proc.communicate(timeout=7200)
                            self._audio_bg_process = None
                            # Half of every merge used to be invisible: this
                            # output was captured and then discarded.
                            self._log_audio_leg(audio_format_id, proc.returncode,
                                                stdout_b, stderr_b)
                            if proc.returncode != 0 and _aj:
                                # The reused info did not work. Extract normally
                                # from here on rather than repeating the failure.
                                self._info_json_disabled = True
                                self.root.after(0, lambda: self.append_terminal_output(
                                    'Reusing the analysis failed for the audio leg'
                                    ' - falling back to a fresh extraction.\n',
                                    'warning'))
                            # Simulate a CompletedProcess-like result so the
                            # existing returncode / stderr checks below still work.
                            result = subprocess.CompletedProcess(
                                args=cmd,
                                returncode=proc.returncode,
                                stdout='',
                                stderr=stderr_b.decode('utf-8', errors='replace') if stderr_b else '',
                            )
                            _audio_result[0] = result
                        except Exception as exc:
                            self._audio_bg_process = None
                            _audio_exc[0] = exc
                        finally:
                            # cookie copies are reclaimed only by the process-guarded reap
                            pass

                    self.append_terminal_output(
                        "Downloading video + audio streams concurrently...\n", 'info')
                    audio_thread = threading.Thread(target=_download_audio_bg, daemon=True)
                    audio_thread.start()

                    # Video runs with terminal output as usual
                    video_args = [
                        '--no-warnings', '--newline', '--progress',
                        '-c', '--retries', '10', '--fragment-retries', '10', '--retry-sleep', 'linear=1::2',
                        '--no-part',
                        '--add-headers', 'Connection:keep-alive',
                        '--buffer-size', '16K',
                        '--http-chunk-size', '10M',
                        '--concurrent-fragments', '4',
                        '-o', video_temp, '-f', video_format_id
                    ]
                    video_args.extend(self.get_player_client_extractor_args())
                    video_args.extend(self.get_ytdlp_dns_args())
                    if self.yt_dlp_cache_dir:
                        video_args.extend(['--cache-dir', self.yt_dlp_cache_dir])
                    video_args.append(url)
                    self.run_ytdlp_command_with_terminal(video_args, capture_output=False, timeout=7200)

                    # Wait for audio thread to finish
                    audio_thread.join(timeout=7210)
                    if _audio_exc[0]:
                        raise Exception("Audio download failed: " + str(_audio_exc[0]))
                    if _audio_result[0] is None:
                        raise Exception("Audio download timed out")
                    if _audio_result[0].returncode != 0:
                        err = (_audio_result[0].stderr or "").strip()
                        raise Exception("Audio download failed: " + (err or "yt-dlp returned non-zero"))

                elif _v_need:
                    # Only video needs downloading
                    self.append_terminal_output("Downloading video stream (ID: " + str(video_format_id) + ")...\n", 'info')
                    video_args = [
                        '--no-warnings', '--newline', '--progress',
                        '-c', '--retries', '10', '--fragment-retries', '10', '--retry-sleep', 'linear=1::2',
                        '--no-part',
                        '--add-headers', 'Connection:keep-alive',
                        '--buffer-size', '16K',
                        '--http-chunk-size', '10M',
                        '-o', video_temp, '-f', video_format_id
                    ]
                    video_args.extend(self.get_player_client_extractor_args())
                    video_args.extend(self.get_ytdlp_dns_args())
                    if self.yt_dlp_cache_dir:
                        video_args.extend(['--cache-dir', self.yt_dlp_cache_dir])
                    video_args.append(url)
                    self.run_ytdlp_command_with_terminal(video_args, capture_output=False, timeout=7200)

                elif _a_need:
                    # Only audio needs downloading
                    self.append_terminal_output("Downloading audio stream (ID: " + audio_format_id + ")...\n", 'info')
                    audio_args = [
                        '--no-warnings', '--newline', '--progress',
                        '-c', '--retries', '10', '--fragment-retries', '10', '--retry-sleep', 'linear=1::2',
                        '--no-part',
                        '--add-headers', 'Connection:keep-alive',
                        '--buffer-size', '16K',
                        '--http-chunk-size', '10M',
                        '--concurrent-fragments', '4',
                        '-o', audio_temp, '-f', audio_format_id
                    ]
                    audio_args.extend(self.get_player_client_extractor_args())
                    audio_args.extend(self.get_ytdlp_dns_args())
                    if self.yt_dlp_cache_dir:
                        audio_args.extend(['--cache-dir', self.yt_dlp_cache_dir])
                    audio_args.append(url)
                    self.run_ytdlp_command_with_terminal(audio_args, capture_output=False, timeout=7200)

                # ── Resolve final file paths ────────────────────────────────
                # (a salvaged leg is already resolved and size-verified)
                if not video_cached and not _v_salv:
                    video_files = [f for f in os.listdir(temp_dir) if f.startswith(f"video_{video_format_id}")]
                    if not video_files:
                        raise Exception("Video download failed - file not found")
                    video_temp = os.path.join(temp_dir, video_files[0])
                    if not os.path.exists(video_temp) or os.path.getsize(video_temp) == 0:
                        raise Exception("Video file is missing or empty")

                if not audio_cached and not _a_salv:
                    audio_files = [f for f in os.listdir(temp_dir) if f.startswith("audio_" + audio_format_id)]
                    if not audio_files:
                        raise Exception("Audio download failed - file not found")
                    audio_temp = os.path.join(temp_dir, audio_files[0])
                    if not os.path.exists(audio_temp) or os.path.getsize(audio_temp) == 0:
                        raise Exception("Audio file is missing or empty")

                # ── Cache both streams ──────────────────────────────────────
                if self.video_cache_dir and not video_cached:
                    self.append_terminal_output("Caching video for future downloads...\n", 'cache')
                    cached_path = self.cache_video_stream(video_id, video_format_id, video_temp)
                    if cached_path:
                        video_temp = cached_path
                        use_cache = True
                        cached_video_path = cached_path
                        self._resume_args = (video_format_id, audio_format_id, output_path,
                                             quality, use_cache, cached_video_path, temp_dir, url, video_id, video_info)
                        self.append_terminal_output("Video cached successfully\n", 'cache')

                if self.audio_cache_dir and not audio_cached:
                    self.append_terminal_output("Caching audio for future downloads...\n", 'cache')
                    cached_a = self.cache_audio_stream(video_id, audio_format_id, audio_temp)
                    if cached_a:
                        audio_temp = cached_a
                        self.root.after(0, self._update_cache_size_label)
                        self.append_terminal_output("Audio cached successfully\n", 'cache')

                # ── Advance queue on streams done ────────────────────────────
                # When enabled, clear _download_active and start the next queued
                # item now - before FFmpeg merge begins.  The current item's merge
                # and post-processing continue in this thread.  Multiple FFmpeg
                # processes may run concurrently (merge + hardsub from prior item).
                if getattr(self, 'advance_queue_on_streams_done', False):
                    self.root.after(0, lambda: setattr(self, '_download_active', False))
                    self.root.after(500, self._start_next_queued)
                # ────────────────────────────────────────────────────────────

                # ── Single-pass: merge + metadata + thumbnail ────────────
                self.append_terminal_output("Merging video and audio with FFmpeg...\n", 'info')
                os.makedirs(os.path.dirname(output_path), exist_ok=True)

                # Build metadata using per-field toggles and download thumbnail
                meta = {}
                thumb_path = None
                subtitle_path = None
                if self.ffmpeg_path and getattr(self, '_m_embed', False):
                    info = video_info or {}
                    if getattr(self, 'meta_embed_title', True) and info.get('title'):
                        meta['title'] = info['title']
                    if getattr(self, 'meta_embed_artist', True) and (info.get('uploader') or info.get('channel')):
                        meta['artist'] = info.get('uploader') or info.get('channel')
                    if getattr(self, 'meta_embed_date', True) and info.get('upload_date'):
                        _rd = str(info['upload_date'])
                        meta['date'] = (_rd[:4] + '-' + _rd[4:6] + '-' + _rd[6:8]) if len(_rd) == 8 else _rd
                    if getattr(self, 'meta_embed_comment', True) and (info.get('webpage_url') or info.get('original_url')):
                        meta['comment'] = info.get('webpage_url') or info.get('original_url')
                    if getattr(self, 'meta_embed_synopsis', True) and info.get('description'):
                        meta['synopsis'] = info['description'][:500]
                    thumb_url = info.get('thumbnail')
                    if thumb_url:
                        thumb_path = self.cache_thumbnail(video_id, thumb_url, info)

                # ── Download subtitle if requested ───────────────────────
                sub_is_auto = False   # tracks whether auto-generated sub was used
                _sub_src = _snap_sub_src
                sub_lang = _snap_sub_lang  # always defined; used later for metadata
                if _sub_src != 'off' and self.ffmpeg_path:

                    # ── Cache check: manual sub ───────────────────────────────
                    _cached_manual = self.get_cached_subtitle_path(video_id, sub_lang, False)
                    if _cached_manual:
                        # Copy from cache into this download's temp dir so FFmpeg
                        # can consume it without touching the cached original.
                        subtitle_path = os.path.join(temp_dir, 'subtitle_dl.srt')
                        shutil.copy2(_cached_manual, subtitle_path)
                        self.append_terminal_output(
                            'Subtitle (manual) from cache: ' + os.path.basename(_cached_manual) + '\n', 'info')

                    # ── Cache check: auto sub (also for external mode) ───────
                    if not subtitle_path and _sub_src in ('auto', 'external'):
                        _cached_auto = self.get_cached_subtitle_path(video_id, sub_lang, True)
                        if _cached_auto:
                            subtitle_path = os.path.join(temp_dir, 'subtitle_dl.srt')
                            shutil.copy2(_cached_auto, subtitle_path)
                            sub_is_auto = True
                            self.append_terminal_output(
                                'Subtitle (auto-generated) from cache: ' + os.path.basename(_cached_auto) + '\n', 'info')

                    # ── Network download if no cache hit ──────────────────────
                    if not subtitle_path:
                        _sub_out = os.path.join(temp_dir, 'subtitle_dl.%(ext)s')

                        # Warn upfront if language not in known available sets
                        _known_manual = set((video_info.get('subtitles') or {}).keys())
                        _known_auto   = set((video_info.get('automatic_captions') or {}).keys())
                        _lang_in_manual = sub_lang in _known_manual
                        _lang_in_auto   = (sub_lang in _known_auto or
                                           any(k.startswith(sub_lang + '-') for k in _known_auto))
                        if not _lang_in_manual and not _lang_in_auto:
                            self.append_terminal_output(
                                'No ' + sub_lang + ' subtitles exist for this video - skipping.\n', 'warning')
                        else:
                            # Try manual subs first
                            sub_args_manual = [
                                '--no-warnings', '--write-sub',
                                '--sub-lang', sub_lang, '--skip-download',
                                '--sub-format', 'srt/vtt/best',
                                '-o', _sub_out,
                            ]
                            sub_args_manual.extend(self.get_player_client_extractor_args())
                            sub_args_manual.extend(self.get_ytdlp_dns_args())
                            sub_args_manual.append(url)
                            if _lang_in_manual:
                                self.append_terminal_output(
                                    'Fetching subtitle (' + sub_lang + ', manual)...\n', 'info')
                            try:
                                _res_manual = subprocess.run(
                                    self._ytdlp_head() + sub_args_manual,
                                    capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=60,
                                    creationflags=CREATE_NO_WINDOW)
                                for _f in os.listdir(temp_dir):
                                    if _f.startswith('subtitle_dl.') and _f.endswith(('.srt', '.vtt', '.ass')):
                                        subtitle_path = os.path.join(temp_dir, _f)
                                        self.append_terminal_output(
                                            'Subtitle (manual) downloaded: ' + _f + '\n', 'info')
                                        self.cache_subtitle(video_id, sub_lang, False, subtitle_path)
                                        break
                                if not subtitle_path and _res_manual.stderr.strip():
                                    self.append_terminal_output(
                                        'Manual sub note: ' + _res_manual.stderr.strip()[:120] + '\n', 'warning')
                            except Exception as _se:
                                self.append_terminal_output(
                                    'Manual subtitle download failed: ' + str(_se) + '\n', 'warning')

                            # Auto-generated fallback if no manual found and source allows it
                            if not subtitle_path and _sub_src in ('auto', 'external'):
                                # Recently-ended live streams report auto-captions in
                                # metadata immediately, but YouTube hasn't finished
                                # generating them yet - fetching hangs until timeout.
                                # Skip if still in active post-processing (post_live),
                                # or if was_live and ended within the last 24 hours
                                # (captions may still be generating).  Old live VODs
                                # that aired more than 24 hours ago are treated normally.
                                _live_status  = video_info.get('live_status', '')
                                _vid_ts       = video_info.get('timestamp')
                                _recent_live  = (
                                    bool(video_info.get('was_live')) and
                                    _vid_ts is not None and
                                    (time.time() - float(_vid_ts)) < 86400
                                )
                                _skip_auto_sub = (_live_status == 'post_live' or _recent_live)
                                if _skip_auto_sub:
                                    self.append_terminal_output(
                                        'Skipping auto-subtitle - live stream, captions still processing.\n', 'warning')
                                else:
                                    sub_args_auto = [
                                        '--no-warnings', '--write-auto-subs',
                                        '--sub-lang', sub_lang, '--skip-download',
                                        '--sub-format', 'srt/vtt/best',
                                        '-o', _sub_out,
                                    ]
                                    sub_args_auto.extend(self.get_player_client_extractor_args())
                                    sub_args_auto.extend(self.get_ytdlp_dns_args())
                                    sub_args_auto.append(url)
                                    self.append_terminal_output(
                                        'Fetching subtitle (' + sub_lang + ', auto, up to 60s)...\n', 'info')
                                    try:
                                        _res_auto = subprocess.run(
                                            self._ytdlp_head() + sub_args_auto,
                                            capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=60,
                                            creationflags=CREATE_NO_WINDOW)
                                        for _f in os.listdir(temp_dir):
                                            if _f.startswith('subtitle_dl.') and _f.endswith(('.srt', '.vtt', '.ass')):
                                                subtitle_path = os.path.join(temp_dir, _f)
                                                sub_is_auto = True
                                                self.append_terminal_output(
                                                    'Subtitle (auto-generated) downloaded: ' + _f + '\n', 'info')
                                                self.cache_subtitle(video_id, sub_lang, True, subtitle_path)
                                                break
                                        if not subtitle_path and _res_auto.stderr.strip():
                                            self.append_terminal_output(
                                                'Auto sub note: ' + _res_auto.stderr.strip()[:120] + '\n', 'warning')
                                    except Exception as _se:
                                        self.append_terminal_output(
                                            'Auto subtitle download failed: ' + str(_se) + '\n', 'warning')

                    if not subtitle_path:
                        if _sub_src != 'off':
                            self.append_terminal_output(
                                'No subtitle embedded - file renamed without sub tag.\n', 'warning')

                # ── Build FFmpeg command ─────────────────────────────────────
                _sub_mode = _snap_sub_mode
                # External mode: subtitle downloaded but not embedded.
                # The file is saved alongside the output after the merge completes.
                _do_external_sub = (subtitle_path and os.path.exists(subtitle_path)
                                    and _snap_sub_src == 'external')
                _do_hardsub = (subtitle_path and os.path.exists(subtitle_path)
                               and _sub_mode == 'HS' and not _do_external_sub)
                _do_softsub = (subtitle_path and os.path.exists(subtitle_path)
                               and _sub_mode in ('S', 'SD') and not _do_external_sub)

                if _do_hardsub:
                    # Hard sub: re-encode video with subtitle burned in.
                    # FFmpeg's subtitles filter path parsing is unreliable on Windows
                    # with absolute paths (drive colons, spaces, brackets all cause
                    # issues).  Safest fix: copy the sub to a plain short name in the
                    # temp dir and pass just the filename, running FFmpeg with
                    # cwd=temp_dir so it resolves the relative path correctly.
                    _safe_sub = os.path.join(temp_dir, 'hs_sub.srt')
                    try:
                        shutil.copy2(subtitle_path, _safe_sub)
                        # ── Hardsub overlap fix ───────────────────────────────
                        # FFmpeg burns every SRT entry that is active on a frame.
                        # If entry N's end-time overlaps entry N+1's start-time,
                        # both are painted simultaneously causing subtitle stacking.
                        # Pre-process the copy: clamp each entry's end to the
                        # next entry's start minus 1 ms so no two are ever active
                        # at the same time.  Soft-sub paths are unaffected.
                        try:
                            import re as _srt_re
                            def _srt_ms(t):
                                h, m, s, ms = int(t[0]), int(t[1]), int(t[2]), int(t[3])
                                return ((h * 3600 + m * 60 + s) * 1000) + ms
                            def _ms_srt(ms):
                                ms = max(0, ms)
                                h = ms // 3600000; ms %= 3600000
                                m = ms // 60000;   ms %= 60000
                                s = ms // 1000;    ms %= 1000
                                return '{:02d}:{:02d}:{:02d},{:03d}'.format(h, m, s, ms)
                            _tc_pat = _srt_re.compile(
                                r'(\d+):(\d+):(\d+),(\d+)\s*-->\s*(\d+):(\d+):(\d+),(\d+)')
                            with open(_safe_sub, 'r', encoding='utf-8', errors='replace') as _sf:
                                _raw = _sf.read()
                            _entries = [e.strip() for e in _srt_re.split(r'\n\s*\n', _raw) if e.strip()]
                            _timecodes = []
                            for _e in _entries:
                                _m = _tc_pat.search(_e)
                                if _m:
                                    _timecodes.append((_srt_ms(_m.groups()[:4]),
                                                       _srt_ms(_m.groups()[4:])))
                                else:
                                    _timecodes.append(None)
                            _out_entries = []
                            for _i, _e in enumerate(_entries):
                                if _timecodes[_i] is None:
                                    _out_entries.append(_e)
                                    continue
                                _start, _end = _timecodes[_i]
                                # Find next entry with a valid timecode
                                _next_start = None
                                for _j in range(_i + 1, len(_timecodes)):
                                    if _timecodes[_j] is not None:
                                        _next_start = _timecodes[_j][0]
                                        break
                                if _next_start is not None and _end > _next_start:
                                    _end = _next_start - 1
                                _fixed = _tc_pat.sub(
                                    _ms_srt(_start) + ' --> ' + _ms_srt(_end), _e, count=1)
                                _out_entries.append(_fixed)
                            with open(_safe_sub, 'w', encoding='utf-8') as _sf:
                                _sf.write('\n\n'.join(_out_entries) + '\n')
                        except Exception:
                            pass  # If pre-processing fails, burn original as-is
                    except Exception:
                        _safe_sub = subtitle_path
                    # subtitles filter needs original_size=WxH for WebM/VP9 inputs
                    _vid_w, _vid_h = 0, 0
                    try:
                        for _fmt in (video_info or {}).get('formats', []):
                            if str(_fmt.get('format_id', '')) == str(video_format_id):
                                _vid_w = _fmt.get('width') or 0
                                _vid_h = _fmt.get('height') or 0
                                break
                    except Exception:
                        pass
                    if not (_vid_w and _vid_h):
                        try:
                            _vid_h = int(quality.rstrip('p'))
                            _vid_w = int(round(_vid_h * 16 / 9))
                        except Exception:
                            _vid_w, _vid_h = 256, 144
                    _orig_size = str(_vid_w) + 'x' + str(_vid_h)
                    _vf_filter = 'subtitles=hs_sub.srt:original_size=' + _orig_size
                    # All -i inputs must come first, then output options.
                    # This construction only runs on the hardsub branch, so the
                    # hw-decode args need no gate; the softsub/copy branch below
                    # builds its own command and is untouched.
                    merge_cmd = ([self.ffmpeg_path, '-y']
                                 + self._hardsub_input_args()
                                 + ['-i', video_temp, '-i', audio_temp])
                    if thumb_path and os.path.exists(thumb_path):
                        merge_cmd += ['-i', thumb_path]
                    merge_cmd += ['-map', '0:v', '-map', '1:a']
                    if thumb_path and os.path.exists(thumb_path):
                        merge_cmd += ['-map', '2',
                                      '-c:v:1', 'mjpeg',
                                      '-disposition:v:1', 'attached_pic']
                    merge_cmd += self._hardsub_codec_args('-c:v:0') + [
                                  '-vf', _vf_filter,
                                  '-c:a', 'copy']
                else:
                    # Soft sub or no sub: stream copy video.
                    # IMPORTANT: softsub output is MKV, not MP4. The FFmpeg MP4
                    # muxer hardcodes default=1 on the first subtitle track and
                    # ignores -disposition overrides entirely (tested: FFmpeg 6.x).
                    # MKV respects -disposition flags correctly.
                    # Thumbnail embedding is skipped for MKV softsub - MKV attached
                    # image support is inconsistent across players; the thumbnail
                    # metadata is still embedded via -metadata.
                    merge_cmd = [self.ffmpeg_path, '-y', '-i', video_temp, '-i', audio_temp]
                    if _do_softsub:
                        merge_cmd += ['-i', subtitle_path]
                    if thumb_path and os.path.exists(thumb_path):
                        merge_cmd += ['-i', thumb_path]
                    # ISO 639-1 (2-letter) -> ISO 639-2 (3-letter) for FFmpeg language tag
                    # MPV requires 3-letter codes; VLC accepts both
                    _ISO2_TO_3 = {
                        'en': 'eng', 'es': 'spa', 'fr': 'fra', 'de': 'deu',
                        'it': 'ita', 'pt': 'por', 'ru': 'rus', 'ja': 'jpn',
                        'ko': 'kor', 'zh': 'zho', 'ar': 'ara', 'hi': 'hin',
                    }
                    _LANG_NAMES = {
                        'en': 'English', 'es': 'Spanish', 'fr': 'French',
                        'de': 'German', 'it': 'Italian', 'pt': 'Portuguese',
                        'ru': 'Russian', 'ja': 'Japanese', 'ko': 'Korean',
                        'zh': 'Chinese', 'ar': 'Arabic', 'hi': 'Hindi',
                    }
                    _lang3 = _ISO2_TO_3.get(sub_lang.lower(), sub_lang.lower())
                    _lang_title = _LANG_NAMES.get(sub_lang.lower(), sub_lang.upper())
                    if _do_softsub and thumb_path and os.path.exists(thumb_path):
                        merge_cmd += ['-map', '0:v:0', '-map', '1:a:0', '-map', '2:s:0', '-map', '3:v:0',
                                      '-c:v:0', 'copy',
                                      '-c:a:0', 'copy',
                                      '-c:s:0', 'mov_text',
                                      '-metadata:s:2', 'language=' + _lang3,
                                      '-metadata:s:2', 'title=' + _lang_title,
                                      '-disposition:s:0', 'default+forced' if _sub_mode == 'SD' else 'none',
                                      '-c:v:1', 'mjpeg',
                                      '-disposition:v:1', 'attached_pic']
                    elif _do_softsub:
                        merge_cmd += ['-map', '0:v:0', '-map', '1:a:0', '-map', '2:s:0',
                                      '-c:v:0', 'copy',
                                      '-c:a:0', 'copy',
                                      '-c:s:0', 'mov_text',
                                      '-metadata:s:0', 'language=' + _lang3,
                                      '-metadata:s:0', 'title=' + _lang_title,
                                      '-disposition:s:0', 'default+forced' if _sub_mode == 'SD' else 'none']
                    elif thumb_path and os.path.exists(thumb_path):
                        merge_cmd += ['-map', '0:v:0', '-map', '1:a:0', '-map', '2:v:0',
                                      '-c:v:0', 'copy',
                                      '-c:a:0', 'copy',
                                      '-c:v:1', 'mjpeg',
                                      '-disposition:v:1', 'attached_pic']
                    else:
                        merge_cmd += ['-map', '0:v:0', '-map', '1:a:0',
                                      '-c:v:0', 'copy', '-c:a:0', 'copy']

                for k, v in meta.items():
                    merge_cmd += ['-metadata', k + '=' + str(v)]

                if meta:
                    self.append_terminal_output('Metadata fields: ' + str(list(meta.keys())) + '\n', 'info')

                _merge_tmp = os.path.join(temp_dir, 'merged_output.mp4')
                # For hardsub we use -progress pipe:1 so FFmpeg writes key=value
                # progress lines we can parse to show a frame counter.
                # For copy-codec paths keep -loglevel error (no overhead).
                if _do_hardsub:
                    # -hwaccel auto lets FFmpeg use GPU decoding where available
                    # (DXVA2/D3D11VA on Windows, NVDEC on NVIDIA, etc.).
                    # FFmpeg silently falls back to CPU if no hardware decoder is
                    # found - this flag is always safe to pass.
                    # Apply ONLY to hardsub; stream-copy paths do no decoding.
                    merge_cmd = [self.ffmpeg_path, '-y',
                                 '-hwaccel', 'auto',
                                 '-threads', '0'] + merge_cmd[2:]
                    merge_cmd += ['-movflags', '+faststart',
                                  '-loglevel', 'warning',
                                  '-progress', 'pipe:1', '-nostats',
                                  _merge_tmp]
                else:
                    merge_cmd += ['-threads', '0',
                                  '-movflags', '+faststart', '-loglevel', 'error', _merge_tmp]

                # Hardsub re-encodes every frame with libx264 - encode time is
                # proportional to video length and CPU speed with no reliable upper
                # bound, so we never impose a timeout.  Copy-codec merges (soft sub,
                # no sub) finish in seconds; 1800 s is a generous safety net.
                _merge_timeout = None if _do_hardsub else 1800

                # ── Apply clip (section download) if active ─────────────────
                # Use output-level -ss/-to (placed after codec options, before
                # the output file).  This is slower than input-level seeking
                # (FFmpeg reads from the start) but guarantees perfect A/V sync.
                # Input-level -ss (before -i) causes audio to start late because
                # video and audio keyframes are at different positions.
                if _clip_active:
                    _clip_dur = _clip_end_sec - _clip_start_sec
                    # Insert -ss and -to right before the output path (last element)
                    merge_cmd.insert(-1, '-ss')
                    merge_cmd.insert(-1, _clip_start_hms)
                    merge_cmd.insert(-1, '-to')
                    merge_cmd.insert(-1, _clip_end_hms)
                    self.append_terminal_output(
                        'Clip: ' + _clip_start_hms + ' to ' + _clip_end_hms +
                        ' (' + str(round(_clip_dur, 1)) + 's)\n', 'info')

                # Use Popen instead of run so we can store the process handle and
                # allow the Stop button to kill FFmpeg mid-merge.
                _ffmpeg_proc = subprocess.Popen(
                    merge_cmd,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.STDOUT,
                    text=True, encoding='utf-8', errors='replace',
                    creationflags=CREATE_NO_WINDOW,
                    cwd=temp_dir,
                )
                self._ffmpeg_process = _ffmpeg_proc
                # Re-enable Stop button - it was greyed out after yt-dlp finished
                self.root.after(0, lambda: self.stop_btn.config(state='normal'))

                # ── Parallel hardsub: release the queue now ─────────────────
                # ── Parallel stream pre-caching: handled by _start_next_queued ──
                # Pre-caching fires at the start of every download when
                # parallel_hardsub is enabled, so no separate trigger needed here.
                # ────────────────────────────────────────────────────────────

                _merge_stdout_buf = []
                try:
                    if _do_hardsub:
                        # ── Hardsub progress with frame counter and ETA ──────
                        # Compute total expected frames from video duration × fps.
                        # Both come from video_info; fall back gracefully if absent.
                        _hs_duration = float((video_info or {}).get('duration') or 0)
                        _hs_fps = 0.0
                        try:
                            for _pf in (video_info or {}).get('formats', []):
                                if str(_pf.get('format_id', '')) == str(video_format_id):
                                    _hs_fps = float(_pf.get('fps') or 0)
                                    break
                        except Exception:
                            pass
                        _hs_total_frames = int(_hs_duration * _hs_fps) if (_hs_duration and _hs_fps) else 0
                        # Short title for status bar (max 30 chars so it fits)
                        _hs_title = (video_info or {}).get('title', '') or ''
                        _hs_label = (_hs_title[:27] + '…') if len(_hs_title) > 30 else _hs_title
                        _hs_start_time = time.monotonic()
                        _hs_frame = 0

                        for _pline in _ffmpeg_proc.stdout:
                            _pline = _pline.rstrip()
                            _merge_stdout_buf.append(_pline)
                            if _pline.startswith('frame='):
                                try:
                                    _hs_frame = int(_pline.split('=', 1)[1].strip())
                                    _elapsed = time.monotonic() - _hs_start_time
                                    # Build progress string
                                    if _hs_total_frames > 0 and _hs_frame > 0:
                                        _pct = min(100, int(_hs_frame * 100 / _hs_total_frames))
                                        # ETA = elapsed / frames_done * frames_remaining
                                        _eta_s = (_elapsed / _hs_frame) * (_hs_total_frames - _hs_frame)
                                        if _eta_s < 60:
                                            _eta_str = '{:.0f}s'.format(_eta_s)
                                        else:
                                            _eta_str = '{:.0f}m{:.0f}s'.format(
                                                _eta_s // 60, _eta_s % 60)
                                        _prog_msg = ('HS {pct}% - frame {f}/{t} - ETA {eta}'
                                                     ' [{lbl}]').format(
                                            pct=_pct, f=_hs_frame,
                                            t=_hs_total_frames, eta=_eta_str,
                                            lbl=_hs_label)
                                    else:
                                        _prog_msg = ('HS frame {f} [{lbl}]').format(
                                            f=_hs_frame, lbl=_hs_label)
                                    self.root.after(0, lambda m=_prog_msg:
                                        self.progress_var.set(m))
                                except Exception:
                                    pass
                            if self._download_stopped:
                                break
                        # Drain any remaining output so the pipe buffer never
                        # blocks FFmpeg and causes wait() to deadlock.
                        try:
                            _ffmpeg_proc.stdout.read()
                        except Exception:
                            pass
                        _ffmpeg_proc.wait()
                        self.root.after(0, lambda: self.progress_var.set('Merging...'))
                        _merge_stdout = '\n'.join(_merge_stdout_buf)
                    else:
                        _merge_stdout, _ = _ffmpeg_proc.communicate(timeout=_merge_timeout)
                except subprocess.TimeoutExpired:
                    _ffmpeg_proc.kill()
                    _ffmpeg_proc.communicate()
                    self._ffmpeg_process = None
                    raise Exception("FFmpeg merge timed out after " + str(_merge_timeout) + "s")
                finally:
                    self._ffmpeg_process = None

                # If the user clicked Stop while FFmpeg was running, honour it now
                if self._download_stopped:
                    raise _DownloadStoppedError("stopped during merge")

                merge_returncode = _ffmpeg_proc.returncode

                if merge_returncode != 0:
                    if _do_hardsub:
                        self._hardsub_demote('merge burn', merge_returncode)
                    ffmpeg_err = (_merge_stdout or '').strip()[-500:]
                    raise Exception("FFmpeg merge failed (code " + str(merge_returncode) + "):\n" + ffmpeg_err)

                if not os.path.exists(_merge_tmp) or os.path.getsize(_merge_tmp) == 0:
                    raise Exception("Merge completed but output file is missing or empty")

                if meta or thumb_path:
                    self.append_terminal_output('Merge + metadata embedded in single pass.\n', 'success')
                else:
                    self.append_terminal_output('Merge complete.\n', 'success')

                # Patch the subtitle Track_Enabled bit in the tkhd box.
                # FFmpeg's MP4 muxer ignores -disposition flags for this bit,
                # so we correct it directly regardless of mode:
                #   S / AS  -> clear the bit (user-select, do not auto-show)
                #   SD / ASD -> set the bit   (default-on, auto-show)
                if _do_softsub:
                    self._patch_mp4_subtitle_flag(_merge_tmp, enabled=(_sub_mode == 'SD'))
                # ─────────────────────────────────────────────────────────────

                # ── Determine final filename ──────────────────────────────────
                # Resolve the correct subtitle tag based on what actually happened,
                # then move _merge_tmp to the downloads folder in one atomic step.
                # The collision guard runs on the final resolved name so the (2)
                # suffix is only added when a genuinely distinct file already exists.
                #
                # Pre-build a subtitle-free fallback path so that if the rename
                # logic below throws, the except block uses a clean name that does
                # not carry any subtitle tag (we can't be sure what was embedded).
                # Derive audio language here so both the fallback and the normal
                # rename path share the same value without duplicating the lookup.
                _ren_lang = ''
                try:
                    for _af in (video_info.get('formats') or []):
                        if str(_af.get('format_id', '')) == str(audio_format_id):
                            _dl = self.detect_audio_language(_af)
                            if _dl and _dl != 'unknown':
                                _ren_lang = _dl.upper()
                            break
                except Exception:
                    pass
                _ren_qt = (quality + ' ' + _ren_lang).strip()
                _fallback_path = self._unique_output_path(os.path.join(
                    self.download_path,
                    self._assemble_filename(video_info, _ren_qt, '.mp4')),
                    (video_info or {}).get('id'))
                try:
                    _sub_embedded = (subtitle_path and os.path.exists(subtitle_path))
                    if _sub_embedded and _do_hardsub:
                        _final_sub_tag = 'AHS' if sub_is_auto else 'HS'
                    elif _sub_embedded and _do_softsub:
                        if _snap_sub_mode == 'SD':
                            _final_sub_tag = 'ASD' if sub_is_auto else 'SD'
                        else:
                            _final_sub_tag = 'AS' if sub_is_auto else 'S'
                    else:
                        _final_sub_tag = None  # no sub found - omit tag
                    # _ren_lang and _ren_qt already computed above (shared with fallback path).
                    if _final_sub_tag:
                        _ren_bracket = _ren_qt + ' ' + _final_sub_tag
                    else:
                        _ren_bracket = _ren_qt
                    _resolved_path = os.path.join(
                        self.download_path,
                        self._assemble_filename(video_info, _ren_bracket, '.mp4'))
                    # Collision guard on the final resolved name only
                    _final_path = self._unique_output_path(_resolved_path, (video_info or {}).get('id'))
                    shutil.move(_merge_tmp, _final_path)
                    output_path = _final_path
                except Exception as _pe:
                    # Fallback: move to a subtitle-free path so the filename
                    # does not carry a tag that may not reflect what was embedded.
                    self.append_terminal_output(
                        'Warning: final rename failed (' + str(_pe) + ') - using original name.\n', 'warning')
                    shutil.move(_merge_tmp, _fallback_path)
                    output_path = _fallback_path
                # ────────────────────────────────────────────────────────────

                # ── Set filesystem timestamps to publish date ────────────────
                self._set_file_timestamps(output_path, video_info)
                # ────────────────────────────────────────────────────────────

                # ── External subtitle: save .srt alongside output file ────────
                if _do_external_sub and subtitle_path and os.path.exists(subtitle_path):
                    try:
                        _sub_base = os.path.splitext(output_path)[0]
                        _ext_sub_dest = _sub_base + '.' + sub_lang + '.srt'
                        shutil.copy2(subtitle_path, _ext_sub_dest)
                        self.append_terminal_output(
                            'Subtitle saved externally: ' + os.path.basename(_ext_sub_dest) + '\n', 'success')
                    except Exception as _ext_err:
                        self.append_terminal_output(
                            'External subtitle save failed: ' + str(_ext_err) + '\n', 'warning')
                # ────────────────────────────────────────────────────────────

                download_time = time.time() - self.download_start_time
                file_size = self.format_file_size(os.path.getsize(output_path))
                cache_info = " (using cached video)" if use_cache else ""

                self.append_terminal_output("\nDownload and merge completed successfully!\n", 'success')
                self.append_terminal_output("File: " + os.path.basename(output_path) + "\n", 'success')
                self.append_terminal_output("Size: " + file_size + "\n", 'success')
                self.append_terminal_output("Time: " + self._format_download_time(download_time) + "\n", 'success')
                if cache_info:
                    self.append_terminal_output("Cache optimization used\n", 'cache')
                self.append_terminal_output("\n", 'info')

                # Clean up temp dir on success
                try:
                    shutil.rmtree(temp_dir, ignore_errors=True)
                    self.append_terminal_output("Cleaned up temp directory.\n", 'info')
                except Exception:
                    pass

                self._pending_history_meta = {'url': url, 'video_info': video_info, 'quality': quality}
                self.root.after(0, lambda: self._download_complete(output_path, "Download & Merge" + cache_info, download_time))
                return
                
            except (_DownloadStoppedError, _DownloadPausedError):
                # User intentionally stopped or paused - do not retry
                return
            except Exception as e:
                _last_exc_str = str(e)
                self.append_terminal_output("\nAttempt " + str(attempt + 1) + " failed: " + str(e) + "\n", 'error')
                self.append_terminal_output("Partial stream files kept in temp dir for resume.\n", 'info')

                # "Requested format is not available" means the stream URL/token
                # has expired between analysis time and download time (common in long
                # queues).  Re-fetch fresh video info and restart with the new format
                # IDs instead of giving up.
                if 'Requested format is not available' in _last_exc_str and attempt == 0:
                    self.append_terminal_output(
                        "\nStream URL expired - re-fetching fresh format IDs for " + quality + "...\n", 'warning')
                    try:
                        fresh_info = self.get_video_info(url)
                        fresh_vid_fid, fresh_aud_fid = self._resolve_fresh_format_ids(
                            fresh_info, video_format_id, audio_format_id, quality)
                        if fresh_vid_fid and fresh_aud_fid:
                            # Guard 1 - identical ids. If the refresh handed
                            # back exactly what just failed, the restart would
                            # re-issue the same request and fail the same way.
                            # This happens when the info leg and the download
                            # leg use different player clients: info reports a
                            # format the download client does not offer, and no
                            # number of refreshes will change that.
                            if (str(fresh_vid_fid) == str(video_format_id)
                                    and str(fresh_aud_fid) == str(audio_format_id)):
                                self.append_terminal_output(
                                    "Refresh returned the same format IDs (video="
                                    + str(fresh_vid_fid) + " audio="
                                    + str(fresh_aud_fid) + ") - not a stale URL.\n"
                                    "The download client may not offer this format. "
                                    "Try Player Client = default in Settings.\n",
                                    'error')
                                raise
                            # Guard 2 - depth. Mirrors _fmt_restart_depth in
                            # the audio-only path: the restart below re-enters
                            # this worker from inside its own except handler,
                            # which resets `attempt` and defeats the attempt==0
                            # check above.
                            _d = getattr(self, '_fmt_restart_depth', 0)
                            if _d >= 2:
                                self.append_terminal_output(
                                    "Format kept expiring after " + str(_d)
                                    + " refreshes - giving up on this attempt.\n",
                                    'error')
                                raise
                            self.append_terminal_output(
                                "Fresh format IDs: video=" + fresh_vid_fid +
                                " audio=" + fresh_aud_fid + " - restarting download.\n", 'info')
                            # Wipe the stale temp dir and restart the whole worker
                            # with the fresh IDs so the retry loop gets a clean slate.
                            try:
                                shutil.rmtree(temp_dir, ignore_errors=True)
                            except Exception:
                                pass
                            self._fmt_restart_depth = _d + 1
                            try:
                                self._download_and_merge_worker_with_terminal(
                                    fresh_vid_fid, fresh_aud_fid, output_path, quality,
                                    False, None, None, url, video_id, fresh_info)
                            finally:
                                self._fmt_restart_depth = _d
                            return
                        elif fresh_vid_fid and fresh_aud_fid is None:
                            # Find actual resolution of combined stream so the
                            # filename label matches what was actually downloaded
                            actual_quality = quality
                            try:
                                for _fmt in fresh_info.get('formats', []):
                                    if str(_fmt.get('format_id', '')) == fresh_vid_fid:
                                        _h = _fmt.get('height') or 0
                                        _w = _fmt.get('width') or 0
                                        _dim = min(_h, _w) if _h and _w else (_h or _w)
                                        if _dim:
                                            actual_quality = str(_dim) + 'p'
                                        break
                            except Exception:
                                pass
                            # Rebuild output path with the corrected quality label.
                            # Use _assemble_filename so the name is built cleanly
                            # from fresh_info - no regex surgery, no backreference bugs.
                            if actual_quality != quality:
                                _ren_lang = ''
                                try:
                                    for _af in (fresh_info.get('formats') or []):
                                        if str(_af.get('format_id', '')) == fresh_vid_fid:
                                            _dl = self.detect_audio_language(_af)
                                            if _dl and _dl != 'unknown':
                                                _ren_lang = ' ' + _dl.upper()
                                            break
                                except Exception:
                                    pass
                                _new_bracket = actual_quality + _ren_lang
                                _new_name = self._assemble_filename(
                                    fresh_info, _new_bracket, '.mp4')
                                output_path = os.path.join(self.download_path, _new_name)
                            self.append_terminal_output(
                                "Fresh format ID: combined=" + fresh_vid_fid +
                                " (" + actual_quality + ", no separate DASH streams)"
                                " - restarting as direct download.\n", 'info')
                            try:
                                shutil.rmtree(temp_dir, ignore_errors=True)
                            except Exception:
                                pass
                            self._download_direct_worker_with_terminal(
                                fresh_vid_fid, output_path, actual_quality, url, fresh_info,
                                sub_settings=(_snap_sub_src, _snap_sub_mode, _snap_sub_lang),
                                video_id=video_id)
                            return
                        else:
                            self.append_terminal_output(
                                "Could not find matching streams in fresh info - giving up.\n", 'error')
                    except Exception as refresh_err:
                        self.append_terminal_output(
                            "Re-fetch failed: " + str(refresh_err) + "\n", 'error')

                    # Re-fetch failed or no matching stream - hard fail
                    error_msg = "Download failed (format expired, re-fetch unsuccessful): " + str(e)
                    self.append_terminal_output("\nFinal failure: " + error_msg + "\n\n", 'error')
                    self._emit_dev_event('failed', error=error_msg)
                    try:
                        shutil.rmtree(temp_dir, ignore_errors=True)
                    except Exception:
                        pass
                    self.root.after(0, lambda m=error_msg: self._download_error(m))
                    return

                if attempt == max_retries - 1:
                    error_msg = "Download and merge failed after " + str(max_retries) + " attempts: " + str(e)
                    self.append_terminal_output("\nFinal failure: " + error_msg + "\n\n", 'error')
                    self._emit_dev_event('failed', error=error_msg)
                    try:
                        shutil.rmtree(temp_dir, ignore_errors=True)
                    except Exception:
                        pass
                    self.root.after(0, lambda m=error_msg: self._download_error(m))
                    return

            finally:
                if attempt == 0:
                    self.root.after(0, lambda: self.progress_bar.stop())

    

    def _resolve_fresh_format_ids(self, fresh_info, old_video_fid, old_audio_fid, quality):
        """Given freshly-fetched video info, find the best video and audio format IDs
        that match the original quality intent (same resolution, same audio preference).
        Returns (video_format_id, audio_format_id) strings, or (None, None) on failure.
        Returns (combined_format_id, None) when only a combined stream is available.

        Called when a queued download hits 'Requested format is not available' because
        the stream URL token expired between analysis time and download time."""
        try:
            formats = fresh_info.get('formats', [])
            video_only, audio_only, combined = [], [], []
            for fmt in formats:
                has_video = fmt.get('vcodec') not in (None, 'none')
                has_audio = fmt.get('acodec') not in (None, 'none')
                if has_video and not has_audio:
                    video_only.append(fmt)
                elif has_audio and not has_video:
                    if 'detected_language' not in fmt:
                        _, lang = self.get_audio_stream_description(fmt)
                        fmt['detected_language'] = lang
                    audio_only.append(fmt)
                elif has_video and has_audio:
                    combined.append(fmt)

            # --- Video: match by resolution (height) that corresponds to quality ---
            target_px = int(quality.rstrip('p')) if quality.rstrip('p').isdigit() else None

            def _eff(v):
                h = v.get('height', 0) or 0
                w = v.get('width', 0) or 0
                return min(h, w) if h and w else (h or w)

            if target_px:
                # Use tier matching so non-standard resolutions (e.g. 1086p)
                # are found when the quality label is the standard tier (1080p).
                candidates = [v for v in video_only
                              if _eff(v) > 0 and self._nearest_standard_quality(_eff(v)) == target_px]
            else:
                candidates = video_only

            fresh_video = self.select_best_video_stream(candidates) if candidates else None
            if not fresh_video:
                # Fall back: any video stream closest to original height
                fresh_video = (sorted(video_only, key=_eff, reverse=True) or [None])[0]

            # --- Audio: use select_best_audio_stream (respects language preference) ---
            detected_languages = {}
            for fmt in audio_only:
                lang = fmt.get('detected_language', 'unknown')
                detected_languages.setdefault(lang, []).append(fmt)
            fresh_audio = self.select_best_audio_stream(audio_only, detected_languages)

            if fresh_video and fresh_audio:
                return str(fresh_video.get('format_id', '')), str(fresh_audio.get('format_id', ''))

            # --- Fallback: no separate DASH streams - use best combined stream ---
            if combined:
                if target_px:
                    combined_at_quality = [v for v in combined
                                           if _eff(v) > 0 and self._nearest_standard_quality(_eff(v)) == target_px]
                else:
                    combined_at_quality = combined
                best_combined = (
                    sorted(combined_at_quality, key=_eff, reverse=True) or
                    sorted(combined, key=_eff, reverse=True)
                )[0]
                return str(best_combined.get('format_id', '')), None

        except Exception:
            pass
        return None, None

    def _set_file_timestamps(self, file_path, video_info):
        """Set filesystem created/modified timestamps to the video's publish date.

        We use local noon (12:00) on the upload date rather than UTC midnight.
        UTC midnight converts to the *previous* evening in negative-offset timezones
        (e.g. 8 pm EDT), causing Windows Explorer to show the wrong calendar date.
        Local noon is always within the correct calendar day for any timezone on Earth.
        """
        try:
            raw_date = (video_info or {}).get('upload_date')
            if raw_date and len(str(raw_date)) == 8:
                raw_date = str(raw_date)
                # Naive local noon - Python converts to UTC internally via .timestamp()
                pub_dt_local = datetime.datetime(
                    int(raw_date[:4]), int(raw_date[4:6]), int(raw_date[6:8]),
                    12, 0, 0)
                pub_ts = pub_dt_local.timestamp()
                os.utime(file_path, (pub_ts, pub_ts))
                # Windows FILETIME: 100-ns intervals since 1601-01-01 00:00:00 UTC
                # Derive from the POSIX timestamp to stay consistent with os.utime.
                FILETIME_EPOCH_OFFSET = 11644473600  # seconds between 1601-01-01 and 1970-01-01
                intervals = int((pub_ts + FILETIME_EPOCH_OFFSET) * 10_000_000)
                ft = ctypes.wintypes.FILETIME(
                    intervals & 0xFFFFFFFF, (intervals >> 32) & 0xFFFFFFFF)
                kernel32 = ctypes.windll.kernel32
                kernel32.CreateFileW.restype = ctypes.c_void_p
                _INVALID = ctypes.c_void_p(-1).value
                handle = kernel32.CreateFileW(file_path, 256, 0, None, 3, 128, None)
                if handle is not None and handle != _INVALID:
                    kernel32.SetFileTime(handle, ctypes.byref(ft), None, ctypes.byref(ft))
                    kernel32.CloseHandle(handle)
                self.append_terminal_output(
                    'Filesystem dates set to ' + raw_date[:4] + '-' + raw_date[4:6] + '-' + raw_date[6:8] + '.\n',
                    'success')
        except Exception as ts_err:
            self.append_terminal_output('Could not set filesystem date: ' + str(ts_err) + '\n', 'warning')

    def _embed_metadata(self, output_path, video_info=None):
        """Embed video metadata and thumbnail into output_path using FFmpeg.
        video_info: the info dict for the video being embedded. Falls back to
        self.current_video_info only when not supplied (legacy/direct calls).
        Skips silently if FFmpeg is unavailable or embed_metadata is disabled.
        Returns the final file path on success (may differ from output_path if a
        collision was resolved at write time), or None if skipped or failed."""
        if not self.ffmpeg_path or not getattr(self, '_m_embed', False):
            return None

        thumb_path = None
        meta_out = None
        try:
            info = video_info if video_info is not None else self.current_video_info
            meta = {}
            if info.get('title'):
                meta['title'] = info['title']
            if info.get('uploader') or info.get('channel'):
                meta['artist'] = info.get('uploader') or info.get('channel')
            if info.get('upload_date'):
                raw = str(info['upload_date'])
                meta['date'] = (raw[:4] + '-' + raw[4:6] + '-' + raw[6:8]) if len(raw) == 8 else raw
            if info.get('webpage_url') or info.get('original_url'):
                meta['comment'] = info.get('webpage_url') or info.get('original_url')
            if info.get('description'):
                meta['synopsis'] = info['description'][:500]

            self.append_terminal_output('Metadata fields: ' + str(list(meta.keys())) + '\n', 'info')

            thumb_url = info.get('thumbnail')
            if thumb_url:
                _vid_id = info.get('id', 'unknown')
                thumb_path = self.cache_thumbnail(_vid_id, thumb_url, info)

            base, ext = os.path.splitext(output_path)
            meta_out = base + '_metaembed' + ext

            is_mp3 = ext.lower() == '.mp3'
            is_m4a = ext.lower() == '.m4a'
            embed_cmd = [self.ffmpeg_path, '-y', '-i', output_path]

            if is_mp3:
                # MP3: cover art embedded as ID3v2 APIC frame.
                if thumb_path and os.path.exists(thumb_path):
                    embed_cmd += ['-i', thumb_path,
                                  '-map', '0:a', '-map', '1:v',
                                  '-acodec', 'copy',
                                  '-id3v2_version', '3',
                                  '-metadata:s:v', 'title=Album cover',
                                  '-metadata:s:v', 'comment=Cover (front)']
                else:
                    embed_cmd += ['-map', '0', '-acodec', 'copy',
                                  '-id3v2_version', '3']
                for k, v in meta.items():
                    embed_cmd += ['-metadata', k + '=' + str(v)]
                embed_cmd += ['-loglevel', 'error', meta_out]
            elif is_m4a:
                # M4A: the ipod muxer rejects mjpeg attached pictures and
                # non-AAC codecs. Force the mp4 muxer explicitly (-f mp4) -
                # the file is still valid M4A (M4A is a subset of MP4).
                # Thumbnail embedding requirements by player:
                #   VLC (Android/desktop): needs -c:v mjpeg to produce a
                #     properly boxed MJPEG stream with full encoder headers.
                #     -c:v copy skips header setup and VLC cannot decode it.
                #   Windows Explorer / iTunes / Android MediaStore: need the
                #     stream-level metadata tags title=Album cover and
                #     comment=Cover (front) to classify the stream as artwork.
                # Both requirements are satisfied together below.
                if thumb_path and os.path.exists(thumb_path):
                    embed_cmd += ['-i', thumb_path,
                                  '-map', '0:a', '-map', '1:v',
                                  '-c:a', 'copy',
                                  '-c:v', 'mjpeg',
                                  '-metadata:s:v:0', 'title=Album cover',
                                  '-metadata:s:v:0', 'comment=Cover (front)',
                                  '-disposition:v:0', 'attached_pic']
                else:
                    embed_cmd += ['-map', '0:a', '-c:a', 'copy']
                for k, v in meta.items():
                    embed_cmd += ['-metadata', k + '=' + str(v)]
                embed_cmd += ['-movflags', '+faststart', '-f', 'mp4', '-loglevel', 'error', meta_out]
            else:
                # MP4/MKV/WebM: cover art as attached video stream
                if thumb_path and os.path.exists(thumb_path):
                    embed_cmd += ['-i', thumb_path,
                                  '-map', '0', '-map', '1',
                                  '-c', 'copy',
                                  '-c:v:1', 'mjpeg',
                                  '-disposition:v:1', 'attached_pic']
                else:
                    embed_cmd += ['-map', '0', '-c', 'copy']
                for k, v in meta.items():
                    embed_cmd += ['-metadata', k + '=' + str(v)]
                embed_cmd += ['-movflags', '+faststart', '-loglevel', 'error', meta_out]

            self.append_terminal_output('Embedding metadata and thumbnail...\n', 'info')
            embed_result = subprocess.run(
                embed_cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True, encoding='utf-8', errors='replace',
                timeout=120,
                creationflags=CREATE_NO_WINDOW,
            )

            if embed_result.returncode == 0 and os.path.exists(meta_out):
                # On Windows, Explorer/AV may briefly hold the target file open
                # immediately after it was written.  Retry a few times before giving up.
                _replaced = False
                for _attempt in range(5):
                    try:
                        os.replace(meta_out, output_path)
                        _replaced = True
                        break
                    except PermissionError:
                        time.sleep(0.3)
                if _replaced:
                    self.append_terminal_output('Metadata and thumbnail embedded.\n', 'success')
                    return output_path  # return final path so caller can update its variable
                else:
                    # Last resort: save the metaembed file under a unique name so
                    # it is not lost, and leave the original untouched.
                    _fallback = self._unique_output_path(output_path, (info or {}).get('id'))
                    try:
                        os.replace(meta_out, _fallback)
                        self.append_terminal_output(
                            'Metadata embedded (target locked - saved as ' +
                            os.path.basename(_fallback) + ').\n', 'warning')
                        return _fallback
                    except Exception:
                        pass
                    return None
            else:
                ffmpeg_err = (embed_result.stdout or '').strip()[-300:]
                self.append_terminal_output(
                    'Metadata embed failed (code ' + str(embed_result.returncode) + ') - file saved without metadata:\n' +
                    ffmpeg_err + '\n', 'warning')
                return None

        except Exception as meta_err:
            self.append_terminal_output('Metadata embedding error: ' + str(meta_err) + '\n', 'warning')
            return None
        finally:
            # thumb_path now points to the thumbnail cache - do NOT delete it.
            if meta_out and os.path.exists(meta_out):
                try:
                    os.remove(meta_out)
                except Exception:
                    pass


    # ── Download Queue ─────────────────────────────────────────────────────

    def _setup_queue_panel(self, parent_frame):
        """Create the queue panel in the RIGHT column of _bottom_container.
        Fixed width (220 px), scrollable vertically, so a large queue never
        resizes the window or pushes the stream/terminal views off screen.
        parent_frame argument kept for API compatibility but is not used."""

        self._queue_frame = ttk.LabelFrame(self._bottom_container,
                                           text="Queue", padding="4")
        self._queue_frame.grid(row=0, column=1,
                               sticky=(tk.N, tk.S, tk.E, tk.W))
        self._queue_frame.columnconfigure(0, weight=1)
        self._queue_frame.rowconfigure(0, weight=1)
        # Start hidden – shown only when queue has entries
        self._queue_frame.grid_remove()

        # Canvas gives us a fixed-height scrollable area
        self._queue_canvas = tk.Canvas(
            self._queue_frame,
            background="SystemButtonFace",
            width=340,            # fixed width; does not affect terminal width
            highlightthickness=0)
        self._queue_scrollbar = ttk.Scrollbar(
            self._queue_frame, orient=tk.VERTICAL,
            command=self._queue_canvas.yview)
        self._queue_canvas.configure(yscrollcommand=self._queue_scrollbar.set)
        self._queue_canvas.grid(row=0, column=0,
                                sticky=(tk.N, tk.S, tk.E, tk.W))
        self._queue_scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))

        # Inner frame drawn inside the canvas
        self._queue_listbox = tk.Frame(self._queue_canvas, background="SystemButtonFace")
        self._queue_canvas_window = self._queue_canvas.create_window(
            (0, 0), window=self._queue_listbox, anchor="nw")

        # Keep scroll-region in sync with inner frame size
        def _on_inner_resize(event):
            # bbox('all') is measured from the CURRENT layout. Tk lays out
            # lazily, so when many queue rows are added at once this fires
            # before the inner frame has been sized and returns the old
            # (tiny) bounds - the canvas then believes it has almost
            # nothing to show and paints blank until a scroll forces a
            # relayout. Deferring to idle measures after layout instead.
            def _apply():
                try:
                    self._queue_canvas.configure(
                        scrollregion=self._queue_canvas.bbox("all"))
                except Exception:
                    pass
            self._queue_canvas.after_idle(_apply)
        self._queue_listbox.bind("<Configure>", _on_inner_resize)

        # Stretch inner frame to match canvas width
        def _on_canvas_resize(event):
            self._queue_canvas.itemconfig(
                self._queue_canvas_window, width=event.width)
        self._queue_canvas.bind("<Configure>", _on_canvas_resize)

        # Mouse-wheel scrolling
        def _on_mousewheel(event):
            self._queue_canvas.yview_scroll(
                int(-1 * (event.delta / 120)), "units")
        self._queue_canvas.bind("<MouseWheel>", _on_mousewheel)
        self._queue_listbox.bind("<MouseWheel>", _on_mousewheel)

    def _enqueue_current_selection(self, vi_override=None, url_override=None):
        """Read the current Recommended tab selection and add it to the queue.
        vi_override/url_override: pass explicit snapshots to avoid reading stale
        self.current_video_info during batch re-fetch races."""
        selection = self.recommended_tree.selection()
        if not selection:
            self._notify_warning("Queue", "Please select a stream in the Recommended tab to queue.")
            return

        item = self.recommended_tree.item(selection[0])
        values = item['values']
        if not values:
            return

        quality    = values[0]
        video_info = values[1]
        audio_info = values[2]

        # Prefer the explicitly supplied snapshot (batch re-fetch path) so we
        # never read self.current_video_info which may already point to the next
        # batch video by the time a re-fetch callback fires.
        _vi_src = vi_override if vi_override is not None else (
            self.current_video_info if self.current_video_info else {})
        title = _vi_src.get('title', 'Unknown')
        channel_prefix = self.get_safe_channel_prefix(_vi_src)
        display_name = (channel_prefix + ' - ' + title) if channel_prefix else title
        label = display_name + '  [' + str(quality) + ']'

        # Snapshot URL, video_id, and video_info - use overrides when provided.
        url_snap      = url_override or getattr(self, 'current_video_url', None) or self.url_var.get().strip()
        video_id_snap = _vi_src.get('id', 'unknown')
        # Store only the fields actually used after enqueue time - the full
        # video_info dict can be 200-500KB per entry (formats, captions, thumbnails).
        # This keeps queue memory and JSON serialisation lean on large batches.
        _vi_keys_needed = ('id', 'title', 'uploader', 'channel', 'upload_date',
                           'thumbnail', 'thumbnails', 'duration', 'formats',
                           'subtitles', 'automatic_captions', 'webpage_url')
        vi_snap = {k: _vi_src[k] for k in _vi_keys_needed if k in _vi_src}

        # Build the worker call the same way download_recommended_selection does
        if "Direct:" in video_info:
            # Direct combined stream
            format_id = video_info.split('(')[1].split(')')[0] if '(' in video_info else ''
            if not format_id:
                self._notify_error("Queue", "Could not extract format ID from selection.")
                return
            target_fmt = next((f for f in self.current_formats
                               if str(f.get('format_id', '')) == format_id), None)
            ext = target_fmt.get('ext', 'mp4') if target_fmt else 'mp4'
            # Include subtitle suffix in filename at enqueue time, same as merge path.
            _dq_sub_src  = getattr(self, 'subtitle_source', 'off')
            _dq_sub_mode = getattr(self, 'subtitle_mode', 'S')
            _dq_sub_lang = getattr(self, 'subtitle_lang', 'en') or 'en'
            if _dq_sub_src == 'off' or _dq_sub_src == 'external':
                _dq_sub_suffix = ''
            elif _dq_sub_src == 'auto':
                _dq_sub_suffix = ' A' + _dq_sub_mode
            else:
                _dq_sub_suffix = ' ' + _dq_sub_mode
            _dq_lang = self.detect_audio_language(target_fmt) if target_fmt else 'unknown'
            _dq_lang_tag = (' ' + _dq_lang.upper()) if _dq_lang and _dq_lang != 'unknown' else ''
            _dq_bracket = str(quality).rstrip('p') + 'D' + _dq_lang_tag + _dq_sub_suffix
            filepath       = self._unique_output_path(os.path.join(self.download_path, self._assemble_filename(vi_snap, _dq_bracket, '.' + ext)), vi_snap.get('id'))
            _dq_sub_snap = (_dq_sub_src, _dq_sub_mode, _dq_sub_lang)
            if self.audio_only_mode.get():
                mp3_path = self._unique_output_path(os.path.join(self.download_path, self._assemble_filename(vi_snap, str(quality), '.mp3')), vi_snap.get('id'))
                worker   = self._download_audio_only_worker
                args     = (mp3_path, quality, url_snap, vi_snap)
            else:
                worker = self._download_direct_worker_with_terminal
                args   = (format_id, filepath, quality, url_snap, vi_snap,
                          _dq_sub_snap, video_id_snap)
        else:
            # Merge combination
            video_format_id = video_info.split('(')[1].split(')')[0] if '(' in video_info else ''
            audio_format_id = (audio_info.split('ID:')[1].split(' ')[0]
                               if 'ID:' in audio_info
                               else (audio_info.split('(')[1].split(')')[0] if '(' in audio_info else ''))
            if not video_format_id or not audio_format_id:
                self._notify_error("Queue", "Could not extract format IDs from selection.")
                return
            # Build output path (same logic as download_and_merge_combination)
            video_title    = vi_snap.get('title', 'video')
            safe_title     = self.sanitize_filename(video_title)
            audio_lang     = 'unknown'
            if '(' in audio_info and ')' in audio_info:
                lang_part = audio_info.split('(')[-1].split(')')[0]
                if len(lang_part) <= 3:
                    audio_lang = lang_part
            lang_tag       = audio_lang.upper() if audio_lang and audio_lang != 'unknown' else ''
            quality_tag    = (str(quality) + ' ' + lang_tag).strip()
            # Subtitle suffix baked into filename at enqueue time
            _q_sub_src_pre  = getattr(self, 'subtitle_source', 'off')
            _q_sub_mode_pre = getattr(self, 'subtitle_mode', 'S')
            if _q_sub_src_pre == 'off' or _q_sub_src_pre == 'external':
                _q_sub_suffix = ''
            elif _q_sub_src_pre == 'auto':
                _q_sub_suffix = ' A' + _q_sub_mode_pre
            else:
                _q_sub_suffix = ' ' + _q_sub_mode_pre
            output_path    = self._unique_output_path(os.path.join(self.download_path, self._assemble_filename(vi_snap, quality_tag + _q_sub_suffix, '.mp4')), vi_snap.get('id'))
            cached_video   = self.get_cached_video_path(video_id_snap, video_format_id)
            use_cache      = cached_video is not None
            # Snapshot subtitle settings at enqueue time so mid-queue UI
            # toggles cannot change what gets embedded or how the file is named.
            _q_sub_src  = _q_sub_src_pre
            _q_sub_mode = getattr(self, 'subtitle_mode', 'S')
            _q_sub_lang = (getattr(self, 'subtitle_lang', 'en') or 'en')
            _q_sub_snap = (_q_sub_src, _q_sub_mode, _q_sub_lang)
            if self.audio_only_mode.get():
                mp3_path = self._unique_output_path(os.path.join(self.download_path, self._assemble_filename(vi_snap, quality_tag, '.mp3')), vi_snap.get('id'))
                worker   = self._download_audio_only_worker
                args     = (mp3_path, quality, url_snap, vi_snap,
                            audio_format_id, video_id_snap)
            else:
                worker = self._download_and_merge_worker_with_terminal
                args   = (video_format_id, audio_format_id, output_path, quality,
                           use_cache, cached_video, None, url_snap, video_id_snap, vi_snap, _q_sub_snap)

        is_audio = (worker == self._download_audio_only_worker)
        merge_fn  = self._download_and_merge_worker_with_terminal.__func__
        direct_fn = self._download_direct_worker_with_terminal.__func__
        audio_fn  = self._download_audio_only_worker.__func__
        w_fn      = getattr(worker, '__func__', None)
        if w_fn is merge_fn:
            wname = 'merge'
        elif w_fn is direct_fn:
            wname = 'direct'
        elif w_fn is audio_fn:
            wname = 'audio'
        else:
            wname = 'unknown'
        # Build the output_tag string shown in the queue panel.
        # Rules mirror the filename suffix logic:
        #   source=off  → EN (no subtitle indicator)
        #   source=manual, mode=S   → EN S
        #   source=manual, mode=SD  → EN SD
        #   source=manual, mode=HS  → EN HS
        #   source=auto,   mode=S   → EN AS   (A prefix = auto-generated)
        #   source=auto,   mode=SD  → EN ASD
        #   source=auto,   mode=HS  → EN AHS
        #   source=external         → EN EXT
        _sub_src_for_tag  = getattr(self, 'subtitle_source', 'off')
        _sub_mode_for_tag = getattr(self, 'subtitle_mode', 'S')
        if is_audio:
            _output_tag = 'A'
        else:
            _lang_tag = (getattr(self, 'preferred_language', 'en') or 'en').upper()
            if _sub_src_for_tag == 'off':
                _output_tag = _lang_tag
            elif _sub_src_for_tag == 'external':
                _output_tag = _lang_tag + ' EXT'
            elif _sub_src_for_tag == 'auto':
                # Auto-generated subtitles get the A prefix
                _output_tag = _lang_tag + ' A' + _sub_mode_for_tag
            else:
                # Manual source - no A prefix
                _output_tag = _lang_tag + ' ' + _sub_mode_for_tag
        entry = {'worker': worker, 'worker_name': wname, 'args': args, 'label': label,
                 'is_audio': is_audio, 'url': url_snap, 'output_tag': _output_tag}
        with self._queue_lock:
            self._download_queue.append(entry)
            n = len(self._download_queue)
        # Incremental append - O(1) instead of O(N) full rebuild.
        # Reorders and removals still use _refresh_queue_panel.
        self._append_queue_row(entry)
        self.append_terminal_output(
            'Queued (#' + str(n) + '): ' + label + '\n', 'cache')
        self.status_var.set('Queued: ' + label + ' (#' + str(n) + ' in queue)')

        # Fire a pre-warm probe immediately so the CDN has the full wait time to
        # provision the stream. Runs in a daemon thread so it never blocks the UI.
        if self.prewarm_enabled:
            pw_url, pw_fids = self._get_prewarm_info(entry)
            if pw_url and pw_fids:
                threading.Thread(
                    target=self._prewarm_format,
                    args=(pw_url, pw_fids),
                    daemon=True).start()

        # If nothing is currently downloading, start the queue immediately.
        # If a download is active, _download_complete will drain the queue.
        # The root.after(100) is a safety net for the race where _download_complete
        # fires on the Tk thread between this check and the queue append - in that
        # case _download_active is already False here but _start_next_queued ran
        # before the entry existed.  The deferred call catches it 100 ms later.
        if not self._download_active and not self._download_paused:
            self._start_next_queued()
        else:
            self.root.after(100, lambda: (
                self._start_next_queued()
                if not self._download_active and not self._download_paused
                else None
            ))
            # A download is already running - kick the precache system so this
            # newly added item gets its streams downloaded in the background now
            # rather than waiting until it reaches the front of the queue.
            if self._download_active:
                threading.Thread(
                    target=self._precache_next_stream,
                    daemon=True).start()

    def _build_queue_row(self, parent, entry, idx, n_items):
        """Create and return one queue row Frame for the given entry/index.
        Extracted so both full-rebuild and incremental-append can share it."""
        _dm     = getattr(self, 'dark_mode', False)
        _row_bg = "#2b2b2b" if _dm else "SystemButtonFace"
        _dim_fg = "#888888" if _dm else "#666666"
        _rm_fg  = "#f44336" if _dm else "#cc2222"
        _arr_fg = "#aaaaaa" if _dm else "#555555"

        row = tk.Frame(parent, background=_row_bg, highlightthickness=0)
        row.pack(fill=tk.X, padx=4, pady=2)
        row.columnconfigure(2, weight=1)

        is_audio = entry.get('is_audio', False)

        pos_lbl = tk.Label(row, text='#' + str(idx + 1),
                           width=3, anchor='e',
                           background=_row_bg, foreground=_dim_fg,
                           font=('Consolas', 9))
        pos_lbl.grid(row=0, column=0, padx=(4, 2), pady=2)

        badge_text = entry.get('output_tag', 'A' if is_audio else 'EN')
        badge_fg   = '#ce93d8' if (_dm and is_audio) else (
                     '#9060a0' if is_audio else (
                     '#74b8d4' if _dm else '#2060a0'))
        badge_lbl  = tk.Label(row, text=badge_text,
                              background=_row_bg, foreground=badge_fg,
                              font=('Consolas', 8, 'bold'), anchor='w', width=8)
        badge_lbl.grid(row=0, column=1, padx=(0, 4), pady=2)

        def make_remove(i):
            def _remove():
                with self._queue_lock:
                    if 0 <= i < len(self._download_queue):
                        removed = self._download_queue.pop(i)
                    else:
                        return
                self._refresh_queue_panel()
                self.append_terminal_output(
                    'Removed from queue: ' + removed['label'] + '\n', 'warning')
            return _remove

        def make_move_up(i):
            def _move_up():
                with self._queue_lock:
                    if i > 0 and i < len(self._download_queue):
                        q = self._download_queue
                        q[i - 1], q[i] = q[i], q[i - 1]
                self._refresh_queue_panel()
            return _move_up

        def make_move_down(i):
            def _move_down():
                with self._queue_lock:
                    if i < len(self._download_queue) - 1:
                        q = self._download_queue
                        q[i], q[i + 1] = q[i + 1], q[i]
                self._refresh_queue_panel()
            return _move_down

        up_btn = tk.Button(row, text='▲', command=make_move_up(idx),
                           background=_row_bg, foreground=_arr_fg,
                           relief='flat', font=('Consolas', 8),
                           cursor='hand2', padx=2,
                           state='disabled' if idx == 0 else 'normal')
        up_btn.grid(row=0, column=3, padx=(0, 1), pady=2)

        dn_btn = tk.Button(row, text='▼', command=make_move_down(idx),
                           background=_row_bg, foreground=_arr_fg,
                           relief='flat', font=('Consolas', 8),
                           cursor='hand2', padx=2,
                           state='disabled' if idx == n_items - 1 else 'normal')
        dn_btn.grid(row=0, column=4, padx=(0, 1), pady=2)

        rm_btn = tk.Button(row, text='✕', command=make_remove(idx),
                           background=_row_bg, foreground=_rm_fg,
                           relief='flat', font=('Consolas', 9),
                           cursor='hand2', padx=4)
        rm_btn.grid(row=0, column=5, padx=(0, 4), pady=2)

        title_fg = ('#ce93d8' if is_audio else '#d4d4d4') if _dm else (
                    '#7040a0' if is_audio else 'black')
        name_lbl = tk.Label(row, text=entry['label'],
                            anchor='w',
                            justify=tk.LEFT,
                            wraplength=1,
                            background=_row_bg, foreground=title_fg,
                            font=('Consolas', 9))
        name_lbl.grid(row=0, column=2, sticky='ew', padx=(0, 6), pady=2)

        def _update_wrap(event, lbl=name_lbl):
            lbl.config(wraplength=max(1, event.width - 4))
        name_lbl.bind('<Configure>', _update_wrap)
        return row

    def _append_queue_row(self, entry):
        """Append a single new row for `entry` without rebuilding the panel.
        Called at enqueue time - avoids the O(N²) full-rebuild cost.

        The previous last row's ▼ button must be re-enabled, and position
        labels on ALL rows must stay correct, so we update them in-place
        rather than rebuilding.  Reorders and deletions still use the full
        _refresh_queue_panel rebuild since they change all indices anyway.
        """
        with self._queue_lock:
            queue_snapshot = list(self._download_queue)
        n = len(queue_snapshot)
        if n == 0:
            return

        # Show the frame if it was hidden (was empty before)
        self._queue_frame.grid()

        # Re-enable ▼ on the previously-last row if there is one
        children = self._queue_listbox.winfo_children()
        if len(children) >= 1:
            prev_last = children[-1]
            # dn_btn is in column 4 of the row frame
            for w in prev_last.winfo_children():
                gi = w.grid_info()
                if gi.get('column') == 4:
                    w.config(state='normal')
                    break

        # Update position labels on all existing rows to stay accurate
        # (they are already correct because we only append - index = count)
        # Just build the new row at index n-1
        self._build_queue_row(self._queue_listbox, entry, n - 1, n)

        # Scroll to show the new row
        self._queue_canvas.yview_moveto(1.0)

    def _refresh_queue_panel(self):
        """Full rebuild of the queue panel - used for reorders and deletions."""
        for widget in self._queue_listbox.winfo_children():
            widget.destroy()

        with self._queue_lock:
            queue_snapshot = list(self._download_queue)

        if not queue_snapshot:
            self._queue_frame.grid_remove()
            return

        self._queue_frame.grid()

        for idx, entry in enumerate(queue_snapshot):
            self._build_queue_row(self._queue_listbox, entry, idx,
                                  len(queue_snapshot))

        # Scroll to top so the first queued item is always visible after
        # a reorder or deletion.
        self._queue_canvas.yview_moveto(0)


    def _start_next_queued(self):
        """Pop and start the next entry from the queue, if any.

        Must only be called from the main (Tk) thread so that the
        _download_active check-and-set is effectively atomic - Tk processes
        events serially so no two calls can interleave here."""
        if not self._download_queue:
            return
        # Do not start if user has paused (let them Resume first)
        if self._download_paused:
            return
        # Safety guard: if a download is already running (e.g. two _download_complete
        # callbacks queued back-to-back via root.after), do not start another one.
        if self._download_active:
            return

        with self._queue_lock:
            if not self._download_queue:
                return
            entry = self._download_queue.pop(0)
            next_entry = self._download_queue[0] if (self.prewarm_enabled and self._download_queue) else None
        self._currently_downloading_url = entry.get('url', '')
        self._refresh_queue_panel()
        self.append_terminal_output(
            '\nStarting queued download: ' + entry['label'] + '\n', 'cache')
        self._download_stopped = False
        self._download_active = True   # Mark busy before thread starts to close race window
        self._record_attempt(entry.get('url') or '', entry.get('video_info'))
        self._reset_download_buttons()

        # If there is a next item in the queue, fire a background pre-warm probe now
        # so YouTube's CDN has the full download duration to warm up that stream.
        if next_entry is not None:
            pw_url, pw_fids = self._get_prewarm_info(next_entry)
            if pw_url and pw_fids:
                self.append_terminal_output(
                    'Pre-warming stream for: ' + next_entry['label'] + '\n', 'cache')
                pw_thread = threading.Thread(
                    target=self._prewarm_format,
                    args=(pw_url, pw_fids),
                    daemon=True)
                pw_thread.start()

        # Pre-cache streams for the next N queued items in the background while
        # this download runs.  Runs unconditionally so queued items are always
        # ready when their turn comes.
        threading.Thread(
            target=self._precache_next_stream,
            daemon=True).start()

        thread = threading.Thread(target=entry['worker'], args=entry['args'])
        thread.daemon = True
        thread.start()

    def _download_complete(self, file_path, operation, download_time):
        """Handle download completion"""
        # Record download in history - read and clear the meta dict set by the
        # worker thread before it scheduled this call.
        _hist_meta = getattr(self, '_pending_history_meta', None)
        self._pending_history_meta = None
        self._clear_cache_inuse()
        # A sustained run (playlist, deep queue) almost always has a yt-dlp
        # alive, so the reap on copy-creation never fires and copies pile up.
        # A finished download is the most likely idle moment there is; the
        # process guard still decides whether anything is actually removed.
        try:
            threading.Thread(target=self._reap_cookie_copies,
                             kwargs={'threshold': 40}, daemon=True).start()
        except Exception:
            pass
        try:
            _ev_info = (_hist_meta or {}).get('video_info') or {}
            self._emit_dev_event(
                'complete',
                video_id=(_ev_info.get('id') if _ev_info else None),
                title=(_ev_info.get('title') if _ev_info else None),
                path=file_path,
                operation=operation,
                seconds=round(float(download_time or 0), 2),
                size=(os.path.getsize(file_path)
                      if file_path and os.path.exists(file_path) else 0))
        except Exception:
            pass
        try:
            _h_url  = (_hist_meta or {}).get('url', '') or self._currently_downloading_url or ''
            _h_info = (_hist_meta or {}).get('video_info') or {}
            _h_qual = (_hist_meta or {}).get('quality', '') or ''
            self._record_download(file_path, _h_url, _h_info, _h_qual, download_time)
        except Exception:
            pass  # never let history recording block the queue

        # Keep _download_active = True here so any stray root.after callback
        # that fires during the recommendations refresh cannot start a second
        # download. We clear it immediately before _start_next_queued which
        # has its own guard.
        # Format download time
        if download_time < 60:
            time_str = f"{download_time:.1f} seconds"
        elif download_time < 3600:
            minutes = int(download_time // 60)
            seconds = int(download_time % 60)
            time_str = f"{minutes}m {seconds}s"
        else:
            hours = int(download_time // 3600)
            minutes = int((download_time % 3600) // 60)
            time_str = f"{hours}h {minutes}m"
        
        # Get file size
        try:
            file_size = os.path.getsize(file_path)
            size_str = self.format_file_size(file_size)
        except OSError:
            size_str = "Unknown size"
        
        # Update status
        filename = os.path.basename(file_path)
        completion_message = f"{operation} completed in {time_str}"
        self.status_var.set(completion_message)
        self.progress_var.set("Ready")
        
        # Update download status
        download_status = f"✅ {filename} - {size_str} - {time_str}"
        self.download_status_var.set(download_status)
        
        # Refresh recommendations to update cache indicators.
        # Wrapped in try/except so an exception here never prevents
        # _download_active from being cleared and the queue from continuing.
        try:
            if self.current_formats:
                self._populate_recommended_combinations(suppress_auto_download=True)
        except Exception:
            pass

        # Flush cache metadata to disk and evict if needed - deferred to here
        # so it never runs mid-download and never slows the download thread.
        self.root.after(500, self._post_download_cache_maintenance)

        # Clear active flag then start next queued download if any.
        # Always runs - even if the recommendations refresh above threw.
        self._download_active = False
        self._currently_downloading_url = ''
        self._resume_target = None
        self._resume_args = ()
        self._update_subtitle_combo_states()
        self._start_next_queued()
    
    def _show_error_toast(self, title, message):
        """Show a centered, click-to-dismiss error overlay.
        Appears centered on the main window, requires no OK button -
        clicking anywhere on it dismisses it."""
        try:
            toast = tk.Toplevel(self.root)
            toast.title(title)
            toast.resizable(False, False)
            toast.transient(self.root)
            toast.grab_set()

            # Center on main window
            self.root.update_idletasks()
            rw = self.root.winfo_width()
            rh = self.root.winfo_height()
            rx = self.root.winfo_rootx()
            ry = self.root.winfo_rooty()
            tw, th = 420, 160
            tx = rx + (rw - tw) // 2
            ty = ry + (rh - th) // 2
            toast.geometry(f'{tw}x{th}+{tx}+{ty}')

            # Content
            _dm = getattr(self, 'dark_mode', False)
            _bg = '#2b2b2b' if _dm else '#fff0f0'
            _fg = '#ff8080' if _dm else '#cc0000'
            _body_fg = '#eeeeee' if _dm else '#333333'
            toast.configure(bg=_bg)

            tk.Label(toast, text='\u26a0 ' + title, font=('Arial', 11, 'bold'),
                     fg=_fg, bg=_bg).pack(pady=(14, 4))
            tk.Label(toast, text=message, font=('Arial', 9),
                     fg=_body_fg, bg=_bg, wraplength=380, justify='center').pack(
                padx=16, pady=(0, 8))
            tk.Label(toast, text='Click anywhere to dismiss',
                     font=('Arial', 8), fg='gray', bg=_bg).pack(pady=(0, 10))

            toast.bind('<Button-1>', lambda e: toast.destroy())
            toast.bind('<Escape>', lambda e: toast.destroy())
            toast.focus_set()
        except Exception:
            # Fallback to standard messagebox if Toplevel creation fails
            self._notify_error(title, message)

    def _download_error(self, error_message):
        """Handle download error"""
        self._download_active = False
        self._currently_downloading_url = ''
        self._resume_target = None
        self._resume_args = ()
        self._update_subtitle_combo_states()
        self.status_var.set("Download failed")
        self.progress_var.set("Ready")
        self.download_status_var.set("❌ Download failed")
        self._show_error_toast("Download Error", error_message)
        # Still try next queued item after an error
        self._start_next_queued()
    
    # Translation table built once at class level - faster than a replace loop
    _FILENAME_STRIP = str.maketrans('', '', '<>:"/\\|?*')
    # Normalise common Unicode typography to ASCII equivalents.
    # Curly single quotes -> straight apostrophe, curly double quotes -> "
    # (double quotes are then removed by _FILENAME_STRIP).
    # En/em dashes -> hyphen, ellipsis -> three dots.
    _FILENAME_UNICODE_NORM = str.maketrans({
        '\u2018': "'", '\u2019': "'",   # left/right single curly quotes
        '\u201C': '"', '\u201D': '"',   # left/right double curly quotes
        '\u2013': '-', '\u2014': '-',   # en-dash, em-dash
        '\u2026': '...',                # ellipsis
        '\u00A0': ' ',                  # non-breaking space
    })

    def sanitize_filename(self, filename):
        """Sanitize filename for filesystem - removes invalid chars entirely."""
        filename = filename.translate(self._FILENAME_UNICODE_NORM)
        filename = filename.translate(self._FILENAME_STRIP)
        # Collapse any double spaces left by removals
        while '  ' in filename:
            filename = filename.replace('  ', ' ')
        filename = filename.strip()
        # Windows rejects trailing dots/spaces and reserved device names
        # (CON, NUL, COM1...) even when an extension is appended.
        filename = filename.rstrip('. ')
        _reserved = {'CON', 'PRN', 'AUX', 'NUL',
                     'COM1', 'COM2', 'COM3', 'COM4', 'COM5', 'COM6', 'COM7',
                     'COM8', 'COM9', 'LPT1', 'LPT2', 'LPT3', 'LPT4', 'LPT5',
                     'LPT6', 'LPT7', 'LPT8', 'LPT9'}
        if filename.upper() in _reserved:
            filename = '_' + filename
        return filename[:100] if len(filename) > 100 else filename

    def get_safe_channel_prefix(self, video_info_dict=None):
        """Return sanitized channel display name for filename prefix.
        Uses uploader (display name) with fallback to channel then empty string.
        Pass video_info_dict to derive from a specific snapshot rather than
        self.current_video_info (which changes as the UI loads new videos)."""
        info = video_info_dict if video_info_dict is not None else self.current_video_info
        channel = (info.get('uploader') or info.get('channel') or '')
        if not channel.strip():
            return ''
        return self.sanitize_filename(channel.strip())

    def _build_output_base_name(self, video_info_dict, channel_prefix=None):
        """Return the base filename stem (no extension, no quality tag).
        Use _assemble_filename() to get the full name with bracket tag at correct position."""
        if channel_prefix is None:
            channel_prefix = self.get_safe_channel_prefix(video_info_dict)
        title = self.sanitize_filename(video_info_dict.get('title', 'video'))
        raw_date = video_info_dict.get('upload_date', '')
        upload_str = ''
        if raw_date and len(str(raw_date)) == 8:
            r = str(raw_date)
            upload_str = 'U' + r[:4] + '-' + r[4:6] + '-' + r[6:8]
        fmt = self._normalise_filename_format()
        _vid_id_base = (video_info_dict.get('id') or '').strip()
        _slot_map = {
            'Channel': channel_prefix,
            'Title': title,
            'Upload Date': upload_str,
            'Download Date': 'D' + time.strftime('%Y-%m-%d'),
            'Video ID': _vid_id_base,
            'Duration': self._format_duration_tag(video_info_dict.get('duration')),
            'Queue Index': '#' + str(self._session_download_counter).zfill(2),
        }
        parts = []
        for slot in fmt.split('|'):
            slot = slot.strip()
            if slot in ('(none)', '', 'Quality Tag'):
                continue
            val = _slot_map.get(slot)
            if val:
                parts.append(val)
        return ' - '.join(parts) if parts else title

    def _normalise_filename_format(self):
        """Return filename_format as a normalised pipe-separated string."""
        fmt = getattr(self, 'filename_format', 'Channel|Title|Upload Date|Quality Tag') or 'Channel|Title|Upload Date|Quality Tag'
        if '|' not in fmt:
            if fmt == 'channel - title' and getattr(self, 'filename_include_date', False):
                return 'Upload Date|Channel|Title|Quality Tag'
            _legacy = {
                'channel - title':        'Channel|Title|Quality Tag',
                'title - channel':        'Title|Channel',
                'channel - date - title': 'Channel|Upload Date|Title',
                'date - channel - title': 'Upload Date|Channel|Title',
                'date - title - channel': 'Upload Date|Title|Channel',
                'title':                  'Title',
                'date - title':           'Upload Date|Title',
            }
            return _legacy.get(fmt, 'Channel|Title|Upload Date')
        # Migrate legacy 'Date' → 'Upload Date' per-token (avoids corrupting
        # 'Upload Date' or 'Download Date' which already contain 'Date').
        parts = fmt.split('|')
        parts = [('Upload Date' if p.strip() == 'Date' else p) for p in parts]
        return '|'.join(parts)

    def _assemble_filename(self, video_info_dict, bracket_tag, ext, channel_prefix=None):
        """Assemble full filename respecting Quality Tag slot position.
        bracket_tag: content without brackets e.g. '1080p EN S'
        ext: with dot e.g. '.mp4'
        The Video ID slot (if selected by the user) provides a stable unique
        identifier so two videos with identical titles remain distinguishable.
        If Video ID is not in the format, filenames fall back to _unique_output_path
        collision resolution."""
        if channel_prefix is None:
            channel_prefix = self.get_safe_channel_prefix(video_info_dict)
        title = self.sanitize_filename(video_info_dict.get('title', 'video'))
        raw_date = video_info_dict.get('upload_date', '')
        upload_str = ''
        if raw_date and len(str(raw_date)) == 8:
            r = str(raw_date)
            upload_str = 'U' + r[:4] + '-' + r[4:6] + '-' + r[6:8]
        _vid_id = (video_info_dict.get('id') or '').strip()
        fmt = self._normalise_filename_format()
        tag_str = '[' + bracket_tag + ']'
        _slot_map = {
            'Channel':       channel_prefix,
            'Title':         title,
            'Upload Date':   upload_str,
            'Download Date': 'D' + time.strftime('%Y-%m-%d'),
            'Quality Tag':   tag_str,
            'Video ID':      _vid_id,
            'Duration':      self._format_duration_tag(video_info_dict.get('duration')),
            'Queue Index':   '#' + str(self._session_download_counter).zfill(2),
        }
        # Build parts in slot order
        slots_ordered = [s.strip() for s in fmt.split('|') if s.strip() not in ('(none)', '')]
        # Title is always included - inject it at the end if the user omitted it.
        if 'Title' not in slots_ordered:
            slots_ordered = slots_ordered + ['Title']
        parts = []
        for slot in slots_ordered:
            val = _slot_map.get(slot)
            if val:
                parts.append(val)
        if not parts:
            return title + ext
        stem = ' - '.join(parts)
        # Cap total stem length to 180 chars so the full path (stem + bracket +
        # extension + directory) stays well under Windows MAX_PATH (260 chars).
        if len(stem) > 180:
            stem = stem[:177] + '...'
        return stem + ext

    def _format_duration_tag(self, duration_seconds):
        """Format a duration in seconds to a compact filename-safe tag.
        Under 1 min: '5s', '47s'
        1-59 min: '3m24s', '12m05s'
        1 hr+: '1h12m', '2h03m'
        Returns '' if duration is unavailable."""
        try:
            secs = int(float(duration_seconds or 0))
        except (ValueError, TypeError):
            return ''
        if secs <= 0:
            return ''
        if secs < 60:
            return str(secs) + 's'
        m, s = divmod(secs, 60)
        if m < 60:
            return str(m) + 'm' + str(s).zfill(2) + 's'
        h, m = divmod(m, 60)
        return str(h) + 'h' + str(m).zfill(2) + 'm'

    @staticmethod
    def _parse_time_to_hhmmss(text):
        """Convert a user-supplied time string to 'HH:MM:SS.ss'.

        Output always carries hundredths so the precision is visible and
        round-trips without silently losing it - yt-dlp
        --download-sections and FFmpeg -ss / -to both accept fractional
        seconds. Accepts:
          '90'          -> '00:01:30.00'
          '90.5'        -> '00:01:30.50'
          '1:30'        -> '00:01:30.00'
          '1:30.25'     -> '00:01:30.25'
          '1:30:00'     -> '01:30:00.00'
          '1:30:00.125' -> '01:30:00.12'   (ties round to even)
          '0:01.15'     -> '00:00:01.15'
        Returns None if the string cannot be parsed.
        """
        text = (text or '').strip()
        if not text:
            return None
        parts = text.split(':')
        try:
            if len(parts) == 1:
                total = float(parts[0])
                h = int(total // 3600)
                rem = total - h * 3600
                m = int(rem // 60)
                s = rem - m * 60
            elif len(parts) == 2:
                h = 0
                m = int(parts[0])
                s = float(parts[1])
            elif len(parts) == 3:
                h = int(parts[0])
                m = int(parts[1])
                s = float(parts[2])
            else:
                return None
            if m >= 60 or s >= 60 or h < 0 or m < 0 or s < 0:
                return None
            hh = str(h).zfill(2)
            mm = str(m).zfill(2)
            ss = '{:05.2f}'.format(s)
            # 59.999 rounds to '60.00' - carry it rather than emit a bad time
            if ss.startswith('60'):
                ss = '00.00'
                m += 1
                if m >= 60:
                    m -= 60
                    h += 1
                hh = str(h).zfill(2)
                mm = str(m).zfill(2)
            return hh + ':' + mm + ':' + ss
        except (ValueError, TypeError):
            return None

    def _hardsub_input_args(self):
        """Input-side argv for a burn: hardware decode with hardware encode.

        '-hwaccel auto' asks FFmpeg for the best available hardware
        decoder and silently falls back to software when none fits. The
        AV1 sources this app caches (itag 398/399) decode brutally
        slowly on the CPU, which capped batch 1b's gains - the encode
        moved to hardware while the decode leg stayed throttled. Rides
        the same switch as the encoder: forced or demoted libx264 means
        a FULLY software pipeline, so the direct path's failure retry
        rebuilds with no hwaccel either.
        """
        if getattr(self, 'hardsub_encoder', 'libx264') == 'libx264':
            return []
        if self._pick_hardsub_encoder() == 'libx264':
            return []
        return ['-hwaccel', 'auto']

    def _hardsub_codec_args(self, stream_spec='-c:v'):
        """Video-codec argv slice for a subtitle burn (batch 1b).

        'auto' (default) uses the probed hardware encoder; setting the
        config key hardsub_encoder to 'auto' opts in to hardware - the
        hand-editable escape hatch until the Settings row lands in 1c.
        Quality mappings target libx264-crf-23-class output: QSV ICQ
        global_quality 23, NVENC constqp qp 23 preset p4, AMF CQP 23
        balanced. Logs one line per burn naming the encoder so field
        logs always show which path produced a file.
        """
        _pref = getattr(self, 'hardsub_encoder', 'libx264')
        enc = 'libx264' if _pref == 'libx264' else self._pick_hardsub_encoder()
        if enc == 'h264_qsv':
            args = [stream_spec, 'h264_qsv', '-global_quality', '23',
                    '-preset', 'veryfast']
        elif enc == 'h264_nvenc':
            args = [stream_spec, 'h264_nvenc', '-rc', 'constqp',
                    '-qp', '23', '-preset', 'p4']
        elif enc == 'h264_amf':
            args = [stream_spec, 'h264_amf', '-quality', 'balanced',
                    '-rc', 'cqp', '-qp_i', '23', '-qp_p', '23']
        else:
            args = [stream_spec, 'libx264', '-crf', '23',
                    '-preset', 'veryfast']
        self.append_terminal_output(
            'Hardsub: encoding with ' + args[1] + '.\n', 'info')
        return args

    def _hardsub_demote(self, where, rc):
        """Hardware burn failed on a real input the probe's synthetic
        test did not predict: pin this session to libx264 and say so.
        No-op when already on software, so a plain libx264 failure
        keeps today's behaviour byte-for-byte."""
        if getattr(self, '_hardsub_encoder', None) in (None, 'libx264'):
            return
        self._hardsub_encoder = 'libx264'
        self.append_terminal_output(
            'Hardsub: hardware encode failed in ' + where + ' (rc='
            + str(rc) + ') - falling back to libx264 for this session.\n',
            'warning')

    def _pick_hardsub_encoder(self):
        """Best WORKING H.264 encoder for subtitle burn-in, probed once.

        Batch 1b: the choice feeds _hardsub_codec_args() for BOTH burn
        paths. If a hardware encode fails on a real input the synthetic
        test did not predict, _hardsub_demote() pins this session back
        to libx264 (the direct path also retries that burn once).

        'ffmpeg -encoders' advertises what was COMPILED in, not what can
        initialise on this machine (a CPU-only box still lists nvenc),
        so each advertised candidate must pass a tiny null-sink test
        encode before it is trusted. Preference order NVENC > QSV > AMF
        per current benchmarks. Any failure anywhere means libx264 -
        never an error. parallel_hardsub means workers can race here;
        double-checked lock so the probe runs once per session.
        """
        got = getattr(self, '_hardsub_encoder', None)
        if got:
            return got
        with self._hardsub_probe_lock:
            got = getattr(self, '_hardsub_encoder', None)
            if got:
                return got
            choice = 'libx264'
            try:
                if self.ffmpeg_path:
                    r = subprocess.run(
                        [self.ffmpeg_path, '-hide_banner', '-encoders'],
                        capture_output=True, text=True, encoding='utf-8',
                        errors='replace', timeout=10,
                        creationflags=CREATE_NO_WINDOW)
                    _adv = r.stdout or ''
                    for _cand in ('h264_nvenc', 'h264_qsv', 'h264_amf'):
                        if _cand not in _adv:
                            continue
                        t = subprocess.run(
                            [self.ffmpeg_path, '-hide_banner',
                             '-loglevel', 'error', '-f', 'lavfi', '-i',
                             'testsrc2=duration=0.2:size=256x144:rate=10',
                             '-frames:v', '3', '-c:v', _cand,
                             '-f', 'null', '-'],
                            capture_output=True, text=True, encoding='utf-8',
                            errors='replace', timeout=20,
                            creationflags=CREATE_NO_WINDOW)
                        if t.returncode == 0:
                            choice = _cand
                            break
            except Exception:
                choice = 'libx264'
            self._hardsub_encoder = choice
            if choice == 'libx264':
                self.append_terminal_output(
                    'Hardsub encoder probe: libx264 - software (no working'
                    ' hardware encoder found).\n', 'info')
            else:
                self.append_terminal_output(
                    'Hardsub encoder probe: ' + choice + ' - HARDWARE'
                    ' encoder selected for burn-in.\n', 'info')
            return choice

    def _unique_output_path(self, preferred_path, video_id=None):
        """Return preferred_path if it does not exist on disk, otherwise append
        a numeric suffix (2), (3), … up to a hard cap of 9999 to avoid
        overwriting an existing file.

        The video_id parameter is accepted for call-site compatibility but is
        no longer used for suffix generation - Video ID can be embedded directly
        in filenames via the filename slot system in Settings instead.

        Hard cap of 9999 prevents an infinite loop on unusually full directories
        or when os.path.exists behaves unexpectedly (network drives, permissions)."""
        if not os.path.exists(preferred_path):
            return preferred_path
        base, ext = os.path.splitext(preferred_path)
        for n in range(2, 10000):
            candidate = base + ' (' + str(n) + ')' + ext
            if not os.path.exists(candidate):
                return candidate
        # Extremely unlikely - fall back to a 6-digit timestamp suffix
        ts = str(int(time.time()))[-6:]
        return base + ' (' + ts + ')' + ext


    def on_recommended_double_click(self, event):
        """Double-click a Recommended row: summarise it, then merge.

        The row's details go to the terminal instead of a modal dialog, and
        the download starts - which is what a double-click reads as. The
        full details dialog is still available on right-click.

        Guarded: no selection does nothing; an already-running download or a
        disabled Merge button reports why rather than starting a second job.
        """
        tree = self.recommended_tree
        sel = tree.selection()
        if not sel:
            return
        try:
            vals = tree.item(sel[0]).get('values') or []
            if vals:
                self.append_terminal_output(
                    'Selected: ' + ' | '.join(str(v) for v in vals[:4]) + '\n',
                    'info')
        except Exception:
            pass
        if getattr(self, '_download_active', False):
            self.append_terminal_output(
                'A download is already running - double-click ignored.\n', 'info')
            return
        try:
            if str(self.download_merge_btn['state']) == 'disabled':
                self.append_terminal_output(
                    'Nothing to merge yet - analyse a video first.\n', 'info')
                return
        except Exception:
            pass
        self.download_and_merge()

    def show_combination_details(self, event):
        """Show details about selected combination with caching info"""
        tree = self.recommended_tree
        selection = tree.selection()
        if not selection:
            return
        
        item = tree.item(selection[0])
        values = item['values']
        
        if not values:
            return
        
        quality = values[0]
        video_info = values[1] 
        audio_info = values[2]
        cache_status = values[4]  # Instructions/Cache Status column
        
        # Create details dialog
        dialog = tk.Toplevel(self.root)
        dialog.title(f"Download Instructions - {quality}")
        dialog.geometry("650x550")
        dialog.transient(self.root)
        dialog.grab_set()
        
        # Title
        ttk.Label(dialog, text=f"How to Download {quality} Quality", 
                 font=('Arial', 12, 'bold')).pack(pady=10)
        
        # Instructions text
        instructions_text = scrolledtext.ScrolledText(dialog, height=18, wrap=tk.WORD)
        instructions_text.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        
        # Check if this is a cached combination
        is_cached = "🗂️" in cache_status or "cached" in cache_status.lower()
        
        if "Direct:" in video_info:
            # Direct download instructions
            detail_text = f"""✅ DIRECT DOWNLOAD - {quality}

This is a combined video+audio file that's ready to use!

Video Format: {video_info}
Audio: {audio_info}

DOWNLOAD METHODS:

Method 1: Using yt-dlp.exe (Command Line)
yt-dlp.exe -f "{video_info.split('(')[1].split(')')[0]}" "YOUR_YOUTUBE_URL"

Method 2: Using Stream URL
1. Double-click this row to get the direct stream URL
2. Use any download manager (IDM, wget, etc.)
3. The file is ready to play immediately

Method 3: Browser Download
1. Get the stream URL
2. Open it in your browser
3. Right-click → Save As

✅ No merging required - file is ready to use!"""
        else:
            # Combination download instructions
            video_format_id = video_info.split('(')[1].split(')')[0] if '(' in video_info else ''
            audio_format_id = audio_info.split('ID:')[1].split(' ')[0] if 'ID:' in audio_info else audio_info.split('(')[1].split(')')[0] if '(' in audio_info else ''
            
            cache_info = ""
            if is_cached:
                cache_info = f"""
🗂️ CACHE OPTIMIZATION:
The video stream for {quality} is already cached from a previous download!
Only the audio stream needs to be downloaded, making this much faster.

"""
            
            detail_text = f"""🔧 COMBINATION DOWNLOAD - {quality}

For {quality} quality, you need to download video and audio separately, then merge them.

Video Stream: {video_info}
Audio Stream: {audio_info}
Cache Status: {cache_status}

{cache_info}DOWNLOAD METHODS:

Method 1: yt-dlp.exe (Automatic Merging) ⭐ RECOMMENDED
yt-dlp.exe -f "{video_format_id}+{audio_format_id}" "YOUR_YOUTUBE_URL"
(This downloads both and merges automatically)

Method 2: Manual Download + Merge
Step 1: Download video stream (format {video_format_id})
yt-dlp.exe -f {video_format_id} "YOUR_YOUTUBE_URL"
Step 2: Download audio stream (format {audio_format_id})
yt-dlp.exe -f {audio_format_id} "YOUR_YOUTUBE_URL"  
Step 3: Merge with ffmpeg:
ffmpeg -i video.mp4 -i audio.m4a -c copy output.mp4

Method 3: Using this GUI ⚡ FASTEST FOR MULTI-LANGUAGE
1. Click "Download & Merge" button below
2. The program will automatically use cached video if available
3. Only downloads what's needed (video cached = audio only)

MERGER TOOLS:
- ffmpeg (command line)
- Handbrake (GUI)
- VLC Media Player (Convert/Save)
- Online video mergers

💡 Why separate streams?
YouTube uses DASH streaming for high quality videos (720p+), which separates 
video and audio to save bandwidth.

🗂️ Why caching helps?
Once you download a video quality (e.g., 1080p), it's cached locally. 
If you want the same video in a different language, only the new audio 
is downloaded and merged with the cached video - much faster!

EXECUTABLE NOTES:
This version uses yt-dlp.exe binary for maximum compatibility and portability."""
        
        instructions_text.insert('1.0', detail_text)
        instructions_text.config(state='disabled')
        
        # Buttons
        btn_frame = ttk.Frame(dialog)
        btn_frame.pack(pady=10)
        
        def copy_instructions():
            self.root.clipboard_clear()
            self.root.clipboard_append(detail_text)
            self._notify_info("Copied", "Instructions copied to clipboard!")
        
        ttk.Button(btn_frame, text="Copy Instructions", command=copy_instructions).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Close", command=dialog.destroy).pack(side=tk.LEFT, padx=5)

    def _download_audio_only_worker(self, output_path, quality, url=None, video_info=None,
                                    audio_format_id=None, video_id=None,
                                    resume_temp_dir=None):
        """Download audio in one of three formats controlled by self.audio_only_format:

        'm4a_native' - Download whatever stream select_best_audio_stream chose.
            AAC: embed metadata/thumbnail normally. Opus: save as-is, skip embedding.

        'm4a_aac'   - Target AAC streams only. Bitrate preference honoured within
            the AAC pool (139/140/141). Silent fallback to Opus+transcode if no AAC.

        'mp3'       - Unchanged from original behaviour.

        All paths follow the merge worker pattern:
          1. All work happens in a temp directory
          2. _set_file_timestamps applied to the temp file
          3. File moved atomically to output folder as the very last step
        This ensures Explorer never sees a partial file and the file appears
        in the folder already complete - no re-sort mid-download.
        """
        fmt = getattr(self, 'audio_only_format', 'm4a_native')
        use_native = fmt == 'm4a_native'
        use_aac    = fmt == 'm4a_aac'
        use_mp3    = fmt == 'mp3'

        max_retries = 5
        if url is None:
            url = self.url_var.get().strip()
        if video_info is None:
            video_info = dict(self.current_video_info)
        # M5 fix: create/reuse the temp dir ONCE, outside the retry loop,
        # so partial files survive pause/resume and retry attempts (paired
        # with -c below). Mirrors the merge worker's resume_temp_dir pattern.
        if resume_temp_dir and os.path.isdir(resume_temp_dir):
            temp_dir = resume_temp_dir
            self.append_terminal_output(
                'Reusing temp dir from paused download: '
                + os.path.basename(temp_dir) + '\n', 'cache')
        else:
            temp_dir = self._make_temp_dir('ysa_audio_')

        # FFmpeg transcode timeout scaled to source duration: the fixed 300s
        # died repeatedly on a 10-hour Opus->AAC conversion in the field.
        # ~0.5x realtime is a generous ceiling for single-threaded AAC.
        try:
            _dur = int((video_info or {}).get('duration') or 0)
        except Exception:
            _dur = 0
        _conv_to = max(600, min(int(_dur * 0.5), 7200)) if _dur else 900

        # Output bitrate for any transcode, per the user's policy.
        _src_abr = self._audio_source_abr(video_info, audio_format_id)
        _tgt_abr = self._audio_output_bitrate(_src_abr)
        _abr_arg = (str(_tgt_abr) + 'k') if _tgt_abr else '128k'
        _mp3_q   = _abr_arg if _tgt_abr else '0'
        _mp3_enc = ['-b:a', _abr_arg] if _tgt_abr else ['-q:a', '0']

        # ── Clip snapshot (Audio Only) ─────────────────────────────────────
        # Same validation as the video workers; the range is applied via
        # yt-dlp --download-sections so ONLY the slice is downloaded - a
        # 3-minute clip of a 10-hour source fetches megabytes, not 500 MB.
        _m_on   = bool(getattr(self, '_m_clip_on', False))
        _cs_raw = getattr(self, '_m_clip_start', '') or ''
        _ce_raw = getattr(self, '_m_clip_end', '') or ''
        try:
            _clip_start_hms = self._parse_time_to_hhmmss(_cs_raw) if _m_on else None
            _clip_end_hms   = self._parse_time_to_hhmmss(_ce_raw) if _m_on else None
        except Exception:
            _clip_start_hms = _clip_end_hms = None
        def _a_hms2sec(t):
            if not t:
                return 0.0
            p = str(t).split(':')
            try:
                return int(p[0]) * 3600 + int(p[1]) * 60 + float(p[2])
            except Exception:
                return 0.0
        _clip_active = bool(_m_on and _clip_start_hms and _clip_end_hms
                            and _a_hms2sec(_clip_end_hms) > _a_hms2sec(_clip_start_hms))
        _clip_section_args = (
            ['--download-sections', '*' + str(_clip_start_hms) + '-' + str(_clip_end_hms)]
            if _clip_active else [])
        self._resume_target = self._download_audio_only_worker
        self._resume_args   = (output_path, quality, url, video_info,
                                audio_format_id, video_id, temp_dir)
        _last_exc_str = ''
        self._pending_history_meta = {'url': url, 'video_info': video_info, 'quality': quality}

        for attempt in range(max_retries):
            try:
                if attempt == 0:
                    self.download_start_time = time.time()
                    self._session_download_counter += 1
                if attempt > 0:
                    is_format_err = 'Requested format is not available' in _last_exc_str
                    is_state_err  = is_format_err or ('HTTP Error 416' in _last_exc_str)
                    wait_secs = 0 if is_state_err else min(5 * attempt, 30)
                    retry_note = 'retrying immediately' if is_state_err else (
                        'resuming in ' + str(wait_secs) + 's')
                    self.append_terminal_output(
                        'Retry attempt ' + str(attempt + 1) + ' of ' + str(max_retries) +
                        ' for audio (' + retry_note + ')...\n', 'warning')
                    if wait_secs:
                        time.sleep(wait_secs)
                    if 'HTTP Error 416' in _last_exc_str:
                        _exp416 = (0 if _clip_active else
                                   self._expected_stream_size(video_info, audio_format_id))
                        _got416 = self._resolve_leg_file(
                            os.path.join(temp_dir, 'audio.%(ext)s'))
                        if _got416 and _got416.lower().endswith('.mp3'):
                            _exp416 = 0  # extracted mp3: size not comparable
                        self._resolve_416_partial(
                            os.path.join(temp_dir, 'audio.%(ext)s'),
                            _exp416, 'Audio')
                else:
                    fmt_label = {'m4a_native': 'M4A Native', 'm4a_aac': 'M4A AAC',
                                 'mp3': 'MP3'}.get(fmt, fmt.upper())
                    self.append_terminal_output(
                        'Starting audio-only download (' + fmt_label + '): ' + quality + '\n', 'info')
                    self.root.after(0, lambda: self.progress_bar.start())

                _vid = video_id or (video_info.get('id') if video_info else None)

                # ── Helper: codec detection via format ID lookup ──────────
                def _is_aac_file(path, fmt_id=None):
                    """True when the file's audio really is AAC.

                    Had two defects that cancelled out until the naming
                    policy exposed them:
                      * HLS-derived ids carry a suffix ('140-7', '249-20')
                        and matched neither id set, so every one of them
                        fell through to the probe below.
                      * The probe searched the WHOLE of 'ffmpeg -i' output
                        for 'opus'. Every full FFmpeg build advertises
                        --enable-libopus in its banner, so that test was
                        always true and the probe always answered False -
                        even for a freshly transcoded AAC file.
                    """
                    # Ask the FILE first. The id argument is the RECOMMENDED
                    # format, but the selector chain often downloads something
                    # else - asking for AAC can legitimately land on 140-16
                    # while the recommendation was 251-16. Trusting the id
                    # then declared a genuine AAC file "Opus" and transcoded
                    # it to AAC for nothing.
                    if self.ffmpeg_path and os.path.exists(path):
                        try:
                            _p = subprocess.run(
                                [self.ffmpeg_path, '-hide_banner', '-i', path],
                                capture_output=True, text=True, encoding='utf-8',
                                errors='replace', timeout=10,
                                creationflags=CREATE_NO_WINDOW)
                            _out = (_p.stdout or '') + (_p.stderr or '')
                            for _line in _out.splitlines():
                                if 'Audio:' in _line:
                                    return 'aac' in _line.lower()
                        except Exception:
                            pass
                    # No FFmpeg (or an unreadable file): fall back to the id,
                    # stripping the HLS suffix so '140-16' matches '140'.
                    _fid = str(fmt_id).split('-')[0] if fmt_id else ''
                    if _fid in _YT_AUDIO_AAC_IDS:
                        return True
                    if _fid in _YT_AUDIO_OPUS_IDS or _fid in _YT_AUDIO_VORBIS_IDS:
                        return False
                    return False

                # ── Helper: move temp file to final output path ───────────
                def _move_to_output(tmp_path):
                    """Move completed audio file from temp dir to output folder.
                    Computes the final filename from video_info so naming is
                    consistent regardless of what yt-dlp called the temp file.
                    Returns the final path."""
                    _ext  = os.path.splitext(tmp_path)[1].lower() or '.m4a'
                    # Build the final filename using the same assembly logic
                    # used by the merge worker so naming is consistent.
                    # Quality tag: for audio-only the video quality is
                    # meaningless - 240p and 720p fetch the SAME audio
                    # stream, so a [720p] tag implied a difference that did
                    # not exist. Default is the real audio bitrate.
                    _qtmode = getattr(self, 'audio_quality_tag', 'audio')
                    if _qtmode == 'none':
                        _qt = ''
                    elif _qtmode == 'video':
                        _qt = quality
                    else:
                        _abr0 = self._audio_source_abr(video_info, audio_format_id)
                        _qt = ((str(_abr0) + 'kbps') if _abr0
                               else (str(audio_format_id) if audio_format_id else ''))
                    _lang = ''
                    try:
                        for _af in (video_info.get('formats') or []):
                            if str(_af.get('format_id', '')) == str(audio_format_id):
                                _dl = self.detect_audio_language(_af)
                                if _dl and _dl != 'unknown':
                                    _lang = _dl.upper()
                                break
                    except Exception:
                        pass
                    _bracket = (_qt + ' ' + _lang).strip()
                    _final_name = self._assemble_filename(video_info, _bracket, _ext)
                    # Optional separate destination for audio-only output.
                    _outdir = getattr(self, 'audio_output_folder', '') or self.download_path
                    try:
                        os.makedirs(_outdir, exist_ok=True)
                    except Exception:
                        _outdir = self.download_path
                    _target = os.path.join(_outdir, _final_name)
                    _dup = getattr(self, 'audio_duplicate_action', 'number')
                    if _dup == 'skip' and os.path.exists(_target):
                        self.append_terminal_output(
                            'File already exists - keeping the existing copy'
                            ' (duplicate handling: skip).\n', 'warning')
                        try:
                            os.remove(tmp_path)
                        except Exception:
                            pass
                        return _target
                    if _dup == 'overwrite':
                        _final_path = _target
                        if os.path.exists(_final_path):
                            try:
                                os.remove(_final_path)
                            except Exception:
                                _final_path = self._unique_output_path(_target, _vid)
                    else:
                        _final_path = self._unique_output_path(_target, _vid)
                    shutil.move(tmp_path, _final_path)
                    return _final_path

                def _apply_ext_policy(p, is_aac_content):
                    """Decide the final container extension for M4A output.

                    Native mode wrote every stream to 'audio.m4a' regardless
                    of codec, so a low-bitrate Opus pick was delivered as an
                    .m4a that iTunes/iOS and many car stereos refuse. Real
                    AAC still gets .m4a; Opus follows the user's setting."""
                    if is_aac_content:
                        if not p.lower().endswith('.m4a'):
                            _r = os.path.join(temp_dir, 'audio.m4a')
                            os.replace(p, _r)
                            return _r
                        return p
                    _mode = getattr(self, 'audio_opus_naming', 'codec')
                    if _mode == 'm4a':
                        if not p.lower().endswith('.m4a'):
                            _r = os.path.join(temp_dir, 'audio.m4a')
                            os.replace(p, _r)
                            return _r
                        return p
                    if _mode == 'remux':
                        _r = os.path.join(temp_dir, 'audio_remux.m4a')
                        try:
                            _rr = subprocess.run(
                                [self.ffmpeg_path, '-y', '-i', p, '-c:a', 'copy',
                                 '-strict', '-2', '-loglevel', 'error', _r],
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                text=True, encoding='utf-8', errors='replace',
                                timeout=_conv_to, creationflags=CREATE_NO_WINDOW)
                            if _rr.returncode == 0 and os.path.exists(_r):
                                try:
                                    os.remove(p)
                                except Exception:
                                    pass
                                return _r
                            self.append_terminal_output(
                                'Remux to M4A failed - keeping the original'
                                ' container.\n', 'warning')
                        except Exception:
                            pass
                    # 'codec' (default), or remux failed: keep the true
                    # extension yt-dlp produced so the file never lies.
                    if p.lower().endswith('.m4a'):
                        _true = os.path.join(temp_dir, 'audio.webm')
                        try:
                            os.replace(p, _true)
                            return _true
                        except Exception:
                            return p
                    return p

                # temp_dir is created once before the retry loop (M5) so
                # partials survive pause/resume and retry attempts.
                _attempt_ok = False
                try:
                    # ── Cache fast-path (attempt 0 only; full files, so
                    # bypassed in clip mode) ──────────────────────────────
                    if attempt == 0 and not _clip_active:
                        if use_mp3:
                            _cached_mp3 = None
                            if audio_format_id and _vid:
                                _cached_mp3 = self.get_cached_mp3_path(_vid, audio_format_id)
                            if _cached_mp3:
                                _tmp_mp3 = os.path.join(temp_dir, 'audio.mp3')
                                shutil.copy2(_cached_mp3, _tmp_mp3)
                                self.append_terminal_output(
                                    'MP3 from cache (no conversion needed).\n', 'cache')
                                _embed_result = self._embed_metadata(_tmp_mp3, video_info)
                                _tmp_mp3 = _embed_result if _embed_result else _tmp_mp3
                                self._set_file_timestamps(_tmp_mp3, video_info)
                                actual_path = _move_to_output(_tmp_mp3)
                                download_time = time.time() - self.download_start_time
                                file_size = self.format_file_size(os.path.getsize(actual_path))
                                self.append_terminal_output('Audio download complete (from cache)!\n', 'success')
                                self.append_terminal_output('File: ' + os.path.basename(actual_path) + '\n', 'success')
                                self.append_terminal_output('Size: ' + file_size + '\n', 'success')
                                self.append_terminal_output('Time: ' + self._format_download_time(download_time) + '\n\n', 'success')
                                self.root.after(0, lambda p=actual_path, t=download_time:
                                    self._download_complete(p, 'Audio Download (cached)', t))
                                _attempt_ok = True
                                return

                            cached_src = None
                            if audio_format_id and _vid:
                                cached_src = self.get_cached_audio_path(_vid, audio_format_id)
                            if not cached_src and _vid and _vid in self.cached_videos:
                                with self._cache_lock:
                                    for key, path in list(self.cached_videos[_vid].items()):
                                        if key.startswith('audio_') and os.path.exists(path):
                                            cached_src = path
                                            break
                            if cached_src:
                                self.append_terminal_output(
                                    'Using cached audio - skipping download\n', 'cache')
                                _tmp_mp3 = os.path.join(temp_dir, 'audio.mp3')
                                _cached_ext = os.path.splitext(cached_src)[1].lower()
                                if _cached_ext == '.mp3':
                                    shutil.copy2(cached_src, _tmp_mp3)
                                    conv_ok = True
                                else:
                                    conv_cmd = [
                                        self.ffmpeg_path, '-y', '-i', cached_src,
                                        '-vn', '-acodec', 'libmp3lame'] + _mp3_enc + [
                                        '-loglevel', 'error', _tmp_mp3
                                    ]
                                    self.append_terminal_output(
                                        'Converting cached audio to MP3...\n', 'info')
                                    conv_result = subprocess.run(
                                        conv_cmd, stdout=subprocess.PIPE,
                                        stderr=subprocess.STDOUT, text=True, encoding='utf-8', errors='replace',
                                        timeout=_conv_to, creationflags=CREATE_NO_WINDOW)
                                    conv_ok = conv_result.returncode == 0
                                if conv_ok and os.path.exists(_tmp_mp3):
                                    _embed_result = self._embed_metadata(_tmp_mp3, video_info)
                                    _tmp_mp3 = _embed_result if _embed_result else _tmp_mp3
                                    self._set_file_timestamps(_tmp_mp3, video_info)
                                    if audio_format_id and _vid and _embed_result:
                                        self.cache_mp3_stream(_vid, audio_format_id, _tmp_mp3)
                                    actual_path = _move_to_output(_tmp_mp3)
                                    download_time = time.time() - self.download_start_time
                                    file_size = self.format_file_size(os.path.getsize(actual_path))
                                    self.append_terminal_output('Audio download complete (from cache)!\n', 'success')
                                    self.append_terminal_output('File: ' + os.path.basename(actual_path) + '\n', 'success')
                                    self.append_terminal_output('Size: ' + file_size + '\n', 'success')
                                    self.append_terminal_output('Time: ' + self._format_download_time(download_time) + '\n\n', 'success')
                                    self.root.after(0, lambda p=actual_path, t=download_time:
                                        self._download_complete(p, 'Audio Download (cached)', t))
                                    _attempt_ok = True
                                    return
                                else:
                                    self.append_terminal_output(
                                        'Cached conversion failed, falling back to download...\n', 'warning')

                        else:
                            # M4A Native / M4A AAC cache path
                            cached_src = None
                            if audio_format_id and _vid:
                                cached_src = self.get_cached_audio_path(_vid, audio_format_id)
                            if not cached_src and _vid and _vid in self.cached_videos:
                                with self._cache_lock:
                                    for key, path in list(self.cached_videos[_vid].items()):
                                        if key.startswith('audio_') and os.path.exists(path):
                                            cached_src = path
                                            break
                            if cached_src:
                                self.append_terminal_output(
                                    'Using cached audio stream\n', 'cache')
                                is_aac = _is_aac_file(cached_src, audio_format_id)

                                if use_native:
                                    # Name the staged copy after the cached
                                    # file's real container, then let the
                                    # policy decide - hardcoding .m4a here
                                    # meant a CACHED Opus stream arrived as
                                    # .m4a while a freshly downloaded one
                                    # arrived as .webm.
                                    self._mark_cache_inuse(cached_src)
                                    _c_ext = os.path.splitext(cached_src)[1] or '.m4a'
                                    _tmp_m4a = os.path.join(temp_dir, 'audio' + _c_ext)
                                    shutil.copy2(cached_src, _tmp_m4a)
                                    _tmp_m4a = _apply_ext_policy(_tmp_m4a, is_aac)
                                    if is_aac:
                                        self.append_terminal_output(
                                            'Cached audio is native AAC - embedding metadata...\n', 'cache')
                                        _embed_result = self._embed_metadata(_tmp_m4a, video_info)
                                        _tmp_m4a = _embed_result if _embed_result else _tmp_m4a
                                    else:
                                        self.append_terminal_output(
                                            'Cached audio is Opus codec - metadata/thumbnail embedding '
                                            'skipped (Opus is not supported in M4A container for embedding).\n',
                                            'warning')
                                    self._set_file_timestamps(_tmp_m4a, video_info)
                                    actual_path = _move_to_output(_tmp_m4a)
                                    download_time = time.time() - self.download_start_time
                                    file_size = self.format_file_size(os.path.getsize(actual_path))
                                    self.append_terminal_output('Audio download complete (from cache)!\n', 'success')
                                    self.append_terminal_output('File: ' + os.path.basename(actual_path) + '\n', 'success')
                                    self.append_terminal_output('Size: ' + file_size + '\n', 'success')
                                    self.append_terminal_output('Time: ' + self._format_download_time(download_time) + '\n\n', 'success')
                                    self.root.after(0, lambda p=actual_path, t=download_time:
                                        self._download_complete(p, 'Audio Download (cached)', t))
                                    _attempt_ok = True
                                    return
                                else:
                                    # M4A AAC: transcode if needed
                                    _tmp_m4a = os.path.join(temp_dir, 'audio.m4a')
                                    if is_aac:
                                        shutil.copy2(cached_src, _tmp_m4a)
                                        self.append_terminal_output(
                                            'Cached audio is native AAC - embedding metadata...\n', 'cache')
                                        conv_ok = True
                                    else:
                                        self.append_terminal_output(
                                            'No AAC stream available - converting from Opus...\n', 'info')
                                        conv_cmd = [
                                            self.ffmpeg_path, '-y', '-i', cached_src,
                                            '-vn', '-acodec', 'aac', '-b:a', _abr_arg,
                                            '-loglevel', 'error', _tmp_m4a
                                        ]
                                        conv_result = subprocess.run(
                                            conv_cmd, stdout=subprocess.PIPE,
                                            stderr=subprocess.STDOUT, text=True, encoding='utf-8', errors='replace',
                                            timeout=_conv_to, creationflags=CREATE_NO_WINDOW)
                                        conv_ok = (conv_result.returncode == 0 and
                                                   os.path.exists(_tmp_m4a))
                                    if conv_ok:
                                        _embed_result = self._embed_metadata(_tmp_m4a, video_info)
                                        _tmp_m4a = _embed_result if _embed_result else _tmp_m4a
                                        self._set_file_timestamps(_tmp_m4a, video_info)
                                        actual_path = _move_to_output(_tmp_m4a)
                                        download_time = time.time() - self.download_start_time
                                        file_size = self.format_file_size(os.path.getsize(actual_path))
                                        self.append_terminal_output('Audio download complete (from cache)!\n', 'success')
                                        self.append_terminal_output('File: ' + os.path.basename(actual_path) + '\n', 'success')
                                        self.append_terminal_output('Size: ' + file_size + '\n', 'success')
                                        self.append_terminal_output('Time: ' + self._format_download_time(download_time) + '\n\n', 'success')
                                        self.root.after(0, lambda p=actual_path, t=download_time:
                                            self._download_complete(p, 'Audio Download (cached)', t))
                                        _attempt_ok = True
                                        return
                                    else:
                                        self.append_terminal_output(
                                            'Cached conversion failed, falling back to download...\n', 'warning')

                    # ── Network download into temp dir ────────────────────
                    _common_args = [
                        '--no-warnings', '--newline', '--progress',
                        '--retries', '10', '--fragment-retries', '10',
                        '--retry-sleep', 'linear=1::2',
                        '--no-part',
                        '-c',
                        '--add-headers', 'Connection:keep-alive',
                        '--buffer-size', '16K',
                        '--http-chunk-size', '10M',
                    ]
                    if _clip_active:
                        # Sections are not resumable - drop -c for clip runs.
                        _common_args = [a for a in _common_args if a != '-c']
                        _common_args = _common_args + _clip_section_args
                        self.append_terminal_output(
                            'Clip (audio): ' + str(_clip_start_hms) + ' to '
                            + str(_clip_end_hms)
                            + ' - downloading only this section.\n', 'info')

                    if use_mp3:
                        _tmp_out = os.path.join(temp_dir, 'audio.%(ext)s')
                        # Honour the recommended stream (carries the user's
                        # bitrate preference); bestaudio only as last resort.
                        _mp3_sel = (str(audio_format_id) + '/bestaudio/best'
                                    if audio_format_id else 'bestaudio/best')
                        args = _common_args + [
                            '-f', _mp3_sel,
                            '--extract-audio', '--audio-format', 'mp3',
                            '--audio-quality', _mp3_q,
                            '-o', _tmp_out,
                        ]
                        args.extend(self.get_player_client_extractor_args())
                        if self.ffmpeg_path and self.ffmpeg_path not in ('ffmpeg', 'ffmpeg.exe'):
                            args += ['--ffmpeg-location', os.path.dirname(self.ffmpeg_path)]
                        args.extend(self.get_ytdlp_dns_args())
                        if self.yt_dlp_cache_dir:
                            args += ['--cache-dir', self.yt_dlp_cache_dir]
                        args.append(url)
                        _pre_done = False
                        _pre_is_mp3 = ('--extract-audio' in args)
                        if not _clip_active and not _pre_is_mp3:
                            _exp0 = self._expected_stream_size(video_info, audio_format_id)
                            _got0 = self._resolve_leg_file(os.path.join(temp_dir, 'audio.%(ext)s'))
                            if _got0 and _exp0 and os.path.getsize(_got0) >= _exp0:
                                self.append_terminal_output(
                                    'Audio already complete from a previous'
                                    ' attempt (size verified) - skipping'
                                    ' download.\n', 'success')
                                _pre_done = True
                        if not _pre_done:
                            self.run_ytdlp_command_with_terminal(args, capture_output=False, timeout=7200)

                        # Find the output file yt-dlp wrote
                        _tmp_audio = None
                        for _f in os.listdir(temp_dir):
                            if _f.startswith('audio.'):
                                _tmp_audio = os.path.join(temp_dir, _f)
                                break
                        if not _tmp_audio or not os.path.exists(_tmp_audio):
                            raise Exception('MP3 file not found after conversion in temp dir')

                        _embed_result = self._embed_metadata(_tmp_audio, video_info)
                        _tmp_audio = _embed_result if _embed_result else _tmp_audio
                        self._set_file_timestamps(_tmp_audio, video_info)
                        _vid2 = video_id or (video_info.get('id') if video_info else None)
                        if _vid2 and audio_format_id and _embed_result:
                            self.cache_mp3_stream(_vid2, audio_format_id, _tmp_audio)
                        actual_path = _move_to_output(_tmp_audio)

                    elif use_native:
                        _fmt_sel  = audio_format_id if audio_format_id else 'bestaudio'
                        if getattr(self, 'audio_opus_naming', 'codec') == 'prefer_aac':
                            # Ask for a real AAC stream first; fall back to
                            # the recommended pick when the video has none.
                            _fmt_sel = 'bestaudio[acodec^=mp4a]/' + _fmt_sel
                        _tmp_out  = os.path.join(temp_dir, 'audio.%(ext)s')
                        args = _common_args + ['-f', _fmt_sel, '-o', _tmp_out]
                        args.extend(self.get_player_client_extractor_args())
                        args.extend(self.get_ytdlp_dns_args())
                        if self.yt_dlp_cache_dir:
                            args += ['--cache-dir', self.yt_dlp_cache_dir]
                        args.append(url)
                        _pre_done = False
                        _pre_is_mp3 = ('--extract-audio' in args)
                        if not _clip_active and not _pre_is_mp3:
                            _exp0 = self._expected_stream_size(video_info, audio_format_id)
                            _got0 = self._resolve_leg_file(os.path.join(temp_dir, 'audio.%(ext)s'))
                            if _got0 and _exp0 and os.path.getsize(_got0) >= _exp0:
                                self.append_terminal_output(
                                    'Audio already complete from a previous'
                                    ' attempt (size verified) - skipping'
                                    ' download.\n', 'success')
                                _pre_done = True
                        if not _pre_done:
                            self.run_ytdlp_command_with_terminal(args, capture_output=False, timeout=7200)

                        # Locate what yt-dlp actually wrote
                        _tmp_audio = None
                        for _f in os.listdir(temp_dir):
                            if _f.startswith('audio.'):
                                _tmp_audio = os.path.join(temp_dir, _f)
                                break
                        if not _tmp_audio or not os.path.exists(_tmp_audio):
                            raise Exception('Audio file not found in temp dir after download')

                        # Cache the RAW stream (before renaming/embedding) so
                        # repeat downloads and later merges reuse it.
                        if not _clip_active:
                            self._cache_raw_audio_stream(_vid, audio_format_id, _tmp_audio)

                        _tmp_audio = _apply_ext_policy(
                            _tmp_audio, _is_aac_file(_tmp_audio, audio_format_id))

                        if _is_aac_file(_tmp_audio, audio_format_id):
                            _embed_result = self._embed_metadata(_tmp_audio, video_info)
                            _tmp_audio = _embed_result if _embed_result else _tmp_audio
                        else:
                            self.append_terminal_output(
                                'Audio is Opus codec - metadata/thumbnail embedding skipped '
                                '(Opus is not supported in M4A container for embedding).\n', 'warning')
                        self._set_file_timestamps(_tmp_audio, video_info)
                        actual_path = _move_to_output(_tmp_audio)

                    else:
                        # M4A AAC
                        _limit = getattr(self, 'preferred_audio_bitrate', 0)
                        if _limit and _limit > 0:
                            _aac_sel = ('139' if _limit <= 64
                                        else '141/140/139' if _limit >= 192
                                        else '140/139')
                        else:
                            _aac_sel = '141/140/139'
                        # When the video has no AAC at all, fall back to the
                        # RECOMMENDED stream (honours the bitrate preference)
                        # before ever reaching bare bestaudio - previously a
                        # no-AAC video grabbed the largest Opus regardless.
                        _fid_fb   = (str(audio_format_id) + '/') if audio_format_id else ''
                        # 'acodec=aac' matches nothing: YouTube reports its
                        # AAC streams as mp4a.40.2, so the filter always
                        # failed and the chain fell through to the plain
                        # recommended id - an Opus stream - which then got
                        # transcoded for no reason. Bare ids like '140' also
                        # miss the HLS-derived '140-16' variants, so match on
                        # codec and container instead of on id alone.
                        _fmt_sel  = (_aac_sel
                                     + '/bestaudio[acodec^=mp4a]'
                                     + '/bestaudio[ext=m4a]'
                                     + '/' + _fid_fb + 'bestaudio')
                        _tmp_out  = os.path.join(temp_dir, 'audio.m4a')
                        args = _common_args + ['-f', _fmt_sel, '-o', _tmp_out]
                        args.extend(self.get_player_client_extractor_args())
                        args.extend(self.get_ytdlp_dns_args())
                        if self.yt_dlp_cache_dir:
                            args += ['--cache-dir', self.yt_dlp_cache_dir]
                        args.append(url)
                        _pre_done = False
                        _pre_is_mp3 = ('--extract-audio' in args)
                        if not _clip_active and not _pre_is_mp3:
                            _exp0 = self._expected_stream_size(video_info, audio_format_id)
                            _got0 = self._resolve_leg_file(os.path.join(temp_dir, 'audio.%(ext)s'))
                            if _got0 and _exp0 and os.path.getsize(_got0) >= _exp0:
                                self.append_terminal_output(
                                    'Audio already complete from a previous'
                                    ' attempt (size verified) - skipping'
                                    ' download.\n', 'success')
                                _pre_done = True
                        if not _pre_done:
                            self.run_ytdlp_command_with_terminal(args, capture_output=False, timeout=7200)

                        _tmp_audio = None
                        for _f in os.listdir(temp_dir):
                            if _f.startswith('audio.'):
                                _tmp_audio = os.path.join(temp_dir, _f)
                                break
                        if not _tmp_audio or not os.path.exists(_tmp_audio):
                            raise Exception('Audio file not found in temp dir after download')

                        # Cache the RAW stream only when it is genuine AAC: a
                        # transcode must never be stored under the source
                        # format id.
                        if not _clip_active and _is_aac_file(_tmp_audio, audio_format_id):
                            self._cache_raw_audio_stream(_vid, audio_format_id, _tmp_audio)

                        _did_convert = False
                        _no_aac = (not _is_aac_file(_tmp_audio, audio_format_id))
                        _na_act = getattr(self, 'audio_no_aac_action', 'transcode')
                        if _no_aac and _na_act == 'skip':
                            raise Exception(
                                'No AAC stream available for this video and'
                                ' the no-AAC setting is "skip".')
                        if _no_aac and _na_act == 'keep_opus':
                            self.append_terminal_output(
                                'No AAC stream available - keeping the original'
                                ' Opus stream without transcoding.\n', 'warning')
                        if _no_aac and _na_act == 'transcode':
                            self.append_terminal_output(
                                'No AAC stream available - converting from Opus...\n', 'info')
                            _conv_out = os.path.join(temp_dir, 'audio_aac.m4a')
                            conv_cmd = [
                                self.ffmpeg_path, '-y', '-i', _tmp_audio,
                                '-vn', '-acodec', 'aac', '-b:a', _abr_arg,
                                '-loglevel', 'error', _conv_out
                            ]
                            conv_result = subprocess.run(
                                conv_cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True, encoding='utf-8', errors='replace',
                                timeout=_conv_to, creationflags=CREATE_NO_WINDOW)
                            if conv_result.returncode == 0 and os.path.exists(_conv_out):
                                try:
                                    os.remove(_tmp_audio)
                                except Exception:
                                    pass
                                _tmp_audio = _conv_out
                                _did_convert = True
                            else:
                                # M6 fix: never rename an unconverted Opus file
                                # to .m4a as if it were AAC - that delivers a
                                # mislabeled, often unplayable file as success.
                                _cv_err = (conv_result.stdout or '').strip()[-300:]
                                raise Exception(
                                    'AAC conversion failed (ffmpeg rc='
                                    + str(conv_result.returncode) + '): '
                                    + (_cv_err or 'no ffmpeg output'))

                        # A completed transcode is AAC in an M4A container by
                        # construction - asking _is_aac_file about it with the
                        # SOURCE format id is both wrong and fragile.
                        _tmp_audio = _apply_ext_policy(
                            _tmp_audio,
                            _did_convert or _is_aac_file(_tmp_audio, audio_format_id))

                        _embed_result = self._embed_metadata(_tmp_audio, video_info)
                        _tmp_audio = _embed_result if _embed_result else _tmp_audio
                        self._set_file_timestamps(_tmp_audio, video_info)
                        actual_path = _move_to_output(_tmp_audio)

                    download_time = time.time() - self.download_start_time
                    file_size = self.format_file_size(os.path.getsize(actual_path))
                    self.append_terminal_output('Audio download complete!\n', 'success')
                    self.append_terminal_output('File: ' + os.path.basename(actual_path) + '\n', 'success')
                    self.append_terminal_output('Size: ' + file_size + '\n', 'success')
                    self.append_terminal_output('Time: ' + self._format_download_time(download_time) + '\n\n', 'success')
                    self.root.after(0, lambda p=actual_path, t=download_time:
                        self._download_complete(p, 'Audio Download', t))
                    _attempt_ok = True
                    return

                finally:
                    # Clean up only on a successful attempt (the audio file
                    # has already been moved out). On pause/stop/retryable
                    # failure the partial is kept so -c can resume it.
                    # An explicit flag is used rather than sys.exc_info():
                    # that reports any exception being handled ANYWHERE up
                    # the stack, so the format-refresh restart - which calls
                    # this worker from inside an except block - made every
                    # nested success look like a failure and leaked its
                    # temp dir.
                    if _attempt_ok:
                        shutil.rmtree(temp_dir, ignore_errors=True)

            except (_DownloadStoppedError, _DownloadPausedError):
                return
            except Exception as e:
                _last_exc_str = str(e)
                self.append_terminal_output(
                    'Attempt ' + str(attempt + 1) + ' failed: ' + str(e) + '\n', 'error')

                # On first failure, if format expired re-fetch and restart
                if 'Requested format is not available' in _last_exc_str and attempt == 0:
                    self.append_terminal_output(
                        '\nStream URL expired - re-fetching fresh audio format ID...\n', 'warning')
                    try:
                        fresh_info = self.get_video_info(url)
                        all_audio = [f for f in fresh_info.get('formats', [])
                                     if f.get('acodec') not in (None, 'none')
                                     and f.get('vcodec') in (None, 'none')]
                        det_langs = {}
                        for af in all_audio:
                            if 'detected_language' not in af:
                                _, lang = self.get_audio_stream_description(af)
                                af['detected_language'] = lang
                            det_langs.setdefault(af['detected_language'], []).append(af)
                        fresh_audio = self.select_best_audio_stream(all_audio, det_langs)
                        if fresh_audio:
                            fresh_fid = str(fresh_audio.get('format_id', ''))
                            self.append_terminal_output(
                                'Fresh audio format ID: ' + fresh_fid + ' - restarting.\n', 'info')
                            # New format id: the old partial is unusable, so
                            # clear the dir contents but keep reusing the dir.
                            try:
                                for _pf in os.listdir(temp_dir):
                                    os.remove(os.path.join(temp_dir, _pf))
                            except Exception:
                                pass
                            # Depth guard: a format that keeps "expiring" would
                            # otherwise restart the worker from inside its own
                            # except handler without limit.
                            _d = getattr(self, '_fmt_restart_depth', 0)
                            if _d >= 2:
                                self.append_terminal_output(
                                    'Format kept expiring after ' + str(_d)
                                    + ' refreshes - giving up on this attempt.\n',
                                    'error')
                                raise
                            self._fmt_restart_depth = _d + 1
                            try:
                                self._download_audio_only_worker(
                                    output_path, quality, url, fresh_info,
                                    fresh_fid, video_id, temp_dir)
                            finally:
                                self._fmt_restart_depth = _d
                            return
                        else:
                            self.append_terminal_output(
                                'No audio stream found in fresh info - continuing retries.\n', 'warning')
                    except Exception as refresh_err:
                        self.append_terminal_output(
                            'Re-fetch failed: ' + str(refresh_err) + '\n', 'error')

                if attempt == max_retries - 1:
                    shutil.rmtree(temp_dir, ignore_errors=True)
                    err = 'Audio download failed: ' + str(e)
                    self.append_terminal_output(err + '\n', 'error')
                    self.root.after(0, lambda m=err: self._download_error(m))
                    return
            finally:
                if attempt == 0:
                    self.root.after(0, lambda: self.progress_bar.stop())


    def _preview_error(self, message):
        """Show a small click-to-dismiss error overlay for Preview errors."""
        try:
            ew = tk.Toplevel(self.root)
            ew.title('Preview')
            ew.resizable(False, False)
            ew.attributes('-topmost', True)
            bg = '#2d2d2d' if getattr(self, 'dark_mode', False) else '#fff5cc'
            fg = '#eeeeee' if getattr(self, 'dark_mode', False) else '#333333'
            ew.configure(background=bg)
            lbl = tk.Label(ew, text=message + '\n\nClick anywhere to close.',
                           background=bg, foreground=fg,
                           font=('Arial', 10), padx=20, pady=16,
                           justify=tk.LEFT, wraplength=360)
            lbl.pack()
            for widget in (ew, lbl):
                widget.bind('<Button-1>', lambda e, w=ew: w.destroy())
            ew.update_idletasks()
            rx = self.root.winfo_rootx() + self.root.winfo_width() // 2 - ew.winfo_width() // 2
            ry = self.root.winfo_rooty() + self.root.winfo_height() // 2 - ew.winfo_height() // 2
            ew.geometry('+' + str(rx) + '+' + str(ry))
        except Exception:
            pass

    def _show_preview(self):
        """Open a browser-based preview window for the current video.

        Source priority (quality-aware):
          1. Selected quality streams cached -> instant stream-copy merge (full seek)
          2. Premux or any cached pair -> instant file serve (full seek)
          3. Nothing cached -> live CDN:
             a. Selected quality -> piped fragmented WebM (-c copy, no transcode)
             b. No selection -> direct premuxed CDN redirect
             c. Last resort -> piped fragmented WebM from best available pair
        """
        import http.server
        import urllib.parse as _urlparse
        import webbrowser
        import socket as _socket
        import re as _re

        vi = self.current_video_info
        if not vi:
            self._preview_error('Analyze a video first.')
            return

        video_id  = vi.get('id', 'unknown')
        _duration = float(vi.get('duration') or 0) or 0.0

        # ── Read selected quality from recommended tree ───────────────────────
        _sel_quality_label = None
        _sel_vfid = _sel_afid = None
        try:
            _sel = self.recommended_tree.selection()
            if _sel:
                _vals = self.recommended_tree.item(_sel[0], 'values')
                if _vals and 'Direct:' not in str(_vals[1]):
                    _sel_quality_label = str(_vals[0])
                    _vi2 = str(_vals[1])
                    _ai2 = str(_vals[2])
                    _sel_vfid = _vi2.split('(')[1].split(')')[0] if '(' in _vi2 else ''
                    _sel_afid = (_ai2.split('ID:')[1].split(' ')[0]
                                 if 'ID:' in _ai2
                                 else (_ai2.split('(')[1].split(')')[0]
                                       if '(' in _ai2 else ''))
        except Exception:
            pass

        # ── Source variables ──────────────────────────────────────────────────
        _video_path     = None   # complete local file -> full seek via Range
        _direct_url     = None   # CDN redirect -> browser streams directly
        _pipe_video_url = None   # CDN video URL for WebM pipe (-c copy)
        _pipe_audio_url = None   # CDN audio URL for WebM pipe (-c copy)
        _has_selection  = bool(_sel_vfid and _sel_afid)

        # 1a. Selected quality -> check cache first (instant if cached)
        if _has_selection:
            _cv = self.get_cached_video_path(video_id, _sel_vfid)
            _ca = self.get_cached_audio_path(video_id, _sel_afid)
            if _cv and _ca and self.ffmpeg_path:
                try:
                    _pd   = self._make_temp_dir('ysa_preview_')
                    _pout = os.path.join(_pd, 'preview.mp4')
                    subprocess.run(
                        [self.ffmpeg_path, '-y',
                         '-i', _cv, '-i', _ca,
                         '-c:v', 'copy', '-c:a', 'copy',
                         '-movflags', '+faststart',
                         '-loglevel', 'error', _pout],
                        capture_output=True, timeout=120,
                        creationflags=CREATE_NO_WINDOW)
                    if os.path.exists(_pout):
                        _video_path = _pout
                        self.append_terminal_output(
                            'Preview: ' + str(_sel_quality_label) + ' from cache\n', 'info')
                except Exception:
                    pass

        # 1b. Selected quality NOT cached -> try CDN at the selected resolution
        #     This runs BEFORE the premuxed/any-pair fallback so we always
        #     preview at the resolution the user actually selected.
        if not _video_path and _has_selection:
            try:
                _url = getattr(self, 'current_video_url', None) or self.url_var.get().strip()
                self.append_terminal_output(
                    'Preview: fetching CDN for ' + str(_sel_quality_label) + '...\n', 'info')
                _fresh = self.get_video_info(_url)
                if _fresh:
                    _all_fmts = _fresh.get('formats', [])
                    def _fmt_url_sel(fid):
                        for _f in _all_fmts:
                            if str(_f.get('format_id', '')) == str(fid):
                                return _f.get('url') or _f.get('fragment_base_url')
                        return None
                    _vu = _fmt_url_sel(_sel_vfid)
                    _au = _fmt_url_sel(_sel_afid)
                    if _vu and _au and self.ffmpeg_path:
                        _pipe_video_url = _vu
                        _pipe_audio_url = _au
                        self.append_terminal_output(
                            'Preview: WebM pipe ' + str(_sel_quality_label) +
                            ' (no transcode)\n', 'info')
                    elif _vu:
                        # Video-only stream with audio in a combined format
                        _direct_url = _vu
                        self.append_terminal_output(
                            'Preview: direct CDN ' + str(_sel_quality_label) + '\n', 'info')
            except Exception as _fe:
                self.append_terminal_output(
                    'Preview: CDN fetch failed for selected quality: ' + str(_fe) + '\n', 'warning')

        # 2a. No selection -> premuxed cache (best available, instant)
        if not _video_path and not _pipe_video_url and not _direct_url and not _has_selection:
            for _vkey in list(self.cached_premuxed.get(video_id, {}).keys()):
                _p = self.get_cached_premuxed_path(video_id, _vkey)
                if _p:
                    _video_path = _p
                    self.append_terminal_output('Preview: premuxed cache\n', 'info')
                    break

        # 2b. No selection -> any cached video+audio pair (instant merge)
        if not _video_path and not _pipe_video_url and not _direct_url and not _has_selection:
            with self._cache_lock:
                _ve = dict(self.cached_videos.get(video_id, {}))
            _bv = _ba = None
            for _fid, _fp in _ve.items():
                if not _fid.startswith('audio_') and not _fid.startswith('mp3_') and os.path.exists(_fp):
                    _bv = _fp; break
            for _fid, _fp in _ve.items():
                if _fid.startswith('audio_') and os.path.exists(_fp):
                    _ba = _fp; break
            if _bv and _ba and self.ffmpeg_path:
                try:
                    _pd   = self._make_temp_dir('ysa_preview_')
                    _pout = os.path.join(_pd, 'preview.mp4')
                    subprocess.run(
                        [self.ffmpeg_path, '-y', '-i', _bv, '-i', _ba,
                         '-c:v', 'copy', '-c:a', 'copy',
                         '-movflags', '+faststart', '-loglevel', 'error', _pout],
                        capture_output=True, timeout=120,
                        creationflags=CREATE_NO_WINDOW)
                    if os.path.exists(_pout):
                        _video_path = _pout
                        self.append_terminal_output('Preview: merged cached streams\n', 'info')
                except Exception:
                    pass

        # 2c. No selection, nothing cached -> live CDN (best premuxed or DASH pair)
        if not _video_path and not _pipe_video_url and not _direct_url and not _has_selection:
            try:
                _url = getattr(self, 'current_video_url', None) or self.url_var.get().strip()
                self.append_terminal_output('Preview: fetching live CDN URLs...\n', 'info')
                _fresh = self.get_video_info(_url)
                if _fresh:
                    _all_fmts = _fresh.get('formats', [])

                    # Direct premuxed CDN URL (best quality combined stream)
                    # Exclude HLS/m3u8 streams - browsers (except Safari) cannot
                    # play m3u8 playlist URLs directly.
                    _combined = [f for f in _all_fmts
                                 if f.get('acodec') not in (None, 'none')
                                 and f.get('vcodec') not in (None, 'none')
                                 and f.get('url')
                                 and 'm3u8' not in (f.get('protocol') or '').lower()]
                    _combined.sort(key=lambda f: (
                        f.get('ext', '') == 'mp4',
                        f.get('height') or 0), reverse=True)
                    if _combined:
                        _direct_url = _combined[0]['url']
                        self.append_terminal_output(
                            'Preview: direct CDN (' +
                            str(_combined[0].get('height', '?')) + 'p)\n', 'info')

                    # Last resort -> pipe best available DASH pair
                    if not _direct_url and self.ffmpeg_path:
                        _vids = sorted(
                            [f for f in _all_fmts
                             if f.get('vcodec') not in (None, 'none')
                             and f.get('acodec') in (None, 'none') and f.get('url')],
                            key=lambda f: f.get('height') or 0, reverse=True)
                        _auds = sorted(
                            [f for f in _all_fmts
                             if f.get('acodec') not in (None, 'none')
                             and f.get('vcodec') in (None, 'none') and f.get('url')],
                            key=lambda f: f.get('abr') or 0, reverse=True)
                        if _vids and _auds:
                            _pipe_video_url = _vids[0]['url']
                            _pipe_audio_url = _auds[0]['url']
                            self.append_terminal_output(
                                'Preview: WebM pipe best available quality\n', 'info')
            except Exception as _fe:
                self.append_terminal_output(
                    'Preview: CDN fetch failed: ' + str(_fe) + '\n', 'warning')

        if not _video_path and not _pipe_video_url and not _direct_url:
            self._preview_error(
                'No cached video and could not fetch live stream.\n'
                'Check your connection and try again.')
            return

        # ── 2. Read clip state ────────────────────────────────────────────────
        _clip_on = (getattr(self, '_clip_enabled_var', None) and
                    self._clip_enabled_var.get())

        def _hhmmss_to_sec(t):
            if not t:
                return 0.0
            parts = t.split(':')
            try:
                return int(parts[0]) * 3600 + int(parts[1]) * 60 + float(parts[2])
            except Exception:
                return 0.0

        _start_sec   = _hhmmss_to_sec(
            self._parse_time_to_hhmmss(self._clip_start_var.get())) if _clip_on else 0.0
        _end_sec     = _hhmmss_to_sec(
            self._parse_time_to_hhmmss(self._clip_end_var.get())) if _clip_on else 0.0
        _clip_active = _clip_on and _end_sec > _start_sec

        # ── 3. Pick a free port ───────────────────────────────────────────────
        with _socket.socket(_socket.AF_INET, _socket.SOCK_STREAM) as _ts:
            _ts.bind(('127.0.0.1', 0))
            _port = _ts.getsockname()[1]

        _app_ref = self

        # ── 4. Build HTML ─────────────────────────────────────────────────────
        _use_pipe = bool(_pipe_video_url)

        _html = ('<!DOCTYPE html>\n<html>\n<head>\n<meta charset="utf-8">\n'
                 '<title>YSA Preview</title>\n<style>\n'
                 '*{box-sizing:border-box;margin:0;padding:0}\n'
                 'body{background:#111;color:#eee;font-family:Arial,sans-serif;\n'
                 '     display:flex;flex-direction:column;height:100vh;overflow:hidden}\n'
                 '#vwrap{flex:1;display:flex;align-items:center;justify-content:center;\n'
                 '       background:#000;min-height:0;position:relative}\n'
                 'video{width:100%;height:100%;object-fit:contain;display:block}\n'
                 '#hls-status{position:absolute;bottom:8px;left:50%;transform:translateX(-50%);\n'
                 '            background:rgba(0,0,0,.7);color:#aaa;font-size:11px;padding:3px 10px;\n'
                 '            border-radius:3px;pointer-events:none;display:none}\n'
                 '#strip{display:flex;align-items:center;justify-content:center;\n'
                 '       background:#181818;padding:5px 10px;flex-shrink:0;\n'
                 '       border-top:1px solid #2a2a2a}\n'
                 '#stoggle{background:#2a2a2a;color:#aaa;border:1px solid #444;\n'
                 '         padding:3px 16px;border-radius:4px;cursor:pointer;font-size:11px}\n'
                 '#stoggle:hover{background:#3a3a3a;color:#fff}\n'
                 '#ctrl{padding:8px 14px 10px;background:#1c1c1c;flex-shrink:0;\n'
                 '      user-select:none;display:none}\n'
                 '.lbl{font-size:11px;color:#777;margin-bottom:4px}\n'
                 '#seekwrap{position:relative;height:44px;margin-bottom:10px;cursor:pointer}\n'
                 '#seektrack{position:absolute;left:0;right:0;top:32px;height:4px;\n'
                 '           background:#3a3a3a;border-radius:2px}\n'
                 '#seekprog{position:absolute;top:32px;left:0;height:4px;\n'
                 '          background:#666;border-radius:2px}\n'
                 '#seekthumb{position:absolute;top:24px;width:18px;height:18px;\n'
                 '           border-radius:50%;background:#aaa;border:2px solid #fff;\n'
                 '           cursor:grab;transform:translateX(-50%);z-index:4;\n'
                 '           box-shadow:0 1px 4px rgba(0,0,0,.6)}\n'
                 '#seekthumb:active{cursor:grabbing}\n'
                 '#seeklabel{position:absolute;top:2px;transform:translateX(-50%);\n'
                 '           background:#333;color:#fff;font-size:10px;white-space:nowrap;\n'
                 '           padding:2px 5px;border-radius:3px;pointer-events:none;\n'
                 '           border:1px solid #555;z-index:5}\n'
                 '#clipsec{overflow:hidden}\n'
                 '.ci{font-size:11px;color:#1e90ff;margin-left:6px}\n'
                 '#dslider{position:relative;height:24px;margin-bottom:10px;cursor:pointer}\n'
                 '#dtrack{position:absolute;left:0;right:0;top:10px;height:4px;background:#3a3a3a;border-radius:2px}\n'
                 '#dfill{position:absolute;top:10px;height:4px;background:#1e90ff;border-radius:2px}\n'
                 '.dhandle{position:absolute;top:3px;width:18px;height:18px;border-radius:50%;\n'
                 '         background:#1e90ff;border:2px solid #fff;cursor:grab;\n'
                 '         transform:translateX(-50%);z-index:4;box-shadow:0 1px 4px rgba(0,0,0,.5)}\n'
                 '.dhandle:active{cursor:grabbing}\n'
                 '.br{display:flex;gap:6px;align-items:center;flex-wrap:wrap}\n'
                 'button{background:#2a2a2a;color:#ddd;border:1px solid #444;\n'
                 '       padding:4px 11px;border-radius:4px;cursor:pointer;font-size:12px}\n'
                 'button:hover{background:#3a3a3a}\n'
                 '#sbtn{background:#1a4a8e;border-color:#1e90ff;color:#fff}\n'
                 '#sbtn:hover{background:#2060b0}\n'
                 '#tdis{margin-left:auto;font-size:12px;color:#aaa}\n'
                 '</style>\n</head>\n<body>\n'
                 '<div id="vwrap">\n'
                 '  <video id="v" controls preload="auto"></video>\n'
                 '  <div id="hls-status"></div>\n'
                 '</div>\n'
                 '<div id="strip">\n'
                 '  <button id="stoggle" onclick="toggleControls()">&#9650; Show controls</button>\n'
                 '</div>\n'
                 '<div id="ctrl">\n'
                 '  <div class="lbl">Seek</div>\n'
                 '  <div id="seekwrap">\n'
                 '    <div id="seeklabel">0:00.0</div>\n'
                 '    <div id="seektrack"></div>\n'
                 '    <div id="seekprog"></div>\n'
                 '    <div id="seekthumb"></div>\n'
                 '  </div>\n'
                 '  <div style="display:flex;align-items:center;margin-bottom:4px">\n'
                 '    <span class="lbl" style="margin:0">Clip range<span class="ci" id="ci"></span></span>\n'
                 '    <button id="ctoggle" onclick="toggleClip()"\n'
                 '      style="margin-left:8px;font-size:10px;padding:1px 7px;line-height:1.4">&#9660; Hide</button>\n'
                 '  </div>\n'
                 '  <div id="clipsec">\n'
                 '    <div id="dslider">\n'
                 '      <div id="dtrack"></div>\n'
                 '      <div id="dfill"></div>\n'
                 '      <div id="hs" class="dhandle"></div>\n'
                 '      <div id="he" class="dhandle"></div>\n'
                 '    </div>\n'
                 '    <div style="margin-bottom:8px;font-size:12px">\n'
                 '      <label style="opacity:.8">Start</label>\n'
                 '      <input id="cs" type="text" value="00:00:00.00" spellcheck="false"\n'
                 '        style="width:96px;text-align:center;font-family:Consolas,monospace;padding:2px 4px">\n'
                 '      <button onclick="setFromPlayhead(&quot;S&quot;)" title="Use the current playback position"\n'
                 '        style="font-size:11px;padding:3px 7px">&#9673;</button>\n'
                 '      <label style="margin-left:12px;opacity:.8">End</label>\n'
                 '      <input id="ce" type="text" value="00:00:00.00" spellcheck="false"\n'
                 '        style="width:96px;text-align:center;font-family:Consolas,monospace;padding:2px 4px">\n'
                 '      <button onclick="setFromPlayhead(&quot;E&quot;)" title="Use the current playback position"\n'
                 '        style="font-size:11px;padding:3px 7px">&#9673;</button>\n'
                 '      <button onclick="applyBoxes()" style="font-size:11px;padding:3px 9px;margin-left:8px">Apply</button>\n'
                 '      <span style="margin-left:8px;opacity:.55;font-size:11px">HH:MM:SS.ss &#183; Enter applies &#183; &#8593;&#8595; 0.1s, Shift 1s, Ctrl 0.01s</span>\n'
                 '    </div>\n'
                 '    <div style="margin-bottom:8px">\n'
                 '      <button onclick="resetClip()" style="font-size:11px;padding:3px 9px">&#8635; Reset clip range</button>\n'
                 '    </div>\n'
                 '  </div>\n'
                 '  <div class="br">\n'
                 '    <button id="pb" onclick="togglePlay()">&#9654; Play</button>\n'
                 '    <button id="sbtn" onclick="sendClip()">&#10003; Send to Clip</button>\n'
                 '    <span id="tdis">0.0 / 0.0</span>\n'
                 '  </div>\n'
                 '</div>\n'
                 '<script>\n'
                 'const v   = document.getElementById("v");\n'
                 'const ci  = document.getElementById("ci");\n'
                 'const pb  = document.getElementById("pb");\n'
                 'const td  = document.getElementById("tdis");\n'
                 'const ds  = document.getElementById("dslider");\n'
                 'const df  = document.getElementById("dfill");\n'
                 'const hs  = document.getElementById("hs");\n'
                 'const he  = document.getElementById("he");\n'
                 'const sw  = document.getElementById("seekwrap");\n'
                 'const sth = document.getElementById("seekthumb");\n'
                 'const slb = document.getElementById("seeklabel");\n'
                 'const sp  = document.getElementById("seekprog");\n'
                 'const hlsStat = document.getElementById("hls-status");\n'
                 '\n'
                 'const DUR = ' + str(_duration) + ';\n'
                 'const CA  = ' + ('true' if _clip_active else 'false') + ';\n'
                 'const IS  = ' + str(_start_sec) + ';\n'
                 'const IE  = ' + str(_end_sec if _clip_active else _duration) + ';\n'
                 '\n'
                 'let dur = DUR || 1;\n'
                 'let pS = CA ? IS/(DUR||1) : 0.0;\n'
                 'let pE = CA ? IE/(DUR||1) : 1.0;\n'
                 '\n'
                 'function fmt(s){\n'
                 '  s=Math.max(0,s);\n'
                 '  var h=Math.floor(s/3600),m=Math.floor((s%3600)/60),sc=s%60;\n'
                 '  var ss=sc.toFixed(2); if(sc<10) ss="0"+ss;\n'
                 '  if(ss.indexOf("60")===0){ss="00.00"; m+=1; if(m>=60){m-=60;h+=1;}}\n'
                 '  var p=function(n,d){return String(n).padStart(d,"0");};\n'
                 '  return h>0?p(h,2)+":"+p(m,2)+":"+ss:p(m,2)+":"+ss;\n'
                 '}\n'
                 'function clamp01(x){return Math.max(0,Math.min(1,x));}\n'
                 '\n'
                 'v.src = "/video";\n'
                 '\n'
                 'function updateSeekThumb(frac){\n'
                 '  const w=sw.offsetWidth;\n'
                 '  sth.style.left=(frac*w)+"px";\n'
                 '  sp.style.width=(frac*100)+"%";\n'
                 '  slb.style.left=(frac*w)+"px";\n'
                 '  slb.textContent=fmt(frac*dur);\n'
                 '}\n'
                 'let seekDragging=false;\n'
                 'function seekTo(frac){\n'
                 '  frac=clamp01(frac);\n'
                 '  v.currentTime=frac*dur;\n'
                 '  updateSeekThumb(frac);\n'
                 '}\n'
                 'sth.addEventListener("mousedown",function(e){seekDragging=true;e.preventDefault();e.stopPropagation();});\n'
                 'sw.addEventListener("mousedown",function(e){if(e.target===sth)return;const rect=sw.getBoundingClientRect();seekTo((e.clientX-rect.left)/rect.width);});\n'
                 'document.addEventListener("mousemove",function(e){if(!seekDragging)return;const rect=sw.getBoundingClientRect();seekTo((e.clientX-rect.left)/rect.width);});\n'
                 'document.addEventListener("mouseup",function(){seekDragging=false;});\n'
                 '\n'
                 'function updateHandles(){\n'
                 '  const w=ds.offsetWidth,lo=Math.min(pS,pE),hi=Math.max(pS,pE);\n'
                 '  hs.style.left=(pS*w)+"px"; he.style.left=(pE*w)+"px";\n'
                 '  df.style.left=(lo*100)+"%"; df.style.width=((hi-lo)*100)+"%";\n'
                 '  const s=lo*dur,e=hi*dur;\n'
                 '  ci.textContent=" "+_hms(s)+" \\u2192 "+_hms(e)+"  ("+Math.max(0,e-s).toFixed(2)+"s)";\n'
                 '}\n'
                 'let dragging=null;\n'
                 'function startDrag(h,e){dragging=h;e.preventDefault();}\n'
                 'hs.addEventListener("mousedown",e=>startDrag("S",e));\n'
                 'he.addEventListener("mousedown",e=>startDrag("E",e));\n'
                 'document.addEventListener("mousemove",function(e){\n'
                 '  if(!dragging)return;\n'
                 '  const rect=ds.getBoundingClientRect(),p=clamp01((e.clientX-rect.left)/rect.width);\n'
                 '  if(dragging==="S"){pS=p;if(pS>pE-0.001)pS=Math.max(0,pE-0.001);}\n'
                 '  else{pE=p;if(pE<pS+0.001)pE=Math.min(1,pS+0.001);}\n'
                 '  updateHandles();\n'
                 '});\n'
                 'document.addEventListener("mouseup",function(){\n'
                 '  if(!dragging)return; dragging=null;\n'
                 '  const lo=Math.min(pS,pE)*dur,hi=Math.max(pS,pE)*dur;\n'
                 '  if(v.currentTime<lo||v.currentTime>=hi) v.currentTime=lo;\n'
                 '  fetch("/update?start="+lo+"&end="+hi);\n'
                 '});\n'
                 'ds.addEventListener("mousedown",function(e){\n'
                 '  if(e.target===hs||e.target===he)return;\n'
                 '  const rect=ds.getBoundingClientRect(),p=clamp01((e.clientX-rect.left)/rect.width);\n'
                 '  if(Math.abs(p-pS)<=Math.abs(p-pE)){pS=p;if(pS>pE-0.001)pS=Math.max(0,pE-0.001);}\n'
                 '  else{pE=p;if(pE<pS+0.001)pE=Math.min(1,pS+0.001);}\n'
                 '  updateHandles();\n'
                 '});\n'
                 '\n'
                 'v.addEventListener("loadedmetadata",function(){\n'
                 '  dur = DUR || v.duration || 1;\n'
                 '  pS=CA?IS/dur:0.0; pE=CA?IE/dur:1.0;\n'
                 '  v.currentTime=CA?IS:0;\n'
                 '  updateHandles(); updateSeekThumb(CA?IS/dur:0);\n'
                 '});\n'
                 'v.addEventListener("timeupdate",function(){\n'
                 '  updateSeekThumb(v.currentTime/dur);\n'
                 '  td.textContent=fmt(v.currentTime)+" / "+fmt(dur);\n'
                 '  const endT=Math.max(pS,pE)*dur;\n'
                 '  if(v.currentTime>=endT){v.pause();v.currentTime=endT;}\n'
                 '});\n'
                 'v.addEventListener("play", function(){pb.textContent="\\u23F8 Pause";});\n'
                 'v.addEventListener("pause",function(){pb.textContent="\\u25B6 Play";});\n'
                 '\n'
                 'function togglePlay(){\n'
                 '  if(v.paused){\n'
                 '    const endT=Math.max(pS,pE)*dur;\n'
                 '    if(v.currentTime>=endT) v.currentTime=Math.min(pS,pE)*dur;\n'
                 '    v.play();\n'
                 '  } else { v.pause(); }\n'
                 '}\n'
                 'let ctrlVisible=false;\n'
                 'function toggleControls(){\n'
                 '  ctrlVisible=!ctrlVisible;\n'
                 '  document.getElementById("ctrl").style.display=ctrlVisible?"block":"none";\n'
                 '  document.getElementById("stoggle").textContent=ctrlVisible?"\\u25BC Hide controls":"\\u25B2 Show controls";\n'
                 '}\n'
                 'let clipVisible=true;\n'
                 'function toggleClip(){\n'
                 '  const sec=document.getElementById("clipsec"),btn=document.getElementById("ctoggle");\n'
                 '  clipVisible=!clipVisible;\n'
                 '  sec.style.display=clipVisible?"":"none";\n'
                 '  btn.textContent=clipVisible?"\\u25BC Hide":"\\u25B2 Show";\n'
                 '}\n'
                 'function resetClip(){pS=0;pE=1;updateHandles();fetch("/update?start=0&end="+dur);}\n'
                 'function sendClip(){fetch("/update?start="+Math.min(pS,pE)*dur+"&end="+Math.max(pS,pE)*dur);}\n'
                 '\n'
                 'function _hms(t){t=Math.max(0,t||0);\n'
                 '  var h=Math.floor(t/3600),m=Math.floor((t%3600)/60),s=t%60;\n'
                 '  var ss=s.toFixed(2); if(s<10) ss="0"+ss;\n'
                 '  if(ss.indexOf("60")===0){ss="00.00"; m+=1; if(m>=60){m-=60;h+=1;}}\n'
                 '  return (h<10?"0":"")+h+":"+(m<10?"0":"")+m+":"+ss;}\n'
                 'function _parseHMS(x){var p=String(x||"").trim().split(":"),v;\n'
                 '  if(p.length===3){v=(+p[0])*3600+(+p[1])*60+parseFloat(p[2]);}\n'
                 '  else if(p.length===2){v=(+p[0])*60+parseFloat(p[1]);}\n'
                 '  else {v=parseFloat(p[0]);}\n'
                 '  return isNaN(v)?null:v;}\n'
                 'function syncBoxes(){var a=document.getElementById("cs"),b=document.getElementById("ce");\n'
                 '  if(!a||!b)return;\n'
                 '  if(document.activeElement!==a) a.value=_hms(Math.min(pS,pE)*dur);\n'
                 '  if(document.activeElement!==b) b.value=_hms(Math.max(pS,pE)*dur);}\n'
                 'function applyBoxes(){\n'
                 '  var s=_parseHMS(document.getElementById("cs").value);\n'
                 '  var e=_parseHMS(document.getElementById("ce").value);\n'
                 '  if(s===null||e===null){syncBoxes();return;}\n'
                 '  s=Math.max(0,Math.min(s,dur)); e=Math.max(0,Math.min(e,dur));\n'
                 '  if(e<=s) e=Math.min(dur,s+0.05);\n'
                 '  pS=s/dur; pE=e/dur; updateHandles();\n'
                 '  if(v.currentTime<s||v.currentTime>=e) v.currentTime=s;\n'
                 '  fetch("/update?start="+s+"&end="+e);}\n'
                 'function setFromPlayhead(w){\n'
                 '  var t=v.currentTime;\n'
                 '  if(w==="S"){document.getElementById("cs").value=_hms(t);}\n'
                 '  else {document.getElementById("ce").value=_hms(t);}\n'
                 '  applyBoxes();}\n'
                 'var _origUH=updateHandles;\n'
                 'updateHandles=function(){_origUH.apply(this,arguments); syncBoxes();};\n'
                 '["cs","ce"].forEach(function(id){\n'
                 '  var el=document.getElementById(id); if(!el)return;\n'
                 '  el.addEventListener("keydown",function(ev){\n'
                 '    if(ev.key==="Enter"){ev.preventDefault();applyBoxes();el.blur();}\n'
                 '    else if(ev.key==="ArrowUp"||ev.key==="ArrowDown"){\n'
                 '      ev.preventDefault();\n'
                 '      var t=_parseHMS(el.value); if(t===null)return;\n'
                 '      var step=ev.ctrlKey?0.01:(ev.shiftKey?1:0.1);\n'
                 '      el.value=_hms(t+(ev.key==="ArrowUp"?step:-step)); applyBoxes();}\n'
                 '  });\n'
                 '  el.addEventListener("blur",applyBoxes);\n'
                 '  el.addEventListener("focus",function(){el.select();});\n'
                 '});\n'
                 'updateHandles(); updateSeekThumb(0);\n'
                 'window.addEventListener("resize",function(){updateHandles();updateSeekThumb(v.currentTime/dur);});\n'
                 '</script>\n</body>\n</html>')

        # ── 5. HTTP server ────────────────────────────────────────────────────
        class _Handler(http.server.BaseHTTPRequestHandler):
            def log_message(self, fmt, *args):
                pass

            def do_GET(self):
                parsed = _urlparse.urlparse(self.path)
                path   = parsed.path

                if path == '/':
                    body = _html.encode('utf-8')
                    self.send_response(200)
                    self.send_header('Content-Type', 'text/html; charset=utf-8')
                    self.send_header('Content-Length', str(len(body)))
                    self.end_headers()
                    self.wfile.write(body)

                elif path == '/video':
                    if _direct_url:
                        self.send_response(302)
                        self.send_header('Location', _direct_url)
                        self.end_headers()
                    elif _pipe_video_url:
                        self._serve_pipe()
                    else:
                        self._serve_file(_video_path)

                elif path == '/update':
                    params = _urlparse.parse_qs(parsed.query)
                    try:
                        _s = float(params.get('start', ['0'])[0])
                        _e = float(params.get('end',   ['0'])[0])
                        def _sec_fmt(sec):
                            sec=max(0.0,float(sec)); h=int(sec//3600)
                            m=int((sec%3600)//60); s=sec%60
                            return str(h).zfill(2)+':'+str(m).zfill(2)+':'+'{:05.2f}'.format(s)
                        def _apply():
                            _app_ref._clip_start_var.set(_sec_fmt(_s))
                            _app_ref._clip_end_var.set(_sec_fmt(_e))
                            if not getattr(_app_ref, '_m_clip_on', False):
                                _app_ref._clip_enabled_var.set(True)
                                _fn = getattr(_app_ref, '_on_clip_toggle_fn', None)
                                if _fn: _fn()
                        _app_ref.root.after(0, _apply)
                    except Exception:
                        pass
                    self.send_response(200)
                    self.send_header('Content-Type', 'text/plain')
                    self.end_headers()
                    self.wfile.write(b'ok')

                else:
                    self.send_response(404)
                    self.end_headers()

            def _serve_pipe(self):
                """Pipe two CDN streams through FFmpeg into fragmented WebM."""
                try:
                    self.send_response(200)
                    self.send_header('Content-Type', 'video/webm')
                    self.send_header('Cache-Control', 'no-cache')
                    self.end_headers()
                    _ffcmd = [
                        _app_ref.ffmpeg_path, '-y',
                        '-i', _pipe_video_url,
                        '-i', _pipe_audio_url,
                        '-c:v', 'copy',
                        '-c:a', 'libopus', '-b:a', '128k',
                        '-f', 'webm',
                        'pipe:1'
                    ]
                    _proc = subprocess.Popen(
                        _ffcmd,
                        stdout=subprocess.PIPE,
                        stderr=subprocess.DEVNULL,
                        creationflags=CREATE_NO_WINDOW)
                    try:
                        while True:
                            chunk = _proc.stdout.read(65536)
                            if not chunk:
                                break
                            self.wfile.write(chunk)
                            self.wfile.flush()
                    finally:
                        _proc.kill()
                except Exception:
                    pass

            def _serve_file(self, path):
                """Serve a complete local file with Range support."""
                try:
                    fsize = os.path.getsize(path)
                    rng   = self.headers.get('Range', None)
                    if rng:
                        m = _re.match(r'bytes=(\d+)-(\d*)', rng)
                        if m:
                            bstart = int(m.group(1))
                            bend   = int(m.group(2)) if m.group(2) else fsize - 1
                            bend   = min(bend, fsize - 1)
                            blen   = bend - bstart + 1
                            self.send_response(206)
                            self.send_header('Content-Range',
                                'bytes '+str(bstart)+'-'+str(bend)+'/'+str(fsize))
                            self.send_header('Content-Length', str(blen))
                            self.send_header('Content-Type', 'video/mp4')
                            self.send_header('Accept-Ranges', 'bytes')
                            self.end_headers()
                            with open(path, 'rb') as fv:
                                fv.seek(bstart)
                                rem = blen
                                while rem:
                                    chunk = fv.read(min(65536, rem))
                                    if not chunk: break
                                    self.wfile.write(chunk)
                                    rem -= len(chunk)
                    else:
                        self.send_response(200)
                        self.send_header('Content-Type', 'video/mp4')
                        self.send_header('Content-Length', str(fsize))
                        self.send_header('Accept-Ranges', 'bytes')
                        self.end_headers()
                        with open(path, 'rb') as fv:
                            while True:
                                chunk = fv.read(65536)
                                if not chunk: break
                                self.wfile.write(chunk)
                except Exception:
                    self.send_response(500)
                    self.end_headers()

        # M4 fix: shut down any previous preview server so repeated Preview
        # clicks don't leak listening sockets and threads for the session.
        _old_srv = getattr(self, '_preview_srv', None)
        if _old_srv is not None:
            try:
                _old_srv.shutdown()
                _old_srv.server_close()
            except Exception:
                pass
        # M4 fix: ThreadingHTTPServer - the plain HTTPServer handles one
        # request at a time, so while the browser held the long-lived /video
        # stream open, the /update calls behind "Send to Clip" starved.
        _srv = http.server.ThreadingHTTPServer(('127.0.0.1', _port), _Handler)
        _srv.daemon_threads = True
        self._preview_srv = _srv
        threading.Thread(target=_srv.serve_forever, daemon=True).start()
        self.append_terminal_output(
            'Preview server on port ' + str(_port) + '\n', 'info')
        webbrowser.open('http://127.0.0.1:' + str(_port) + '/')


    def test_network_connectivity(self):
        """Test basic connectivity to YouTube and show results in terminal."""
        self.append_terminal_output("Running network connectivity test...\n", "info")
        results = []

        try:
            ip = _original_getaddrinfo("www.youtube.com", 443, 0, 1, 6)[0][4][0]
            results.append(("System DNS  www.youtube.com", True, ip))
        except Exception as e:
            results.append(("System DNS  www.youtube.com", False, str(e)))

        try:
            s = socket.create_connection(("www.youtube.com", 443), timeout=5)
            s.close()
            results.append(("TCP :443    www.youtube.com", True, "OK"))
        except Exception as e:
            results.append(("TCP :443    www.youtube.com", False, str(e)))

        try:
            s = socket.create_connection(("googlevideo.com", 443), timeout=5)
            s.close()
            results.append(("TCP :443    googlevideo.com", True, "OK"))
        except Exception as e:
            results.append(("TCP :443    googlevideo.com", False, str(e)))

        try:
            r, _ = _dns_query("www.youtube.com", _primary_dns, timeout=3)
            if r:
                results.append(("Google DNS  8.8.8.8:53", True, r))
            else:
                results.append(("Google DNS  8.8.8.8:53", False, "No response"))
        except Exception as e:
            results.append(("Google DNS  8.8.8.8:53", False, str(e)))

        try:
            res = subprocess.run(
                self._ytdlp_head() + ["--version"],
                capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=5,
                creationflags=CREATE_NO_WINDOW)
            if res.returncode == 0:
                results.append(("yt-dlp binary", True, res.stdout.strip()))
            else:
                results.append(("yt-dlp binary", False, res.stderr.strip()))
        except Exception as e:
            results.append(("yt-dlp binary", False, str(e)))

        self.append_terminal_output("-" * 55 + "\n", "info")
        all_ok = True
        for label, ok, detail in results:
            icon = "[OK]  " if ok else "[FAIL]"
            tag = "success" if ok else "error"
            self.append_terminal_output(icon + " " + label + "  " + detail + "\n", tag)
            if not ok:
                all_ok = False

        self.append_terminal_output("-" * 55 + "\n", "info")
        if all_ok:
            self.append_terminal_output("All connectivity checks passed.\n\n", "success")
        else:
            self.append_terminal_output(
                "One or more checks FAILED.\n"
                "If TCP checks fail: your firewall is blocking yt-dlp network access.\n"
                "Solution: add yt-dlp.exe as an allowed application in your firewall.\n"
                "If only DNS fails: custom DNS is blocked but downloads may still work.\n\n",
                "warning")

    def _show_dns_status_in_terminal(self):
        """Show DNS and toggle status in the terminal on startup."""
        if self.custom_dns_enabled.get():
            self.append_terminal_output(
                "Custom DNS: ACTIVE - local proxy started on port " + str(_proxy_port or 0) + " (Google DNS 8.8.8.8)\n",
                "success")
        else:
            self.append_terminal_output(
                "Custom DNS: INACTIVE (using system DNS)\n", "info")
        # Make the yt-dlp stub impossible to miss: with --noconsole the
        # startup print() goes nowhere, so an override that silently failed to
        # apply looked exactly like one that worked.
        try:
            _ov = (os.environ.get('YSA_YTDLP_PATH') or '').strip().strip('"')
            if _ov and os.path.normcase(os.path.abspath(_ov)) == \
                    os.path.normcase(os.path.abspath(str(self.ytdlp_path or ''))):
                self.append_terminal_output(
                    "*** TEST STUB ACTIVE *** yt-dlp is overridden by "
                    + _ov + "\n    mode: "
                    + (os.environ.get('YSA_FAKE_MODE') or 'ok')
                    + "   (unset YSA_YTDLP_PATH to use the real yt-dlp)\n",
                    "warning")
            elif _ov:
                self.append_terminal_output(
                    "YSA_YTDLP_PATH is set to '" + _ov + "' but was NOT used"
                    " - the path does not exist. Using " + str(self.ytdlp_path)
                    + "\n", "warning")
        except Exception:
            pass
        self.append_terminal_output(
            "Embed Metadata: " + ("ON" if self.embed_metadata_enabled.get() else "OFF") + "\n", "info")
        self.append_terminal_output(
            "Audio Only Mode: " + ("ON (MP3 output)" if self.audio_only_mode.get() else "OFF") + "\n", "info")
        # Show cookie status. The toolbar toggle gates what is actually
        # SENT (get_ytdlp_cookies_args returns [] while it is off), so
        # this banner must report the toggle, not just what sits on
        # disk - it used to claim 'cookies.txt (today)' in green while
        # cookies were deliberately disabled to rest a flagged account.
        _ck_on = getattr(self, '_m_cookies_on',
                         getattr(self, 'cookies_enabled', True))
        _cf = getattr(self, "cookies_file", "") or ""
        _ck_browser = getattr(self, "cookies_browser", "none") or "none"
        if not _ck_on and (_cf or _ck_browser != "none"):
            _what = (os.path.basename(_cf) if _cf
                     else "browser=" + _ck_browser)
            self.append_terminal_output(
                "Cookies: OFF (toolbar toggle) - " + _what
                + " is configured but NOT sent.\n", "warning")
        elif _cf and os.path.isfile(_cf):
            try:
                _age_d = int((time.time() - os.path.getmtime(_cf)) / 86400)
                _age_str = ("today" if _age_d == 0 else str(_age_d) + "d old")
                _col = "success" if _age_d < 7 else "warning"
                self.append_terminal_output(
                    "Cookies: " + os.path.basename(_cf) + " (" + _age_str + ")\n", _col)
            except Exception:
                self.append_terminal_output("Cookies: " + os.path.basename(_cf) + "\n", "success")
        else:
            _browser = getattr(self, "cookies_browser", "none") or "none"
            if _browser != "none":
                self.append_terminal_output("Cookies: browser=" + _browser + "\n", "info")
            else:
                self.append_terminal_output(
                    "Cookies: NONE - bot-check errors likely. Add cookies.txt in Settings.\n", "warning")
        # bgutil status, autostart and the yt-dlp diagnostic run on a
        # worker: probing the server blocks up to 2 x 0.6s when it is
        # down (urlopen ping, then the TCP fallback), and root.after
        # callbacks run on the main thread. Same pattern as the Settings
        # probe (_refresh_bgutil_status, test 42) and the diagnostic
        # thread that already lived inside this block.
        threading.Thread(target=self._bgutil_startup_status,
                         daemon=True).start()

    def _bgutil_startup_status(self):
        """bgutil startup status + optional autostart + yt-dlp diagnostic.

        Runs on a daemon thread: _bgutil_check_server() blocks up to 0.6s
        twice when the server is down, which stalled the UI at every
        launch while this ran inside a root.after callback. Safe off the
        main thread: every terminal write goes through
        append_terminal_output, whose guard marshals back to the main
        thread; _bgutil_check_plugin() only touches the filesystem; and
        _bgutil_running defaults to False in __init__, so an info fetch
        racing this probe takes the extended-cascade path it would take
        anyway while the server is down.
        """
        # bgutil PO token provider status
        # Auto-start bgutil server if configured
        _bgutil_plugin_ok = self._bgutil_check_plugin()
        _bgutil_server_ok = self._bgutil_check_server()
        self._bgutil_running = _bgutil_server_ok
        if not _bgutil_server_ok and getattr(self, 'bgutil_autostart', False):
            self.append_terminal_output(
                'bgutil: auto-starting server...\n', 'info')
            def _autostart():
                ok = self._bgutil_start_server()
                if ok:
                    self._bgutil_running = True
                    self.root.after(0, lambda: self.append_terminal_output(
                        'bgutil: server auto-started.\n', 'success'))
                else:
                    self.root.after(0, lambda: self.append_terminal_output(
                        'bgutil: auto-start failed - check Settings > bgutil.\n', 'warning'))
            threading.Thread(target=_autostart, daemon=True).start()
            _bgutil_server_ok = True  # optimistic - server starting
        elif _bgutil_server_ok and getattr(self, 'bgutil_autostart', False):
            self.append_terminal_output(
                'bgutil: server already running (no restart needed).\n', 'info')
        if _bgutil_server_ok and _bgutil_plugin_ok:
            self.append_terminal_output(
                'bgutil: Server RUNNING + Plugin INSTALLED - PO tokens active.\n', 'success')
        elif _bgutil_server_ok and not _bgutil_plugin_ok:
            self.append_terminal_output(
                'bgutil: Server RUNNING but plugin not found in yt-dlp-plugins/.\n', 'warning')
        elif not _bgutil_server_ok and _bgutil_plugin_ok:
            self.append_terminal_output(
                'bgutil: Plugin installed but server NOT running - start in Settings > bgutil.\n', 'warning')
        else:
            self.append_terminal_output(
                'bgutil: Not configured (optional). See Settings > bgutil for setup.\n', 'info')
        # ── Quick diagnostic: verify yt-dlp actually sees the plugin + JS runtime ──
        # Runs in a background thread so startup messages appear instantly.
        # The probe spawns a yt-dlp subprocess that loads 1864 extractors,
        # which takes 2-4 seconds - too slow for the main thread.
        if _bgutil_plugin_ok:
            def _run_diagnostic():
                self._diagnose_ytdlp_environment()
                self.append_terminal_output("-" * 50 + "\n", "info")
            threading.Thread(target=_run_diagnostic, daemon=True).start()
        else:
            self.append_terminal_output("-" * 50 + "\n", "info")

    def _dns_warmup_notify(self):
        """Background DNS warm-up for the Settings toggle (see _on_dns_toggle)."""
        if not _dns_probe_and_warm():
            self.root.after(0, lambda: self.append_terminal_output(
                "WARNING: Google DNS (8.8.8.8) did not respond - downloads may"
                " stall. Turn Custom DNS off in Settings if this persists.\n",
                "warning"))

    def _on_dns_toggle(self):
        """Enable or disable custom DNS when checkbox toggled."""
        if self.custom_dns_enabled.get():
            enable_custom_dns(probe=False)
            dns_ok = True
            threading.Thread(target=self._dns_warmup_notify, daemon=True).start()
            if dns_ok:
                self.append_terminal_output(
                    "Custom DNS ENABLED - local proxy on port " + str(_proxy_port or 0) +
                    " (Google DNS 8.8.8.8)\n", "success")
                self.status_var.set("Custom DNS enabled")
            else:
                # Google DNS unreachable - warn loudly so user knows to turn it off
                self.append_terminal_output(
                    "Custom DNS ENABLED but Google DNS (8.8.8.8) is UNREACHABLE on this network.\n"
                    "The proxy will stall and make downloads fail. Recommendation: turn Custom DNS OFF.\n",
                    "warning")
                self.status_var.set("Custom DNS: WARNING - Google DNS unreachable")
        else:
            disable_custom_dns()
            self.append_terminal_output(
                "Custom DNS DISABLED (using system DNS)\n", "info")
            self.status_var.set("Custom DNS disabled")
        self.custom_dns = self.custom_dns_enabled.get()
        self._save_config()

    def _on_audio_only_toggle(self):
        """Update UI hint when audio-only mode is toggled; refresh sizes in recommended tree."""
        fmt_raw = getattr(self, 'audio_only_format', 'm4a_native')
        fmt_label = {'m4a_native': 'M4A Native', 'm4a_aac': 'M4A AAC', 'mp3': 'MP3'}.get(fmt_raw, fmt_raw.upper())
        if self.audio_only_mode.get():
            self.append_terminal_output(
                'Audio Only mode ON - output format: ' + fmt_label + '\n', 'info')
            self.status_var.set('Audio Only mode enabled (' + fmt_label + ')')
        else:
            self.append_terminal_output(
                'Audio Only mode OFF - full video download\n', 'info')
            self.status_var.set('Audio Only mode disabled')
        if self.current_formats:
            self._populate_recommended_combinations(suppress_auto_download=True)

    def _on_audio_format_changed(self):
        """Persist format choice and update status when format selector changes."""
        fmt_var = getattr(self, '_audio_format_var', None)
        if fmt_var:
            # Normalise display value back to internal key
            _display = fmt_var.get().lower().replace(' ', '_')
            self.audio_only_format = _display
            # Keep combobox showing canonical display value
            _display_map = {'m4a_native': 'M4A NATIVE', 'm4a_aac': 'M4A AAC', 'mp3': 'MP3'}
            fmt_var.set(_display_map.get(_display, fmt_var.get().upper()))
            self._save_config()
            if self.audio_only_mode.get():
                fmt_label = {'m4a_native': 'M4A Native', 'm4a_aac': 'M4A AAC', 'mp3': 'MP3'}.get(_display, _display)
                self.status_var.set('Audio Only mode enabled (' + fmt_label + ')')
                self.append_terminal_output('Audio format set to ' + fmt_label + '\n', 'info')

    # ── Config persistence ─────────────────────────────────────────────────

    def _apply_saved_geometry(self, default_geom):
        """Restore the window size/position saved at the last clean exit.

        Guarded: a saved position from a monitor that is no longer attached
        (or a resolution change) can put the window somewhere unreachable,
        so anything that would land off-screen falls back to the default
        rather than leaving a window that cannot be dragged into view."""
        geom = getattr(self, 'window_geometry', '') or ''
        if not getattr(self, 'remember_window', True) or not geom:
            self.root.geometry(default_geom)
            return
        try:
            _m = re.match(r'^(\d+)x(\d+)([+-]\d+)([+-]\d+)$', geom.strip())
            if not _m:
                self.root.geometry(default_geom)
                return
            w, h = int(_m.group(1)), int(_m.group(2))
            x, y = int(_m.group(3)), int(_m.group(4))
            sw = self.root.winfo_screenwidth()
            sh = self.root.winfo_screenheight()
            # winfo_screenwidth is the PRIMARY monitor only, so a window on a
            # second screen looked "off-screen" and got re-centred every time.
            # The virtual root covers the whole desktop, including monitors
            # left of or above the primary one (negative origin).
            try:
                vx, vy = self.root.winfo_vrootx(), self.root.winfo_vrooty()
                vw = max(sw, self.root.winfo_vrootwidth())
                vh = max(sh, self.root.winfo_vrootheight())
            except Exception:
                vx, vy, vw, vh = 0, 0, sw, sh
            w = max(700, min(w, vw))
            h = max(500, min(h, vh))
            # Negative coordinates cannot be restored: Tk reads a leading '-'
            # in a geometry string as "distance from the RIGHT/BOTTOM edge",
            # not as a negative position, so a window on a monitor left of or
            # above the primary one would be placed somewhere else entirely.
            # Those re-centre; monitors to the right/below use plain positive
            # coordinates and restore exactly.
            if (x < 0 or y < 0
                    or x > vx + vw - 120 or y > vy + vh - 80):
                x = max(0, (vw - w) // 2 if vx >= 0 else (sw - w) // 2)
                y = max(0, (vh - h) // 3 if vy >= 0 else (sh - h) // 3)
            _geom = str(w) + 'x' + str(h) + '+' + str(x) + '+' + str(y)
            self.root.geometry(_geom)

            # Windows usually ignores a POSITION set before the window is
            # mapped - the size sticks but the WM places the window itself,
            # which is why size persisted and position never did. Re-apply
            # once the event loop is running and the window really exists.
            def _reapply_geom():
                try:
                    if (self.root.winfo_exists()
                            and not getattr(self, 'window_maximized', False)):
                        self.root.geometry(_geom)
                except Exception:
                    pass
            try:
                self.root.after(120, _reapply_geom)
            except Exception:
                pass

            if getattr(self, 'window_maximized', False):
                try:
                    self.root.after(150, lambda: self.root.state('zoomed'))
                except Exception:
                    pass
        except Exception:
            self.root.geometry(default_geom)

    def _capture_window_geometry(self):
        """Remember the window box. Maximized state is stored separately -
        a zoomed window reports a geometry string that restores badly."""
        try:
            if not getattr(self, 'remember_window', True):
                return
            _zoomed = False
            try:
                _zoomed = (self.root.state() == 'zoomed')
            except Exception:
                pass
            self.window_maximized = _zoomed
            if not _zoomed:
                self.root.update_idletasks()
                self.window_geometry = self.root.geometry()
        except Exception:
            pass

    def _reset_window_geometry(self):
        self.window_geometry = ''
        self.window_maximized = False
        try:
            self.root.state('normal')
        except Exception:
            pass
        self.root.geometry("1000x1100")
        self._save_config_now()
        self._notify_info("Window", "Window size and position reset.")

    def _cfg_get(self, cfg, key, current, cast=None):
        """Read ONE config key defensively; never let it poison the rest.

        The loader used to be a single try block: one bad value (a string
        where an int was expected, a hand-edit typo, a half-written file)
        raised, and every setting AFTER that line silently reverted to its
        default. With the settings count growing, that failure mode gets
        worse, so each key now stands alone - a bad one keeps its previous
        value and is reported, and its neighbours are untouched."""
        if key not in cfg:
            return current
        try:
            val = cfg[key]
            if cast is not None:
                val = cast(val)
            return val
        except Exception:
            try:
                self._cfg_bad_keys.append(key)
            except Exception:
                pass
            return current

    def _load_config(self):
        """Load persistent configuration from ysa_config.json."""
        self._cfg_bad_keys = []
        config_file = os.path.join(SCRIPT_DIR, getattr(self, 'config_filename', 'ysa_config.json'))
        if not os.path.exists(config_file):
            return
        try:
            with open(config_file, 'r') as f:
                cfg = json.load(f)
            self.download_path = self._cfg_get(cfg, 'download_path', self.download_path)
            self.default_quality = self._cfg_get(cfg, 'default_quality', self.default_quality)
            self.dark_mode = self._cfg_get(cfg, 'dark_mode', self.dark_mode)
            self.persistent_cache = self._cfg_get(cfg, 'persistent_cache', self.persistent_cache)
            self.max_cache_mb = self._cfg_get(cfg, 'max_cache_mb', self.max_cache_mb, int)
            self.preferred_language = self._cfg_get(cfg, 'preferred_language', self.preferred_language)
            self.auto_update_tools = self._cfg_get(cfg, 'auto_update_tools', self.auto_update_tools, bool)
            self.ytdlp_channel = self._cfg_get(cfg, 'ytdlp_channel', 'nightly', str)
            self.size_limit_enabled = self._cfg_get(cfg, 'size_limit_enabled', self.size_limit_enabled, bool)
            self.size_limit_mb = self._cfg_get(cfg, 'size_limit_mb', self.size_limit_mb, int)
            self.size_limit_fallback = self._cfg_get(cfg, 'size_limit_fallback', self.size_limit_fallback)
            self.size_upgrade_enabled = self._cfg_get(cfg, 'size_upgrade_enabled', self.size_upgrade_enabled, bool)
            self.size_upgrade_to = self._cfg_get(cfg, 'size_upgrade_to', self.size_upgrade_to)
            self.player_client = self._cfg_get(cfg, 'player_client', self.player_client)
            self.prewarm_enabled = self._cfg_get(cfg, 'prewarm_enabled', self.prewarm_enabled, bool)
            self.parallel_hardsub = self._cfg_get(cfg, 'parallel_hardsub', self.parallel_hardsub, bool)
            self.hardsub_encoder = self._cfg_get(cfg, 'hardsub_encoder', 'libx264', str)
            self.clear_cache_on_exit = self._cfg_get(cfg, 'clear_cache_on_exit', self.clear_cache_on_exit, bool)
            self.preserve_logs_on_clear = self._cfg_get(cfg, 'preserve_logs_on_clear', True, bool)
            self.preserve_ytdlp_on_clear = self._cfg_get(cfg, 'preserve_ytdlp_on_clear', False, bool)
            self.preserve_history_on_clear = self._cfg_get(cfg, 'preserve_history_on_clear', False, bool)
            self.advance_queue_on_streams_done = self._cfg_get(cfg, 'advance_queue_on_streams_done', self.advance_queue_on_streams_done, bool)
            self.precache_concurrent_count = self._cfg_get(cfg, 'precache_concurrent_count', self.precache_concurrent_count, lambda v: max(1, int(v)))
            self.batch_concurrent_fetches = self._cfg_get(cfg, 'batch_concurrent_fetches', getattr(self, 'batch_concurrent_fetches', 3), lambda v: max(1, min(8, int(v))))
            self.clipboard_watch = self._cfg_get(cfg, 'clipboard_watch', self.clipboard_watch, bool)
            self.batch_start_immediately = self._cfg_get(cfg, 'batch_start_immediately', self.batch_start_immediately, bool)
            self.terminal_expanded = self._cfg_get(cfg, 'terminal_expanded', self.terminal_expanded, bool)
            self.custom_dns = self._cfg_get(cfg, 'custom_dns', self.custom_dns, bool)
            self.filename_include_date = self._cfg_get(cfg, 'filename_include_date', self.filename_include_date, bool)
            self.filename_format = self._cfg_get(cfg, 'filename_format', self.filename_format, str)
            self.cookies_browser = self._cfg_get(cfg, 'cookies_browser', self.cookies_browser, str)
            self.cookies_file = self._cfg_get(cfg, 'cookies_file', self.cookies_file, str)
            # Resolve relative cookie paths against SCRIPT_DIR so they survive
            # working-directory changes (e.g. from file-browse dialogs on Windows).
            if self.cookies_file and not os.path.isabs(self.cookies_file):
                self.cookies_file = os.path.join(SCRIPT_DIR, self.cookies_file)
            self.cookies_enabled = self._cfg_get(cfg, 'cookies_enabled', getattr(self, 'cookies_enabled', True), bool)
            self.bgutil_server_url = self._cfg_get(cfg, 'bgutil_server_url', self.bgutil_server_url, str)
            self.bgutil_server_path = self._cfg_get(cfg, 'bgutil_server_path', self.bgutil_server_path, str)
            self.bgutil_autostart = self._cfg_get(cfg, 'bgutil_autostart', self.bgutil_autostart, bool)
            self.bgutil_keep_running = self._cfg_get(cfg, 'bgutil_keep_running', getattr(self, 'bgutil_keep_running', True), bool)
            self.extended_client_cascade = self._cfg_get(cfg, 'extended_client_cascade', self.extended_client_cascade, bool)
            self.meta_embed_title = self._cfg_get(cfg, 'meta_embed_title', self.meta_embed_title, bool)
            self.meta_embed_artist = self._cfg_get(cfg, 'meta_embed_artist', self.meta_embed_artist, bool)
            self.meta_embed_date = self._cfg_get(cfg, 'meta_embed_date', self.meta_embed_date, bool)
            self.meta_embed_comment = self._cfg_get(cfg, 'meta_embed_comment', self.meta_embed_comment, bool)
            self.meta_embed_synopsis = self._cfg_get(cfg, 'meta_embed_synopsis', self.meta_embed_synopsis, bool)
            self.embed_metadata = self._cfg_get(cfg, 'embed_metadata', self.embed_metadata, bool)
            # Legacy migration: embed_subtitles bool -> subtitle_source
            try:
                _legacy_embed = cfg.get('embed_subtitles', None)
                self.subtitle_source = cfg.get('subtitle_source',
                    ('manual' if _legacy_embed else 'off') if _legacy_embed is not None
                    else self.subtitle_source)
            except Exception:
                self._cfg_bad_keys.append('subtitle_source')
            # subtitle_last_source remembers the combo selection even when toggle is off.
            # Migration: if no saved value, derive from subtitle_source (if it's not 'off').
            _default_last_src = self.subtitle_source if self.subtitle_source != 'off' else self.subtitle_last_source
            self.subtitle_last_source = self._cfg_get(cfg, 'subtitle_last_source', _default_last_src)
            self.subtitle_mode = self._cfg_get(cfg, 'subtitle_mode', self.subtitle_mode)
            self.subtitle_lang = self._cfg_get(cfg, 'subtitle_lang', self.subtitle_lang)
            self.preferred_audio_bitrate = self._cfg_get(cfg, 'preferred_audio_bitrate', self.preferred_audio_bitrate, int)
            self.preferred_video_bitrate = self._cfg_get(cfg, 'preferred_video_bitrate', self.preferred_video_bitrate, int)
            self.include_hls_streams = self._cfg_get(cfg, 'include_hls_streams', False, bool)
            self.reuse_info_json = self._cfg_get(cfg, 'reuse_info_json', True, bool)
            self.audio_only_mode_default = self._cfg_get(cfg, 'audio_only_mode', self.audio_only_mode_default, bool)
            self.audio_only_format = self._cfg_get(cfg, 'audio_only_format', getattr(self, 'audio_only_format', 'm4a_native'))
            self.audio_opus_naming = self._cfg_get(cfg, 'audio_opus_naming', self.audio_opus_naming, str)
            self.audio_bitrate_policy = self._cfg_get(cfg, 'audio_bitrate_policy', self.audio_bitrate_policy, str)
            self.audio_fixed_bitrate = self._cfg_get(cfg, 'audio_fixed_bitrate', self.audio_fixed_bitrate, lambda v: max(32, min(320, int(v))))
            self.audio_drc_pref = self._cfg_get(cfg, 'audio_drc_pref', self.audio_drc_pref, str)
            self.audio_quality_tag = self._cfg_get(cfg, 'audio_quality_tag', self.audio_quality_tag, str)
            self.audio_no_aac_action = self._cfg_get(cfg, 'audio_no_aac_action', self.audio_no_aac_action, str)
            self.audio_cache_streams = self._cfg_get(cfg, 'audio_cache_streams', self.audio_cache_streams, bool)
            self.audio_output_folder = self._cfg_get(cfg, 'audio_output_folder', self.audio_output_folder, str)
            self.audio_duplicate_action = self._cfg_get(cfg, 'audio_duplicate_action', self.audio_duplicate_action, str)
            self.history_enabled = self._cfg_get(cfg, 'history_enabled', self.history_enabled, bool)
            self.remember_window = self._cfg_get(cfg, 'remember_window', self.remember_window, bool)
            self.window_geometry = self._cfg_get(cfg, 'window_geometry', self.window_geometry, str)
            self.window_maximized = self._cfg_get(cfg, 'window_maximized', self.window_maximized, bool)
            # Migrate old 'm4a' value to 'm4a_native'
            if self.audio_only_format == 'm4a':
                self.audio_only_format = 'm4a_native'
            # Sync the combobox if UI already built
            if hasattr(self, '_audio_format_var'):
                _dm = {'m4a_native': 'M4A NATIVE', 'm4a_aac': 'M4A AAC', 'mp3': 'MP3'}
                self._audio_format_var.set(_dm.get(self.audio_only_format, self.audio_only_format.upper()))
        except Exception as e:
            print('Could not load config: ' + str(e))
        if getattr(self, '_cfg_bad_keys', None):
            print('Config: kept previous values for unreadable keys: '
                  + ', '.join(self._cfg_bad_keys))
        # Load download history from separate file
        self._load_download_history()

    def _save_config(self):
        """Save persistent configuration to ysa_config.json.
        Debounced: rapid successive calls collapse into a single write
        500ms after the last call, preventing disk thrash on rapid UI changes."""
        if getattr(self, '_save_config_after_id', None):
            try:
                self.root.after_cancel(self._save_config_after_id)
            except Exception:
                pass
        self._save_config_after_id = self.root.after(500, self._save_config_now)

    def _save_config_now(self):
        """Save persistent configuration to ysa_config.json."""
        config_file = os.path.join(SCRIPT_DIR, getattr(self, 'config_filename', 'ysa_config.json'))
        try:
            pvar = getattr(self, 'persistent_cache_var', None)
            dmvar = getattr(self, 'dark_mode_var', None)
            cfg = {
                'download_path': self.download_path,
                'default_quality': self.default_quality,
                'dark_mode': dmvar.get() if dmvar else self.dark_mode,
                'persistent_cache': pvar.get() if pvar else self.persistent_cache,
                'clear_cache_on_exit': self.clear_cache_on_exit,
                'preserve_logs_on_clear': self.preserve_logs_on_clear,
                'preserve_ytdlp_on_clear': self.preserve_ytdlp_on_clear,
                'preserve_history_on_clear': self.preserve_history_on_clear,
                'max_cache_mb': self.max_cache_mb,
                'preferred_language': self.preferred_language,
                'auto_update_tools': self.auto_update_tools,
                'ytdlp_channel': self.ytdlp_channel,
                'size_limit_enabled': self.size_limit_enabled,
                'size_limit_mb': self.size_limit_mb,
                'size_limit_fallback': self.size_limit_fallback,
                'size_upgrade_enabled': self.size_upgrade_enabled,
                'size_upgrade_to': self.size_upgrade_to,
                'player_client': self.player_client,
                'prewarm_enabled': self.prewarm_enabled,
                'parallel_hardsub': self.parallel_hardsub,
                'hardsub_encoder': self.hardsub_encoder,
                'precache_concurrent_count': self.precache_concurrent_count,
                'batch_concurrent_fetches': getattr(self, 'batch_concurrent_fetches', 3),
                'advance_queue_on_streams_done': self.advance_queue_on_streams_done,
                'clipboard_watch': self.clipboard_watch,
                'batch_start_immediately': self.batch_start_immediately,
                'terminal_expanded': self.terminal_expanded,
                'custom_dns': self.custom_dns_enabled.get() if hasattr(self, 'custom_dns_enabled') else self.custom_dns,
                'filename_include_date': self.filename_include_date,
                'filename_format': self.filename_format,
                'cookies_browser': self.cookies_browser,
                'cookies_file': getattr(self, 'cookies_file', ''),
                'cookies_enabled': self._cookies_enabled_var.get() if hasattr(self, '_cookies_enabled_var') else True,
                'bgutil_server_url': getattr(self, 'bgutil_server_url', 'http://127.0.0.1:4416'),
                'bgutil_server_path': getattr(self, 'bgutil_server_path', ''),
                'bgutil_autostart': getattr(self, 'bgutil_autostart', False),
                'bgutil_keep_running': getattr(self, 'bgutil_keep_running', True),
                'extended_client_cascade': getattr(self, 'extended_client_cascade', True),
                'meta_embed_title': self.meta_embed_title,
                'meta_embed_artist': self.meta_embed_artist,
                'meta_embed_date': self.meta_embed_date,
                'meta_embed_comment': self.meta_embed_comment,
                'meta_embed_synopsis': self.meta_embed_synopsis,
                'embed_metadata': self.embed_metadata_enabled.get() if hasattr(self, 'embed_metadata_enabled') else self.embed_metadata,
                'subtitle_source': self.subtitle_source,
                'subtitle_last_source': self.subtitle_last_source,
                'subtitle_mode': self.subtitle_mode,
                'subtitle_lang': self.subtitle_lang,
                'preferred_audio_bitrate': self.preferred_audio_bitrate,
                'preferred_video_bitrate': self.preferred_video_bitrate,
                'include_hls_streams': self.include_hls_streams,
                'reuse_info_json': self.reuse_info_json,
                'audio_only_mode': self.audio_only_mode.get() if hasattr(self, 'audio_only_mode') else self.audio_only_mode_default,
                'audio_only_format': getattr(self, 'audio_only_format', 'm4a'),
                'audio_opus_naming': getattr(self, 'audio_opus_naming', 'codec'),
                'audio_bitrate_policy': getattr(self, 'audio_bitrate_policy', 'match_source'),
                'audio_fixed_bitrate': getattr(self, 'audio_fixed_bitrate', 128),
                'audio_drc_pref': getattr(self, 'audio_drc_pref', 'avoid'),
                'audio_quality_tag': getattr(self, 'audio_quality_tag', 'audio'),
                'audio_no_aac_action': getattr(self, 'audio_no_aac_action', 'transcode'),
                'audio_cache_streams': getattr(self, 'audio_cache_streams', True),
                'audio_output_folder': getattr(self, 'audio_output_folder', ''),
                'audio_duplicate_action': getattr(self, 'audio_duplicate_action', 'number'),
                'history_enabled': (self._history_enabled_var.get()
                                    if hasattr(self, '_history_enabled_var')
                                    else getattr(self, 'history_enabled', True)),
                'remember_window': getattr(self, 'remember_window', True),
                'window_geometry': getattr(self, 'window_geometry', ''),
                'window_maximized': getattr(self, 'window_maximized', False),
            }
            tmp_file = config_file + '.tmp'
            with open(tmp_file, 'w') as f:
                json.dump(cfg, f, indent=2)
            os.replace(tmp_file, config_file)
        except Exception as e:
            print('Could not save config: ' + str(e))
            try:
                if os.path.exists(tmp_file):
                    os.remove(tmp_file)
            except Exception:
                pass

    # ── Queue persistence ──────────────────────────────────────────────────

    # ── Download history persistence ──────────────────────────────────────

    def _load_download_history(self):
        """Load download history from ysa_history.json."""
        history_file = os.path.join(SCRIPT_DIR, 'ysa_history.json')
        if not os.path.exists(history_file):
            return
        try:
            with open(history_file, 'r', encoding='utf-8') as f:
                data = json.load(f)
            if isinstance(data, list):
                self.download_history = data
        except Exception as e:
            print('Could not load history: ' + str(e))

    def _sweep_pending_on_load(self):
        """Anything left 'pending' from a previous session never finished."""
        self._sweep_pending_attempts('interrupted - app closed before it finished')

    def _save_download_history(self):
        """Save download history to ysa_history.json."""
        history_file = os.path.join(SCRIPT_DIR, 'ysa_history.json')
        try:
            tmp_file = history_file + '.tmp'
            with open(tmp_file, 'w', encoding='utf-8') as f:
                json.dump(self.download_history, f, indent=2, ensure_ascii=False)
            os.replace(tmp_file, history_file)
        except Exception as e:
            print('Could not save history: ' + str(e))
            try:
                if os.path.exists(tmp_file):
                    os.remove(tmp_file)
            except Exception:
                pass

    def _stub_active(self):
        """True while downloads are fake (toolbar stub or a stubbed scenario)."""
        try:
            if getattr(self, 'stub_enabled', False):
                return True
            return 'ysa_fake_ytdlp' in str(getattr(self, 'ytdlp_path', '')).lower()
        except Exception:
            return False

    def _history_key(self, url, video_info=None):
        """One stable identity for a history row, used by BOTH recorders.

        _record_attempt runs at download START, when video_info is often not
        populated yet, so it had no id and keyed on the URL. _record_download
        later keyed on the video id. The two never matched, so success
        APPENDED a second row instead of replacing the pending one - and the
        orphan was then swept to 'failed'. Six such pairs appeared in a
        31-scenario run, every one an ok row beside a failed row with an
        empty video_id.

        The id is parsed out of the URL when the info dict cannot supply it,
        so both callers derive the same key from the same download. Legacy
        rows key identically (their URL yields the same id), so existing
        duplicates collapse the next time that video is downloaded.
        """
        try:
            import re as _re
            _vid = ''
            if video_info:
                _vid = str(video_info.get('id') or '')
            if not _vid and url:
                _m = _re.search(
                    r'(?:[?&]v=|/shorts/|/live/|/embed/|youtu\.be/)'
                    r'([A-Za-z0-9_-]{8,})', str(url))
                if _m:
                    _vid = _m.group(1)
            return _vid or (url or '')
        except Exception:
            return url or ''

    def _record_attempt(self, url, video_info=None):
        """Log a download the moment it STARTS, with status 'pending'.

        Success later replaces this entry via the same video_id/URL dedup
        that _record_download already uses, flipping it to 'ok'. Anything
        that never reaches success therefore stays 'pending' - and a
        'pending' entry with no download running is, by definition, a
        download that did not finish. That covers errors, stops, crashes
        and power loss identically, without hooking a single failure path
        (there are more than ten places _download_active goes False).

        Same gates as _record_download: honours the History toggle and
        never records stub downloads.
        """
        try:
            if not getattr(self, '_m_history_on',
                           getattr(self, 'history_enabled', True)):
                return
            if self._stub_active():
                return
            if not url:
                return
            vid_id = (video_info.get('id') or '') if video_info else ''
            _key = self._history_key(url, video_info)
            if not vid_id and _key and _key != url:
                vid_id = _key   # recovered from the URL
            for i, ex in enumerate(self.download_history):
                if self._history_key(ex.get('url', ''),
                                     {'id': ex.get('video_id')}) == _key:
                    ex['status'] = 'pending'
                    ex['fail_reason'] = ''
                    ex['timestamp'] = datetime.datetime.now().strftime(
                        '%Y-%m-%d %H:%M:%S')
                    self._save_download_history()
                    return
            self.download_history.append({
                'url': url,
                'channel': (video_info.get('uploader')
                            or video_info.get('channel') or '') if video_info else '',
                'title': (video_info.get('title') or '') if video_info else '',
                'upload_date': '',
                'timestamp': datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                'file_path': '',
                'video_id': vid_id,
                'status': 'pending',
                'fail_reason': '',
            })
            if len(self.download_history) > 500:
                self.download_history = self.download_history[-500:]
            self._save_download_history()
        except Exception:
            pass

    def _sweep_pending_attempts(self, reason):
        """Turn every still-'pending' entry into a failure.

        Called when no download can possibly be running: at startup (the
        previous session ended without finishing) and whenever the History
        panel refreshes while idle. Returns True if anything changed, so
        the caller can avoid a pointless save.
        """
        changed = False
        try:
            for ex in self.download_history:
                if ex.get('status') == 'pending':
                    ex['status'] = 'failed'
                    ex['fail_reason'] = reason
                    changed = True
            if changed:
                self._save_download_history()
        except Exception:
            pass
        return changed

    def _record_download(self, file_path, url, video_info, quality, download_time):
        # History recording can be switched off from the History tab. Read
        # the plain mirror, not the Tk variable - this runs on worker threads.
        if not getattr(self, '_m_history_on', getattr(self, 'history_enabled', True)):
            return
        # Stub downloads are not real videos - "Fake Test Video" repeated once
        # per test is noise in a library history. Scenario runs against the
        # REAL yt-dlp still record, because those downloads actually happened.
        if self._stub_active():
            return
        """Record a completed download in the history list.
        Deduplicates by video_id (or URL fallback) - if the same video is
        downloaded again, the existing entry is updated rather than duplicated."""
        vid_id = (video_info.get('id') or '') if video_info else ''
        # Format upload date as YYYY-MM-DD if available
        _raw_date = (video_info.get('upload_date') or '') if video_info else ''
        _upload_date = ''
        if _raw_date and len(str(_raw_date)) == 8:
            _r = str(_raw_date)
            _upload_date = _r[:4] + '-' + _r[4:6] + '-' + _r[6:8]
        new_entry = {
            'url': url or '',
            'channel': (video_info.get('uploader') or video_info.get('channel') or '') if video_info else '',
            'title': (video_info.get('title') or '') if video_info else '',
            'upload_date': _upload_date,
            'timestamp': datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
            'file_path': file_path or '',
            'video_id': vid_id,
            'status': 'ok',
            'fail_reason': '',
        }
        # Check for existing entry with same video_id or same URL
        # Must derive exactly as _record_attempt does, or a completed
        # download appends a new row beside its own pending one.
        _match_key = self._history_key(url, video_info)
        replaced = False
        if _match_key:
            for i, existing in enumerate(self.download_history):
                _ex_key = self._history_key(existing.get('url', ''),
                                            {'id': existing.get('video_id')})
                if _ex_key and _ex_key == _match_key:
                    self.download_history[i] = new_entry
                    replaced = True
                    break
        if not replaced:
            self.download_history.append(new_entry)
        # Keep at most 500 entries
        if len(self.download_history) > 500:
            self.download_history = self.download_history[-500:]
        self._save_download_history()
        # Refresh the history treeview if it exists
        if hasattr(self, '_history_tree'):
            self.root.after(0, self._refresh_history_panel)

    # ── Clipboard watch ────────────────────────────────────────────────────

    def _start_clipboard_watch(self):
        """Begin polling the clipboard every second for new YouTube URLs.
        Stops any existing loop first, then starts a fresh one - safe to call
        multiple times without creating duplicate parallel loops."""
        # Mark any currently-running loop as stale so it exits on its next tick
        self._clipboard_watch_active = False
        # Use a generation counter - the new loop only continues while the
        # generation matches, so stale loops self-terminate immediately.
        self._clipboard_gen = getattr(self, '_clipboard_gen', 0) + 1
        # Do NOT seed _clipboard_last_seen from the current clipboard contents.
        # If we did, a URL that was already in the clipboard when the program
        # launched (or when the watch was toggled on) would silently be skipped
        # even after the user re-copies it.  Starting empty means the very first
        # poll will pick up whatever is currently there.
        self._clipboard_last_seen = ''
        self._clipboard_watch_active = True
        # 250 ms, not 1000: the clipboard is a single slot, so anything
        # copied and replaced between two polls is never seen at all. Nine
        # links clicked in a few seconds produced six downloads.
        self.root.after(250, self._clipboard_poll, self._clipboard_gen)

    def _clipboard_poll(self, gen=0):
        """Single tick of the clipboard watch loop. Reschedules itself via root.after.
        The gen parameter ensures only the most recently started loop continues -
        any older loop whose generation no longer matches self._clipboard_gen exits."""
        if not getattr(self, '_clipboard_watch_active', False):
            return
        if not self.clipboard_watch:
            self._clipboard_watch_active = False
            return
        # Stale loop - a newer one was started after a toggle; self-terminate
        if gen != getattr(self, '_clipboard_gen', 0):
            return
        # Don't fire while any modal dialog has grab focus (e.g. Settings)
        try:
            if self.root.grab_current() is not None:
                self.root.after(250, self._clipboard_poll, gen)
                return
        except Exception:
            pass
        try:
            text = self.root.clipboard_get().strip()
        except Exception:
            text = ''
        # Reject multiline content - a URL is always a single line
        if text and '\n' not in text and text != self._clipboard_last_seen:
            self._clipboard_last_seen = text
            if self.is_valid_youtube_url(text) or self.is_playlist_url(text):
                self.url_var.set(text)
                self.append_terminal_output(
                    'Clipboard: detected URL - ' + text[:60] + '\n', 'info')
                self._enqueue_url_for_analysis(text)
        self.root.after(250, self._clipboard_poll, gen)

    # ── Queue persistence ──────────────────────────────────────────────────


    def _save_queue(self):
        """Serialize pending (not-yet-started) queue entries to ysa_queue.json."""
        with self._queue_lock:
            queue_snapshot = list(self._download_queue)
        if not queue_snapshot:
            return
        queue_file = os.path.join(SCRIPT_DIR, 'ysa_queue.json')
        serializable = []
        for entry in queue_snapshot:
            worker_name = entry.get('worker_name', '')
            if not worker_name or worker_name == 'unknown':
                continue
            try:
                json.dumps(list(entry['args']), default=str)  # test serialisability
                serializable.append({
                    'worker_name': worker_name,
                    'args': list(entry['args']),
                    'label': entry.get('label', ''),
                    'is_audio': entry.get('is_audio', False),
                })
            except Exception:
                pass
        if not serializable:
            return
        try:
            tmp_file = queue_file + '.tmp'
            with open(tmp_file, 'w') as f:
                json.dump(serializable, f, indent=2, default=str)
            # Atomic replace - if write fails mid-way the original is untouched
            os.replace(tmp_file, queue_file)
            print('Saved ' + str(len(serializable)) + ' queue entries.')
        except Exception as e:
            print('Could not save queue: ' + str(e))
            try:
                if os.path.exists(tmp_file):
                    os.remove(tmp_file)
            except Exception:
                pass

    def _restore_queue(self):
        """Restore queue and/or pending batch URLs from previous session.
        Shows a single combined dialog if either or both files exist."""
        self._update_cache_size_label()
        queue_file = os.path.join(SCRIPT_DIR, 'ysa_queue.json')
        batch_file = os.path.join(SCRIPT_DIR, 'ysa_batch_pending.json')

        has_queue = os.path.exists(queue_file)
        has_batch = os.path.exists(batch_file)

        if not has_queue and not has_batch:
            return

        # Load whatever files exist
        saved_queue = []
        saved_batch = []
        try:
            if has_queue:
                with open(queue_file, 'r') as f:
                    saved_queue = json.load(f) or []
        except Exception as e:
            print('Could not read queue file: ' + str(e))
            has_queue = False
        try:
            if has_batch:
                with open(batch_file, 'r') as f:
                    saved_batch = json.load(f) or []
        except Exception as e:
            print('Could not read batch file: ' + str(e))
            has_batch = False

        if not saved_queue and not saved_batch:
            for f in (queue_file, batch_file):
                try:
                    if os.path.exists(f):
                        os.remove(f)
                except Exception:
                    pass
            return

        # Build combined dialog message
        msg = "The last session was interrupted.\n"

        if saved_queue:
            q_labels = [item.get('label', 'Unknown') for item in saved_queue]
            msg += "\n" + str(len(saved_queue)) + " download(s) ready to continue:\n"
            for l in q_labels[:4]:
                msg += "  \u2022 " + l + "\n"
            if len(q_labels) > 4:
                msg += "  \u2022 ... and " + str(len(q_labels) - 4) + " more\n"

        if saved_batch:
            msg += "\n" + str(len(saved_batch)) + " URL(s) still need analyzing:\n"
            for u in saved_batch[:4]:
                msg += "  \u2022 " + u + "\n"
            if len(saved_batch) > 4:
                msg += "  \u2022 ... and " + str(len(saved_batch) - 4) + " more\n"

        msg += "\nResume previous session?\n\nYes = restore and continue\nNo  = discard and start fresh"

        resume = messagebox.askyesno("Resume Previous Session?", msg)

        # Always delete files regardless of answer
        for f in (queue_file, batch_file):
            try:
                if os.path.exists(f):
                    os.remove(f)
            except Exception:
                pass

        if not resume:
            self.append_terminal_output('Previous session discarded - starting fresh.\n', 'info')
            return

        # Restore download queue
        if saved_queue:
            worker_map = {
                'merge': self._download_and_merge_worker_with_terminal,
                'direct': self._download_direct_worker_with_terminal,
                'audio': self._download_audio_only_worker,
            }
            count = 0
            for item in saved_queue:
                worker = worker_map.get(item.get('worker_name'))
                if not worker:
                    continue
                args = tuple(item.get('args', []))
                self._download_queue.append({
                    'worker': worker,
                    'worker_name': item.get('worker_name', 'unknown'),
                    'args': args,
                    'label': item.get('label', 'Restored download'),
                    'is_audio': item.get('is_audio', False),
                })
                count += 1
            if count > 0:
                self._refresh_queue_panel()
                self.append_terminal_output(
                    'Restored ' + str(count) + ' queued download(s) from previous session.\n',
                    'cache')

        # Restore pending batch URLs
        if saved_batch:
            if not getattr(self, '_batch_panel_visible', False):
                self._toggle_batch_panel()
            self._batch_text.delete('1.0', tk.END)
            self._batch_text.insert('1.0', '\n'.join(saved_batch))
            self._batch_cancelled = False
            self._batch_queue_btn.config(state='disabled', text='Running...')
            t = threading.Thread(
                target=self._batch_analyze_worker,
                args=(saved_batch,),
                daemon=True)
            t.start()
            self.append_terminal_output(
                'Resuming batch analysis: ' + str(len(saved_batch)) + ' URL(s) pending.\n',
                'cache')

        # Kick off downloads after a short delay
        if saved_queue:
            self.root.after(500, self._start_next_queued)

    def _restore_batch_pending(self):
        """Superseded by _restore_queue which handles both queue and batch together."""
        pass

    def _update_cache_size_label(self):
        """Refresh the cache size label in the download settings box."""
        try:
            mb = self._get_cache_size_mb()
            txt = ("Cache: {:.2f} GB".format(mb / 1024.0)
                   if mb >= 1024 else "Cache: {:.1f} MB".format(mb))
            self.cache_size_var.set(txt)
        except Exception:
            pass

    def _get_cache_size_mb(self):
        """Return total cache size in MB using the incremental counter (no os.walk)."""
        return self._cache_size_bytes / (1024.0 * 1024.0)

    def _scan_cache_size_mb(self):
        """Rescan cache dirs from disk and reseed the running counter.
        Only called once at startup if metadata is missing - never mid-download."""
        total = 0
        for d in [self.video_cache_dir, self.audio_cache_dir, self.subtitle_cache_dir,
                  self.thumbnail_cache_dir, self.premuxed_cache_dir, self.mp3_cache_dir]:
            if d and os.path.isdir(d):
                for root_dir, dirs, files in os.walk(d):
                    for name in files:
                        try:
                            total += os.path.getsize(os.path.join(root_dir, name))
                        except Exception:
                            pass
        self._cache_size_bytes = total
        return total / (1024.0 * 1024.0)

    def _is_cache_protected(self, file_path):
        """True if this cached file must not be evicted right now."""
        try:
            _n = os.path.normcase(os.path.abspath(file_path))
            with self._cache_lock:
                if _n in self._cache_inuse:
                    return True
            # Anything cached in the last two minutes is almost certainly
            # about to be used by whatever just wrote it.
            return (time.time() - os.path.getmtime(file_path)) < 120
        except Exception:
            return True          # cannot tell -> leave it alone

    def _mark_cache_inuse(self, *paths):
        """Protect cached files a running download is about to read.

        Eviction is triggered from cache_video_stream / cache_audio_stream -
        i.e. WHILE a download is in progress - and deletes oldest-first. A
        stream cached in an earlier session is both the oldest thing in the
        cache and exactly what a queued merge may be about to read, and
        nothing tracked that.
        """
        try:
            with self._cache_lock:
                for p in paths:
                    if p:
                        self._cache_inuse.add(os.path.normcase(os.path.abspath(p)))
        except Exception:
            pass

    def _clear_cache_inuse(self):
        try:
            with self._cache_lock:
                self._cache_inuse.clear()
        except Exception:
            pass

    def _evict_cache_if_needed(self):
        """Delete oldest cached files until total cache is under max_cache_mb.
        Uses the incremental _cache_size_bytes counter - no os.walk scan needed."""
        if not self.max_cache_mb:
            return
        limit_bytes = self.max_cache_mb * 1024 * 1024
        if self._cache_size_bytes <= limit_bytes:
            return
        # Build sorted list once; use stored file_size from metadata (no per-file stat)
        entries = []
        for video_id, formats in list(self.cached_videos.items()):
            for format_id, file_path in list(formats.items()):
                # mp3_ keys are handled in their own section below
                if format_id.startswith('mp3_'):
                    continue
                if file_path and os.path.exists(file_path):
                    try:
                        if self._is_cache_protected(file_path):
                            continue
                        mtime = os.path.getmtime(file_path)
                        # Use stored size from metadata to avoid extra stat() calls
                        stored_size = (self.cache_metadata.get('videos', {})
                                       .get(video_id, {}).get('formats', {})
                                       .get(format_id, {}).get('file_size', 0))
                        entries.append((mtime, file_path, 'video', video_id, format_id, stored_size))
                    except Exception:
                        pass
        # Include subtitle files in the eviction pool - they are small individually
        # but accumulate unbounded without eviction.  Size is read via stat() since
        # subtitle metadata doesn't store file_size.
        for video_id, subs in list(self.cached_subtitles.items()):
            for cache_key, file_path in list(subs.items()):
                if file_path and os.path.exists(file_path):
                    try:
                        if self._is_cache_protected(file_path):
                            continue
                        mtime = os.path.getmtime(file_path)
                        size = os.path.getsize(file_path)
                        entries.append((mtime, file_path, 'subtitle', video_id, cache_key, size))
                    except Exception:
                        pass
        # Include thumbnail files - one per video_id, small but worth evicting.
        if self.thumbnail_cache_dir and os.path.isdir(self.thumbnail_cache_dir):
            for fname in os.listdir(self.thumbnail_cache_dir):
                fpath = os.path.join(self.thumbnail_cache_dir, fname)
                if os.path.isfile(fpath):
                    try:
                        mtime = os.path.getmtime(fpath)
                        size = os.path.getsize(fpath)
                        vid_id = os.path.splitext(fname)[0]
                        entries.append((mtime, fpath, 'thumbnail', vid_id, fname, size))
                    except Exception:
                        pass
        # Include premuxed files - these are the largest per-entry items.
        for vid_id, fmts in list(self.cached_premuxed.items()):
            for fmt_id, fpath in list(fmts.items()):
                if fpath and os.path.exists(fpath):
                    try:
                        mtime = os.path.getmtime(fpath)
                        size = os.path.getsize(fpath)
                        entries.append((mtime, fpath, 'premuxed', vid_id, fmt_id, size))
                    except Exception:
                        pass
        # Include MP3 cache files - 10–35 MB each, accumulate without bound
        # if max_cache_mb is set and they're not evicted.
        for vid_id, fmts in list(self.cached_videos.items()):
            for key, fpath in list(fmts.items()):
                if key.startswith('mp3_') and fpath and os.path.exists(fpath):
                    try:
                        mtime = os.path.getmtime(fpath)
                        size = os.path.getsize(fpath)
                        entries.append((mtime, fpath, 'mp3', vid_id, key, size))
                    except Exception:
                        pass
        entries.sort(key=lambda x: x[0])
        for entry in entries:
            if self._cache_size_bytes <= limit_bytes:
                break
            _mtime, file_path, entry_type, video_id, key, stored_size = entry
            try:
                if stored_size:
                    actual_size = stored_size
                else:
                    # Entries recorded without a size: stat before deleting
                    # so the byte counter stays truthful and eviction can't
                    # spiral into deleting far more than the overage.
                    try:
                        actual_size = os.path.getsize(file_path)
                    except Exception:
                        actual_size = 0
                os.remove(file_path)
                self._cache_size_bytes = max(0, self._cache_size_bytes - actual_size)
                if entry_type == 'video':
                    if video_id in self.cached_videos:
                        self.cached_videos[video_id].pop(key, None)
                        if not self.cached_videos[video_id]:
                            del self.cached_videos[video_id]
                    (self.cache_metadata.get('videos', {})
                     .get(video_id, {}).get('formats', {}).pop(key, None))
                elif entry_type == 'subtitle':
                    if video_id in self.cached_subtitles:
                        self.cached_subtitles[video_id].pop(key, None)
                        if not self.cached_subtitles[video_id]:
                            del self.cached_subtitles[video_id]
                    (self.cache_metadata.get('subtitles', {})
                     .get(video_id, {}).pop(key, None))
                # thumbnails: file already deleted, no in-memory index to update
                elif entry_type == 'premuxed':
                    if video_id in self.cached_premuxed:
                        self.cached_premuxed[video_id].pop(key, None)
                        if not self.cached_premuxed[video_id]:
                            del self.cached_premuxed[video_id]
                elif entry_type == 'mp3':
                    if video_id in self.cached_videos:
                        self.cached_videos[video_id].pop(key, None)
                        if not self.cached_videos[video_id]:
                            del self.cached_videos[video_id]
                    (self.cache_metadata.get('videos', {})
                     .get(video_id, {}).get('formats', {}).pop(key, None))
            except Exception:
                pass
        # Flush metadata after eviction (called post-download, not mid-stream)
        self.save_cache_metadata()

    # ── Update banner (main window) ──────────────────────────────────────────

    def _show_update_banner(self, message):
        """Show the orange update banner in the main window with the given message."""
        try:
            self._update_banner_lbl.config(text=message)
            self._update_banner_frame.grid(row=6, column=0, columnspan=3,
                                           sticky=(tk.W, tk.E), pady=(2, 0))
        except Exception:
            pass

    def _dismiss_update_banner(self):
        try:
            self._update_banner_frame.grid_remove()
        except Exception:
            pass

    def _run_pending_updates(self):
        """Triggered by the Update Now button - runs whichever tools need updating."""
        self._dismiss_update_banner()
        needs = getattr(self, '_tools_needing_update', [])
        if 'yt-dlp' in needs:
            threading.Thread(target=self._update_ytdlp, daemon=True).start()
        if 'ffmpeg' in needs:
            self._update_ffmpeg()
        self._tools_needing_update = []

    # ── Startup update check ──────────────────────────────────────────────────

    def _startup_update_check(self):
        """Background thread: compare local versions to latest, auto-update if enabled,
        or show the banner if not.  Runs once 2 seconds after startup."""
        self._tools_needing_update = []
        results = {}  # tool -> ('ok'|'update'|'unknown', local_ver, latest_ver)

        # ── yt-dlp ────────────────────────────────────────────────────────────
        local_ytdlp = self._get_ytdlp_version()
        import requests  # deferred - see _get_http_session at module top
        try:
            resp = requests.get(
                self._ytdlp_release_api_url(),
                timeout=8, headers={'Accept': 'application/vnd.github+json'})
            resp.raise_for_status()
            latest_ytdlp = resp.json().get('tag_name', '').strip()
        except Exception:
            latest_ytdlp = None

        if not local_ytdlp:
            results['yt-dlp'] = ('unknown', '', '')
        elif not latest_ytdlp:
            results['yt-dlp'] = ('offline', local_ytdlp, '')
        elif self._version_key(local_ytdlp) >= self._version_key(latest_ytdlp):
            results['yt-dlp'] = ('ok', local_ytdlp, latest_ytdlp)
        else:
            results['yt-dlp'] = ('update', local_ytdlp, latest_ytdlp)
            self._tools_needing_update.append('yt-dlp')

        # ── ffmpeg ────────────────────────────────────────────────────────────
        local_ffmpeg = self._get_ffmpeg_version()
        latest_ffmpeg, _ = self._get_ffmpeg_latest_info()

        local_sv = self._parse_ffmpeg_semver(local_ffmpeg)
        latest_sv = self._parse_ffmpeg_semver(latest_ffmpeg)

        if not local_sv:
            results['ffmpeg'] = ('unknown', '', '')
        elif not latest_sv:
            results['ffmpeg'] = ('offline', local_ffmpeg, '')
        elif local_sv >= latest_sv:
            results['ffmpeg'] = ('ok', local_ffmpeg, latest_ffmpeg)
        else:
            results['ffmpeg'] = ('update', local_ffmpeg, latest_ffmpeg)
            self._tools_needing_update.append('ffmpeg')

        # ── Auto-update or show banner ─────────────────────────────────────
        if self._tools_needing_update:
            if self.auto_update_tools:
                # Silent auto-update
                for tool in list(self._tools_needing_update):
                    local_v = results[tool][1] or 'unknown'
                    latest_v = results[tool][2] or 'unknown'
                    self.append_terminal_output(
                        'Auto-updating ' + tool + ' (' + local_v + ' -> ' + latest_v + ')...\n', 'info')
                    if tool == 'yt-dlp':
                        # Replacing yt-dlp.exe while an invocation is in
                        # flight corrupts it mid-read: the running process
                        # dies with 'Error -3 while decompressing data:
                        # incorrect header check' and the caller burns
                        # retries. Seen in the field costing 3 attempts and
                        # ~18s. _any_ytdlp_running fails CLOSED, so an
                        # ambiguous answer defers rather than risks it; the
                        # update simply happens on a later launch.
                        if (getattr(self, '_download_active', False)
                                or self._any_ytdlp_running()):
                            self.append_terminal_output(
                                'yt-dlp update deferred - a download or an'
                                ' extraction is still running. It will be'
                                ' applied next launch.\n', 'info')
                        else:
                            self._update_ytdlp()
                    elif tool == 'ffmpeg':
                        self._update_ffmpeg()
                self.root.after(0, lambda: self.status_var.set('Tools updated to latest versions'))
            else:
                # Show the orange banner
                names = ' and '.join(self._tools_needing_update)
                parts = []
                for t in self._tools_needing_update:
                    lv, rv = results[t][1] or '?', results[t][2] or '?'
                    parts.append(t + ': ' + lv + ' -> ' + rv)
                msg = 'Updates available  |  ' + '   '.join(parts)
                self.root.after(0, lambda m=msg: self._show_update_banner(m))

    # ── yt-dlp version & update ────────────────────────────────────────────────

    def _get_ytdlp_version(self):
        """Return yt-dlp version string or None."""
        if not self.ytdlp_path:
            return None
        try:
            result = subprocess.run(
                self._ytdlp_head() + ['--version'],
                capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                creationflags=CREATE_NO_WINDOW)
            if result.returncode == 0:
                return result.stdout.strip()
        except Exception:
            pass
        return None

    def _ytdlp_release_api_url(self):
        """GitHub releases API for the channel yt-dlp is actually on.

        Nightly builds live in a DIFFERENT repository (yt-dlp-nightly-builds).
        Checking a nightly binary against the stable repo compares a tag like
        2026.08.16.232941 with one like 2026.03.17 and reports nonsense - the
        bug this method exists to remove.
        """
        if getattr(self, 'ytdlp_channel', 'nightly') == 'stable':
            return 'https://api.github.com/repos/yt-dlp/yt-dlp/releases/latest'
        return ('https://api.github.com/repos/yt-dlp/yt-dlp-nightly-builds'
                '/releases/latest')

    def _update_ytdlp(self):
        """Run yt-dlp -U in a background thread and stream output to terminal."""
        if not self.ytdlp_path:
            self.append_terminal_output('yt-dlp not found - cannot update.\n', 'error')
            return
        self.append_terminal_output('Updating yt-dlp...\n', 'info')
        try:
            proc = subprocess.Popen(
                self._ytdlp_head() + ['--update-to',
                                      getattr(self, 'ytdlp_channel', 'nightly')],
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                text=True, encoding='utf-8', errors='replace', bufsize=1,
                creationflags=CREATE_NO_WINDOW)
            for line in iter(proc.stdout.readline, ''):
                if line.strip():
                    self.append_terminal_output(line.rstrip() + '\n', 'info')
            proc.wait()
            self.append_terminal_output('yt-dlp update finished.\n', 'success')
        except Exception as e:
            self.append_terminal_output('yt-dlp update error: ' + str(e) + '\n', 'error')

    # ── FFmpeg version & update ───────────────────────────────────────────────

    # ── FFmpeg version helpers ────────────────────────────────────────────────

    @staticmethod
    def _parse_ffmpeg_semver(version_str):
        """Extract a comparable (major, minor, patch) tuple from an ffmpeg version string.
        Handles GyanD/codexffmpeg format ('7.1.1-essentials_build...') and raw tokens.
        Returns a tuple of ints, e.g. (7, 1, 1), or None if unparseable."""
        if not version_str:
            return None
        import re as _re
        m = _re.search(r'(\d+)\.(\d+)\.(\d+)', version_str)
        if m:
            return (int(m.group(1)), int(m.group(2)), int(m.group(3)))
        # Two-part fallback: "7.1"
        m2 = _re.search(r'(\d+)\.(\d+)', version_str)
        if m2:
            return (int(m2.group(1)), int(m2.group(2)), 0)
        return None

    def _get_ffmpeg_version(self):
        """Return the local ffmpeg version string (e.g. '7.1.1') or None."""
        if not self.ffmpeg_path:
            return None
        try:
            result = subprocess.run(
                [self.ffmpeg_path, '-version'],
                capture_output=True, text=True, encoding='utf-8', errors='replace', timeout=10,
                creationflags=CREATE_NO_WINDOW)
            if result.returncode == 0:
                first_line = result.stdout.splitlines()[0].strip() if result.stdout else ''
                # "ffmpeg version 7.1.1-essentials_build ..."
                if 'version' in first_line:
                    raw = first_line.split('version', 1)[1].strip().split(' ')[0]
                    # Return just the numeric part (strip build suffix)
                    import re as _re
                    m = _re.search(r'(\d+\.\d+(?:\.\d+)?)', raw)
                    return m.group(1) if m else raw
        except Exception:
            pass
        return None

    def _get_ffmpeg_latest_info(self):
        """Fetch the latest FFmpeg release from GyanD/codexffmpeg on GitHub.
        Returns (version_string, download_url) or (None, None) on failure."""
        import requests  # deferred - see _get_http_session at module top
        try:
            api_url = 'https://api.github.com/repos/GyanD/codexffmpeg/releases/latest'
            resp = requests.get(api_url, timeout=10,
                                headers={'Accept': 'application/vnd.github+json'})
            resp.raise_for_status()
            data = resp.json()
            latest_ver = data.get('tag_name', '').strip()  # e.g. "7.1.1"
            # Find the essentials_build zip asset
            asset_url = None
            for asset in data.get('assets', []):
                name = asset.get('name', '')
                if 'essentials_build.zip' in name:
                    asset_url = asset.get('browser_download_url')
                    break
            if not latest_ver or not asset_url:
                return None, None
            return latest_ver, asset_url
        except Exception:
            return None, None

    def _resolve_ffmpeg_update_dest(self):
        """Determine where the ffmpeg update should be written.

        Returns (dest_path, note) where note is a human-readable string explaining
        the destination choice (shown in the terminal log).

        Priority:
          1. If self.ffmpeg_path is a real writable file that is NOT inside the
             PyInstaller extraction dir (_MEIPASS) -> update it in place.
          2. If self.ffmpeg_path is the bare command 'ffmpeg' (PATH), resolve its
             full path via shutil.which and check writeability.
          3. Fall back to SCRIPT_DIR/ffmpeg.exe in all other cases
             (frozen bundle, unwritable system path, None).
        """
        active = self.ffmpeg_path or ''

        # Resolve bare 'ffmpeg' command to a full path
        if active in ('ffmpeg', 'ffmpeg.exe'):
            resolved = shutil.which('ffmpeg') or shutil.which('ffmpeg.exe')
            if resolved:
                active = resolved

        # Never write into PyInstaller's temporary extraction directory
        meipass = getattr(sys, '_MEIPASS', None)
        if meipass and active.startswith(meipass):
            dest = os.path.join(SCRIPT_DIR, 'ffmpeg.exe')
            note = ('Active ffmpeg is inside the app bundle (read-only). '
                    'Writing to local directory instead: ' + dest)
            return dest, note

        # If it points to a real file, try to update it in place
        if os.path.isfile(active):
            if os.access(active, os.W_OK):
                return active, 'Updating active ffmpeg in place: ' + active
            else:
                dest = os.path.join(SCRIPT_DIR, 'ffmpeg.exe')
                note = ('No write permission for ' + active + ' (may need admin rights). '
                        'Writing to local directory instead: ' + dest
                        + '\nThe local copy will take priority over the system copy on next launch.')
                return dest, note

        # Default: write to SCRIPT_DIR (covers missing ffmpeg_path, PATH not found, etc.)
        dest = os.path.join(SCRIPT_DIR, 'ffmpeg.exe')
        return dest, 'Writing ffmpeg to local directory: ' + dest

    def _update_ffmpeg(self, on_done_callback=None):
        """Download the latest GyanD/codexffmpeg FFmpeg essentials build, extract
        ffmpeg.exe and replace the currently active copy.
        on_done_callback(success, message) is called on the main thread when finished."""
        def _run():
            def log(msg, tag='info'):
                self.append_terminal_output(msg, tag)
            def done(ok, msg):
                log(msg + '\n', 'success' if ok else 'error')
                if on_done_callback:
                    self.root.after(0, lambda: on_done_callback(ok, msg))

            # Resolve destination before downloading so the user sees it upfront
            dest_path, dest_note = self._resolve_ffmpeg_update_dest()
            log(dest_note + '\n', 'info')

            log('Checking latest FFmpeg release (GyanD/codexffmpeg)...\n', 'info')
            latest_ver, asset_url = self._get_ffmpeg_latest_info()
            if not asset_url:
                done(False, 'Could not retrieve FFmpeg release info from GitHub (GyanD/codexffmpeg).')
                return

            log('Latest version: ' + (latest_ver or 'unknown') + '\n', 'info')
            log('Downloading: ' + asset_url + '\n', 'info')

            # ~90 MB - belongs in the app's temp folder, not the user's
            # Windows temp, where nothing cleans it up on our schedule.
            self._ensure_cache_dirs()
            _zip_dir = getattr(self, 'ysa_tmp_dir', None) or tempfile.gettempdir()
            zip_tmp = os.path.join(_zip_dir, 'ffmpeg_update.zip')

            import requests  # deferred - see _get_http_session at module top
            try:
                resp = requests.get(asset_url, stream=True, timeout=120)
                resp.raise_for_status()
                total = int(resp.headers.get('content-length', 0))
                downloaded = 0
                with open(zip_tmp, 'wb') as f:
                    for chunk in resp.iter_content(chunk_size=1024 * 256):
                        if chunk:
                            f.write(chunk)
                            downloaded += len(chunk)
                            if total:
                                pct = downloaded * 100 // total
                                self.root.after(0, lambda p=pct:
                                    self.status_var.set('FFmpeg download: ' + str(p) + '%'))
                log('Download complete. Extracting ffmpeg.exe...\n', 'info')

                import zipfile
                with zipfile.ZipFile(zip_tmp, 'r') as zf:
                    # zip layout: ffmpeg-7.1.1-essentials_build/bin/ffmpeg.exe
                    ffmpeg_members = [m for m in zf.namelist()
                                      if m.endswith('/ffmpeg.exe') or m == 'ffmpeg.exe']
                    if not ffmpeg_members:
                        done(False, 'ffmpeg.exe not found inside the downloaded archive.')
                        return
                    target_member = next((m for m in ffmpeg_members if '/bin/' in m),
                                         ffmpeg_members[0])
                    with zf.open(target_member) as src_f, open(dest_path, 'wb') as dst_f:
                        shutil.copyfileobj(src_f, dst_f)

                os.remove(zip_tmp)
                self.ffmpeg_path = dest_path
                self.root.after(0, lambda: self.status_var.set('Ready'))
                done(True, 'FFmpeg updated to ' + (latest_ver or 'latest') + ' -> ' + dest_path)

            except Exception as e:
                try:
                    os.remove(zip_tmp)
                except Exception:
                    pass
                self.root.after(0, lambda: self.status_var.set('Ready'))
                done(False, 'FFmpeg update failed: ' + str(e))

        threading.Thread(target=_run, daemon=True).start()

    # ── Default quality auto-enqueue ───────────────────────────────────────

    # Resolution fallback order used by auto-download (highest to lowest)
    _QUALITY_FALLBACK = ['2160p', '1440p', '1080p', '720p', '480p', '360p', '240p', '144p']

    # Standard resolution tiers (numeric) used to bucket non-standard resolutions
    _STANDARD_TIERS = (2160, 1440, 1080, 720, 480, 360, 240, 144)

    @staticmethod
    def _nearest_standard_quality(px):
        """Map any pixel resolution to the nearest standard tier.

        Used by auto-download and Smart Quality to match a user's standard
        quality setting (e.g. '1080p') against non-standard actual resolutions
        (e.g. 1086p, 1628p, 814p).  NOT used for display or filenames — those
        show the real resolution for accuracy.

        Returns 0 for invalid input."""
        if not px or px <= 0:
            return 0
        _tiers = (2160, 1440, 1080, 720, 480, 360, 240, 144)
        return min(_tiers, key=lambda t: abs(t - px))

    def _get_video_stream_mb_for_quality(self, quality_str):
        """Return the video stream filesize in MB for the given quality string (e.g. '1086p'),
        or None if unknown.  Respects preferred_video_bitrate - returns the size of the
        stream that select_best_video_stream would actually choose, so Smart Quality
        size checks stay consistent with what will be downloaded.

        Tries exact resolution match first (handles actual resolutions like 1086p
        shown in the recommended tree).  Falls back to nearest-tier matching so
        standard settings values (e.g. 1080p) still find non-standard streams."""
        if not self.current_formats:
            return None
        target_px = int(quality_str.rstrip('p')) if quality_str.rstrip('p').isdigit() else None
        if target_px is None:
            return None
        exact = []
        tier = []
        for fmt in self.current_formats:
            if fmt.get('vcodec', 'none') in ('none', '', None):
                continue
            h = fmt.get('height', 0) or 0
            w = fmt.get('width', 0) or 0
            eff = min(h, w) if h and w else (h or w)
            if eff == target_px:
                exact.append(fmt)
            elif eff > 0 and self._nearest_standard_quality(eff) == target_px:
                tier.append(fmt)
        candidates = exact or tier
        chosen = self.select_best_video_stream(candidates)
        if chosen:
            fs = chosen.get('filesize') or chosen.get('filesize_approx')
            if fs:
                return fs / (1024 * 1024)
        return None

    def _get_audio_stream_mb(self):
        """Return the filesize in MB of the audio stream that would actually be
        downloaded for the current video, or None if unknown.

        Mirrors the bitrate preference logic in select_best_audio_stream without
        requiring the full detected_languages map - good enough for a size check.
        Audio-only streams are those with a valid acodec and no vcodec."""
        if not self.current_formats:
            return None
        audio_streams = [
            f for f in self.current_formats
            if f.get('acodec') not in (None, 'none', '')
            and f.get('vcodec') in (None, 'none', '')
        ]
        if not audio_streams:
            return None
        limit = getattr(self, 'preferred_audio_bitrate', 0)
        if limit and limit > 0:
            under = [s for s in audio_streams if (s.get('abr') or 0) <= limit]
            chosen = max(under, key=lambda x: x.get('abr', 0)) if under else \
                     min(audio_streams, key=lambda x: x.get('abr', 0))
        else:
            chosen = max(audio_streams, key=lambda x: x.get('abr', 0))
        fs = chosen.get('filesize') or chosen.get('filesize_approx')
        if fs:
            return fs / (1024 * 1024)
        return None

    def _auto_download_best_quality(self):
        """After analysis, automatically download the best available quality at or below
        the configured default.  Falls back through lower resolutions until one is found.
        Starts immediately if idle, or queues if a download is already running.
        Fires only once per fresh video analysis (guarded by _auto_enqueue_done flag).

        When the video uses non-standard resolutions (e.g. 1086p instead of
        1080p), a nearest-tier mapping bridges the gap between the user's
        standard setting and the actual available streams.  A terminal message
        is logged whenever a closest match is used instead of an exact one."""

        # Guard: only fire once per fresh video analysis, not on cache/language refreshes
        if getattr(self, '_auto_enqueue_done', True):
            return

        target = getattr(self, 'default_quality', None)
        if not target:
            return

        children = self.recommended_tree.get_children()
        if not children:
            return

        self._auto_enqueue_done = True  # Prevent re-firing on subsequent refreshes

        # Build a dict of {quality_str: iid} from the recommended tree
        available = {}
        for iid in children:
            vals = self.recommended_tree.item(iid, 'values')
            if vals:
                available[str(vals[0])] = iid

        # Build a mapping from standard quality tiers to the closest actual
        # available quality.  This lets the _QUALITY_FALLBACK walk find
        # non-standard resolutions like 1086p when looking for 1080p.
        # Only considers DASH entries (not Direct: combined streams).
        available_by_tier = {}  # e.g. {'1080p': '1086p', '720p': '814p'}
        for q_str, iid in available.items():
            # Skip Direct/combined entries - they have their own handling
            vals = self.recommended_tree.item(iid, 'values')
            if vals and 'Direct:' in str(vals[1]):
                continue
            px_str = q_str.rstrip('p')
            if not px_str.isdigit():
                continue
            px = int(px_str)
            tier = self._nearest_standard_quality(px)
            tier_str = str(tier) + 'p'
            if tier_str not in available_by_tier:
                available_by_tier[tier_str] = q_str
            else:
                # Keep the resolution closer to the tier centre
                existing_px = int(available_by_tier[tier_str].rstrip('p'))
                if abs(px - tier) < abs(existing_px - tier):
                    available_by_tier[tier_str] = q_str

        def _resolve(standard_q):
            """Map a standard quality string to the actual available quality.
            Returns the actual quality string if found, else None."""
            if standard_q in available:
                return standard_q  # exact match (standard video)
            actual = available_by_tier.get(standard_q)
            if actual and actual in available:
                return actual
            return None

        # ── Premuxed mode: pick the best available direct stream ─────────
        # When the user selects "Premuxed" in the auto-download menu, skip the
        # DASH walk entirely and go straight to combined/direct streams.
        if target == 'Premuxed':
            chosen_iid = None
            chosen_quality = None
            for iid in children:
                vals = self.recommended_tree.item(iid, 'values')
                if vals and 'Direct:' in str(vals[1]):
                    chosen_iid = iid
                    chosen_quality = str(vals[0])
                    break
            if chosen_iid is not None:
                self.append_terminal_output(
                    'Auto-download: premuxed ' + chosen_quality + ' selected\n', 'info')
                self._enqueue_chosen(chosen_iid, chosen_quality)
            else:
                self.append_terminal_output(
                    'Auto-download: no premuxed stream available for this video\n', 'warning')
            return
        if (self.size_upgrade_enabled and self.size_limit_enabled
                and self.size_upgrade_to in self._QUALITY_FALLBACK
                and target in self._QUALITY_FALLBACK):
            upgrade_idx = self._QUALITY_FALLBACK.index(self.size_upgrade_to)
            target_idx  = self._QUALITY_FALLBACK.index(target)
            if upgrade_idx < target_idx:  # upgrade_to is higher res than target
                # Try each resolution from upgrade_to down to target
                for q in self._QUALITY_FALLBACK[upgrade_idx:target_idx]:
                    actual_q = _resolve(q)
                    if actual_q:
                        iid = available[actual_q]
                        vals = self.recommended_tree.item(iid, 'values')
                        # Estimate video-only size from tree (col 3 has combined size_str)
                        # We need the raw video stream size - look it up from current_formats
                        vid_mb = self._get_video_stream_mb_for_quality(actual_q)
                        aud_mb = self._get_audio_stream_mb()
                        total_mb = (vid_mb or 0) + (aud_mb or 0)
                        limit_mb = self.size_limit_mb
                        if vid_mb is not None and total_mb <= limit_mb:
                            _upgrade_msg = 'Smart Quality: upgrading to ' + actual_q
                            if actual_q != q:
                                _upgrade_msg += ' (closest to ' + q + ')'
                            _upgrade_msg += (' ('
                                + '{:.0f}'.format(total_mb) + ' MB total <= '
                                + str(limit_mb) + ' MB limit)\n')
                            self.append_terminal_output(_upgrade_msg, 'info')
                            target = actual_q
                        break  # Only check the best available upgrade candidate

        # Walk the fallback list starting from the target quality downwards
        start_idx = self._QUALITY_FALLBACK.index(target) if target in self._QUALITY_FALLBACK else 2
        chosen_iid = None
        chosen_quality = None
        for q in self._QUALITY_FALLBACK[start_idx:]:
            actual_q = _resolve(q)
            if actual_q:
                # ── Smart quality: enforce size cap ────────────────────────
                if self.size_limit_enabled:
                    vid_mb = self._get_video_stream_mb_for_quality(actual_q)
                    aud_mb = self._get_audio_stream_mb()
                    total_mb = (vid_mb or 0) + (aud_mb or 0)
                    limit_mb = self.size_limit_mb
                    if vid_mb is not None and total_mb > limit_mb:
                        # Try the configured fallback resolution instead
                        fb = self.size_limit_fallback
                        actual_fb = _resolve(fb)
                        _cap_label = actual_q + (' (closest to ' + q + ')' if actual_q != q else '')
                        self.append_terminal_output(
                            'Smart Quality: ' + _cap_label + ' is '
                            + '{:.0f}'.format(total_mb) + ' MB total (limit ' + str(limit_mb)
                            + ' MB) - using ' + (actual_fb or fb) + ' instead\n', 'warning')
                        if actual_fb:
                            chosen_iid = available[actual_fb]
                            chosen_quality = actual_fb
                        else:
                            # Walk down from fallback
                            fb_start = self._QUALITY_FALLBACK.index(fb) if fb in self._QUALITY_FALLBACK else len(self._QUALITY_FALLBACK)
                            for fq in self._QUALITY_FALLBACK[fb_start:]:
                                actual_fq = _resolve(fq)
                                if actual_fq:
                                    chosen_iid = available[actual_fq]
                                    chosen_quality = actual_fq
                                    break
                        break  # Do not continue outer loop
                chosen_iid = available[actual_q]
                chosen_quality = actual_q
                break

        if chosen_iid is None:
            # Nothing found at or below target - walk UP to the nearest higher quality
            for q in reversed(self._QUALITY_FALLBACK[:start_idx]):
                actual_q = _resolve(q)
                if actual_q:
                    chosen_iid = available[actual_q]
                    chosen_quality = actual_q
                    break

        if chosen_iid is None:
            # Last resort: some videos only have combined/progressive streams at
            # non-standard resolutions (e.g. 340p for format-18) that are absent
            # from _QUALITY_FALLBACK.  Scan the tree directly for any Direct: entry.
            for iid in children:
                vals = self.recommended_tree.item(iid, 'values')
                if vals and 'Direct:' in str(vals[1]):
                    chosen_iid = iid
                    chosen_quality = str(vals[0])
                    break

        if chosen_iid is None:
            self.append_terminal_output(
                'Auto-download: no suitable quality found for this video\n', 'warning')
            return

        if chosen_quality != target:
            # Check the already-fetched formats list - no network call needed.
            # The video_info captured during analysis already contains all formats.
            # A re-fetch was previously used to handle YouTube's occasional
            # stripped format list on first fetch, but the cost (2-4s network call
            # per fallback) outweighs the benefit.  The merge worker's CDN retry
            # logic handles any stale format IDs at download time.
            url_to_verify = getattr(self, 'current_video_url', None) or self.url_var.get().strip()
            fallback_quality = chosen_quality
            vi_snap = dict(self.current_video_info) if self.current_video_info else {}
            fallback_row_vals = tuple(self.recommended_tree.item(chosen_iid, 'values'))

            # Check cached formats for target quality - O(N), no I/O
            _existing_video_only = [
                f for f in vi_snap.get('formats', [])
                if f.get('vcodec') not in (None, 'none')
                and f.get('acodec') in (None, 'none')
            ]
            _target_px = int(target.rstrip('p')) if target.rstrip('p').isdigit() else None
            def _eff_q(v):
                h = v.get('height', 0) or 0
                w = v.get('width', 0) or 0
                return min(h, w) if h and w else (h or w)
            _target_in_cache = bool(
                [v for v in _existing_video_only if _eff_q(v) == _target_px]
            ) if _target_px else False

            if _target_in_cache:
                # Target is in the already-fetched info - queue from cached info
                self.append_terminal_output(
                    'Auto-download: ' + target + ' confirmed in cached formats.\n', 'info')
                self._analysis_done_mode = 'deferred'
                self.root.after(0, lambda fi=vi_snap, u=url_to_verify:
                    self._refetch_and_enqueue(fi, u, target))
            else:
                # Not in cached formats - accept closest available match
                # Check whether the fallback is a nearest-tier match
                _fb_px = int(fallback_quality.rstrip('p')) if fallback_quality.rstrip('p').isdigit() else 0
                _is_closest = (_target_px and _fb_px
                               and self._nearest_standard_quality(_fb_px) == _target_px)
                if _is_closest:
                    _fb_msg = ('Auto-download: ' + target
                               + ' not available, closest match '
                               + fallback_quality + ' selected\n')
                else:
                    _fb_msg = ('Auto-download: ' + target
                               + ' not found, using '
                               + fallback_quality + '\n')
                self.append_terminal_output(_fb_msg, 'info')
                # Mark deferred BEFORE scheduling so the _update_video_info
                # finally block does not fire _on_url_analysis_done early.
                self._analysis_done_mode = 'deferred'
                def _confirm_fallback(fq=fallback_quality,
                                      fvals=fallback_row_vals,
                                      vi=vi_snap,
                                      u=url_to_verify):
                    self._enqueue_from_row_vals(fvals, vi_override=vi, url_override=u)
                    self._on_url_analysis_done()
                self.root.after(0, _confirm_fallback)
            return

        # Target quality found on first analysis - proceed immediately
        self._enqueue_chosen(chosen_iid, chosen_quality)

    def _refetch_and_enqueue(self, fresh_info, url, target_quality):
        """Called on the main thread after a successful re-fetch that confirmed the
        target quality is available.  Rebuilds the entire UI from fresh_info so that
        format IDs, video_id, and treeview rows are always correct for this video -
        never read from a potentially-stale treeview that the batch worker may have
        already overwritten with the next URL's data.
        _update_video_info resets _analysis_done_mode to 'pending', so its own
        finally block will call _on_url_analysis_done when done."""
        try:
            self._auto_enqueue_done = False
            self._update_video_info(fresh_info, url)
        except Exception:
            # Even on error, advance the queue so nothing is permanently stalled.
            self._on_url_analysis_done()

    def _enqueue_from_row_vals(self, row_vals, vi_override, url_override):
        """Enqueue a download using a pre-snapshotted treeview row tuple.
        Temporarily inserts the row into the recommended tree, selects it,
        calls _enqueue_current_selection, then removes the temporary row.
        This bypasses the live treeview entirely - safe to call even when the
        tree has been repopulated with a different video (e.g. in batch mode)."""
        temp_iid = self.recommended_tree.insert('', 0, values=row_vals)
        try:
            self.recommended_tree.selection_set(temp_iid)
            self._enqueue_current_selection(vi_override=vi_override, url_override=url_override)
        finally:
            self.recommended_tree.delete(temp_iid)

    def _enqueue_chosen(self, chosen_iid, chosen_quality, vi_override=None, url_override=None):
        """Select the given treeview row and enqueue/start the download.
        Called from _auto_download_best_quality (both direct and re-fetch paths).
        vi_override/url_override are forwarded to _enqueue_current_selection so
        that batch re-fetch callbacks never contaminate self.current_video_info."""
        # Select the row so _enqueue_current_selection reads it
        self.recommended_tree.selection_set(chosen_iid)

        # If idle: start immediately.  If busy/paused/batch: queue.
        busy = (self._download_active or
                (self._download_process is not None
                 and self._download_process.poll() is None))
        if busy or self._download_paused or getattr(self, '_batch_running', False):
            self._enqueue_current_selection(vi_override=vi_override, url_override=url_override)
        else:
            # Start immediately - same path as pressing Download & Merge while idle
            self._download_active = True
            self._record_attempt(url_override or self.url_var.get().strip(),
                                 vi_override or self.current_video_info)
            self._download_stopped = False
            self._reset_download_buttons()
            self.download_recommended_selection()

    # ── Dark mode ──────────────────────────────────────────────────────────

    # ── Colour palettes ───────────────────────────────────────────────────────
    # One unified dark background so labels never show contrast boxes.
    # Every surface uses the same base so parent/child bg always match.
    _DARK = {
        'bg':        '#2b2b2b',   # single background for everything
        'bg_input':  '#323232',   # entries / comboboxes / treeview rows
        'bg_btn':    '#3a3a3a',   # button face
        'bg_btn_act':'#484848',   # button hover/active
        'bg_sel':    '#3d6185',   # selection highlight (calm blue)
        'fg':        '#e0e0e0',   # primary text - near-white, not harsh
        'fg_dim':    '#999999',   # secondary text
        'fg_sel':    '#ffffff',   # selected text
        'border':    '#484848',   # widget borders
        # Status colours adapted for dark bg (softer, not pure bright)
        'fg_green':  '#6abf69',   # success / found
        'fg_orange': '#e0a86a',   # warning
        'fg_blue':   '#7eb8e8',   # info  (was jarring bright blue)
        'fg_red':    '#e07070',   # error
        'fg_gray':   '#888888',   # muted secondary
        # Treeview row tags  (muted pastels that work on dark bg)
        'tag_green': '#2d4a2d',   # direct_en
        'tag_blue':  '#2d3a4a',   # direct_other
        'tag_gray':  '#3a3a3a',   # direct
        'tag_green2':'#2d4a2d',   # both_cached
        'tag_yellow':'#3a3a26',   # cached / en
        'tag_cyan':  '#1e3a3a',   # selected lang
        'tag_red':   '#4a2d2d',   # other lang
    }
    def _snapshot_light(self):
        pass

    def _apply_dark_mode(self):
        """Switch to a clean dark theme.  One flat background everywhere so
        labels never show contrast boxes against their parent widget."""
        try:
            self._snapshot_light()
            BG      = '#2b2b2b'   # single surface colour - used for everything
            BG_IN   = '#333333'   # slightly raised: entries, treeview, comboboxes
            BG_BTN  = '#3a3a3a'   # button face
            BG_ACT  = '#4a4a4a'   # button hover / active
            BG_SEL  = '#3a5a7a'   # selection highlight - calm steel blue
            FG      = '#e0e0e0'   # primary text, near-white but not harsh
            FG_DIM  = '#909090'   # secondary / muted text
            FG_SEL  = '#ffffff'   # selected text
            BORDER  = '#484848'   # widget borders

            style = ttk.Style()
            style.theme_use('clam')

            self.root.configure(background=BG)

            # Universal base - every widget inherits unless overridden
            style.configure('.',
                background=BG, foreground=FG, bordercolor=BORDER,
                troughcolor=BG, focuscolor=BG)

            # Frames and labels - all share the same BG so there are no boxes
            style.configure('TFrame',            background=BG)
            style.configure('TLabel',            background=BG, foreground=FG)
            style.configure('TLabelframe',       background=BG, foreground=FG,
                                                 bordercolor=BORDER, relief='groove')
            style.configure('TLabelframe.Label', background=BG, foreground=FG)

            # Buttons
            style.configure('TButton', background=BG_BTN, foreground=FG,
                                       bordercolor=BORDER, focuscolor=BG,
                                       relief='flat', padding=4)
            style.map('TButton',
                background=[('active', BG_ACT), ('pressed', BG_IN)],
                foreground=[('active', FG), ('disabled', FG_DIM)],
                relief=[('pressed', 'sunken')])

            # Checkbuttons
            style.configure('TCheckbutton', background=BG, foreground=FG,
                                            focuscolor=BG)
            style.map('TCheckbutton',
                background=[('active', BG)],
                foreground=[('active', FG), ('disabled', FG_DIM)])

            # Text input widgets
            style.configure('TEntry',
                fieldbackground=BG_IN, foreground=FG,
                insertcolor=FG, bordercolor=BORDER,
                selectbackground=BG_SEL, selectforeground=FG_SEL)

            style.configure('TCombobox',
                fieldbackground=BG_IN, foreground=FG,
                background=BG_BTN, selectbackground=BG_SEL,
                selectforeground=FG_SEL, bordercolor=BORDER, arrowcolor=FG)
            style.map('TCombobox',
                fieldbackground=[('readonly', BG_IN)],
                foreground=[('readonly', FG)],
                selectbackground=[('readonly', BG_SEL)],
                selectforeground=[('readonly', FG_SEL)])
            # Subtitle combos - explicit styles so grey is visible in both themes
            style.configure('SubtitleActive.TCombobox',
                fieldbackground=BG_IN, foreground=FG,
                background=BG_BTN, selectbackground=BG_SEL,
                selectforeground=FG_SEL, bordercolor=BORDER, arrowcolor=FG)
            style.map('SubtitleActive.TCombobox',
                fieldbackground=[('readonly', BG_IN)],
                foreground=[('readonly', FG)],
                selectbackground=[('readonly', BG_SEL)],
                selectforeground=[('readonly', FG_SEL)])
            style.configure('SubtitleDisabled.TCombobox',
                fieldbackground='#4a4a4a', foreground='#666666',
                background='#3a3a3a', selectbackground='#4a4a4a',
                selectforeground='#666666', bordercolor=BORDER, arrowcolor='#555555')
            style.map('SubtitleDisabled.TCombobox',
                fieldbackground=[('readonly', '#4a4a4a'), ('disabled', '#4a4a4a')],
                foreground=[('readonly', '#666666'), ('disabled', '#666666')])
            # Auto-download disabled combo - darker grey in dark mode
            style.configure('Disabled.TCombobox',
                fieldbackground='#3a3a3a', foreground='#555555',
                background='#3a3a3a', arrowcolor='#555555')
            style.map('Disabled.TCombobox',
                fieldbackground=[('disabled', '#3a3a3a'), ('readonly', '#3a3a3a')],
                foreground=[('disabled', '#555555'), ('readonly', '#555555')])
            style.configure('Disabled.TCombobox',
                fieldbackground='#4a4a4a', foreground='#666666',
                background='#3a3a3a', arrowcolor='#555555')
            style.map('Disabled.TCombobox',
                fieldbackground=[('disabled', '#4a4a4a'), ('readonly', '#4a4a4a')],
                foreground=[('disabled', '#666666'), ('readonly', '#666666')])

            # Notebook tabs
            style.configure('TNotebook',     background=BG, bordercolor=BORDER)
            style.configure('TNotebook.Tab', background=BG_BTN, foreground=FG_DIM,
                                             padding=[8, 3], bordercolor=BORDER)
            style.map('TNotebook.Tab',
                background=[('selected', BG)],
                foreground=[('selected', FG)])

            # Treeview
            style.configure('Treeview',
                background=BG_IN, foreground=FG,
                fieldbackground=BG_IN,
                selectbackground=BG_SEL, selectforeground=FG_SEL,
                bordercolor=BORDER, rowheight=22)
            style.map('Treeview',
                background=[('selected', BG_SEL)],
                foreground=[('selected', FG_SEL)])
            style.configure('Treeview.Heading',
                background=BG_BTN, foreground=FG,
                bordercolor=BORDER, relief='flat')
            style.map('Treeview.Heading',
                background=[('active', BG_ACT)])

            # Scrollbars
            style.configure('TScrollbar',
                background=BG_BTN, troughcolor=BG,
                bordercolor=BORDER, arrowcolor=FG, relief='flat')
            style.map('TScrollbar',
                background=[('active', BG_ACT)])

            style.configure('TSeparator', background=BORDER)
            style.configure('TProgressbar', background='#5a8a5a', troughcolor=BG_IN)

            # Terminal widget (tk.Text, not ttk - set directly)
            if hasattr(self, 'terminal_text'):
                self.terminal_text.config(
                    background='#252525', foreground='#d4d4d4',
                    insertbackground='#d4d4d4')

            # Fix up treeview row tags for dark bg (muted pastels)
            for tree_attr in ('recommended_tree', 'combined_tree',
                              'video_tree', 'audio_tree', 'all_tree'):
                tree = getattr(self, tree_attr, None)
                if tree:
                    tree.tag_configure('direct_en',               background='#2a3d2a', foreground='#90d490')
                    tree.tag_configure('direct_other',            background='#2a3040', foreground='#90b8d4')
                    tree.tag_configure('direct',                  background='#363636', foreground=FG)
                    tree.tag_configure('combination_both_cached', background='#2a3d2a', foreground='#90d490')
                    tree.tag_configure('combination_cached',      background='#3a3a26', foreground='#d4c87a')
                    tree.tag_configure('combination_audio_cached',background='#2a3d2a', foreground='#90d490')
                    tree.tag_configure('combination_en',          background='#3a3a26', foreground='#d4c87a')
                    tree.tag_configure('combination_selected',    background='#263a3a', foreground='#80c8c8')
                    tree.tag_configure('combination_other',       background='#3a2e2e', foreground='#e8c0c0')

            # Update queue canvas background (raw tk widget, not ttk)
            if hasattr(self, '_queue_canvas'):
                self._queue_canvas.configure(background=BG)
            if hasattr(self, '_queue_listbox'):
                self._queue_listbox.configure(background=BG)
            if hasattr(self, '_refresh_queue_panel'):
                self._refresh_queue_panel()

            # Update hardcoded-colour labels stored as instance vars
            for lbl in getattr(self, '_themed_labels', {}).get('blue', []):
                try: lbl.config(foreground='#7eb8e8')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('green', []):
                try: lbl.config(foreground='#6abf69')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('orange', []):
                try: lbl.config(foreground='#d4945a')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('gray', []):
                try: lbl.config(foreground='#909090')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('red', []):
                try: lbl.config(foreground='#d47070')
                except Exception: pass
            for lbl in self.info_labels.values():
                try: lbl.config(foreground=FG)
                except Exception: pass

            self.dark_mode = True
            if hasattr(self, 'dark_mode_var'):
                self.dark_mode_var.set(True)
            # Re-apply correct subtitle combo style now that styles are registered
            self._update_subtitle_combo_states()
        except Exception as e:
            print('Dark mode error: ' + str(e))

    def _apply_light_mode(self):
        """Restore the original light colour scheme."""
        try:
            style = ttk.Style()

            SYS_BG   = 'SystemButtonFace'
            SYS_FG   = 'SystemButtonText'
            SYS_WIN  = 'SystemWindow'
            SYS_HI   = 'SystemHighlight'
            SYS_HIFG = 'SystemHighlightText'

            self.root.configure(background=SYS_BG)

            style.configure('.',
                background=SYS_BG, foreground=SYS_FG,
                bordercolor='#6d6d6d', troughcolor=SYS_BG, focuscolor=SYS_BG)
            style.configure('TFrame',            background=SYS_BG)
            style.configure('TLabel',            background=SYS_BG, foreground=SYS_FG)
            style.configure('TLabelframe',       background=SYS_BG, foreground=SYS_FG,
                                                 bordercolor='#6d6d6d', relief='groove')
            style.configure('TLabelframe.Label', background=SYS_BG, foreground=SYS_FG)

            style.configure('TButton',
                background=SYS_BG, foreground=SYS_FG,
                bordercolor='#6d6d6d', focuscolor=SYS_BG,
                relief='raised', padding=4)
            style.map('TButton',
                background=[('active', SYS_BG), ('pressed', SYS_BG), ('disabled', SYS_BG)],
                foreground=[('active', SYS_FG), ('disabled', 'SystemDisabledText')],
                relief=[('pressed', 'sunken'), ('!pressed', 'raised')])

            style.configure('TCheckbutton',
                background=SYS_BG, foreground=SYS_FG, focuscolor=SYS_BG)
            style.map('TCheckbutton',
                background=[('active', SYS_BG)],
                foreground=[('active', SYS_FG), ('disabled', 'SystemDisabledText')])

            style.configure('TEntry',
                fieldbackground=SYS_WIN, foreground=SYS_FG,
                insertcolor=SYS_FG, bordercolor='#6d6d6d',
                selectbackground=SYS_HI, selectforeground=SYS_HIFG)

            style.configure('TCombobox',
                fieldbackground=SYS_WIN, foreground=SYS_FG,
                background=SYS_BG, selectbackground=SYS_HI,
                selectforeground=SYS_HIFG, bordercolor='#6d6d6d', arrowcolor=SYS_FG)
            style.map('TCombobox',
                fieldbackground=[('readonly', SYS_WIN)],
                foreground=[('readonly', SYS_FG)],
                selectbackground=[('readonly', SYS_HI)],
                selectforeground=[('readonly', SYS_HIFG)])
            # Subtitle combos - explicit styles so grey is visible in both themes
            style.configure('SubtitleActive.TCombobox',
                fieldbackground=SYS_WIN, foreground=SYS_FG,
                background=SYS_BG, selectbackground=SYS_HI,
                selectforeground=SYS_HIFG, bordercolor='#6d6d6d', arrowcolor=SYS_FG)
            style.map('SubtitleActive.TCombobox',
                fieldbackground=[('readonly', SYS_WIN)],
                foreground=[('readonly', SYS_FG)],
                selectbackground=[('readonly', SYS_HI)],
                selectforeground=[('readonly', SYS_HIFG)])
            style.configure('SubtitleDisabled.TCombobox',
                fieldbackground='#d0d0d0', foreground='#888888',
                background='#d0d0d0', selectbackground='#d0d0d0',
                selectforeground='#888888', bordercolor='#aaaaaa', arrowcolor='#aaaaaa')
            style.map('SubtitleDisabled.TCombobox',
                fieldbackground=[('readonly', '#d0d0d0'), ('disabled', '#d0d0d0')],
                foreground=[('readonly', '#888888'), ('disabled', '#888888')])
            style.configure('Disabled.TCombobox',
                fieldbackground='#d0d0d0', foreground='#888888',
                background='#d0d0d0', arrowcolor='#aaaaaa')
            style.map('Disabled.TCombobox',
                fieldbackground=[('disabled', '#d0d0d0'), ('readonly', '#d0d0d0')],
                foreground=[('disabled', '#888888'), ('readonly', '#888888')])

            style.configure('TNotebook',
                background=SYS_BG, bordercolor='#6d6d6d')
            style.configure('TNotebook.Tab',
                background=SYS_BG, foreground=SYS_FG,
                padding=[8, 3], bordercolor='#6d6d6d')
            style.map('TNotebook.Tab',
                background=[('selected', SYS_BG)],
                foreground=[('selected', SYS_FG)])

            style.configure('Treeview',
                background=SYS_WIN, foreground=SYS_FG,
                fieldbackground=SYS_WIN,
                selectbackground=SYS_HI, selectforeground=SYS_HIFG,
                bordercolor='#6d6d6d', rowheight=22)
            style.map('Treeview',
                background=[('selected', SYS_HI)],
                foreground=[('selected', SYS_HIFG)])
            style.configure('Treeview.Heading',
                background=SYS_BG, foreground=SYS_FG,
                bordercolor='#6d6d6d', relief='raised')
            style.map('Treeview.Heading',
                background=[('active', SYS_BG)])

            style.configure('TScrollbar',
                background=SYS_BG, troughcolor=SYS_BG,
                bordercolor='#6d6d6d', arrowcolor=SYS_FG, relief='raised')
            style.map('TScrollbar',
                background=[('active', SYS_BG)])

            style.configure('TSeparator',   background='#c0c0c0')
            style.configure('TProgressbar', background='#4a90d9', troughcolor=SYS_BG)

            if hasattr(self, 'terminal_text'):
                self.terminal_text.config(
                    background='#1e1e1e', foreground='#d4d4d4',
                    insertbackground='white')

            for tree_attr in ('recommended_tree', 'combined_tree',
                              'video_tree', 'audio_tree', 'all_tree'):
                tree = getattr(self, tree_attr, None)
                if tree:
                    tree.tag_configure('direct_en',               background='lightgreen',  foreground='')
                    tree.tag_configure('direct_other',            background='lightblue',   foreground='')
                    tree.tag_configure('direct',                  background='lightgray',   foreground='')
                    tree.tag_configure('combination_both_cached', background='#90EE90',     foreground='darkgreen')
                    tree.tag_configure('combination_cached',      background='lightyellow', foreground='darkgreen')
                    tree.tag_configure('combination_audio_cached',background='#E0FFE0',     foreground='darkgreen')
                    tree.tag_configure('combination_en',          background='lightyellow', foreground='')
                    tree.tag_configure('combination_selected',    background='lightcyan',   foreground='')
                    tree.tag_configure('combination_other',       background='lightcoral',  foreground='')

            if hasattr(self, '_queue_canvas'):
                self._queue_canvas.configure(background=SYS_BG)
            if hasattr(self, '_queue_listbox'):
                self._queue_listbox.configure(background=SYS_BG)
            if hasattr(self, '_refresh_queue_panel'):
                self._refresh_queue_panel()

            for lbl in getattr(self, '_themed_labels', {}).get('blue', []):
                try: lbl.config(foreground='blue')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('green', []):
                try: lbl.config(foreground='green')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('orange', []):
                try: lbl.config(foreground='orange')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('gray', []):
                try: lbl.config(foreground='gray')
                except Exception: pass
            for lbl in getattr(self, '_themed_labels', {}).get('red', []):
                try: lbl.config(foreground='red')
                except Exception: pass
            for lbl in self.info_labels.values():
                try: lbl.config(foreground='gray')
                except Exception: pass

            self.dark_mode = False
            if hasattr(self, 'dark_mode_var'):
                self.dark_mode_var.set(False)

            # Re-apply correct subtitle combo style now that styles are registered
            self._update_subtitle_combo_states()
            self.root.update_idletasks()

        except Exception as e:
            print('Light mode error: ' + str(e))


    # ── Playlist support ───────────────────────────────────────────────────

    def is_playlist_url(self, url):
        """Return True if the URL looks like a YouTube playlist or channel."""
        # M8 fix: require a YouTube domain, otherwise clipboard-watch fires
        # on e.g. tiktok.com/@user or any URL containing 'list='.
        _u = (url or '').lower()
        if ('youtube.com' not in _u) and ('youtu.be' not in _u):
            return False
        return ('list=' in url or 'youtube.com/playlist' in url or
                '/c/' in url or '/channel/' in url or '/@' in url)

    def _handle_playlist_worker(self, url):
        """Detect playlist size, confirm with user, then enqueue each video."""
        try:
            self.root.after(0, lambda: self.paste_btn.config(state='disabled'))
            self.root.after(0, lambda: self.progress_bar.start())
            self.root.after(0, lambda: self.progress_var.set("Detecting playlist..."))
            self.append_terminal_output('Detecting playlist: ' + url + '\n', 'info')

            # Get flat playlist entries to count videos
            args = [
                '--flat-playlist', '--dump-json', '--no-warnings',
                '--extractor-args', 'youtube:player_client=default,-tv_simply',
            ]
            args.extend(self.get_ytdlp_dns_args())
            if self.yt_dlp_cache_dir:
                args.extend(['--cache-dir', self.yt_dlp_cache_dir])
            args.append(url)

            result = self.run_ytdlp_command(args, timeout=60)
            if result.returncode != 0 or not result.stdout.strip():
                self.root.after(0, lambda: self._notify_error(
                    "Playlist Error", "Could not read playlist. Is the URL correct?"))
                return

            lines = [l for l in result.stdout.strip().splitlines() if l.strip()]
            entries = []
            for line in lines:
                try:
                    entries.append(json.loads(line))
                except Exception:
                    pass

            n = len(entries)
            if n == 0:
                self.root.after(0, lambda: self._notify_warning(
                    "Playlist", "No videos found in playlist."))
                return

            self.append_terminal_output(
                'Playlist detected: ' + str(n) + ' video(s)\n', 'info')

            # Confirm with user on main thread
            confirmed = threading.Event()
            single_only = threading.Event()

            def ask():
                ans = messagebox.askyesnocancel(
                    "Playlist Detected",
                    "Playlist detected (" + str(n) + " video(s))." + "\n\n"
                    "Yes  - Queue all " + str(n) + " videos\n"
                    "No   - Analyze first video only\n"
                    "Cancel - Abort")
                if ans is True:
                    confirmed.set()
                elif ans is False:
                    single_only.set()
                    confirmed.set()

            self.root.after(0, ask)
            confirmed.wait(timeout=120)

            if single_only.is_set():
                # Analyze just the first video
                first_id = entries[0].get('id') or entries[0].get('url', '')
                if first_id:
                    video_url = 'https://www.youtube.com/watch?v=' + first_id
                    self.root.after(0, lambda u=video_url: self.url_var.set(u))
                    self.root.after(100, self.analyze_video)
                return

            if not confirmed.is_set():
                self.append_terminal_output('Playlist queuing cancelled.\n', 'warning')
                return

            # Queue all videos at default quality
            _target_q = getattr(self, 'default_quality', '') or ''
            if not _target_q:
                # Mirror the batch-mode guard: with Auto-Download OFF there
                # is no quality to queue at. Previously this line silently
                # forced 1080p, ignoring the user's OFF state.
                self.root.after(0, lambda: self._notify_warning(
                    "Playlist",
                    "Auto-Download is disabled.\n"
                    "Enable it and select a quality so each video knows"
                    " what to queue."))
                return
            target_q = _target_q
            self.append_terminal_output(
                'Queuing playlist at ' + target_q + '...\n', 'info')

            for i, entry in enumerate(entries):
                vid_id = entry.get('id') or entry.get('url', '')
                if not vid_id:
                    continue
                video_url = 'https://www.youtube.com/watch?v=' + vid_id
                self.root.after(0, lambda u=video_url, pos=i, total=n:
                    self.append_terminal_output(
                        'Queuing playlist: ' + str(pos + 1) + '/' + str(total) + '\n', 'info'))
                try:
                    info = self.get_video_info(video_url)
                    all_formats = info.get('formats', [])

                    # Work entirely with local variables - never touch self.* shared state
                    # from a background thread to avoid races with the main thread.
                    local_video_streams = [
                        f for f in all_formats
                        if f.get('vcodec') not in (None, 'none')
                        and f.get('acodec') in (None, 'none')]
                    local_audio_streams = [
                        f for f in all_formats
                        if f.get('acodec') not in (None, 'none')
                        and f.get('vcodec') in (None, 'none')]

                    local_detected = {}
                    for fmt in local_audio_streams:
                        if 'detected_language' not in fmt:
                            desc, lang = self.get_audio_stream_description(fmt)
                            fmt['detected_language'] = lang
                            fmt['description'] = desc
                        local_detected.setdefault(fmt['detected_language'], []).append(fmt)

                    best_audio = self.select_best_audio_stream(
                        local_audio_streams, local_detected)

                    target_h = int(target_q.replace('p', ''))
                    # Use tier matching so non-standard resolutions (e.g.
                    # 1086p) are matched when the target is 1080p.  Also use
                    # min(h, w) for consistency with the recommended tab.
                    def _pl_eff(v):
                        _h = v.get('height', 0) or 0
                        _w = v.get('width', 0) or 0
                        return min(_h, _w) if _h and _w else (_h or _w)

                    pl_candidates = [v for v in local_video_streams
                                     if _pl_eff(v) > 0 and self._nearest_standard_quality(_pl_eff(v)) == target_h]
                    best_video = self.select_best_video_stream(pl_candidates)

                    if best_video and best_audio:
                        vfid = str(best_video.get('format_id', ''))
                        afid = str(best_audio.get('format_id', ''))
                        title = info.get('title', 'Unknown')
                        raw_ch = (info.get('uploader') or info.get('channel') or '').strip()
                        ch = self.sanitize_filename(raw_ch) if raw_ch else ''
                        safe_t = self.sanitize_filename(title)
                        base = (ch + ' - ' + safe_t) if ch else safe_t
                        out_path = os.path.join(
                            self.download_path, base + ' [' + target_q + '].mp4')
                        label = base + '  [' + target_q + ']'
                        vid_id_snap = info.get('id', 'unknown')
                        use_c = self.get_cached_video_path(vid_id_snap, vfid) is not None
                        c_path = self.get_cached_video_path(vid_id_snap, vfid)
                        w_args = (vfid, afid, out_path, target_q,
                                  use_c, c_path, None, video_url, vid_id_snap, info)
                        entry_dict = {
                            'worker': self._download_and_merge_worker_with_terminal,
                            'worker_name': 'merge',
                            'args': w_args, 'label': label, 'is_audio': False}
                        # M1 fix: queue mutations follow the _queue_lock
                        # convention used everywhere else in the file.
                        with self._queue_lock:
                            self._download_queue.append(entry_dict)
                        self.root.after(0, self._refresh_queue_panel)
                except Exception as e:
                    self.append_terminal_output(
                        'Skipped video ' + str(i + 1) + ': ' + str(e) + '\n', 'warning')

            with self._queue_lock:
                _q_n = len(self._download_queue)
            self.append_terminal_output(
                'Playlist queuing complete. ' + str(_q_n) +
                ' item(s) in queue.\n', 'success')
            self.root.after(0, self._refresh_queue_panel)
            # M1 fix: actually start the queue. Every other enqueue path
            # (manual 'Download', batch, session restore) triggers
            # _start_next_queued; playlist items previously sat idle until
            # an unrelated download kicked the queue.
            self.root.after(500, lambda: (
                self._start_next_queued()
                if not self._download_active and not self._download_paused
                else None))

        except Exception as e:
            err = str(e)
            self.root.after(0, lambda m=err: self._notify_error("Playlist Error", m))
        finally:
            self.root.after(0, lambda: self.progress_bar.stop())
            self.root.after(0, lambda: self.progress_var.set("Ready"))
            self.root.after(0, lambda: self.paste_btn.config(state='normal'))


def main():
    """Main application entry point with error handling"""
    try:
        root = tk.Tk()
        app = YouTubeStreamAnalyzerGUI(root)  # noqa: F841 - holds ref to prevent GC
        
        # Center window on screen
        root.update_idletasks()
        height = root.winfo_height()
        # Place window so its left edge starts a few pixels right of screen centre,
        # keeping it vertically centred.
        x = (root.winfo_screenwidth() // 2) + 20
        y = max(0, (root.winfo_screenheight() // 2) - (height // 2))
        root.geometry(f"+{x}+{y}")
        
        root.mainloop()
        
    except ImportError as e:
        error_msg = "Missing required module: " + str(e) + "\n\nPlease ensure yt-dlp.exe is available"
        show_error_dialog("Import Error", error_msg)
        sys.exit(1)
        
    except Exception as e:
        error_msg = "Failed to start YSA:\n\n" + str(e) + "\n\nWorking directory: " + os.getcwd() + "\nScript location: " + str(SCRIPT_DIR)
        show_error_dialog("Startup Error", error_msg)
        log_error("YSA Startup Error: " + str(e) + "\nWorking dir: " + os.getcwd() + "\nScript dir: " + str(SCRIPT_DIR))
        sys.exit(1)

def show_error_dialog(title, message):
    """Show error dialog with copyable text, fallback to console if GUI fails"""
    try:
        # Try to show GUI error dialog with copyable text
        root = tk.Tk()
        root.withdraw()  # Hide the root window
        
        # Create custom error dialog with copyable text
        error_dialog = tk.Toplevel(root)
        error_dialog.title(title)
        error_dialog.geometry("600x400")
        error_dialog.transient(root)
        error_dialog.grab_set()
        
        # Make window appear on top
        error_dialog.lift()
        error_dialog.attributes('-topmost', True)
        
        # Title label
        title_label = ttk.Label(error_dialog, text=title, font=('Arial', 12, 'bold'), foreground="red")
        title_label.pack(pady=10)
        
        # Scrollable text area with the error message
        text_frame = ttk.Frame(error_dialog)
        text_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=(0, 10))
        
        error_text = scrolledtext.ScrolledText(text_frame, wrap=tk.WORD, font=('Consolas', 9))
        error_text.pack(fill=tk.BOTH, expand=True)
        error_text.insert('1.0', message)
        error_text.config(state='normal')  # Keep it editable so text can be selected and copied
        
        # Button frame
        btn_frame = ttk.Frame(error_dialog)
        btn_frame.pack(pady=10)
        
        def copy_error():
            root.clipboard_clear()
            root.clipboard_append(message)
            copy_btn.config(text="Copied!")
            root.after(2000, lambda: copy_btn.config(text="Copy Error"))
        
        def close_dialog():
            error_dialog.destroy()
            root.destroy()
        
        copy_btn = ttk.Button(btn_frame, text="Copy Error", command=copy_error)
        copy_btn.pack(side=tk.LEFT, padx=5)
        
        close_btn = ttk.Button(btn_frame, text="Close", command=close_dialog)
        close_btn.pack(side=tk.LEFT, padx=5)
        
        # Center the dialog
        error_dialog.update_idletasks()
        width = error_dialog.winfo_width()
        height = error_dialog.winfo_height()
        x = (error_dialog.winfo_screenwidth() // 2) - (width // 2)
        y = (error_dialog.winfo_screenheight() // 2) - (height // 2)
        error_dialog.geometry(f"+{x}+{y}")
        
        # Wait for dialog to close
        error_dialog.wait_window()
        
    except Exception as e:
        # Fallback to console output
        print("\n" + str(title) + ": " + str(message))
        print("\nAdditional error showing dialog: " + str(e))
        try:
            input("Press Enter to exit...")
        except:
            time.sleep(3)

def log_error(message):
    """Log error to file for debugging"""
    try:
        log_file = os.path.join(SCRIPT_DIR, "YSA_error.log")
        with open(log_file, "w") as f:
            f.write("YSA Error Log - " + time.strftime('%Y-%m-%d %H:%M:%S') + "\n")
            f.write("=" * 50 + "\n")
            f.write(message + "\n")
            f.write("=" * 50 + "\n")
            f.write("Python version: " + str(sys.version) + "\n")
            f.write("Platform: " + str(sys.platform) + "\n")
            f.write("Working directory: " + os.getcwd() + "\n")
            f.write("Script directory: " + str(SCRIPT_DIR) + "\n")
            f.write("Executable: " + str(sys.executable) + "\n")
            f.write("yt-dlp executable: " + str(YTDLP_PATH) + "\n")
            if hasattr(sys, 'frozen'):
                f.write("Running as: PyInstaller executable\n")
            else:
                f.write("Running as: Python script\n")
    except:
        pass  # Ignore logging errors

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\nYSA interrupted by user")
        sys.exit(0)
    except Exception as e:
        # Final fallback error handling
        error_msg = f"Critical error starting YSA: {e}"
        log_error(error_msg)
        try:
            print(error_msg)
            input("Press Enter to exit...")
        except:
            pass
        sys.exit(1)
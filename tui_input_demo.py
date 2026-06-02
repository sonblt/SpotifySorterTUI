#!/usr/bin/env python3
"""Simple TUI with Spotify PKCE login and playlist listing."""

from __future__ import annotations

import curses
import base64
import datetime
import hashlib
import json
import os
import secrets
import shutil
import subprocess
import threading
import textwrap
import time
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from collections.abc import Callable
from dataclasses import dataclass, field
from http.server import BaseHTTPRequestHandler, HTTPServer


SPOTIFY_AUTH_URL = "https://accounts.spotify.com/authorize"
SPOTIFY_TOKEN_URL = "https://accounts.spotify.com/api/token"
SPOTIFY_PLAYLISTS_URL = "https://api.spotify.com/v1/me/playlists"
SPOTIFY_PLAYLIST_FIELDS = "items(id,name,snapshot_id,owner(id),tracks(total),items(total)),next,total"
SPOTIFY_PLAYLIST_ITEMS_FIELDS = "items(item(name,uri,artists(name))),next,total"
SPOTIFY_PLAYLIST_TRACKS_FIELDS = "items(track(name,uri,artists(name))),next,total"
SPOTIFY_PLAYLIST_TRACKS_LIMIT = 50
SPOTIFY_PLAYLIST_TRACKS_URL_TEMPLATE = "https://api.spotify.com/v1/playlists/{playlist_id}/tracks"
SPOTIFY_PLAYLIST_ITEMS_URL_TEMPLATE = "https://api.spotify.com/v1/playlists/{playlist_id}/items"
SPOTIFY_USER_PLAYLISTS_URL_TEMPLATE = "https://api.spotify.com/v1/users/{user_id}/playlists"
SPOTIFY_SCOPE = (
    "playlist-read-private playlist-read-collaborative playlist-modify-private "
    "playlist-modify-public user-library-read user-read-private user-read-email"
)
SPOTIFY_MAX_RETRIES = 4
TOKEN_EXPIRY_BUFFER_SECONDS = 30
DEFAULT_TOKEN_EXPIRY_SECONDS = 3600
INITIAL_BACKOFF_SECONDS = 1.0
PKCE_VERIFIER_BYTES = 64
DEFAULT_PLAYLIST_NAME = "Unnamed Playlist"
DEFAULT_TRACK_NAME = "Unknown Track"
UI_POLL_INTERVAL_MS = 100
DEFAULT_SPOTIFY_SYNC_INTERVAL_SECONDS = 60
UI_HELP_TEXT = (
    "c: connect (disconnected only)  ↑/↓: move in focused pane  "
    "→: open/focus next pane  ←: previous pane  Enter: action in move pane  q: quit"
)
MIN_COLS_FOR_SPLIT_PANE = 70
MIN_LEFT_PANEL_WIDTH = 24
PANEL_PLAYLISTS = "playlists"
PANEL_TRACKS = "tracks"
PANEL_TARGETS = "targets"
CREATE_PLAYLIST_OPTION_LABEL = "+ Create new playlist"


@dataclass(slots=True)
class TrackInfo:
    display: str
    uri: str = ""


@dataclass(slots=True)
class PlaylistInfo:
    id: str
    name: str
    track_total: int
    snapshot_id: str = ""
    owner_id: str = ""
    tracks: list[TrackInfo] = field(default_factory=list)
    tracks_loaded: bool = False


@dataclass(slots=True)
class SpotifySession:
    client_id: str
    token_cache: dict[str, object]


class SpotifyApiError(RuntimeError):
    def __init__(self, status_code: int, error_message: str) -> None:
        super().__init__(f"Spotify API error {status_code}: {error_message}")
        self.status_code = status_code
        self.error_message = error_message


@dataclass(slots=True)
class UiState:
    connection_status: str = "disconnected"
    status_message: str = "Press c to connect to Spotify with PKCE."
    error_message: str = ""
    playlists: list[PlaylistInfo] = field(default_factory=list)
    selected_index: int = 0
    opened_playlist_id: str | None = None
    focused_panel: str = PANEL_PLAYLISTS
    tracks_selected_index: int = 0
    target_selected_index: int = 0
    creating_playlist: bool = False
    new_playlist_name: str = ""
    session: SpotifySession | None = None


def _base64_url_encode(data: bytes) -> str:
    return base64.urlsafe_b64encode(data).rstrip(b"=").decode("utf-8")


def _build_pkce_pair() -> tuple[str, str]:
    code_verifier = secrets.token_urlsafe(PKCE_VERIFIER_BYTES)
    challenge_raw = hashlib.sha256(code_verifier.encode("utf-8")).digest()
    code_challenge = _base64_url_encode(challenge_raw)
    return code_verifier, code_challenge


def _open_authorization_page(auth_url: str) -> None:
    parsed_auth_url = urllib.parse.urlparse(auth_url)

    if parsed_auth_url.scheme != "https" or not parsed_auth_url.netloc:
        raise RuntimeError("Generated Spotify authorization URL is invalid.")

    try:
        subprocess.Popen(
            ["microsoft-edge-stable", auth_url],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            close_fds=True,
            start_new_session=True,
        )
    except OSError as e:
        raise RuntimeError(
            f"Failed to launch Microsoft Edge. Open this URL manually: {auth_url}"
        ) from e


def _validate_redirect_uri(redirect_uri: str) -> urllib.parse.ParseResult:
    parsed = urllib.parse.urlparse(redirect_uri)
    if not parsed.hostname:
        raise RuntimeError("SPOTIFY_REDIRECT_URI must include a hostname.")
    if parsed.scheme == "https":
        return parsed
    if parsed.scheme == "http" and parsed.hostname == "127.0.0.1":
        return parsed
    raise RuntimeError(
        "SPOTIFY_REDIRECT_URI must use https://, except http://127.0.0.1 for local development."
    )


def _wait_for_auth_code(redirect_uri: str, expected_state: str, timeout_seconds: int = 180) -> str:
    parsed = _validate_redirect_uri(redirect_uri)
    if parsed.scheme != "http" or parsed.hostname != "127.0.0.1" or not parsed.port:
        raise RuntimeError(
            "Local callback listener requires SPOTIFY_REDIRECT_URI like http://127.0.0.1:8888/callback."
        )

    result: dict[str, str] = {}
    done = threading.Event()

    class CallbackHandler(BaseHTTPRequestHandler):
        def do_GET(self) -> None:  # noqa: N802 - required by BaseHTTPRequestHandler
            request_url = urllib.parse.urlparse(self.path)
            if request_url.path != parsed.path:
                self.send_response(404)
                self.end_headers()
                return

            query = urllib.parse.parse_qs(request_url.query)
            state = query.get("state", [""])[0]
            code = query.get("code", [""])[0]
            error = query.get("error", [""])[0]

            if state != expected_state:
                result["error"] = "Invalid OAuth state returned by Spotify."
            elif error:
                result["error"] = f"Spotify authorization error: {error}"
            elif not code:
                result["error"] = "No authorization code returned by Spotify."
            else:
                result["code"] = code

            self.send_response(200)
            self.send_header("Content-Type", "text/html; charset=utf-8")
            self.end_headers()
            self.wfile.write(
                b"<html><body><h2>Spotify authorization complete.</h2>"
                b"<p>You can return to the terminal.</p></body></html>"
            )
            done.set()

        def log_message(self, fmt: str, *args: object) -> None:
            pass

    server = HTTPServer((parsed.hostname, parsed.port), CallbackHandler)
    thread = threading.Thread(target=server.serve_forever, daemon=True)
    thread.start()

    try:
        deadline = time.time() + timeout_seconds
        while time.time() < deadline:
            if done.wait(timeout=0.25):
                break
        else:
            raise TimeoutError("Timed out waiting for Spotify authorization callback.")
    finally:
        server.shutdown()
        server.server_close()

    if "error" in result:
        raise RuntimeError(result["error"])
    return result["code"]


def _read_error_message(error_body: bytes, status_code: int) -> str:
    default_message = f"HTTP {status_code}"
    if not error_body:
        return default_message
    try:
        payload = json.loads(error_body.decode("utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError):
        return default_message

    if isinstance(payload, dict):
        nested_error = payload.get("error")
        if isinstance(nested_error, dict):
            message = nested_error.get("message")
            if isinstance(message, str) and message.strip():
                return message.strip()
        if isinstance(nested_error, str):
            description = payload.get("error_description")
            if isinstance(description, str) and description.strip():
                return f"{nested_error}: {description.strip()}"
            if nested_error.strip():
                return nested_error.strip()
    return default_message


def _safe_int(value: object, default: int) -> int:
    if isinstance(value, int):
        return value
    if isinstance(value, str):
        try:
            return int(value)
        except ValueError:
            return default
    return default


def _safe_non_empty_string(value: object, default: str) -> str:
    if isinstance(value, str):
        normalized = value.strip()
        if normalized:
            return normalized
    return default


def _spotify_request_json(
    url: str,
    *,
    method: str = "GET",
    headers: dict[str, str] | None = None,
    form_body: dict[str, str] | None = None,
    json_body: dict[str, object] | list[object] | None = None,
    max_retries: int = SPOTIFY_MAX_RETRIES,
) -> dict[str, object]:
    body: bytes | None = None
    request_headers = dict(headers or {})
    if form_body is not None and json_body is not None:
        raise ValueError("Cannot provide both form_body and json_body to the same request.")
    if form_body is not None:
        body = urllib.parse.urlencode(form_body).encode("utf-8")
        request_headers["Content-Type"] = "application/x-www-form-urlencoded"
    elif json_body is not None:
        body = json.dumps(json_body).encode("utf-8")
        request_headers["Content-Type"] = "application/json"

    backoff_seconds = INITIAL_BACKOFF_SECONDS
    for attempt in range(max_retries + 1):
        request = urllib.request.Request(url, data=body, method=method, headers=request_headers)
        try:
            with urllib.request.urlopen(request, timeout=20) as response:
                response_text = response.read().decode("utf-8")
            payload = json.loads(response_text) if response_text else {}
            if isinstance(payload, dict):
                return payload
            raise RuntimeError("Spotify returned an unexpected response format.")
        except urllib.error.HTTPError as exc:
            error_body = exc.read()
            error_message = _read_error_message(error_body, exc.code)
            if exc.code == 429 and attempt < max_retries:
                retry_after_header = exc.headers.get("Retry-After", "").strip()
                try:
                    sleep_seconds = max(0.0, float(retry_after_header))
                except ValueError:
                    sleep_seconds = backoff_seconds
                    try:
                        retry_after_time = datetime.datetime.strptime(
                            retry_after_header,
                            "%a, %d %b %Y %H:%M:%S GMT",
                        ).replace(tzinfo=datetime.timezone.utc)
                        now_utc = datetime.datetime.now(datetime.timezone.utc)
                        sleep_seconds = max(0.0, (retry_after_time - now_utc).total_seconds())
                    except ValueError:
                        pass
                time.sleep(sleep_seconds)
                backoff_seconds *= 2.0
                continue
            raise SpotifyApiError(exc.code, error_message) from exc
        except urllib.error.URLError as exc:
            raise RuntimeError(f"Network error while contacting Spotify: {exc.reason}") from exc

    raise RuntimeError("Spotify request failed after retries.")


def _exchange_code_for_token(
    client_id: str, redirect_uri: str, code: str, code_verifier: str
) -> dict[str, object]:
    payload = _spotify_request_json(
        SPOTIFY_TOKEN_URL,
        method="POST",
        form_body={
            "client_id": client_id,
            "grant_type": "authorization_code",
            "code": code,
            "redirect_uri": redirect_uri,
            "code_verifier": code_verifier,
        },
    )
    access_token = payload.get("access_token")
    if not access_token:
        raise RuntimeError("No access token received from Spotify.")
    expires_in = _safe_int(payload.get("expires_in"), DEFAULT_TOKEN_EXPIRY_SECONDS)
    return {
        "access_token": access_token,
        "refresh_token": payload.get("refresh_token"),
        "expires_at": time.time() + expires_in - TOKEN_EXPIRY_BUFFER_SECONDS,
    }


def _refresh_access_token(client_id: str, refresh_token: str) -> dict[str, object]:
    payload = _spotify_request_json(
        SPOTIFY_TOKEN_URL,
        method="POST",
        form_body={
            "client_id": client_id,
            "grant_type": "refresh_token",
            "refresh_token": refresh_token,
        },
    )
    access_token = payload.get("access_token")
    if not access_token:
        raise RuntimeError("Spotify refresh response did not include an access token.")
    expires_in = _safe_int(payload.get("expires_in"), DEFAULT_TOKEN_EXPIRY_SECONDS)
    return {
        "access_token": access_token,
        "refresh_token": payload.get("refresh_token", refresh_token),
        "expires_at": time.time() + expires_in - TOKEN_EXPIRY_BUFFER_SECONDS,
    }


def _get_access_token(
    client_id: str,
    token_cache: dict[str, object],
    force_refresh: bool = False,
) -> str:
    access_token = token_cache.get("access_token")
    raw_expires_at = token_cache.get("expires_at", 0)
    if isinstance(raw_expires_at, (float, int)):
        expires_at = float(raw_expires_at)
    elif isinstance(raw_expires_at, str):
        try:
            expires_at = float(raw_expires_at)
        except ValueError:
            expires_at = 0.0
    else:
        expires_at = 0.0

    current_time = time.time()
    if not force_refresh and isinstance(access_token, str) and access_token and current_time < expires_at:
        return access_token

    refresh_token = token_cache.get("refresh_token")
    if not isinstance(refresh_token, str) or not refresh_token:
        raise RuntimeError("Access token expired and no refresh token is available.")
    refreshed = _refresh_access_token(client_id, refresh_token)
    token_cache.update(refreshed)
    return str(token_cache["access_token"])


def _parse_playlist_item(item: object) -> PlaylistInfo | None:
    if not isinstance(item, dict):
        return None
    playlist_id = item.get("id")
    if not isinstance(playlist_id, str) or not playlist_id:
        return None
    name = _safe_non_empty_string(item.get("name"), DEFAULT_PLAYLIST_NAME)
    snapshot_id = _safe_non_empty_string(item.get("snapshot_id"), "")
    owner_id = ""
    owner = item.get("owner")
    if isinstance(owner, dict):
        owner_id = _safe_non_empty_string(owner.get("id"), "")
    tracks_value = item.get("tracks")
    if not isinstance(tracks_value, dict):
        tracks_value = item.get("items")
    track_total = 0
    if isinstance(tracks_value, dict):
        track_total = _safe_int(tracks_value.get("total"), 0)
    return PlaylistInfo(
        id=playlist_id,
        name=name,
        track_total=max(0, track_total),
        snapshot_id=snapshot_id,
        owner_id=owner_id,
    )


def _fetch_current_user_id(
    client_id: str,
    token_cache: dict[str, object],
) -> str:
    access_token = _get_access_token(client_id, token_cache)
    payload = _spotify_request_json(
        "https://api.spotify.com/v1/me",
        headers={"Authorization": f"Bearer {access_token}"},
    )
    return _safe_non_empty_string(payload.get("id"), "")


def _parse_track_item(item: object) -> TrackInfo:
    if not isinstance(item, dict):
        return TrackInfo(display=DEFAULT_TRACK_NAME)
    track = item.get("item")
    if not isinstance(track, dict):
        track = item.get("track")
    if not isinstance(track, dict):
        return TrackInfo(display=DEFAULT_TRACK_NAME)
    track_name = _safe_non_empty_string(track.get("name"), DEFAULT_TRACK_NAME)
    track_uri = _safe_non_empty_string(track.get("uri"), "")
    artists_raw = track.get("artists", [])
    artist_names: list[str] = []
    if isinstance(artists_raw, list):
        for artist in artists_raw:
            if not isinstance(artist, dict):
                continue
            artist_name = _safe_non_empty_string(artist.get("name"), "")
            if artist_name:
                artist_names.append(artist_name)
    if not artist_names:
        return TrackInfo(display=track_name, uri=track_uri)
    return TrackInfo(display=f"{track_name} — {', '.join(artist_names)}", uri=track_uri)


def _fetch_playlist_tracks_page(
    client_id: str,
    token_cache: dict[str, object],
    playlist_id: str,
    *,
    endpoint_url_template: str,
    fields: str,
    force_refresh: bool = False,
) -> list[TrackInfo]:
    track_entries: list[TrackInfo] = []
    query = urllib.parse.urlencode(
        {
            "limit": SPOTIFY_PLAYLIST_TRACKS_LIMIT,
            "fields": fields,
        }
    )
    quoted_playlist_id = urllib.parse.quote(playlist_id, safe="")
    next_url = endpoint_url_template.format(playlist_id=quoted_playlist_id)
    next_url = f"{next_url}?{query}"
    page_num = 0
    while next_url:
        page_num += 1
        access_token = _get_access_token(client_id, token_cache, force_refresh=force_refresh)
        payload = _spotify_request_json(
            next_url,
            headers={"Authorization": f"Bearer {access_token}"},
        )
        items = payload.get("items", [])
        if not isinstance(items, list):
            items = []
        for item in items:
            parsed_track = _parse_track_item(item)
            track_entries.append(parsed_track)
        raw_next = payload.get("next")
        next_url = raw_next if isinstance(raw_next, str) and raw_next else ""
    return track_entries


def _fetch_playlist_tracks(
    client_id: str,
    token_cache: dict[str, object],
    playlist_id: str,
    force_refresh: bool = False,
) -> list[TrackInfo]:
    try:
        return _fetch_playlist_tracks_page(
            client_id,
            token_cache,
            playlist_id,
            endpoint_url_template=SPOTIFY_PLAYLIST_ITEMS_URL_TEMPLATE,
            fields=SPOTIFY_PLAYLIST_ITEMS_FIELDS,
            force_refresh=force_refresh,
        )
    except SpotifyApiError as exc:
        if exc.status_code != 403:
            raise
        return _fetch_playlist_tracks_page(
            client_id,
            token_cache,
            playlist_id,
            endpoint_url_template=SPOTIFY_PLAYLIST_TRACKS_URL_TEMPLATE,
            fields=SPOTIFY_PLAYLIST_TRACKS_FIELDS,
            force_refresh=force_refresh,
        )


def _fetch_user_playlists(
    client_id: str,
    token_cache: dict[str, object],
    status_callback: Callable[[str], None] | None = None,
) -> list[PlaylistInfo]:
    playlists: list[PlaylistInfo] = []
    query = urllib.parse.urlencode(
        {
            "limit": 50,
            "fields": SPOTIFY_PLAYLIST_FIELDS,
        }
    )
    next_url = f"{SPOTIFY_PLAYLISTS_URL}?{query}"
    page_count = 0

    while next_url:
        page_count += 1
        if status_callback is not None:
            status_callback(f"Fetching playlists from Spotify (page {page_count})...")
        access_token = _get_access_token(client_id, token_cache)
        payload = _spotify_request_json(
            next_url,
            headers={"Authorization": f"Bearer {access_token}"},
        )

        items = payload.get("items", [])
        if not isinstance(items, list):
            items = []
        for item in items:
            playlist_info = _parse_playlist_item(item)
            if playlist_info is not None:
                playlists.append(playlist_info)

        raw_next = payload.get("next")
        next_url = raw_next if isinstance(raw_next, str) and raw_next else ""

    return playlists


def _hydrate_playlist_tracks(
    client_id: str,
    token_cache: dict[str, object],
    current_user_id: str,
    playlists: list[PlaylistInfo],
    status_callback: Callable[[str], None] | None = None,
) -> list[PlaylistInfo]:
    hydrated: list[PlaylistInfo] = []
    total = len(playlists)
    for index, playlist in enumerate(playlists, start=1):
        if current_user_id and playlist.owner_id and playlist.owner_id != current_user_id:
            if status_callback is not None:
                status_callback(f"Skipping followed playlist: {playlist.name}")
            continue
        if status_callback is not None:
            status_callback(f"Fetching tracks for playlist {index}/{total}: {playlist.name}")
        try:
            tracks = _fetch_playlist_tracks(client_id, token_cache, playlist.id)
            updated_total = len(tracks)
        except SpotifyApiError as exc:
            if exc.status_code != 403:
                raise
            if status_callback is not None:
                status_callback(f"Skipping playlist due to Spotify permissions (403): {playlist.name}")
            continue
        hydrated.append(
            PlaylistInfo(
                id=playlist.id,
                name=playlist.name,
                track_total=updated_total,
                snapshot_id=playlist.snapshot_id,
                owner_id=playlist.owner_id,
                tracks=tracks,
                tracks_loaded=bool(tracks),
            )
        )
    return hydrated


def _sync_playlists(
    session: SpotifySession,
    current_user_id: str,
    status_callback: Callable[[str], None] | None = None,
) -> list[PlaylistInfo]:
    playlists = _fetch_user_playlists(session.client_id, session.token_cache, status_callback=status_callback)
    return _hydrate_playlist_tracks(
        session.client_id,
        session.token_cache,
        current_user_id,
        playlists,
        status_callback,
    )


def connect_and_get_session_playlists(
    status_callback: Callable[[str], None] | None = None,
) -> tuple[SpotifySession, list[PlaylistInfo]]:
    client_id = os.getenv("SPOTIFY_CLIENT_ID", "").strip()
    redirect_uri = os.getenv("SPOTIFY_REDIRECT_URI", "http://127.0.0.1:8888/callback").strip()
    if not client_id:
        raise RuntimeError("Set SPOTIFY_CLIENT_ID before connecting to Spotify.")
    _validate_redirect_uri(redirect_uri)

    code_verifier, code_challenge = _build_pkce_pair()
    state = secrets.token_urlsafe(32)
    auth_query = urllib.parse.urlencode(
        {
            "client_id": client_id,
            "response_type": "code",
            "redirect_uri": redirect_uri,
            "scope": SPOTIFY_SCOPE,
            "state": state,
            "code_challenge_method": "S256",
            "code_challenge": code_challenge,
        }
    )
    auth_url = f"{SPOTIFY_AUTH_URL}?{auth_query}"

    if status_callback is not None:
        status_callback("Opening Spotify authorization in browser...")
    _open_authorization_page(auth_url)
    if status_callback is not None:
        status_callback("Waiting for Spotify login approval in browser...")
    code = _wait_for_auth_code(redirect_uri, state)
    if status_callback is not None:
        status_callback("Authorization approved. Fetching playlists from Spotify...")
    tokens = _exchange_code_for_token(client_id, redirect_uri, code, code_verifier)
    session = SpotifySession(client_id=client_id, token_cache=tokens)
    current_user_id = _fetch_current_user_id(session.client_id, session.token_cache)
    playlists = _sync_playlists(session, current_user_id, status_callback=status_callback)
    return session, playlists


def _clamp_index(index: int, total: int) -> int:
    if total <= 0:
        return 0
    return min(max(0, index), total - 1)


def _find_playlist_by_id(playlists: list[PlaylistInfo], playlist_id: str | None) -> PlaylistInfo | None:
    if not playlist_id:
        return None
    for playlist in playlists:
        if playlist.id == playlist_id:
            return playlist
    return None


def _find_playlist_index_by_id(playlists: list[PlaylistInfo], playlist_id: str | None) -> int | None:
    if not playlist_id:
        return None
    for idx, playlist in enumerate(playlists):
        if playlist.id == playlist_id:
            return idx
    return None


def _find_track_index_by_uri(tracks: list[TrackInfo], track_uri: str) -> int | None:
    if not track_uri:
        return None
    for idx, track in enumerate(tracks):
        if track.uri == track_uri:
            return idx
    return None


def _create_playlist(
    client_id: str,
    token_cache: dict[str, object],
    user_id: str,
    playlist_name: str,
) -> PlaylistInfo:
    access_token = _get_access_token(client_id, token_cache)
    quoted_user_id = urllib.parse.quote(user_id, safe="")
    payload = _spotify_request_json(
        SPOTIFY_USER_PLAYLISTS_URL_TEMPLATE.format(user_id=quoted_user_id),
        method="POST",
        headers={"Authorization": f"Bearer {access_token}"},
        json_body={"name": playlist_name, "public": False},
    )
    playlist_info = _parse_playlist_item(payload)
    if playlist_info is None:
        raise RuntimeError(
            "Failed to parse playlist details from Spotify's response after creation. "
            "The API may have returned unexpected data."
        )
    return playlist_info


def _add_track_to_playlist(
    client_id: str,
    token_cache: dict[str, object],
    playlist_id: str,
    track_uri: str,
) -> None:
    access_token = _get_access_token(client_id, token_cache)
    quoted_playlist_id = urllib.parse.quote(playlist_id, safe="")
    _spotify_request_json(
        SPOTIFY_PLAYLIST_TRACKS_URL_TEMPLATE.format(playlist_id=quoted_playlist_id),
        method="POST",
        headers={"Authorization": f"Bearer {access_token}"},
        json_body={"uris": [track_uri]},
    )


def _remove_track_from_playlist(
    client_id: str,
    token_cache: dict[str, object],
    playlist_id: str,
    track_uri: str,
    track_position: int,
) -> None:
    access_token = _get_access_token(client_id, token_cache)
    quoted_playlist_id = urllib.parse.quote(playlist_id, safe="")
    _spotify_request_json(
        SPOTIFY_PLAYLIST_TRACKS_URL_TEMPLATE.format(playlist_id=quoted_playlist_id),
        method="DELETE",
        headers={"Authorization": f"Bearer {access_token}"},
        json_body={"tracks": [{"uri": track_uri, "positions": [track_position]}]},
    )


def _add_line(
    stdscr: curses.window,
    row: int,
    col: int,
    text: str,
    width: int,
    attr: int = curses.A_NORMAL,
) -> None:
    if width <= 0:
        return
    rows, _cols = stdscr.getmaxyx()
    if row < 0 or row >= rows:
        return
    stdscr.addnstr(row, col, text, width, attr)


def _wrap_text_lines(text: str, width: int) -> list[str]:
    if width <= 0:
        return []
    lines: list[str] = []
    for raw_line in text.splitlines() or [""]:
        wrapped = textwrap.wrap(
            raw_line,
            width=width,
            break_long_words=True,
            break_on_hyphens=False,
            replace_whitespace=False,
            drop_whitespace=False,
        )
        lines.extend(wrapped or [""])
    return lines


def _add_wrapped_text(
    stdscr: curses.window,
    row: int,
    col: int,
    text: str,
    width: int,
    attr: int = curses.A_NORMAL,
) -> int:
    rows, _cols = stdscr.getmaxyx()
    if width <= 0 or row >= rows:
        return 0
    lines = _wrap_text_lines(text, width)
    drawn = 0
    for line in lines:
        draw_row = row + drawn
        if draw_row >= rows:
            break
        _add_line(stdscr, draw_row, col, line, width, attr)
        drawn += 1
    return drawn


def run(stdscr: curses.window) -> None:
    curses.curs_set(0)
    stdscr.timeout(UI_POLL_INTERVAL_MS)
    stdscr.keypad(True)

    connection_lock = threading.Lock()
    state = UiState()
    stop_sync_event = threading.Event()
    sync_interval_seconds = max(
        10,
        _safe_int(
            os.getenv("SPOTIFY_SYNC_INTERVAL_SECONDS", str(DEFAULT_SPOTIFY_SYNC_INTERVAL_SECONDS)),
            DEFAULT_SPOTIFY_SYNC_INTERVAL_SECONDS,
        ),
    )

    def connect_worker() -> None:
        def update_status(message: str) -> None:
            with connection_lock:
                state.status_message = message

        try:
            established_session, fetched_playlists = connect_and_get_session_playlists(
                status_callback=update_status
            )
            with connection_lock:
                state.session = established_session
                state.playlists = fetched_playlists
                state.selected_index = 0
                state.opened_playlist_id = None
                state.focused_panel = PANEL_PLAYLISTS
                state.tracks_selected_index = 0
                state.target_selected_index = 0
                state.creating_playlist = False
                state.new_playlist_name = ""
                state.error_message = ""
                state.connection_status = "connected"
                if state.playlists:
                    state.status_message = (
                        f"Connected. Synced {len(state.playlists)} playlist(s). Use up/down and →."
                    )
                else:
                    state.status_message = "Connected. No playlists found for this user."
        except (
            RuntimeError,
            TimeoutError,
            urllib.error.URLError,
            json.JSONDecodeError,
            UnicodeDecodeError,
        ) as exc:
            with connection_lock:
                state.session = None
                state.connection_status = "disconnected"
                state.error_message = f"Connection failed: {exc}"
                state.status_message = "Press c to retry Spotify connection."

    def sync_worker() -> None:
        def update_sync_status(message: str) -> None:
            with connection_lock:
                if state.connection_status == "connected":
                    state.status_message = message

        while not stop_sync_event.wait(timeout=sync_interval_seconds):
            try:
                with connection_lock:
                    active_session = state.session
                    current_user_id = ""
                    is_connected = (
                        state.connection_status == "connected" and active_session is not None
                    )
                    if is_connected:
                        state.status_message = "Connected. Syncing Spotify updates..."
                if not is_connected:
                    continue
                try:
                    current_user_id = _fetch_current_user_id(
                        active_session.client_id,
                        active_session.token_cache,
                    )
                except Exception as exc:
                    with connection_lock:
                        state.session = None
                        state.connection_status = "disconnected"
                        state.error_message = f"Connection lost: {exc}"
                        state.status_message = "Connection lost. Press c to reconnect."
                    continue
                refreshed_playlists = _sync_playlists(
                    active_session,
                    current_user_id,
                    status_callback=update_sync_status,
                )
                with connection_lock:
                    state.playlists = refreshed_playlists
                    state.selected_index = _clamp_index(state.selected_index, len(state.playlists))
                    opened_playlist = _find_playlist_by_id(state.playlists, state.opened_playlist_id)
                    if opened_playlist is None:
                        state.opened_playlist_id = None
                        state.focused_panel = PANEL_PLAYLISTS
                        state.tracks_selected_index = 0
                    else:
                        state.tracks_selected_index = _clamp_index(
                            state.tracks_selected_index, len(opened_playlist.tracks)
                        )
                    option_count = len(state.playlists) + 1
                    state.target_selected_index = _clamp_index(state.target_selected_index, option_count)
                    if state.creating_playlist and state.target_selected_index != len(state.playlists):
                        state.creating_playlist = False
                        state.new_playlist_name = ""
                    state.error_message = ""
                    state.status_message = f"Connected. Last synced at {time.strftime('%H:%M:%S')}."
            except Exception as exc:
                with connection_lock:
                    state.session = None
                    state.connection_status = "disconnected"
                    state.error_message = f"Connection lost: {exc}"
                    state.status_message = "Connection lost. Press c to reconnect."

    def load_playlist_tracks_worker(playlist_id: str) -> None:
        with connection_lock:
            active_session = state.session
            if active_session is None or state.connection_status != "connected":
                return
        try:
            fetched_tracks = _fetch_playlist_tracks(
                active_session.client_id,
                active_session.token_cache,
                playlist_id,
            )
            with connection_lock:
                found = False
                for idx, playlist in enumerate(state.playlists):
                    if playlist.id != playlist_id:
                        continue
                    found = True
                    state.playlists[idx] = PlaylistInfo(
                        id=playlist.id,
                        name=playlist.name,
                        track_total=len(fetched_tracks),
                        snapshot_id=playlist.snapshot_id,
                        owner_id=playlist.owner_id,
                        tracks=fetched_tracks,
                        tracks_loaded=True,
                    )
                    break
                state.error_message = ""
                state.status_message = f"Loaded {len(fetched_tracks)} track(s) from selected playlist."
        except (
            RuntimeError,
            TimeoutError,
            urllib.error.URLError,
            json.JSONDecodeError,
            UnicodeDecodeError,
            SpotifyApiError,
        ) as exc:
            with connection_lock:
                if isinstance(exc, SpotifyApiError) and exc.status_code == 403:
                    state.playlists = [playlist for playlist in state.playlists if playlist.id != playlist_id]
                    state.selected_index = _clamp_index(state.selected_index, len(state.playlists))
                    if state.opened_playlist_id == playlist_id:
                        state.opened_playlist_id = None
                        state.focused_panel = PANEL_PLAYLISTS
                        state.tracks_selected_index = 0
                        state.target_selected_index = 0
                        state.creating_playlist = False
                        state.new_playlist_name = ""
                    state.error_message = ""
                    state.status_message = "Hidden playlist that Spotify does not allow this app to read."
                else:
                    state.error_message = f"Unable to load selected playlist tracks: {exc}"

    def move_track_worker(
        source_playlist_id: str,
        source_track_uri: str,
        source_track_position: int,
        destination_playlist_id: str | None,
        new_playlist_name: str | None,
        selected_playlist_id: str | None,
        opened_playlist_id: str | None,
        previous_tracks_selected_index: int,
        restore_target_playlist_id: str | None,
    ) -> None:
        with connection_lock:
            active_session = state.session
            is_connected = state.connection_status == "connected" and active_session is not None
        if not is_connected:
            with connection_lock:
                state.error_message = "Not connected. Press c to connect before moving songs."
            return
        try:
            resolved_destination_playlist_id = destination_playlist_id
            created_playlist_name = ""
            current_user_id = ""
            if resolved_destination_playlist_id is None:
                current_user_id = _fetch_current_user_id(active_session.client_id, active_session.token_cache)
                created_playlist = _create_playlist(
                    active_session.client_id,
                    active_session.token_cache,
                    current_user_id,
                    str(new_playlist_name),
                )
                resolved_destination_playlist_id = created_playlist.id
                created_playlist_name = created_playlist.name

            if not resolved_destination_playlist_id:
                raise RuntimeError(
                    "Could not determine destination playlist. Please try selecting a playlist again."
                )

            _add_track_to_playlist(
                active_session.client_id,
                active_session.token_cache,
                resolved_destination_playlist_id,
                source_track_uri,
            )
            _remove_track_from_playlist(
                active_session.client_id,
                active_session.token_cache,
                source_playlist_id,
                source_track_uri,
                source_track_position,
            )

            if not current_user_id:
                current_user_id = _fetch_current_user_id(
                    active_session.client_id, active_session.token_cache
                )
            refreshed_playlists = _sync_playlists(active_session, current_user_id)

            with connection_lock:
                state.playlists = refreshed_playlists

                restored_left_index = _find_playlist_index_by_id(state.playlists, selected_playlist_id)
                if restored_left_index is None:
                    state.selected_index = _clamp_index(state.selected_index, len(state.playlists))
                else:
                    state.selected_index = restored_left_index

                restored_opened = _find_playlist_by_id(state.playlists, opened_playlist_id)
                if restored_opened is None:
                    state.opened_playlist_id = None
                    state.tracks_selected_index = 0
                    state.focused_panel = PANEL_PLAYLISTS
                else:
                    state.opened_playlist_id = restored_opened.id
                    restored_track_index = _find_track_index_by_uri(
                        restored_opened.tracks, source_track_uri
                    )
                    if restored_track_index is None:
                        state.tracks_selected_index = _clamp_index(
                            previous_tracks_selected_index, len(restored_opened.tracks)
                        )
                    else:
                        state.tracks_selected_index = restored_track_index

                target_playlist_to_restore = restore_target_playlist_id or resolved_destination_playlist_id
                restored_target_index = _find_playlist_index_by_id(
                    state.playlists, target_playlist_to_restore
                )
                option_count = len(state.playlists) + 1
                if restored_target_index is None:
                    state.target_selected_index = _clamp_index(state.target_selected_index, option_count)
                else:
                    state.target_selected_index = restored_target_index
                state.creating_playlist = False
                state.new_playlist_name = ""

                if created_playlist_name:
                    state.status_message = (
                        f"Created playlist '{created_playlist_name}' and moved selected song."
                    )
                else:
                    state.status_message = "Moved selected song."
                state.error_message = ""
        except (
            RuntimeError,
            TimeoutError,
            urllib.error.URLError,
            json.JSONDecodeError,
            UnicodeDecodeError,
            SpotifyApiError,
        ) as exc:
            with connection_lock:
                state.error_message = f"Could not move selected song: {exc}"

    threading.Thread(target=sync_worker, daemon=True).start()

    while True:
        with connection_lock:
            status_snapshot = state.status_message
            error_snapshot = state.error_message
            playlists_snapshot = list(state.playlists)
            selected_snapshot = state.selected_index
            opened_playlist_snapshot = state.opened_playlist_id
            focused_panel_snapshot = state.focused_panel
            tracks_selected_snapshot = state.tracks_selected_index
            target_selected_snapshot = state.target_selected_index
            creating_playlist_snapshot = state.creating_playlist
            new_playlist_name_snapshot = state.new_playlist_name

        stdscr.erase()
        rows, cols = stdscr.getmaxyx()

        title = "Spotify Playlist Viewer TUI"
        width = max(1, cols - 1)
        left_panel_width = (
            width if cols < MIN_COLS_FOR_SPLIT_PANE else max(MIN_LEFT_PANEL_WIDTH, (width // 2) - 1)
        )
        right_panel_col = left_panel_width + 2
        right_panel_width = max(0, width - right_panel_col)
        songs_panel_col = right_panel_col
        songs_panel_width = right_panel_width
        targets_panel_col = right_panel_col
        targets_panel_width = 0
        if right_panel_width >= (MIN_LEFT_PANEL_WIDTH * 2) + 1:
            songs_panel_width = max(MIN_LEFT_PANEL_WIDTH, (right_panel_width // 2) - 1)
            targets_panel_col = songs_panel_col + songs_panel_width + 1
            targets_panel_width = max(0, right_panel_width - songs_panel_width - 1)

        content_row = 0
        content_row += _add_wrapped_text(stdscr, content_row, 0, title, width)
        content_row += _add_wrapped_text(stdscr, content_row, 0, UI_HELP_TEXT, width)
        if content_row < rows:
            stdscr.hline(content_row, 0, "-", width)
        content_row += 1
        content_row += _add_wrapped_text(stdscr, content_row, 0, status_snapshot, width)
        if error_snapshot:
            content_row += _add_wrapped_text(stdscr, content_row, 0, error_snapshot, width)

        list_header_row = content_row
        playlist_header_lines = _add_wrapped_text(stdscr, list_header_row, 0, "Playlists:", left_panel_width)
        left_list_start_row = list_header_row + max(1, playlist_header_lines)

        if not playlists_snapshot:
            _add_wrapped_text(stdscr, left_list_start_row, 0, "No playlists loaded yet.", left_panel_width)
        else:
            max_visible = max(1, rows - (left_list_start_row + 1))
            start_index = max(0, selected_snapshot - max_visible + 1)
            visible = playlists_snapshot[start_index : start_index + max_visible]
            left_draw_row = left_list_start_row
            for row_offset, playlist in enumerate(visible):
                if left_draw_row >= rows:
                    break
                playlist_index = start_index + row_offset
                line = f"{playlist_index + 1}. {playlist.name} ({playlist.track_total} tracks)"
                is_selected = playlist_index == selected_snapshot
                if is_selected and focused_panel_snapshot == PANEL_PLAYLISTS:
                    attr = curses.A_REVERSE
                elif is_selected:
                    attr = curses.A_BOLD
                else:
                    attr = curses.A_NORMAL
                left_draw_row += _add_wrapped_text(stdscr, left_draw_row, 0, line, left_panel_width, attr)

        if right_panel_width > 0:
            for row in range(list_header_row, rows):
                _add_line(stdscr, row, left_panel_width + 1, "│", 1)
            if targets_panel_width > 0:
                for row in range(list_header_row, rows):
                    _add_line(stdscr, row, targets_panel_col - 1, "│", 1)
            opened_playlist = _find_playlist_by_id(playlists_snapshot, opened_playlist_snapshot)
            songs_header_lines = _add_wrapped_text(
                stdscr, list_header_row, songs_panel_col, "Songs:", songs_panel_width
            )
            right_list_start_row = list_header_row + max(1, songs_header_lines)
            if opened_playlist is None:
                _add_line(
                    stdscr,
                    right_list_start_row,
                    songs_panel_col,
                    "Press → on a playlist to open songs.",
                    songs_panel_width,
                )
            else:
                header = f"{opened_playlist.name} ({len(opened_playlist.tracks)} tracks)"
                songs_row = right_list_start_row
                songs_row += _add_wrapped_text(stdscr, songs_row, songs_panel_col, header, songs_panel_width)
                if songs_row < rows:
                    if not opened_playlist.tracks:
                        _add_line(
                            stdscr,
                            songs_row,
                            songs_panel_col,
                            "No tracks found in this playlist.",
                            songs_panel_width,
                        )
                    else:
                        max_visible_tracks = max(1, rows - songs_row)
                        tracks_start_index = max(
                            0, tracks_selected_snapshot - max_visible_tracks + 1
                        )
                        visible_tracks = opened_playlist.tracks[
                            tracks_start_index : tracks_start_index + max_visible_tracks
                        ]
                        for row_offset, track_name in enumerate(visible_tracks):
                            draw_row = songs_row + row_offset
                            if draw_row >= rows:
                                break
                            track_index = tracks_start_index + row_offset
                            line = f"{track_index + 1}. {track_name.display}"
                            is_selected = track_index == tracks_selected_snapshot
                            if is_selected and focused_panel_snapshot == PANEL_TRACKS:
                                attr = curses.A_REVERSE
                            elif is_selected:
                                attr = curses.A_BOLD
                            else:
                                attr = curses.A_NORMAL
                            _add_line(stdscr, draw_row, songs_panel_col, line, songs_panel_width, attr)

            if targets_panel_width > 0:
                targets_header_lines = _add_wrapped_text(
                    stdscr, list_header_row, targets_panel_col, "Move to:", targets_panel_width
                )
                targets_list_start_row = list_header_row + max(1, targets_header_lines)
                if opened_playlist is None:
                    _add_line(
                        stdscr,
                        targets_list_start_row,
                        targets_panel_col,
                        "Open a song first with →.",
                        targets_panel_width,
                    )
                elif not opened_playlist.tracks:
                    _add_line(
                        stdscr,
                        targets_list_start_row,
                        targets_panel_col,
                        "No songs to move.",
                        targets_panel_width,
                    )
                else:
                    option_count = len(playlists_snapshot) + 1
                    selected_target = _clamp_index(target_selected_snapshot, option_count)
                    max_visible_targets = max(1, rows - targets_list_start_row)
                    targets_start_index = max(0, selected_target - max_visible_targets + 1)
                    draw_row = targets_list_start_row
                    for option_index in range(
                        targets_start_index,
                        min(option_count, targets_start_index + max_visible_targets),
                    ):
                        if draw_row >= rows:
                            break
                        if option_index < len(playlists_snapshot):
                            playlist = playlists_snapshot[option_index]
                            line = f"{option_index + 1}. {playlist.name} ({playlist.track_total} tracks)"
                        else:
                            if creating_playlist_snapshot and option_index == selected_target:
                                line = (
                                    f"New playlist: {new_playlist_name_snapshot}"
                                    if new_playlist_name_snapshot
                                    else "New playlist: "
                                )
                            else:
                                line = CREATE_PLAYLIST_OPTION_LABEL
                        is_selected = option_index == selected_target
                        if is_selected and focused_panel_snapshot == PANEL_TARGETS:
                            attr = curses.A_REVERSE
                        elif is_selected:
                            attr = curses.A_BOLD
                        else:
                            attr = curses.A_NORMAL
                        _add_line(stdscr, draw_row, targets_panel_col, line, targets_panel_width, attr)
                        draw_row += 1

        stdscr.refresh()

        key = stdscr.getch()
        if key == -1:
            continue
        if key in (ord("q"), ord("Q")):
            stop_sync_event.set()
            break
        if key in (ord("c"), ord("C")):
            should_start_connection = False
            with connection_lock:
                if state.connection_status == "connecting":
                    state.status_message = "Connection already in progress..."
                elif state.connection_status == "connected":
                    state.status_message = "Already connected. Waiting for automatic sync updates."
                else:
                    state.status_message = "Connecting to Spotify..."
                    state.error_message = ""
                    state.connection_status = "connecting"
                    should_start_connection = True
            if should_start_connection:
                threading.Thread(target=connect_worker, daemon=True).start()
            continue
        if key in (curses.KEY_ENTER, 10, 13):
            move_args: tuple[
                str,
                str,
                int,
                str | None,
                str | None,
                str | None,
                str | None,
                int,
                str | None,
            ] | None = None
            with connection_lock:
                if state.focused_panel == PANEL_TARGETS:
                    opened_playlist = _find_playlist_by_id(state.playlists, state.opened_playlist_id)
                    if opened_playlist is None or not opened_playlist.tracks:
                        state.error_message = "Select a song first before choosing move target."
                    else:
                        track_index = _clamp_index(state.tracks_selected_index, len(opened_playlist.tracks))
                        track_to_move = opened_playlist.tracks[track_index]
                        if not track_to_move.uri:
                            state.error_message = (
                                "Selected song cannot be moved because track information is incomplete. "
                                "Try reconnecting to Spotify."
                            )
                        else:
                            option_count = len(state.playlists) + 1
                            state.target_selected_index = _clamp_index(
                                state.target_selected_index, option_count
                            )
                            create_option_index = len(state.playlists)
                            destination_playlist_id: str | None = None
                            new_playlist_name: str | None = None
                            restore_target_playlist_id: str | None = None
                            if state.target_selected_index == create_option_index:
                                if not state.creating_playlist:
                                    state.creating_playlist = True
                                    state.new_playlist_name = ""
                                    state.error_message = ""
                                    state.status_message = (
                                        "Type new playlist name and press Enter to create it and move selected song."
                                    )
                                    continue
                                requested_name = state.new_playlist_name.strip()
                                if not requested_name:
                                    state.error_message = (
                                        "Playlist name cannot be empty. Please enter a name to create the playlist."
                                    )
                                    continue
                                new_playlist_name = requested_name
                            else:
                                target_playlist = state.playlists[state.target_selected_index]
                                if target_playlist.id == opened_playlist.id:
                                    state.error_message = (
                                        "Cannot move song to the same playlist it's already in."
                                    )
                                    continue
                                destination_playlist_id = target_playlist.id
                                restore_target_playlist_id = target_playlist.id
                                state.creating_playlist = False
                                state.new_playlist_name = ""

                            selected_playlist_id = None
                            if state.playlists:
                                selected_playlist_id = state.playlists[state.selected_index].id
                            move_args = (
                                opened_playlist.id,
                                track_to_move.uri,
                                track_index,
                                destination_playlist_id,
                                new_playlist_name,
                                selected_playlist_id,
                                state.opened_playlist_id,
                                state.tracks_selected_index,
                                restore_target_playlist_id,
                            )
                            state.error_message = ""
                            state.status_message = "Moving selected song..."
            if move_args is not None:
                threading.Thread(target=move_track_worker, args=move_args, daemon=True).start()
            continue
        if key == 27:
            with connection_lock:
                if state.focused_panel == PANEL_TARGETS and state.creating_playlist:
                    state.creating_playlist = False
                    state.new_playlist_name = ""
                    state.status_message = "Canceled new playlist creation."
                    state.error_message = ""
                    continue
        if key in (curses.KEY_BACKSPACE, 127, 8):
            with connection_lock:
                if state.focused_panel == PANEL_TARGETS and state.creating_playlist:
                    state.new_playlist_name = state.new_playlist_name[:-1]
                    continue
        if 32 <= key <= 126:
            with connection_lock:
                if state.focused_panel == PANEL_TARGETS and state.creating_playlist:
                    state.new_playlist_name += chr(key)
                    continue
        if key == curses.KEY_UP:
            with connection_lock:
                if state.focused_panel == PANEL_PLAYLISTS and state.playlists:
                    state.selected_index = _clamp_index(state.selected_index - 1, len(state.playlists))
                elif state.focused_panel == PANEL_TRACKS:
                    opened_playlist = _find_playlist_by_id(state.playlists, state.opened_playlist_id)
                    if opened_playlist is not None:
                        state.tracks_selected_index = _clamp_index(
                            state.tracks_selected_index - 1, len(opened_playlist.tracks)
                        )
                elif state.focused_panel == PANEL_TARGETS:
                    option_count = len(state.playlists) + 1
                    state.target_selected_index = _clamp_index(
                        state.target_selected_index - 1, option_count
                    )
                    if state.creating_playlist and state.target_selected_index != len(state.playlists):
                        state.creating_playlist = False
                        state.new_playlist_name = ""
            continue
        if key == curses.KEY_DOWN:
            with connection_lock:
                if state.focused_panel == PANEL_PLAYLISTS and state.playlists:
                    state.selected_index = _clamp_index(state.selected_index + 1, len(state.playlists))
                elif state.focused_panel == PANEL_TRACKS:
                    opened_playlist = _find_playlist_by_id(state.playlists, state.opened_playlist_id)
                    if opened_playlist is not None:
                        state.tracks_selected_index = _clamp_index(
                            state.tracks_selected_index + 1, len(opened_playlist.tracks)
                        )
                elif state.focused_panel == PANEL_TARGETS:
                    option_count = len(state.playlists) + 1
                    state.target_selected_index = _clamp_index(
                        state.target_selected_index + 1, option_count
                    )
                    if state.creating_playlist and state.target_selected_index != len(state.playlists):
                        state.creating_playlist = False
                        state.new_playlist_name = ""
            continue
        if key == curses.KEY_RIGHT:
            playlist_to_refresh: str | None = None
            with connection_lock:
                if state.focused_panel == PANEL_PLAYLISTS and state.playlists:
                    selected_playlist = state.playlists[state.selected_index]
                    if state.opened_playlist_id != selected_playlist.id:
                        state.tracks_selected_index = 0
                    state.opened_playlist_id = selected_playlist.id
                    state.focused_panel = PANEL_TRACKS
                    state.tracks_selected_index = _clamp_index(
                        state.tracks_selected_index, len(selected_playlist.tracks)
                    )
                    if (
                        state.connection_status == "connected"
                        and state.session is not None
                        and not selected_playlist.tracks_loaded
                    ):
                        playlist_to_refresh = selected_playlist.id
                        state.status_message = (
                            f"Loading tracks for playlist: {selected_playlist.name}"
                        )
                elif state.focused_panel == PANEL_TRACKS:
                    opened_playlist = _find_playlist_by_id(state.playlists, state.opened_playlist_id)
                    if opened_playlist is None or not opened_playlist.tracks:
                        state.status_message = "Open a playlist with songs before choosing a destination."
                    else:
                        state.focused_panel = PANEL_TARGETS
                        option_count = len(state.playlists) + 1
                        state.target_selected_index = _clamp_index(
                            state.target_selected_index, option_count
                        )
            if playlist_to_refresh is not None:
                threading.Thread(
                    target=load_playlist_tracks_worker, args=(playlist_to_refresh,), daemon=True
                ).start()
            continue
        if key == curses.KEY_LEFT:
            with connection_lock:
                if state.focused_panel == PANEL_TARGETS:
                    state.focused_panel = PANEL_TRACKS
                    state.creating_playlist = False
                    state.new_playlist_name = ""
                elif state.focused_panel == PANEL_TRACKS:
                    state.focused_panel = PANEL_PLAYLISTS
            continue


def main() -> None:
    curses.wrapper(run)


if __name__ == "__main__":
    main()

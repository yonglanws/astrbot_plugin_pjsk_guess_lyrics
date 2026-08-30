"""歌曲题库数据服务（学习 PJSK Wordle 的 master 自动同步机制）。

数据来源与职责：
- 日服题库: https://github.com/Team-Haruki/haruki-sekai-master   (master/musics.json)
- 国服题库: https://github.com/Team-Haruki/haruki-sekai-sc-master (master/musics.json)
- 歌曲中文译名: https://translation.exmeaning.com/files/translation/music.json （Moesekai 同款翻译源）
- 歌曲别名:     https://moe.exmeaning.com/data/music_alias/music_aliases.json （Moesekai 同款别名源）

拉取策略：GitHub 托管的文件一律优先 GitHub Contents API；musics.json 超过 1MB 时
自动改用同一 API 的 raw 媒体类型（支持 1~100MB 文件）；GitHub API 不可用时回退 jsDelivr。
非 GitHub 托管的翻译/别名直接从其官方源拉取。

为节省流量：每次周期检查先拉取很小的 current_version.json，若 dataVersion 没有变化
（新歌曲只会随游戏数据版本更新上架），则跳过 musics.json 重新下载；
翻译/别名数据属于社区日常维护，每次周期检查都按间隔刷新。

所有文件持久化在 plugin_data 目录，每 24 小时自动更新一次；
基于原始数据构建派生题库 derived.json（含中文名/别名），游戏运行时只读派生题库。
"""

import asyncio
import base64
import json
import time
from datetime import datetime
from pathlib import Path

import aiohttp

try:  # 在 AstrBot 内使用其 logger，脱离 AstrBot（单测）时退回标准 logging
    from astrbot.api import logger
except ImportError:  # pragma: no cover
    import logging

    logger = logging.getLogger("astrbot_plugin_pjsk_guess_lyrics")

SERVER_JP = "jp"
SERVER_SC = "sc"
SERVER_LABELS = {SERVER_JP: "日服", SERVER_SC: "国服"}

_SERVER_FILES = {
    SERVER_JP: [
        ("master/musics.json", "musics.json"),
        ("versions/current_version.json", "current_version.json"),
    ],
    SERVER_SC: [
        ("master/musics.json", "musics.json"),
        ("versions/current_version.json", "current_version.json"),
    ],
}

_GITHUB_REPOS = {
    SERVER_JP: "Team-Haruki/haruki-sekai-master",
    SERVER_SC: "Team-Haruki/haruki-sekai-sc-master",
}
_GITHUB_BRANCH = "main"

# 派生题库构建规则版本：规则变更时 +1，启动时用本地原始文件离线重建
DERIVED_RULE = 1

_EXTRA_SOURCES = {
    "translation": "https://translation.exmeaning.com/files/translation/music.json",
    "alias": "https://moe.exmeaning.com/data/music_alias/music_aliases.json",
}

_JSDELIVR_TPL = "https://cdn.jsdelivr.net/gh/{repo}@{branch}/{path}"


class MasterDataService:
    """歌曲题库下载、缓存、派生与查询。"""

    def __init__(
        self,
        data_dir: Path,
        update_interval_hours: int = 24,
        request_timeout: int = 90,
    ):
        self.data_dir = Path(data_dir)
        self.music_dir = self.data_dir / "musicdata"
        self.music_dir.mkdir(parents=True, exist_ok=True)
        self.update_interval_hours = max(1, int(update_interval_hours))
        self.request_timeout = request_timeout

        self.meta_path = self.music_dir / "meta.json"
        self.meta: dict = {}

        self.songs: dict[str, list[dict]] = {SERVER_JP: [], SERVER_SC: []}
        # 翻译/别名属于两服共用的补充数据
        self.cn_by_title: dict[str, str] = {}
        self.alias_by_id: dict[int, list[str]] = {}
        self.alias_by_title: dict[str, list[str]] = {}

        self._fetch_lock = asyncio.Lock()
        self._session: aiohttp.ClientSession | None = None
        self._update_task: asyncio.Task | None = None
        # 题库更新后的回调（由插件主流程注入，用于刷新匹配数据）
        self.on_songs_updated = None

    # ---------- 路径辅助 ----------

    def _server_dir(self, server: str) -> Path:
        return self.music_dir / server

    @property
    def derived_path(self) -> dict[str, Path]:
        return {s: self._server_dir(s) / "derived.json" for s in (SERVER_JP, SERVER_SC)}

    # ---------- 生命周期 ----------

    async def start(self):
        """启动：加载本地缓存，缺失则立即拉取，并启动 24h 周期更新任务。"""
        self.music_dir.mkdir(parents=True, exist_ok=True)
        self._load_meta()
        self._load_extras_memory()

        loaded_any = False
        for server in (SERVER_JP, SERVER_SC):
            if not self._load_derived(server):
                continue
            loaded_any = True
            # 派生规则升级时，用本地缓存的原始文件离线重建
            info = self.meta.setdefault("servers", {}).get(server, {})
            if info.get("derived_rule") != DERIVED_RULE:
                if not self._rebuild_from_local(server):
                    # 本地原始文件不全，清除时间戳以便周期任务重新拉取
                    info.pop("updated_at", None)
                    self._save_meta()
        if loaded_any:
            logger.info("[PJSK歌词猜曲] 本地题库加载完成。")
            self._notify_updated()

        self._update_task = asyncio.create_task(self._update_loop())

    async def terminate(self):
        if self._update_task:
            self._update_task.cancel()
            try:
                await self._update_task
            except (asyncio.CancelledError, Exception):
                pass
            self._update_task = None
        if self._session and not self._session.closed:
            await self._session.close()
        self._session = None

    # ---------- 对外查询接口 ----------

    def get_songs(self, server: str) -> list[dict]:
        return self.songs.get(server, [])

    def get_song_count(self, server: str) -> int:
        return len(self.songs.get(server, []))

    def get_version(self, server: str) -> str:
        """题库版本号：优先游戏数据版本 dataVersion（如 6.8.0.12），否则更新日期。"""
        info = self.meta.get("servers", {}).get(server, {})
        version = info.get("version")
        if version:
            return str(version)
        updated = info.get("updated_at")
        if updated:
            return datetime.fromtimestamp(updated).strftime("%Y%m%d")
        return "unknown"

    def is_ready(self, server: str) -> bool:
        return bool(self.songs.get(server))

    # ---------- 周期更新 ----------

    async def _update_loop(self):
        """每 30 分钟检查一次，超过更新间隔（默认 24h）的数据源自动重新拉取。"""
        try:
            await self.refresh_if_stale()
        except Exception as e:
            logger.error(f"[PJSK歌词猜曲] 首次题库检查失败: {e}", exc_info=True)
        while True:
            await asyncio.sleep(1800)
            try:
                await self.refresh_if_stale()
            except asyncio.CancelledError:
                raise
            except Exception as e:
                logger.error(f"[PJSK歌词猜曲] 周期题库更新失败: {e}", exc_info=True)

    async def refresh_if_stale(self, force: bool = False):
        """按 24h 间隔刷新所有数据源；force=True 时无视间隔与版本守卫强制刷新。"""
        async with self._fetch_lock:
            now = time.time()
            interval = self.update_interval_hours * 3600
            stale_servers = [
                server
                for server in (SERVER_JP, SERVER_SC)
                if force
                or not self.songs.get(server)
                or now - self.meta.get("servers", {}).get(server, {}).get("updated_at", 0)
                >= interval
            ]
            stale_extras = [
                key
                for key in _EXTRA_SOURCES
                if force
                or now - self.meta.get("extras", {}).get(key, {}).get("updated_at", 0) >= interval
            ]

            updated = False
            extras_updated = False
            # 先更新共用补充数据（别名/翻译），重建派生数据时才能带上它们
            if stale_extras:
                try:
                    extras_updated = await self._update_extras(stale_extras)
                    updated = updated or extras_updated
                except Exception as e:
                    logger.error(
                        f"[PJSK歌词猜曲] 补充数据（别名/翻译）更新失败: {e}",
                        exc_info=True,
                    )

            for server in stale_servers:
                try:
                    if await self._update_server(server, force=force):
                        updated = True
                except Exception as e:
                    logger.error(
                        f"[PJSK歌词猜曲] {SERVER_LABELS[server]}题库更新失败: {e}",
                        exc_info=True,
                    )

            if extras_updated:
                for server in (SERVER_JP, SERVER_SC):
                    if not self.songs.get(server):
                        continue
                    try:
                        if self._rebuild_from_local(server):
                            updated = True
                    except Exception as e:
                        logger.warning(
                            f"[PJSK歌词猜曲] {SERVER_LABELS[server]}补充数据重建失败: {e}",
                            exc_info=True,
                        )

            if updated:
                self._save_meta()
                self._notify_updated()

    def _notify_updated(self):
        if self.on_songs_updated:
            try:
                result = self.on_songs_updated()
                if asyncio.iscoroutine(result):
                    asyncio.get_running_loop().create_task(result)
            except RuntimeError:
                try:
                    result.close()
                except Exception:
                    pass
            except Exception as e:
                logger.warning(f"[PJSK歌词猜曲] 题库更新回调执行失败: {e}")

    # ---------- 单服务器题库更新 ----------

    async def _update_server(self, server: str, force: bool = False) -> bool:
        """更新单个服务器的歌曲题库，返回题库是否有变化。"""
        repo = _GITHUB_REPOS[server]

        # 先拉取很小的版本文件做版本守卫：dataVersion 未变则跳过大文件下载
        version_data, _ = await self._fetch_remote_json(
            repo, "versions/current_version.json", small=True
        )
        data_version = str((version_data or {}).get("dataVersion") or "").strip()

        info = self.meta.setdefault("servers", {}).setdefault(server, {})
        if (
            not force
            and data_version
            and info.get("data_version") == data_version
            and self.songs.get(server)
            and info.get("derived_rule") == DERIVED_RULE
        ):
            if info.get("updated_at", 0) < time.time() - 300:
                info["updated_at"] = time.time()
                self._save_meta()
            return False

        parsed: dict = {}
        for remote_path, local_name in _SERVER_FILES[server]:
            if local_name == "current_version.json" and version_data is not None:
                parsed[local_name] = version_data
                continue
            data, _ = await self._fetch_remote_json(repo, remote_path, small=False)
            if data is None:
                raise RuntimeError(f"拉取 {repo}/{remote_path} 失败（所有通道）")
            parsed[local_name] = data
            await asyncio.sleep(0.3)  # 轻微限速，尊重匿名 API 配额

        self._store_server(server, parsed, data_version, via="github")
        return True

    def _rebuild_from_local(self, server: str) -> bool:
        """用本地缓存的原始 JSON 离线重建派生题库（用于派生规则升级）。"""
        sdir = self._server_dir(server)
        parsed: dict = {}
        for _, local_name in _SERVER_FILES[server]:
            f = sdir / local_name
            if not f.exists():
                logger.warning(
                    f"[PJSK歌词猜曲] 本地缺少 {SERVER_LABELS[server]}/{local_name}，跳过离线重建"
                )
                return False
            try:
                parsed[local_name] = json.loads(f.read_text(encoding="utf-8"))
            except Exception as e:
                logger.warning(f"[PJSK歌词猜曲] 本地文件 {local_name} 解析失败: {e}")
                return False
        try:
            info = self.meta.get("servers", {}).get(server, {})
            self._store_server(
                server,
                parsed,
                str(info.get("data_version") or ""),
                via="local-rebuild",
            )
            return True
        except Exception as e:
            logger.warning(f"[PJSK歌词猜曲] {SERVER_LABELS[server]}离线重建失败: {e}")
            return False

    def _store_server(self, server: str, parsed: dict, data_version: str, via: str):
        """落盘原始文件并重建派生题库。"""
        sdir = self._server_dir(server)
        sdir.mkdir(parents=True, exist_ok=True)
        for name, data in parsed.items():
            (sdir / name).write_text(json.dumps(data, ensure_ascii=False), encoding="utf-8")

        songs = self._build_derived(parsed)
        if not songs:
            raise RuntimeError(f"{SERVER_LABELS[server]}题库解析结果为空")

        self.songs[server] = songs
        self.derived_path[server].write_text(
            json.dumps(songs, ensure_ascii=False), encoding="utf-8"
        )

        display_version = data_version or datetime.now().strftime("%Y%m%d")
        servers = self.meta.setdefault("servers", {})
        servers[server] = {
            "version": display_version,
            "data_version": data_version or None,
            "updated_at": time.time(),
            "via": via,
            "count": len(songs),
            "derived_rule": DERIVED_RULE,
        }
        self._save_meta()
        logger.info(
            f"[PJSK歌词猜曲] {SERVER_LABELS[server]}题库已更新: "
            f"{len(songs)} 首, 版本 {display_version} (via {via})"
        )

    # ---------- 补充数据（别名 / 翻译） ----------

    async def _update_extras(self, keys: list[str]) -> bool:
        """更新补充数据，返回至少一个数据源是否成功刷新。"""
        errors = []
        updated = False
        for key in keys:
            try:
                raw = await self._fetch_url(_EXTRA_SOURCES[key])
                self._store_extra(key, json.loads(raw.decode("utf-8")), update_meta=True)
                updated = True
            except asyncio.CancelledError:
                raise
            except Exception as e:
                errors.append(f"{key}: {e}")
                logger.warning(f"[PJSK歌词猜曲] 拉取 {key} 数据失败: {e}")
        if not updated:
            raise RuntimeError("全部补充数据拉取失败: " + "; ".join(errors))
        return updated

    def _store_extra(self, key: str, data, update_meta: bool = False):
        if key == "translation":
            # 结构: {"artist": {...}, "title": {日文原名: 中文译名}, "vocalCaption": {...}}
            self.cn_by_title = dict(data.get("title") or {})
            (self.music_dir / "translation_music.json").write_text(
                json.dumps(data, ensure_ascii=False), encoding="utf-8"
            )
        elif key == "alias":
            # 结构: {"generated_at": ..., "musics": [{"music_id": int, "title": str, "aliases": [...]}]}
            self.alias_by_id = {}
            self.alias_by_title = {}
            for entry in data.get("musics", []):
                mid = entry.get("music_id")
                aliases = [a for a in entry.get("aliases", []) if a]
                if not isinstance(mid, int):
                    continue
                self.alias_by_id[mid] = aliases
                title = entry.get("title")
                if title:
                    self.alias_by_title[title] = aliases
            (self.music_dir / "alias.json").write_text(
                json.dumps(data, ensure_ascii=False), encoding="utf-8"
            )

        if update_meta:
            extras = self.meta.setdefault("extras", {})
            extras[key] = {
                "updated_at": time.time(),
                "generated_at": data.get("generated_at") if isinstance(data, dict) else None,
            }
            self._save_meta()

    def _load_extras_memory(self):
        """启动时从本地缓存恢复别名/翻译数据（不刷新更新时间戳）。"""
        path_map = {
            "translation": self.music_dir / "translation_music.json",
            "alias": self.music_dir / "alias.json",
        }
        for key, path in path_map.items():
            if not path.exists():
                continue
            try:
                data = json.loads(path.read_text(encoding="utf-8"))
                self._store_extra(key, data, update_meta=False)
            except Exception as e:
                logger.warning(f"[PJSK歌词猜曲] 加载本地 {key} 数据失败: {e}")

    # ---------- 派生题库构建 ----------

    def _build_derived(self, parsed: dict) -> list[dict]:
        musics = parsed.get("musics.json", [])
        result: list[dict] = []
        for m in musics:
            mid = m.get("id")
            title = m.get("title")
            if mid is None or not title:
                continue
            aliases = list(self.alias_by_id.get(mid, []))
            if not aliases:
                aliases = list(self.alias_by_title.get(title, []))
            cn = self.cn_by_title.get(title) or title
            result.append({"id": mid, "title": title, "cn": cn, "aliases": aliases})
        result.sort(key=lambda x: x["id"])
        return result

    # ---------- 本地加载 ----------

    def _load_meta(self):
        if not self.meta_path.exists():
            self.meta = {}
            return
        try:
            self.meta = json.loads(self.meta_path.read_text(encoding="utf-8"))
        except Exception as e:
            logger.warning(f"[PJSK歌词猜曲] meta.json 解析失败，将重建: {e}")
            self.meta = {}

    def _save_meta(self):
        self.music_dir.mkdir(parents=True, exist_ok=True)
        self.meta_path.write_text(
            json.dumps(self.meta, ensure_ascii=False, indent=1), encoding="utf-8"
        )

    def _load_derived(self, server: str) -> bool:
        path = self.derived_path[server]
        if not path.exists():
            return False
        try:
            songs = json.loads(path.read_text(encoding="utf-8"))
            if not isinstance(songs, list) or not songs:
                return False
            self.songs[server] = songs
            return True
        except Exception as e:
            logger.warning(f"[PJSK歌词猜曲] 加载 {SERVER_LABELS[server]}派生题库失败: {e}")
            return False

    # ---------- 网络层 ----------

    async def _get_session(self) -> aiohttp.ClientSession:
        if self._session is None or self._session.closed:
            self._session = aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=self.request_timeout),
                headers={
                    "User-Agent": "astrbot_plugin_pjsk_guess_lyrics (+https://github.com/AstrBotDevs/AstrBot)"
                },
            )
        return self._session

    async def _fetch_url(self, url: str) -> bytes:
        session = await self._get_session()
        async with session.get(url) as resp:
            resp.raise_for_status()
            return await resp.read()

    async def _fetch_remote_json(
        self, repo: str, remote_path: str, small: bool
    ) -> tuple[object | None, str | None]:
        """优先 GitHub Contents API 拉取 JSON，返回 (解析结果, blob sha)。

        small=True（1MB 以下文件）走 base64 通道；small=False（大文件）先按 base64
        探测，拿不到内容时自动改用同一 API 的 raw 媒体类型（支持 1~100MB）。
        GitHub API 不可用时回退 jsDelivr。全部失败时返回 (None, None)。
        """
        api_url = f"https://api.github.com/repos/{repo}/contents/{remote_path}?ref={_GITHUB_BRANCH}"
        session = await self._get_session()

        # 1) base64 通道（同时拿到 blob sha）
        try:
            async with session.get(api_url) as resp:
                if resp.status == 200:
                    payload = await resp.json()
                    content = payload.get("content")
                    encoding = payload.get("encoding", "base64")
                    sha = payload.get("sha")
                    if content and encoding == "base64":
                        return json.loads(base64.b64decode(content)), sha
                    if small:
                        logger.warning(
                            f"[PJSK歌词猜曲] GitHub API 未返回 {repo}/{remote_path} 的内容，回退 jsDelivr"
                        )
                    # 大文件 content 为空（超过 1MB），进入 raw 通道
                elif resp.status == 403:
                    logger.warning(
                        "[PJSK歌词猜曲] GitHub API 限流(403)。"
                        "提示: 匿名限额 60 次/小时/IP，可等待配额恢复。"
                    )
                else:
                    logger.warning(
                        f"[PJSK歌词猜曲] GitHub API 返回 {resp.status}: {repo}/{remote_path}"
                    )
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.warning(f"[PJSK歌词猜曲] GitHub API 拉取失败({repo}/{remote_path}): {e}")

        # 2) raw 媒体类型通道（1MB ~ 100MB 文件）
        if not small:
            try:
                async with session.get(api_url, headers={"Accept": "application/vnd.github.raw"}) as resp:
                    if resp.status == 200:
                        data = await resp.read()
                        return json.loads(data.decode("utf-8")), None
                    logger.warning(
                        f"[PJSK歌词猜曲] GitHub API raw 通道返回 {resp.status}: {repo}/{remote_path}"
                    )
            except asyncio.CancelledError:
                raise
            except Exception as e:
                logger.warning(
                    f"[PJSK歌词猜曲] GitHub API raw 通道拉取失败({repo}/{remote_path}): {e}"
                )

        # 3) jsDelivr 回退
        jsd_url = _JSDELIVR_TPL.format(repo=repo, branch=_GITHUB_BRANCH, path=remote_path)
        try:
            data = await self._fetch_url(jsd_url)
            return json.loads(data.decode("utf-8")), None
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.warning(f"[PJSK歌词猜曲] jsDelivr 回退失败({repo}/{remote_path}): {e}")
            return None, None

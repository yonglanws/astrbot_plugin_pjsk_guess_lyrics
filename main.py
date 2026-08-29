import asyncio
import json
import random
import time
import os
import sqlite3
import urllib.request
import urllib.error
import io
import re
from datetime import datetime
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, List, Dict, Generator, Tuple
from collections import OrderedDict
from urllib.parse import quote

from PIL import Image, ImageDraw, ImageFont
from pilmoji import Pilmoji

from astrbot.api import logger

try:
    from astrbot.api.event import filter, AstrMessageEvent
    from astrbot.api.star import Context, Star, register, StarTools
    import astrbot.api.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController, SessionFilter
    from astrbot.api import AstrBotConfig
    from astrbot.core.utils.astrbot_path import get_astrbot_data_path
except ImportError:
    logger.error("Failed to import from astrbot.api, attempting fallback.")
    from astrbot.core.plugin import Plugin as Star, Context, register, filter, AstrMessageEvent
    import astrbot.core.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController, SessionFilter

    class StarTools:
        @staticmethod
        def get_data_dir(plugin_name: str) -> Path:
            return Path(__file__).parent.parent.parent.parent / 'data' / 'plugin_data' / plugin_name

    def get_astrbot_data_path() -> Path:
        return Path(__file__).parent.parent.parent.parent / 'data'


try:
    from .master_data_service import SERVER_JP, SERVER_SC, MasterDataService
except ImportError:  # 直接以脚本方式加载（单测）时使用绝对导入
    from master_data_service import SERVER_JP, SERVER_SC, MasterDataService



try:
    from PIL.Image import Resampling
    LANCZOS = Resampling.LANCZOS
except ImportError:
    LANCZOS = 1


PLUGIN_NAME = "pjsk_guess_lyrics"
PLUGIN_AUTHOR = "慵懒午睡"
PLUGIN_DESCRIPTION = "PJSK歌词猜曲插件"
PLUGIN_VERSION = "1.1.0"
PLUGIN_REPO_URL = "https://github.com/yonglanws/astrbot_plugin_pjsk_guess_lyrics"
DEFAULT_PLATFORM_NAME = "aiocqhttp"
OFFICIAL_PLATFORM_NAME = "qq_official"
OFFICIAL_QID_PATTERN = re.compile(r"^[0-9a-fA-F]{32}$")

# --- 题库服务器与官机 markdown 机制（与 PJSK Wordle 保持一致） ---
SERVER_JP = "jp"
SERVER_SC = "sc"
SERVER_LABELS = {SERVER_JP: "日服", SERVER_SC: "国服"}
SERVER_BADGES = {SERVER_JP: "日服题库", SERVER_SC: "国服题库"}
# 结算尾部显示的切换指令（当前日服 → 提示切换国服）
SWITCH_COMMANDS = {SERVER_JP: "歌词猜曲切换国服题库", SERVER_SC: "歌词猜曲切换日服题库"}
# 结算连接入口使用的指令名（与注册指令别名一一对应）
CONNECT_SWITCH_COMMANDS = {SERVER_JP: "歌词猜曲切换国服题库", SERVER_SC: "歌词猜曲切换日服题库"}

# 指令连接的默认 markdown 模板：QQ 官方机器人 markdown 消息的参数指令标签
# （见 bot.q.qq.com/wiki 的 markdown / text-chain 文档）。
# text 只放指令本身：QQ 客户端在群聊发送时会自动 @ 官方机器人，
# 拼进 "@id" 反而会出现双重 @。
DEFAULT_CONNECT_TEMPLATE = '<qqbot-cmd-input text="{encoded_command}" show="{encoded_name}" />'
DEFAULT_JP_RESOURCE_URL_BASE = "https://storage.exmeaning.com/sekai-jp-assets"
DEFAULT_SC_RESOURCE_URL_BASE = "https://storage.exmeaning.com/sekai-sc-assets"
# 旧版本默认模板特征：命中即视为未自定义，自动升级到新默认模板
_LEGACY_TEMPLATE_MARKERS = ("{encoded_at_text}", "mqqapi://")

# 快捷入口：所有 PJSK 娱乐插件的触发指令，Wordle 固定排最后


class BindingSessionFilter(SessionFilter):
    """只接收发起绑定的同一用户在同一会话中的确认消息。"""

    def __init__(self, session_id: str, user_id: str):
        self.session_id = str(session_id)
        self.user_id = str(user_id)

    def filter(self, event: AstrMessageEvent) -> str:
        if (
            str(event.unified_msg_origin) != self.session_id
            or str(event.get_sender_id()) != self.user_id
        ):
            return ""
        return f"{event.unified_msg_origin}:{event.get_sender_id()}"


@dataclass
class SongInfo:
    """歌曲信息数据类"""
    music_id: int
    original_name: str
    lrc_path: Path
    image_path: Optional[Path] = None
    cn_title: Optional[str] = None
    
    @property
    def display_name(self) -> str:
        """获取显示名称"""
        return self.cn_title if self.cn_title else self.original_name


@dataclass
class GameData:
    """游戏数据类"""
    correct_song: SongInfo
    lyrics_snippet: List[str]
    options: List[SongInfo]
    correct_index: int
    score: int = 1


@dataclass
class GameSession:
    """游戏会话状态"""
    game_data: Optional[GameData] = None
    answer_index: Optional[int] = None
    game_ended_by_timeout: bool = False
    total_attempts: int = 0
    player_attempts: Dict[str, int] = None
    
    def __post_init__(self):
        if self.player_attempts is None:
            self.player_attempts = {}


class LRUDict(OrderedDict):
    """LRU缓存字典，防止内存无限增长"""
    
    def __init__(self, max_size: int = 500):
        super().__init__()
        self.max_size = max_size
    
    def __setitem__(self, key, value):
        if key in self:
            self.move_to_end(key)
        super().__setitem__(key, value)
        if len(self) > self.max_size:
            self.popitem(last=False)


class Config:
    """配置常量"""
    DEFAULT_OPTION_COUNT = 10
    DEFAULT_TIMEOUT = 30
    DEFAULT_COOLDOWN = 30
    DEFAULT_DAILY_LIMIT = 10
    DEFAULT_MAX_ATTEMPTS = 10
    CLEANUP_INTERVAL = 3600
    MAX_AGE_SECONDS = 3600
    LYRICS_LINES_COUNT = 20
    MAX_CUSTOM_NAME_LENGTH = 20
    MAX_SESSION_CACHE_SIZE = 500
    
    class Image:
        MAX_WIDTH = 800
        PADDING = 40
        LINE_SPACING = 15
        OPTION_HEIGHT = 80
        HEADER_HEIGHT = 60
        COVER_SIZE = 60
        
        class Grid:
            COLUMNS = 2
            CARD_WIDTH = 480
            CARD_HEIGHT = 160
            CARD_GAP = 20
            CARD_PADDING = 15
            COVER_SIZE = 130
        
        class FontSize:
            LYRICS_JP = 28
            LYRICS_CN = 24
            TITLE = 36
            OPTION = 24
            SMALL = 18
            CARD_TITLE = 24
            CARD_SUBTITLE = 16
    
    class Color:
        BG_WHITE = (255, 255, 255)
        BG_LIGHT = (248, 249, 250)
        BG_CARD = (255, 255, 255)
        TEXT_DARK = (33, 37, 41)
        TEXT_GRAY = (108, 117, 125)
        TEXT_LIGHT_GRAY = (173, 181, 189)
        TEXT_ACCENT = (102, 126, 234)
        TEXT_JP = (33, 37, 41)
        TEXT_CN = (108, 117, 125)
        BORDER_LIGHT = (222, 226, 230)
        CARD_SHADOW = (233, 236, 239)
        BG_DARK = (25, 25, 35)
        BG_MEDIUM = (30, 30, 50)
        BG_RANKING = (30, 40, 60)
        TEXT_WHITE = (255, 255, 255)
        TEXT_SHADOW = (100, 100, 120)
        TEXT_GOLD = (255, 220, 100)
        TEXT_YELLOW = (255, 200, 100)
        TEXT_GREEN = (100, 255, 100)
        TEXT_BLUE = (100, 200, 255)
        TEXT_SUBTITLE = (102, 102, 102)
        OUTLINE = (80, 80, 120)
        CARD_OUTLINE = (70, 72, 100)
        LINE = (60, 60, 80)
        MEDAL_GOLD = (255, 215, 0)


class CloudJacketLoader:
    """云端曲绘加载器"""
    
    def __init__(self, cache_dir: Optional[Path] = None, config=None):
        self.cache_dir = cache_dir
        self.config = config or {}
        if cache_dir:
            cache_dir.mkdir(parents=True, exist_ok=True)
    
    def _format_jacket_id(self, music_id: int) -> str:
        """格式化曲绘 ID：1-99 补零至三位，其余保持原样。"""
        return f"{music_id:03d}" if 1 <= music_id <= 99 else str(music_id)

    def get_jacket_url(self, music_id: int, server: str = SERVER_JP) -> Optional[str]:
        """获取当前题库服务器对应的曲绘 URL。"""
        if music_id < 1:
            return None
        config_key = "sc_resource_url_base" if server == SERVER_SC else "jp_resource_url_base"
        default = DEFAULT_SC_RESOURCE_URL_BASE if server == SERVER_SC else DEFAULT_JP_RESOURCE_URL_BASE
        base_url = str(self.config.get(config_key, default) or default).strip().rstrip("/")
        jacket_id = self._format_jacket_id(music_id)
        return f"{base_url}/music/jacket/jacket_s_{jacket_id}/jacket_s_{jacket_id}.png"

    def load_jacket_image(self, music_id: int, server: str = SERVER_JP) -> Optional[Image.Image]:
        """从云端加载曲绘图片"""
        if self.cache_dir:
            cache_file = self.cache_dir / f"{server}_{music_id}.png"
            if cache_file.exists():
                try:
                    with Image.open(cache_file) as img:
                        return img.copy()
                except (IOError, OSError) as e:
                    logger.warning(f"Failed to load cached image {cache_file}: {e}")
                    try:
                        cache_file.unlink()
                    except OSError:
                        pass
        
        url = self.get_jacket_url(music_id, server)
        if not url:
            return None
        
        try:
            req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0'})
            with urllib.request.urlopen(req, timeout=10) as response:
                img_data = response.read()
                img = Image.open(io.BytesIO(img_data))
                img.load()
                
                if self.cache_dir:
                    try:
                        cache_file = self.cache_dir / f"{server}_{music_id}.png"
                        img.save(cache_file)
                    except (IOError, OSError) as save_error:
                        logger.warning(f"Failed to cache jacket image: {save_error}")
                
                return img
        except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError, IOError) as e:
            logger.warning(f"Failed to load jacket from cloud for music_id {music_id}: {e}")
            return None


class LocalDataManager:
    """本地数据管理器，从本地文件读取歌曲翻译和别名数据"""
    
    def __init__(self, data_dir: Path, songs_file: Optional[Path] = None, aliases_file: Optional[Path] = None):
        self.data_dir = data_dir
        self.data_dir.mkdir(parents=True, exist_ok=True)
        self.songs_file = songs_file
        self.aliases_file = aliases_file
        self.cn_map: Dict[int, str] = {}
        self.name_to_id_map: Dict[str, int] = {}
        self.id_to_name_map: Dict[int, str] = {}
        self.aliases_map: Dict[int, List[str]] = {}
        self._load_local_data()
    
    def _load_local_data(self):
        """从本地 JSON 文件加载数据"""
        self._load_songs_data()
        self._load_aliases_data()
    
    def _load_songs_data(self):
        """加载歌曲数据（包含中文翻译）"""
        if self.songs_file and self.songs_file.exists():
            self._parse_songs_file(self.songs_file)
        else:
            translation_file = self.data_dir / "translations.json"
            if translation_file.exists():
                try:
                    with open(translation_file, 'r', encoding='utf-8') as f:
                        data = json.load(f)
                        self._build_cn_map(data)
                    logger.info(f"Loaded {len(self.cn_map)} translations from local file")
                except (json.JSONDecodeError, IOError, OSError) as e:
                    logger.warning(f"Failed to load translations: {e}")
            else:
                logger.warning(f"Translation file not found: {translation_file}")
    
    def _parse_songs_file(self, file_path: Path):
        """解析 songs.json 格式的数据"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)

            for item in data:
                if item.get("g") == "music":
                    music_id = item.get("id")
                    name = item.get("n", "")
                    cn_title = item.get("cn")
                    
                    if music_id:
                        self.id_to_name_map[music_id] = name
                        if cn_title:
                            self.cn_map[music_id] = cn_title
                            self.name_to_id_map[cn_title] = music_id
                        self.name_to_id_map[name] = music_id

            logger.info(f"Loaded {len(self.cn_map)} translations, {len(self.id_to_name_map)} songs from songs.json")
        except (json.JSONDecodeError, IOError, OSError, KeyError) as e:
            logger.warning(f"Failed to load songs data: {e}")
    
    def _build_cn_map(self, search_index_data: List[Dict]):
        """构建 musicId -> 中文标题 的映射"""
        self.cn_map = {}
        for item in search_index_data:
            if item.get("g") == "music" and item.get("cn"):
                try:
                    music_id = int(item.get("id"))
                    self.cn_map[music_id] = item["cn"]
                except (ValueError, TypeError):
                    continue
    
    def _load_aliases_data(self):
        """加载别名数据"""
        if self.aliases_file and self.aliases_file.exists():
            self._parse_aliases_file(self.aliases_file)
        else:
            aliases_file = self.data_dir / "aliases.json"
            if aliases_file.exists():
                try:
                    with open(aliases_file, 'r', encoding='utf-8') as f:
                        data = json.load(f)
                        self._build_aliases_map(data)
                    logger.info(f"Loaded {len(self.aliases_map)} aliases from local file")
                except (json.JSONDecodeError, IOError, OSError) as e:
                    logger.warning(f"Failed to load aliases: {e}")
    
    def _parse_aliases_file(self, file_path: Path):
        """解析 aliases.json 格式的数据"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            self._build_aliases_map(data)
            logger.info(f"Loaded {len(self.aliases_map)} aliases from aliases.json")
        except (json.JSONDecodeError, IOError, OSError) as e:
            logger.warning(f"Failed to load aliases data: {e}")
    
    def _build_aliases_map(self, aliases_data: Dict):
        """构建 musicId -> 别名列表 的映射"""
        self.aliases_map = {}
        musics = aliases_data.get("musics", [])
        for entry in musics:
            try:
                music_id = int(entry.get("music_id"))
                aliases = entry.get("aliases", [])
                if aliases:
                    self.aliases_map[music_id] = aliases
            except (ValueError, TypeError):
                continue
    
    def get_cn_title(self, music_id: Optional[int]) -> Optional[str]:
        """获取中文标题"""
        if music_id is None:
            return None
        return self.cn_map.get(music_id)
    
    def get_music_id_by_name(self, name: str) -> Optional[int]:
        """通过名称获取 music_id"""
        return self.name_to_id_map.get(name)
    
    def get_aliases(self, music_id: int) -> List[str]:
        """获取歌曲的所有别名"""
        return self.aliases_map.get(music_id, [])

    def apply_master_songs(self, songs: List[dict], replace: bool = False) -> None:
        """用 master 同步数据重建歌名/翻译/别名映射（覆盖两服并集）。"""
        if replace:
            self.cn_map.clear()
            self.name_to_id_map.clear()
            self.id_to_name_map.clear()
            self.aliases_map.clear()
        for song in songs:
            mid = song.get("id")
            title = song.get("title")
            if mid is None or not title:
                continue
            self.id_to_name_map[mid] = title
            self.name_to_id_map[title] = mid
            cn = song.get("cn")
            if cn:
                self.cn_map[mid] = cn
                self.name_to_id_map[cn] = mid
            aliases = song.get("aliases") or []
            if aliases:
                self.aliases_map[mid] = list(aliases)
    
    def reload_data(self):
        """重新加载本地数据"""
        self.cn_map.clear()
        self.name_to_id_map.clear()
        self.id_to_name_map.clear()
        self.aliases_map.clear()
        self._load_local_data()


class LrcParser:
    """LRC 歌词解析器"""
    
    ENCODINGS = ['utf-8', 'utf-8-sig', 'utf-16', 'shift-jis', 'gbk', 'latin1']
    
    @classmethod
    def parse(cls, lrc_path: Path) -> List[str]:
        """解析 LRC 文件并提取歌词文本"""
        content = cls._read_file(lrc_path)
        if content is None:
            logger.error(f"Failed to read LRC file with any encoding: {lrc_path}")
            return []

        return cls._extract_lyrics(content)
    
    @classmethod
    def _read_file(cls, lrc_path: Path) -> Optional[str]:
        """尝试多种编码读取文件"""
        for encoding in cls.ENCODINGS:
            try:
                with open(lrc_path, 'r', encoding=encoding) as f:
                    return f.read()
            except (UnicodeDecodeError, LookupError, IOError):
                continue
        return None
    
    @classmethod
    def _extract_lyrics(cls, content: str) -> List[str]:
        """从内容中提取歌词"""
        lyrics = []
        for line in content.split('\n'):
            line = line.strip()
            if line and not line.startswith('['):
                lyrics.append(line)
        return lyrics


class LocalSongManager:
    """本地歌曲管理器"""
    
    def __init__(self, lyrics_dir: Path, data_manager: LocalDataManager, cloud_jacket_loader: Optional[CloudJacketLoader] = None):
        self.lyrics_dir = lyrics_dir
        self.data_manager = data_manager
        self.cloud_jacket_loader = cloud_jacket_loader
        self.songs: List[SongInfo] = []
        self._load_local_songs()
    
    def _load_local_songs(self):
        """加载所有歌曲"""
        if not self.lyrics_dir.exists():
            logger.warning(f"Lyrics directory does not exist: {self.lyrics_dir}")
            return
        
        lrc_files = list(self.lyrics_dir.glob("*.lrc"))
        
        for lrc_file in lrc_files:
            try:
                music_id = int(lrc_file.stem)
            except ValueError:
                logger.warning(f"Invalid lrc filename (not a number): {lrc_file}")
                continue
            
            original_name = self.data_manager.id_to_name_map.get(music_id, str(music_id))
            cn_title = self.data_manager.get_cn_title(music_id)
            
            self.songs.append(SongInfo(
                music_id=music_id,
                original_name=original_name,
                lrc_path=lrc_file,
                image_path=None,
                cn_title=cn_title
            ))
        
        logger.info(f"Loaded {len(self.songs)} songs from {self.lyrics_dir}")
    
    def get_random_song(self, songs: Optional[List[SongInfo]] = None) -> Optional[SongInfo]:
        """获取随机歌曲（默认从全部歌曲中选取，可指定题库曲池）"""
        pool = songs if songs is not None else self.songs
        return random.choice(pool) if pool else None

    def get_random_options(
        self,
        correct_song: SongInfo,
        option_count: int = Config.DEFAULT_OPTION_COUNT,
        songs: Optional[List[SongInfo]] = None,
    ) -> List[SongInfo]:
        """获取随机选项（包含正确答案，默认从全部歌曲中选取）"""
        pool = songs if songs is not None else self.songs
        options = [correct_song]
        available_songs = [s for s in pool if s.music_id != correct_song.music_id]
        
        if len(available_songs) >= option_count - 1:
            options.extend(random.sample(available_songs, option_count - 1))
        else:
            options.extend(available_songs)
        
        random.shuffle(options)
        return options
    
    def get_display_name(self, song: SongInfo) -> str:
        """获取歌曲显示名称"""
        return song.display_name
    
    def get_jacket_image(self, song: SongInfo, server: str = SERVER_JP) -> Optional[Image.Image]:
        """按当前题库服务器获取曲绘图片（优先从云端加载）。"""
        if self.cloud_jacket_loader:
            img = self.cloud_jacket_loader.load_jacket_image(song.music_id, server)
            if img:
                return img
        return None


class ImageGenerator:
    """图片生成器"""
    
    def __init__(self, font_path: Optional[Path] = None):
        self.font_path = font_path
        self.lyrics_jp_font: ImageFont.FreeTypeFont
        self.lyrics_cn_font: ImageFont.FreeTypeFont
        self.title_font: ImageFont.FreeTypeFont
        self.option_font: ImageFont.FreeTypeFont
        self.small_font: ImageFont.FreeTypeFont
        self.card_title_font: ImageFont.FreeTypeFont
        self.card_subtitle_font: ImageFont.FreeTypeFont
        self.ranking_title_font: ImageFont.FreeTypeFont
        self.header_font: ImageFont.FreeTypeFont
        self.body_font: ImageFont.FreeTypeFont
        self.id_font: ImageFont.FreeTypeFont
        self.medal_font: ImageFont.FreeTypeFont
        self._load_fonts()

    def _load_fonts(self):
        """加载字体（排行榜字号与猜卡面排行榜保持一致）"""
        default_font = ImageFont.load_default()

        if self.font_path and self.font_path.exists():
            try:
                self.lyrics_jp_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.LYRICS_JP)
                self.lyrics_cn_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.LYRICS_CN)
                self.title_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.TITLE)
                self.option_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.OPTION)
                self.small_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.SMALL)
                self.card_title_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.CARD_TITLE)
                self.card_subtitle_font = ImageFont.truetype(str(self.font_path), Config.Image.FontSize.CARD_SUBTITLE)
                # 排行榜专用字号（与猜卡面排行榜完全一致）
                self.ranking_title_font = ImageFont.truetype(str(self.font_path), 48)
                self.header_font = ImageFont.truetype(str(self.font_path), 28)
                self.body_font = ImageFont.truetype(str(self.font_path), 26)
                self.id_font = ImageFont.truetype(str(self.font_path), 16)
                self.medal_font = ImageFont.truetype(str(self.font_path), 36)
                return
            except (IOError, OSError) as e:
                logger.error(f"Failed to load fonts: {e}")

        self.lyrics_jp_font = default_font
        self.lyrics_cn_font = default_font
        self.title_font = default_font
        self.option_font = default_font
        self.small_font = default_font
        self.card_title_font = default_font
        self.card_subtitle_font = default_font
        self.ranking_title_font = default_font
        self.header_font = default_font
        self.body_font = default_font
        self.id_font = default_font
        self.medal_font = default_font
        logger.warning("Using default font")
    
    def _get_text_width(self, draw: ImageDraw.ImageDraw, text: str, font: ImageFont.FreeTypeFont) -> int:
        """获取文本宽度"""
        try:
            return int(draw.textlength(text, font=font))
        except AttributeError:
            return font.getsize(text)[0]
    
    def _truncate_text(self, draw: ImageDraw.ImageDraw, text: str, font: ImageFont.FreeTypeFont, max_width: int) -> str:
        """截断文本以适应最大宽度"""
        while self._get_text_width(draw, text + "...", font) > max_width and len(text) > 0:
            text = text[:-1]
        return text
    
    def create_lyrics_image(self, lyrics_lines: List[str]) -> Optional[Image.Image]:
        """创建歌词图片（白色色调，日文中文交替显示）"""
        try:
            if not lyrics_lines:
                return None
            
            colors = Config.Color
            padding = 50
            line_spacing = 8
            jp_cn_gap = 4
            
            dummy_draw = ImageDraw.Draw(Image.new('RGB', (1, 1)))
            max_text_width = 0
            for line in lyrics_lines:
                bbox = dummy_draw.textbbox((0, 0), line, font=self.lyrics_jp_font)
                text_width = bbox[2] - bbox[0]
                max_text_width = max(max_text_width, text_width)
            
            img_width = min(Config.Image.MAX_WIDTH, max_text_width + padding * 2)
            
            jp_height = Config.Image.FontSize.LYRICS_JP
            cn_height = Config.Image.FontSize.LYRICS_CN
            pair_height = jp_height + cn_height + jp_cn_gap + line_spacing
            img_height = len(lyrics_lines) * pair_height + padding * 2 + 80
            
            img = Image.new('RGB', (img_width, img_height), colors.BG_WHITE)
            draw = ImageDraw.Draw(img)
            
            title = "歌词片段"
            title_width = self._get_text_width(draw, title, self.title_font)
            draw.text(((img_width - title_width) // 2, 20), title, font=self.title_font, fill=colors.TEXT_ACCENT)
            
            for i, line in enumerate(lyrics_lines):
                y = padding + 60 + i * pair_height
                
                text_width = self._get_text_width(draw, line, self.lyrics_jp_font)
                x = (img_width - text_width) // 2
                
                draw.text((x, y), line, font=self.lyrics_jp_font, fill=colors.TEXT_JP)
                
               
            return img
        except (IOError, OSError, ValueError, KeyError) as e:
            logger.error(f"Failed to create lyrics image: {e}")
            return None
    

    
    def create_options_image(self, options: List[Tuple[int, Optional[str], str, Optional[str]]]) -> Optional[Image.Image]:
        """
        创建选项图片（两排网格布局，白色色调，大封面）
        
        Args:
            options: 选项列表，每个元素为 (序号, 中文名称, 原名称, 封面路径)
                     中文名称可能为 None
        
        Returns:
            生成的图片或 None
        """
        try:
            grid = Config.Image.Grid
            colors = Config.Color
            
            columns = grid.COLUMNS
            rows = (len(options) + columns - 1) // columns
            
            img_width = columns * grid.CARD_WIDTH + (columns + 1) * grid.CARD_GAP
            img_height = 80 + rows * grid.CARD_HEIGHT + (rows + 1) * grid.CARD_GAP
            
            img = Image.new('RGB', (img_width, img_height), colors.BG_LIGHT)
            draw = ImageDraw.Draw(img)
            
            header_text = "请发送正确答案 (1-10)"
            header_width = self._get_text_width(draw, header_text, self.title_font)
            draw.text(((img_width - header_width) // 2, 20), header_text, font=self.title_font, fill=colors.TEXT_ACCENT)
            
            for i, (num, cn_title, original_name, cover_path) in enumerate(options):
                row = i // columns
                col = i % columns
                
                x = grid.CARD_GAP + col * (grid.CARD_WIDTH + grid.CARD_GAP)
                y = 80 + grid.CARD_GAP + row * (grid.CARD_HEIGHT + grid.CARD_GAP)
                
                self._draw_option_card(img, draw, x, y, num, cn_title, original_name, cover_path)
            
            return img
        except (IOError, OSError, ValueError, KeyError) as e:
            logger.error(f"Failed to create options image: {e}")
            return None
    
    def _draw_option_card(
        self, 
        img: Image.Image, 
        draw: ImageDraw.ImageDraw, 
        x: int, 
        y: int, 
        num: int, 
        cn_title: Optional[str], 
        original_name: str,
        cover_path: Optional[str]
    ):
        """绘制单个选项卡片（白色色调，大封面）"""
        grid = Config.Image.Grid
        colors = Config.Color
        
        draw.rounded_rectangle(
            [x, y, x + grid.CARD_WIDTH, y + grid.CARD_HEIGHT],
            radius=15,
            fill=colors.BG_CARD,
            outline=colors.BORDER_LIGHT,
            width=1
        )
        
        if cover_path:
            self._paste_cover_in_card(img, cover_path, x, y, grid)
        
        text_start_x = x + grid.CARD_PADDING
        max_text_width = grid.CARD_WIDTH - grid.COVER_SIZE - grid.CARD_PADDING * 3
        
        num_text = f"{num}."
        draw.text((text_start_x, y + grid.CARD_PADDING), num_text, font=self.card_title_font, fill=colors.TEXT_ACCENT)
        
        if cn_title:
            title = self._truncate_text(draw, cn_title, self.card_title_font, max_text_width)
            draw.text((text_start_x + 35, y + grid.CARD_PADDING), title, font=self.card_title_font, fill=colors.TEXT_DARK)
            
            subtitle = self._truncate_text(draw, original_name, self.card_subtitle_font, max_text_width)
            draw.text((text_start_x, y + grid.CARD_PADDING + 35), subtitle, font=self.card_subtitle_font, fill=colors.TEXT_GRAY)
        else:
            title = self._truncate_text(draw, original_name, self.card_title_font, max_text_width)
            draw.text((text_start_x + 35, y + grid.CARD_PADDING), title, font=self.card_title_font, fill=colors.TEXT_DARK)
            
            subtitle = self._truncate_text(draw, original_name, self.card_subtitle_font, max_text_width)
            draw.text((text_start_x, y + grid.CARD_PADDING + 35), subtitle, font=self.card_subtitle_font, fill=colors.TEXT_LIGHT_GRAY)
    
    def _paste_cover_in_card(self, img: Image.Image, cover_path: str, card_x: int, card_y: int, grid):
        """在卡片内粘贴封面图片（大封面）"""
        try:
            path = Path(cover_path)
            if not path.exists():
                return
            cover_img = Image.open(path)
            cover_img = cover_img.resize((grid.COVER_SIZE, grid.COVER_SIZE), LANCZOS)
            
            cover_x = card_x + grid.CARD_WIDTH - grid.COVER_SIZE - grid.CARD_PADDING
            cover_y = card_y + (grid.CARD_HEIGHT - grid.COVER_SIZE) // 2
            
            mask = Image.new('L', (grid.COVER_SIZE, grid.COVER_SIZE), 0)
            mask_draw = ImageDraw.Draw(mask)
            mask_draw.rounded_rectangle([0, 0, grid.COVER_SIZE, grid.COVER_SIZE], radius=10, fill=255)
            
            output = Image.new('RGBA', cover_img.size, (0, 0, 0, 0))
            output.paste(cover_img, (0, 0))
            output.putalpha(mask)
            
            img.paste(output, (cover_x, cover_y), output)
        except (IOError, OSError) as e:
            logger.warning(f"Failed to load cover: {e}")
    
    def save_image(self, img: Image.Image, output_dir: Path, prefix: str = "quiz") -> Optional[str]:
        """保存图片并返回路径"""
        try:
            os.makedirs(output_dir, exist_ok=True)
            filepath = output_dir / f"{prefix}_{time.time_ns()}.png"
            img.save(filepath)
            return str(filepath)
        except (IOError, OSError) as e:
            logger.error(f"Failed to save image: {e}")
            return None
    
    def create_ranking_image(self, rows: List[Tuple], output_dir: Path) -> Optional[str]:
        """渲染与猜卡面排行榜一致的横向表格图片"""
        try:
            width = 850
            base_height = 250
            item_height = 70
            height = base_height + len(rows) * item_height

            bg_color_start = (230, 240, 255)
            bg_color_end = (200, 210, 240)
            img = Image.new("RGB", (width, height), bg_color_start)
            draw_bg = ImageDraw.Draw(img)
            for y in range(height):
                r = int(bg_color_start[0] + (bg_color_end[0] - bg_color_start[0]) * y / height)
                g = int(bg_color_start[1] + (bg_color_end[1] - bg_color_start[1]) * y / height)
                b = int(bg_color_start[2] + (bg_color_end[2] - bg_color_start[2]) * y / height)
                draw_bg.line([(0, y), (width, y)], fill=(r, g, b))

            if img.mode != "RGBA":
                img = img.convert("RGBA")

            white_overlay = Image.new("RGBA", img.size, (255, 255, 255, 100))
            img = Image.alpha_composite(img, white_overlay)

            title_text = "PJSK歌词猜曲排行榜"
            font_color = (30, 30, 50)
            shadow_color = (180, 180, 190, 128)
            header_color = (80, 90, 120)
            score_color = (235, 120, 20)
            accuracy_color = (0, 128, 128)

            with Pilmoji(img) as pilmoji:
                center_x, title_y = int(width / 2), 80
                pilmoji.text(
                    (center_x + 2, title_y + 2),
                    title_text,
                    font=self.ranking_title_font,
                    fill=shadow_color,
                    anchor="mm",
                    emoji_position_offset=(0, 6),
                )
                pilmoji.text(
                    (center_x, title_y),
                    title_text,
                    font=self.ranking_title_font,
                    fill=font_color,
                    anchor="mm",
                    emoji_position_offset=(0, 6),
                )

                headers = ["排名", "玩家", "总分", "正确率", "总次数"]
                col_positions_header = [40, 150, 500, 610, 720]
                title_height = pilmoji.getsize(title_text, font=self.ranking_title_font)[1]
                current_y = title_y + int(title_height / 2) + 45
                for header in headers:
                    pilmoji.text(
                        (col_positions_header.pop(0), current_y),
                        header,
                        font=self.header_font,
                        fill=header_color,
                    )

                current_y += 55
                rank_icons = ["🥇", "🥈", "🥉"]

                for i, row in enumerate(rows):
                    user_id, user_name, custom_name, score, attempts, correct_attempts = (
                        str(row[0]), row[1], row[2], str(row[3]), str(row[4]), row[5]
                    )
                    is_unbound_official = len(row) > 6 and bool(row[6])
                    display_name = custom_name if custom_name else user_name
                    accuracy = f"{(correct_attempts * 100 / int(attempts) if int(attempts) > 0 else 0):.1f}%"

                    rank = i + 1
                    col_positions = [40, 150, 500, 610, 720]
                    rank_num_align_x = 130
                    pilmoji.text(
                        (rank_num_align_x, current_y),
                        str(rank),
                        font=self.body_font,
                        fill=font_color,
                        anchor="ra",
                    )

                    if i < 3:
                        pilmoji.text(
                            (col_positions[0], current_y - 30),
                            rank_icons[i],
                            font=self.medal_font,
                            fill=font_color,
                        )

                    name_x = col_positions[1]
                    if is_unbound_official:
                        badge_text = "未绑定QQ"
                        badge_text_width = pilmoji.getsize(
                            badge_text,
                            font=self.id_font,
                        )[0]
                        badge_width = badge_text_width + 16
                        badge_height = 26
                        badge_y = current_y + 3
                        draw = ImageDraw.Draw(img)
                        draw.rounded_rectangle(
                            [
                                name_x,
                                badge_y,
                                name_x + badge_width,
                                badge_y + badge_height,
                            ],
                            radius=8,
                            fill=(115, 125, 150, 230),
                        )
                        pilmoji.text(
                            (name_x + 8, badge_y + 4),
                            badge_text,
                            font=self.id_font,
                            fill=(255, 255, 255, 255),
                        )
                        name_x += badge_width + 10

                    max_name_width = col_positions[2] - name_x - 20
                    if self.body_font.getbbox(display_name)[2] > max_name_width:
                        while self.body_font.getbbox(display_name + "...")[2] > max_name_width and len(display_name) > 0:
                            display_name = display_name[:-1]
                        display_name += "..."

                    pilmoji.text(
                        (name_x, current_y),
                        display_name,
                        font=self.body_font,
                        fill=font_color,
                    )
                    id_text = f"{user_name} ID: {user_id}"
                    max_id_width = col_positions[2] - col_positions[1] - 20
                    if self.id_font.getbbox(id_text)[2] > max_id_width:
                        while self.id_font.getbbox(id_text + "...")[2] > max_id_width and len(id_text) > 0:
                            id_text = id_text[:-1]
                        id_text += "..."
                    pilmoji.text(
                        (col_positions[1], current_y + 32),
                        id_text,
                        font=self.id_font,
                        fill=header_color,
                    )
                    pilmoji.text(
                        (col_positions[2], current_y),
                        score,
                        font=self.body_font,
                        fill=score_color,
                    )
                    pilmoji.text(
                        (col_positions[3], current_y),
                        accuracy,
                        font=self.body_font,
                        fill=accuracy_color,
                    )
                    pilmoji.text(
                        (col_positions[4], current_y),
                        attempts,
                        font=self.body_font,
                        fill=font_color,
                    )

                    separator_y = current_y + 60
                    if i < len(rows) - 1:
                        draw = ImageDraw.Draw(img)
                        draw.line([(30, separator_y), (width - 30, separator_y)], fill=(200, 200, 210, 128), width=1)

                    current_y += 70

                footer_text = f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}"
                footer_y = height - 25
                pilmoji.text(
                    (center_x, footer_y),
                    footer_text,
                    font=self.id_font,
                    fill=header_color,
                    anchor="ms",
                )

            os.makedirs(output_dir, exist_ok=True)
            img_path = output_dir / f"ranking_{time.time_ns()}.png"
            img.save(img_path)
            return str(img_path)

        except Exception as e:
            logger.error(f"渲染排行榜图片失败: {e}", exc_info=True)
            return None
    def _get_text_height(self, draw: ImageDraw.ImageDraw, text: str, font: ImageFont.FreeTypeFont) -> int:
        """获取文本高度"""
        try:
            bbox = draw.textbbox((0, 0), text, font=font)
            return bbox[3] - bbox[1]
        except AttributeError:
            return font.getsize(text)[1]


class DatabaseManager:
    """数据库管理器"""
    
    def __init__(self, db_path: str):
        self.db_path = db_path
        self._user_rank_cache: Dict[int, Tuple[int, float]] = {}
        self._cache_ttl = 60
        self._init_db()
    
    def _init_db(self):
        """初始化数据库"""
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS user_stats (
                    user_id TEXT PRIMARY KEY,
                    user_name TEXT,
                    custom_name TEXT,
                    score INTEGER DEFAULT 0,
                    attempts INTEGER DEFAULT 0,
                    correct_attempts INTEGER DEFAULT 0,
                    last_play_date TEXT,
                    daily_plays INTEGER DEFAULT 0
                )
            """)
            cursor.execute("CREATE INDEX IF NOT EXISTS idx_score ON user_stats(score DESC)")
            cursor.execute("PRAGMA table_info(user_stats)")
            columns = [column[1] for column in cursor.fetchall()]
            if 'custom_name' not in columns:
                cursor.execute("ALTER TABLE user_stats ADD COLUMN custom_name TEXT")
            if 'platform_name' not in columns:
                cursor.execute(
                    "ALTER TABLE user_stats ADD COLUMN platform_name TEXT NOT NULL DEFAULT 'aiocqhttp'"
                )
            cursor.execute("""
                CREATE TABLE IF NOT EXISTS account_bindings (
                    official_platform TEXT NOT NULL,
                    official_user_id TEXT NOT NULL,
                    qq_user_id TEXT NOT NULL,
                    bound_at TEXT NOT NULL,
                    PRIMARY KEY (official_platform, official_user_id)
                )
            """)
            legacy_rows = cursor.execute(
                "SELECT user_id FROM user_stats WHERE platform_name = ?",
                (DEFAULT_PLATFORM_NAME,),
            ).fetchall()
            for (legacy_user_id,) in legacy_rows:
                if OFFICIAL_QID_PATTERN.fullmatch(str(legacy_user_id)):
                    cursor.execute(
                        "UPDATE user_stats SET platform_name = ? WHERE user_id = ?",
                        (OFFICIAL_PLATFORM_NAME, legacy_user_id),
                    )
            conn.commit()
    
    @contextmanager
    def _get_connection(self) -> Generator[sqlite3.Connection, None, None]:
        """获取数据库连接的上下文管理器"""
        conn = sqlite3.connect(self.db_path, timeout=30.0)
        try:
            yield conn
        finally:
            conn.close()
    
    def _invalidate_rank_cache(self):
        """清除排名缓存"""
        self._user_rank_cache.clear()

    def resolve_user_id(self, platform_name: str, user_id: str) -> str:
        """将已绑定的官方机器人 QID 解析为普通 QQ 号。"""
        if str(platform_name or DEFAULT_PLATFORM_NAME).strip().lower() != OFFICIAL_PLATFORM_NAME:
            return str(user_id)
        with self._get_connection() as conn:
            row = conn.execute(
                "SELECT qq_user_id FROM account_bindings "
                "WHERE official_platform = ? AND official_user_id = ?",
                (OFFICIAL_PLATFORM_NAME, str(user_id)),
            ).fetchone()
        return str(row[0]) if row else str(user_id)

    def bind_official_account(self, official_user_id: str, qq_user_id: str) -> bool:
        """合并官方机器人账号在本插件内的历史数据并记录绑定关系。"""
        source_id = str(official_user_id).strip()
        target_id = str(qq_user_id).strip()
        if not source_id or not re.fullmatch(r"\d{5,12}", target_id) or source_id == target_id:
            return False

        with self._get_connection() as conn:
            try:
                conn.execute("BEGIN IMMEDIATE")
                if conn.execute(
                    "SELECT 1 FROM account_bindings WHERE official_platform = ? AND official_user_id = ?",
                    (OFFICIAL_PLATFORM_NAME, source_id),
                ).fetchone():
                    conn.rollback()
                    return False

                fields = "user_name, custom_name, score, attempts, correct_attempts, last_play_date, daily_plays"
                source_row = conn.execute(
                    f"SELECT {fields} FROM user_stats WHERE user_id = ? AND platform_name = ?",
                    (source_id, OFFICIAL_PLATFORM_NAME),
                ).fetchone()
                target_row = conn.execute(
                    f"SELECT {fields} FROM user_stats WHERE user_id = ? AND platform_name = ?",
                    (target_id, DEFAULT_PLATFORM_NAME),
                ).fetchone()

                if source_row and target_row:
                    source_name, source_custom, source_score, source_attempts, source_correct, source_date, source_daily = source_row
                    target_name, target_custom, target_score, target_attempts, target_correct, target_date, target_daily = target_row
                    source_date = source_date or ""
                    target_date = target_date or ""
                    if source_date == target_date:
                        merged_date = source_date or None
                        merged_daily = int(source_daily or 0) + int(target_daily or 0)
                    elif source_date > target_date:
                        merged_date = source_date or None
                        merged_daily = int(source_daily or 0)
                    else:
                        merged_date = target_date or None
                        merged_daily = int(target_daily or 0)
                    conn.execute(
                        "UPDATE user_stats SET user_name = ?, custom_name = ?, score = ?, attempts = ?, "
                        "correct_attempts = ?, last_play_date = ?, daily_plays = ? WHERE user_id = ? AND platform_name = ?",
                        (
                            target_name or source_name,
                            target_custom or source_custom,
                            int(target_score or 0) + int(source_score or 0),
                            int(target_attempts or 0) + int(source_attempts or 0),
                            int(target_correct or 0) + int(source_correct or 0),
                            merged_date,
                            merged_daily,
                            target_id,
                            DEFAULT_PLATFORM_NAME,
                        ),
                    )
                elif source_row:
                    source_name, source_custom, source_score, source_attempts, source_correct, source_date, source_daily = source_row
                    conn.execute(
                        "UPDATE user_stats SET user_id = ?, platform_name = ? WHERE user_id = ? AND platform_name = ?",
                        (target_id, DEFAULT_PLATFORM_NAME, source_id, OFFICIAL_PLATFORM_NAME),
                    )

                conn.execute(
                    "INSERT INTO account_bindings (official_platform, official_user_id, qq_user_id, bound_at) VALUES (?, ?, ?, ?)",
                    (OFFICIAL_PLATFORM_NAME, source_id, target_id, time.strftime("%Y-%m-%d %H:%M:%S")),
                )
                if source_row and target_row:
                    conn.execute(
                        "DELETE FROM user_stats WHERE user_id = ? AND platform_name = ?",
                        (source_id, OFFICIAL_PLATFORM_NAME),
                    )
                conn.commit()
                self._invalidate_rank_cache()
                return True
            except Exception as exc:
                conn.rollback()
                logger.error(f"绑定歌词猜曲官方机器人账号失败: {exc}", exc_info=True)
                return False
    
    def get_user_stats(self, user_id: str, platform_name: str = DEFAULT_PLATFORM_NAME) -> Optional[Tuple]:
        """获取用户统计"""
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT score, attempts, correct_attempts, last_play_date, daily_plays "
                "FROM user_stats WHERE user_id = ? AND platform_name = ?",
                (user_id, platform_name)
            )
            return cursor.fetchone()
    
    def get_user_rank(self, score: int, platform_name: str = DEFAULT_PLATFORM_NAME) -> int:
        """获取用户排名（带缓存）"""
        current_time = time.time()
        
        # 排名是本插件内的统一排行榜；平台字段只负责定位当前用户记录。
        cache_key = score
        if cache_key in self._user_rank_cache:
            cached_rank, cached_time = self._user_rank_cache[cache_key]
            if current_time - cached_time < self._cache_ttl:
                return cached_rank
        
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT COUNT(*) FROM user_stats WHERE score > ?",
                (score,),
            )
            rank = cursor.fetchone()[0] + 1
            
            self._user_rank_cache[cache_key] = (rank, current_time)
            return rank
    
    def update_user_game_result(
        self,
        user_id: str,
        user_name: str,
        score: int,
        correct: bool,
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ):
        """原子性更新用户游戏结果（使用纯SQL原子操作）"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                """INSERT INTO user_stats (user_id, user_name, platform_name, score, attempts, correct_attempts, last_play_date, daily_plays)
                   VALUES (?, ?, ?, ?, 1, ?, ?, 1)
                   ON CONFLICT(user_id) DO UPDATE SET
                       score = score + excluded.score,
                       attempts = attempts + 1,
                       correct_attempts = correct_attempts + excluded.correct_attempts,
                       user_name = excluded.user_name,
                       last_play_date = excluded.last_play_date,
                       daily_plays = CASE WHEN last_play_date = excluded.last_play_date THEN daily_plays + 1 ELSE 1 END
                """,
                    (user_id, user_name, platform_name, score, 1 if correct else 0, today)
            )
            conn.commit()
            self._invalidate_rank_cache()
    
    def update_user_play(
        self,
        user_id: str,
        user_name: str,
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ):
        """更新用户游戏记录"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT last_play_date, daily_plays FROM user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (user_id, platform_name),
            )
            user_data = cursor.fetchone()
            
            if user_data:
                last_play_date, daily_plays = user_data
                new_daily_plays = daily_plays + 1 if last_play_date == today else 1
                cursor.execute(
                    "UPDATE user_stats SET user_name = ?, platform_name = ?, last_play_date = ?, daily_plays = ? "
                    "WHERE user_id = ? AND platform_name = ?",
                    (user_name, platform_name, today, new_daily_plays, user_id, platform_name)
                )
            else:
                cursor.execute(
                    "INSERT INTO user_stats (user_id, user_name, platform_name, last_play_date, daily_plays) VALUES (?, ?, ?, ?, ?)",
                    (user_id, user_name, platform_name, today, 1)
                )
            conn.commit()
    
    def update_user_score(
        self,
        user_id: str,
        user_name: str,
        score: int,
        correct: bool,
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ):
        """更新用户分数"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT score, attempts, correct_attempts FROM user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (user_id, platform_name),
            )
            user_data = cursor.fetchone()
            
            if user_data:
                new_score = user_data[0] + score
                new_attempts = user_data[1] + 1
                new_correct = user_data[2] + (1 if correct else 0)
                cursor.execute(
                    "UPDATE user_stats SET score = ?, attempts = ?, correct_attempts = ?, user_name = ?, platform_name = ? "
                    "WHERE user_id = ? AND platform_name = ?",
                    (new_score, new_attempts, new_correct, user_name, platform_name, user_id, platform_name)
                )
            else:
                cursor.execute(
                    "INSERT INTO user_stats (user_id, user_name, platform_name, score, attempts, correct_attempts, last_play_date, daily_plays) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                    (user_id, user_name, platform_name, score, 1, 1 if correct else 0, today, 0)
                )
            conn.commit()
    
    def can_play_today(
        self,
        user_id: str,
        daily_limit: int,
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ) -> bool:
        """检查用户今日是否还能游戏"""
        if daily_limit == -1:
            return True
        
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT daily_plays, last_play_date FROM user_stats "
                "WHERE user_id = ? AND platform_name = ?",
                (user_id, platform_name),
            )
            user_data = cursor.fetchone()
            if user_data and user_data[1] == today:
                return user_data[0] < daily_limit
            return True
    
    def set_custom_name(
        self,
        user_id: str,
        user_name: str,
        custom_name: Optional[str],
        platform_name: str = DEFAULT_PLATFORM_NAME,
    ) -> bool:
        """设置自定义名称，返回是否成功"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT user_id FROM user_stats WHERE user_id = ? AND platform_name = ?",
                (user_id, platform_name),
            )
            exists = cursor.fetchone() is not None
            
            if custom_name:
                if exists:
                    cursor.execute(
                        "UPDATE user_stats SET custom_name = ? WHERE user_id = ? AND platform_name = ?",
                        (custom_name, user_id, platform_name),
                    )
                else:
                    cursor.execute(
                    "INSERT INTO user_stats (user_id, user_name, custom_name, platform_name, score, attempts, correct_attempts, last_play_date, daily_plays) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
                        (user_id, user_name, custom_name, platform_name, 0, 0, 0, today, 0)
                    )
            elif exists:
                cursor.execute(
                    "UPDATE user_stats SET custom_name = NULL WHERE user_id = ? AND platform_name = ?",
                    (user_id, platform_name),
                )
            else:
                return False
            
            conn.commit()
            return True
    
    def get_ranking(self, limit: int) -> List[Tuple]:
        """获取排行榜数据"""
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT user_id, user_name, custom_name, score, attempts, correct_attempts, "
                "CASE WHEN platform_name = ? AND NOT EXISTS ("
                "SELECT 1 FROM account_bindings AS b WHERE b.official_platform = user_stats.platform_name "
                "AND b.official_user_id = user_stats.user_id) THEN 1 ELSE 0 END "
                "FROM user_stats ORDER BY score DESC LIMIT ?",
                (OFFICIAL_PLATFORM_NAME, limit)
            )
            return cursor.fetchall()


@register(PLUGIN_NAME, PLUGIN_AUTHOR, PLUGIN_DESCRIPTION, PLUGIN_VERSION, PLUGIN_REPO_URL)
class GuessLyricsPlugin(Star):
    """PJSK 歌词猜曲插件主类"""
    
    def __init__(self, context: Context, config: 'AstrBotConfig'):
        super().__init__(context)
        self.config = config
        
        self.plugin_dir = Path(os.path.dirname(__file__))
        self.resources_dir = self.plugin_dir / "res"
        
        self.plugin_data_path = StarTools.get_data_dir(self.name)
        self.lyrics_dir = self.resources_dir / "lyrics"
        self.jacket_cache_dir = self.plugin_data_path / "jacket_cache"
        self.output_dir = self.plugin_data_path / "output"
        self.local_data_dir = self.plugin_data_path / "local_data"
        
        self._ensure_directories()
        
        self.db_path = str(self.plugin_data_path / "guess_lyrics_data.db")
        self.db = DatabaseManager(self.db_path)
        
        songs_file = self.resources_dir / "songs.json"
        aliases_file = self.resources_dir / "aliases.json"
        self.data_manager = LocalDataManager(
            self.local_data_dir, 
            songs_file if songs_file.exists() else None,
            aliases_file if aliases_file.exists() else None
        )
        
        self.cloud_jacket_loader = CloudJacketLoader(self.jacket_cache_dir, self.config)
        
        font_path = self.resources_dir / "font.ttf"
        self.image_generator = ImageGenerator(font_path if font_path.exists() else None)
        
        self.active_game_sessions: set = set()
        self.game_sessions: Dict[str, GameSession] = LRUDict(max_size=Config.MAX_SESSION_CACHE_SIZE)
        self.session_locks: Dict[str, asyncio.Lock] = LRUDict(max_size=Config.MAX_SESSION_CACHE_SIZE)
        self.last_game_end_time: Dict[str, float] = LRUDict(max_size=Config.MAX_SESSION_CACHE_SIZE)
        self._lock_creation_lock = asyncio.Lock()
        self.song_manager: Optional[LocalSongManager] = None
        self.data_initialized = False

        self.auto_sessions: set = set()
        self.auto_stop_events: Dict[str, asyncio.Event] = LRUDict(max_size=Config.MAX_SESSION_CACHE_SIZE)

        # --- 题库服务器偏好与 master 数据自动同步 ---
        self.server_prefs_path = self.plugin_data_path / "session_servers.json"
        self.server_prefs: dict = self._load_server_prefs()
        self.master_data = MasterDataService(
            self.plugin_data_path,
            update_interval_hours=int(config.get("update_interval_hours", 24)),
        )
        self.master_data.on_songs_updated = self._on_master_updated

        self._cleanup_output_dir()
        self._cleanup_task = asyncio.create_task(self._periodic_cleanup())
        self._init_task = asyncio.create_task(self._initialize_data())
        self._master_task = asyncio.create_task(self._start_master_data())

        logger.info(f"PJSK Guess Lyrics Plugin initialized (v{PLUGIN_VERSION})")

    # --- 题库服务器与 master 数据同步 ---

    async def _start_master_data(self):
        """启动歌曲题库自动同步服务。"""
        try:
            await self.master_data.start()
        except Exception as e:
            logger.error(f"题库同步服务启动失败: {e}", exc_info=True)

    def _load_server_prefs(self) -> dict:
        try:
            if self.server_prefs_path.exists():
                return json.loads(self.server_prefs_path.read_text(encoding="utf-8"))
        except Exception as e:
            logger.warning(f"加载题库服务器偏好失败: {e}")
        return {}

    def _save_server_prefs(self):
        try:
            self.server_prefs_path.write_text(
                json.dumps(self.server_prefs, ensure_ascii=False, indent=1),
                encoding="utf-8",
            )
        except Exception as e:
            logger.warning(f"保存题库服务器偏好失败: {e}")

    def _server_for_session(self, session_id: str) -> str:
        saved = self.server_prefs.get(session_id)
        if saved in (SERVER_JP, SERVER_SC):
            return saved
        default = str(self.config.get("default_server", SERVER_JP)).lower()
        return SERVER_SC if default == SERVER_SC else SERVER_JP

    def _on_master_updated(self):
        """master 数据更新后重建歌名/翻译/别名映射、歌曲管理器与各服曲池。"""
        try:
            union: List[dict] = []
            seen: set = set()
            for server in (SERVER_JP, SERVER_SC):
                for song in self.master_data.get_songs(server):
                    if song.get("id") not in seen:
                        seen.add(song.get("id"))
                        union.append(song)
            if not union:
                return
            self.data_manager.apply_master_songs(union, replace=True)
            self.song_manager = LocalSongManager(
                self.lyrics_dir,
                self.data_manager,
                self.cloud_jacket_loader,
            )
            self.data_initialized = True
            logger.info(f"[歌词猜曲] 题库已随 master 数据更新，当前本地可猜歌曲 {len(self.song_manager.songs)} 首。")
        except Exception as e:
            logger.error(f"应用 master 题库数据失败: {e}", exc_info=True)

    def _get_pool_for_session(self, session_id: str) -> List[SongInfo]:
        """获取会话当前服务器的曲池（本地 lrc 歌词 ∩ 对应服务器 master 曲目）。"""
        server = self._server_for_session(session_id)
        if self.song_manager is None:
            return []
        master_ids = {s.get("id") for s in self.master_data.get_songs(server)}
        if not master_ids:
            # master 题库未就绪：回退全部本地歌曲
            return self.song_manager.songs
        return [s for s in self.song_manager.songs if s.music_id in master_ids]

    # --- 官机 markdown 机制（与 PJSK Wordle 一致） ---

    def _build_connect_link(self, command: str, self_id: str, show: Optional[str] = None) -> str:
        """按配置模板生成 markdown 格式的指令连接。

        默认使用 QQ 官方机器人 markdown 消息的参数指令标签
        <qqbot-cmd-input>：点击后在聊天框填入指令，QQ 客户端发送时会自动 @ 官方机器人。
        show 为展示名（默认与指令一致）。可通过 connect_link_template 配置项适配环境，
        模板显式置空则退回纯文本"（连接：@官机 指令）"。
        """
        template = self.config.get("connect_link_template")
        if template is None or any(marker in str(template) for marker in _LEGACY_TEMPLATE_MARKERS):
            template = DEFAULT_CONNECT_TEMPLATE
        template = str(template).strip()
        if not template:
            return f"（连接：@{self_id} {command}）"
        display = show or command
        at_text = f"@{self_id} {command}"
        return template.format(
            name=command,
            command=command,
            self_id=self_id,
            at_text=at_text,
            encoded_command=quote(command, safe=""),
            encoded_name=quote(display, safe=""),
            encoded_at_text=quote(at_text, safe=""),
        )

    def _get_official_connect_id(self, event: AstrMessageEvent) -> str:
        """返回官机连接模板的兼容 ID；默认 qqbot-cmd-input 不依赖该值。"""
        return self._get_official_self_id(event) or "qq_official"

    def _get_official_self_id(self, event: AstrMessageEvent) -> str:
        return str(getattr(event.message_obj, "self_id", "") or "").strip()

    async def _send_markdown_text(self, event: AstrMessageEvent, text: str):
        """以 QQ 官方机器人 markdown 消息发送纯文本（含连接标签）。"""
        result = event.make_result()
        result.chain = [Comp.Plain(text)]
        result.use_markdown(True)
        await event.send(result)

    def _get_quick_entries(self) -> list[str]:
        """读取快捷入口配置；若列表为空则不显示快捷入口。"""
        entries = self.config.get("quick_entries")
        if not entries:
            return []
        cleaned = [str(x).strip() for x in entries if str(x).strip()]
        wordle = "Wordle"
        if wordle in cleaned:
            cleaned = [x for x in cleaned if x != wordle] + [wordle]
        return cleaned

    def _build_server_footer(self, event: AstrMessageEvent, server: str) -> List[str]:
        """构建结算消息的题库服务器尾部：官机附 markdown 连接入口与快捷入口，普通 QQ 仅提示指令。"""
        other = SERVER_SC if server == SERVER_JP else SERVER_JP
        switch_cmd = SWITCH_COMMANDS[server]
        connect_switch_cmd = CONNECT_SWITCH_COMMANDS[server]
        lines = [f"本局题库服务器：{SERVER_LABELS[server]}"]

        if self._get_event_platform_name(event) == OFFICIAL_PLATFORM_NAME:
            self_id = self._get_official_connect_id(event)
            if self_id:
                lines.append(self._build_connect_link(connect_switch_cmd, self_id))
                account_links = ["歌词猜曲绑定QQ", "歌词猜曲个人分数", "歌词猜曲排行榜"]
                lines.append(
                    "  ".join(self._build_connect_link(name, self_id) for name in account_links)
                )
                entries = self._get_quick_entries()
                if entries:
                    lines.append("快捷入口：")
                    lines.append(
                        "  ".join(self._build_connect_link(name, self_id) for name in entries)
                    )
                return lines
        lines.append(f"你可以使用{switch_cmd}指令切换{SERVER_LABELS[other]}题库。")
        return lines

    async def _switch_server(self, event: AstrMessageEvent, server: str):
        """切换当前会话的题库服务器。"""
        session_id = event.unified_msg_origin
        if session_id in self.active_game_sessions:
            await event.send(event.plain_result("本局游戏还在进行中，结束后再切换题库服务器吧。"))
            return
        current = self._server_for_session(session_id)
        if current == server:
            await event.send(event.plain_result(f"当前题库已经是{SERVER_LABELS[server]}题库了。"))
            return
        self.server_prefs[session_id] = server
        self._save_server_prefs()
        count = len(self._get_pool_for_session(session_id))
        version = self.master_data.get_version(server)
        await event.send(
            event.plain_result(
                f"已切换为{SERVER_BADGES[server]}（共 {count} 首，版本 {version}），下一局生效。"
            )
        )

    @staticmethod
    def _get_event_platform_name(event: AstrMessageEvent) -> str:
        getter = getattr(event, "get_platform_name", None)
        try:
            platform_name = getter() if callable(getter) else DEFAULT_PLATFORM_NAME
        except Exception:
            platform_name = DEFAULT_PLATFORM_NAME
        return str(platform_name or DEFAULT_PLATFORM_NAME).strip().lower()

    def _is_qq_official_event(self, event: AstrMessageEvent) -> bool:
        return self._get_event_platform_name(event) == OFFICIAL_PLATFORM_NAME

    def _get_account_identity(self, event: AstrMessageEvent) -> tuple[str, str]:
        platform_name = self._get_event_platform_name(event)
        raw_user_id = str(event.get_sender_id())
        resolved_user_id = self.db.resolve_user_id(platform_name, raw_user_id)
        if resolved_user_id != raw_user_id:
            return str(resolved_user_id), DEFAULT_PLATFORM_NAME
        return raw_user_id, platform_name

    def _is_event_user_blacklisted(self, event: AstrMessageEvent, canonical_user_id: Optional[str] = None) -> bool:
        raw_user_id = str(event.get_sender_id())
        return self._is_user_blacklisted(raw_user_id) or (
            canonical_user_id is not None and self._is_user_blacklisted(canonical_user_id)
        )

    @staticmethod
    def _build_binding_confirmation_message(qq_user_id: str) -> str:
        return (
            f"你确认将账号绑定至  {qq_user_id} ？官方机作答的分数将迁移至该账号。\n"
            "发送“确认”将开始绑定。发送“取消”将取消绑定。"
        )
    
    def _ensure_directories(self):
        """确保必要的目录存在"""
        os.makedirs(self.lyrics_dir, exist_ok=True)
        os.makedirs(self.jacket_cache_dir, exist_ok=True)
        os.makedirs(self.output_dir, exist_ok=True)
        os.makedirs(self.local_data_dir, exist_ok=True)
    
    async def _initialize_data(self):
        """初始化数据"""
        try:
            self.song_manager = LocalSongManager(
                self.lyrics_dir, 
                self.data_manager,
                self.cloud_jacket_loader
            )
            logger.info(
                f"Data initialization complete. "
                f"{len(self.data_manager.cn_map)} translations, "
                f"{len(self.song_manager.songs)} local songs"
            )
            self.data_initialized = True
        except (IOError, OSError, ValueError, KeyError) as e:
            logger.error(f"Failed to initialize data: {e}")
    
    def _cleanup_output_dir(self):
        """清理旧输出图片"""
        if not self.output_dir.exists():
            return
        
        now = time.time()
        try:
            for file_path in self.output_dir.iterdir():
                if file_path.is_file() and (now - file_path.stat().st_mtime) > Config.MAX_AGE_SECONDS:
                    file_path.unlink()
        except OSError as e:
            logger.error(f"Cleanup error: {e}")
    
    async def _periodic_cleanup(self):
        """定期清理任务"""
        while True:
            await asyncio.sleep(Config.CLEANUP_INTERVAL)
            self._cleanup_output_dir()
    
    def _is_group_allowed(self, event: AstrMessageEvent) -> bool:
        """检查群组是否在白名单中"""
        whitelist = {str(x) for x in self.config.get("group_whitelist", [])}
        if not whitelist:
            return True
        group_id = event.get_group_id()
        return bool(group_id and str(group_id) in whitelist)

    def _get_whitelist_reject_message(self) -> Optional[str]:
        """获取白名单拒绝提示信息"""
        msg = self.config.get("whitelist_reject_message", "")
        if msg and msg.strip():
            return msg.strip()
        return None
    
    def _is_user_blacklisted(self, user_id: str) -> bool:
        """检查用户是否在黑名单中"""
        return str(user_id) in {str(x) for x in self.config.get("blacklist", [])}
    
    def _is_super_user(self, user_id: str) -> bool:
        """检查是否为超级用户"""
        super_users = {str(x) for x in self.config.get("super_users", [])}
        if not super_users:
            return False
        return str(user_id) in super_users
    
    def _get_cooldown_remaining(self, session_id: str) -> float:
        """获取冷却剩余时间"""
        cooldown = self.config.get("game_cooldown_seconds", Config.DEFAULT_COOLDOWN)
        last_end_time = self.last_game_end_time.get(session_id, 0)
        return max(0, cooldown - (time.time() - last_end_time))
    
    async def _get_session_lock(self, session_id: str) -> asyncio.Lock:
        """线程安全地获取会话锁"""
        async with self._lock_creation_lock:
            if session_id not in self.session_locks:
                self.session_locks[session_id] = asyncio.Lock()
            return self.session_locks[session_id]
    
    def start_new_game(self, pool: Optional[List[SongInfo]] = None) -> Optional[GameData]:
        """开始新游戏（可指定题库曲池，默认全部本地歌曲）"""
        if not self.song_manager:
            logger.error("Song manager not initialized")
            return None

        for _ in range(Config.DEFAULT_MAX_ATTEMPTS):
            correct_song = self.song_manager.get_random_song(pool)
            if not correct_song:
                logger.error("No songs available for game")
                return None

            lyrics = LrcParser.parse(correct_song.lrc_path)
            if not lyrics:
                logger.warning(f"Failed to parse lyrics for song: {correct_song.display_name}, retrying...")
                continue

            lyrics_snippet = self._extract_random_lyrics(lyrics, Config.LYRICS_LINES_COUNT)
            options = self.song_manager.get_random_options(correct_song, songs=pool)
            correct_index = options.index(correct_song)
            
            return GameData(
                correct_song=correct_song,
                lyrics_snippet=lyrics_snippet,
                options=options,
                correct_index=correct_index
            )
        
        logger.error("Failed to start game after multiple attempts")
        return None
    
    def _extract_random_lyrics(self, lyrics: List[str], count: int) -> List[str]:
        """
        随机选取连续的歌词行
        
        Args:
            lyrics: 歌词列表
            count: 需要选取的行数
            
        Returns:
            连续的歌词行列表
        """
        if not lyrics:
            return []
        
        if len(lyrics) <= count:
            return lyrics
        
        max_start = len(lyrics) - count
        start_index = random.randint(0, max_start)
        
        return lyrics[start_index:start_index + count]
    
    async def _run_game_impl(self, event: AstrMessageEvent, auto_mode: bool = False):
        """歌词猜曲游戏核心逻辑"""
        if not self.data_initialized:
            yield event.plain_result("数据正在初始化中，请稍后再试...")
            return

        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return
        
        user_id, platform_name = self._get_account_identity(event)
        if self._is_event_user_blacklisted(event, user_id):
            yield event.plain_result("抱歉，你已被禁止使用此功能 😔")
            return
        
        session_id = event.unified_msg_origin
        round_server = self._server_for_session(session_id)
        is_official_round = self._get_event_platform_name(event) == OFFICIAL_PLATFORM_NAME
        first_round = True
        no_answer_streak = 0
        
        while True:
            session_lock = await self._get_session_lock(session_id)
            
            async with session_lock:
                if session_id in self.active_game_sessions:
                    if first_round:
                        yield event.plain_result("当前已经有一个游戏在进行中啦~ 等它结束后再来玩吧！")
                        return
                    else:
                        yield event.plain_result("检测到有人开始了新游戏，自动模式已停止。")
                        break
                
                if not first_round and not auto_mode:
                    break
                
                # 冷却检查：自动模式下跳过（每轮之间由自动模式自己控制间隔）
                if not auto_mode or first_round:
                    cooldown_remaining = self._get_cooldown_remaining(session_id)
                    if cooldown_remaining > 0:
                        time_display = f"{cooldown_remaining:.1f}" if cooldown_remaining < 1 else str(int(cooldown_remaining))
                        yield event.plain_result(f"让我们休息一下吧！{time_display}秒后再来玩哦~ 😊")
                        return
                
                daily_limit = self.config.get("daily_play_limit", Config.DEFAULT_DAILY_LIMIT)
                if not self.db.can_play_today(user_id, daily_limit, platform_name):
                    if auto_mode:
                        yield event.plain_result(f"今天的游戏次数已经用完啦~ 自动模式已停止！每天最多可以玩{daily_limit}次哦~ ✨")
                        break
                    else:
                        yield event.plain_result(f"今天的游戏次数已经用完啦~ 明天再来玩吧！每天最多可以玩{daily_limit}次哦~ ✨")
                        return
                
                self.active_game_sessions.add(session_id)
            
            try:
                game_data = self.start_new_game(self._get_pool_for_session(session_id))
                if not game_data:
                    yield event.plain_result("开始游戏失败，可能存在歌词文件损坏或格式不正确，请联系管理员检查日志。")
                    break
                
                max_attempts_per_player = max(1, int(self.config.get("max_attempts_per_player", 1)))
                max_attempts_total = max(1, int(self.config.get("max_attempts_total", 5)))
                lyrics_display_mode = str(self.config.get("lyrics_display_mode", "image")).lower()
                
                if lyrics_display_mode not in ["image", "text"]:
                    logger.warning(f"Invalid lyrics_display_mode '{lyrics_display_mode}', defaulting to 'image'")
                    lyrics_display_mode = "image"
                
                async def load_single_jacket(opt):
                    """加载单个曲绘"""
                    jacket_img = await asyncio.to_thread(
                        self.song_manager.get_jacket_image, opt, round_server
                    )
                    if jacket_img:
                        temp_path = self.output_dir / f"temp_jacket_{opt.music_id}_{time.time_ns()}.png"
                        jacket_img.save(temp_path)
                        return str(temp_path)
                    return None
                
                jacket_tasks = [load_single_jacket(opt) for opt in game_data.options]
                jacket_paths = await asyncio.gather(*jacket_tasks)
                
                options_with_images = [
                    (i + 1, opt.cn_title, opt.original_name, jacket_paths[i])
                    for i, opt in enumerate(game_data.options)
                ]
                
                options_img = await asyncio.to_thread(
                    self.image_generator.create_options_image, options_with_images
                )
                if not options_img:
                    yield event.plain_result("生成选项图片时出错，请稍后再试。")
                    break
                
                options_img_path = self.image_generator.save_image(options_img, self.output_dir, "options")
                
                if not options_img_path:
                    yield event.plain_result("保存图片时出错，请稍后再试。")
                    break
                
                correct_display_name = self.song_manager.get_display_name(game_data.correct_song)
                logger.info(f"[歌词猜曲插件] 新游戏开始. 答案: {correct_display_name}, 模式: {lyrics_display_mode}, 自动模式: {auto_mode}")
                
                game_session = GameSession(game_data=game_data)
                self.game_sessions[session_id] = game_session
                
                timeout_seconds = self.config.get("answer_timeout", Config.DEFAULT_TIMEOUT)
                
                await asyncio.to_thread(
                    self.db.update_user_play,
                    user_id,
                    event.get_sender_name(),
                    platform_name,
                )
                
                intro_tail = (
                    f"每位玩家最多可回答{max_attempts_per_player}次，全局共{max_attempts_total}次机会\n\n"
                )
                in_auto_mode = session_id in self.auto_sessions
                official_self_id = self._get_official_connect_id(event) if is_official_round else ""
                # 自动模式不出现 markdown 按钮；仅手动局的官机消息附连接
                use_markdown_intro = (not in_auto_mode) and bool(official_self_id)
                if is_official_round:
                    if in_auto_mode:
                        quit_tail = (
                            "\n"
                            + self._build_connect_link("退出本局", official_self_id)
                            + "  "
                            + self._build_connect_link("退出自动模式", official_self_id)
                        )
                    else:
                        quit_tail = (
                            "\n"
                            + self._build_connect_link("退出本局", official_self_id)
                        )
                elif in_auto_mode:
                    quit_tail = "\n发送「退出」可结束自动模式，发送「退出本局」可提前结束这一局。"
                else:
                    quit_tail = "\n发送「退出本局」可提前结束这一局。"
                if is_official_round:
                    if lyrics_display_mode == "text":
                        lyrics_text = "\n".join(game_data.lyrics_snippet)
                        intro_text = (
                            f"请在{timeout_seconds}秒内输入数字(1-10)选择正确答案~\n"
                            f"{intro_tail}"
                            f"【歌词片段】\n{lyrics_text}\n\n"
                            f"{quit_tail}"
                        )
                        try:
                            await self._send_markdown_text(event, intro_text)
                            yield event.chain_result([
                                Comp.Image(file=options_img_path)
                            ])
                        except Exception as e:
                            logger.error(f"发送开局消息失败: {e}", exc_info=True)
                            yield event.plain_result("发送开局消息时出错，游戏中断。")
                            break
                    else:
                        lyrics_img = await asyncio.to_thread(
                            self.image_generator.create_lyrics_image, game_data.lyrics_snippet
                        )
                        if not lyrics_img:
                            yield event.plain_result("生成歌词图片时出错，请稍后再试。")
                            break

                        lyrics_img_path = self.image_generator.save_image(lyrics_img, self.output_dir, "lyrics")
                        if not lyrics_img_path:
                            yield event.plain_result("保存图片时出错，请稍后再试。")
                            break

                        intro_text = (
                            f"请在{timeout_seconds}秒内输入数字(1-10)选择正确答案~\n"
                            f"{intro_tail}"
                            f"歌词片段：\n"
                            f"{quit_tail}"
                        )
                        try:
                            await self._send_markdown_text(event, intro_text)
                            yield event.chain_result([
                                Comp.Image(file=lyrics_img_path),
                                Comp.Image(file=options_img_path)
                            ])
                        except Exception as e:
                            logger.error(f"发送开局消息失败: {e}", exc_info=True)
                            yield event.plain_result("发送开局消息时出错，游戏中断。")
                            break
                elif lyrics_display_mode == "text":
                    lyrics_text = "\n".join(game_data.lyrics_snippet)
                    intro_text = (
                        f"请在{timeout_seconds}秒内输入数字(1-10)选择正确答案~\n"
                        f"{intro_tail}"
                        f"【歌词片段】\n{lyrics_text}\n\n"
                        f"{quit_tail}"
                    )

                    yield event.chain_result([
                        Comp.Plain(intro_text),
                        Comp.Image(file=options_img_path)
                    ])
                else:
                    lyrics_img = await asyncio.to_thread(
                        self.image_generator.create_lyrics_image, game_data.lyrics_snippet
                    )
                    if not lyrics_img:
                        yield event.plain_result("生成歌词图片时出错，请稍后再试。")
                        break

                    lyrics_img_path = self.image_generator.save_image(lyrics_img, self.output_dir, "lyrics")
                    if not lyrics_img_path:
                        yield event.plain_result("保存图片时出错，请稍后再试。")
                        break

                    intro_text = (
                        f"请在{timeout_seconds}秒内输入数字(1-10)选择正确答案~\n"
                        f"{intro_tail}"
                        f"歌词片段：\n"
                        f"{quit_tail}"
                    )

                    yield event.chain_result([
                        Comp.Plain(intro_text),
                        Comp.Image(file=lyrics_img_path),
                        Comp.Image(file=options_img_path)
                    ])
                answered_correctly = False
                final_answer_user_id = None
                final_answer_user_name = None
                final_answer_platform_name = None
                final_answer_index = None
                all_answers_history = []
                winners_list = []
                first_correct_time = None
                reward_valid_time = self.config.get("reward_valid_time", 0)
                quit_ended_round = False

                logger.info(f"[歌词猜曲] 奖励有效时间配置: {reward_valid_time}秒")

                @session_waiter(timeout=timeout_seconds)
                async def answer_waiter(controller: SessionController, answer_event: AstrMessageEvent):
                    nonlocal answered_correctly, final_answer_user_id, final_answer_user_name, final_answer_platform_name, final_answer_index
                    nonlocal all_answers_history, first_correct_time, winners_list, quit_ended_round

                    answer_user_id, answer_platform_name = self._get_account_identity(answer_event)
                    if self._is_event_user_blacklisted(answer_event, answer_user_id):
                        return
                    answer_text = answer_event.message_str.strip()

                    # 仅退出本局：只在游玩时生效，立即结束当前对局（不影响自动模式）
                    if answer_text in ["仅退出本局", "退出本局"]:
                        quit_ended_round = True
                        controller.stop()
                        return

                    # 退出自动模式：任何时候可触发，本局继续、自动模式停止
                    if answer_text in ["退出自动模式", "退出"] and session_id in self.auto_sessions:
                        self.auto_sessions.discard(session_id)
                        if session_id in self.auto_stop_events:
                            self.auto_stop_events[session_id].set()
                        await answer_event.send(answer_event.plain_result("已退出自动模式，本局结束后将不再自动开局。"))
                        return
                    
                    if not answer_text.isdigit():
                        return
                    
                    try:
                        selected_num = int(answer_text)
                        if not (1 <= selected_num <= 10):
                            return
                    except ValueError:
                        return
                    
                    answer_key = (answer_user_id, answer_platform_name)
                    player_current_attempts = game_session.player_attempts.get(answer_key, 0)
                    if player_current_attempts >= max_attempts_per_player:
                        return
                    
                    if game_session.total_attempts >= max_attempts_total:
                        controller.stop()
                        return
                    
                    game_session.total_attempts += 1
                    game_session.player_attempts[answer_key] = player_current_attempts + 1
                    
                    all_answers_history.append({
                        'user_id': answer_user_id,
                        'platform_name': answer_platform_name,
                        'user_name': answer_event.get_sender_name(),
                        'selected_num': selected_num,
                        'attempt_number': game_session.total_attempts
                    })
                    
                    correct_index = game_session.game_data.correct_index + 1
                    
                    if selected_num == correct_index:
                        current_time = time.time()
                        
                        if not answered_correctly:
                            answered_correctly = True
                            final_answer_user_id = answer_user_id
                            final_answer_user_name = answer_event.get_sender_name()
                            final_answer_platform_name = answer_platform_name
                            final_answer_index = selected_num
                            first_correct_time = current_time
                            winners_list.append({
                                'user_id': answer_user_id,
                                'platform_name': answer_platform_name,
                                'user_name': answer_event.get_sender_name(),
                                'answer_time': current_time,
                                'is_first': True
                            })
                            
                            if reward_valid_time > 0:
                                logger.info(f"[歌词猜曲] 第一个答对者: {final_answer_user_name}，启动{reward_valid_time}秒奖励有效时间")
                                async def stop_after_delay():
                                    await asyncio.sleep(reward_valid_time)
                                    controller.stop()
                                asyncio.create_task(stop_after_delay())
                            else:
                                controller.stop()
                        else:
                            time_since_first_correct = current_time - first_correct_time
                            if time_since_first_correct <= reward_valid_time and reward_valid_time > 0:
                                if not any(
                                    w['user_id'] == answer_user_id
                                    and w.get('platform_name') == answer_platform_name
                                    for w in winners_list
                                ):
                                    winners_list.append({
                                        'user_id': answer_user_id,
                                        'platform_name': answer_platform_name,
                                        'user_name': answer_event.get_sender_name(),
                                        'answer_time': current_time,
                                        'is_first': False
                                    })
                                    logger.info(f"[歌词猜曲] 奖励有效时间内额外答对: {answer_event.get_sender_name()} (+{time_since_first_correct:.2f}s)")
                    else:
                        if game_session.total_attempts >= max_attempts_total:
                            controller.stop()
                
                try:
                    await answer_waiter(event)
                except TimeoutError:
                    game_session.game_ended_by_timeout = True
                
                self.last_game_end_time[session_id] = time.time()
                
                correct_name = self.song_manager.get_display_name(game_session.game_data.correct_song)
                correct_index = game_session.game_data.correct_index + 1
                
                if game_session.game_ended_by_timeout and not answered_correctly:
                    result_text = f"⏰ 时间到！正确答案是 [{correct_index}] {correct_name}"

                    # 超时局中已提交的作答同样要记为失败尝试，否则正确率统计会虚高
                    for answer_record in all_answers_history:
                        self.db.update_user_game_result(
                            answer_record['user_id'],
                            answer_record['user_name'],
                            0,
                            correct=False,
                            platform_name=answer_record['platform_name'],
                        )
                elif answered_correctly:
                    if len(winners_list) == 1:
                        result_text = (
                            f"🎉 {final_answer_user_name} 答对了！获得1分！\n"
                            f"正确答案是 [{correct_index}] {correct_name}\n"
                        )
                        self.db.update_user_game_result(
                            final_answer_user_id,
                            final_answer_user_name,
                            1,
                            correct=True,
                            platform_name=final_answer_platform_name,
                        )
                        
                        for answer_record in all_answers_history:
                            if (
                                answer_record['user_id'], answer_record['platform_name']
                            ) != (
                                final_answer_user_id, final_answer_platform_name
                            ) or answer_record['selected_num'] != correct_index:
                                self.db.update_user_game_result(
                                    answer_record['user_id'], 
                                    answer_record['user_name'], 
                                    0, 
                                    correct=False,
                                    platform_name=answer_record['platform_name'],
                                )
                    else:
                        winner_names = [w['user_name'] for w in winners_list]
                        result_text = (
                            f"🎉 恭喜以下玩家答对！每人获得1分！\n"
                            f"{'、'.join(winner_names)}\n\n"
                            f"正确答案是 [{correct_index}] {correct_name}"
                        )
                        
                        for winner in winners_list:
                            self.db.update_user_game_result(
                                winner['user_id'],
                                winner['user_name'],
                                1,
                                correct=True,
                                platform_name=winner['platform_name'],
                            )
                        
                        for answer_record in all_answers_history:
                            if not any(
                                w['user_id'] == answer_record['user_id']
                                and w.get('platform_name') == answer_record['platform_name']
                                for w in winners_list
                            ):
                                self.db.update_user_game_result(
                                    answer_record['user_id'],
                                    answer_record['user_name'],
                                    0,
                                    correct=False,
                                    platform_name=answer_record['platform_name'],
                                )
                elif quit_ended_round:
                    result_text = (
                        f"本局已结束（仅退出本局）\n"
                        f"正确答案是 [{correct_index}] {correct_name}\n"
                    )

                    # 退出局中已提交的作答同样要记为失败尝试，否则正确率统计会虚高
                    for answer_record in all_answers_history:
                        self.db.update_user_game_result(
                            answer_record['user_id'],
                            answer_record['user_name'],
                            0,
                            correct=False,
                            platform_name=answer_record['platform_name'],
                        )
                else:
                    result_text = (
                        f"⚠️ 作答次数已全部用尽！\n"
                        f"正确答案是 [{correct_index}] {correct_name}\n"
                    )

                    for answer_record in all_answers_history:
                        self.db.update_user_game_result(
                            answer_record['user_id'],
                            answer_record['user_name'],
                            0,
                            correct=False,
                            platform_name=answer_record['platform_name'],
                        )

                if session_id in self.auto_sessions:
                    # 自动模式：只显示结果与歌名，随后自动开始下一局，不出现 markdown 按钮
                    yield event.plain_result(result_text)
                else:
                    result_text += "\n" + "\n".join(
                        self._build_server_footer(event, round_server)
                    )
                    if is_official_round:
                        # 官方机器人以 markdown 渲染结算消息，附切换/绑定/查分/排行榜连接与快捷入口
                        await self._send_markdown_text(event, result_text)
                    else:
                        yield event.plain_result(result_text)
                
                correct_jacket_img = await asyncio.to_thread(
                    self.song_manager.get_jacket_image, game_session.game_data.correct_song, round_server
                )
                if correct_jacket_img:
                    jacket_path = self.output_dir / f"correct_jacket_{time.time_ns()}.png"
                    correct_jacket_img.save(jacket_path)
                    yield event.image_result(str(jacket_path))
            
            finally:
                self.active_game_sessions.discard(session_id)
                self.game_sessions.pop(session_id, None)
            
            # 判断是否继续自动模式
            if not auto_mode:
                break
            
            if session_id not in self.auto_sessions:
                break

            # 更新连续无人作答计数：只要本局有人作答（无论对错）就不算无人作答
            if answered_correctly or all_answers_history:
                no_answer_streak = 0
            else:
                no_answer_streak += 1

            if no_answer_streak >= 3:
                yield event.plain_result("连续3局无人作答，自动模式已停止。")
                break
            
            yield event.plain_result("本局结束，3秒后自动开始下一局…发送「退出自动模式」可停止")
            
            if session_id not in self.auto_stop_events:
                self.auto_stop_events[session_id] = asyncio.Event()
            
            try:
                await asyncio.wait_for(self.auto_stop_events[session_id].wait(), timeout=3.0)
                # 收到退出信号
                break
            except asyncio.TimeoutError:
                pass
            
            first_round = False
        
        # 清理自动模式状态
        if auto_mode:
            self.auto_sessions.discard(session_id)
            self.auto_stop_events.pop(session_id, None)

    @filter.command("歌词猜曲", alias={"pjsk歌词猜曲", "猜歌词", "歌词识曲", "歌词猜歌"})
    async def start_guess_lyrics(self, event: AstrMessageEvent):
        """开始歌词猜曲游戏"""
        async for result in self._run_game_impl(event, auto_mode=False):
            yield result
    
    @filter.command("自动歌词猜曲", alias={"pjsk自动歌词猜曲", "自动猜歌词"})
    async def start_auto_guess_lyrics(self, event: AstrMessageEvent):
        """开始自动歌词猜曲模式"""
        if not self.data_initialized:
            yield event.plain_result("数据正在初始化中，请稍后再试...")
            return

        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return
        
        user_id, _ = self._get_account_identity(event)
        if self._is_event_user_blacklisted(event, user_id):
            yield event.plain_result("抱歉，你已被禁止使用此功能 😔")
            return
        
        session_id = event.unified_msg_origin
        
        session_lock = await self._get_session_lock(session_id)
        async with session_lock:
            if session_id in self.active_game_sessions or session_id in self.auto_sessions:
                yield event.plain_result("当前已经有一个游戏或自动模式在进行中啦~")
                return
            self.auto_sessions.add(session_id)
            self.auto_stop_events[session_id] = asyncio.Event()
        
        yield event.plain_result("🎮 自动歌词猜曲模式已开启！每局结束后将自动开始下一局，发送「退出自动模式」可随时停止。")
        
        async for result in self._run_game_impl(event, auto_mode=True):
            yield result

    @filter.command("退出自动模式", alias={"退出"})
    async def quit_auto_mode(self, event: AstrMessageEvent):
        """退出自动歌词猜曲模式（本局进行中时由对局等待器处理）"""
        session_id = event.unified_msg_origin
        if session_id not in self.auto_sessions or session_id in self.active_game_sessions:
            return
        
        self.auto_sessions.discard(session_id)
        if session_id in self.auto_stop_events:
            self.auto_stop_events[session_id].set()
        yield event.plain_result("已退出自动歌词猜曲模式。")
    
    @filter.command("歌词猜曲切换国服题库", alias={"歌词猜曲切换国服"})
    async def switch_to_sc(self, event: AstrMessageEvent):
        """切换为国服题库。"""
        await self._switch_server(event, SERVER_SC)

    @filter.command("歌词猜曲切换日服题库", alias={"歌词猜曲切换日服"})
    async def switch_to_jp(self, event: AstrMessageEvent):
        """切换为日服题库。"""
        await self._switch_server(event, SERVER_JP)

    @filter.command("歌词猜曲绑定", alias={"pjsk歌词猜曲绑定", "歌词猜曲绑定QQ"})
    async def bind_lyrics_account(self, event: AstrMessageEvent):
        """QQ 官方机器人账号绑定到普通 QQ 账号。"""
        if not self._is_qq_official_event(event):
            yield event.plain_result("此绑定功能仅支持 QQ 官方机器人使用。")
            return

        parts = event.message_str.strip().split(maxsplit=1)
        qq_user_id = parts[1].strip() if len(parts) > 1 else ""
        if not re.fullmatch(r"\d{5,12}", qq_user_id):
            yield event.plain_result("请按“歌词猜曲绑定 QQ号”的格式输入，例如：歌词猜曲绑定 21555762216。")
            return

        official_user_id = str(event.get_sender_id())
        current_user_id = self.db.resolve_user_id(OFFICIAL_PLATFORM_NAME, official_user_id)
        if str(current_user_id) != official_user_id:
            yield event.plain_result(f"当前官方机器人账号已经绑定至 QQ号 {current_user_id}。")
            return

        yield event.plain_result(self._build_binding_confirmation_message(qq_user_id))
        decision = None

        @session_waiter(timeout=60)
        async def binding_waiter(controller: SessionController, answer_event: AstrMessageEvent):
            nonlocal decision
            answer_text = answer_event.message_str.strip()
            if answer_text == "确认":
                decision = "confirm"
                controller.stop()
            elif answer_text == "取消":
                decision = "cancel"
                controller.stop()

        try:
            await binding_waiter(
                event,
                session_filter=BindingSessionFilter(event.unified_msg_origin, official_user_id),
            )
        except TimeoutError:
            yield event.plain_result("绑定确认已超时，绑定操作已取消。")
            return

        if decision == "cancel":
            yield event.plain_result("已取消绑定。")
            return
        if decision != "confirm":
            yield event.plain_result("未收到有效的绑定确认，绑定操作已取消。")
            return

        bound = await asyncio.to_thread(
            self.db.bind_official_account,
            official_user_id,
            qq_user_id,
        )
        if bound:
            yield event.plain_result(f"绑定成功！官方机的历史分数已迁移至 QQ号 {qq_user_id}。")
        else:
            yield event.plain_result("绑定失败：该官方账号可能已绑定，请稍后重试。")

    @filter.command("歌词猜曲帮助")
    async def show_help(self, event: AstrMessageEvent):
        """显示帮助信息"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return
        
        max_attempts_per_player = self.config.get("max_attempts_per_player", 1)
        max_attempts_total = self.config.get("max_attempts_total", 5)
        lyrics_display_mode = str(self.config.get("lyrics_display_mode", "image")).lower()
        
        help_text = (
            "🎵 PJSK 歌词猜曲指南 🎵\n\n"
            "【游戏指令】\n"
            "歌词猜曲 - 随机一首歌曲，展示歌词片段，猜出歌名！\n"
            "自动歌词猜曲 - 开启自动模式，每局结束后自动开始下一局\n"
            "歌词猜曲切换日服题库/歌词猜曲切换国服题库 - 切换题库服务器（下一局生效）\n"
            "歌词猜曲分数 - 查看自己的游戏数据统计\n"
            "歌词猜曲排行榜 - 查看总分排行榜\n"
            "歌词猜曲绑定 QQ号 - QQ官方机器人绑定到你的QQ号，需发送“确认”\n"
            "歌词猜曲自定义名称 [名称] - 设置你的个性化ID（不带参数可清除）\n\n"
            "【当前配置】\n"
            f"• 每位玩家每轮可作答: {max_attempts_per_player} 次\n"
            f"• 全局总作答次数: {max_attempts_total} 次\n"
            f"• 歌词展示模式: {'图片模式' if lyrics_display_mode == 'image' else '纯文本模式'}\n\n"
            "【管理员指令】\n"
            "刷新本地数据 - 重新加载本地翻译和别名数据\n\n"
            "【玩法说明】\n"
            "1. 发送「歌词猜曲」开始游戏，或发送「自动歌词猜曲」开启自动模式\n"
            "2. 系统随机选择一首歌曲并展示歌词片段\n"
            "3. 在限时内输入数字(1-10)选择正确答案\n"
            "4. 每位玩家有独立的作答次数限制，全局也有总次数限制\n"
            "5. 任一限制触发或有人答对时，本轮结束\n"
            "6. 答对获得1分，答错不计分但会消耗作答机会\n"
            "7. 自动模式下发送「退出自动模式」可随时停止自动开局"
        )
        yield event.plain_result(help_text)
    
    @filter.command("刷新本地数据", alias={"重载本地数据", "刷新数据"})
    async def reload_local_data(self, event: AstrMessageEvent):
        """刷新本地数据"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return
        
        if not self._is_super_user(event.get_sender_id()):
            yield event.plain_result("只有管理员才能使用此命令哦~")
            return
        
        yield event.plain_result("正在刷新本地数据，请稍候...")
        
        try:
            self.data_manager.reload_data()
            self.song_manager = LocalSongManager(
                self.lyrics_dir,
                self.data_manager,
                self.cloud_jacket_loader
            )

            # master 题库已同步时，重新套用（保证刷新后仍是同步数据优先）
            if self.master_data.is_ready(SERVER_JP) or self.master_data.is_ready(SERVER_SC):
                self._on_master_updated()

            yield event.plain_result(
                f"刷新完成！\n"
                f"本地歌曲: {len(self.song_manager.songs)}\n"
                f"中文翻译: {len(self.data_manager.cn_map)}\n"
                f"别名数据: {len(self.data_manager.aliases_map)}"
            )
        except (IOError, OSError, ValueError, KeyError) as e:
            logger.error(f"Failed to reload data: {e}")
            yield event.plain_result(f"刷新失败: {e}")
    
    @filter.command("歌词猜曲分数", alias={"pjsk歌词猜曲分数", "猜歌词分数", "歌词猜曲查分", "歌词猜曲个人分数"})
    async def show_user_score(self, event: AstrMessageEvent):
        """显示用户分数"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return
        
        raw_user_id = str(event.get_sender_id())
        user_id, platform_name = self._get_account_identity(event)
        user_name = event.get_sender_name()
        raw_platform_name = self._get_event_platform_name(event)
        platform_display_name = {
            OFFICIAL_PLATFORM_NAME: "QQ官方机器人",
            DEFAULT_PLATFORM_NAME: "普通QQ",
        }.get(raw_platform_name, raw_platform_name)
        identity_lines = [
            f"👤 用户ID: {raw_user_id}",
            f"🌐 平台: {platform_display_name}（{raw_platform_name}）",
        ]
        if raw_platform_name == OFFICIAL_PLATFORM_NAME and user_id == raw_user_id:
            identity_lines.extend([
                "当前官方机器人账号尚未绑定QQ号。",
                "如需将官方机分数迁移到普通QQ账号，请发送：歌词猜曲绑定 QQ号",
            ])
        elif user_id != raw_user_id:
            identity_lines.append(f"🔗 统计账号: {user_id}")
        identity_text = "\n".join(identity_lines)

        user_data = self.db.get_user_stats(user_id, platform_name)
        if not user_data:
            yield event.plain_result(
                f"{identity_text}\n\n"
                f"{user_name}，你还没有参与过歌词猜曲游戏哦！快来一起玩呀~ 🎮"
            )
            return
        
        score, attempts, correct_attempts, last_play_date, daily_plays = user_data
        accuracy = (correct_attempts * 100 / attempts) if attempts > 0 else 0
        rank = self.db.get_user_rank(score, platform_name)
        
        daily_limit = self.config.get("daily_play_limit", Config.DEFAULT_DAILY_LIMIT)
        today = time.strftime("%Y-%m-%d")
        
        if daily_limit == -1:
            remaining_plays = "无限次数"
        elif last_play_date == today:
            remaining = daily_limit - daily_plays
            remaining_plays = f"{remaining}次" if remaining > 0 else "0次"
        else:
            remaining_plays = f"{daily_limit}次"
        
        stats_text = (
            f"{identity_text}\n"
            f"✨ {user_name} 的歌词猜曲数据 ✨\n"
            f"🏆 总分: {score} 分\n"
            f"🎯 正确率: {accuracy:.1f}%\n"
            f"🎮 游戏次数: {attempts} 次\n"
            f"✅ 答对次数: {correct_attempts} 次\n"
            f"🏅 当前排名: 第 {rank} 名\n"
            f"📅 今日剩余: {remaining_plays}\n"
        )
        
        yield event.plain_result(stats_text)
    
    @filter.command("歌词猜曲排行榜", alias={"歌词猜曲排行", "pjsk歌词猜曲排行榜"})
    async def show_ranking(self, event: AstrMessageEvent):
        """显示排行榜"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return
        
        self._cleanup_output_dir()
        
        ranking_count = self.config.get("ranking_display_count", 10)
        # 边界值验证：确保排行榜人数在合理范围内
        ranking_count = max(1, min(int(ranking_count), 50))
        rows = self.db.get_ranking(ranking_count)
        
        if not rows:
            yield event.plain_result("还没有人参与过歌词猜曲游戏呢~ 快来成为第一个玩家吧！✨")
            return
        
        try:
            img_path = await asyncio.to_thread(
                self.image_generator.create_ranking_image, rows, self.output_dir
            )
            if img_path:
                yield event.image_result(str(img_path))
            else:
                yield event.plain_result("生成排行榜图片时出错。")
        except (IOError, OSError, ValueError, KeyError, TypeError) as e:
            logger.error(f"Failed to render ranking: {e}")
            yield event.plain_result("生成排行榜图片时出错。")
    
    @filter.command("歌词猜曲自定义名称", alias={"歌词猜曲昵称", "歌词猜曲名称", "歌词猜曲起名"})
    async def set_custom_name(self, event: AstrMessageEvent):
        """设置自定义名称"""
        if not self._is_group_allowed(event):
            reject_msg = self._get_whitelist_reject_message()
            if reject_msg:
                yield event.plain_result(reject_msg)
            return
        
        sender_id, platform_name = self._get_account_identity(event)
        if self._is_event_user_blacklisted(event, sender_id):
            yield event.plain_result("抱歉，你已被禁止使用此功能 😔")
            return
        parts = event.message_str.strip().split(maxsplit=1)
        custom_name = parts[1].strip() if len(parts) > 1 else None
        
        if custom_name:
            if len(custom_name) > Config.MAX_CUSTOM_NAME_LENGTH:
                yield event.plain_result(f"自定义名称过长，最多{Config.MAX_CUSTOM_NAME_LENGTH}个字符哦~")
                return
            if not custom_name.replace(' ', '').isprintable():
                yield event.plain_result("自定义名称包含非法字符！")
                return
            self.db.set_custom_name(sender_id, event.get_sender_name(), custom_name, platform_name)
            yield event.plain_result(f"好的！你的自定义名称已设置为：{custom_name} ✨")
        else:
            if self.db.set_custom_name(sender_id, event.get_sender_name(), None, platform_name):
                yield event.plain_result("好的！你的自定义名称已清除 ✨")
            else:
                yield event.plain_result("你还没有参与过游戏哦~ 🎮")
    
    async def terminate(self):
        """插件终止时的清理"""
        logger.info("Closing PJSK Guess Lyrics Plugin...")

        if hasattr(self, '_cleanup_task') and not self._cleanup_task.done():
            self._cleanup_task.cancel()
            try:
                await self._cleanup_task
            except asyncio.CancelledError:
                pass

        if hasattr(self, '_init_task') and not self._init_task.done():
            self._init_task.cancel()
            try:
                await self._init_task
            except asyncio.CancelledError:
                pass

        # 停止题库自动同步服务
        try:
            await self.master_data.terminate()
        except Exception as e:
            logger.warning(f"停止题库同步服务时出错: {e}")

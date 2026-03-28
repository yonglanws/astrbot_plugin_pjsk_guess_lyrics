import asyncio
import json
import random
import time
import os
import sqlite3
import urllib.request
import urllib.error
import io
from datetime import datetime
from contextlib import contextmanager
from dataclasses import dataclass
from pathlib import Path
from typing import Optional, List, Dict, Generator, Tuple
from collections import OrderedDict

from PIL import Image, ImageDraw, ImageFont

from astrbot.api import logger

try:
    from astrbot.api.event import filter, AstrMessageEvent
    from astrbot.api.star import Context, Star, register, StarTools
    import astrbot.api.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController
    from astrbot.api import AstrBotConfig
    from astrbot.core.utils.astrbot_path import get_astrbot_data_path
except ImportError:
    logger.error("Failed to import from astrbot.api, attempting fallback.")
    from astrbot.core.plugin import Plugin as Star, Context, register, filter, AstrMessageEvent
    import astrbot.core.message_components as Comp
    from astrbot.core.utils.session_waiter import session_waiter, SessionController

    class StarTools:
        @staticmethod
        def get_data_dir(plugin_name: str) -> Path:
            return Path(__file__).parent.parent.parent.parent / 'data' / 'plugin_data' / plugin_name

    def get_astrbot_data_path() -> Path:
        return Path(__file__).parent.parent.parent.parent / 'data'


try:
    from PIL.Image import Resampling
    LANCZOS = Resampling.LANCZOS
except ImportError:
    LANCZOS = 1


PLUGIN_NAME = "pjsk_guess_lyrics"
PLUGIN_AUTHOR = "慵懒午睡"
PLUGIN_DESCRIPTION = "PJSK歌词猜曲插件"
PLUGIN_VERSION = "2.5.0"
PLUGIN_REPO_URL = "https://github.com/yonglanws/astrbot_plugin_pjsk_guess_lyrics"


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
    
    BASE_URL = "https://snowyassets.exmeaning.com/startapp/music/jacket/jacket_s_{id}/jacket_s_{id}.png"
    
    def __init__(self, cache_dir: Optional[Path] = None):
        self.cache_dir = cache_dir
        if cache_dir:
            cache_dir.mkdir(parents=True, exist_ok=True)
    
    def _format_jacket_id(self, music_id: int) -> str:
        """
        格式化曲绘ID
        
        规则：
        - 1-99: 格式化为3位数字，前补零（如 001, 089）
        - 100-732: 直接使用数字本身
        """
        if 1 <= music_id <= 99:
            return f"{music_id:03d}"
        elif 100 <= music_id <= 732:
            return str(music_id)
        else:
            return str(music_id)
    
    def get_jacket_url(self, music_id: int) -> Optional[str]:
        """获取曲绘的云端URL"""
        if 1 <= music_id <= 732:
            formatted_id = self._format_jacket_id(music_id)
            return self.BASE_URL.format(id=formatted_id)
        return None
    
    def load_jacket_image(self, music_id: int) -> Optional[Image.Image]:
        """从云端加载曲绘图片"""
        if self.cache_dir:
            cache_file = self.cache_dir / f"{music_id}.png"
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
        
        url = self.get_jacket_url(music_id)
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
                        cache_file = self.cache_dir / f"{music_id}.png"
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
    
    def get_random_song(self) -> Optional[SongInfo]:
        """获取随机歌曲"""
        return random.choice(self.songs) if self.songs else None
    
    def get_random_options(self, correct_song: SongInfo, option_count: int = Config.DEFAULT_OPTION_COUNT) -> List[SongInfo]:
        """获取随机选项（包含正确答案）"""
        options = [correct_song]
        available_songs = [s for s in self.songs if s.music_id != correct_song.music_id]
        
        if len(available_songs) >= option_count - 1:
            options.extend(random.sample(available_songs, option_count - 1))
        else:
            options.extend(available_songs)
        
        random.shuffle(options)
        return options
    
    def get_display_name(self, song: SongInfo) -> str:
        """获取歌曲显示名称"""
        return song.display_name
    
    def get_jacket_image(self, song: SongInfo) -> Optional[Image.Image]:
        """获取曲绘图片（优先从云端加载）"""
        if self.cloud_jacket_loader:
            img = self.cloud_jacket_loader.load_jacket_image(song.music_id)
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
        self._load_fonts()
    
    def _load_fonts(self):
        """加载字体"""
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
                
                cn_text = self._get_chinese_translation(line)
                if cn_text:
                    cn_width = self._get_text_width(draw, cn_text, self.lyrics_cn_font)
                    cn_x = (img_width - cn_width) // 2
                    draw.text((cn_x, y + jp_height + jp_cn_gap), cn_text, font=self.lyrics_cn_font, fill=colors.TEXT_CN)
            
            return img
        except (IOError, OSError, ValueError, KeyError) as e:
            logger.error(f"Failed to create lyrics image: {e}")
            return None
    
    def _get_chinese_translation(self, japanese_line: str) -> str:
        """获取日文歌词的中文翻译（这里返回空，实际需要翻译数据）"""
        return ""
    
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
        """渲染排行榜图片（精美卡片式设计，白色色调）"""
        try:
            width = 720
            card_width = 680
            card_height = 100
            card_gap = 16
            header_height = 130
            footer_height = 50
            
            height = header_height + len(rows) * (card_height + card_gap) + footer_height
            
            img = Image.new("RGB", (width, height), (255, 255, 255))
            draw = ImageDraw.Draw(img)
            
            self._draw_gradient_background(draw, width, height)
            
            title_color = (50, 50, 70)
            subtitle_color = (120, 120, 140)
            card_bg = (255, 255, 255)
            card_border = (230, 230, 240)
            text_dark = (40, 40, 60)
            text_gray = (100, 100, 120)
            score_color = (255, 140, 0)
            accuracy_color = (0, 150, 136)
            attempts_color = (100, 149, 237)
            
            medal_colors = [
                (255, 193, 7),
                (192, 192, 192),
                (205, 127, 50)
            ]
            
            title_text = "歌词猜曲排行榜"
            title_width = self._get_text_width(draw, title_text, self.title_font)
            draw.text(((width - title_width) // 2, 40), title_text, font=self.title_font, fill=title_color)
            
            subtitle = f"共 {len(rows)} 位玩家"
            subtitle_width = self._get_text_width(draw, subtitle, self.small_font)
            draw.text(((width - subtitle_width) // 2, 95), subtitle, font=self.small_font, fill=subtitle_color)
            
            current_y = header_height
            
            card_x = (width - card_width) // 2
            
            data_area_right_edge = card_x + card_width - 30
            
            fixed_attempts_right = data_area_right_edge
            fixed_acc_center = card_x + card_width - 180
            fixed_score_left = card_x + card_width - 290
            
            for i, row in enumerate(rows):
                user_id, user_name, custom_name, score, attempts, correct_attempts = row
                display_name = custom_name if custom_name else user_name
                accuracy = f"{(correct_attempts * 100 / attempts if attempts > 0 else 0):.1f}%"
                
                self._draw_rounded_rect(draw, card_x, current_y, card_x + card_width, current_y + card_height, 14, card_bg, card_border)
                
                rank_circle_x = card_x + 35
                rank_circle_y = current_y + card_height // 2
                circle_radius = 22
                
                if i < 3:
                    draw.ellipse([rank_circle_x - circle_radius, rank_circle_y - circle_radius,
                                  rank_circle_x + circle_radius, rank_circle_y + circle_radius],
                                 fill=medal_colors[i])
                    rank_text = str(i + 1)
                    rank_text_width = self._get_text_width(draw, rank_text, self.option_font)
                    draw.text((rank_circle_x - rank_text_width // 2, rank_circle_y - 15),
                              rank_text, font=self.option_font, fill=(255, 255, 255))
                else:
                    draw.ellipse([rank_circle_x - circle_radius, rank_circle_y - circle_radius,
                                  rank_circle_x + circle_radius, rank_circle_y + circle_radius],
                                 fill=(220, 220, 230))
                    rank_text = str(i + 1)
                    rank_text_width = self._get_text_width(draw, rank_text, self.option_font)
                    draw.text((rank_circle_x - rank_text_width // 2, rank_circle_y - 15),
                              rank_text, font=self.option_font, fill=text_dark)
                
                name_x = card_x + 85
                name_y = current_y + 22
                name_display = str(display_name)[:20]
                name_width = self._get_text_width(draw, name_display, self.option_font)
                if name_width > 240:
                    name_display = self._truncate_text(draw, name_display, self.option_font, 230) + "..."
                draw.text((name_x, name_y), name_display, font=self.option_font, fill=text_dark)
                
                draw.text((name_x, name_y + 32), f"ID: {user_id}", font=self.small_font, fill=text_gray)
                
                attempts_str = str(attempts)
                attempts_label = "次"
                attempts_str_width = self._get_text_width(draw, attempts_str, self.card_title_font)
                attempts_label_width = self._get_text_width(draw, attempts_label, self.small_font)
                attempts_x = fixed_attempts_right - attempts_str_width - 5 - attempts_label_width
                attempts_y = current_y + 28
                draw.text((attempts_x, attempts_y), attempts_str, font=self.card_title_font, fill=attempts_color)
                draw.text((attempts_x + attempts_str_width + 5, attempts_y + 6), attempts_label, font=self.small_font, fill=text_gray)
                
                acc_label = "正确率"
                acc_str_width = self._get_text_width(draw, accuracy, self.card_title_font)
                acc_label_width = self._get_text_width(draw, acc_label, self.small_font)
                acc_x = fixed_acc_center - acc_str_width // 2
                acc_y = current_y + 28
                draw.text((acc_x, acc_y), accuracy, font=self.card_title_font, fill=accuracy_color)
                draw.text((fixed_acc_center - acc_label_width // 2, acc_y + 30), acc_label, font=self.small_font, fill=text_gray)
                
                score_str = str(score)
                score_label = "分"
                score_str_width = self._get_text_width(draw, score_str, self.card_title_font)
                score_x = fixed_score_left
                score_y = current_y + 28
                draw.text((score_x, score_y), score_str, font=self.card_title_font, fill=score_color)
                draw.text((score_x + score_str_width + 5, score_y + 6), score_label, font=self.small_font, fill=text_gray)
                
                current_y += card_height + card_gap
            
            footer_text = f"Generated on {datetime.now().strftime('%Y-%m-%d %H:%M')}"
            footer_width = self._get_text_width(draw, footer_text, self.small_font)
            draw.text(((width - footer_width) // 2, height - 30), footer_text, font=self.small_font, fill=(180, 180, 190))
            
            os.makedirs(output_dir, exist_ok=True)
            img_path = output_dir / f"ranking_{time.time_ns()}.png"
            img.save(img_path)
            return str(img_path)
        
        except (IOError, OSError, ValueError, KeyError, TypeError) as e:
            logger.error(f"渲染排行榜图片失败: {e}", exc_info=True)
            return None
    
    def _draw_gradient_background(self, draw: ImageDraw.ImageDraw, width: int, height: int):
        """绘制渐变背景（优化版本，使用批量绘制）"""
        if height <= 0:
            return
        
        step = max(1, height // 100)
        for y in range(0, height, step):
            gray_val = 252 - int(8 * y / height)
            end_y = min(y + step, height)
            draw.rectangle([(0, y), (width, end_y)], fill=(gray_val, gray_val, gray_val + 2))
    
    def _draw_rounded_rect(self, draw: ImageDraw.ImageDraw, x1: int, y1: int, x2: int, y2: int, radius: int, fill: tuple, outline: tuple):
        """绘制圆角矩形"""
        # 绘制主体矩形
        draw.rectangle([x1 + radius, y1, x2 - radius, y2], fill=fill)
        draw.rectangle([x1, y1 + radius, x2, y2 - radius], fill=fill)
        
        # 绘制四个圆角
        draw.ellipse([x1, y1, x1 + radius * 2, y1 + radius * 2], fill=fill)
        draw.ellipse([x2 - radius * 2, y1, x2, y1 + radius * 2], fill=fill)
        draw.ellipse([x1, y2 - radius * 2, x1 + radius * 2, y2], fill=fill)
        draw.ellipse([x2 - radius * 2, y2 - radius * 2, x2, y2], fill=fill)
        
        # 绘制边框
        draw.arc([x1, y1, x1 + radius * 2, y1 + radius * 2], 180, 270, fill=outline)
        draw.arc([x2 - radius * 2, y1, x2, y1 + radius * 2], 270, 360, fill=outline)
        draw.arc([x1, y2 - radius * 2, x1 + radius * 2, y2], 90, 180, fill=outline)
        draw.arc([x2 - radius * 2, y2 - radius * 2, x2, y2], 0, 90, fill=outline)
        draw.line([(x1 + radius, y1), (x2 - radius, y1)], fill=outline)
        draw.line([(x1 + radius, y2), (x2 - radius, y2)], fill=outline)
        draw.line([(x1, y1 + radius), (x1, y2 - radius)], fill=outline)
        draw.line([(x2, y1 + radius), (x2, y2 - radius)], fill=outline)
    
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
    
    def get_user_stats(self, user_id: str) -> Optional[Tuple]:
        """获取用户统计"""
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT score, attempts, correct_attempts, last_play_date, daily_plays FROM user_stats WHERE user_id = ?",
                (user_id,)
            )
            return cursor.fetchone()
    
    def get_user_rank(self, score: int) -> int:
        """获取用户排名（带缓存）"""
        current_time = time.time()
        
        if score in self._user_rank_cache:
            cached_rank, cached_time = self._user_rank_cache[score]
            if current_time - cached_time < self._cache_ttl:
                return cached_rank
        
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT COUNT(*) FROM user_stats WHERE score > ?", (score,))
            rank = cursor.fetchone()[0] + 1
            
            self._user_rank_cache[score] = (rank, current_time)
            return rank
    
    def update_user_game_result(self, user_id: str, user_name: str, score: int, correct: bool):
        """原子性更新用户游戏结果（使用纯SQL原子操作）"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                """INSERT INTO user_stats (user_id, user_name, score, attempts, correct_attempts, last_play_date, daily_plays)
                   VALUES (?, ?, ?, 1, ?, ?, 1)
                   ON CONFLICT(user_id) DO UPDATE SET
                       score = score + excluded.score,
                       attempts = attempts + 1,
                       correct_attempts = correct_attempts + excluded.correct_attempts,
                       user_name = excluded.user_name,
                       last_play_date = excluded.last_play_date,
                       daily_plays = CASE WHEN last_play_date = excluded.last_play_date THEN daily_plays + 1 ELSE 1 END
                """,
                (user_id, user_name, score, 1 if correct else 0, today)
            )
            conn.commit()
            self._invalidate_rank_cache()
    
    def update_user_play(self, user_id: str, user_name: str):
        """更新用户游戏记录"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT last_play_date, daily_plays FROM user_stats WHERE user_id = ?", (user_id,))
            user_data = cursor.fetchone()
            
            if user_data:
                last_play_date, daily_plays = user_data
                new_daily_plays = daily_plays + 1 if last_play_date == today else 1
                cursor.execute(
                    "UPDATE user_stats SET user_name = ?, last_play_date = ?, daily_plays = ? WHERE user_id = ?",
                    (user_name, today, new_daily_plays, user_id)
                )
            else:
                cursor.execute(
                    "INSERT INTO user_stats (user_id, user_name, last_play_date, daily_plays) VALUES (?, ?, ?, ?)",
                    (user_id, user_name, today, 1)
                )
            conn.commit()
    
    def update_user_score(self, user_id: str, user_name: str, score: int, correct: bool):
        """更新用户分数"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT score, attempts, correct_attempts FROM user_stats WHERE user_id = ?", (user_id,))
            user_data = cursor.fetchone()
            
            if user_data:
                new_score = user_data[0] + score
                new_attempts = user_data[1] + 1
                new_correct = user_data[2] + (1 if correct else 0)
                cursor.execute(
                    "UPDATE user_stats SET score = ?, attempts = ?, correct_attempts = ?, user_name = ? WHERE user_id = ?",
                    (new_score, new_attempts, new_correct, user_name, user_id)
                )
            else:
                cursor.execute(
                    "INSERT INTO user_stats (user_id, user_name, score, attempts, correct_attempts, last_play_date, daily_plays) VALUES (?, ?, ?, ?, ?, ?, ?)",
                    (user_id, user_name, score, 1, 1 if correct else 0, today, 0)
                )
            conn.commit()
    
    def can_play_today(self, user_id: str, daily_limit: int) -> bool:
        """检查用户今日是否还能游戏"""
        if daily_limit == -1:
            return True
        
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT daily_plays, last_play_date FROM user_stats WHERE user_id = ?", (user_id,))
            user_data = cursor.fetchone()
            if user_data and user_data[1] == today:
                return user_data[0] < daily_limit
            return True
    
    def set_custom_name(self, user_id: str, user_name: str, custom_name: Optional[str]) -> bool:
        """设置自定义名称，返回是否成功"""
        today = time.strftime("%Y-%m-%d")
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute("SELECT user_id FROM user_stats WHERE user_id = ?", (user_id,))
            exists = cursor.fetchone() is not None
            
            if custom_name:
                if exists:
                    cursor.execute("UPDATE user_stats SET custom_name = ? WHERE user_id = ?", (custom_name, user_id))
                else:
                    cursor.execute(
                        "INSERT INTO user_stats (user_id, user_name, custom_name, score, attempts, correct_attempts, last_play_date, daily_plays) VALUES (?, ?, ?, ?, ?, ?, ?, ?)",
                        (user_id, user_name, custom_name, 0, 0, 0, today, 0)
                    )
            elif exists:
                cursor.execute("UPDATE user_stats SET custom_name = NULL WHERE user_id = ?", (user_id,))
            else:
                return False
            
            conn.commit()
            return True
    
    def get_ranking(self, limit: int) -> List[Tuple]:
        """获取排行榜数据"""
        with self._get_connection() as conn:
            cursor = conn.cursor()
            cursor.execute(
                "SELECT user_id, user_name, custom_name, score, attempts, correct_attempts FROM user_stats ORDER BY score DESC LIMIT ?",
                (limit,)
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
        
        self.cloud_jacket_loader = CloudJacketLoader(self.jacket_cache_dir)
        
        font_path = self.resources_dir / "font.ttf"
        self.image_generator = ImageGenerator(font_path if font_path.exists() else None)
        
        self.active_game_sessions: set = set()
        self.game_sessions: Dict[str, GameSession] = LRUDict(max_size=Config.MAX_SESSION_CACHE_SIZE)
        self.session_locks: Dict[str, asyncio.Lock] = {}
        self.last_game_end_time: Dict[str, float] = LRUDict(max_size=Config.MAX_SESSION_CACHE_SIZE)
        self._lock_creation_lock = asyncio.Lock()
        self.song_manager: Optional[LocalSongManager] = None
        self.data_initialized = False
        
        self._cleanup_output_dir()
        self._cleanup_task = asyncio.create_task(self._periodic_cleanup())
        self._init_task = asyncio.create_task(self._initialize_data())
        
        logger.info(f"PJSK Guess Lyrics Plugin initialized (v{PLUGIN_VERSION})")
    
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
    
    def start_new_game(self) -> Optional[GameData]:
        """开始新游戏"""
        if not self.song_manager:
            logger.error("Song manager not initialized")
            return None
        
        for _ in range(Config.DEFAULT_MAX_ATTEMPTS):
            correct_song = self.song_manager.get_random_song()
            if not correct_song:
                logger.error("No songs available for game")
                return None
            
            lyrics = LrcParser.parse(correct_song.lrc_path)
            if not lyrics:
                logger.warning(f"Failed to parse lyrics for song: {correct_song.display_name}, retrying...")
                continue
            
            lyrics_snippet = self._extract_random_lyrics(lyrics, Config.LYRICS_LINES_COUNT)
            options = self.song_manager.get_random_options(correct_song)
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
    
    @filter.command("歌词猜曲", alias={"pjsk歌词猜曲", "猜歌词", "歌词识曲", "歌词猜歌"})
    async def start_guess_lyrics(self, event: AstrMessageEvent):
        """开始歌词猜曲游戏"""
        if not self.data_initialized:
            yield event.plain_result("数据正在初始化中，请稍后再试...")
            return
        
        if not self._is_group_allowed(event):
            return
        
        user_id = event.get_sender_id()
        if self._is_user_blacklisted(user_id):
            yield event.plain_result("抱歉，你已被禁止使用此功能 😔")
            return
        
        session_id = event.unified_msg_origin
        
        session_lock = await self._get_session_lock(session_id)
        
        async with session_lock:
            if session_id in self.active_game_sessions:
                yield event.plain_result("当前已经有一个游戏在进行中啦~ 等它结束后再来玩吧！")
                return
            
            cooldown_remaining = self._get_cooldown_remaining(session_id)
            if cooldown_remaining > 0:
                time_display = f"{cooldown_remaining:.1f}" if cooldown_remaining < 1 else str(int(cooldown_remaining))
                yield event.plain_result(f"让我们休息一下吧！{time_display}秒后再来玩哦~ 😊")
                return
            
            daily_limit = self.config.get("daily_play_limit", Config.DEFAULT_DAILY_LIMIT)
            if not self.db.can_play_today(user_id, daily_limit):
                yield event.plain_result(f"今天的游戏次数已经用完啦~ 明天再来玩吧！每天最多可以玩{daily_limit}次哦~ ✨")
                return
            
            self.active_game_sessions.add(session_id)
        
        try:
            game_data = self.start_new_game()
            if not game_data:
                yield event.plain_result("开始游戏失败，可能存在歌词文件损坏或格式不正确，请联系管理员检查日志。")
                return
            
            lyrics_img = self.image_generator.create_lyrics_image(game_data.lyrics_snippet)
            if not lyrics_img:
                yield event.plain_result("生成歌词图片时出错，请稍后再试。")
                return
            
            async def load_single_jacket(opt):
                """加载单个曲绘"""
                jacket_img = await asyncio.to_thread(
                    self.song_manager.get_jacket_image, opt
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
            
            options_img = self.image_generator.create_options_image(options_with_images)
            if not options_img:
                yield event.plain_result("生成选项图片时出错，请稍后再试。")
                return
            
            lyrics_img_path = self.image_generator.save_image(lyrics_img, self.output_dir, "lyrics")
            options_img_path = self.image_generator.save_image(options_img, self.output_dir, "options")
            
            if not lyrics_img_path or not options_img_path:
                yield event.plain_result("保存图片时出错，请稍后再试。")
                return
            
            correct_display_name = self.song_manager.get_display_name(game_data.correct_song)
            logger.info(f"[歌词猜曲插件] 新游戏开始. 答案: {correct_display_name}")
            
            game_session = GameSession(game_data=game_data)
            self.game_sessions[session_id] = game_session
            
            timeout_seconds = self.config.get("answer_timeout", Config.DEFAULT_TIMEOUT)
            intro_text = f"🎵 歌词猜曲 🎵\n请在{timeout_seconds}秒内输入数字(1-10)选择正确答案~\n\n歌词片段：\n"
            
            yield event.chain_result([
                Comp.Plain(intro_text),
                Comp.Image(file=lyrics_img_path),
                Comp.Image(file=options_img_path)
            ])
            
            answered_user_id = None
            answered_user_name = None
            
            @session_waiter(timeout=timeout_seconds)
            async def answer_waiter(controller: SessionController, answer_event: AstrMessageEvent):
                nonlocal answered_user_id, answered_user_name
                answer_text = answer_event.message_str.strip()
                if answer_text.isdigit():
                    try:
                        selected_num = int(answer_text)
                        if 1 <= selected_num <= 10:
                            game_session.answer_index = selected_num
                            answered_user_id = answer_event.get_sender_id()
                            answered_user_name = answer_event.get_sender_name()
                            controller.stop()
                    except ValueError:
                        pass
            
            try:
                await answer_waiter(event)
            except TimeoutError:
                game_session.game_ended_by_timeout = True
            
            self.last_game_end_time[session_id] = time.time()
            
            correct_name = self.song_manager.get_display_name(game_session.game_data.correct_song)
            correct_index = game_session.game_data.correct_index + 1
            
            result_user_id = answered_user_id if answered_user_id else user_id
            result_user_name = answered_user_name if answered_user_name else event.get_sender_name()
            
            if game_session.answer_index is None:
                result_text = f"⏰ 时间到！正确答案是 [{correct_index}] {correct_name}"
            elif game_session.answer_index == correct_index:
                result_text = f"🎉 {result_user_name}答对了！获得1分！\n正确答案是 [{correct_index}] {correct_name}"
                self.db.update_user_game_result(result_user_id, result_user_name, 1, correct=True)
            else:
                result_text = f"❌ {result_user_name}回答错误！正确答案是 [{correct_index}] {correct_name}"
                self.db.update_user_game_result(result_user_id, result_user_name, 0, correct=False)
            
            yield event.plain_result(result_text)
            
            # 显示正确答案的曲绘
            correct_jacket_img = await asyncio.to_thread(
                self.song_manager.get_jacket_image, game_session.game_data.correct_song
            )
            if correct_jacket_img:
                jacket_path = self.output_dir / f"correct_jacket_{time.time_ns()}.png"
                correct_jacket_img.save(jacket_path)
                yield event.image_result(str(jacket_path))
            
        finally:
            self.active_game_sessions.discard(session_id)
            self.game_sessions.pop(session_id, None)
            self.session_locks.pop(session_id, None)
    
    @filter.command("歌词猜曲帮助")
    async def show_help(self, event: AstrMessageEvent):
        """显示帮助信息"""
        if not self._is_group_allowed(event):
            return
        
        help_text = (
            "🎵 PJSK 歌词猜曲指南 🎵\n\n"
            "【歌词猜曲】\n"
            "歌词猜曲 - 随机一首歌曲，展示歌词片段，猜出歌名！\n"
            "歌词猜曲分数 - 查看自己的游戏数据统计\n"
            "歌词猜曲排行榜 - 查看总分排行榜\n"
            "歌词猜曲自定义名称 - 设置你的个性化ID\n\n"
            "【管理员指令】\n"
            "刷新本地数据 - 重新加载本地翻译和别名数据\n"
        )
        yield event.plain_result(help_text)
    
    @filter.command("刷新本地数据", alias={"重载本地数据", "刷新数据"})
    async def reload_local_data(self, event: AstrMessageEvent):
        """刷新本地数据"""
        if not self._is_group_allowed(event):
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
            
            yield event.plain_result(
                f"刷新完成！\n"
                f"本地歌曲: {len(self.song_manager.songs)}\n"
                f"中文翻译: {len(self.data_manager.cn_map)}\n"
                f"别名数据: {len(self.data_manager.aliases_map)}"
            )
        except (IOError, OSError, ValueError, KeyError) as e:
            logger.error(f"Failed to reload data: {e}")
            yield event.plain_result(f"刷新失败: {e}")
    
    @filter.command("歌词猜曲分数", alias={"pjsk歌词猜曲分数", "猜歌词分数", "歌词猜曲查分"})
    async def show_user_score(self, event: AstrMessageEvent):
        """显示用户分数"""
        if not self._is_group_allowed(event):
            return
        
        user_id = event.get_sender_id()
        user_name = event.get_sender_name()
        
        user_data = self.db.get_user_stats(user_id)
        if not user_data:
            yield event.plain_result(f"{user_name}，你还没有参与过歌词猜曲游戏哦！快来一起玩呀~ 🎮")
            return
        
        score, attempts, correct_attempts, last_play_date, daily_plays = user_data
        accuracy = (correct_attempts * 100 / attempts) if attempts > 0 else 0
        rank = self.db.get_user_rank(score)
        
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
            return
        
        sender_id = event.get_sender_id()
        parts = event.message_str.strip().split(maxsplit=1)
        custom_name = parts[1].strip() if len(parts) > 1 else None
        
        if custom_name:
            if len(custom_name) > Config.MAX_CUSTOM_NAME_LENGTH:
                yield event.plain_result(f"自定义名称过长，最多{Config.MAX_CUSTOM_NAME_LENGTH}个字符哦~")
                return
            if not custom_name.replace(' ', '').isprintable():
                yield event.plain_result("自定义名称包含非法字符！")
                return
            self.db.set_custom_name(sender_id, event.get_sender_name(), custom_name)
            yield event.plain_result(f"好的！你的自定义名称已设置为：{custom_name} ✨")
        else:
            if self.db.set_custom_name(sender_id, event.get_sender_name(), None):
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

import importlib
import sys
import types
from pathlib import Path


PLUGIN_DIR = Path(__file__).parents[1]


def _install_astrbot_stubs():
    logger = types.SimpleNamespace(
        debug=lambda *args, **kwargs: None,
        error=lambda *args, **kwargs: None,
        info=lambda *args, **kwargs: None,
        warning=lambda *args, **kwargs: None,
    )
    astrbot = types.ModuleType("astrbot")
    api = types.ModuleType("astrbot.api")
    api.logger = logger
    api.AstrBotConfig = dict
    event = types.ModuleType("astrbot.api.event")
    event.AstrMessageEvent = object
    event.filter = types.SimpleNamespace(command=lambda *args, **kwargs: lambda func: func)
    star = types.ModuleType("astrbot.api.star")
    star.Context = object
    star.Star = object
    star.StarTools = types.SimpleNamespace(get_data_dir=lambda name: None)
    star.register = lambda *args, **kwargs: lambda cls: cls
    components = types.ModuleType("astrbot.api.message_components")
    core = types.ModuleType("astrbot.core")
    utils = types.ModuleType("astrbot.core.utils")
    astrbot_path = types.ModuleType("astrbot.core.utils.astrbot_path")
    astrbot_path.get_astrbot_data_path = lambda: None
    waiter = types.ModuleType("astrbot.core.utils.session_waiter")
    waiter.SessionController = object
    waiter.SessionFilter = object
    waiter.session_waiter = lambda *args, **kwargs: lambda func: func

    sys.modules.update(
        {
            "astrbot": astrbot,
            "astrbot.api": api,
            "astrbot.api.event": event,
            "astrbot.api.star": star,
            "astrbot.api.message_components": components,
            "astrbot.core": core,
            "astrbot.core.utils": utils,
            "astrbot.core.utils.astrbot_path": astrbot_path,
            "astrbot.core.utils.session_waiter": waiter,
        }
    )


def _load_main_module():
    _install_astrbot_stubs()
    sys.path.insert(0, str(PLUGIN_DIR))
    sys.modules.pop("main", None)
    return importlib.import_module("main")


def test_answer_results_do_not_consume_daily_start_limit(tmp_path):
    module = _load_main_module()
    db = module.DatabaseManager(str(tmp_path / "lyrics.db"))

    db.update_user_play("starter", "Starter")
    db.update_user_game_result("starter", "Starter", 1, correct=True)
    db.update_user_game_result("participant", "Participant", 0, correct=False)

    assert db.get_user_stats("starter")[-1] == 1
    assert db.get_user_stats("participant")[-1] == 0


def test_runtime_dependencies_are_declared():
    requirements = (PLUGIN_DIR / "requirements.txt").read_text(encoding="utf-8")

    assert "aiohttp" in requirements
    assert "Pillow" in requirements
    assert "pilmoji" in requirements


def test_lyrics_are_grouped_as_original_and_translation_pairs():
    module = _load_main_module()

    assert module.ImageGenerator._lyrics_pairs(["日文一", "中文一", "日文二", "中文二"]) == [
        ("日文一", "中文一"),
        ("日文二", "中文二"),
    ]
    assert module.ImageGenerator._lyrics_pairs(["Only one line"]) == [("Only one line", "")]


def test_cached_master_data_notifies_after_start(tmp_path):
    sys.path.insert(0, str(PLUGIN_DIR))
    sys.modules.pop("master_data_service", None)
    service_module = importlib.import_module("master_data_service")
    service = service_module.MasterDataService(tmp_path)
    derived_path = tmp_path / "musicdata" / service_module.SERVER_JP / "derived.json"
    derived_path.parent.mkdir(parents=True)
    derived_path.write_text('[{"id": 1, "title": "Song", "cn": "歌曲", "aliases": []}]', encoding="utf-8")
    notifications = []
    service.on_songs_updated = lambda: notifications.append(True)

    async def start_and_stop():
        await service.start()
        await service.terminate()

    import asyncio

    asyncio.run(start_and_stop())
    assert notifications == [True]

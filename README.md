# astrbot_plugin_pjsk_guess_lyrics

《初音未来 缤纷舞台》（Project SEKAI）**歌词猜曲**娱乐插件。用户根据展示的歌词片段与选项卡片，在限时内猜出正确的歌曲名称。

## 特性

- 🎵 **歌词展示模式**：支持精美图片模式（image）与快速纯文本模式（text），可自由切换
- 🔄 **题库自动同步**：歌名、中文译名与别名自 Haruki master 每 24 小时自动同步，新歌随游戏版本更新自动入库（可猜曲目 = 本地歌词库 ∩ 对应服务器曲目）
- 🌐 **多服务器题库**：支持日服 / 国服题库自由切换，按群独立记忆
- 🏆 **精美数据面板**：内置积分排行榜（Pillow 本地渲染横向表格，与猜卡面同款视觉规范，支持自定义名称、未绑定 QQ 徽章）、个人战绩查询、每日次数限制与冷却
- 🤖 **QQ 官方机器人支持**：官机 markdown 渲染，开局附操作连接，结算附切换题库/绑定/查分/排行榜连接；快捷入口由 `quick_entries` 配置控制（默认关闭）；支持绑定普通 QQ 迁移分数
- ⚡ **双模式退出**：`仅退出本局` 与 `退出自动模式` 严格分离，自动模式精简无扰
- 👥 **双重作答机制**：支持玩家个人作答次数限制与全局总次数限制协同工作

## 指令

### 游戏指令

| 指令 | 别名 | 说明 |
| --- | --- | --- |
| `歌词猜曲` | `pjsk歌词猜曲`、`猜歌词`、`歌词识曲`、`歌词猜歌` | 开始一轮歌词猜曲游戏 |
| `自动歌词猜曲` | `pjsk自动歌词猜曲`、`自动猜歌词` | 自动模式：每局结束后自动开始下一局 |

### 题库与账号

| 指令 | 说明 |
| --- | --- |
| `歌词猜曲切换日服题库` / `歌词猜曲切换国服题库` | 切换本群题库服务器（下一局生效） |
| `歌词猜曲绑定 QQ号` | 将 QQ 官方机器人账号绑定到普通 QQ 号，分数自动迁移（需发送"确认"） |

### 数据与帮助

| 指令 | 别名 | 说明 |
| --- | --- | --- |
| `歌词猜曲排行榜` | `歌词猜曲排行`、`pjsk歌词猜曲排行榜` | 查看总分排行榜 |
| `歌词猜曲分数` | `pjsk歌词猜曲分数`、`猜歌词分数`、`歌词猜曲查分`、`歌词猜曲个人分数` | 查看自己的游戏数据统计 |
| `歌词猜曲自定义名称 [名称]` | `歌词猜曲昵称`、`歌词猜曲名称`、`歌词猜曲起名` | 设置自定义 ID（不带参数可清除） |
| `歌词猜曲帮助` | - | 显示帮助信息 |

### 管理员指令

| 指令 | 说明 |
| --- | --- |
| `刷新本地数据` | 重新加载本地翻译和别名数据 |

### 退出机制说明

- **`仅退出本局`**：仅在游玩中生效，立即结束当前对局并公布答案（自动模式继续开下一局）。
- **`退出自动模式`**（别名：`退出`）：任何时候可触发，停止自动续局（当前对局继续打完）。
- **自动模式精简**：自动模式期间全程不出现 markdown 连接按钮，结算只显示结果、歌名与下一局提示，退出自动模式后恢复完整结算面板。

## 配置说明

通过 AstrBot WebUI 界面进行配置：

| 配置项 | 类型 | 默认值 | 说明 |
| --- | --- | --- | --- |
| `default_server` | string | `jp` | 默认题库服务器（`jp`=日服 / `sc`=国服） |
| `update_interval_hours` | int | `24` | master 题库自动更新间隔（小时） |
| `connect_link_template` | string | （官方标签） | QQ 官方机器人结算连接的 markdown 模板 |
| `quick_entries` | list | `[]` | 结算快捷入口列表（若为空则不显示快捷入口） |
| `jp_resource_url_base` | string | `https://storage.exmeaning.com/sekai-jp-assets` | 日服曲绘资源根地址 |
| `sc_resource_url_base` | string | `https://storage.exmeaning.com/sekai-sc-assets` | 国服曲绘资源根地址 |
| `answer_timeout` | int | `30` | 答题超时时间（秒） |
| `daily_play_limit` | int | `10` | 每日游戏次数上限（-1 为无限制） |
| `game_cooldown_seconds` | int | `30` | 游戏冷却时间（秒） |
| `ranking_display_count` | int | `10` | 排行榜显示人数（建议 5-20） |
| `max_attempts_per_player`| int | `1` | 每位玩家每轮可作答次数上限 |
| `max_attempts_total` | int | `5` | 每轮游戏全局总作答次数上限 |
| `lyrics_display_mode` | string | `image` | 歌词展示模式：`image`（图片）或 `text`（纯文本） |
| `reward_valid_time` | int | `0` | 首位答对后的奖励有效时间（秒，0 为禁用） |
| `group_whitelist` | list | `[]` | 群聊白名单（为空则所有群可用） |
| `whitelist_reject_message`| string | （提示语） | 非白名单群聊提示语（留空不提示） |
| `super_users` | list | `[]` | 管理员用户 ID 列表 |
| `blacklist` | list | `[]` | 黑名单用户 ID 列表 |

## 资源

- 日服master：[Team-Haruki/haruki-sekai-master](https://github.com/Team-Haruki/haruki-sekai-master)
- 国服master：[Team-Haruki/haruki-sekai-sc-master](https://github.com/Team-Haruki/haruki-sekai-sc-master)
- 中文译名：`translation.exmeaning.com`（Moesekai 翻译源）
- 歌曲别名：`moe.exmeaning.com/data/music_alias`（Moesekai 别名源）
- 歌词数据：网易云音乐（本地歌词库）
- 日服曲绘资源：`https://storage.exmeaning.com/sekai-jp-assets/music/jacket`
- 国服曲绘资源：`https://storage.exmeaning.com/sekai-sc-assets/music/jacket`

优先走 GitHub Contents API，失败时回退 jsDelivr CDN。数据持久化于 `data/plugin_data/pjsk_guess_lyrics/`。

## 依赖

`Pillow`、`pilmoji`、`aiohttp`。图片全部使用 Pillow 本地渲染。

## 致谢

部分代码及灵感参考自 [astrbot_plugin_pjsk_guess_song](https://github.com/nichinichisou0609/astrbot_plugin_pjsk_guess_song)。在此致谢。

完整更新历史见 [CHANGELOG.md](CHANGELOG.md)。

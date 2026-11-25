# Hyg：仓库和研究记录的卫生整理（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-25 07:32 至 07:49 |
| 工具调用 / agda 编译 (粗数) | 108 / 2 |
| token (usage 字段，按消息去重) | 输出 65132；新写入缓存的输入 223823；读缓存的输入 14437115；其余输入 196 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `Hyg` (在 `<实验目录>/hyg/`) |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它，再严格照做（它是自足的：范围、硬约束、可以直接修的四类、只列出不动的五类、验收与交付格式都在里面）：

<实验目录>/briefs/Hyg.md

要点提示（以简报为准）：任务是对一个 Agda 研究仓库（<仓库>）做仓库和研究记录的卫生整理。只有四类机械的、不改含义的毛病可以直接修：仓库文件里的本机路径换成占位符、可唯一确定目标的断链、坏掉的表格与代码围栏、以及在已改文件里顺手处理的尾随空白；每一处都要记进改动清单文件。其余一律只列出不动。硬约束：不改任何结论、定理、判断、数字或措辞；不碰 src/、archive/、AGENTS.md、.claude/、Agda 代码块与 .agda/.agda.txt 文件；不删除、不移动、不改名任何文件；不做任何 git 写操作；留档的回报原文只允许把本机路径换成占位符；台账只修表格格式；发现的个人信息只报文件与行号，不抄内容。临时文件只放工作目录 <实验目录>/hyg ；同时只跑一个 agda，堆上限 6G。最终消息就是回报原文，中文，区分已核实与判断。

## 回报原文

### Hyg 回报：仓库与研究记录的卫生整理

#### 一句话结论
改了 6 个文件，共 105 处：路径 1 处，表格 104 处，断链 0 处，空白 0 处。这 6 个文件都没有尾随空白，末尾也都有换行，所以空白一类不用动。硬约束没有拦下任何必须改的东西；凡是受约束的地方（留档、`archive/`、Agda 源文件、LOG 旧段落）都只列出，没有改。三个验收入口都退出 0。

改动清单在 `<实验目录>/hyg/Hyg-changes.tsv`，共 6 行，每行 4 列。

#### 已修（已核实：逐行和主审的 `hyg-baseline` 副本 diff 过，变化只有下面这些）
**路径（1 处）**
- `probes/OCF/Align/BoundedCompletionStageWf.lagda.md` 第 6 行，在代码围栏外：`<临时目录>/lambda-target-arch` 换成 `<实验目录>/lambda-target-arch`。这个模块没有被任何文件导入，文首自己写着 251 草案。

**表格（104 处，格内文字一字未动）**
- `probes/RESULTS.md` 第 131–229 行，共 99 处。表头是 5 列（层 | 声称 | 文件 | 定理 | 档），这 99 行只有 4 格。我核对过每一行，第 3 格都是模块列表，第 4 格都是档位，所以在两者之间插入一个空的"定理"格。脚本断言过：每行插入前正好 5 根竖线，插入后去掉新加的格就等于原行。
- 文字里未转义的 `|x|`（绝对值）把行拆出了多余的格，我把这些竖线转义成 `\|`。渲染出来的文字不变：
  - `probes/Survey/IdeaLedger.md` 第 876 行（V501），1 处。台账的条目和文字都没动。
  - `probes/Survey/RouteReview3.md` 第 654 行，在代码片段 `|β|·ω³` 里，1 处。
  - `probes/Survey/RR3-Backward.md` 第 196 行，1 处。
  - `probes/Survey/SkeletonAudit.md` 第 46 行和第 88 行，2 处。

**断链：0 处。** 检查范围是 README、LOG、RESULTS 和 `Survey/` 下非留档的 .md 与 .lagda.md，里面没有真正的断链。唯一的命中在 `research_notes/…/R2_infinitary_derivations.md:45`，是把公式 `\mathcal H[Z](X)` 误认成了链接。

#### 只列出，不动

##### A. 该删的候选（只清点）
- **.agdai：5001 个，约 2.97 GB。** 全部在 `./_build`（165 个文件，32M）和 `probes/_build`（整个目录 2.8G）里。它们都被 `.gitignore` 的 `*.agdai` 忽略。但 `/_build` 规则只管根目录，所以 `probes/_build` 里不是 .agdai 的 862 个文件没有被忽略，在 git 里显示为未跟踪：840 个 html、12 个 dot、5 个 css、3 个 json、1 个 sha256，外加 `YiCarryPlus-audit/libraries`。
- **日志：11 个，都在 `probes/_build/{YiCarryPlus,YiWall,YiK1b}-audit/`。** 被 `*.log` 忽略。这三个 audit 目录看起来是审计试验留下的。
- **空文件：1 个，`public/.nojekyll`。** 判断：这是 GitHub Pages 有意放的，不算候选。
- **内容完全相同的重复：6 组，多出 6 个副本，共 21,280 字节。**
  - `Reports-2026-11-24/attachments` 里的 `M4-KOpPow` 与 `M4b-KOpPow`、`M2-KIface` 与 `M2v2-KIface`。materialize 脚本用的是 M4b 和 M2v2。
  - `Lead/attachments/B10Join`、`B11Join` 各与 `Reports-2026-11-16/attachments` 里的对应文件相同。
  - `scripts/scafladder` 与 `scripts/uniform5` 里的两份 `*-Sb2.patch`。
- **其他遗留**
  - `.DS_Store` 8 个，其中 3 个被跟踪（都在 `public/` 下）。
  - `probes/Survey/Reports-2026-11-18/__pycache__/verify.cpython-311.pyc`，未跟踪，也没有被忽略。

##### B. 未跟踪与已改文件的清点
- **已改（M）：开工前 8 个**：AGENTS、LOG、README、RESULTS、EBOHandbook、OrdinalNotationsGuide、ResearchHistory、importclosure.py。现在多了我改的 2 个已跟踪文件（BoundedCompletionStageWf、SkeletonAudit），共 10 个。
- **未跟踪：`probes/_build` 以外 3513 个文件**（`-uall` 计数）：
  - `OCF/Lean` 1353 个（Yi* 一族，mtime 11-11 至 11-18）
  - `OCF/Align` 319 个（Jia*、Yi*、K3Cap、K4Mono、TreeLevels 等，11-08 至 11-17）
  - `Survey/Reports-2026-11-12` 425 个，`-11-18` 397 个，`-11-19` 320 个，`-11-16` 250 个，`-11-24` 103 个，`-11-25` 69 个，`-11-11` 45 个，`-11-10` 10 个，`-11-23` 2 个
  - `Survey/` 顶层 165 个
  - `Survey/Lead` 37 个，`research_notes` 9 个，`Survey/reports`（小写）2 个
  - `scripts`：w5cand 2 个，w4klower 1 个，w4rebase 1 个，agentreport.py 1 个
  - `probes/STATUS-ARCHIVE-2026-11.md`、`.claude/settings.json`
- **按 mtime 看属于 11-24 与 11-25 的：285 个。** 构成是 `Survey/` 顶层 109 个（主要是约 100 个 W4* 的 .lagda.md，加上 W4CountableLower、W4Rebase、W5Candidate、GoalOdds、IdeaLedger），Reports-2026-11-24 的 103 个，Reports-2026-11-25 的 69 个，三个 materialize 脚本目录的 4 个。
  - 这个数已经扣掉了被我改动刷新了 mtime 的 RouteReview3（原为 11-17）和 RR3-Backward（原为 11-08）。
  - 其余约 3228 个是更早的遗留，以 11-11 至 11-19 为主。
- **判断（值得注意）**：AGENTS 里点名的核心记录（GoalOdds、IdeaLedger、RouteReview3、RR4、RR5、Retro、STATUS-ARCHIVE、agentreport.py）都未跟踪。三个定稿入口要靠 materialize 脚本才能编译，而这些脚本也未跟踪。

##### C. 记录之间不一致
- **首页"当前阶段"**：只有一段（第 12 行）。里面的 9 个链接都指得到。提到的定理名都能找到：`above-btbo`、`next-closure` 定义在 W4CountableLower；`steer-node`、`no-01`、`fallback-Z` 在 W4Rebase 里以别名重导出。LOG 里确有标题"2026-11-25　更正：换参数就是换基；查重漏了"。GoalOdds 最上面一份确是第五十五份。（已核实）
  - 判断：同一节"当前任务与目标"在这一段之后还有约 174 条加粗条目和若干加粗段落（第 13–247 行），看起来是累积下来的逐轮记录，和 AGENTS"首页只维护当前状态"的要求不一致。这要靠判断，所以没动。
- **首页、EBOHandbook、AGENTS 里指向的文件与小节**：全部存在（已核实）。逐条对过标题的有：AGENTS 的手册 §3.1、§5.2、§5.6、第 4 节，RouteReview3 §5.5–5.11、§5.9、§5.10，RR5 §2；README 的 RouteReview3 §5.5、§5.10–5.12，RR5 §5，Retro §3，RR11 §1，RR14 §3，EBOEndgame §8–§11、§13（含锚点）；手册的 RouteSeal §1、§4，RouteReview §2、§5，RouteReview2 §4，StallDiagnosis §4，ValueJudgeInst §4。
  - 唯一不在仓库里的是 Bedrock 的 `dev/cubical-agda-performance.md`，这是作者定的、有意放在仓库外。
- **台账编号**：V1–V638、U1–41、C1–10、P1–9、B1–8、F1–8、R1–7 都没有跳号，也没有重号，V 号按顺序排列。同一编号出现多行的只有 10 处，全部是"（状态更新）"行。（已核实）
- **GoalOdds**：第二份到第五十五份编号连续，新的在前，日期不增。没有"第一份"标题。另有 5 个不带编号的标题：第 7 行是格式说明，第 1001 行是 11-14 的附加问题，第 1323、1379、1429 行是 11-11、11-10、11-10 的早期三份。
- **留档里仍标"在跑"**：`Reports-2026-11-11/YiTail.md` 与 `YiBaseVal.md` 第 8 行仍写"在跑，尚未返回；本文件只有简报"。但同目录 README 的第 47 和 49 行写"已停"，LOG 第 7841 和 7857 行也写已停下、仍停着，回报不会来，除非续派。
  - 另外 Reports-2026-11-19、-23、-24、-25 四个目录没有 README 索引，此前各日的目录都有。

##### D. 规则的违例
- **文首超过 5 行**：11-24 与 11-25 新增的 103 个 literate 文件里，文首（第一个代码围栏之前、不含 `#` 标题）最多 2 行，没有超过 5 行的。文首最长的是 W4CountableLower，一行约 535 字。
- **只有导入语句的报告文件**：共 182 个 literate 文件的代码块里只有 import 和 open。其中未跟踪的 6 个，文字都不超过 10 行。11-10 以后加进仓库、文字又超过 10 行的，按首次提交日期算是 0 个。
- **个人信息（只报位置）**
  - `archive/probes/OCF/PastBTBO/SMB/FINDINGS.md` 第 3 行：本机用户名。
  - `probes/_build/YiCarryPlus-audit/` 的 4 个 cold.log 和 `YiWall-audit/` 的 4 个 cold.log，各 1 行；`YiK1b-audit/html-build.log` 4 行。内容都是含用户名的主目录路径。这些文件都在构建目录里，被忽略，未跟踪。
  - git 提交元数据里，600 个提交的作者邮箱不是 noreply 地址（不在仓库文件里，和手册 §3.12 有关）。
  - 判断，不算本仓库的个人信息：`Survey/CommunityCubical.md:28` 引的是第三方项目的本机路径；`research_notes/折叠难点跨领域启发调查/X4_self_generated_levels.md:51` 是公开邮件列表地址。
  - 主机名和电脑名的检索都是 0 命中。

##### E. 该整理但不属于机械修的
- **本机路径类剩余 17 行命中，都不改**
  - LOG:343 与 LOG:718 记的是"`/tmp/null`"事故。这是 LOG 旧段落，换掉也会改变事实。
  - EBOHandbook:112、114、240、475、497 和 EBOHandbook-proposals:58、116、134 说的是系统目录 `/tmp`、`/private/tmp` 本身的行为，不是具体路径。
  - `agentreport.py`:98–99 与 `handbook/extract.py`:46–50 是脱敏用的正则，功能上要用。
  - `Reports-2026-11-25/attachments/Hyg-简报.md:26` 是简报里描述检索模式的文字。
  - 不在检索模式里、也没改的：`scripts/handbook/run.sh:22` 里功能上要用的路径；LOG:2151 的 `/opt/homebrew/share/agda`（LOG 旧段落）。
- **范围外或留档里的断链，共 181 条命中。** 非留档 20 条，其中 1 条是上面 R2 那条公式误报：
  - `OCF/Align/TLOpsDW.lagda.md:597` 指向 `TLOpsDForce.lagda.md`，找不到这个文件。
  - `OCF/Align/LadderLabZNFWForce.lagda.md:7` 与 `LadderNFWForce.lagda.md:5` 指向 `Lab/NotFree.lagda.md`。实际文件在 `OCF/Free/Lab/`。
  - `OCF/Align/EboLean/OT/Order.lagda.md:5` 与 `Syntax.lagda.md:5`、`:168` 指向 `../ROADMAP.md`、`../DECISION.md`、`../Notation/…`。同名文件只在 `archive/` 里，而且有多个。
  - `scripts/monoport7`、`scripts/monoport9` 里的 5 个 `*_header.md` 共 11 条。判断：这些是拼进 `OCF/Align` 生成文件的模板，链接是按目标目录写的。
  - 留档 161 条：`Reports-2026-11-12/YiPF.md` 113 条，是早先脱敏把链接目标换成了 `<仓库>/…`；`Lead/回报-0*` 19 条，原因相同；`Reports-2026-11-16` 的 B8A、B8N、B9A、B9N、B10A、B10B、B11A、B11B 共 28 条，链接按 `Lead/` 目录写的；LEMAudit-回报 1 条。
- **没修的表格与围栏**
  - `RESULTS.md:532` 少了"档"一格，补什么内容定不了。
  - `OCF/Align/KcFold:74,76`、`LvTop:111,112`、`LvKt:108,109` 的竖线在 `$…$` 公式里。转义成 `\|` 在 LaTeX 里会变成 ‖，有歧义。
  - `OCF/Align/DiagK3One.lagda.md` 最后一个 ```agda 围栏没有闭合（第 126 行起到文件尾）。改它会改变 Agda 源文件、让接口失效，所以只列出。
  - 留档里的：`Reports-2026-11-16/ProbeP5a.md:15`、`README.md:291`、`RedefN1.md:105`，`Reports-2026-11-12/YiGT.md:384`（分隔行列数不对），`YiSL.md:124` 与 `YiRD.md:110`（表格后紧跟文字）。
- **其他**
  - RESULTS.md 没有 11-20 以后的任何条目，11-25 的两个定稿入口没有进成果目录。要不要补是内容决定。
  - 建议在 `.gitignore` 里加 `probes/_build/`（或 `_build/`）和 `__pycache__/`。这是改配置，不归我改。

#### 验收
1. **三个入口的编译**（materialize 都退出 0，按简报的命令在新的实验目录里跑，6G）：
   - W4CountableLower：退出码 0，日志里 33 行 Checking
   - W5Candidate：退出码 0，58 行 Checking，只有 UnsupportedIndexedMatch 警告
   - W4Rebase：退出码 0，26 行 Checking
   - Checking 的全是实验目录里抄出的模块。三个入口自己没有重新检查：`probes/_build` 里它们的接口被接受了，大概因为依赖的接口哈希没变。所以我又把三个入口的正文抄成改名副本 HygE1–3，只改模块名、补上库选项，放在工作目录里编译：退出码都是 0，每个副本各被 Checking 1 次。`src`、`probes` 里已有的模块用的是现有接口，不是冷编。
2. **改完后重跑第 1 类检索**：剩余 17 行命中，都是上面 E 里列的四种，都不改。
3. **git status --short**：和开工前（也和主审的 `hyg-status-before.txt`）相比，只多了两行 ` M`（BoundedCompletionStageWf、SkeletonAudit）。从开工到现在，仓库里变化的文件只有我改的 6 个，没有新增 .agdai，没有新增、删除或改名任何文件。

#### 没查到或没把握的
- 普通链接里的锚点（`#…`）只核了首页指向 EBOEndgame 的 5 个，别的没查。AGENTS 里提到的定理名没有逐个核。
- 表格检查只针对"表头下一行是分隔行"的 GFM 表格。没有分隔行的伪表格，以及跨行截断后又带竖线的行，可能漏查。
- "11-24、11-25 的工作"是按 mtime 分的，留档附件抄进来时可能带着旧的 mtime，归类会有误差。
- 竖线转义按 GitHub 的渲染规则判断：代码片段里的 `\|` 渲染出来是 `|`。别的渲染器（比如 zhihuify）没有验证。

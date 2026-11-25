# Cln：清理 .agdai、死代码死文件，修复悬空引用（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-25 08:26 至 08:48 |
| 工具调用 / agda 编译 (粗数) | 88 / 1 |
| token (usage 字段，按消息去重) | 输出 59854；新写入缓存的输入 199858；读缓存的输入 10767104；其余输入 176 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `Cln` (在 `<实验目录>/cln/`) |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它，再严格照做（它是自足的：范围、哪些可以直接删、死文件的判定条件、悬空引用怎么修、硬约束、验收与交付格式都在里面）：

<实验目录>/briefs/Cln.md

要点提示（以简报为准）：任务是在一个 Agda 研究仓库（<仓库>）里清理 .agdai 与构建产物、清理死代码死文件、修复悬空引用。最要紧的一条：仓库里约 3500 个文件没有进 git，未跟踪的文件删了找不回来，所以不可再生又未跟踪的文件一律不删，只列进候选清单；可再生的产物（.agdai、两个 _build 目录、__pycache__、未跟踪的 .DS_Store）直接删；被 git 跟踪的死文件要同时满足"没有被引用"和简报列的四种情形之一才删，并写明证据；没有被导入的叶子定理模块不是死文件。Agda 模块内部的死代码只列出不改。不碰 src/、archive/、.claude/、public/、tools/、AGENTS.md、记忆目录、各 attachments 目录、三个定稿入口及其脚本；留档目录里的文件不删，只允许修链接目标；不做任何 git 写操作。每一处删除与改动都记进清单文件。临时文件只放工作目录 <实验目录>/cln ；同时只跑一个 agda，堆上限 6G。最终消息就是回报原文，中文，区分已核实与判断。

## 回报原文

#### Cln 回报：清理 .agdai，清理死代码死文件，修复悬空引用

##### 结论
仓库清理已完成，三个定稿入口冷编都退出 0。共删了 5,882 个文件，腾出约 3.03 GB（3,025,612,278 字节）：
- 构建产物 5,874 个，其中 .agdai 5,001 个。
- `__pycache__` 里的 .pyc 1 个。
- 未跟踪的 `.DS_Store` 3 个。
- 被跟踪的死文件 1 个。

验收编译之后又清了一次，删掉新生成的 126 个 .agdai（85,328,647 字节）。现在仓库里没有 .agdai，也没有 `_build`。

改了 21 个文件，共 95 处：
- 4 个脚本里删了 6 个从未调用的函数。
- 17 个文件里修了 79 个链接目标，其中留档 15 个、OCF 模块 2 个。

没有做任何 git 写操作，Agda 代码一字未改。清单都在工作目录 `<实验目录>/cln/` 下：
- `Cln-deleted.tsv`
- `Cln-changes.tsv`
- `Cln-candidates.tsv`（130 条）

##### 一、.agdai 与构建产物（已核实）
- **构建目录**：删了 `_build/` 和 `probes/_build/` 下全部 5,874 个文件，共 3,025,579,733 字节，两个目录本身也删了。
  - .agdai 5,001 个，共 2,974,216,175 字节，清单里按目录汇总成 3 行。
  - 其余 873 个逐个列出：html 840 个，dot 12 个，日志 11 个，css 5 个，json 3 个，sha256 1 个，`YiCarryPlus-audit/libraries` 1 个。
  - git 不跟踪这些文件。
- **pyc**：删了 `probes/Survey/Reports-2026-11-18/__pycache__/verify.cpython-311.pyc`（9,688 字节），连同它所在的目录。
- **.DS_Store**：删了根目录、`probes/`、`probes/OCF/` 下未跟踪的 3 个，共 22,540 字节。
  - `src/.DS_Store` 和 `archive/probes/OCF/PastBTBO/.DS_Store` 也没被跟踪，但硬约束不许碰 `src/` 和 `archive/`，所以没删，列进了候选。
  - `public/` 下被跟踪的 3 个没动。

##### 二、死文件
**删了 1 个（已核实）**：`probes/OCF/Align/BoundedCompletionStageWfImport.lagda.md`，317 字节，被跟踪，可从提交 09edf10 恢复。
- (a) 没有被引用：在全仓库（除 `.git` 和它自己）按全名、`WfImport`、`StageWfImp`、"空导入"、"WfFsn导入" 检索，0 命中。删完后复查，仍然没有指向它的引用。
- (b) 代码只有 OPTIONS、模块头和一行 `import OCF.Align.WfFsn`，文首自述"没有数学或值验收结论"。

**做法**：我按文件名、不带扩展名的名字、模块名三种写法，在全仓库所有文本里检索（比简报列的记录范围更宽，也就更保守）。`probes/` 下 6,761 个文件里，没有被引用的只有 302 个，绝大多数在留档的 attachments 里。
- 被跟踪又没被引用的 Agda 模块有 6 个，只有上面这一个满足 (b)。
- 其余 5 个都是正常的叶子定理模块：`FrozenOutputNegInitial`、`InaccModulusAccept`、`InaccModulusWall`、`Uniform4Walk`，以及下面单说的 `BoundedCompletionStageWfLabel`。
- 被跟踪又没被引用的脚本有 16 个，都不满足 (b)。

**没删的**：
- `BoundedCompletionStageWfLabel` 文首自称草案，但 `LOG.md:2943` 和 `HANDOFF-2026-11-07.md:400` 用缩写 `StageWfLabel` 提到了它，(a) 不成立；它自述的失败是 251，不是 42。所以没删，也没编译。
- **判断，列进候选**：`probes/Survey/W4-EBO-独立审计材料.zip`（未跟踪，5.7 MB，是 11-24 的仓库打包副本），没有被引用，但 (b) 不严格成立。
- 内容逐字相同的重复有 6 组，Hyg 已经清点过。它们都在 attachments 或 scripts 里，而且每份都被引用，所以不算死文件。

##### 三、死代码
**脚本（已核实）**：4 个文件里删了 6 个函数，共 16 行。被删的名字在全仓库只出现在定义处，这 4 个文件也没有被按行号引用。
- `scripts/cmp.py`：`W_ONE`、`W_ONE_`、`wadd`
- `scripts/modulus/ebo.py`：`wlen`（e1 到 e7 用 `from ebo import *` 引入它，但都没用到）
- `scripts/scafladder/mkworld.py`：`subre`
- `scripts/tlops/portPsi.py`：`fix_blk`（恒等函数）

改后检查语法时，我用的是 Python 的 `compile()`，没有用 `py_compile`，因为后者会在仓库里写出 `__pycache__`。两者检查的东西相同，4 个文件都通过。

**有一处没删**：`mnot.py:74` 的 `inP` 也从未使用。但 CodeGuide、OrdinalNotationsGuide、MahloLevelRules 按行号引用了 `mnot.py:112-113`、`:113`、`:171`，删它会让这些行号错位。

**Agda（只列出）**：
- 判断为真正的死代码：
  - `Uniform5Head:43` 的 private `lνk`，以及它的两个机械克隆
  - `VerdictSpecEvid:42` 的 private `𝟎`
  - `JiaRound5:80-85` 的一段注释伪代码（判断：多半是有意的说明）
- private 块里没被使用的 `refl` 检验（d₀、keepΩ 等），我判断不是死代码：它们是类型检查时执行的有限测试，文中多处点名为"有限测试"。
- 补列 Hyg 报过的 `DiagK3One` 末尾围栏没有闭合。

##### 四、悬空引用
**Markdown 链接**：找到 180 处断链，修了 79 处，其余 101 处没修。

修了的 79 处，按依据分三种（已核实：修完重跑检查器，这 79 处都能解析）：
- **把 `<仓库>/…` 占位换算成相对路径，51 处**：
  - YiPF 26 处，Lead/回报-0* 共 19 处，LEMAudit-回报 1 处，回报-01-答疑 里带行号的 5 处。
  - 后者形如 `…agda.txt:443`，我改成了 `…agda.txt#L443`。
- **按原简报所在目录换算，28 处**：Reports-2026-11-16 的 B8A、B8N、B9A、B9N、B10A、B10B、B11A、B11B。
  - 每一行都逐字只出现在 `Lead/第X批/` 下的一份原简报里，按那份文件所在的目录换算。
- **按原文件目录换算，5 处**：`OCF/Align/EboLean/OT/Order`、`Syntax` 里的 5 个链接，现在指到 `archive/src/Mahlo/…`。
  - 这一行逐字只出现在 `archive/src/Mahlo/Inacc/` 下的原文件里。
  - 改动只在代码围栏外；围栏行的条数和位置没变，围栏内逐行相同（已核实）。

没修的 101 处，都列进了候选清单：
- YiPF 有 87 处指向 `<实验目录>` 或 `<初始实验目录>`，那是仓库外的目录，无从换算。
- `TLOpsDW:597` 指向 `TLOpsDForce`，同名文件 0 个。
- `LadderNFWForce` 和 `LadderLabZNFWForce` 里的 `Lab/NotFree`：唯一正确的目标是 `OCF/Free/Lab/NotFree`，但这两个文件是机械克隆，LOG:213 记着"重新生成逐字节相同"，改了会让这条记录失真。
- `scripts/monoport7`、`monoport9` 下的 11 个头部模板：链接是按生成文件所在的目录写的，在生成文件里能解析，改模板反而会让重新生成的文件断链。

**记录里提到的路径**：README、RESULTS、Survey 顶层各 md 和 EBOHandbook 里，没有可以修的。
- 不在仓库里的路径分三类：外部项目的路径（CodeGuide 等）；模块名或定理名的缩写列表（如 `LvRdIf/Pkg/World`）；仓库外实验目录里的文件（`rr3backward/`、`R12Scope.agda`、`results.tsv`、digest 输出等）。
- 光写文件名的提法，在仓库里都能唯一找到对应文件。

**Agda 导入**：共 71,328 处。
- 47,571 处在仓库内有对应文件。
- 1,339 处只由留档附件 `*.agda.txt` 满足，按简报这是有意的。
- Agda 自带的 `Agda.Primitive` 和 `Agda.Builtin.*` 不算悬空。
- 真正缺的有两类，只列出、没改：
  - `Mahlo.Inacc.*` 共 12 个模块，源文件只在 `archive/src/Mahlo/Inacc/` 下。导入它们的是 `WfScoutPull`、`WfScoutTau`、`WfTauNF` 和 `scripts/eboi/SetzerTest.agda`。
  - `YiLAB7Replay` 和 `YiLAB7Orbit` 被 20 个 `Survey/W4*` 模块导入，共 18 处。它们的源码只以代码块形式出现在 `Lead/指令-01.md`，没有附件，三个 materialize 脚本也不抄它们。三个定稿入口不导入它们。

##### 验收（都已核实）
1. **三个定稿入口**：materialize 后，按简报的命令用 6G 编译，都退出 0，日志里没有错误行。
   - W4CountableLower：156 行 Checking
   - W5Candidate：60 行
   - W4Rebase：27 行
   - 接口事先全删了，所以这是真正的冷编，三个入口自己都被重新检查了。
2. **围栏**：改过文字的 `.lagda.md` 只有 `EboLean/OT` 下的两个，围栏行的条数和位置都没变。
3. **两次清理**：第一次删了 5,874 个构建文件（其中 .agdai 5,001 个），共 3,025,579,733 字节；第二次删了 126 个 .agdai，共 85,328,647 字节。现在仓库里 .agdai、`_build`、`__pycache__` 都是 0。
4. **基线核对**：
   - 基线里有、现在没有的文件 5 个（pyc 1 个、.DS_Store 3 个、WfImport 1 个），全都在 `Cln-deleted.tsv` 里。
   - 内容变了的文件 22 个：21 个都在 `Cln-changes.tsv` 里，剩下的是 `AGENTS.md`，由另一路在改，按简报除外。
   - 新增 2 个文件，都是主审放进来的（attachments 下的 `Mem-简报.md` 和 `Cln-简报.md`）。
   - `git status` 与开工前相比只多了 7 行：1 行 ` D`（WfImport），6 行 ` M`（EboLean 两个，脚本四个）。

##### 没有把握的地方
- **`#LN` 写法**（判断）：把 `:N` 行号改成 `#LN`，是按 GitHub 的写法定的，别的渲染器没验证。
- **"按原简报所在目录换算"这条规则**（判断）：依据是"该行逐字只出现在一份原文件里"，我认为算得上"唯一可确定"，请主审确认。
- **死文件的检索**：按字母数字分词，所以缩写提法会漏，比如 `StageWfLabel`。删除的那一个文件，我另外补查了几种缩写。其余文件因为没有删，没有逐个补查缩写。
- **被修改的未跟踪文件**：15 个留档文件改前做了备份，放在 `…/scratchpad/cln/backup/`。EboLean 的两个文件被 git 跟踪，没有另做备份。

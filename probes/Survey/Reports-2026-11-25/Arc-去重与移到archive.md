# Arc：重复附件去重；编译不过的草案移到 archive（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-25 09:27 至 09:54 |
| 工具调用 / agda 编译 (粗数) | 61 / 0 |
| token (usage 字段，按消息去重) | 输出 40364；新写入缓存的输入 167036；读缓存的输入 8003822；其余输入 146 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `Arc` (在 `<实验目录>/arc/`) |

## 简报原文

你的任务简报全文在这个文件里，请先完整读它，再严格照做（它是自足的：两件清理各自的判定条件与做法、编译命令、硬约束、收尾与交付格式都在里面）：

<实验目录>/briefs/Arc.md

要点提示（以简报为准）：任务是在一个 Agda 研究仓库（<仓库>）里做作者定的两件清理，只做这两件。一、六组内容完全相同的重复附件各删一份，留被脚本读取或引用多的那份，并把全仓库指向被删文件的链接目标、反引号里的路径、脚本里的读取路径改到留下的那份。二、把导入已归档 Mahlo 而编译不了的三个模块，以及文首自称草案且实测编译不过、又没有被别的模块导入的模块，原样移到 archive/probes/ 下相同的相对路径（只移不删，内容不改），再把指向它们的 Markdown 链接目标改到新位置；每个候选都要实测编译并记下退出码。不碰 src/、.claude/、AGENTS.md、记忆目录、三个定稿入口及其脚本；不改 Agda 代码与任何结论或措辞；不做任何 git 写操作，移动与删除用普通的文件操作；每一处都记进清单文件。结束前清掉重新生成的 .agdai 与 _build。临时文件只放工作目录 <实验目录>/arc ；同时只跑一个 agda，堆上限 6G。最终消息就是回报原文，中文，区分已核实与判断。

## 回报原文

#### Arc 回报：重复附件去重，编译不过的草案移到 archive/

##### 一句话结论
两件都做了，硬约束都守住了。
- **第一件**：六组重复附件各删了一份，共 6 个文件，改了 8 处引用。
- **第二件 (a)**：三个导入已归档 Mahlo 的模块一个都没移，因为都不满足简报的两条前提。
- **第二件 (b)**：自称草案、实测编译不过、又没有被导入的 4 个模块，原样移到了 `archive/probes/OCF/Align/`。

没有做任何 git 写操作，Agda 代码一字未改。清单在 `<实验目录>/arc/Arc-changes.tsv`（18 条加表头），编译日志与 `results.tsv` 在同一目录。

##### 一、重复附件（已核实）
六组都用 sha256 核过，确实逐字节相同。对全仓库（含 src、archive，不含 .git、_build、.claude）另做了一次全量查重，结果恰好就是这六组，没有别的重复。删掉的 6 个文件都被 git 跟踪，可以从 HEAD 恢复。

| 组 | 留下 | 删掉 | 依据 | 改的引用 |
|---|---|---|---|---|
| KOpPow | `Reports-2026-11-24/attachments/M4b-KOpPow.agda.txt` | `M4-KOpPow.agda.txt` | w4klower、w5cand 两个 materialize.py 读 `M4b-` | 0 |
| KIface | `M2v2-KIface.agda.txt` | `M2-KIface.agda.txt` | materialize.py 读 `M2v2-` | 1（`W4-可数层号定理-纸面.md:107` 的反引号路径） |
| B10Join | `Reports-2026-11-16/attachments/B10Join-B10Join.agda.txt` | `Lead/attachments/B10Join.agda.txt` | `Reports-2026-11-18/verify.py` 用 glob `B10Join-*` 读 R16 那份 | 4 处，见下 |
| B11Join | `Reports-2026-11-16/attachments/B11Join-B11Join.agda.txt` | `Lead/attachments/B11Join.agda.txt` | 同上 | 2 处，见下 |
| StandardOmega-Sb2 | `scripts/scafladder/` 那份 | `scripts/uniform5/` 那份 | `scafladder/mkworld.py` 第 15、17 行从本目录读 | 合在下一行 |
| SystemOmega-Sb2 | 同上 | 同上 | 同上 | 1（LOG:82） |

B10Join、B11Join 的 6 处引用：
- **Markdown 链接 2 处**：`Lead/回报-04.md:3`、`Lead/指令-04.md:7`，目标都改成 `../Reports-2026-11-16/attachments/B10Join-B10Join.agda.txt`，已核实能解析。
- **反引号路径 4 处**：`Reports-2026-11-16/README.md:335`、`:344`，`Lead/协调-03.md:41`，`Lead/协调-04.md:51`。

`git diff --word-diff` 核过，8 处的改动都只是路径字符。脚本一个没改，因为留下的都是脚本读的那份。改完再检索，没有指向被删文件的引用。只剩 4 处描述重复本身的文字，我没改：Hyg 回报第 54–56 行、`Cln-candidates.tsv:3`、`Cln-changes.tsv:20`、留档的 `Arc-简报.md:12`。

**判断，请你看一下：**
- README:335/344 和 协调-03/04 原句是 "源码存在 A 与 B" 或 "（另存 B）"。按规则改完后，两处路径指的是同一个文件，措辞没动。
- LOG:82 原文 "补丁草稿 `Survey/scripts/uniform5/`" 是目录路径，不是文件路径。被删的两份就是那里的补丁草稿，所以我按 "指向被删文件的引用" 改成了 `Survey/scripts/scafladder/`。不同意的话，回退这一行即可。
- uniform5 删空后，我 rmdir 了这个空目录。它不是文件，git 不跟踪目录。

##### 二(a)、导入已归档 Mahlo 的三个模块：都没移（已核实）
简报要求退出 42、日志指向缺 Mahlo 源文件，并且没有别的模块导入它们。三个模块各缺至少一条：

| 模块 | 退出码 | 首个错误 | 导入者 | 结论 |
|---|---|---|---|---|
| `WfScoutTau` | `exit=42`（41 秒） | `WfScoutTau.lagda.md:25.1-110: error: [FileNotFound] Failed to find source of module Mahlo.Inacc.Syntax` | `WfScoutPull`、`WfTauNF` | 被导入，不移 |
| `WfScoutPull` | `exit=251`（444 秒） | 堆耗尽，6144 MB；最后一行 Checking 是依赖 `OCF.Align.ScafLadderZUniform5Psi`，没走到 Mahlo 导入 | `WfTauNF` | 退出码不对，也被导入，不移 |
| `WfTauNF` | `exit=251`（76 秒） | 堆耗尽；最后一行 Checking 是依赖 `OCF.Align.ScafLadderQRel` | `WfFsn` | 退出码不对，也被导入，不移 |

导入链比预想的长。从这三个往上，传递导入者共 12 个：
- `WfFsn`
- `LambdaTarget`、`EboLeanCmp`、`LambdaCountableTarget`、`EndLowAccept`、`EndLow`、`HtValAcceptE`
- `BoundedCompletionStageWf`、`BoundedCompletionStageWfLabel`、`BoundedCompletionStageWfOpaque`、`BoundedCompletionStageWfEbo`、`BoundedCompletionStageWfBridge`

`WfFsn` 文首写着编译时要把归档拷贝加进 `-i`，`EndLow:76` 写了做法。判断：照那个做法，这一族原本是可以编译的；只把三个模块移走，这条路就断了。所以三个都不动，交你定。

##### 二(b)、自称草案的模块（已核实）
检索 `probes/` 下所有 `.lagda.md` 的文首，关键词有：草案、草稿、废弃、作废、未完成、编译不过、堆耗尽、251 等。命中 113 个，绝大多数说的是任务没完成，或别的文件、别的试验。真正自称本模块是草案或作废的有 12 个，没超过上限。

**移走的 4 个**：都没有导入者。移前移后 sha256 相同，与 `git show HEAD:` 逐字节比对也相同。也没有任何 Markdown 链接指向它们，所以不用改链接。

| 模块 | 退出码 | 首个错误 |
|---|---|---|
| `CrossNestedBuildNecessary` | `exit=251`（193 秒） | 堆耗尽；最后一行 Checking 是 `OCF.Free.Base` |
| `LambdaTarget` | `exit=251`（112 秒） | 堆耗尽；最后一行 Checking 是 `ScafLadderQRel` |
| `BoundedCompletionStageWf` | `exit=251`（91 秒） | 同上 |
| `BoundedCompletionStageWfLabel` | `exit=251`（95 秒） | 同上 |

判断：这 4 个的堆耗尽都发生在依赖模块里，不在它们自己身上。后三个还要经 `WfFsn` 导入 Mahlo，即使不爆堆也会退出 42。这与它们文首自报的 251 一致，按简报的口径都算编译不过。

另外，`ScafLadderQRel` 在 6G 冷编时有 4 次都卡在这里，只是观察，没有深究。

**没移的 8 个**：
- 编译通过：`ColimWNegDraft`（`exit=0`）、`YiLglAllReport`（`exit=0`）。
- 被导入，没编译：
  - `CrossNestedIf`，导入者是 `CrossNestedBuildNecessary`。后者现已移走，它在 `probes/` 里已经没有导入者，可以下一轮再定。
  - `AdmWNegDraft`，导入者是 `AdmWNeg`。
  - `TopDown`，有 5 个导入者。
  - `TreeLevelsO1Chain`，有 2 个导入者。
  - `LadderLabZTopDown`、`ScafLadderZTopDown`，各有 4 个导入者，而且是 mkworld 生成的机械克隆。

**没列为候选的（判断）**：`YiH2Ref`、`YiWYCut` 文首说的堆墙在别的试验文件上；`CrossMHighSeedAccept` 后来已在 12G 下退出 0。

##### 验收（已核实）
- **构建产物**：结束前删了新生成的 `_build` 和 `probes/_build`，里面只有 140 个 .agdai，都没被跟踪。现在仓库里 .agdai、`_build`、`__pycache__` 都是 0。
- **`git status --short` 对上清单**：
  - ` D` 10 行：删掉的 6 个，加移走的 4 个。
  - ` M` 7 行：改引用的 7 个文件，numstat 共 8 行增 8 行删。
  - `??` 一项是 `archive/probes/OCF/Align/`，新建的目录，里面就是那 4 个文件，`archive/` 里原有的文件没动。
  - 另一项 `.claude/` 是开工前就有的。
- 9 次编译的日志首行都不是 LibraryError，同时只跑过一个 agda，堆上限 6G。

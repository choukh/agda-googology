# 合并副本，折叠与引理按表参数化（工程） (YiPM)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 改派外部模型（原话 “额度告急, 从现在开始派发外部模型, 请给每路都写任务breif并给出路径, 以便我直接复制”）；作者转发 |
| 前缀 | `YiPM` |
| 回报 | 2026-11-14 已返回；本会话主审独立复核，见文末 |

## 简报原文（本机路径换成占位）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

## 作者的决定（2026-11-14，选项原文）
- 本路（选项原文）："(3) 工程：合并副本"，说明是 "折叠对 '那一行的写法' 参数化，保持引理与下降引理各写一次，F2 对照块同样参数化；只建新文件"。
- AGENTS："同类引理以不同名字第二次出现时, 合并成一条并写进接口"。台账 `probes/Survey/IdeaLedger.md` V163。
- 本路是工程，不改任何数学结论，不改已有文件，不碰定义（树、折叠、合法性）的数学内容。

## 现状（主审复核过的编译事实）
- **精简块一侧**：折叠 `YiTBRow.ψ` 已经对表 `r : Rb ℓ` 参数化：空表 `rb-no` 时那一行逐字是原行（`YiTBRow.row-no`），新主线配 `YiMTTab.rbᶻ`。但保持引理按折叠各抄了一份：
  - `YiRBFam`（兄弟孩子折叠 `YiRBSib`）；`YiTBFam`（比较表折叠，逐字副本）；`YiHCFold`、`YiHCBridge`、`YiHCLim`（遗传封闭的关系，`YiRBSib` 折叠）；`YiLTFold`、`YiLTLim`、`YiLTKid`（新主线折叠，搬自 `YiHC*`、`YiKPRel`，约 500 行）。
- **F2 一侧**：原 F2 折叠 `YiLegFold`；对照块 `YiVTFold`（只改那一行的四个子句：`ψs`、`nzs`、`monos` 的 `◃u` 与 `◃c`；另加表 `tbᶠ`）。下降引理一族抄了 24 份 `YiVT*` 副本（约 4100 行），其中 16 份只换了导入，8 份有 "改:" 注释的手改。回报 `probes/Survey/Reports-2026-11-12/YiVT.md`，§5 列了手改处；执行方建议 "把 F2 的折叠改成对表参数化的一个文件，原 F2 是空表实例"。
- 关系：`YiVTRel`（新主线折叠与 `YiVTFold` 逐层相关，脚本自 `YiSMRel` 改写）。

## 要做的（按序；只建新文件）
0. **最小实例检查**，在临时目录（纯 `.agda`）：
   - 写一个对 F2 表参数化的 F2 折叠 `ψs[tb]`（照 `YiVTFold` 的那一行，表作参数）。
   - 检查 `YiLegFold.ψs` 与 `ψs[空表]`、`YiVTFold.ψs` 与 `ψs[tbᶠ]` 在若干闭的输入上 `refl`，或给出逐点相等的证明。
   - 若参数化让停机或堆用量出问题（例如超过 8G），就停下回报。
1. **F2 一侧**：新建参数化折叠，把 `YiVT*` 副本里依赖折叠的下降引理（`ψs-⊵`、`ok-d*`、`reach`、`reach³`、`reachG` 一族，及 16 份只换导入的）写成对表参数化的一份（模块参数或记录），再给出两个实例：空表（对应原 F2）与 `tbᶠ`（对应对照块）。8 份手改过的，若依赖回退行的输出形状，单列，说明哪些能参数化、哪些不能。
2. **精简块一侧**：把保持引理（`Qu`、`Self.PF`、`LF`、`chain`、`sΩ-LF`、`LFω` 一组、`LF¹`）对 `YiTBRow.ψ` 的任意表陈述一份；Ω 形状层号上需要对表加的条件（例如条目与关系相容）写成参数，并给出 `rb-no` 与 `rbᶻ` 两个实例。
3. **验证不丢结论**：在新文件里，用参数化的版本重得几条代表性的已有结论：`YiVTANLim.tω≼EBOᴿ`（新主线终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))），`YiLTLift.lift-lim`，`YiHCPlus.crit₊` 的新折叠版本（若 `crit₊` 依赖兄弟孩子折叠特有的东西，说明并跳过）。
4. **账**：交一张表，列出哪些已有文件今后可以由参数化版本的实例代替（只列，不删，不改），以及代替后省掉的行数（用代码行计）。

**纪律**：已有引理先检索再写；不改任何已有文件；若参数化要求改树、折叠、合法性的数学内容（不只是加参数），停下回报；停止条件触发时先停下回报。

## 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiPM`（模块名 `OCF.Lean.YiPM…`）。不碰 `src/`、`archive/`，不碰并行的另两路前缀 `YiSS`、`YiTS`。参数化的折叠文件文首标明 "参数化（工程），数学内容与 <来源> 相同"；验收文件标明 "验收文件"。参数化的精简块折叠若作定义候选，用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包干净。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库的 .agda-lib 路径>
  <cubical 的 .agda-lib 路径>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - 同时只跑一个 agda，堆上限 8G（另两路也在编译）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：`YiMTHit` 一类冷编约 7G；参数化后若某个文件超过 8G，拆小或停下回报。
- 不在你的临时目录与你前缀的新文件之外删除任何东西，不 `pkill`，不装包，不提交，不推送。
- 查签名用检索，不整篇读大文件；搬运时可以写脚本，脚本留在临时目录，不进仓库。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步不成立。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

## 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；F2 一侧、精简块一侧、重得结论各到哪一步；可代替的文件与省掉的行数表；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容。

## 本会话主审复核（2026-11-14）

34 件独立删接口、8G 冷编均为 0，日志各只有自身 Checking；已核任意表与最小表的陈述范围、非空终点实例和 8 件专用条件。34 件由临时生成脚本隔离重建后逐字节相同。16 对证明的局部行数账独立重算为 5404 → 2846，候选省 2558；当前没有删除旧源码。

本会话按作者指令用 Codex 协作工具直接派发三路；未采集可核对的 token 用量。回报原文仅机械替换本机路径、降低标题层级，保留阶段性统计与原判断；后续确认以本节为准。

临时源码留档：[第 0 步完整参数化块与六个闭输入](attachments/YiPM-PM0.agda.txt)。生成脚本按简报留在实验目录，没有加入仓库。

## 回报原文（Codex 协作子智能体）

### YiPM 回报：合并副本，按表参数化

#### 1. 判决与范围

对纲领与目标的意义：这是验收工程的收拢。F2 的同一互递归块与保持、下降证明已量化任意比较表，空表和最小表共用证明。没有改树、折叠各行的数学公式或合法性；没有增加序数强度，也没有把这批验收文件当作“树自足”的定义成果。

第 0 步：临时纯 Agda `PM0.agda` 首编退出码 0，30 分钟内完成。完整 F2 互递归块把四处 `tbᶠ` 查询换成参数 `tb`，停机通过；六条闭输入 `refl` 通过：两边分别在 `zero`、`suc zero`、实际经过 Ω 形状层号指定孩子那一行的 `uK` 上一致。此项按有限测试交付；没有证明两套递归函数对所有输入逐点相等。仓库 `YiPMInst` 保留六条测试，并给出任意输入的 `empty-row` 定理。

F2 一侧：
- `YiPMFold.F tb` 为单份参数化折叠、非零、单调；`YiPMLSFold.F tb` 的 `ψs-⊵` 及 `ok-d*`、`YiPMEVReach.F tb` 的 `reach`、`YiPMPHEnd.F tb` 的 `reach³`、`YiPMANReach.F tb` 的 `Reach.reachG` 都对任意表编译。16 件原“只换导入”的证明各写一次。
- `YiPMInst.Empty`、`Minimum` 为两个实例命名空间，各引用同一份参数化证明。原 F2 与空表的关联交了闭输入测试和任意输入的回退行定理；未交全域函数相等。
- 对表的数学要求只有 `Table` 中返回的路径证据；没有加全局可判定比较。

精简块一侧：`YiTBFam`、`YiLTFold`、`YiLTLim`、`YiLTKid` 本来已对任意 `Rb` 量化，故 `YiPMThin` 复用这些证明，未再克隆。`For rows` 的 `Qu`、`Self`、`Limit.Fold`、`Limit.Uniform`、`Ω`、`Lift` 插入所选表；`Finite` 仍是任意表的原始接口，保留显式 `r` 参数，未固定到 `rows`。`Empty` 与 `Minimum` 分别选 `rb-no`、`rbᶻ`。

Ω 入口的准确范围：只有 `ℓ¹ = tw 1` 的 `YiLTKid.Top`，经 `Kidˢ` 实例；`LF¹` 仍要求 `Pw`、`GB¹`、`Sp` 等原条件。`Kid` 的 `Pc`、`pz`、`pk`、`gb⊴`、`foldᶜ` 沿用原接口，并由 `Kidˢ` 实填。没有证任意 Ω 形状层号的保持，也没有消除 `Lift₁`。ℕ 极限接口仍要求孩子为有限读回层号、相邻路径的规范证据，以及一致目标路径的 `Pt` 读回证据。

代表结论：
- `YiPMMinANLim.tω≼EBOᴿ` 及无悬空实例 `instω` 已从新参数化最小表折叠、相关关系、闭项相关与下降族重证，实际依赖链是 `YiPMFold.F tbᶠ → YiPMMinRel → YiPMMinTw → YiPMMinEVEnd/PHEnd/ANEnd/ANLim`，没有重导 `YiVTANLim` 的终点定理。结论是已有 `tω` 参照的下界，强度未提高；本轮未另证它在 Ω 算术下的上下界读法。
- `YiPMThin.Minimum.Lift.lift-lim`、`Empty.Lift.lift-lim` 从原本已任意表的 `YiLTLift.Inst` 复用，表选择经过统一接口。
- 完整 `YiHCPlus.crit₊` 新折叠出口依赖旧 `YiRBCrit.gˢ` 与 `atω`，按简报允许跳过；没有把新折叠的分支核心冒称为完整 `crit₊`。没有另写该分支核心。

##### 8 件手改的逐项处理

| 来源 | 任意表已编译的部分 | 保留的条件或专用范围 |
|---|---|---|
| `YiVTLSFold` | 全部保持与下降，含 `ψs-⊵` 按表三支 | `tb : Table` 任意 |
| `YiVTT2Frame` | `ok-dW`、`up-lower`、`eqk`、链等；`fallback` | `fallback` 明带 `tb k h c c′ ≡ nothing`；`flat-lim` 两表有限测试移到 Inst，原空表 `β₁-form` 也在 Inst |
| `YiVTEVTw2` | 所用下降在通用接口 | `YiPMMinEVTw2` 固定最小表；`compβ` 仍使用孩子为 ℕ 极限的 `rowG` |
| `YiVTEVEnd` | `reach` 等用通用接口 | `YiPMMinEVEnd` 固定最小表；具体 `hi1`、`c₁`、`path₂` 不推广 |
| `YiVTPHEnd` | `Lo³`、`AtThree`、`reach³` 抽到 `YiPMPHEnd.F tb` | `YiPMMinPHEnd` 固定最小表，保留 `path₃`、`hi1` 与终点出口 |
| `YiVTANEnd` | 记号参照与 `AtN` 抽到 `YiPMANEnd.F tb` | `YiPMMinANEnd` 固定最小表，保留 `G/shape/gk/pathN`、`hi1` 与出口 |
| `YiVTANLim` | 极限出口依赖所给有限站下界 | 此实例的有限站下界来自最小表 `YiPMMinANEnd` |
| `YiVTTWEnd` | 所用下降用通用接口 | `YiPMMinTWEnd` 固定最小表，具体 `path₁`、`hi1` 不推广 |

未把后六项称为“不能参数化”：本轮只交以上已编译范围，没有否定定理。

##### 问题表

| 问题 | 位置 | 档 |
|---|---|---|
| 两套原函数与新函数的全域逐点相等未交；六个闭例及回退行已交 | `YiPMInst` | 有限测试 / 编译定理分别标明 |
| 任意 Ω 形状层号的统一保持没有推出 | `YiPMThin.For.Ω` 仅 `tw 1` | 陈述范围 |
| 六个具体路径/终点实例固定最小表 | `YiPMMin*` | 编译定理，表固定 |
| 完整新折叠 `crit₊` 未交 | 旧 `gˢ`、`atω` 出口 | 未做，按简报允许跳过 |
| 尚未迁移或删除旧文件 | 全仓库 | 工程事实；当前净删 0 行 |

#### 2. 文件、冷编与内存

34 件全是新增 `probes/OCF/Lean/YiPM*.lagda.md`。代码行口径：Agda 代码块内非空且非整行 `--` 注释的行，含选项、模块、导入与签名；不是依赖切片。内存列是 `+RTS -s` 的 maximum residency，字节，非 RSS。

前 32 件冷编由主审独立删当前模块接口完成，已逐件确认退出码 0、只有自身 Checking；Thin/Inst 列本路自行删接口冷编结果（均 0、只有自身 Checking），待主审独立复核。

| 文件 | 代码行 | 冷编退出码 | max residency (bytes) |
|---|---:|---:|---:|
| `YiPMTable` | 50 | 0 | 157460672 |
| `YiPMFold` | 296 | 0 | 250316224 |
| `YiPMLSFold` | 681 | 0 | 2371999488 |
| `YiPMMEAnchor` | 207 | 0 | 700240304 |
| `YiPMLSTw1` | 119 | 0 | 675912392 |
| `YiPMMEStep` | 84 | 0 | 702626408 |
| `YiPMMWPre` | 119 | 0 | 729555352 |
| `YiPMEBShape` | 66 | 0 | 721292304 |
| `YiPMLSBtbo` | 194 | 0 | 844211704 |
| `YiPMT2Desc` | 119 | 0 | 830892040 |
| `YiPMPHBase` | 118 | 0 | 699045112 |
| `YiPMANFam` | 219 | 0 | 640185256 |
| `YiPMEBBtbo` | 111 | 0 | 962664456 |
| `YiPMT2Frame` | 116 | 0 | 864298512 |
| `YiPMEXRow` | 87 | 0 | 1199109608 |
| `YiPMEVReach` | 96 | 0 | 1344864088 |
| `YiPMPHCtx` | 375 | 0 | 1387585152 |
| `YiPMANKp` | 235 | 0 | 1173598576 |
| `YiPMPHEnd` | 122 | 0 | 1332949592 |
| `YiPMANLv` | 598 | 0 | 1276925152 |
| `YiPMANReach` | 49 | 0 | 1269109624 |
| `YiPMANEnd` | 125 | 0 | 1334183696 |
| `YiPMMinRel` | 401 | 0 | 1846771336 |
| `YiPMMinEmb` | 60 | 0 | 1155026712 |
| `YiPMMinTw` | 31 | 0 | 1069472568 |
| `YiPMMinHi` | 38 | 0 | 1104796352 |
| `YiPMMinEVTw2` | 62 | 0 | 1248626824 |
| `YiPMMinEVEnd` | 84 | 0 | 1367880232 |
| `YiPMMinPHEnd` | 66 | 0 | 1356298896 |
| `YiPMMinTWEnd` | 56 | 0 | 1270235744 |
| `YiPMMinANEnd` | 101 | 0 | 1364182296 |
| `YiPMMinANLim` | 117 | 0 | 1390196408 |
| `YiPMThin` | 51 | 0 | 1388812144 |
| `YiPMInst` | 124 | 0 | 1294583576 |

##### 可替代与行数账

以下 16 组是整份保持/下降证明的候选替代：`Yi<后缀>` 与 `YiVT<后缀>` 改用 `YiPM<后缀>.F empty/tbᶠ`。迁移消费者后仍须复核；本轮没有删旧文件。每组的新成本另计三个实例入口代码行（一条导入、两条模块别名），两个共同命名空间头另计 2 行。此局部账不包含共同折叠、表、测试、相关关系或精简块接口，因此不当作整个导入闭包的节省。

| 两份旧文件的后缀 | 旧两份代码行 | 参数化文件代码行 | 两个实例入口 | 局部可省 |
|---|---:|---:|---:|---:|
| `LSTw1` | 230 | 119 | 3 | 108 |
| `EBShape` | 122 | 66 | 3 | 53 |
| `LSBtbo` | 378 | 194 | 3 | 181 |
| `EBBtbo` | 208 | 111 | 3 | 94 |
| `MEAnchor` | 408 | 207 | 3 | 198 |
| `MEStep` | 160 | 84 | 3 | 73 |
| `T2Desc` | 228 | 119 | 3 | 106 |
| `EXRow` | 166 | 87 | 3 | 76 |
| `MWPre` | 230 | 119 | 3 | 108 |
| `EVReach` | 178 | 96 | 3 | 79 |
| `PHBase` | 226 | 118 | 3 | 105 |
| `PHCtx` | 734 | 375 | 3 | 356 |
| `ANFam` | 428 | 219 | 3 | 206 |
| `ANKp` | 452 | 235 | 3 | 214 |
| `ANLv` | 1176 | 598 | 3 | 575 |
| `ANReach` | 80 | 49 | 3 | 28 |

16 组局部合计：5404 → 2796+48+2 = 2846 行，候选净省 2558 行。共同的参数化折叠、表、有限测试和相关证明另计，没有混入这个差额。

| 其余来源 | 已给替代 | 行数处理 |
|---|---|---|
| `YiLSFold` / `YiVTLSFold` | `YiPMLSFold.F empty/tbᶠ` | 旧 1351 行；新 681 行，实例入口另计 3 行，局部候选省 667 行 |
| `YiT2Frame` / `YiVTT2Frame` | 通用 `YiPMT2Frame` + `YiPMInst` 两表形状测试 | 测试另列，未给整件净省数 |
| `YiPHEnd` / `YiVTPHEnd` | `YiPMPHEnd.F tb` 的下降前缀 + 专用尾部 | 旧专用尾部仍须留，未给整件净省数 |
| `YiANEnd` / `YiVTANEnd` | `YiPMANEnd.F tb` 的 AtN 前缀 + 专用尾部 | 同上 |
| `YiEVTw2` / `YiVTEVTw2` | 最小表端 `YiPMMinEVTw2` | 原空表的专用端未搬，未给净省数 |
| `YiEVEnd` / `YiVTEVEnd` | 最小表端 `YiPMMinEVEnd` | 同上 |
| `YiANLim` / `YiVTANLim` | 最小表端 `YiPMMinANLim` | 同上 |
| `YiTWEnd` / `YiVTTWEnd` | 最小表端 `YiPMMinTWEnd` | 同上 |
| `YiRBFam/YiTBFam`、`YiHC*/YiLT*` | `YiPMThin` 统一已任意表的接口入口 | 复用旧证明；本轮未把旧模块拆出，未计省数 |

`YiLegFold` 的 Base、kp 等仍被导入，不能把整个文件列为可删除。`YiPMMinRel/Tw/Emb/Hi` 是使新参数化折叠的具体出口接回主线所需的验收支持，未把这些成本遗漏成 0。

#### 3. 定理表与逐字陈述

以下各签名按源文件逐字提取。F2 的陈述都在 `module F (tb : Table)` 内；`tb` 任意，除非表明 Min 文件。白话与条件紧随签名，所有一般项为编译定理。


##### `YiPMTable.Table`

```agda
Table : Set
```

返回一个实际路径证据或没有条目的表。 档：编译定理。


##### `YiPMFold.ψs`

```agda
    ψs : (ℓ : L) → Ev ℓ → Rt ℓ → Base ℓ → (j : L) → j ≤ ℓ → (β : Tr j) → j ⊢ zero ◃ β → Tr ℓ → Tr j
```

折叠的表作模块参数，树和行公式不变。 档：编译定理。


##### `YiPMFold.nzs`

```agda
    nzs : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
        → j ⊢ zero ◃ ψs ℓ ε ρ B j w β nβ x
```

参数化折叠仍非零。 档：编译定理。


##### `YiPMFold.monos`

```agda
    monos : (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) {x y : Tr ℓ}
          → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε ρ B j w β nβ x ◃ ψs ℓ ε ρ B j w β nβ y
```

参数化折叠保持树序。 档：编译定理。


##### `YiPMLSFold.ψs-⊵`

```agda
  ψs-⊵ : (ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) (j : LF) (w : j ≤ ℓ) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr ℓ)
    → j ⊢ β ⊴ ψs ℓ ε ρ B j w β nβ x
```

折叠不低于起点。 档：编译定理。


##### `YiPMLSFold.ok-dS`

```agda
  ok-dS : ∀ {a} (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) → OKB (suc a) B → (t : Tr (suc a))
    → OKB a (dS a ε ρ B t)
```

底的条件经后继孩子下降。 档：编译定理。


##### `YiPMLSFold.ok-dL`

```agda
  ok-dL : (g : ℕ → LF) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) → OKB (lim g) B → (n : ℕ) (t : Tr (lim g))
    → OKB (g n) (dL g ε ρ B n t)
```

底的条件经 ℕ 极限孩子下降。 档：编译定理。


##### `YiPMT2Frame.ok-dW`

```agda
  ok-dW : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → OKB (Ωₗ k h) B
    → (c : Tr k) (t : Tr (Ωₗ k h)) → OKB (h c) (dW k h ε ρ B c t)
```

底的条件经 Ω 形状的指定孩子下降。 档：编译定理。


##### `YiPMT2Frame.fallback`

```agda
  fallback : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : LF)
    (c′ : Tr k) (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
    (e : h c ⊢ zero ◃ y)
    → tb k h c c′ ≡ nothing   -- 改: 原行只在表里没有条目时出现
    → ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
    ≡ ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (ψ₀ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) y)
```

只有表明确无条目时才有回退行公式。 档：编译定理。


##### `YiPMEVReach.reach`

```agda
  reach : ∀ {ℓ} → two ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo ℓ ε ρ B
```

带层号路径、OKB、Hi 的下降。 档：编译定理。


##### `YiPMPHEnd.reach³`

```agda
  reach³ : ∀ {ℓ} → three ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo³ ℓ ε ρ B
```

同一机制到第 3 层的参照。 档：编译定理。


##### `YiPMANReach.reachG`

```agda
    reachG : Anchor → ∀ {ℓ} → n₀ ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → LoG ℓ ε ρ B
```

给任意起始层的 Anchor 后沿路径下降。 档：编译定理。


##### `YiPMInst.empty-row`

```agda
empty-row : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
  (c′ : Tr k) (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
  (e : h c ⊢ zero ◃ y)
  → E.ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
  ≡ E.ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (E.ψ₀ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) y)
```

空表在所有这类输入上给原回退公式。 档：编译定理。


##### `YiPMThin.Qu`

```agda
  Qu : ∀ {t} (o : Ok zero) (B : Base zero) (w : zero ≤ zero) (b : Tr⁺ zero)
     → M⁰ (ψᴺ 0 t) (proj₁ b) → ∀ {s y} → M⁰ s y
     → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ zero o (rows zero) B zero w b y))
```

统一 Rows 插入第 0 层所选表。 档：编译定理。


##### `YiPMMinANLim.tω≼EBOᴿ`

```agda
tω≼EBOᴿ : (h : HC tω) → R2.Rt h ≼ readRW EBOᶻ
```

最小表参数化族重得已有终点下界。 档：编译定理。


##### `YiPMMinANLim.instω`

```agda
instω : R2.Rt hΩω ≼ readRW EBOᶻ
```

上条的 HC 前提由具体 hΩω 实例满足。 档：编译定理。


精简块复用的精确入口（不是新证明）：
- `For rows.Self ... = YiLTFold.Self ... (rows ...) ...`，提供 `PF`。
- `For rows.Finite` 直接重导 `YiLTFold.LF/chain/sΩ-LF/LFA/LFAB/LFP/LFPB`，表仍显式。
- `For rows.Limit.Fold` 实例化 `YiLTLim.LimT.Fold`，提供 `LFω` 一族；`Limit.Uniform` 实例化 `LimU.FoldU`，保留 `P/q` 路径条件。
- `For rows.Ω = YiLTKid.Top o¹ (rows ℓ¹) [] (Sem.Kidˢ (rows ℓ¹))`，因此 `Fold.LF¹` 仍有下列原条件；并非裸表保证所有 Ω 情形。


```agda
      LF¹ : ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
          → ∀ {a x} (m : M¹ a x) → Sp m → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (F w β x))
```


```agda
  lift-lim : ∀ f a → Kdˢ (lim f a) (E.Ωt ωᵀ) (proj₁ (Ωt (h₁ (lim f a))))
```


前提可满足：`Kidˢ` 已直接实填给 `Ω` 模块；`Empty/Minimum` 是具体两表实例。终点的 `hΩω` 在 opaque 内由 `hc nωᴮ (B.c∷ B.c[])` 给出，`instω` 编译。没有以矛盾前提给出终点结论。一般 descent 的条件也由本文件族的具体 `ok-B₀`、`ok-d*`、`hi1`、各 path 实例使用；没有声称任意 `Hi` 自动存在。

`YiPMInst` 的 `old-zero/old-one/old-row`、`new-zero/new-one/new-row`，以及 `EmptyShape.β₁-form/flat-lim`、`MinimumShape.flat-lim` 均为有限测试档。没有从这些有限项推出函数全域相等。

#### 4. 第一个障碍

未遇到参数化的停机或 8G 堆墙。第一处需保留数学条件的是 `YiPMT2Frame.F.fallback`：表可能给条目，所以回退形状必须以 `tb k h c c′ ≡ nothing` 为前提，源码已保留。具体 `path₂/path₃/pathN/path₁` 的构造仍依赖最小表上的闭输入形状；本轮未把这些形状定理抽成任意表接口。此处是已交陈述的范围，不是不能推广的否定。

#### 5. 偏离、事故与读过的材料

- 没有改旧文件，没有写 src、archive 或另两路前缀，没有提交、推送、装包、pkill，也没有在私有临时目录和本前缀之外删除。
- 为让新参数化实例真正接回主线，额外重证了最小表的关系 `YiPMMinRel`、闭项相关 `MinTw`、行下界 `MinEmb`、`MinHi`；它们与具体出口各自标为最小表实例，不伪装成任意表定理。
- 把 T2Frame 的 `flat-lim` 有限测试移到 Inst；原空表 `β₁-form` 同时补回。一般数学结论未改。
- 发生的普通作用域错误：`F` 模块重名、应用模块后公开辅助名 `tbᶠ/B₀` 产生歧义、Thin 少导入 `Tr⁺` 及 `T` 模块撞数据类型模块。均用模块别名、限定名或限制 using 修正；未进行数学重新设计。未出现 251、124、154。
- 已完整读简报、AGENTS、手册 §4；读了 YiVT 回报相关部分及被搬运源码。精简块原保持证明按入口、签名和所用段落核对，不声称重新证明这些已有定理。未凭未读的外部材料或文献作结论。
- 全 34 件在私有 regen 目录由脚本重生成，逐字节差异 0。禁用构造、Funext、洞、本机路径检索 0。所有源码冻结。

#### 6. 临时源码、脚本、日志的确切路径（仅供主审，不写入数学文件）

- 临时第 0 步：`<实验目录>/PM0.agda`；日志 `<实验目录>/PM0.log`；初次生成脚本 `<实验目录>/generate.py`。其中实际 Ω 行的两条 closed-row 测试后来直接追加在 PM0；PM0 本体为最终源码。
- 仓库代码生成/搬运脚本：`<实验目录>/genrepo.py`（32 件核心与 Min），`<实验目录>/genapi.py`（Thin），`<实验目录>/geninst.py`（Inst）。从独立目录运行，目录下需放原 `probes/OCF/Lean/YiVT*.lagda.md`；源脚本只读这些原文件。完整复现目录 `<实验目录>/regen/` 已生成 34 件，与仓库逐字节一致。
- 本路串行批编脚本：`<实验目录>/buildcore.py`、`<实验目录>/buildextra.py`；每件日志 `<实验目录>/YiPM<后缀>.log`，Thin/Inst 最终自行冷编日志 `<实验目录>/cold-YiPMThin.log`、`cold-YiPMInst.log`。
- 库文件：`<实验目录>/libraries`。
- 主审已确认的 32 件冷编数据（只读）：`<复核目录>/review-pm-core.json`、`review-pm-min.json`。
- 本回报生成脚本：`<实验目录>/makereport.py`；回报原文 `<实验目录>/report.md`。

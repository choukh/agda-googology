# 最小实例 MinimalGoal 的组装 (YiMN)：简报原文（外部模型，广撒网第三批，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-17 "你直接写下一批简报"；主审选题；外部模型，作者转发 |
| 前缀 | `YiMN` |
| 回报 | 已启动 Codex 独立新对话，每路6G，编译三槽排队；回报原文依作者决定不转存，关键范围/条件/阻点写模块简述 |

## 简报原文（本机路径换成占位）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

## 作者的决定（2026-11-17）
- 作者："另外外部模型额度富余很多, 可以再派一些“广撒网”类的任务, 碰碰运气"；之后又说 "你直接写下一批简报"。本路是广撒网第三批之一（主审选题："最小实例 MinimalGoal 的组装（登记事件）"）。广撒网的意思：试探性的、彼此独立的尝试，允许不成功；不成功就如实交出走到哪里、挡在哪里，不硬撑，不夸大。
- 同时在跑的还有内部第七十三批五路：独立审核 `YiVA`（塔第 1 项前缀层号上折叠会不会掉值）、上界工具 `YiTU`（第 2 站闭项的上界）、构造续 `YiRQ`（限在读回域推导上的证据）、定义候选 `YiDX`、摆脱侧 `YiPT`（前缀 3）。不碰它们的前缀，也不导入它们的文件。

## 当前状态（主审复核过的事实）
- 主线：精简块 `YiRW*`，折叠 `YiTBRow.ψ`，最小比较表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。第一档已完成（读法 ψ₀(Λ) 的合法闭项、内部 View、FGH；`YiPXFull`）。
- 终点归结为各站值下界（`YiS1Accept.ebo-from-stations`；松一层的版本 `YiSYFrame.ebo-from-stations′`）。第 0 到 2 站成立（`YiFRStations.k0/k1/k2`；`k2` 是 BTBO 下界加站间单调）。第 3 站未证。
- 现主线的无条件终点值：ψ₀(Ω_Ω+ψ₁(Ω_ω)+2)（`YiFZClimb.strict-ebo₂`）。树侧值的最高验收仍是 11-04 封存的带高度族的 ψ₀(Ω_{Ω·ω²})（`probes/OCF/Align/EmbVVInstO2` 的 `vv-ω²`）。里程碑 ψ₀(Ω_{Ω₂})（`YiAZLocal.S 2`）尚未达到。
- **整体引理（读回域上的 Leaf 加 LowKeep）的进度**：Leaf 在读回域上成立（`YiGLDom.dom-top`、`YiMGRel.topᵐ`）；精确标签下 LowKeep 对一切不含 Ω 形状的层号无条件成立（`YiXPExact.lowKeepAt-noΩ`、`YiMGFrame.lowKeepAtᵐ-noΩ`）；记号侧工具齐了（`YiELLim.limAt`、`YiTAChain.ex-add′`、`ex-limc`、`lbl-limc`、`YiTAReal.real-exact`、`cofΩ-all`）；第 0 层分支前提要换精确读回（`YiELZero.no-all`）。Ω 形状层号上：颈结点的走链精确证据为空（`YiMGNeck.no-chain-neck`）；塔第 1 项上以下界关系宽量化的链步接口不成立（`YiTFTw1.no-stepU′-tw1`）；同一孩子里两个分支类型与读法相同的槽位，一个走链、一个保留（`YiKTSlot` 的有限测试）。值上是否掉值未判定（内部 YiVA 在审）。
- 其他已编译：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiCXLabels.cut-unique`（统一派发要唯一标签）、`YiCXWindow.window-frame`、`window-nonunique`（局部派发允许不唯一的标签窗口）；`YiTDOrder`（全域派发 ⇔ 弱口径记号系统）；`YiCVDomain.no-root-cover`（现主线比较表在龙骨上不满足共现覆盖）；`YiORBound.original-neg`；摆脱侧 `YiRRTwo.prefix-two`（两条实际链前缀 2 的值界，不读记号）。各模块文首写明范围，先读文首。
- 三条更正（不要照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧的项序单调，不是树侧折叠的跨层单调；`YiKWObjects.kept` 与 `YiC1Slot` 不透明块里的 `kept` 不是同一个对象；`OCF.Align.Level` 的下标类型 `Ordᴵ` 只有 `zero`、`suc`、`lim`，写不出不可数的下标。
- 原则：最终定义与记号无关（纲领第 4 条）；"不能以'追求同步'为名反过来指导树的定义形状"；"第 4 层不反过来改前 3 层"（改树、折叠、合法性只能在新文件里做候选，进主线由作者定）。
- **回报**：作者决定外部各路的回报原文不再转进仓库；所以你的回报里写清的东西，最好也写进模块文首（不超过 5 行）或代码之间的简短说明里，主审只看得到仓库文件。

## 背景
- 最小实例 `YiBVSmall`（`layer = nd (sΩ zero) child`，`child d = two ⊕ ↑ zero (suc d)`）的目标 `MinimalGoal = D.Input.Goal minimal`（即 `YiC1Slot.BranchNeed` 的最小实例）。现有零件：
  - `YiXPSmall`：`low-child : ∀ d → LowKeepAtˣ (S.child d)`；`Needˣ : E.T → Tr zero → Set`；`needˣ : ∀ d {λ′} → Lbl (S.child d) λ′ → ∀ η → η ≤ᵀ λ′ → Needˣ η d`；`need-fin`、`need-ω`。YiXP 回报指出要回到原来的 `YiQLRead.Need` 还差三处：(a) 结论在 `Rˣ` 里带向下封闭 `mc`，`YiCLFam.M 1` 没有 `mc`；(b) `Needˣ` 多要 `Prefixˣ base []`；(c) η 的范围要从 `M⁰ η d` 推出 η ≤ λ。
  - `YiELZero`：`Ex⁰ η d = Lbl (↑ zero d) η`、`ex→M⁰`、`child-lbl`（对带精确读回的 d，孩子层号有精确标签，夹在 η 与 η+2 之间）；`no-all`（带下界证据的 d 不都有精确标签）。
  - `YiTAReal.real-exact : ∀ {η} → NF η → η <ᵀ E.Ωs [] → Σ (Tr zero) (Ex⁰ η)`。
  - `YiGCBridge.from-narrow`、`YiQLRead.minimal-from`、`YiRXOmegaHead.omega-head`（分支关系 ⇒ Ω 头关系）。
- 这是一个登记过的事件：最小实例上 `MinimalGoal` 成立 → 第 3 站那一步的估计回调。

## 要做的
0. 列出从已有零件到 `MinimalGoal` 的组装链，逐处标出缺口（上面的 (a)(b)(c)，以及 `MinimalGoal` 对一切带 `M⁰` 证据的 d 量化、而精确标签只对带精确读回的 d 有，这一处怎么办）。编译类型。
1. 逐处补：(a) 证 `Rˣ` 在第 1 层的结论能去掉 `mc`（或说明为什么不能）；(b) 对实际底实填 `Prefixˣ`；(c) 从下界证据推出所需的 η 范围，或把 `MinimalGoal` 的量化域收到带精确读回的 d 上并说明这一步改了什么。
2. 交出 `MinimalGoal`（或它的读回域版本）的编译定理，或第一个挡住的地方。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

## 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiMN`（模块名 `OCF.Lean.YiMN…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiVA`、`YiTU`、`YiRQ`、`YiDX`、`YiPT`、`YiNC`、`YiLW`、`YiH2`、`YiFY`、`YiCO`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库的 .agda-lib 路径>
  <cubical 的 .agda-lib 路径>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 6G**：机器共 64G，同时有十来路在编译；峰值超过 4G 时先按 C-9、C-10、S-1 改形状。若某个文件确实要超过 6G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件（本路特别规定，覆盖上面的通用写法）**：退出 251 时不原样重跑（Bedrock H-6），先按 C-9、C-10、S-1 改形状并定位；改过形状后在同一上限下仍撞墙才停，附二分或 profile 数据；要加堆在回报里写明，由主审安排。同一处两次重新设计仍过不了检查器也停。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

## 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

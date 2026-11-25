# 换模型挑战 "缺口在精确标签" (YiCX)：简报原文（外部模型，广撒网第二批，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-16 广撒网第二批（作者问 “广撒网还有下一批吗” 后选项全选；第一批原话：“外部模型额度富余很多，可以再派一些“广撒网”类的任务，碰碰运气”）；外部模型，作者转发 |
| 前缀 | `YiCX` |
| 回报 | 2026-11-16 代码已由 Claude 主审冷编复核；按作者2026-11-17决定不再转存回报原文；按本批简报所载主审复核接收，本会话未重核 |

## 简报原文（本机路径换成占位）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

## 作者的决定（2026-11-16，原话或选项原文）
- 作者："另外外部模型额度富余很多, 可以再派一些“广撒网”类的任务, 碰碰运气"。本路是广撒网第二批八路之一（第一批八路已回并复核），选项原文 "换模型挑战 “缺口在精确标签”"。广撒网的意思：试探性的、彼此独立的尝试，允许不成功；不成功就如实交出走到哪里、挡在哪里，不硬撑，不夸大。
- 同时在跑的还有内部第七十一批四路（作者定 "停逐项，改攻整体引理"）：工程 `YiXP`（把 `YiGT` 保持引理族移到精确标签的关系上）、数学 `YiEL`（一般的 `LimAt`、第 0 层输出带精确标签、Ω 形状层号的精确标签）、摆脱侧 `YiWB`（比 `Le` 宽的底关系）、同步对象上的 `Tail` `YiTL`。不碰它们的前缀，也不导入它们的文件。

## 当前状态（主审复核过的事实）
- 主线：精简块 `YiRW*`，折叠 `YiTBRow.ψ`，最小比较表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。第一档已完成（读法 ψ₀(Λ) 的合法闭项、内部 View、FGH；`YiPXFull` 导入闭包干净）。
- 终点归结为各站值下界：`YiS1Accept.Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)`，`ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；`YiGIEnd.row-eq : ∀ n → Keel⁻.row keelᴱ n ≡ E.EBOψ n`（第 1 站 ψ₀(Ω₁)，第 2 站 ψ₀(Ω_Ω)，第 3 站 ψ₀(Ω_{Ω_Ω})）。第 0 到 2 站成立（`YiFRStations.k0/k1/k2`；`k2` 的证明是 BTBO 下界加站间单调 `station-step`，`tw 2` 的折叠没有贡献新值）。第 3 站未证。
- 现主线的无条件终点值：ψ₀(Ω_Ω+ψ₁(Ω_ω)+1)（`YiOLBoost.strict-ebo`）。树侧值的最高验收仍是 11-04 封存的带高度族的 ψ₀(Ω_{Ω·ω²})（`probes/OCF/Align/EmbVVInstO2` 的 `vv-ω²`）。
- 里程碑 ψ₀(Ω_{Ω₂})（`YiAZLocal.S 2`）**尚未达到**。干净对象 `YiUTTwo`（层号 `two ⊕ ↑ two (Ωt two)`，标准底）上基本列第 0 项成立（`YiC0Accept.first-row`，经新旧块对应搬旧块的 BTBO 下界），第 1 项 ψ₀(Ω_{ψ₁(Ω_Ω)}) 未证。
- 三路 Fable 5.2 审核（留档 `probes/Survey/Reports-2026-11-16/`）的共识：第六十一到六十九批的逐项攻法停工（不是否定）；同一缺口以约二十个名字出现，都是 "读回域上的 Leaf 加 LowKeep" 的实例（抽象接口 `YiAbsGIface`，条件定理 `YiGIEnd.eboᵍ`）。
- **最近两批的结果**（主审复核过）：整体引理一路（`YiGL*`）：读回域 `YiGLDom.Dom` 上 Leaf、Lift 无前提成立（`dom-top`、`leafᴰ`、`liftᴰ`）；LowKeep 的现有框架在槽位标签取下界读法时无居民（`YiGLFrame.no-frame-S`），换成精确标签 `Lbl` 后有（`frameˣ-S`），精确标签的关系 `YiGLExact.Rˣ`、`topˣ`、`LowKeepˣ`（无居民）。对位调整（`YiSY*`）：`ebo-from-stations′`，第 3 站归约到同步对象上的 `Tail`（`YiSYSmall.k2′-from-tail`）。摆脱侧（`YiLX*`）：`YiLXClimb.climb`。配对否定（`YiVN*`）：以下标的树侧值序作前提的下标单调不成立（`YiVNIdx.Gen.no-value-index-mono≈`）。广撒网第一批：封闭关系下原行仍不过判据（`YiORBound.original-neg`）；全域派发 ⇔ 弱口径记号系统，结点内完备派发推不出全序（`YiTDOrder`、`YiTDDiamond`、`YiTDExpose`）；干净对象第一支 ≤ ψ₀(Ω₄)（`YiXUFirst.first-ceiling`）；退路保留此前折叠的值（`YiFOValue.fallback-prefix`）；换基、带高度族、B7 只到原型（`YiBS*`、`YiHF*`、`YiFW*`）。各模块文首写明范围，先读文首。
- 三条更正（不要照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧的项序单调，不是树侧折叠的跨层单调；`YiKWObjects.kept` 与 `YiC1Slot` 不透明块里的 `kept` 不是同一个对象；`OCF.Align.Level` 的下标类型 `Ordᴵ` 只有 `zero`、`suc`、`lim`，写不出不可数的下标。
- 原则：最终定义与记号无关（纲领第 4 条）；"不能以'追求同步'为名反过来指导树的定义形状"；"第 4 层不反过来改前 3 层"（改树、折叠、合法性只能在新文件里做候选，进主线由作者定）。

## 本路的做法（务必照此顺序）
本路是**换模型的独立挑战**：由作者选一个与前几路不同的模型，新对话。**先读定义，不先读结论**。
0. **只读定义，写一页判断并封存**（算出 SHA256，记 UTC）：只读主线块与折叠（`probes/OCF/Lean/YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`、`YiTBRow`、`YiMTTab`），关系族 `YiGIRel`（`R`、`Rd`），保持引理族 `YiGTIndex`（`NodeFrame`、`SlotPres`、`PresAt`、`Kit`）、`YiGTFold`（`pres`），参照一侧 `OCF/Align/EboLeanDef`。判断的问题：要证 "Ω 树折到更低层时关系保持"（LowKeep），保持引理族里每个结点的保留判定（`kp`）与记号一侧的派发怎样对齐；槽位标签取下界读法（`Rd`）时能否对齐；你会怎样设计标签。
1. **封存后**读 `probes/Survey/Reports-2026-11-16/YiGL.md` 与 `YiGLFrame`、`YiGLExact`、`YiGLNode` 的文首和陈述。YiGL 的结论："下界标签下框架无居民（`no-frame-S`），要换精确标签 `Lbl`；剩下的是第 0 层输出是否带精确标签"。挑战它：结论对不对；有没有不需要精确标签的出路（例如目标关系带向下封闭、源一侧的结点读低时的补救）；`Lbl` 对 Ω 形状层号取 `⊥` 是否必然。
2. **编译**最关键的一步（一个反例、一个替代设计的可满足性检查、或一条支持 YiGL 的引理）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

## 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiCX`（模块名 `OCF.Lean.YiCX…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXP`、`YiEL`、`YiWB`、`YiTL`、`YiHG`、`YiXW`、`YiCV`、`YiRT`、`YiBT`、`YiBN`、`YiFZ`）。验收文件，文首标明。
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

# 带 mc 的关系上的出口 (YiMX)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十八批（"派：带 mc 的关系上的出口 (Recommended)"）；外部模型，作者转发 |
| 前缀 | `YiMX` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：带 mc 的关系上的出口（数学，记号一侧，构造与否定配对）（前缀 YiMX）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十八批（选项原文 "派：带 mc 的关系上的出口 (Recommended)"），与在跑的 YiXV、YiLK、YiFM、YiLL、YiPC、YiVW 在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **要去掉的条件**：`eboᵍ` 的第四个前提是 `Assembly.ExitCondition = ∀ n → H.Exᴴ (T.folded lk n)`（`YiGIEnd` 第 56–57 行），即塔每一行由 `LowKeep` 的证明 `lk` 产生的第 0 层关系推导，都满足出口条件。它依赖抽象的证明 `lk`，所以直接验证不了。
- **出口条件**（`YiHCRel` 第 139–146 行）：`Exᴴ` 只在 `mc` 结点上有内容，其余各行逐项传递或为 `⊤`：
  ```agda
  Exᴴ (mc {s} {t} _ m) = NF s × NF t × Ctbl t × Exᴴ m
  ```
  `mc : ∀ {s t x} → s ≤ᵀ t → Mᴴ … t x → Mᴴ … s x`（关系对参照项沿项序向下封闭）。出口 `exitᴴ : ∀ {s x} (m : M⁰ s x) → Exᴴ m → (h : HC s) → Rt h ≼ readRW x`（第 152 行起）。
- **用到的记号引理**：`YiNFOCond.mono≤ᶜ : CofinNF → ∀ {s t} → NF s → NF t → Ctbl t → (h : HC s) (h′ : HC t) → (s <ᵀ t) ⊎ (s ≡ t) → Rt h ≼ Rt h′`，`CofinNF` 由 `YiCFCofin.cofin`（要标准形）给出，实例 `YiCFMono.mono≤ⁿ`。
- **上一路（YiNX）**，回报 `probes/Survey/Reports-2026-11-12/YiNX.md`：
  - `YiNXNote`：`W k = ψ₀(ψₖ(Ωₖ₊₁))` 有 `HC`、不是标准形（`¬nfW`），与 `N k = ψ₀(Ωₖ₊₁)` 参照值互相 ≼（`W≼N`、`N≼W`），`W<N : W k <ᵀ N k`，`monoW`；
  - `YiNXFull`：`fromM` 从**基础**关系推导取得 `HC`（不适用于带 `mc` 的推导），`Out.exit-low0` 对 `YiMHLean.¬ex-low0` 那一类推导去掉了标准形条件；
  - `YiNXLow.¬shift₄`：相邻层的平移等式不能原样用到下一片（只否定一条语法等式）。
  - 其他反例：`YiDCExit.¬nf₂ : NF (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) → ⊥`。
- AGENTS "构造与否定配对"：本路一路构造、一路对同一陈述找否定，共用同一个陈述文件。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：写出一般陈述
   `Mono : Set`，`Mono = ∀ {s t} → s ≤ᵀ t → (h : HC s) (h′ : HC t) → Rt h ≼ Rt h′`（不要求标准形；若需要 `Ctbl t` 一类可数条件，说明理由）。
   在几对小的非标准形项上判定它：(W k, N k) 两个方向；s = ψ₀(ψ₁(Ω₃)) 与 t = ψ₀(Ω₂)（先确认两者的项序关系与 `HC`）；再挑一两对非相邻层的。每一对编译实例，或编译反例。前提不可满足（例如 `HC` 推导不存在）就换一对，并在回报里说明。
1. **构造方向**（若第 0 步没有反例）：证 `Mono`，或证足够的较弱形式（例如只对 `mc` 实际产生的项对）。然后编译不带出口条件的出口 `exitᴴ′ : ∀ {s x} (m : M⁰ s x) → (h : HC s) → Rt h ≼ readRW x`，再在新文件里用 `YiGIEnd` 的 `Assembly` 编译不带 `ExitCondition` 的终点定理（前提只剩 `Leaf`、`Lift`、`LowKeep`）。
2. **否定方向**（若第 0 步有反例）：把反例写成编译的否定 `¬Mono`，并检查它会不会出现在 `mc` 的实际用法里（`YiKQFold.feedΩ`、`YiHCRel` 的保持证明里 `mc` 的调用）。然后给出改写：一个连同出口条件一起产生推导的 `LowKeepᴱ`（结论里带 `Exᴴ`），编译 "`LowKeepᴱ` ⇒ `eboᵍ` 的结论"，使出口条件不再依赖抽象的证明；并在第 0 层（`YiGICheck.low-zero` 那种情形）给一个实例。
3. 无论哪个方向，都对另一方向在最小实例上做一次检查（配对）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiMX`（模块名 `OCF.Lean.YiMX…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiLK`、`YiFM`、`YiLL`、`YiPC`、`YiVW`）。验收文件（读记号），文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有七路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；5G 仍耗尽（先在回报里说明）；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。



## 主审复核

各新模块均逐件删自身接口5G冷编0，禁用构造、洞、本机路径、Funext 0。完整范围见 probes/LOG.md。

## 回报原文（Codex 独立任务）

### YiMX 完整回报（定稿、冻结；已纳入 Leaf 范围更新）

#### 0. 最新范围更正

主审追加通知：YiLLLeafNeg.noLeaf 与 noLeafOk 已由主审独立 5G 冷编复核并冻结。本路读取了这两个定理的实际陈述：它们针对同一 gradedᵍ/domsᵍ 的全域 Leaf，noLeaf : Leaf → ⊥；noLeafOk 还否定只加 Ok 的全域版本。规范塔域没有相应否定。

因此 YiMXEnd.eboᴱ 的 Leaf 前提已经被否定。该条件组装虽经编译，在原实例上的前提不可满足，不能报为可实填的 EBO 下界或强度进展。保留其源码作为接口接线的记录；其有效数学交付为 Mono/Exit′ 的否定、LowKeepᴱ 的接口及零层实例。零层实例不依赖 Leaf，也不受此次范围更正影响。

五个 YiMX 数学文件保持冻结，源码、接口与冷编散列不变；只更新本回报。附录保留原冻结源码，其中 YiMXEnd 文首“全域律未实填”须按本更正读为“全域 Leaf 已被否定”。未改任何共享定义。此次不重复编译或宣称独立复核 YiLLLeafNeg；“主审已冷编复核”的证据来自追加任务通知。

#### 1. 判决与范围

本路只新增验收关系的陈述与定理，没有修改树、折叠、合法性、证书或 src。对纲领与目标的意义：无标准形前提的项序单调不能作为统一出口；这一点由两个具体反例编译证明，不是壁垒定理的类比。新增 LowKeepᴱ 把出口证据与推导一起返回，因而终点不再另带一个依赖抽象 lk 的全塔 ExitCondition。LowKeepᴱ 仍未全域实填，而原实例的 Leaf 前提已由 YiLLLeafNeg.noLeaf 否定。这一步没有取得可实填的 EBO 下界，也没有宣称树已自足。

**状态：五个新模块已定稿并冻结。** 冷编时逐件删自身接口，依赖保留热接口；全部退出码 0，各日志只有自己的 Checking 行。禁用构造与本机路径扫描为 0。未提交、未推送、未修改导航、台账或其他前缀；未派子路。

##### 第 0 步

- 共用陈述位于 YiMXIface.Mono：∀ {s t} → s ≤ᵀ t → (h : HC s) (h′ : HC t) → Rt h ≼ Rt h′。没有补 Ctbl，因为反例两端已有 Ctbl，补它也不能恢复全域陈述。
- W k = ψ₀(ψₖ(Ωₖ₊₁)) 与 N k = ψ₀(Ωₖ₊₁)：任意 k 的 W k ≤ᵀ N k 编译通过；反方向的项序前提不可能（reverse-impossible）。k = 1 的两个值方向都通过。这里“反方向”没有假装成可满足的 Mono 实例。
- 额外的最小反例 bad = 1 + ω + 1、t = ω：bad <ᵀ ω；hbad、hωt 分别给 HC；ct-bad、ct-ω 分别给 Ctbl；bad-value : Rt hbad ≼ Rt hωt → ⊥。该对象不是标准形（¬nf-bad）。由此编译 ¬Mono。
- 指定单项 A = ψ₀(ψ₁(Ω₃))、N = ψ₀(Ω₂)：hA 通过两次旧基础折叠取得 HC；A<N 证明 A <ᵀ N；N≺A 证明 suc (Rt (hN 1)) ≼ Rt hA，故 ¬A≼N。十七次基本列取支到 W 1 + 1 的 pathA 及所有共尾度证据均经 Agda 检查。该反例不是不排序和的重复。
- 另外的非相邻层样本 W 0、W 2：W0<W2、W0≼W2、¬W2≼W0 均通过。
- 首个临时文件 Mini 的第一次成功编译距私有实验目录建立约 75 秒；在读取简报与手册后即建立该目录，满足首个临时检查 30 分钟内编译的要求。

##### 后续步骤

第 0 步得到反例，故走第 2 步。YiMXNeg.bad-mc = mc (inj₁ bad<ω) (of⁰ ωᶜ-M) 是第 0 层关系的实际闭合推导，并不是只在纸面上能写 mc。back-ω 给 readRW ωᶜ ≼ Rt hωt，故无条件的 Exit′ 被 ¬Exit′ 否定；该具体推导的 Exᴴ 也被 ¬ex-bad 否定。

YiMXEnd.LowKeepᴱ 的结论是一个 Σ：推导及其出口证据。非零层的 Exᵍ 为 ⊤，零层为 Exᴴ。forgetᴱ 取推导；End.exits 取同次调用的证据，接回冻结的 YiGIEnd.Assembly。最终：

    eboᴱ : Leaf → Lift → LowKeepᴱ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ

这是编译通过的条件蕴含：Leaf、Lift、LowKeepᴱ 推出所列序数值比较。但当前 gradedᵍ/domsᵍ 的 Leaf 已有编译否定，所以联合前提不可满足；该蕴含不能作为可实填 EBO 下界。零层实例不能代替它。low-zeroᴱ 对任意基础关系输入构造输出及 Exᴴ；startᴱ 是全部输入具体给出的首个闭合实例。这里明确区分“证明接口已有零层实例”和“全域保持律已填”。

第 3 步的配对：同一 Mono 陈述既有上述编译反例，也有 W/N 与 W 0/W 2 的肯定样本；没有尝试在反例出现后继续证明一般 Mono。

##### 实际 mc 调用的逐处核查

1. YiKQFold.feedΩ 的 mc 比较 Ωt (γT a [] k) 与 One.ΩΩ（源码 34–36、49–51 行），两端都是 Ωt 单项。bad≢Ω、bad≢singleton 编译证明和的反例 bad 不可能字面等于这些源项。这里只排除同一个 bad 的字面匹配，不证明该回灌链满足出口。
2. YiKQFold.LF² 的 mc 保持行将 le 映为 app≤ 0 [] le（106 行），结果是 ψ₀ 的单项。bad 的和形状不直接匹配；指定 A 反例则表明“单项”本身不能恢复全域 Mono。未证明 A 这一对能出现在该指定 LF² 调用的带证据量化域里。
3. YiHCRel.Gen.m-add 在 mc 行使用 ∷≤ p le（83 行），增加同一前缀；m-right 的 mc 行原样保留 le（104 行）。它们不会自动产生 NF 或 Exᴴ。未把“关系允许 bad-mc”说成“规范塔一定生成 bad-mc”。规范生成域上更弱的出口仍未判定。

##### 问题表

| 问题 | 位置 | 结论与档 |
|---|---|---|
| 可否不带 NF 地使用全域项序单调？ | YiMXNote.¬Mono；YiMXSamples.¬A≼N | 否，编译的否定定理 |
| 只补可数性是否够？ | YiMXNote.ct-bad、ct-ω、bad-value | 否，同一编译反例两端可数 |
| 可否对全部带 mc 的 M⁰ 无条件出口？ | YiMXNeg.¬Exit′ | 否，编译的否定定理 |
| 规范塔是否生成该反例？ | feedΩ、LF²、m-add、m-right 的调用域 | 未证明；源码核查的范围见上，不作路线否定 |
| 出口证据与保持一起返回能否接终点？ | YiMXEnd.eboᴱ | 编译的条件组装；Leaf 已否定，不能实填或作为强度进展 |
| 加强保持律有何实例？ | YiMXEnd.low-zeroᴱ、startᴱ | 不依赖 Leaf 的基础关系片段零层实例；全域 Leaf 已否定 |

#### 2. 文件、冷编与内存

代码行按 Agda 代码块的非空、非纯注释行计；最大驻留与总内存都直接取 +RTS -s，不把累计分配量当峰值。机器同时有其他路工作，墙钟时间仅作记录。每次仅一个 Agda，堆上限 5G。

| 文件 | 代码行 | 总行 | 冷编退出码 | 秒 | 最大驻留字节 | RTS 总内存 |
|---|---:|---:|---:|---:|---:|---:|
| probes/OCF/Lean/YiMXIface.lagda.md | 8 | 15 | 0 | 11.36 | 998,073,976 | 1667 MiB |
| probes/OCF/Lean/YiMXNote.lagda.md | 79 | 97 | 0 | 15.23 | 1,330,022,208 | 2222 MiB |
| probes/OCF/Lean/YiMXSamples.lagda.md | 61 | 77 | 0 | 14.43 | 1,197,530,376 | 2056 MiB |
| probes/OCF/Lean/YiMXNeg.lagda.md | 40 | 56 | 0 | 15.64 | 1,393,144,976 | 2337 MiB |
| probes/OCF/Lean/YiMXEnd.lagda.md | 60 | 76 | 0 | 15.92 | 1,483,225,904 | 2576 MiB |

完整冷编命令由实验目录 cold.py 逐个执行，先删除写死路径的自身 .agdai，再运行：

    agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<模块>.lagda.md

无 --ignore-interfaces；未删除其他模块的接口。首个临时文件与包含十七步具体取支的 Samples 都已在临时目录先编译；后者带 timeout 600。

#### 3. 定理表

以下保留源码签名的词序，只将多行折为空格；完整逐行源码在附录。每条都是编译定理/构造；Mono、Exit′、LowKeepᴱ 是共用陈述或接口而非已填全域实例。

| 名字 | 逐字陈述（折行） | 白话 | 文件 | 档 |
|---|---|---|---|---|
| forward | `forward : ∀ k → W k ≤ᵀ N k` | W 的项序前提可满足 | YiMXNote | 编译定理/构造 |
| reverse-impossible | `reverse-impossible : ∀ k → N k ≤ᵀ W k → ⊥` | N 到 W 的项序前提不可能 | YiMXNote | 编译定理/构造 |
| small-forward | `small-forward : Rt (hW 1) ≼ Rt (hN 1)` | 指定 W/N 值正向 | YiMXNote | 编译定理/构造 |
| small-backward | `small-backward : Rt (hN 1) ≼ Rt (hW 1)` | 指定 W/N 值反向 | YiMXNote | 编译定理/构造 |
| hbad | `hbad : HC bad` | 反例左端可沿基本列递归 | YiMXNote | 编译定理/构造 |
| hωt | `hωt : HC ωᵀ` | 反例右端可沿基本列递归 | YiMXNote | 编译定理/构造 |
| bad<ω | `bad<ω : bad <ᵀ ωᵀ` | 反例的项序前提 | YiMXNote | 编译定理/构造 |
| ¬Mono | `¬Mono : Mono → ⊥` | 否定共用的全域单调 | YiMXNote | 编译定理/构造 |
| ct-bad | `ct-bad : Ctbl bad` | 反例左端可数 | YiMXNote | 编译定理/构造 |
| ct-ω | `ct-ω : Ctbl ωᵀ` | 反例右端可数 | YiMXNote | 编译定理/构造 |
| bad-value | `bad-value : Rt hbad ≼ Rt hωt → ⊥` | 否定该反例的值比较 | YiMXNote | 编译定理/构造 |
| ¬nf-bad | `¬nf-bad : NF bad → ⊥` | 该反例不是标准形 | YiMXNote | 编译定理/构造 |
| W0<W2 | `W0<W2 : W 0 OCF.Align.EboLeanDef.<ᵀ W 2` | 非相邻层样本的项序 | YiMXNote | 编译定理/构造 |
| W0≼W2 | `W0≼W2 : Rt (hW 0) ≼ Rt (hW 2)` | 非相邻层样本的值正向 | YiMXNote | 编译定理/构造 |
| ¬W2≼W0 | `¬W2≼W0 : Rt (hW 2) ≼ Rt (hW 0) → ⊥` | 否定值反向 | YiMXNote | 编译定理/构造 |
| hA | `hA : HC (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))` | 指定单项样本具有闭合 HC | YiMXSamples | 编译定理/构造 |
| A<N | `A<N : ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)) <ᵀ N 1` | 指定单项的项序前提 | YiMXSamples | 编译定理/构造 |
| N≼A | `N≼A : Rt (hN 1) ≼ Rt hA` | 值反向的肯定样本 | YiMXSamples | 编译定理/构造 |
| pathA-ω | `pathA-ω : Allω pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))` | 十七次取支均合法使用 HC 的 ω 行 | YiMXSamples | 编译定理/构造 |
| lastA | `lastA : trace pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) ≡ (OCF.Align.EboLeanDef.ψ [] (ψᴺ 1 (Ωᴺ 2)) ∷ OCF.Align.EboLeanDef.𝟏 ∷ [])` | 取支终点等于 W 1 + 1 | YiMXSamples | 编译定理/构造 |
| N≺A | `N≺A : L.suc (Rt (hN 1)) ≼ Rt hA` | 目标后继值仍受 A 支配 | YiMXSamples | 编译定理/构造 |
| ¬A≼N | `¬A≼N : Rt hA ≼ Rt (hN 1) → ⊥` | 指定单项亦反驳值正向 | YiMXSamples | 编译定理/构造 |
| bad-mc | `bad-mc : M⁰ bad ωᶜ` | 反例确实可构造成闭合 M⁰ 推导 | YiMXNeg | 编译定理/构造 |
| bad≢singleton | `bad≢singleton : ∀ u a → bad ≡ (ψ u a ∷ []) → ⊥` | 和的反例不等于一个单项 | YiMXNeg | 编译定理/构造 |
| bad≢Ω | `bad≢Ω : ∀ u → bad ≡ Ωt u → ⊥` | 和的反例不等于 Ω 单项 | YiMXNeg | 编译定理/构造 |
| back-ω | `back-ω : readRW ωᶜ ≼ Rt hωt` | 规范 ω 树不高于 ω 参照 | YiMXNeg | 编译定理/构造 |
| ¬Exit′ | `¬Exit′ : Exit′ → ⊥` | 否定全部 M⁰ 的无条件出口 | YiMXNeg | 编译定理/构造 |
| ¬ex-bad | `¬ex-bad : Exᴴ bad-mc → ⊥` | 否定具体反例的出口证据 | YiMXNeg | 编译定理/构造 |
| forgetᴱ | `forgetᴱ : LowKeepᴱ → LowKeep` | 加强律返回的推导满足原 LowKeep | YiMXEnd | 编译的条件定理 |
| exits | `exits : A.ExitCondition` | 同次调用得到各塔行的出口证据 | YiMXEnd | 编译的条件定理 |
| eboᴱ | `eboᴱ : Leaf → Lift → LowKeepᴱ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ` | 接线成立，但 Leaf 已否定，原实例不可实填 | YiMXEnd | 编译的条件蕴含；前提不可满足 |
| low-zeroᴱ | `low-zeroᴱ : (b : Bsᵍ B.zero) (β : O.Tr⁺ B.zero) (t₀ : E.T) → K.M⁰ (E.ψ [] t₀ ∷ []) (proj₁ β) → ∀ {a x} → K.M⁰ a x → Σ (GR.R B.zero (E.ψ [] (t₀ ++ a) ∷ []) (proj₁ (ψᵍ B.zero b B.zero P.self β x))) H.Exᴴ` | 任意基础关系输入的零层带证据保持 | YiMXEnd | 编译定理/构造 |
| startᴱ | `startᴱ : Σ (GR.R B.zero (E.EBOψ 0) (proj₁ (ψᵍ B.zero (tt , tt , F.B₀ B.zero) B.zero P.self (O.Ωt B.zero) (proj₁ (O.Ωt B.zero))))) H.Exᴴ` | 全部数据给定的零层闭合实例 | YiMXEnd | 编译定理/构造 |

#### 4. 第一个障碍与未解决项

第一个数学障碍是 Mono 本身，精确位置为 YiMXNote.bad-value/¬Mono；指定的单项障碍为 YiMXSamples.N≺A/¬A≼N。它们阻止以“去掉标准形前提的全域项序单调”删除任意 mc 推导的出口条件。YiMXNeg.¬Exit′ 进一步否定本简报第 1 步所列的无条件全域出口陈述。没有将它们归入 W、V、C 等既有墙，也没有否定规范读回域或只对实际生成的 mc 项对的较弱形式。

LowKeepᴱ 仍未全域实填；当前原实例的 Leaf 已否定，因此原实例的条件终点不能列作待实填的 EBO 下界。本路保留加强接口、条件接线以及不依赖 Leaf 的零层构造。规范塔读回域上的 Leaf 与更弱出口没有被本路或追加通知否定；若改变定理量化域，需要另题，不在本路修改共享定义。

#### 5. 偏离、事故与引用范围

- 研发顺序的偏离：先编译了 W/N 与额外的和反例，在该反例成立后即转入否定分支；指定的 A 样本在带证据保持接口的初稿后补齐。最终冷编顺序是接口、最小反例、指定样本、实际 mc 否定、终点，全部数学交付均已检查。没有在最小反例未成立时投入一般 Mono 证明。
- 临时检查发生过普通的 42：反向项等式该用空模式；解析缩进错误；natT 与 replicate 的写法不相同，改用已有 rep1 显式运输；ω 的 GB 不能写空模式，改用已有 flatGB。没有堆耗尽、无公设、无洞、无停机或正性指示。无同一数学设计两次重设计仍失败的情况。
- 两次 Python 广度枚举作为临时找路径工具，未完成，均由本路 Ctrl-C 停止（130）；其输出不作为定理。随后显式给出的十七步路径由 Agda 从头检查。普通权限的 ps 读取曾失败；一次只读的提升权限查询确认本路搜索进程已结束，未终止其他进程。
- 没有修改任何已有文件的结论；本路新文件在收敛前有常规修正，定稿后冻结。只在 YiMX 前缀、私有实验目录以及要求的报告文件写入。
- 冻结的 YiNX/GI 旧模块及其依赖使用现有接口，没有再删旧模块接口重编；“旧结果已由主审复核”的事实来自任务指令。本路直接阅读了所用的 YiNXNote、YiNXFull 对应定义、YiHCRel、YiGIEnd/Inst/Block/Check 的相关源码及 mc 调用处。
- 简报提到的 YiNX/GI 历史回报、YiCFCofin 的内部证明本轮未另读；没有把它们报告为本路独立复核结果。直接调用的 YiCFMono 出口签名已读，依赖正确性由冻结接口及新文件类型检查承接。

#### 6. 目录、日志、冻结散列

私有实验目录：<实验目录>

要求的完整回报：<临时目录>

frozen/ 是五个定稿源文件的快照；frozen-sha256.json 保存散列。所有临时源文件、辅助脚本和日志都保留，未删除实验材料。数学文件不包含本机路径。

- <实验目录>/Mini.agda
- <实验目录>/Mini.agdai
- <实验目录>/Mini.log
- <实验目录>/Mini2.log
- <实验目录>/Mini3.log
- <实验目录>/Mini4.log
- <实验目录>/Mini5.log
- <实验目录>/Samples.agda
- <实验目录>/Samples.agdai
- <实验目录>/Samples.log
- <实验目录>/Samples2.log
- <实验目录>/Samples3.log
- <实验目录>/YiMXEnd-cold.log
- <实验目录>/YiMXEnd.log
- <实验目录>/YiMXIface-cold.log
- <实验目录>/YiMXNeg-cold.log
- <实验目录>/YiMXNeg.log
- <实验目录>/YiMXNote-cold.log
- <实验目录>/YiMXNote.log
- <实验目录>/YiMXNote2.log
- <实验目录>/YiMXSamples-cold.log
- <实验目录>/YiMXSamples.log
- <实验目录>/audit.json
- <实验目录>/cold-results.json
- <实验目录>/cold-run.log
- <实验目录>/cold.py
- <实验目录>/frozen-sha256.json
- <实验目录>/libraries
- <实验目录>/make-report.log
- <实验目录>/make_report.py
- <实验目录>/search.log
- <实验目录>/search.py
- <实验目录>/search2.log
- <实验目录>/search2.py

定稿源码 SHA-256：

- probes/OCF/Lean/YiMXIface.lagda.md: 3f528e28d7902aa8d7539c14057746907f6c3f245dd162ec75179fd5ddfc6b98
- probes/OCF/Lean/YiMXNote.lagda.md: 71c110a26791a76c260db93eab9a7f90861a4a87fcf3e586439d01e87b8ed8a0
- probes/OCF/Lean/YiMXSamples.lagda.md: e0524359f6d1f73ae83937cf28f56c03204c59dae720e63f2e9106f221122fd2
- probes/OCF/Lean/YiMXNeg.lagda.md: e66966c0a014485ee0ac07eaa513dee99bd1c374b8639c89f56dbe62c75158b2
- probes/OCF/Lean/YiMXEnd.lagda.md: 5773f60244330851ea49d383e246636ae004bdb57b12322ecbd601a75bfe4b65

#### 附录 A：五个定稿源码全文

##### YiMXIface

### 无标准形前提的项序出口陈述
> 验收文件（读记号）。`Mono` 是构造与否定共用的陈述；不要求标准形或可数性。
> `YiMXNote.¬Mono` 的反例两端都可数，因而只补可数性不能恢复这条陈述。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXIface where
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiRefTw2 using (Rt)

Mono : Set
Mono = ∀ {s t} → s ≤ᵀ t → (h : HC s) (h′ : HC t) → Rt h ≼ Rt h′
```

##### YiMXNote

### 全域单调的最小反例与配对检查
> 验收文件（读记号），编译定理：项序有 1 + ω + 1 <ᵀ ω，两端有 HC、Ctbl，但参照值不满足该方向的 ≼。
> ¬Mono 否定共用陈述；W k 与 N k 的双向值比较及非相邻的 W 0、W 2 给肯定侧检查。
> 来源：复用 YiNXNote、YiCFMono、YiRefTw2 与 YiNFO.s≼-irrefl；不改树、折叠、合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXNote where
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-asym)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiNXNote using (W; N; hW; hN; nfN; W<N; W≼N; N≼W)
open import OCF.Lean.YiMXIface using (Mono)
forward : ∀ k → W k ≤ᵀ N k
forward k = inj₁ (W<N k)
reverse-impossible : ∀ k → N k ≤ᵀ W k → ⊥
reverse-impossible k (inj₁ p) = <ᵀ-asym (W<N k) p
reverse-impossible k (inj₂ ())
small-forward : Rt (hW 1) ≼ Rt (hN 1)
small-forward = W≼N 1 (hW 1) (hN 1)
small-backward : Rt (hN 1) ≼ Rt (hW 1)
small-backward = N≼W 1 (hN 1) (hW 1)

open import Data.Nat using (suc)
open import Data.Nat.Properties using (n≤1+n)
open import OCF.Lean.YiCFMono using (mono≤ⁿ; mono<ⁿ)
open import OCF.Lean.YiDCRel using (nat≤)
open import Data.List using ([]; _∷_)
open import OCF.Align.EboLeanDef using (T; ψ; 𝟏; natT; fsn; h1; hω; _<ᵀ_; hd<; ar<; []<)
open import OCF.Align.EboLeanBase using (NF; Ctbl; c∷; c[]; nf-ψ; n[])
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiANEnd using (natB; flatN)
open import OCF.Lean.YiNFOCase using (flatGB)
open import OCF.Lean.YiMHLean using (ctN)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiRefTw2 using (tree-≼)
open import OCF.Align.Value using (s≼s; z≼; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiNFO using (s≼-irrefl)
import OCF.Align.Level as L
bad pre : T
pre = 𝟏 ∷ ψ [] (natT 1) ∷ []
bad = 𝟏 ∷ ψ [] (natT 1) ∷ 𝟏 ∷ []
hnat : ∀ n → HC (natT n)
hnat n = hc (natB n) (ctN n)
hpre : HC pre
hpre = hω refl (λ n → subst HC (sym (cong (𝟏 ∷_) (rep1 n))) (hnat (suc n)))
hbad : HC bad
hbad = h1 refl hpre
hωt : HC ωᵀ
hωt = hω refl (λ n → subst HC (sym (rep1 n)) (hnat n))
bad<ω : bad <ᵀ ωᵀ
bad<ω = hd< (ar< []<)
ω≼pre : Rt hωt ≼ Rt hpre
ω≼pre = l≼ (λ n → ≼l n
  (≼-trans (tree-≼ (rep1 n) _ (hnat n))
    (≼-trans (mono≤ⁿ (natB n) (natB (suc n)) (ctN (suc n)) (hnat n) (hnat (suc n)) (nat≤ (n≤1+n n)))
      (tree-≼ (sym (cong (𝟏 ∷_) (rep1 n))) (hnat (suc n)) _))))

¬Mono : Mono → ⊥
¬Mono m = s≼-irrefl (Rt hωt) (≼-trans (s≼s ω≼pre) (m (inj₁ bad<ω) hbad hωt))

ct-bad : Ctbl bad
ct-bad = c∷ (c∷ (c∷ c[]))

ct-ω : Ctbl ωᵀ
ct-ω = c∷ c[]

bad-value : Rt hbad ≼ Rt hωt → ⊥
bad-value q = s≼-irrefl (Rt hωt) (≼-trans (s≼s ω≼pre) q)

nf-ω : NF ωᵀ
nf-ω = nf-ψ n[] (natB 1) (flatGB (flatN 1))

¬nf-bad : NF bad → ⊥
¬nf-bad ns = bad-value (mono≤ⁿ ns nf-ω ct-ω hbad hωt (inj₁ bad<ω))

N0<N2 : N 0 OCF.Align.EboLeanDef.<ᵀ N 2
N0<N2 = hd< (ar< (hd< (OCF.Align.EboLeanDef.lv< (OCF.Align.EboLeanDef.tl< []<))))

W0<W2 : W 0 OCF.Align.EboLeanDef.<ᵀ W 2
W0<W2 = hd< (ar< (hd< (OCF.Align.EboLeanDef.lv< []<)))

W0≼W2 : Rt (hW 0) ≼ Rt (hW 2)
W0≼W2 = ≼-trans (W≼N 0 (hW 0) (hN 0))
  (≼-trans (mono≤ⁿ (nfN 0) (nfN 2) (c∷ c[]) (hN 0) (hN 2) (inj₁ N0<N2))
    (N≼W 2 (hN 2) (hW 2)))

¬W2≼W0 : Rt (hW 2) ≼ Rt (hW 0) → ⊥
¬W2≼W0 q = s≼-irrefl (Rt (hN 0))
  (≼-trans (mono<ⁿ (nfN 0) (nfN 2) (c∷ c[]) (hN 0) (hN 2) N0<N2)
    (≼-trans (N≼W 2 (hN 2) (hW 2)) (≼-trans q (W≼N 0 (hW 0) (hN 0)))))
```

##### YiMXSamples

### 非相邻层的单项反例
> 验收文件（读记号），编译定理：A = ψ₀(ψ₁(Ω₃)) 有 HC，项序低于 N = ψ₀(Ω₂)，但 N 的后继值不高于 A。
> pathA 的十七次基本列取支给值下界；不是对任意层号的定理，也不改树、折叠或合法性。
> 来源：HC 使用 YiDCCheck.Two 的闭合两次折叠；fromOld 照 YiNXFull.fromM 改为旧基础关系；值工具复用 YiRefTw2。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXSamples where
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω; cof; cω; fsn; _<ᵀ_; hd<; ar<; lv<; tl<; []<)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiANEnd using (nat<)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s)
open import OCF.Lean.YiRefTw2 using (Rt; fs≼; hω-inv; tree-≼)
open import OCF.Lean.YiNXNote using (W; N; hW; hN; nfN; N≼W; W≼N)
open import OCF.Lean.YiNFO using (s≼-irrefl)
import OCF.Align.Level as L
import OCF.Lean.YiMEBase as Old
import OCF.Lean.YiDCCheck as DC
fromOld : ∀ {t x} → Old.M⁰ t x → HC t
fromOld Old.mz = h0 refl
fromOld (Old.m1 e m) = h1 e (fromOld m)
fromOld (Old.mL e f) = hω e (λ n → fromOld (f n))
fromOld (Old.mΩ {p = ()} _ _ _)
fromOld (Old.mU {c = ()} _ _)
fromOld (Old.mw m _) = fromOld m
module Two = DC.Two tt tt tt tt
opaque
  hA : HC (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))
  hA = fromOld Two.wit₂
A<N : ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)) <ᵀ N 1
A<N = hd< (ar< (hd< (lv< (nat< 1))))
N≼A : Rt (hN 1) ≼ Rt hA
N≼A = ≼-trans (N≼W 1 (hN 1) (hW 1))
  (≼-trans (tree-≼ refl (hW 1) (hω-inv hA refl 0)) (fs≼ hA refl 0))

trace : List ℕ → OCF.Align.EboLeanDef.T → OCF.Align.EboLeanDef.T
trace [] t = t
trace (n ∷ ns) t = trace ns (fsn t n)

Allω : List ℕ → OCF.Align.EboLeanDef.T → Set
Allω [] t = ⊤
Allω (n ∷ ns) t = (cof t ≡ cω) × Allω ns (fsn t n)

walk : ∀ ns {t} → Allω ns t → HC t → HC (trace ns t)
walk [] e h = h
walk (n ∷ ns) (e , es) h = walk ns es (hω-inv h e n)

walk≼ : ∀ ns {t} (e : Allω ns t) (h : HC t) → Rt (walk ns e h) ≼ Rt h
walk≼ [] e h = tree-≼ refl h h
walk≼ (n ∷ ns) (e , es) h = ≼-trans (walk≼ ns es (hω-inv h e n)) (fs≼ h e n)

pathA : List ℕ
pathA = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ []

pathA-ω : Allω pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))
pathA-ω = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt

lastA : trace pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) ≡ (OCF.Align.EboLeanDef.ψ [] (ψᴺ 1 (Ωᴺ 2)) ∷ OCF.Align.EboLeanDef.𝟏 ∷ [])
lastA = refl

N≺A : L.suc (Rt (hN 1)) ≼ Rt hA
N≺A = ≼-trans (s≼s (N≼W 1 (hN 1) (hW 1)))
  (≼-trans (tree-≼ (sym lastA) (h1 refl (hW 1)) (walk pathA pathA-ω hA))
    (walk≼ pathA pathA-ω hA))

¬A≼N : Rt hA ≼ Rt (hN 1) → ⊥
¬A≼N q = s≼-irrefl (Rt (hN 1)) (≼-trans N≺A q)
```

##### YiMXNeg

### 反例确实属于带 mc 的零层关系
> 验收文件（读记号），编译定理：`bad-mc` 是同一个反例的合法关系推导，故无条件的 `Exit′` 不成立。
> `¬ex-bad` 也否定该具体推导的出口证据；不据此否定规范塔上的出口。
> 来源：复用 `YiHCCheck.of⁰`、`YiCLCrit.ωᶜ-M`；自然数参照的比较沿后继递归。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXNeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.EboLeanDef using (HC; h0; h1; natT; ψ; Ωt)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiANFam using (cof-nat; pred-nat)
open import OCF.Lean.YiCLFam using (nat)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᶜ-M)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiKVRel using (readRW)
open import OCF.Lean.YiHCRel using (M⁰; mc; Exᴴ; exitᴴ)
open import OCF.Lean.YiHCCheck using (of⁰)
open import OCF.Lean.YiMXNote using (bad; hbad; hωt; bad<ω; bad-value)

bad-mc : M⁰ bad ωᶜ
bad-mc = mc (inj₁ bad<ω) (of⁰ ωᶜ-M)

bad≢singleton : ∀ u a → bad ≡ (ψ u a ∷ []) → ⊥
bad≢singleton u a ()

bad≢Ω : ∀ u → bad ≡ Ωt u → ⊥
bad≢Ω u ()

hn : ∀ n → HC (natT n)
hn zero = h0 refl
hn (suc n) = h1 (cof-nat n) (subst HC (sym (pred-nat n)) (hn n))

back-nat : ∀ n → readRW (nat n) ≼ Rt (hn n)
back-nat zero = z≼
back-nat (suc n) = s≼s (≼-trans (back-nat n)
  (tree-≼ (sym (pred-nat n)) (hn n) _))

back-ω : readRW ωᶜ ≼ Rt hωt
back-ω = l≼ (λ n → ≼l n (≼-trans (back-nat n)
  (tree-≼ (sym (rep1 n)) (hn n) (hω-inv hωt refl n))))

Exit′ : Set
Exit′ = ∀ {s x} (m : M⁰ s x) → (h : HC s) → Rt h ≼ readRW x

¬Exit′ : Exit′ → ⊥
¬Exit′ ex = bad-value (≼-trans (ex bad-mc hbad) back-ω)

¬ex-bad : Exᴴ bad-mc → ⊥
¬ex-bad ex = bad-value (≼-trans (exitᴴ bad-mc ex hbad) back-ω)
```

##### YiMXEnd

### 连同出口证据返回的低层保持
> 验收文件（读记号），条件定理：`Leaf`、`Lift`、`LowKeepᴱ` 推出主线终点的 EBO 序数值下界。
> `LowKeepᴱ` 将零层出口证据与推导放在同一结论；三条全域律仍未实填，不声称无条件达到 EBO。
> 来源：`YiGIEnd.Assembly`；零层的基础关系片段调用 `YiTBFam.Qu`、`YiHCCheck.of⁰/ex-of⁰`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXEnd where
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiMTTab as MT
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiGIBlock using (Bsᵍ; ψᵍ)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; Bdᵍ; keelᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open Laws gradedᵍ domsᵍ using (Leaf; Lift; LowKeep; Gb; Wl; Gx)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)

Exᵍ : ∀ j {s x} → GR.R j s x → Set
Exᵍ B.zero m = H.Exᴴ m
Exᵍ (B.nd s h) m = ⊤

LowKeepᴱ : Set
LowKeepᴱ = ∀ {ℓ j} (b : Bsᵍ ℓ) (w : j P.≤ ℓ) (β : O.Tr⁺ j) (t₀ : E.T)
  → Gb ℓ b → Wl w → Bdᵍ b w β t₀
  → ∀ {a x} → Gx ℓ x → GR.R ℓ a x
  → Σ (GR.R j (E.ψ [] (t₀ ++ a) ∷ []) (proj₁ (ψᵍ ℓ b j w β x))) (Exᵍ j)

forgetᴱ : LowKeepᴱ → LowKeep
forgetᴱ f b w β t₀ gb wl bd gx m = proj₁ (f b w β t₀ gb wl bd gx m)

module End (lf : Leaf) (li : Lift) (f : LowKeepᴱ) where
  module A = GE.Assembly lf li (forgetᴱ f)

  exits : A.ExitCondition
  exits n = proj₂ (f (Keel⁻.b₀ keelᴱ n) (Keel⁻.w₀ keelᴱ n)
    (Keel⁻.β₀ keelᴱ n) (Keel⁻.K₀ keelᴱ n) (Keel⁻.gb keelᴱ n)
    (Keel⁻.wl keelᴱ n) (Keel⁻.bd keelᴱ n) (Keel⁻.gx keelᴱ n) (A.T.keelᴿ n))

  eboᴱ : toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  eboᴱ = GE.eboᵍ lf li (forgetᴱ f) exits

eboᴱ : Leaf → Lift → LowKeepᴱ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
eboᴱ = End.eboᴱ

low-zeroᴱ : (b : Bsᵍ B.zero) (β : O.Tr⁺ B.zero) (t₀ : E.T)
  → K.M⁰ (E.ψ [] t₀ ∷ []) (proj₁ β)
  → ∀ {a x} → K.M⁰ a x
  → Σ (GR.R B.zero (E.ψ [] (t₀ ++ a) ∷ [])
      (proj₁ (ψᵍ B.zero b B.zero P.self β x))) H.Exᴴ
low-zeroᴱ (o , r , b) β t₀ mb m = HC.of⁰ q , HC.ex-of⁰ q
  where
  q = TF.Qu {t = t₀} o r b P.self β mb m

startᴱ : Σ (GR.R B.zero (E.EBOψ 0)
  (proj₁ (ψᵍ B.zero (tt , tt , F.B₀ B.zero)
    B.zero P.self (O.Ωt B.zero) (proj₁ (O.Ωt B.zero))))) H.Exᴴ
startᴱ = low-zeroᴱ (tt , tt , F.B₀ B.zero) (O.Ωt B.zero) []
  (K.m1 {t = E.natT 1} refl K.mz) (K.m1 {t = E.natT 1} refl K.mz)
```

#### 附录 B：冷编日志全文

##### YiMXIface

```text
Checking OCF.Lean.YiMXIface (<仓库>/probes/OCF/Lean/YiMXIface.lagda.md).
  23,867,619,800 bytes allocated in the heap
   9,440,800,312 bytes copied during GC
     998,073,976 bytes maximum residency (33 sample(s))
       1,949,848 bytes maximum slop
            1667 MiB total memory in use (0 MiB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      5210 colls,     0 par    3.991s   4.093s     0.0008s    0.0052s
  Gen  1        33 colls,     0 par    0.237s   0.264s     0.0080s    0.0222s

  TASKS: 4 (1 bound, 3 peak workers (3 total), using -N1)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.001s elapsed)
  MUT     time    7.007s  (  6.890s elapsed)
  GC      time    4.229s  (  4.357s elapsed)
  EXIT    time    0.010s  (  0.005s elapsed)
  Total   time   11.248s  ( 11.253s elapsed)

  Alloc rate    3,406,194,411 bytes per MUT second

  Productivity  62.3% of total user, 61.2% of total elapsed

```

##### YiMXNote

```text
Checking OCF.Lean.YiMXNote (<仓库>/probes/OCF/Lean/YiMXNote.lagda.md).
  32,308,028,408 bytes allocated in the heap
  12,980,013,720 bytes copied during GC
   1,330,022,208 bytes maximum residency (32 sample(s))
       2,074,568 bytes maximum slop
            2222 MiB total memory in use (0 MiB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      7064 colls,     0 par    5.423s   5.548s     0.0008s    0.0049s
  Gen  1        32 colls,     0 par    0.276s   0.307s     0.0096s    0.0408s

  TASKS: 4 (1 bound, 3 peak workers (3 total), using -N1)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.002s  (  0.002s elapsed)
  MUT     time    9.362s  (  9.223s elapsed)
  GC      time    5.699s  (  5.855s elapsed)
  EXIT    time    0.012s  (  0.003s elapsed)
  Total   time   15.075s  ( 15.082s elapsed)

  Alloc rate    3,450,920,863 bytes per MUT second

  Productivity  62.1% of total user, 61.2% of total elapsed

```

##### YiMXSamples

```text
Checking OCF.Lean.YiMXSamples (<仓库>/probes/OCF/Lean/YiMXSamples.lagda.md).
  30,354,562,032 bytes allocated in the heap
  12,121,312,184 bytes copied during GC
   1,197,530,376 bytes maximum residency (35 sample(s))
       2,101,368 bytes maximum slop
            2056 MiB total memory in use (0 MiB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      6636 colls,     0 par    5.168s   5.291s     0.0008s    0.0047s
  Gen  1        35 colls,     0 par    0.269s   0.299s     0.0085s    0.0292s

  TASKS: 4 (1 bound, 3 peak workers (3 total), using -N1)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.001s elapsed)
  MUT     time    8.851s  (  8.723s elapsed)
  GC      time    5.438s  (  5.590s elapsed)
  EXIT    time    0.013s  (  0.002s elapsed)
  Total   time   14.302s  ( 14.316s elapsed)

  Alloc rate    3,429,597,945 bytes per MUT second

  Productivity  61.9% of total user, 60.9% of total elapsed

```

##### YiMXNeg

```text
Checking OCF.Lean.YiMXNeg (<仓库>/probes/OCF/Lean/YiMXNeg.lagda.md).
  33,137,218,648 bytes allocated in the heap
  13,397,073,824 bytes copied during GC
   1,393,144,976 bytes maximum residency (33 sample(s))
       1,182,024 bytes maximum slop
            2337 MiB total memory in use (0 MiB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      7243 colls,     0 par    5.541s   5.678s     0.0008s    0.0048s
  Gen  1        33 colls,     0 par    0.323s   0.361s     0.0109s    0.0500s

  TASKS: 4 (1 bound, 3 peak workers (3 total), using -N1)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.001s elapsed)
  MUT     time    9.628s  (  9.466s elapsed)
  GC      time    5.863s  (  6.039s elapsed)
  EXIT    time    0.014s  (  0.001s elapsed)
  Total   time   15.506s  ( 15.508s elapsed)

  Alloc rate    3,441,740,142 bytes per MUT second

  Productivity  62.1% of total user, 61.0% of total elapsed

```

##### YiMXEnd

```text
Checking OCF.Lean.YiMXEnd (<仓库>/probes/OCF/Lean/YiMXEnd.lagda.md).
  33,361,741,056 bytes allocated in the heap
  13,373,715,952 bytes copied during GC
   1,483,225,904 bytes maximum residency (36 sample(s))
       1,614,504 bytes maximum slop
            2576 MiB total memory in use (0 MiB lost due to fragmentation)

                                     Tot time (elapsed)  Avg pause  Max pause
  Gen  0      7289 colls,     0 par    5.646s   5.801s     0.0008s    0.0048s
  Gen  1        36 colls,     0 par    0.274s   0.307s     0.0085s    0.0451s

  TASKS: 4 (1 bound, 3 peak workers (3 total), using -N1)

  SPARKS: 0 (0 converted, 0 overflowed, 0 dud, 0 GC'd, 0 fizzled)

  INIT    time    0.001s  (  0.001s elapsed)
  MUT     time    9.842s  (  9.672s elapsed)
  GC      time    5.920s  (  6.108s elapsed)
  EXIT    time    0.016s  (  0.008s elapsed)
  Total   time   15.779s  ( 15.790s elapsed)

  Alloc rate    3,389,870,674 bytes per MUT second

  Productivity  62.4% of total user, 61.3% of total elapsed

```

#### 附录 C：临时源码与实验工具全文

##### Mini.agda

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Mini where
open import Data.Nat using (ℕ)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-asym)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiNXNote using (W; N; hW; hN; W<N; W≼N; N≼W)
Mono : Set
Mono = ∀ {s t} → s ≤ᵀ t → (h : HC s) (h′ : HC t) → Rt h ≼ Rt h′
forward : ∀ k → W k ≤ᵀ N k
forward k = inj₁ (W<N k)
reverse-impossible : ∀ k → N k ≤ᵀ W k → ⊥
reverse-impossible k (inj₁ p) = <ᵀ-asym (W<N k) p
reverse-impossible k (inj₂ ())
small-forward : Rt (hW 1) ≼ Rt (hN 1)
small-forward = W≼N 1 (hW 1) (hN 1)
small-backward : Rt (hN 1) ≼ Rt (hW 1)
small-backward = N≼W 1 (hN 1) (hW 1)

open import Data.Nat using (suc)
open import Data.Nat.Properties using (n≤1+n)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Lean.YiDCRel using (nat≤)
open import Data.List using ([]; _∷_)
open import OCF.Align.EboLeanDef using (T; ψ; 𝟏; natT; fsn; h1; hω; _<ᵀ_; hd<; ar<; []<)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Lean.YiANEnd using (natB)
open import OCF.Lean.YiMHLean using (ctN)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiRefTw2 using (tree-≼)
open import OCF.Align.Value using (s≼s; z≼; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiNFO using (s≼-irrefl)
import OCF.Align.Level as L
bad pre : T
pre = 𝟏 ∷ ψ [] (natT 1) ∷ []
bad = 𝟏 ∷ ψ [] (natT 1) ∷ 𝟏 ∷ []
hnat : ∀ n → HC (natT n)
hnat n = hc (natB n) (ctN n)
hpre : HC pre
hpre = hω refl (λ n → subst HC (sym (cong (𝟏 ∷_) (rep1 n))) (hnat (suc n)))
hbad : HC bad
hbad = h1 refl hpre
hωt : HC ωᵀ
hωt = hω refl (λ n → subst HC (sym (rep1 n)) (hnat n))
bad<ω : bad <ᵀ ωᵀ
bad<ω = hd< (ar< []<)
ω≼pre : Rt hωt ≼ Rt hpre
ω≼pre = l≼ (λ n → ≼l n
  (≼-trans (tree-≼ (rep1 n) _ (hnat n))
    (≼-trans (mono≤ⁿ (natB n) (natB (suc n)) (ctN (suc n)) (hnat n) (hnat (suc n)) (nat≤ (n≤1+n n)))
      (tree-≼ (sym (cong (𝟏 ∷_) (rep1 n))) (hnat (suc n)) _))))

¬Mono : Mono → ⊥
¬Mono m = s≼-irrefl (Rt hωt) (≼-trans (s≼s ω≼pre) (m (inj₁ bad<ω) hbad hωt))
```

##### Samples.agda

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module Samples where
open import Mini
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω; cof; cω; fsn; _<ᵀ_; hd<; ar<; lv<; tl<; []<)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiANEnd using (nat<)
open import OCF.Lean.YiCFMono using (mono<ⁿ)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s)
open import OCF.Lean.YiRefTw2 using (Rt; fs≼; hω-inv; tree-≼)
open import OCF.Lean.YiNXNote using (W; N; hW; hN; nfN; N≼W; W≼N)
open import OCF.Lean.YiNFO using (s≼-irrefl)
import OCF.Align.Level as L
import OCF.Lean.YiMEBase as Old
import OCF.Lean.YiDCCheck as DC
fromOld : ∀ {t x} → Old.M⁰ t x → HC t
fromOld Old.mz = h0 refl
fromOld (Old.m1 e m) = h1 e (fromOld m)
fromOld (Old.mL e f) = hω e (λ n → fromOld (f n))
fromOld (Old.mΩ {p = ()} _ _ _)
fromOld (Old.mU {c = ()} _ _)
fromOld (Old.mw m _) = fromOld m
module Two = DC.Two tt tt tt tt
opaque
  hA : HC (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))
  hA = fromOld Two.wit₂
A<N : ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)) <ᵀ N 1
A<N = hd< (ar< (hd< (lv< (nat< 1))))
N≼A : Rt (hN 1) ≼ Rt hA
N≼A = ≼-trans (N≼W 1 (hN 1) (hW 1))
  (≼-trans (tree-≼ refl (hW 1) (hω-inv hA refl 0)) (fs≼ hA refl 0))

trace : List ℕ → OCF.Align.EboLeanDef.T → OCF.Align.EboLeanDef.T
trace [] t = t
trace (n ∷ ns) t = trace ns (fsn t n)

Allω : List ℕ → OCF.Align.EboLeanDef.T → Set
Allω [] t = ⊤
Allω (n ∷ ns) t = (cof t ≡ cω) × Allω ns (fsn t n)

walk : ∀ ns {t} → Allω ns t → HC t → HC (trace ns t)
walk [] e h = h
walk (n ∷ ns) (e , es) h = walk ns es (hω-inv h e n)

walk≼ : ∀ ns {t} (e : Allω ns t) (h : HC t) → Rt (walk ns e h) ≼ Rt h
walk≼ [] e h = tree-≼ refl h h
walk≼ (n ∷ ns) (e , es) h = ≼-trans (walk≼ ns es (hω-inv h e n)) (fs≼ h e n)

pathA : List ℕ
pathA = 1 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 2 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ []

pathA-ω : Allω pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3)))
pathA-ω = refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , refl , tt

lastA : trace pathA (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) ≡ (OCF.Align.EboLeanDef.ψ [] (ψᴺ 1 (Ωᴺ 2)) ∷ OCF.Align.EboLeanDef.𝟏 ∷ [])
lastA = refl

N≺A : L.suc (Rt (hN 1)) ≼ Rt hA
N≺A = ≼-trans (s≼s (N≼W 1 (hN 1) (hW 1)))
  (≼-trans (tree-≼ (sym lastA) (h1 refl (hW 1)) (walk pathA pathA-ω hA))
    (walk≼ pathA pathA-ω hA))

¬A≼N : Rt hA ≼ Rt (hN 1) → ⊥
¬A≼N q = s≼-irrefl (Rt (hN 1)) (≼-trans N≺A q)
```

##### cold.py

```python
from pathlib import Path
import subprocess,json,time
root=Path.cwd()
scratch=Path(__file__).parent
modules=[
 ('YiMXIface','probes/_build/2.8.0.2/agda/OCF/Lean/YiMXIface.agdai'),
 ('YiMXNote','probes/_build/2.8.0.2/agda/OCF/Lean/YiMXNote.agdai'),
 ('YiMXSamples','probes/_build/2.8.0.2/agda/OCF/Lean/YiMXSamples.agdai'),
 ('YiMXNeg','probes/_build/2.8.0.2/agda/OCF/Lean/YiMXNeg.agdai'),
 ('YiMXEnd','probes/_build/2.8.0.2/agda/OCF/Lean/YiMXEnd.agdai'),
]
results=[]
for name,interface in modules:
 Path(interface).unlink(missing_ok=True)
 log=scratch/(name+'-cold.log')
 args=['agda','+RTS','-M5G','-s','-RTS','--library-file='+str(scratch/'libraries'),'-i','src','-i','probes','probes/OCF/Lean/'+name+'.lagda.md']
 start=time.monotonic()
 with log.open('w') as out:
  try:r=subprocess.run(args,stdout=out,stderr=subprocess.STDOUT,timeout=600);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 entry={'module':name,'exit':code,'seconds':round(time.monotonic()-start,2),'log':str(log)}
 results.append(entry)
 (scratch/'cold-results.json').write_text(json.dumps(results,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps(entry,ensure_ascii=False),flush=True)
 if code:raise SystemExit(code)
```

##### search.py

```python
from functools import cache
from collections import deque
Z=()
def p(u,a=Z): return ((u,a),)
ONE=p(0)
A=p(0,p(1,p(3)))
N=p(0,p(2))
@cache
def cof(t):
 if not t:return ('z',0)
 if len(t)>1:return cof(t[1:])
 u,a=t[0]
 if not a:return ('s',0) if u==0 else ('U',u)
 c,i=cof(a)
 if c in ['s','w']:return ('w',0)
 if c=='U':return ('U',i) if u>=i else ('w',0)
 return ('z',0)
@cache
def cmp(s,t):
 if not s:return -bool(t)
 if not t:return 1
 (u,a),*r=s;(v,b),*q=t
 if u!=v:return (u>v)-(u<v)
 k=cmp(a,b)
 return k or cmp(tuple(r),tuple(q))
@cache
def pred(t):
 if len(t)>1:return (t[0],)+pred(t[1:])
 return Z
@cache
def fsT(t,e):
 if not t:return Z
 if len(t)>1:return (t[0],)+fsT(t[1:],e)
 u,a=t[0]
 if not a:return e if u>0 else Z
 c,i=cof(a)
 return p(u,fsT(a,e)) if c=='U' and u>=i else t
@cache
def fsn(t,n):
 if not t:return Z
 if len(t)>1:return (t[0],)+fsn(t[1:],n)
 u,a=t[0]
 if not a:return Z
 c,i=cof(a)
 if c=='s':return ((u,pred(a)),)*n
 if c=='w':return p(u,fsn(a,n))
 if c=='U':
  e=p(i-1)
  for k in range(n):e=p(i-1,fsT(a,e))
  return p(u,fsT(a,e))
 return Z
@cache
def ing(u,t):
 ret=[]
 for v,a in t:
  if u<=v:ret+=[a]+list(ing(u,a))
 return tuple(ret)
@cache
def nf(t):
 for i,(u,a) in enumerate(t):
  if not nf(a) or any(cmp(z,a)>=0 for z in ing(u,a)):return False
  if i+1<len(t) and cmp((t[i],),(t[i+1],))<0:return False
 return True
@cache
def size(t):return sum(1+size(a) for _,a in t)
def show(t):return '0' if not t else '+'.join('P'+str(u)+'('+show(a)+')' for u,a in t)
q=deque([(A,())]);seen={A}
while q:
 t,path=q.popleft()
 if nf(t) and cmp(t,N)>0:
  print('FOUND',path,show(t),size(t),flush=True);break
 if len(path)>=14:continue
 c,i=cof(t)
 if c=='w':steps=[(n,fsn(t,n)) for n in [0,1,2,3]]
 elif c=='s':steps=[('p',pred(t))]
 else:steps=[]
 for n,v in steps:
  if v not in seen and size(v)<150:
   seen.add(v);q.append((v,path+(n,)))
else:print('not found',len(seen))
```

##### search2.py

```python
from functools import cache
from collections import deque
Z=()
def p(u,a=Z): return ((u,a),)
ONE=p(0)
A=p(0,p(1,p(3)))
N=p(0,p(2))
@cache
def cof(t):
 if not t:return ('z',0)
 if len(t)>1:return cof(t[1:])
 u,a=t[0]
 if not a:return ('s',0) if u==0 else ('U',u)
 c,i=cof(a)
 if c in ['s','w']:return ('w',0)
 if c=='U':return ('U',i) if u>=i else ('w',0)
 return ('z',0)
@cache
def cmp(s,t):
 if not s:return -bool(t)
 if not t:return 1
 (u,a),*r=s;(v,b),*q=t
 if u!=v:return (u>v)-(u<v)
 k=cmp(a,b)
 return k or cmp(tuple(r),tuple(q))
@cache
def pred(t):
 if len(t)>1:return (t[0],)+pred(t[1:])
 return Z
@cache
def fsT(t,e):
 if not t:return Z
 if len(t)>1:return (t[0],)+fsT(t[1:],e)
 u,a=t[0]
 if not a:return e if u>0 else Z
 c,i=cof(a)
 return p(u,fsT(a,e)) if c=='U' and u>=i else t
@cache
def fsn(t,n):
 if not t:return Z
 if len(t)>1:return (t[0],)+fsn(t[1:],n)
 u,a=t[0]
 if not a:return Z
 c,i=cof(a)
 if c=='s':return ((u,pred(a)),)*n
 if c=='w':return p(u,fsn(a,n))
 if c=='U':
  e=p(i-1)
  for k in range(n):e=p(i-1,fsT(a,e))
  return p(u,fsT(a,e))
 return Z
@cache
def ing(u,t):
 ret=[]
 for v,a in t:
  if u<=v:ret+=[a]+list(ing(u,a))
 return tuple(ret)
@cache
def nf(t):
 for i,(u,a) in enumerate(t):
  if not nf(a) or any(cmp(z,a)>=0 for z in ing(u,a)):return False
  if i+1<len(t) and cmp((t[i],),(t[i+1],))<0:return False
 return True
@cache
def size(t):return sum(1+size(a) for _,a in t)
def show(t):return '0' if not t else '+'.join('P'+str(u)+'('+show(a)+')' for u,a in t)
q=deque([(A,())]);seen={A}
while q:
 t,path=q.popleft()
 if len(t)>1 and t[0]==p(0,p(1,p(2)))[0]:
  print('FOUND',path,show(t),size(t),flush=True);break
 if len(path)>=13:continue
 c,i=cof(t)
 if c=='w':steps=[(n,fsn(t,n)) for n in [0,1,2,3]]
 elif c=='s':steps=[('p',pred(t))]
 else:steps=[]
 for n,v in steps:
  if v not in seen and size(v)<150:
   seen.add(v);q.append((v,path+(n,)))
else:print('not found',len(seen))
```

#### 附录 D：原始非冷编日志全文

##### Mini.log

```text
Checking Mini (<实验目录>/Mini.agda).
<实验目录>/Mini.agda:18.28-32: error: [ImpossibleConstructor.UnifyConflict]
The case for the constructor refl is impossible
because unification ended with a conflicting equation
  Agda.Builtin.List.List.[] ≟ OCF.Align.EboLeanDef.ψ
                              (OCF.Align.EboLeanDef.natT (ℕ.suc k)) Agda.Builtin.List.List.[]
                              Agda.Builtin.List.List.∷ Agda.Builtin.List.List.[]
Possible solution: remove the clause, or use an absurd pattern ().
when checking that the pattern refl has type
N k Relation.Binary.PropositionalEquality.≡ W k
```

##### Mini2.log

```text
Checking Mini (<实验目录>/Mini.agda).
```

##### Mini3.log

```text
<实验目录>/Mini.agda:54.28: error: [ParseError]
q<ERROR>  = mono≤ⁿ (natB n) (natB (suc ...
```

##### Mini4.log

```text
Checking Mini (<实验目录>/Mini.agda).
<实验目录>/Mini.agda:45.23-35: error: [UnequalTerms]
natT n !=
Data.List.replicate n (ψ [] (OCF.Align.EboLeanDef.pred (𝟏 ∷ [])))
of type Data.List.List OCF.Align.EboLeanDef.PT
when checking that the expression hnat (suc n) has type
HC (OCF.Align.EboLeanDef.fsn pre n)
```

##### Mini5.log

```text
Checking Mini (<实验目录>/Mini.agda).
```

##### Samples.log

```text
Checking Samples (<实验目录>/Samples.agda).
<实验目录>/Samples.agda:35.29-52: error: [UnequalTerms]
[] !=
OCF.Align.EboLeanDef.ψ [] [] Data.List.∷
OCF.Align.EboLeanDef.natT 0
of type Data.List.List OCF.Align.EboLeanDef.PT
when checking that the expression nat< 1 has type
OCF.Align.EboLeanDef.natT 1 <ᵀ OCF.Align.EboLeanDef.natT 3
```

##### Samples2.log

```text
Checking Samples (<实验目录>/Samples.agda).
```

##### Samples3.log

```text
Checking Samples (<实验目录>/Samples.agda).
```

##### YiMXEnd.log

```text
Checking OCF.Lean.YiMXEnd (<仓库>/probes/OCF/Lean/YiMXEnd.lagda.md).
```

##### YiMXNeg.log

```text
Checking OCF.Lean.YiMXNeg (<仓库>/probes/OCF/Lean/YiMXNeg.lagda.md).
```

##### YiMXNote.log

```text
Checking OCF.Lean.YiMXNote (<仓库>/probes/OCF/Lean/YiMXNote.lagda.md).
 Checking OCF.Lean.YiMXIface (<仓库>/probes/OCF/Lean/YiMXIface.lagda.md).
<仓库>/probes/OCF/Lean/YiMXNote.lagda.md:76.27-28: error: [ShouldBeEmpty]
OCF.Align.EboLeanBase.InG [] z (ψ [] [] ∷ []) should be empty, but
the following constructor patterns are valid:
  OCF.Align.EboLeanBase.gp {._} {._} {._} _
  OCF.Align.EboLeanBase.gtl {._} {._} {._} _
  Agda.Primitive.Cubical.primHComp {._} {._} {_} _ _
when checking that the expression λ () has type
OCF.Align.EboLeanBase.InG [] z (ψ [] [] ∷ []) → z <ᵀ ψ [] [] ∷ []
```

##### YiMXNote2.log

```text
Checking OCF.Lean.YiMXNote (<仓库>/probes/OCF/Lean/YiMXNote.lagda.md).
```

##### YiMXSamples.log

```text
Checking OCF.Lean.YiMXSamples (<仓库>/probes/OCF/Lean/YiMXSamples.lagda.md).
```

##### cold-run.log

```text
{"module": "YiMXIface", "exit": 0, "seconds": 11.36, "log": "<实验目录>/YiMXIface-cold.log"}
{"module": "YiMXNote", "exit": 0, "seconds": 15.23, "log": "<实验目录>/YiMXNote-cold.log"}
{"module": "YiMXSamples", "exit": 0, "seconds": 14.43, "log": "<实验目录>/YiMXSamples-cold.log"}
{"module": "YiMXNeg", "exit": 0, "seconds": 15.64, "log": "<实验目录>/YiMXNeg-cold.log"}
{"module": "YiMXEnd", "exit": 0, "seconds": 15.92, "log": "<实验目录>/YiMXEnd-cold.log"}
```

##### make-report.log

```text
```

##### search.log

```text
Traceback (most recent call last):
  File "<实验目录>/search.py", line 70, in <module>
    if nf(t) and cmp(t,N)>0:
  File "<实验目录>/search.py", line 61, in nf
    if not nf(a) or any(cmp(z,a)>=0 for z in ing(u,a)):return False
  File "<实验目录>/search.py", line 61, in <genexpr>
    if not nf(a) or any(cmp(z,a)>=0 for z in ing(u,a)):return False
  File "<实验目录>/search.py", line 24, in cmp
    k=cmp(a,b)
  File "<实验目录>/search.py", line 24, in cmp
    k=cmp(a,b)
  File "<实验目录>/search.py", line 22, in cmp
    (u,a),*r=s;(v,b),*q=t
KeyboardInterrupt
```

##### search2.log

```text
Traceback (most recent call last):
  File "<实验目录>/search2.py", line 74, in <module>
    if c=='w':steps=[(n,fsn(t,n)) for n in [0,1,2,3]]
  File "<实验目录>/search2.py", line 74, in <listcomp>
    if c=='w':steps=[(n,fsn(t,n)) for n in [0,1,2,3]]
  File "<实验目录>/search2.py", line 38, in fsn
    @cache
KeyboardInterrupt
```


# 出口的记号引理：非标准形见证项（数学，记号一侧） (YiNX)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十六批（“外部模型额度很充足，我们可以多线并行”）；外部模型，作者转发 |
| 前缀 | `YiNX` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：出口的记号引理：非标准形见证项（数学，记号一侧）（前缀 YiNX）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十六批六路之一（选项原文 "出口的记号引理（V157 ii）"），与并行的其他各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。原主线 `YiRWFold` 的值定理保留作参照。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **出口**（第 0 层的关系推出序数值的不等式）现在都带条件：见证项是可数标准形。
  - `YiDCExit.exitᴰ`；`YiMHRel.exit̂` 与条件 `Ex`（每片叶子上参照项与见证项是标准形、见证项可数）；`YiHCRel.exitᴴ` 与条件 `Exᴴ`（每个 `mc` 结点上两项为标准形、较大者可数）。
  - 用到的记号引理：`YiCFMono.mono≤ⁿ`（要 `NF s`、`NF t`、`Ctbl t`）、`YiMEBase.lower⁰`、`EboLeanTree.hc : NF t → Ctbl t → HC t`。
- **反例**：复合的折叠会产生非标准形的见证项。
  - `YiDCExit.¬nf₂ : NF (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) → ⊥`；
  - `YiMHLean.¬nf-wit : NF (ψᴺ 0 (ψᴺ 2 (Ωᴺ 3))) → ⊥` 与 `¬ex-low0`：孩子取 ω 的合成推导折到第 0 层后出口条件不成立。
- 台账 `probes/Survey/IdeaLedger.md` V157 (ii)。记号的定义：`OCF/Align/EboLeanDef`、`EboLeanBase`（`NF`、`GB`、`nf-ψ`、`nf-Ω`）、`EboLeanTree`、`EboLeanClosure`；共尾 `YiCFCofin`。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：在 t = ψ₀(ψ₂(Ω₃))（或 ψ₀(ψ₁(Ω₃))）上写出想要的陈述，例如 "s ≤ᵀ t、s 是标准形、t 有推导 → s 的参照值不高于 t 的参照值"；确认 t 有推导（`HC t`）、陈述有意义。不成立就停下回报。
1. **记号引理**，二选一或都做：
   - (a) 非标准形项上项序推出值序：对复合折叠产生的一族 t（形如 ψ_j(t₀ ++ ψ_k(…))），证上述陈述；
   - (b) 规范化：对有推导的 t，给出一个标准形 t′，两者参照值互相 ≼，并且项序关系能搬过去。
2. **接回出口**：用它去掉 `exitᴴ`（或 `exit̂`）的标准形条件，至少对 `¬ex-low0` 那一类推导；交一条无条件的出口定理，或交第一个挡住的引理。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiNX`（模块名 `OCF.Lean.YiNX…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiCD`、`YiDD`、`YiKQ`、`YiSP`、`YiXV`、`YiGI`、`YiVF`）。验收文件（读记号），文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有九路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
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



## 本会话主审复核（2026-11-14）

4 件、285 同口径代码行；主审逐件删自身接口、5G 独立冷编全部 0，各仅自身 Checking，编译期间源码哈希不变。禁用构造、洞、本机路径、Funext 命中 0。已逐字读过相邻层规范化、任取 HC 推导的双向值界、项序搬运及完整 low0 出口；原参数与前提均有闭合实例。Full 的 fromM 只适用于基础 M⁰，不可无证明搬到带 mc 的 Mᴴ。原整类 low0 出口已去 Ex/NF 条件；任意非标准形上的全局序单调与规范化未交。没有新增主线强度鉴定。

## 回报原文（本会话执行）

### YiNX 完整回报（2026-11-14，最终定稿）

#### 1. 判决与进度

对纲领与目标的意义：本轮在记号一侧处理了复合折叠产生的非标准形见证，没有反过来改树、折叠或合法性。已证相邻层族 ψ₀(ψₖ(Ωₖ₊₁)) 的参照值与标准形 ψ₀(Ωₖ₊₁) 互相 `≼`，以及所需方向的项序搬运；又对 `YiMHLean.¬ex-low0` 指出的**整类 low0 合成推导**给出不带 `Ex`、不要求标准形的出口。它仍是验收一侧的结果，不算树自足。

最终交付完成原简报的要求；不是只到第 0 片叶子。`YiNXFull.lowMove : LowMove`、`firstMissing : FirstMissing` 均有构造，前期留下的具名缺口已填。`Out.exit-low0` 保留原 low0 的构造参数与前提，不再加出口标准形条件或任何未证数学假设；`hLow` 构造其左参照的 HC，`full-example` 实填全部参数并交闭合值不等式。

第 0 步通过：临时 `YiNXCheck.agda` 取 t = ψ₀(ψ₂(Ω₃))，构造 `ht : HC t`，写出 `Wanted` 并证明 `wanted : Wanted`；非零标准形实例 s = ψ₀(Ω₂) 的 `ns/st/hs/instance-result` 均通过。临时目录 20:23:12 创建；首轮编译 20:24:03 写完（42，参数误填），20:24:40 修正通过，20:25:39 带 wanted 的完整目标证明通过。第一个临时检查在本轮开始后 30 分钟内已写出并编译。

第 1 步交相邻层族的记号引理与规范化：对所有 k，`W k = ψ₀(ψₖ(Ωₖ₊₁))` 有 HC，不是标准形，与 `N k = ψ₀(Ωₖ₊₁)` 互相 `≼`；`s ≤ᵀ W k` 搬到 `s ≤ᵀ N k`，标准形 s 上由此推出值序。不提供任意 HC 项的全局规范化算法，也不声称任意非标准形上的项序单调。

第 2 步完成到简报指定的 low0 类：`YiNXExit` 先将该族接入既有 `M̂` 叶子；`YiNXFull` 对 `A n = ψ₀(ψ₂(Ωₙ))` 证明统一等式 `A (n+1)[0] = A n`，从基础关系构造全部见证的 HC，沿三次第 0 支比较 A n 与 A (n+3)，从而得到整个 low0 出口。完整出口最后使用这条统一基本列比较；不要求先把非相邻层的每个见证规范化。

没有增加主线 EBO 的已鉴定强度下界。`hLow` 的原始记号项是 ψ₀(ψ₂(Ω_ω))，本轮没有把其值鉴定成 ψ₀(Ω_x)，不把这项写成新的强度站位。相邻层规范化的值鉴定则正是 ψ₀(Ω_{k+1})。

| 问题 | 位置 | 档 |
|---|---|---|
| 最小实例有 HC，目标前提可满足且值比较成立 | 临时 `YiNXCheck.ht/ns/st/hs/wanted/instance-result` | 编译定理 |
| 相邻层非标准形族的 HC、规范化、项序搬运 | `YiNXNote.hW/W≼N/N≼W/orderW/monoW/¬nfW` | 编译定理 |
| 原出口扩展到此族非标准形见证 | `YiNXExit.exitW/exitNX` | 编译定理；叶子新条件有实填 |
| low0 全部叶子见证及左参照都有 HC | `YiNXFull.fromM/Leaves.hWit/hWit-all/hA-all/hLow` | 编译定理 |
| 对所有 n 的基本列方程与三步值比较 | `YiNXFull.fsA0/upA/move` | 编译定理 |
| `LowMove`、`FirstMissing` 已实填 | `YiNXFull.lowMove/firstMissing` | 编译定理；不是具名假设 |
| 整个 low0 类的无标准形出口及闭合实例 | `YiNXFull.Out.exit-low0/full-example` | 编译定理；无未证数学假设 |
| 下一片见证的共尾度及第 0 个基本列项 | `YiNXLow.cofB₁/firstB₁` | 有限测试，编译通过 |
| 原相邻层平移等式不能原样用于下一片 | `YiNXLow.¬shift₄` | 编译否定定理，仅否定该闭项语法等式 |

#### 2. 文件、冷编与自查

代码行口径：Agda 代码块内非空、非整行注释行，包含模块头与导入。四份最终文件均删除自身接口后按 Note、Exit、Low、Full 顺序冷编；依赖保持既有接口，不用 ignore-interfaces。始终同时只有一个本路 Agda，每次 `+RTS -M5G -s -RTS`。

| 文件 | 物理行 | 代码行 | 冷编退出码 | maximum residency (bytes) | total memory (MiB) |
|---|---:|---:|---:|---:|---:|
| `<仓库>/probes/OCF/Lean/YiNXNote.lagda.md` | 94 | 67 | 0 | 1,293,119,720 | 2203 |
| `<仓库>/probes/OCF/Lean/YiNXExit.lagda.md` | 48 | 34 | 0 | 1,310,460,136 | 2249 |
| `<仓库>/probes/OCF/Lean/YiNXLow.lagda.md` | 119 | 87 | 0 | 1,277,969,384 | 2434 |
| `<仓库>/probes/OCF/Lean/YiNXFull.lagda.md` | 124 | 97 | 0 | 1,301,430,000 | 2184 |

RTS maximum residency 与 total memory 取自对应最终冷编日志，不把 5G 上限当成实测占用。四份最终日志各恰有一条自身模块的 Checking 行，无依赖 Checking、无警告、无错误。源码禁用构造、洞、本机绝对路径检索均为 0；未使用函数外延。审计数据和 SHA-256 保存在 `YiNX-audit.json`。

只新建或修订本轮 YiNX 前缀文件；没有改旧数学文件、其他路线前缀、导航、日志、台账、src 或 archive。主审最新指示要求 Full 通过后同步 Note/Low 的过时文首范围，已完成并重新冷编。未派子路、未提交、未推送。

复核命令（仓库根目录，替换模块名）：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiNXFull.lagda.md > <实验目录>/YiNXFull-final-cold.log 2>&1
code=$?
print -r -- "exit $code"
```

仅删除过本路接口，字面路径：

- `probes/_build/2.8.0.2/agda/OCF/Lean/YiNXNote.agdai`
- `probes/_build/2.8.0.2/agda/OCF/Lean/YiNXExit.agdai`
- `probes/_build/2.8.0.2/agda/OCF/Lean/YiNXLow.agdai`
- `probes/_build/2.8.0.2/agda/OCF/Lean/YiNXFull.agdai`

#### 3. 定理表

记法定义：`N k = ψᴺ 0 (Ωᴺ (suc k))`，`W k = ψᴺ 0 (ψᴺ k (Ωᴺ (suc k)))`，`G k n = γT (Ωᴺ (suc k)) (natT k) n`。Low 模块中 `A n = ψᴺ 0 (ψᴺ 2 (Ωᴺ n))`，`Wit n = A (suc (suc (suc n)))`，`lowTerm = ψᴺ 0 (ψᴺ 2 (E.Ωt ωᵀ))`。

下表逐字取源码签名，多行签名在表中并为一行。文件名均指第 2 节绝对路径。`First` 内的两条定理带如下模块参数，`example` 实填这些参数；Full 的 `Leaves` 与 `Out` 使用同样一组参数，`full-example` 实填：

```agda
module First (o : Ok (fn 2)) (r : Rb (fn 2)) (s : Tp 1 0) (b : Base (fn 2)) (ok : OKB b)
             (β : Tr⁺ (fn 0)) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) {c : Tr zero} (cc : Can c) (l : M⁰ ωᵀ c) where
```

| 名字 | 逐字陈述 | 一句白话 | 文件 | 档 |
|---|---|---|---|---|
| `nfN` | `nfN : ∀ k → NF (N k)` | 规范化目标为标准形 | `YiNXNote.lagda.md` | 编译定理 |
| `cofN` | `cofN : ∀ k → cof (N k) ≡ cω` | 规范化目标共尾度为 ω | `YiNXNote.lagda.md` | 编译定理 |
| `cofI` | `cofI : ∀ k → cof (ψᴺ k (Ωᴺ (suc k))) ≡ cω` | 内层折叠的共尾度为 ω | `YiNXNote.lagda.md` | 编译定理 |
| `cofW` | `cofW : ∀ k → cof (W k) ≡ cω` | 非标准形见证共尾度为 ω | `YiNXNote.lagda.md` | 编译定理 |
| `fsN` | `fsN : ∀ k n → fsn (N k) n ≡ ψᴺ 0 (G k n)` | 标准形参照的基本列方程 | `YiNXNote.lagda.md` | 编译定理 |
| `fsI` | `fsI : ∀ k n → fsn (ψᴺ k (Ωᴺ (suc k))) n ≡ ψᴺ k (G k n)` | 内层折叠的基本列方程 | `YiNXNote.lagda.md` | 编译定理 |
| `G-step` | `G-step : ∀ k n → G k (suc n) ≡ ψᴺ k (G k n)` | γ 链的下一步方程 | `YiNXNote.lagda.md` | 编译定理 |
| `shift` | `shift : ∀ k n → fsn (W k) n ≡ fsn (N k) (suc n)` | 非标准形基本列等于标准形基本列去掉第 0 项 | `YiNXNote.lagda.md` | 编译定理 |
| `first-step` | `first-step : ∀ k → fsn (N k) 0 <ᵀ fsn (N k) 1` | 被去掉的第 0 项低于第 1 项 | `YiNXNote.lagda.md` | 编译定理 |
| `W<N` | `W<N : ∀ k → W k <ᵀ N k` | 原见证项在语法序上低于规范化目标 | `YiNXNote.lagda.md` | 编译定理 |
| `hN` | `hN : ∀ k → HC (N k)` | 所有规范化目标都有 HC 推导 | `YiNXNote.lagda.md` | 编译定理 |
| `hW` | `hW : ∀ k → HC (W k)` | 所有非标准形见证都有 HC 推导 | `YiNXNote.lagda.md` | 编译定理 |
| `W≼N` | `W≼N : ∀ k (h : HC (W k)) (h′ : HC (N k)) → Rt h ≼ Rt h′` | 见证的参照值不高于标准形 | `YiNXNote.lagda.md` | 编译定理 |
| `N≼W` | `N≼W : ∀ k (h : HC (N k)) (h′ : HC (W k)) → Rt h ≼ Rt h′` | 标准形的参照值不高于见证 | `YiNXNote.lagda.md` | 编译定理 |
| `orderW` | `orderW : ∀ k {s} → s ≤ᵀ W k → s ≤ᵀ N k` | 所需方向的项序关系搬到标准形 | `YiNXNote.lagda.md` | 编译定理 |
| `monoW` | `monoW : ∀ k {s} → NF s → s ≤ᵀ W k → (h : HC s) (h′ : HC (W k)) → Rt h ≼ Rt h′` | 标准形左项在 W 下的项序推出参照值序 | `YiNXNote.lagda.md` | 编译定理 |
| `¬nfW` | `¬nfW : ∀ k → NF (W k) → ⊥` | 这族见证确实不是标准形 | `YiNXNote.lagda.md` | 编译定理 |
| `exitW` | `exitW : ∀ {X : Set} {R : T → X → Set} (v : X → L.Ordᶜ L.zero) → (∀ {t x} → R t x → (h : HC t) → Rt h ≼ v x) → ∀ k {s x} → NF s → s ≤ᵀ W k → R (W k) x → (h : HC s) → Rt h ≼ v x` | 基础出口接收 W 见证，不要求 NF W | `YiNXExit.lagda.md` | 编译定理 |
| `oldNX` | `oldNX : ∀ {X : Set} {R : T → X → Set} {s x} (m : M̂ R s x) → Ex m → ExNX m` | 原来的出口条件蕴含新条件 | `YiNXExit.lagda.md` | 编译定理 |
| `exitNX` | `exitNX : ∀ {X : Set} {R : T → X → Set} (v : X → L.Ordᶜ L.zero) → (∀ {t x} → R t x → (h : HC t) → Rt h ≼ v x) → ∀ {s x} (m : M̂ R s x) → ExNX m → (h : HC s) → Rt h ≼ v x` | 既有 M̂ 关系在新叶子条件下的出口 | `YiNXExit.lagda.md` | 编译定理 |
| `fsLow` | `fsLow : ∀ n → fsn lowTerm n ≡ A n` | low0 的参照项第 n 个基本列项正是 A n | `YiNXLow.lagda.md` | 编译定理 |
| `nf-small` | `nf-small : ∀ m → m ≤ⁿ 2 → NF (A m)` | 前 3 个左参照项有标准形证明 | `YiNXLow.lagda.md` | 编译定理 |
| `hA₀` | `hA₀ : HC (A 0)` | 第 0 片左参照项有 HC | `YiNXLow.lagda.md` | 编译定理 |
| `hA₁` | `hA₁ : HC (A 1)` | 第 1 片左参照项有 HC | `YiNXLow.lagda.md` | 编译定理 |
| `leAB` | `leAB : ∀ n → A n ≤ᵀ Wit n` | 全部叶子的语法比较均已满足 | `YiNXLow.lagda.md` | 编译定理 |
| `First.first-base` | `first-base : M⁰ (W 2) (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))` | 实际折叠的输出承接第 0 片非标准形见证 | `YiNXLow.lagda.md` | 编译定理 |
| `First.first-exit` | `first-exit : (h : HC (A 0)) → Rt h ≼ readRW (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))` | 第 0 片叶子通过新出口 | `YiNXLow.lagda.md` | 编译定理 |
| `example` | `example : Rt hA₀ ≼ readRW (proj₁ (ψ (fn 2) (okf 2) (rb-no (fn 2)) (B₀ (fn 2)) (fn 0) (tp (tc (ss s0))) (Ωt (fn 0)) (proj₁ (gˢ ωᶜ))))` | 第 0 片叶子出口的闭合参数实例 | `YiNXLow.lagda.md` | 编译定理 |
| `at-zero` | `at-zero : Σ (HC (Wit 0)) λ h′ → (h : HC (A 0)) → Rt h ≼ Rt h′` | LowMove 的第 0 项已填 | `YiNXLow.lagda.md` | 编译定理 |
| `cofB₁` | `cofB₁ : cof (Wit 1) ≡ cω` | 下一片见证的共尾度计算为 ω | `YiNXLow.lagda.md` | 有限测试（编译通过） |
| `firstB₁` | `firstB₁ : fsn (Wit 1) 0 ≡ W 2` | 下一片见证的第 0 个基本列项为 W 2 | `YiNXLow.lagda.md` | 有限测试（编译通过） |
| `¬shift₄` | `¬shift₄ : fsn (Wit 1) 0 ≡ fsn (N 3) 1 → ⊥` | 下一片不满足原来的相邻层平移等式 | `YiNXLow.lagda.md` | 编译定理 |

| 名字 | 逐字陈述 | 一句白话 | 文件 | 档 |
|---|---|---|---|---|
| `fromM` | `fromM : ∀ {t x} → M⁰ t x → HC t` | 第 0 层基础推导本身递归给出 HC | `YiNXFull.lagda.md` | 编译定理 |
| `Leaves.leaf-base` | `leaf-base : ∀ n → M⁰ (Wit n) (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))` | 全部实际叶子见证对着折叠输出 | `YiNXFull.lagda.md` | 编译定理 |
| `Leaves.hWit` | `hWit : ∀ n → HC (Wit n)` | 该模块参数下所有见证有 HC | `YiNXFull.lagda.md` | 编译定理 |
| `hWit-all` | `hWit-all : ∀ n → HC (Wit n)` | 实例化后给出全部闭合见证的 HC | `YiNXFull.lagda.md` | 编译定理 |
| `cofA` | `cofA : ∀ n → cof (A n) ≡ cω` | A n 对所有 n 共尾度均为 ω | `YiNXFull.lagda.md` | 编译定理 |
| `cofAbove` | `cofAbove : ∀ n → cof (ψᴺ 2 (Ωᴺ (suc (suc (suc n))))) ≡ cω` | 高于层 2 的内层折叠共尾度为 ω | `YiNXFull.lagda.md` | 编译定理 |
| `fsAbove0` | `fsAbove0 : ∀ n → fsn (ψᴺ 2 (Ωᴺ (suc (suc (suc n))))) 0 ≡ ψᴺ 2 (Ωᴺ (suc (suc n)))` | 内层折叠第 0 项的统一方程 | `YiNXFull.lagda.md` | 编译定理 |
| `fsA0` | `fsA0 : ∀ n → fsn (A (suc n)) 0 ≡ A n` | A (n+1) 的第 0 个基本列项就是 A n | `YiNXFull.lagda.md` | 编译定理 |
| `hcDown` | `hcDown : ∀ n → HC (A (suc n)) → HC (A n)` | 沿上述第 0 支取得左项的 HC | `YiNXFull.lagda.md` | 编译定理 |
| `hA-all` | `hA-all : ∀ n → HC (A n)` | 所有 A n 都有 HC | `YiNXFull.lagda.md` | 编译定理 |
| `hLow` | `hLow : HC lowTerm` | 完整 low0 左参照有 HC | `YiNXFull.lagda.md` | 编译定理 |
| `upA` | `upA : ∀ n (h : HC (A n)) (h′ : HC (A (suc n))) → Rt h ≼ Rt h′` | 沿一次第 0 支给出值比较 | `YiNXFull.lagda.md` | 编译定理 |
| `move` | `move : ∀ n (h : HC (A n)) (h′ : HC (Wit n)) → Rt h ≼ Rt h′` | 沿三次第 0 支给出全部叶子的值比较 | `YiNXFull.lagda.md` | 编译定理 |
| `lowMove` | `lowMove : LowMove` | 实填 Low 模块的 LowMove | `YiNXFull.lagda.md` | 编译定理 |
| `firstMissing` | `firstMissing : FirstMissing` | 实填早期留下的 FirstMissing | `YiNXFull.lagda.md` | 编译定理 |
| `Out.exit-low0` | `exit-low0 : (h : HC lowTerm) → Rt h ≼ readRW (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))` | 整类 low0 的出口无 Ex 或标准形前提 | `YiNXFull.lagda.md` | 编译定理 |
| `full-example` | `full-example : Rt hLow ≼ readRW (proj₁ (ψ (fn 2) (okf 2) (rb-no (fn 2)) (B₀ (fn 2)) (fn 0) (tp (tc (ss s0))) (Ωt (fn 0)) (proj₁ (gˢ ωᶜ))))` | 完整出口的闭合参数实例 | `YiNXFull.lagda.md` | 编译定理 |

`exitW`、`exitNX` 的 `low` 前提由 `YiKVRel.lower⁰` 实填；`ExNX` 在 `First.first-exit` 的推导上取 `inj₂ (2 , nf-small 0 z≤n , refl)`，不是未给实例的新公理。标准形支直接承接旧条件，`oldNX` 给出包含关系。`nf-small` 的界由 `z≤n`、`s≤s z≤n` 等实例满足；hA₀、hA₁ 已填。`monoW` 的非零标准形前提实例是临时文件的 ψ₀(Ω₂)；实际第 0 片则是 A 0。

`W≼N`、`N≼W` 对两边任取 HC 推导，结果不依赖选定推导；这里没有进一步证明不同写法的 FGH 值相等。

#### 4. 第一个障碍及其最终处理

最先出现的数学切点是非相邻见证 ψ₀(ψ₂(Ω₄)) 不满足相邻层引理的平移等式。`YiNXLow.¬shift₄` 编译证明的只是不等式两端语法树不相等；它没有否定值的规范化，也没有否定这条出口路线。不得把它归成既有墙的一例。

这个切点最终已解决，不再有原任务内的具名未证前提。新做法无需先规范化全部非相邻见证：

```agda
fromM : ∀ {t x} → M⁰ t x → HC t
fsA0 : ∀ n → fsn (A (suc n)) 0 ≡ A n
move : ∀ n (h : HC (A n)) (h′ : HC (Wit n)) → Rt h ≼ Rt h′
lowMove : LowMove
firstMissing : FirstMissing
```

`fromM` 对 mz/m1/mL/mw 递归；第 0 层的 mΩ/mU 不可能出现。`Leaves.leaf-base` 直接复用 LF 与 ω̃ˢ 的全体叶子构造，因而供给每个 Wit n 的 HC。`hcDown` 三次从 Wit n 取得 A n 的 HC；`upA` 与 `move` 再沿同样的三次第 0 支给出值比较。对原参照的 HC 用 `fsLow` 对齐叶子，以 fs-sup 结束。全部是检查器接受的定义及证明，无改变树定义、折叠或合法性的步骤。

最先遇到的工程阻碍定位在 hA-all 对闭项 A 2 调用标准形的良基 HC 构造处：含该声明的无洞前缀 60 秒未完成，而删去该声明、保留其前全部定义的前缀通过。没有把超时说成类型错误或否定定理。最终 hA-all 改为从既有 Wit n 沿三次第 0 支读取 HC，去掉该闭项良基构造的实例化；数学陈述不变，整文件与冷编均通过。

剩余的全局问题超出本简报这次选择的实例族：任意非标准形项上的项序单调、任意 HC 项的规范化，以及无条件消去所有 M̂/Mᴴ 推导中的标准形限制，均未声称完成。本轮完成的是相邻层引理与指定 low0 整类出口。

候选与放下的办法，供主审记账（判断均不作路线否定）：

- 相邻层的“删去首项”规范化是已证的一般 k 结果，保留。
- 对非相邻层逐个扩展同一个平移语法等式：具体等式被 ¬shift₄ 否定；没有继续以这条等式扩展。
- 全部非相邻见证另做规范化：没有判定不可行；因统一第 0 支比较已经完成指定出口，本轮未继续发展。
- M⁰ → HC 是通用已编译引理；量化域是基础关系，不能未经证明搬到含 mc/ĉ 的封闭关系。
- 沿树侧已有推导取得 HC，再用规范叶子对齐作值比较：本轮已实填到低层的这一合成族，未上升成任意项序规则。

#### 5. 偏离、事故与阅读范围

范围与停止条件：保持原任务的非标准形见证与出口问题，没有改题或额外派路线。早期回报草稿只记到 FirstMissing，主审要求继续后没有以几份有用文件结束；最终该切点已填。未发生 5G 耗尽，没有擅自加堆。没有触发同处两次数学重新设计仍过不了检查器的停止条件；长检查按工程定位处理，最终陈述通过。

工程记录：

- `YiNXCheck` 首轮 42：nf-low 所需 3 ≤ 3 误填 0 ≤ 3，改 ≤-refl；不存在的 ≤-trans 导入警告改用真实 ≤-<。后续目标证明版本 0、无警告。
- `YiNXExit` 首轮 42：隐式载体 {X} 的层级元变量，显式 {X : Set} 后通过。
- `YiNXLow` 首轮 42：B 与块字段 B 重名，改 Wit 后通过。
- `YiNXStepCheck` 首轮 42：在组合折叠中直接 rewrite 未继续作用到后续显露的内层共尾度；改成已有 fsnψω 方程的复合，第二轮 0。不是数学反例。
- `YiNXFull` 首轮 42：down 与 YiRWOps 的同名字段冲突，改 fsA0。
- Full 第二、三次完整检查长时间归约，分别人工 INT，退出 130；后者在 600 秒限时前中止。只中止已核对命令行属于本路的 PID 80910、81616，未 pkill，未动其他路。查询进程的普通沙箱调用曾受限，之后仅读取工具授权的进程信息来核对本路进程。
- Full 声明跟踪限时检查 124；带原 hA-all 的临时前缀 124；删去该声明的前缀 0。超时结果均不计定理。
- Full 保持陈述，封装具体 HC 推导，显式写模块孩子参数；最终以三次 hcDown 构造 hA-all 后第四版编译 0，最终冷编 0。无 251、154。

完整读取：原简报、AGENTS.md、EBOHandbook.md §4。导航读取过 README 开头，工具输出有截断，没有把未显示内容当作已读。已读取本轮所用的定义、签名、证明子句：YiDCExit、YiMHLean、YiMHRel、YiCFMono、EboLeanDef；EboLeanBase 的 NF/GB/序工具，EboLeanTree 的 HC 构造，EboLeanClosure 的基本列封闭；YiNFOCase 的 D≼B/B≼D，YiKSRead 的 fs-sup，YiANFam 的记号方程，YiANEnd 的 natB/nat</flatN，YiKVRel 的基础关系与出口，YiRBFam、YiRLCrit、YiCLFam、YiCLLow、YiCLPhi、YiCLCrit、YiRBCrit 的本轮相关签名与子句。没有重读这些大文件全文。

只凭简报、未独立重读：IdeaLedger V157(ii) 的历史定位、前序批次与主审冷编历史；它们只作任务来源，不作新证明的假设。没有外部调研或独立 Fable 审核，不声称有该审核。没有把归约耗时、有限测试、纸面判断当成否定定理。

#### 6. 全部源码、临时目录与日志

仓库交付源码：

- `<仓库>/probes/OCF/Lean/YiNXNote.lagda.md`；SHA-256 `fe5378fa2148b4e1190e46f6f023fd40fdfdd0e90d2f4325adb7acd642e8fa45`
- `<仓库>/probes/OCF/Lean/YiNXExit.lagda.md`；SHA-256 `62baed415f2c15ce3bed130afc69d597272886c4dab84e8bffcb339fc469fca8`
- `<仓库>/probes/OCF/Lean/YiNXLow.lagda.md`；SHA-256 `7e5d2cd6ba7457da0ca93b1bb41b931dea5a190b456fb61f2d00eba2c71104e4`
- `<仓库>/probes/OCF/Lean/YiNXFull.lagda.md`；SHA-256 `dd2e0924cc3f5914b4b54114142c001f3669d6687a16b04da1049d6895267145`

临时目录：`<实验目录>`。全部临时源码与生成脚本：

- `<实验目录>/YiNXCheck.agda`
- `<实验目录>/YiNXFamily.agda`
- `<实验目录>/YiNXHCCheck.agda`
- `<实验目录>/YiNXProbeBase.agda`
- `<实验目录>/YiNXProbeHC.agda`
- `<实验目录>/YiNXStepCheck.agda`
- `<实验目录>/YiNX-report-build.py`（只生成外部回报与审计，不进数学文件）

库配置、审计与草稿：

- `<实验目录>/libraries`
- `<实验目录>/YiNX-audit.json`
- `<实验目录>/YiNX-report-before-full.md`

全部编译日志与结果（Agda 退出码直接取出，不经管道）：

- `<实验目录>/YiNXCheck-pass.log`：退出 0
- `<实验目录>/YiNXCheck-wanted.log`：退出 0
- `<实验目录>/YiNXCheck.log`：退出 42
- `<实验目录>/YiNXExit-build.log`：退出 42
- `<实验目录>/YiNXExit-build2.log`：退出 0
- `<实验目录>/YiNXExit-cold.log`：退出 0
- `<实验目录>/YiNXExit-final-cold.log`：退出 0
- `<实验目录>/YiNXFamily-reuse.log`：退出 0
- `<实验目录>/YiNXFamily.log`：退出 0
- `<实验目录>/YiNXFull-build.log`：退出 42
- `<实验目录>/YiNXFull-build2.log`：退出 130
- `<实验目录>/YiNXFull-build3.log`：退出 130
- `<实验目录>/YiNXFull-build4.log`：退出 0
- `<实验目录>/YiNXFull-final-cold.log`：退出 0
- `<实验目录>/YiNXFull-trace.log`：退出 124
- `<实验目录>/YiNXHCCheck.log`：退出 0
- `<实验目录>/YiNXLow-build.log`：退出 42
- `<实验目录>/YiNXLow-build2.log`：退出 0
- `<实验目录>/YiNXLow-cold.log`：退出 0
- `<实验目录>/YiNXLow-final-cold.log`：退出 0
- `<实验目录>/YiNXNote-build.log`：退出 0
- `<实验目录>/YiNXNote-cold.log`：退出 0
- `<实验目录>/YiNXNote-final-cold.log`：退出 0
- `<实验目录>/YiNXProbeBase.log`：退出 0
- `<实验目录>/YiNXProbeHC.log`：退出 124
- `<实验目录>/YiNXStepCheck.log`：退出 42
- `<实验目录>/YiNXStepCheck2.log`：退出 0

退出码文件：

- `<实验目录>/YiNXExit-cold.exit`
- `<实验目录>/YiNXExit-final-cold.exit`
- `<实验目录>/YiNXFull-final-cold.exit`
- `<实验目录>/YiNXLow-cold.exit`
- `<实验目录>/YiNXLow-final-cold.exit`
- `<实验目录>/YiNXNote-cold.exit`
- `<实验目录>/YiNXNote-final-cold.exit`

所有现存临时接口保留在本临时目录；最终四份 YiNX 接口位于仓库 probes/_build/2.8.0.2/agda/OCF/Lean。没有删除其他模块接口。

原简报：`<临时目录>`。

最终完整回报：`<回报原文>`。本回报取代临时目录中的早期草稿；留待主审独立冷编复核，不写回导航、LOG 或台账。

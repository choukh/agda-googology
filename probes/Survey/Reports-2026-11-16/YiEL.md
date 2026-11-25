# 数学：第 0 层输出带精确标签（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-16 13:31 至 13:52 |
| 工具调用 / agda 编译 (粗数) | 36 / 9 |
| token (usage 字段，按消息去重) | 输出 104184；新写入缓存的输入 242132；读缓存的输入 4815423；其余输入 64 |
| 写过的仓库文件 | `YiELOmega.lagda.md`, `YiELZero.lagda.md` |
| 文件前缀 | `YiEL` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0；limAt（一般的 LimAt）无前提；no-all（带下界证据的 d 不都有精确标签）；分支前提换精确读回 Ex⁰ 后，Ω 形状层号（下标层为第 0 层）有精确标签，uniqᵒ、topᵉ、lbl-layer 成立；部分和链点的精确读回未走通 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b71/YiEL.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiEL 回报：折叠在第 0 层的输出带精确标签（第七十一批）

档位：【定理】= 本路编译过（冷编退出 0）；【判断】= 纸面分析，未编译。没有有限测试档的结果。

#### 1. 判决

**对纲领与目标**：纲领四条未触犯；没有改树、折叠、合法性的定义，也没有发现要改的依据。四个文件都在验收一侧（读记号），不算 "树自足" 的进展。得到的是三件与站无关的事：

- 记号一侧的 `LimAt` 对一切 ω-共尾的项成立，以后不必作字段逐个填。
- 分支前提必须从下界关系换成精确读回（出路 (a)）：有带下界证据而没有任何精确标签的第 0 层树。
- 换了之后，Ω 形状层号（下标层为第 0 层）有精确标签，唯一性与 Leaf 成立，最小实例的颈结点层号实填通过。

**各步到哪一步**

- 第 0 步：完成。一般陈述取 `∀ u → cof u ≡ cω → LimAt u`，不要求 u 是标准形；ω·2、ε₀ 上实例化通过。(a)、(b) 的判断见下。
- 第 1 步：完成，无前提（`limAt`）。证明是新写的，只用了 `EboLeanView` 的视图与 `EboLeanBase` 的 `InG`、`noG-le`、`G-mono`，没有搬证明。
- 第 2 步：选 (a)。交了精确读回 `Ex⁰`、它到下界关系与值的出口、最小实例孩子层号的标签（对一切带精确读回的 d）、关系族 `Rᵉ`。(b) 只做了后继行（`next⁺`）一种链点。
- 第 3 步：交了 Ω 形状（下标层为第 0 层）的一条。`uniqᵒ` 逐字成立；`belowᵒ` 多一个前提（槽位在读回域 `PosOk` 内）；Leaf 在 `Rᵉ` 上成立（`topᵉ`），在 `Rˣ` 上未走通。下标层高于第 0 层的 Ω 形状仍取 `⊥`，没有做。
- 第 4 步：见第 4 节。

**(a) 与 (b) 的精确陈述与判断**

- (a)：槽位层为第 0 层时，分支前提由 `H.M⁰ η d` 换成 `Ex⁰ η d = Lbl (↑ zero d) η`；第 0 层的关系本身仍是 `H.M⁰`。可行，已编译（`Rᵉ`、`topᵉ`、`lbl-layer`）。
- (b)：折叠在第 0 层的每个输出 d（`next⁺`、`limc⁺` 的部分和）都有 η 使 `Ex⁰ η d`。
- 【判断】(b) 单独不够：被保留的 Ω 结点（`YiBVSmall.small-keep`）的孩子对一切带证据的 d 量化，不只对链点；`no-all` 说明下界证据给不出标签。
- 【判断】(a) 之后仍要 (b)：走链一行把折叠输出回灌作 d，这时要它带 `Ex⁰`。`sem→M⁰` 那种 "由值的下界反射出关系" 的接法对 `Ex⁰` 不可用（`no-lbl-slow` 的直接推论：`slow` 对 η = 0 有值的下界而无标签）。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 一般的 `LimAt` 是否成立 | `YiELLim.limAt`、`lim-gen` | 【定理】成立，无前提 |
| 任意带 `M⁰` 证据的 d 是否有精确标签 | `YiELZero.no-lbl-slow`、`no-all` | 【定理】没有 |
| 精确读回能否接到出口 | `YiELZero.ex→M⁰`、`ex-lower` | 【定理】能，经 `H.exitᴴ` |
| 最小实例的孩子层号在精确读回的 d 上有无标签 | `YiELZero.child-lbl` | 【定理】有，且低于 Ω₁ |
| Ω 形状层号能否有精确标签并保住唯一性、Leaf | `YiELOmega.Lblᵒ`、`uniqᵒ`、`topᵉ`、`lbl-layer`、`top-layer` | 【定理】下标层为第 0 层时能；`belowᵒ` 限在读回域 |
| 链点是否都带精确读回 | `YiELChain.ex-next`（只有后继行） | 部分【定理】；部分和与一般链点开放，【判断】是数学问题 |
| 一般 ν 上的 `CofΩ` | `YiELChain.cofΩ-real` | 条件【定理】，前提 `Real` 没有居民 |
| `LowKeep` 在 `Rᵉ` 上 | 无 | 没有陈述，没有做 |

#### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。

| 文件 | 代码行（非空） | 冷编退出码 |
|---|---|---|
| `YiELLim.lagda.md` | 138 | 0 |
| `YiELZero.lagda.md` | 165 | 0 |
| `YiELOmega.lagda.md` | 149 | 0 |
| `YiELChain.lagda.md` | 62 | 0 |

- 冷编：先删这四个模块自己的 `.agdai`，再按依赖次序各编一次（8G）；每份日志只有自己模块的一行 `Checking`。
- 禁用构造与本机路径检索为 0。
- 四个文件都读记号，没有标 "不读记号"，未跑 `importclosure.py`。
- 日志在 `<实验目录>/work/YiEL/`（`*.log`、`*.cold.log`）；第 0 步的临时文件是同目录的 `YiELLim0.agda`。

#### 3. 定理表（陈述逐字）

**YiELLim**（记号一侧）

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `compA` | `∀ {b ν} (w : VΩ b ν) {d Z} → NF d → d <ᵀ b → GB ν d Z → d <ᵀ fΩ w (ψ ν Z ∷ [])` | 分量引理：标准形 d 低于 b，且 d 里经不低于 ν 的下标可达的参数都低于 Z，则 d 低于 b[ψ_ν(Z)] | 【定理】 |
| `Chain.bndT` | `∀ d → NF d → GB ν d b → Σ ℕ λ m → GB ν d (V m)`（`V m = fΩ w (γ w m)`） | 那些参数都低于 b 时，有一个 m 使它们都低于 b[γ_m] | 【定理】 |
| `Chain.cofin` | `∀ {q} → NF q → q <ᵀ b → GB ν q q → Σ ℕ λ m → q <ᵀ V m` | 规则 6 的 γ 链在标准形参数里共尾 | 【定理】 |
| `lim-gen` | `∀ u → cof u ≡ cω → LimAt⁺ u`（`LimAt⁺ u = ∀ {u′} → NF u′ → u′ <ᵀ u → (∀ n → fsn u n ≤ᵀ u′) → ⊥`） | 带 "不高于" 的加强式 | 【定理】 |
| `limAt` | `∀ u → cof u ≡ cω → LimAt u` | 一般的 `LimAt`，u 不必是标准形 | 【定理】 |
| `cofinΩ` | `∀ {a κ} (v : VΩ a κ) {c} → NF c → c <ᵀ a → Σ T λ η → NF η × (η <ᵀ Ωs κ) × (c <ᵀ fΩ v η)` | Ω-共尾一侧：给出见证 η | 【定理】 |
| `t-ω2`、`t-ε0` | `LimAt ω2`；`LimAt ε0` | ω·2、ε₀ 上的实例 | 【定理】 |

**YiELZero**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `Ex⁰` | `Ex⁰ η d = Lbl (↑ zero d) η` | 第 0 层的精确读回 | 定义 |
| `lbl-lim` | `∀ {g ν} → E.cof ν ≡ E.cω → NF ν → (∀ n → Σ E.T λ μ → Lbl (g n) μ × (E.fsn ν n ≤ᵀ μ) × (μ <ᵀ ν)) → Lbl (nd sL g) ν` | ℕ 极限一条不用再填 `LimAt` | 【定理】 |
| `lbl-nf`、`lbl<Ω` | `∀ a {ν} → Lbl a ν → NF ν`；`∀ a {ν} → Lbl a ν → ν <ᵀ Ω₁` | 旧标签是标准形且低于 Ω₁ | 【定理】 |
| `ex→M⁰` | `∀ d {η} → Ex⁰ η d → H.M⁰ η d` | 精确读回推出下界关系 | 【定理】 |
| `ex-lower` | `∀ d {η} → Ex⁰ η d → (h : E.HC η) → Rt h ≼ K.readRW d` | 值的出口 | 【定理】 |
| `two⊕` | `∀ d {η} → Ex⁰ η d → Σ E.T λ μ → Lbl (K.two ⊕ ↑ zero d) μ × (η ≤ᵀ μ) × (μ ≤ᵀ E.sucT (E.sucT η))` | 偏移 2 之后仍有标签，夹在 η 与 η+2 之间 | 【定理】 |
| `child-lbl` | `∀ d {η} → Ex⁰ η d → Σ E.T λ μ → Lbl (S.child d) μ × (η ≤ᵀ μ) × (μ <ᵀ Ω₁)` | 最小实例的孩子层号的精确标签 | 【定理】 |
| `slow-low`、`no-lbl-slow` | `H.M⁰ [] slow`；`∀ ν → Ex⁰ ν slow → ⊥` | `slow`（0, ω, ω+1, … 的极限）带下界证据而没有标签 | 【定理】 |
| `no-all` | `(∀ d η → H.M⁰ η d → Σ E.T λ μ → Ex⁰ μ d) → ⊥` | "带下界证据的 d 都有标签" 不成立 | 【定理】 |

**YiELOmega**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `Lblᵒ` | 零、后继同 `Lbl`；`Lblᵒ (nd sL g) ν = (E.cof ν ≡ E.cω) × NF ν × (∀ n → Σ E.T λ μ → Lblᵒ (g n) μ × (E.fsn ν n ≤ᵀ μ) × (μ <ᵀ ν))`；`Lblᵒ (nd (sΩ zero) h) ν = (E.cof ν ≡ E.cΩ []) × NF ν × CofΩ h ν × (∀ d η → Ex⁰ η d → Σ E.T λ μ → Lblᵒ (h d) μ × (E.fsT ν η ≤ᵀ μ) × (μ <ᵀ ν))`；`Lblᵒ (nd (sΩ (nd s k)) h) ν = ⊥` | Ω 形状一条：对带精确读回的孩子一致 | 定义 |
| `CofΩ` | `CofΩ h ν = ∀ {u′} → NF u′ → E.cof u′ ≡ E.cΩ [] → u′ <ᵀ ν → (∀ d η → Ex⁰ η d → E.fsT ν η <ᵀ u′) → ⊥` | `LimAt` 在 Ω-共尾一侧的对应物，只对共尾度 Ω₁ 的 u′ | 定义 |
| `emb` | `∀ a {ν} → Lbl a ν → Lblᵒ a ν` | 旧标签是新标签 | 【定理】 |
| `uniqᵒ` | `∀ a {ν ν′} → Lblᵒ a ν → Lblᵒ a ν′ → ν ≡ ν′` | 唯一 | 【定理】 |
| `belowᵒ` | `∀ a (q : Pos a) → PosOk a q → ∀ {κ ν} → Lblᵒ (at a q) κ → Lblᵒ a ν → κ <ᵀ ν` | 读回域内的槽位标签严格更低 | 【定理】 |
| `allok` | `∀ a {ν} → Lbl a ν → (p : Pos a) → PosOk a p` | 没有 Ω 形状的层号上 `PosOk` 恒成立 | 【定理】 |
| `Rᵉ` | 与 `YiGLExact.Rˣ` 同形；`Low⁼ᵉ zero (inj₁ _) = Ex⁰`；槽位标签用 `Lblᵒ`；`zero-sameᵉ : Rᵉ zero ≡ H.M⁰` | 分支前提取精确读回的关系族，第 0 层不变 | 定义 |
| `topᵉ` | `∀ a {ν} → Lblᵒ a ν → Rᵉ a (E.Ωt ν) (proj₁ (O.Ωt a))` | `Rᵉ` 上的 Leaf，含 Ω 形状 | 【定理】 |
| `lbl-layer` | `Lblᵒ S.layer Ω₁` | 颈结点层号的标签是 Ω₁，无前提 | 【定理】 |
| `top-layer` | `Rᵉ S.layer (E.Ωt Ω₁) (proj₁ (O.Ωt S.layer))` | 它的 Ω 树读作 Ω_{Ω₁} | 【定理】 |
| `below-layer` | `∀ d {η} → Ex⁰ η d → (t : Pos⁼ (S.child d)) → PosOk⁼ (S.child d) t → ∀ {κ} → Lblᵒ (proj₁ (sl⁼ (S.child d) t)) κ → κ <ᵀ Ω₁` | 实例上的槽位界 | 【定理】 |

**YiELChain**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `ex-add` | `∀ {p} (b y : Tr zero) {s} → NFP p → Ex⁰ (p ∷ []) b → Ex⁰ s y → HdLe p s → Ex⁰ (p ∷ s) (b + y)` | 首项不被吸收时，精确读回对树的加法封闭 | 【定理】 |
| `ex-next` | `∀ {t p} (b : O.Tr⁺ zero) → NFP p → NF t → (e : E.cof t ≡ E.cω) → (∀ n → E.fsn t n ≡ replicate n p) → Ex⁰ (p ∷ []) (proj₁ b) → Ex⁰ t (proj₁ (O.next⁺ b))` | `next⁺` 的输出带精确读回 | 【定理】 |
| `ex-ω′` | `Ex⁰ ωᵀ (proj₁ (O.next⁺ (O.Ωt zero)))` | 第一个链点读作 ω | 【定理】 |
| `Real`、`cofΩ-real` | `Real = ∀ {η} → NF η → η <ᵀ Ω₁ → Σ (Tr zero) λ d → Σ E.T λ η′ → Ex⁰ η′ d × (η ≤ᵀ η′)`；`Real → ∀ {ν} (h : Tr zero → L) → E.cof ν ≡ E.cΩ [] → CofΩ h ν` | 低于 Ω₁ 的标准形都被带精确读回的树盖住时，`CofΩ` 一般成立 | 条件【定理】；`Real` 没有居民 |

#### 4. 第一个障碍

**精确到引理**：部分和的链点带精确读回，即 `ex-add` 去掉 `HdLe p s` 的情形（后项的首项高于前项，记号一侧发生吸收），由此才有 `limc⁺` 输出的 `Ex⁰`。

- 这是**数学上**挡住的，没有编译否定，只写 "未走通"。
- 【判断】要在记号一侧定义带截断的加法 `α ⊞ β`，并证它对 β 单调、与 `fsn` 交换；估计是百行量级的记号侧引理，不涉及树的定义。
- 同一条引理也是 `Real` 的缺口：由 `HC` 推导造树时，ℕ 极限一条的相邻步进要用部分和。【判断】

**它后面还有两件**

- 【判断，数学】一般链点：走链一行的输出要 `Ex⁰`，等于把 LowKeep 在目标第 0 层的结论从 `H.M⁰` 加强成精确读回。Ω 结点行的输出是对角 ℕ 极限，它的精确标签要用到本路的 `Chain.cofin` 的树侧对应。本路没有陈述这条。
- 【判断，工程为主】`YiGT` 一族与 `YiGLNode.node-rowˣ` 写死在 `GR.R` 或 `Rˣ` 上，要移到 `Rᵉ`。`Rˣ` 与 `Rᵉ` 之间本路没有给出映射：高于第 0 层的槽位上分支前提是关系族自身，位置是反变的，两个方向都卡在这里。

**对 `Lblᵒ` 的两点保留**

- `CofΩ` 仍是字段。在 Ω₁ 上空成立（低于 Ω₁ 的标准形可数）；对更大的 ν（偏移含 Ω 结点，如 Ω₁·2）要逐个填，或等 `Real`。偏移含 `sΩ zero` 结点的层号的标签实例没有做。
- `belowᵒ` 多了 `PosOk` 前提。把槽位界写成标签的字段过不了结构递归（要在非子项上引用 `Lblᵒ`）；不带读回的孩子里的槽位没有可用的标签。这符合 "量化域先取读回域"，但将来 Ω 形状层号上的框架要按 `PosOk` 限定槽位。【判断】

#### 5. 偏离与事故；没有读、只凭转述的东西

**偏离**

- 第 3 步要求 `uniq`、`below`、`topˣ` "仍成立"。实际交的是 `uniqᵒ` 逐字、`belowᵒ` 加 `PosOk` 前提、Leaf 换到 `Rᵉ` 上。`Rˣ` 上 Ω 形状的 Leaf 未走通，没有编译否定。
- 出口用的是 `H.exitᴴ`，不是简报写的 `K.lower⁰`：`Rˣ zero` 是 `YiHCRel.M⁰`，`K.lower⁰` 对的是 `YiKVRel.M⁰`，是两个关系。`YiKCSem.sem→M⁰` 只看了签名，没有核它用的是哪一个 `M⁰`，没有接线。
- `Lblᵒ` 的 ℕ 极限一条去掉了 `LimAt` 字段，与 `YiGLFrame.Lbl` 不再逐字同形；用 `emb` 连接。
- 第 2 步 "孩子层号的精确标签" 给的是存在加上下界（η 与 η+2 之间），没有给出闭式。
- `no-lbl-slow` 依赖 `Lbl` 的 ℕ 极限一条是逐项的（`fsn ν n ≤ μ_n`）。若改成共尾式（存在 m），`slow` 会有标签 ω·2。所以它否定的是现行 `Lbl` 下的全称，不是 "任何精确标签的定义"。【判断，未编译】

**事故**：无 251、124、154。三次 42 都是类型错误，改后通过：不开 K 时不能消去 `x = x`，改成带等式参数的引理；另有一处隐式参数要写出。

**没有读证明、只读签名或文首的**

- `YiKCSem`、`YiQLRead`、`YiBVDomain`（只读 `Goal`）、`YiGLNode`、`YiGLDom`（只检索 `dN`）、`YiGT` 一族、`YiC0*`、`YiDN*`。
- `EboLeanTrian`、`EboLeanBach`、`EboLeanClosure` 只用签名。
- Bedrock 性能手册没有打开（没有遇到性能问题）；`EBOHandbook` 4.2 节与 4.6 节前半读了。

**其余标注**

- "(b) 单独不够"、"(a) 之后仍要 (b)"、"截断加法是百行量级"、"移 `YiGT` 是工程量" 都是判断。
- "出路只有 (a)、(b) 两条" 是简报给的穷尽，本路没有挑战，仍是判断。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：数学，折叠在第 0 层的输出带精确标签（前缀 YiEL，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。作者 2026-11-16 定第七十一批，本路选项原文 "数学：第 0 层输出带精确标签 (Recommended)"，执行方 Fable 5.2。同批另三路（工程 YiXP、摆脱侧 YiWB、同步对象上的 Tail YiTL）与你互不导入。

#### 第七十批的结果（主审 8G 冷编复核过，读陈述）
- **整体引理 YiGL**（`probes/OCF/Lean/YiGL*`）：读回域 `YiGLDom.Dom`（`dz`、`dC`、`dN`、`dc`）上 Leaf 对一切层号形状成立（`dom-top`），接口 `YiAbsGIface` 的 Leaf、Lift 无前提成立（`leafᴰ`、`liftᴰ`），全域 Leaf 的反例在域外（`not-in`）。LowKeep 未证：现有条件保持引理 `YiGTFold.pres : ∀ ℓ → Kit ℓ → PresAt ℓ` 要的框架 `NodeFrame`，在槽位标签取下界读法 `Rd` 时，对一切后继形状层号无居民（`YiGLFrame.no-frame-S`、`no-tree-child`）；换成精确标签 `YiGLFrame.Lbl`（`Lbl zero ν = ν ≡ []`；后继逐字；ℕ 极限要 `cof ν ≡ cω`、`NF ν`、`LimAt ν`、各孩子标签与基本列的比较；Ω 形状取 `⊥`）后有居民（`frameˣ-S`、`YiGLNode.frameᴸ-S`）；`uniq`、`below`、`lbl-rd`；精确标签的关系族 `YiGLExact.Rˣ`（第 0 层与 `GR.R` 相同），`topˣ`（含 ℕ 极限层号；`topˣ-ω` 在 `no-omega-seed` 的对象上成立），`LowKeepAtˣ`、`LowKeepˣ`（陈述，无居民），`prefixˣ-B₀`、`betaˣ`；`YiGLNode.node-rowˣ`（结点一行的条件定理）。回报 `probes/Survey/Reports-2026-11-16/YiGL.md`。
- **对位调整 YiSY**：`ebo-from-stations′ : (∀ n → Kᴱ′ (suc n)) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；第 3 站下界归约为 `YiSYSmall.k2′-from-tail : Gᴱ.Tail → Kᴱ′ 2`，`Tail` 未证；`two-shape`、`kl-index`。
- **摆脱侧 YiLX**：`YiLXClimb.climb`（字面路径上源 Ω 树折叠按 `YiVRRel.Le` 不高于目标的，一般形式，不读记号），前缀 0、1；前缀 2 起底前提被否定（`YiLXOne.no-base-two-at0` 等：源底里分支取值在第 0 层的 Ω 结点，`Le` 放不进极限链之下）。
- **配对否定 YiVN**：`YiVNIdx.Gen.no-value-index-mono≈`：以下标的树侧值序作前提的下标单调不成立（谓词太宽）。所以前提只能是字面路径、关系或读回域。
- **作者定**：主线停逐项，改攻整体引理；参照只用记号关系 M（`OCF.Align.Level` 的下标类型只有 `zero`、`suc`、`lim`，接不到终点）。

#### 本路的问题（YiGL 回报第 4 节的第 2、3 条，判断）
1. `Rˣ` 的分支前提 `Lowˣ` 在第 0 层仍是下界关系 `H.M⁰`。孩子来自第 0 层的 Ω 结点（颈结点）要对一切带 `M⁰ η d` 证据的 d 给出孩子层号 `A ⊕ ↑ zero d` 的精确标签；任意的 d 没有这样的标签。两条出路：(a) 把第 0 层的分支前提也换成 "精确读回"；(b) 证明**链点**（折叠在第 0 层的输出，`next⁺`、`limc⁺` 的部分和）经 `↑` 得到的层号都有 `Lbl`。(b) 的 ℕ 极限一条要参照项的 `LimAt`（`YiGLFrame.LimAt u = ∀ {u′} → NF u′ → u′ <ᵀ u → (∀ n → E.fsn u n <ᵀ u′) → ⊥`）；仓库里只对 ω 证了（`YiGLOmega.lim-ω`），YiGL 检索 `EboLeanBase`、`EboLean3Base`、`EboLeanView`、`EboLeanClosure`、`EboLeanBach` 的签名未找到一般的。
2. `Lbl` 对 Ω 形状层号取 `⊥`；第 1 项后半与第 3 站要的偏移含 `sΩ zero` 结点（`YiDNNoOmega.no-offset-slot`），要给它加一条，形状未定。

#### 要做的（按序）
0. **最小检查**：写出 "一般的 `LimAt`" 的陈述（对标准形 u，`cof u ≡ cω` ⇒ `LimAt u`，或你认为对的形式），在 ω、ω·2、ε₀ 一类的项上先编译；写出 (a)、(b) 两条出路的精确陈述，判断哪条可行。不成立就停下回报。
1. **证一般的 `LimAt`**（记号一侧；可借 `EboLeanView` 的共尾视图、`EboLeanClosure` 的封闭引理，搬来的写明来源）。
2. **选 (a) 或 (b) 证明**：给出最小实例 `YiBVSmall` 上实际用到的孩子层号的精确标签，或第 0 层分支前提改为精确读回后的关系族定义，连同它与出口（`YiKCSem.sem→M⁰`、`K.lower⁰`）的接线。
3. **Ω 形状层号的 `Lbl`**：提出并编译一条，使 `uniq`、`below`、`topˣ` 仍成立（或给出编译的否定，说明为什么 Ω 形状不能有精确标签，以及要换成什么）。
4. 交第一个挡住的引理，说明是数学上还是工程上挡住；所有 "穷尽" 的说法标判断。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 8G（同批另有三路，主审也在编译）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
- **停下的条件**：退出 251 时不原样重跑，先按 C-9、C-10、S-1 改形状并定位（附 profile 或二分数据）；改过形状后同一上限仍撞墙才停。同一处两次重新设计仍过不了检查器也停。若某一步要改树、折叠或合法性的定义，停下回报。没有编译的否定时只写 "未走通"。
- **过程**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。动手证一般形式之前先用临时文件检查前提可满足；已有引理先检索（`grep`）再写，不重证，搬来的证明在文首写明来源。查签名用检索，不整篇读大文件。
- 不在你的临时目录与你前缀的新文件之外写、删、移任何东西；不 `pkill`，不写 `/tmp`，不装包，不提交，不改 `probes/README.md`、`probes/LOG.md`、台账与留档。
- **两条已更正的事实**（不要再照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧非标准形项的项序单调，**不是**树侧折叠的跨层单调（树侧跨层单调目前没有编译的否定）；`YiKWObjects.kept` 是新封装的对象，与 `YiC1Slot` 不透明块里的 `kept` 不是同一个。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0；文首标 "不读记号" 的文件用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包。

#### 回报（最后一条消息就是回报，主审会原样留档）
1. 判决：先说对纲领与目标意味着什么；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理；是数学上挡住还是工程上挡住。
5. 偏离与事故；没有读、只凭转述引用的东西。
不用 "只差"、"自然" 一类形容；判断与定理分开写。


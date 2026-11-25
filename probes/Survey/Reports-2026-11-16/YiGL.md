# 整体引理：读回域上的 Leaf 加 LowKeep（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-16 12:34 至 13:03 |
| 工具调用 / agda 编译 (粗数) | 46 / 6 |
| token (usage 字段，按消息去重) | 输出 149464；新写入缓存的输入 585843；读缓存的输入 8649686；其余输入 72 |
| 写过的仓库文件 | `YiGLDom.lagda.md`, `YiGLExact.lagda.md`, `YiGLFrame.lagda.md`, `YiGLNode.lagda.md`, `YiGLOmega.lagda.md` |
| 文件前缀 | `YiGL` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 5 件全部退出 0，禁用构造 0；Leaf/Lift 在读回域 Dom 上无前提成立且 noLeaf 反例在域外；下界标签下现有 LowKeep 框架无居民（no-frame-S），精确标签 Lbl 下有居民；LowKeepˣ 只有陈述 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b70/YiGL.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiGL 回报: 整体引理, 读回域上的 Leaf 加 LowKeep (接口与最小实例)

档位: 【定理】= 本路编译过 (退出 0) 或仓库里已编译且我读过陈述的; 【判断】= 纸面分析, 未编译。没有有限测试档的结果。

#### 1. 判决

**对纲领与目标**: 纲领四条未触犯, 没有改树、折叠、合法性的任何定义, 没有发现要改它们的依据。对目标 "让树自足": 本路的结果都在验收一侧 (读记号), 不算树自足的进展; 但它把九批里反复出现的缺口定位到一个与站无关的事实上: **折叠的保留判定 (`kp`) 按层号的字面路径比较, 记号一侧按余尾下标的项序比较; 槽位标签用下界读法时两边不可能一致, 必须换成序上精确的标签**。这是一条对 (层号, 目标, 下标) 一般的陈述, 不按站定制。

**各步到哪一步**:
- 第 0 步 (接口与量化域): 完成, 5 个文件全部冷编退出 0。Leaf 一半在读回域上成立 (对一切层号形状); LowKeep 一半只有陈述, 没有居民。
- 第 1 步 (没有 Ω 结点的层号, 参照为 M, 得到 `Need η d` 对一切 d): **未走通**。没有得到 `Need`、`MinimalGoal`。
- 第 2 步 (含 `sΩ zero` 结点的层号): **未走通**, 未动手 (依赖第 1 步的同一条引理)。
- 第 3 步: 没有新的条件链; 见第 4 节的障碍说明。
- 第 4 步 (YiSY 的影响): 本路陈述对层号是变量, 对位调整不改变陈述。A 路建议的同步对象 `tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))` 在读回域 `Dom` 内 (由 `dC` 一条给出), 但不在精确标签 `Lbl` 的域内 (`Lbl` 对 Ω 形状层号取空), 所以对位调整不省掉下面的障碍 (判断)。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 读回域上的 Leaf 是否成立, 反例是否在域外 | `YiGLDom.dom-top`, `not-in` | 【定理】成立; 反例在域外 |
| Leaf、Lift 与 `YiAbsGIface` 的关系 | `YiGLDom.gradedᴰ`, `leafᴰ`, `liftᴰ` | 【定理】是把 `Graded.Rd` 换成 `Dom` 的实例化, 不是新律 |
| 现有的条件 LowKeep (`YiGTFold.pres`, `YiGTLow.low-at′`) 的框架前提在链点孩子上有无居民 | `YiGLFrame.no-frame-S`, `no-tree-child` | 【定理】无居民 (对一切后继形状层号, 一切目标下标 ν) |
| 换成精确标签后同一处框架有无居民 | `YiGLFrame.frameˣ-S`, `YiGLNode.frameᴸ-S` | 【定理】有 |
| 精确标签在 ℕ 极限层号上可满足吗 ("Ω 树是部分和") | `YiGLOmega.lbl-ω`, `YiGLExact.topˣ-ω` | 【定理】在 `no-omega-seed` 的对象上可满足 |
| 精确标签关系族 `Rˣ` 上的 LowKeep | `YiGLExact.LowKeepˣ` | 只有陈述; 结点一行是条件定理 (`node-rowˣ`), 其余未做 |
| 链点 (第 0 层的折叠输出) 是否都有精确标签 | 无 | 【判断】开放, 是数学问题 |

#### 2. 文件表 (都在 `<仓库>/probes/OCF/Lean/`)

| 文件 | 代码行 (非空) | 冷编退出码 |
|---|---|---|
| `YiGLDom.lagda.md` | 78 | 0 |
| `YiGLFrame.lagda.md` | 111 | 0 |
| `YiGLOmega.lagda.md` | 84 | 0 |
| `YiGLExact.lagda.md` | 73 | 0 |
| `YiGLNode.lagda.md` | 78 | 0 |

冷编: 删掉这 5 个模块自己的 `.agdai` 后, 编 `YiGLDom` 与 `YiGLNode` 两次 agda (后者带起 Frame、Exact、Omega)。日志里只有这 5 个模块的 `Checking` 行。禁用构造与本机路径检索为 0。5 个文件都读记号, 没有标 "不读记号", 未跑 importclosure。日志在 `<实验目录>/work/YiGL/` (`*.log`, `*.cold.log`)。

#### 3. 定理表 (陈述逐字)

**YiGLDom** (读回域与 Leaf)

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `Dom` | `data Dom : L → E.T → Set`, 构造子 `dz : ∀ a → Dom a []`; `dC : ∀ F ℓ {t ν y} → Dom (run F zero) t → GR.R ℓ ν y → Dom (run F (↑ ℓ y)) (t ++ ν)`; `dN : ∀ {k κ ν} (h : Tr k → L) → Dom k κ → E.cof ν ≡ E.cΩ κ → (∀ η c → GR.R k η c → Dom (h c) (E.fsT ν η)) → Dom (nd (sΩ k) h) ν`; `dc : ∀ {a ν μ} → ν ≤ᵀ μ → Dom a μ → Dom a ν` | 带证据的 (层号, 读法): 空读法、沿上下文读回一棵带关系证据的树、Ω 形状 (对一切孩子一致)、向下封闭。没有 "经 Ω 形状的指定孩子读" | 定义 |
| `dom-top` | `∀ {a ν} → Dom a ν → Top a ν` (`Top a ν = GR.R a (E.Ωt ν) (proj₁ (O.Ωt a))`) | 域上的 Leaf, 层号、偏移、孩子函数都是变量 | 【定理】 |
| `dom-rd` | `∀ {a ν} → Dom a ν → GR.Rd a ν` | 域里的读法是原读法 | 【定理】 |
| `leafᴰ`, `liftᴰ` | `leafᴰ : Leaf`, `liftᴰ : Lift` (`Laws gradedᴰ domsᵍ`, `gradedᴰ = record gradedᵍ { Rd = Dom }`) | 接口的 Leaf、Lift 在换了 `Rd` 的实例上无前提成立 | 【定理】 |
| `dom-tw`, `dom-keel` | `∀ n → Dom (tw n) (κ n)`; `∀ n → Dom (tw n) (Keel⁻.kt keelᴱ n)` | 塔与龙骨读法在域内 | 【定理】 |
| `dom-fin` | `∀ n → Dom (fn n) (E.natT n)` | 有限层号在域内 | 【定理】 |
| `dom-child`, `dom-neck` | `∀ {η d} → GR.R zero η d → Dom (S.child d) η`; `Dom S.layer (E.Ωs [])` | 最小实例的链点孩子与颈结点层号在域内 | 【定理】 |
| `not-in`, `rd-not-dom` | `Dom N.ℓ (E.natT 1) → ⊥`; `(∀ {a ν} → GR.Rd a ν → Dom a ν) → ⊥` | `noLeaf` 的反例不在域内 | 【定理】 |

**YiGLFrame** (配对: 否定与构造)

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `no-frame-S` | `(h : ⊤ → L) (o : Ok (nd sS h)) (q : Pos (h tt)) (ν : E.T) → NodeFrame (nd sS h) o (h tt) (inc tt self) ν → ⊥` | 槽位标签取下界读法时, 后继形状层号折到孩子的框架对任何目标下标都没有 | 【定理】 |
| `no-frame-child`, `no-tree-child` | `∀ d (o : Ok (S.child d)) ν → NodeFrame (S.child d) o (K.two ⊕ ↑ zero d) (inc tt self) ν → ⊥`; `∀ d → IndexTree (S.child d) → ⊥` | 每个链点孩子上, `YiGTLow.low-at′` 的前提 `IndexTree` 没有居民 | 【定理】 |
| `Lbl` | `Lbl zero ν = ν ≡ []`; `Lbl (nd sS h) ν = (E.cof ν ≡ E.c1) × Lbl (h tt) (E.pred ν)`; `Lbl (nd sL g) ν = (E.cof ν ≡ E.cω) × NF ν × LimAt ν × (∀ n → Σ E.T λ μ → Lbl (g n) μ × (E.fsn ν n ≤ᵀ μ) × (μ <ᵀ ν))`; `Lbl (nd (sΩ k) h) ν = ⊥`; `LimAt u = ∀ {u′} → NF u′ → u′ <ᵀ u → (∀ n → E.fsn u n <ᵀ u′) → ⊥` | 精确标签: 后继逐字, ℕ 极限只要求基本列逐项不高于孩子的标签且孩子的标签严格更低 | 定义 |
| `lbl-rd`, `uniq`, `below` | `∀ a {ν} → Lbl a ν → GR.Rd a ν`; `∀ a {ν ν′} → Lbl a ν → Lbl a ν′ → ν ≡ ν′`; `∀ a (q : Pos a) {κ ν} → Lbl (at a q) κ → Lbl a ν → κ <ᵀ ν` | 是读法; 唯一; 槽位的标签严格低于层号的标签 | 【定理】 |
| `frameˣ-S` | `(h : ⊤ → L) (o : Ok (nd sS h)) {ν : E.T} → Lbl (h tt) ν → NodeFrameˣ (nd sS h) o (h tt) (inc tt self) ν` | `no-frame-S` 同一处, 标签换成精确标签后框架有居民 | 【定理】 |

**YiGLOmega**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `lim-ω`, `nf-ω` | `LimAt ωᵀ`; `NF ωᵀ` | ω 的极限性质与正规性 | 【定理】 |
| `lbl-ω`, `lbl-source` | `Lbl Lω ωᵀ` (`Lω = nd sL Gω`, `Gω n = K.two ⊕ ↑ zero (nat n)`, `Lω-eq : K.two ⊕ ↑ zero W.ω ≡ Lω`); `Lbl (S.child W.ω) (E.sucT ωᵀ)` | `no-omega-seed` 的层号有精确标签 ω (孩子标签 n+2, 基本列的项 n) | 【定理】 |
| `frameˣ-source`, `no-frame-source` | `(o : Ok (S.child W.ω)) → NodeFrameˣ (S.child W.ω) o Lω (inc tt self) ωᵀ`; `(o : Ok (S.child W.ω)) (ν : E.T) → NodeFrame (S.child W.ω) o Lω (inc tt self) ν → ⊥` | ω+1 孩子上配对的两条 | 【定理】 |

**YiGLExact / YiGLNode**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `Rˣ` | 与 `YiGIRel.R` 同形, 槽位余尾换成 `λ p → Lbl (at (nd s h) p)`; `zero-same : Rˣ zero ≡ GR.R zero` | 精确标签的关系族; 第 0 层不变, 出口不变 | 定义 |
| `topˣ` | `∀ a {ν} → Lbl a ν → Rˣ a (E.Ωt ν) (proj₁ (O.Ωt a))` | `Rˣ` 上的 Leaf, 含 ℕ 极限层号 | 【定理】 |
| `topˣ-ω`, `topˣ-source` | `Rˣ Lω (E.Ωt ωᵀ) (proj₁ (O.Ωt Lω))`; `Rˣ (S.child W.ω) (E.Ωt (E.sucT ωᵀ)) (proj₁ (O.Ωt (S.child W.ω)))` | ℕ 极限层号上的 Ω 树读作 Ω_ω (与 `no-omega-seed` 的差别: 这里有向下封闭和 "不高于" 的余量) | 【定理】 |
| `LowKeepAtˣ`, `LowKeepˣ` | `LowKeepAtˣ ℓ = ∀ {j} (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ) (β : O.Tr⁺ j) (ν t : E.T) → Lbl j ν → OK B → Prefixˣ B t → Rˣ j (E.ψ ν t ∷ []) (proj₁ β) → ∀ {a x} → Rˣ ℓ a x → Rˣ j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))`; `LowKeepˣ = ∀ ℓ {λ′} → Lbl ℓ λ′ → LowKeepAtˣ ℓ` | 一般陈述, **没有居民** | 陈述 |
| `prefixˣ-B₀`, `betaˣ` | `∀ ℓ → Prefixˣ (B₀ ℓ) []`; `∀ j {ν} → Lbl j ν → Rˣ j (E.ψ ν [] ∷ []) (proj₁ (O.Ωt j))` | `LowKeepAtˣ` 的底与底值前提可满足 | 【定理】 |
| `node-rowˣ` (模块 `Nodeˣ ℓ j o r B w ν t β`) | `NodeFrameᴸ ℓ o j w ν → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → Lbl (at ℓ p) κ → (∀ η c → Lowˣ ℓ p η c → Rˣ j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c)))) → Chainˣ a p κ g → Rˣ j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))` | 条件定理: 框架、分支保持、链推出结点行 (保留与走链两支) | 【定理】(条件; `Chainˣ` 与分支保持未实填) |
| `frameᴸ-S` | `(h : ⊤ → L) (o : Ok (nd sS h)) {ν : E.T} → Lbl (h tt) ν → NodeFrameᴸ (nd sS h) o (h tt) (inc tt self) ν` | 带 `Low` 搬运的框架在后继形状上无前提有居民 | 【定理】 |

#### 4. 第一个障碍

**精确到引理**: `YiGLExact.LowKeepˣ` 没有居民。它要三样, 前两样没有:

1. **(工程为主)** `YiGT` 一族 (`YiGTGen`、`Up`、`Self`、`Emb`、`Node`、`Fold`、`Index`、`Direct`、`Slot`, 约 800 行) 把关系写死为 `YiGIRel.R` (槽位余尾 = 下界读法 `Rd`)。它的主引理 `YiGTFold.pres : ∀ ℓ → Kit ℓ → PresAt ℓ` 已编译, 但前提里的 `NodeFrame` 对一切下界标签量化, `no-frame-S` 证明在每个后继形状层号上无居民。要把这一族对槽位标签参数化后重做到 `Rˣ` 上; 本路只移了结点一行 (`node-rowˣ`), 嵌入、上折、自身三行没有移。这一步我判断是工程量, 不是数学障碍 (判断: 结点行逐字移过去一次通过)。
2. **(数学)** `Rˣ` 的分支前提 `Lowˣ` 在第 0 层仍是下界关系 `H.M⁰`。孩子来自第 0 层的 Ω 结点 (颈结点) 要对一切带 `M⁰ η d` 证据的 d 给出孩子层号 `A ⊕ ↑ zero d` 的精确标签; 任意的 d (第 0 层的任意树) 没有这样的标签 (判断)。所以要么把第 0 层的分支前提也换成 "精确读回", 要么证明**链点** (折叠在第 0 层的输出) 都带精确读回。后者需要: 折叠输出 (`next⁺`、`limc⁺` 的部分和) 的 `↑`-层号有 `Lbl`, 其中 ℕ 极限一条要参照项 ψ_ν(t ++ a) 的 `LimAt` (正规项的极限性质)。仓库里只对 ω 证了 (`lim-ω`); 一般的 `LimAt` 我没有找到现成引理 (检索过 `EboLeanBase`、`EboLean3Base`、`EboLeanView`、`EboLeanClosure`、`EboLeanBach` 的签名), 这是记号一侧的引理。
3. `Lbl` 现在对 Ω 形状层号取空, 第 2 步 (偏移含 `sΩ zero`) 还要给它加一条, 形状未定。

**为什么第 1 步的直接归纳走不通** (判断, 依据是上面的编译否定加纸面推演): 参照 ψ_ν(t ++ a) 在余尾下标 κ < ν 时保留结点, 否则走 γ 链; 树按槽位层是否严格在目标层里面决定。同一层号可以同时读作 0 和 1 (`YiFPReadback.no-rd-notBelow`, 已有), 于是 "参照保留而树走链" 与 "参照走链而树保留" 两种错位都会出现; 前一种在没有向下封闭的目标关系 (`H.M 1`, 即 `Need` 的目标) 里无法补救。`Need` 的目标关系 `H.M 1` 没有向下封闭 (`mc`), 而 ℕ 极限层号上的 Leaf 必须用向下封闭 (`topˣ` 的 `sL` 一行; `no-omega-seed` 是它的反面), 所以按简报原样得到 `YiQLRead.Need η d` 对一切 d 这一目标, 我判断应当改成在带向下封闭的关系族里陈述, 再在第 0 层经出口证书出去。这一条没有编译否定, 只写 "未走通"。

**对终点 `YiCNKeel.LowAt n` 的含义**: `LowAt n` 是 `LowKeep` 在 ℓ = `tw n`、目标第 0 层、Ω 树、继承底上的实例加出口证书。目标是第 0 层时顶层框架恒成立 (`YiGTIndex.index-zero`, 已有), 挡住的是链步: 折到槽位层时需要 `SlotPres`, 它要槽位层作目标的框架, 即上面第 1、2 条。`YiNLKeel.ebo-from-low` 的条件链不变, 本路没有新增能编的条件链。

#### 5. 偏离与事故; 没有读、只凭转述的东西

**偏离**
- 简报没有列 `YiGT` 一族与 `YiNLRaise`/`YiNLCtx`。读回域上的 Leaf 其实已由 `YiNLRaise.raiseR` 与 `YiNLCanonical.reg-top` 给出; `YiGLDom` 的新内容只是把它们并成一个归纳域、加上孩子函数为变量的 Ω 形状一条 (`dN`), 以及接口实例化。"下界标签下框架无居民" 在 `fn 2` 与 `tw 1` 上已有 (`YiGTIndexNeg.no-frame₂`、`no-index-tree-tw1`); 本路的 `no-frame-S` 是它对一切后继形状层号的一般形式。请主审查重时按此折算。
- 第 0 步要求的 "一般陈述" 没有写成 `YiAbsGIface.LowKeep` 的实例: 接口的 `cl : Lv → T → T` 与 `app` 只看层号, 而目标下标来自标签证据, 写不进去。`LowKeepˣ` 是独立的陈述 (文首已注明)。Leaf、Lift 是实例化。
- 第 0 步没有用临时目录的纯 `.agda` 试验, 直接写仓库文件; 第一个文件的首次编译晚于 30 分钟 (前面在读定义与已有引理)。
- 冷编时 `YiGLNode` 的日志里有另外三个本前缀模块的 `Checking` 行 (作为依赖一并冷编), 没有逐个单独再编。
- 没有 251、124、154; 每个文件首次编译即退出 0。

**没有读证明、只读文首或签名的**: `YiTBFam`、`YiASProofLow` (只读了末尾 25 行)、`YiC0*`、`YiDN*`、`YiGTUp`、`YiGTSelf`、`YiGTEmb`、`YiGTDirect` (只读 `IndexTree` 等定义)、`YiGTSlot`、`YiGTInst`、`YiGTOmega`、`YiGTCheck`、`YiGTCompat`、`YiLKIface`、`YiSUIface` (只读 `PrefixU`)、`YiExSuff`、`YiCNAccept`、`YiMXEnd`、`YiLRLow`/`YiLRNeg` (`no-omega-seed` 的机制只从 `YiOPCountable` 的调用处推断)、`EBOHandbook` 4.2/4.6 节与 Bedrock 性能手册 (没有遇到性能问题, 未查)。`Align.Level` 一侧 (`YiGCRel`、`YiGCFold` 等) 读了代码, 只作对照, 没有导入。
- "任意的 d 没有精确标签"、"`LimAt` 对正规项一般成立"、"`LimAt` 对非正规项在 ω 上不成立"、"把 `YiGT` 移到 `Rˣ` 是工程量" 都是判断, 未编译。
- "同一条引理只有这一种做法 (换精确标签)" 是判断; 另一种做法 (保留下界标签, 靠目标关系的向下封闭从精确实例降下来) 我只推到 "源一侧的结点读低了无法重读" 为止, 没有编译否定。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：整体引理，读回域上的 Leaf 加 LowKeep（接口与最小实例）（前缀 YiGL，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。作者 2026-11-16 定："停逐项，改攻整体引理 (Recommended)"，本路选项原文 "整体引理：接口与最小实例 (Recommended)"，执行方 Fable 5.2；参照系统作者定 "只用记号关系 M (Recommended)"。同批另三路（对位调整 YiSY、配对否定 YiVN、摆脱侧 YiLX）与你互不导入。

#### 为什么改攻法（三路 Fable 审核的共识，主审核对过）
第六十一到六十九批在具体链点上逐项展开，同一个缺口以约二十个名字出现（`FirstRow`、`NextSlot`、`BranchNeed`、`MinimalGoal`、`Step`、`StepMissing`、`Narrow`、`SlotLaw`……），无条件终点值只加 1（`YiOLBoost.strict-ebo`）。它们都是同一条引理的实例：**层号读法里出现 Ω 形状或可数无穷的层号时，Ω 树折到低层，值不掉**；即读回域上的 Leaf 加 LowKeep。这条引理的形状早在抽象接口里，条件定理已编译：
- `YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；接口 `YiAbsGIface`（记录 `Ref`、`Rows`、`Graded`、`Doms`；律 Leaf、Lift、LowKeep）；实例 `YiGIInst`（`Graded`、`Doms`、`keelᴱ`）。
- 龙骨上已实填：`YiNLKeel`（`leaf-keel`、`lift-keel`、`ebo-from-low`，只剩 `LowRest`，即第 3 站起的 `YiCNKeel.LowAt n`）。
- 已有实例：有限层号 `YiTBFam.sΩ-LF`、`YiASProofLow.lowKeepᶠ`、不同步对 `YiASIface.LowKeepAsync` 与有限层号的 `lowKeepAsyncᶠ`；没有 Ω 结点的层号在 `Align.Level` 参照下 `YiGCChosen.all-lower`（精确对应 `YiGCCorr`、沿帧机制 `YiGCFold`、`YiFPFrames`）；最小实例上 `YiQLRead`（`Need`、`zero`、`limit`、`weak`、`Step`、`leaf`、`minimal-from`）、`YiSQNat.nat-all`、`YiSQOmega.omega-all`；颈结点 `YiC0Local.neck`（孩子来自第 0 层的 Ω 结点）、`YiC0Accept.first-row`（经旧块搬 BTBO）。

#### 必须避开的（编译否定，读陈述）
- `YiLLLeafNeg.noLeaf : Leaf → ⊥`：全域 Leaf 不成立（反例层号含 Ω 孩子）；量化域必须收到读回域。
- `YiOPCountable.no-omega-seed`：ℕ 极限层号上标准底的 Ω 树不能按**精确标签**读作 Ω_ω；关系要容得下 "ℕ 极限层号上 Ω 树是部分和"。
- `YiFPReadback.no-rd-notBelow`：下界读回 `Rd` 不是函数性的（同一层号既读作 0 也读作 1），F2 那种要精确对应的论证不能逐字照搬。
- `YiDNNoOmega.no-offset-slot`：读回不低于 ψ₁(Ω_Ω) 的偏移必含 Ω 结点。
- 参照只用 M：`OCF.Align.Level` 的下标类型 `Ordᴵ` 只有 `zero`、`suc`、`lim`，写不出 Ω₂、ψ₁(Ω_Ω) 这样的下标，接不到终点；YiGC 的 Level 结果只作对照，不造 Level 到 M 的桥。

#### 审核 A 路给的方向（判断，供参考，可以不同意并说明）
对层号读法归纳（`Rd`，或把 YiGC 的精确对应推广到含 `sΩ zero` 的形状），归纳里携带**源关系**（折叠前，Leaf），不携带折叠后的结论（`YiQLRead.Step` 从折叠后的 `Need` 推下一个，A 路判断形状不对）；三种目标（低于目标保留、同层以输出作下标对角、高于目标经该层走链）各一条；写进 `YiAbsGIface` 的 `Doms`，量化域取链点读回域。全文见 `probes/Survey/Reports-2026-11-16/AuditA.md` 第 2、3、4 节。

#### 要做的（按序）
0. **接口与量化域**（最小检查）：写出读回域（层号 + 读回证据）与一般陈述（层号、偏移、孩子函数、表、底、目标层都是变量；参照为 M），说明它与 `YiAbsGIface` 的 `Leaf`/`LowKeep` 的关系（是其实例化还是新律，不重复）；在已知实例上实填（有限层号、龙骨），编译。确认 `noLeaf` 的反例不在域内。不成立就停下回报。
1. **没有 Ω 结点的层号，参照为 M**：在 M 下重做可数层号（含 ℕ 极限层号）的情形，得到 `YiQLRead.Need η d` 对一切 d（从而 `YiBVSmall.MinimalGoal`）。
2. **含 `sΩ zero` 结点（孩子来自第 0 层）的层号**：第 2 站与颈结点那一型的一般形式（偏移是读回域里的任意层号），由此给出更深颈结点 `YiDNRequests.SlotValue` 一类。
3. **接到终点**：说明 1、2 给出 `YiCNKeel.LowAt n`（或 `LowRest`）需要的哪些，编译能编的条件链；交第一个挡住的引理（数学上还是工程上）。
4. 若 YiSY 一路的对位调整（第 n+1 站参照对 `twᶻ n`）对你的陈述有影响，只在回报里说明，不导入它的文件。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 8G（另有三路与主审在编）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
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


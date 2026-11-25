# 合流两个关系族（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 15:24 至 15:52 |
| 工具调用 / agda 编译 (粗数) | 62 / 10 |
| token (usage 字段，按消息去重) | 输出 164667；新写入缓存的输入 473384；读缓存的输入 8722550；其余输入 84 |
| 写过的仓库文件 | `YiMGFrame.lagda.md`, `YiMGNeck.lagda.md`, `YiMGRel.lagda.md` |
| 文件前缀 | `YiMG` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0；合流关系族 Rᵐ 上 Leaf（topᵐ）与不含 Ω 形状层号的 LowKeep（lowKeepAtᵐ-noΩ）都成立；颈结点折到第 0 层时走链的精确证据第 0 步为空（no-chain-neck），颈槽位保留进孩子的框架为空（no-frame-neck-child）；较弱的 NeckLabChain 只有陈述 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b72/YiMG.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### 1. 判决

**对纲领与目标的意义。** 新增的三个文件都是验收文件（读记号），没有改树、折叠或合法性。合流做成了：同一个关系族 `Rᵐ` 上，YiEL 的 Leaf 和 YiXP 的 LowKeep 都成立，各自在原来的定义域上（LowKeep 只到不含 Ω 形状的层号）。

往塔第 1 项走时，挡住的地方落在颈结点（Ω 形状层号经下标层的那个槽位）的走链上。走链要把折叠的输出当成分支参数喂回去，所以颈槽位的分支前提要同时满足三件事：
- Leaf 要求前提推出孩子有精确读回；
- 走链要求折叠输出满足这个前提；
- 保留进孩子时，要求孩子里第 0 层槽位的前提推出颈槽位的前提。

精确读回的形式已有编译否定（`no-chain-neck`）。较弱的形式还没有走通：迭代有某个精确读回，且读回不低于 γ 链的对应项。判断：这需要折叠输出的上界，或者改颈结点那一行（第 4 层逼出的定义改动，交作者定）。

**各步进度。**
- 第 0 步完成。`Rᵐ` 的槽位标签取 `Lblᵒ`；分支前提只在颈槽位取 `Ex⁰`，孩子路径上的第 0 层槽位仍取 `M⁰`。不处处取 `Ex⁰` 的理由有编译否定：`Rᵉ` 在不含 Ω 形状的层号 `one` 上，走链第 0 步就没有证据。
- 第 1 步完成：`lowKeepAtᵐ-noΩ`。
- 第 2 步挡住，第一个挡住的引理见第 4 节。
- 第 3 步写成判断，见问题表最后两行。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 不含 Ω 形状的层号上，`Rᵐ` 与 `Rˣ` 互相给出 | YiMGRel `toˣ`/`ofˣ` | 编译定理 |
| Leaf 对一切带 `Lblᵒ` 的层号成立（含 S.layer） | YiMGRel `topᵐ`, `top-layerᵐ` | 编译定理 |
| `Rᵐ` 与 `Rᵉ`：第 0 层相同、颈槽位相同、孩子路径上的第 0 层槽位不同；在 `one` 上 `Rᵐ` 嵌入 `Rᵉ` | `zero-sameᵐ`, `neck-sameᵐ`, `one-diffᵐ`, `ᵐ→ᵉ-one` | 编译定理 |
| 更深的层号上，`Rᵐ` 与 `Rᵉ` 两个方向都没有映射（`mΩ` 前提逆变，`M⁰ → Ex⁰` 不成立） | — | 判断 |
| 槽位标签取 `Lblᵒ` 时，不含 Ω 形状的层号有框架和 `IndexTree` | YiMGFrame `frameᵒ`, `index-treeᵒ`, `pres-noΩᵒ` | 编译定理 |
| `Rᵐ` 上不含 Ω 形状的层号有 LowKeep，并给了一个前提全部填上的实例 | `lowKeepAtᵐ-noΩ`, `keep-child-zero` | 编译定理 |
| 第 0 层槽位处处取 `Ex⁰`：在 `one` 上走链第 0 步为空 | YiMGNeck `no-chainᵉ-one` | 编译否定（证据） |
| 第 0 层槽位处处取 `M⁰`：S.layer 的 Leaf 走 `topᵉ` 的证法要给 `M⁰` 孩子标签，这条已被 `YiELZero.no-all` 否定；Leaf 本身对 `slow` 型孩子推不出 | — | 判断 |
| S.layer 折到自身：框架有居民 | `frame-selfᵐ` | 编译定理 |
| S.layer 折到第 0 层：颈槽位的保留判定是走链，链的精确形式第 0 步为空 | `frame-neck-zero`, `no-chain-neck`, `no-chainᵉ-neck` | 编译定理 / 编译否定 |
| S.layer 经孩子 0 折到孩子层号：颈槽位保留进 `M⁰` 前提的槽位，框架为空；孩子槽位那一行与 YiXPNeg 同型 | `no-frame-neck-child`, `no-frame-Ωincᵐ` | 编译否定 |
| 较弱的链引理 `NeckLabChain` | YiMGNeck | 只是陈述；判断：未走通 |
| 离 "塔第 1 项上的 LowKeep" 还差：(i) `Lblᵒ (tw 1)`（判断：常规，要 `zero ⊕ b ≡ b` 搬运）；(ii) tw 1 颈槽位的 `NeckLabChain` 型证据；(iii) 框架只在实际推导上检查，避开 `no-frame-Ωinc` 型障碍（YiTL 方向）；(iv) 记号一侧 `fsT` 对下标单调（检索到 `EmbVVLZStandardOmega.fsT-mono₁`，要 `NF₁`，未核前提） | — | 判断 |
| tw 1 的颈链第一个迭代同样是 `lim`，所以精确形式同样为空（`g zero = up zero zero (suc zero)`，经下标层侧折出来是 `next⁺`）。按 "不替 YiKT 做" 没有编译 | — | 判断 |

#### 2. 文件表

三个文件都放在 `<仓库>/probes/OCF/Lean/` 下。每个文件先删自己的 `.agdai` 再冷编，按顺序编，6G 上限，每次约 15 秒。日志里只有本模块自己的 `Checking` 行。

| 文件 | 代码行 / 物理行 | 冷编退出码 | 最大驻留 |
|---|---|---|---|
| YiMGRel.lagda.md | 128 / 178 | 0 | 1.49G |
| YiMGFrame.lagda.md | 158 / 219 | 0 | 1.37G |
| YiMGNeck.lagda.md | 76 / 129 | 0 | 1.51G |

自查：检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、洞、`--cubical`、`irrelevant-projections`、本机路径，结果都是 0；除选项行外没有别的编译指示。三个文件都标 "读记号"，所以没有跑 importclosure。

#### 3. 定理表

下文的记号：
- `gL c = proj₁ (O.upz c (O.Ωt (S.child c)))`，即 `O.Ωt S.layer` 的分支函数；
- `gOne` 是 `O.Ωt K.one` 的分支函数；
- `neck = inj₁ (inj₁ tt)`；
- YiMGFrame 里的 `R` 指 `YiXPRel Lblᵒ` 的 `R`。

**YiMGRel**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `Rᵐ` 族 | `Rᵐ (nd s h) = H.Mᴴ (Sig (nd s h)) (Lowᵐ (nd s h)) (λ c → Rᵐ (h c)) (λ p → Lblᵒ (at (nd s h) p))`；`Lowᵐ (nd (sΩ k) h) (inj₁ t) = Neckᵐ k t`；`Neckᵐ zero (inj₁ _) = Ex⁰`；`Low⁼ᵐ a (inj₁ _) = Rᵐ a` | 合流后的关系族 | 定义 |
| `topᵐ` | `∀ a {ν} → Lblᵒ a ν → Rᵐ a (E.Ωt ν) (proj₁ (O.Ωt a))` | Leaf：带标签的层号，其 Ω 树读作 Ω_ν | 编译定理 |
| `top-layerᵐ` | `Rᵐ S.layer (E.Ωt Ω₁) (proj₁ (O.Ωt S.layer))` | 颈结点层号上的 Leaf | 编译定理 |
| `toˣ` / `ofˣ` | `∀ ℓ → NoΩ ℓ → ∀ {t x} → Rᵐ ℓ t x → Rˣ ℓ t x`，以及反方向 | 无 Ω 形状时与 `Rˣ` 互相给出 | 编译定理 |
| `zero-sameᵐ` | `(Rᵐ zero ≡ Rᵉ zero) × (Rᵐ zero ≡ Rˣ zero)` | 第 0 层三族相同 | 编译定理 |
| `neck-sameᵐ` | `∀ h → Lowᵐ (nd (sΩ zero) h) (inj₁ (inj₁ tt)) ≡ Lowᵉ (nd (sΩ zero) h) (inj₁ (inj₁ tt))` | 颈槽位前提与 `Rᵉ` 相同 | 编译定理 |
| `one-diffᵐ` | `(Lowᵐ K.one K.q1 ≡ H.M⁰) × (Lowᵉ K.one K.q1 ≡ Ex⁰)` | 孩子路径上的第 0 层槽位不同 | 编译定理 |
| `ᵐ→ᵉ-one` | `∀ {t x} → Rᵐ K.one t x → Rᵉ K.one t x` | 层号 one 上嵌入 `Rᵉ` | 编译定理 |
| `unemb`, `noΩ-child` | `∀ a → NoΩ a → ∀ {ν} → Lblᵒ a ν → Lbl a ν`；`∀ d → NoΩ (S.child d)` | 两种标签互推；最小实例的孩子不含 Ω 形状 | 编译定理 |

**YiMGFrame**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `toX` / `ofX` | `∀ ℓ → NoΩ ℓ → ∀ {t x} → Rᵐ ℓ t x → R ℓ t x`，以及反方向 | 与 `YiXPRel Lblᵒ` 互相给出 | 编译定理 |
| `lbl-pathᵒ` | `∀ {j a} → j ≤ a → NoΩ a → ∀ {ν κ} → Lblᵒ j ν → Lblᵒ a κ → ν ≤ᵀ κ` | 标签沿路径不降 | 编译定理 |
| `frameᵒ` | `∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) {ν κ} → Lblᵒ j ν → Lblᵒ (at ℓ p) κ → KeepSpec ℓ j ν p κ (kp ℓ o p w)` | 框架 | 编译定理 |
| `index-treeᵒ`, `pres-noΩᵒ` | `∀ ℓ → NoΩ ℓ → IndexTree ℓ`；`∀ ℓ → NoΩ ℓ → PresAt ℓ` | 路径证据与保持 | 编译定理 |
| `lowKeepAtᵐ-noΩ` | `∀ ℓ → NoΩ ℓ → LowKeepAtᵐ ℓ`，其中 `LowKeepAtᵐ ℓ = ∀ {j} (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ) (β : Tr⁺ j) (ν t : E.T) → Lblᵒ j ν → OK B → Prefixᵐ B t → Rᵐ j (E.ψ ν t ∷ []) (proj₁ β) → ∀ {a x} → Rᵐ ℓ a x → Rᵐ j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))` | LowKeep 移植到 `Rᵐ` | 编译定理 |
| `lowKeep-child`, `keep-child-zero` | `∀ d → LowKeepAtᵐ (S.child d)`；`∀ d (r : Rb (S.child d)) {a x} → Rᵐ (S.child d) a x → Rᵐ zero (E.ψ [] ([] ++ a) ∷ []) (proj₁ (ψ (S.child d) (proj₂ S.okay d) r (B₀ (S.child d)) zero (z≤ (S.child d)) (Ωt zero) x))` | 最小实例的孩子；前提全部填上 | 编译定理 |

**YiMGNeck**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `frame-selfᵐ` | `NodeFrameᵐ S.layer S.okay S.layer self Ω₁` | 折到自身有框架 | 编译定理 |
| `frame-neck-zero` | `KeepGᵐ zero [] (Lowᵐ S.layer neck) [] (kp S.layer S.okay neck (z≤ S.layer))` | 折到第 0 层时颈槽位走链 | 编译定理 |
| `no-chain-neck`（`no-chainᵉ-neck` 同） | `∀ r B t a → ChainAtᵐ S.layer S.okay r B t a neck [] gL → ⊥` | 链第 0 步要第一个迭代恰好读作 Ω_0（cof 1），而它的头是 `lim` | 编译否定 |
| `no-chainᵉ-one` | `∀ o r B t a → ChainAtᵉ K.one o r B t a K.q1 [] gOne → ⊥` | 处处取 `Ex⁰` 时，连 `one` 都过不了 | 编译否定 |
| `no-frame-neck-child` | `∀ ν → NodeFrameᵐ S.layer S.okay (S.child zero) (inc zero self) ν → ⊥` | 颈槽位保留进 `M⁰` 槽位为空（用 `slow`） | 编译否定 |
| `no-frame-Ωincᵐ` | `∀ c {j} (v : j ≤ S.child c) {ν} (c′ : Tr zero) (t : Pos⁼ (S.child c′)) {κ} → Lblᵒ (proj₁ (sl⁼ (S.child c′) t)) κ → κ <ᵀ ν → NodeFrameᵐ S.layer S.okay j (inc c v) ν → ⊥` | 与 YiXPNeg 同型 | 编译否定 |
| `NeckLabChain` | `∀ n → Σ E.T λ μ → Ex⁰ μ (iter (feed S.layer S.okay r B neck gL) (fromBr S.layer neck zero) (suc n)) × (E.γT (t ++ a) [] n ≤ᵀ μ)` | 第一个挡住的引理的较弱形式 | 只是陈述 |

否定定理的前提都可满足：`r B t a` 任取即可；`no-frame-Ωincᵐ` 取第 0 层子层，κ = [] 且 ν > []。链证据所针对的输入 `O.Ωt S.layer` 在读回域内，`top-layerᵐ` 给出它的推导。

#### 4. 第一个障碍

障碍在 S.layer 颈结点那一行、目标第 0 层时的走链证据，即 `ChainAtᵐ … neck [] gL` 在 n = 0 处：`Neckᵐ zero (inj₁ tt) (E.Ωt []) (feed S.layer S.okay r B neck gL zero)`。

**数学上挡住，不是工程问题。**
- 精确形式已有编译否定（`no-chain-neck`）。
- 换成较弱形式 `NeckLabChain`，还要记号侧 `fsT` 单调；这一形式未走通。
- 判断：分支前提只看 (η, c) 的设计里，Leaf、走链、保留进孩子三方合起来，都会推出 "第 0 层折叠输出有精确读回"。精确读回的 ℕ 极限一条要求孩子的标签严格低于极限的标签，这需要折叠输出的上界。另外 `limc⁺` 的第 0 项是零分支的折叠，而记号基本列的第 0 项是 γ 链的第 0 项，差一位，与 `YiELZero.slow` 同型，我判断很可能不成立。以上都未编译。

其余几处：自身行有框架；折到孩子层号已有两条编译否定。

#### 5. 偏离、事故与未读的东西

**偏离。**
- 第 1 步按简报取 `Lab = Lblᵒ`。但 `Rᵐ` 在颈槽位上不是 `YiXPRel Lblᵒ` 的 `R`；LowKeep 是经 `toX`/`ofX` 在不含 Ω 形状的层号上搬过来的。
- 第 2 步没有把 YiXPRows 的各行复制成颈前提参数化的版本。`KeepGᵐ`、`NodeFrameᵐ`、`ChainAtᵐ` 只是把 YiXPRows 的证据类型局部重述了一遍。`frame-selfᵐ` 编译过了，但没有组装成 S.layer 上的自身行保持定理。

**事故。** 有一次用 `/usr/bin/time -l` 包着跑，被沙盒拦了 sysctl，退出 1；这是 time 的退出码，不是 agda 的。改用 `+RTS -s` 重跑，退出 0。没有撞墙。

**只凭检索或转述的东西。**
- YiTLReduce、YiWBNeg、YiKT、YiTF、YiTA、YiRR 都没读。
- `EmbVVLZStandardOmega.fsT-mono₁` 只是检索到，没有核它的前提。
- "`E.Ωt []` 是 Ω_0 = 1" 是从 `topᵉ zero` 这条子句（`m1 refl mz`）推出来的，没有单独查定义。

一次性试验文件在 `<实验目录>/work/YiMG/`（`MG0.agda`、`MG1.agda` 及日志）。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：合流两个关系族（前缀 YiMG，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路选项原文 "合流两个关系族 (Recommended)"。同批另四路与你互不导入。

#### 作者的决定与背景（2026-11-16）
- 作者定：主线停逐项，改攻整体引理（读回域上的 Leaf 加 LowKeep）；参照只用记号关系 M。第七十二批选项原文："构造：塔第 1 项上的 LowKeep (Recommended), 配对否定：找塔第 1 项上的反例 (Recommended), 合流两个关系族 (Recommended), 记号侧：截断加法与部分和链点"；摆脱侧 "右边放宽的底关系 (Recommended)"。同批五路：构造 `YiKT`（Fable 5.2）、配对否定 `YiTF`、合流 `YiMG`、截断加法 `YiTA`、摆脱侧 `YiRR`（Opus 5.5），互不导入。
- **第七十一批的结果**（主审 8G 冷编复核过，读陈述；回报在 `probes/Survey/Reports-2026-11-16/`）：
  - `YiXPExact.lowKeepAt-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtˣ ℓ`、`lowKeepˣ`：精确标签 `YiGLFrame.Lbl` 下 LowKeep 对一切不含 Ω 形状的层号无条件成立；保持引理族的一般各行不用槽位标签的性质（`YiXPRel`、`YiXPRows`、`YiXPFold` 对抽象 `Lab` 参数化），框架只靠 `uniq`、`below`、`YiXPFrame.lbl-path`。`YiXPNeg.no-index-tree-tw1ˣ`：折叠 `YiRWFold.kp` 对 "Ω 形状、槽位在孩子里、路径经 `inc`" 恒为 `nothing`（走链），记号一侧在孩子里更深的槽位处保留，于是逐槽位证据域 `IndexTree` 在塔第 1 项上为空（只否定证据域）。
  - `YiELLim.limAt : ∀ u → cof u ≡ cω → LimAt u`；`YiELZero.no-all`（带下界证据 `M⁰` 的第 0 层树不都有精确标签）→ 第 0 层分支前提要换精确读回 `Ex⁰ η d = Lbl (↑ zero d) η`（`ex→M⁰`、`ex-lower`、`child-lbl`）；`YiELOmega.Lblᵒ`（下标层为第 0 层的 Ω 形状层号有精确标签，带 `CofΩ` 字段）、`uniqᵒ`、`belowᵒ`（要 `PosOk`）、关系族 `Rᵉ`（第 0 层分支前提用 `Ex⁰`）、`topᵉ`、`lbl-layer`；`YiELChain.ex-next`、`ex-add`（要 `HdLe p s`）。`Rˣ` 与 `Rᵉ` 之间没有映射。
  - `YiWBNeg.Neg.no-next`、`no-base`：只放宽左边的底关系（含最宽的 `Ω≼`）给不出两条实际链前缀 2 的底前提；`val-left-right`：值序上成立，用的是右边一个第 1 层槽位结点的**非首分支**（该槽位层号自己的 Ω 树）。
  - `YiTLReduce`：同步对象（`kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`）各孩子层号 `a₁ c` 上 Leaf 无前提（`leaf-a₁`）；`tail-fromᴱ`、`k2′-from-keep : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → Kᴱ′ 2`（`KeepOut c = ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (proj₁ (out c))`）；`no-lbl-a₁`（这些层号没有 `Lbl`）；第一个挡住的引理 `TightStep d`（顶槽位上紧的链的一步，`StepU′ (a₁ (suc d))` 的实例，陈述已编译），三种现有证据在那里都为空（`no-index-top`、`block-frame`、`no-lbl-hh`）。纸面方向（YiTL 判断）：把框架换成只在实际推导的 κ 处检查，量化域限在读回域的推导上（前缀读空，退路行只承载平凡参照）。
- **决定性问题**（主审判断）：塔第 1 项（及以它为前缀的层号）上的 LowKeep 成不成立。成立要一种新证据；不成立就要改折叠的那一行（第 4 层逼出的定义改动，交作者）。
- 其他已编译的事实：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiFOValue.fallback-prefix`（退路保留此前折叠的值）；`YiXUFirst.first-ceiling`（干净对象第一支 ≤ ψ₀(Ω₄)）；`YiORBound.original-neg`（封闭关系下原行仍不过判据）。

#### 本路的任务
`YiGLExact.Rˣ`（槽位标签 `Lbl`，Ω 形状取 `⊥`；第 0 层分支前提 `M⁰`）与 `YiELOmega.Rᵉ`（槽位标签 `Lblᵒ`，下标层为第 0 层的 Ω 形状层号有标签；第 0 层分支前提 `Ex⁰`）之间没有映射。YiXP 的 LowKeep 定理在 `Rˣ` 上；YiEL 的 Leaf `topᵉ` 在 `Rᵉ` 上。要合成一个关系族，使两边已证的东西都在其上成立。

#### 要做的（按序）
0. **设计**：写出合流后的关系族 `Rᵐ`（槽位标签取 `Lblᵒ`，第 0 层分支前提取 `Ex⁰` 或说明为什么不取），以及它与 `Rˣ`、`Rᵉ` 的关系（嵌入或等价，在不含 Ω 形状的层号上）。在 `YiBVSmall` 的孩子层号与 `S.layer` 上确认类型。不成立就停下回报。
1. **移植 LowKeep**：用 `YiXPRel`/`YiXPRows`/`YiXPFold` 的抽象 `Lab` 参数化，取 `Lab = Lblᵒ`，证框架在不含 Ω 形状的层号上仍有居民（要 `uniqᵒ`、`belowᵒ`（带 `PosOk`）、标签沿路径不降），得到 `Rᵐ` 上的 `lowKeepAt-noΩ`。
2. **下标层为第 0 层的 Ω 形状层号**：在 `Rᵐ` 上试 LowKeep（颈结点一型，`S.layer`）；挡住就交第一个挡住的引理。
3. 说明合流后离 "塔第 1 项上的 LowKeep" 还差什么（判断即可；那是 YiKT 的任务，不要替它做）。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 6G（同批另有四路，外部广撒网也可能在编，机器共 64G；峰值超过 4G 先改形状）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
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


# 记号侧：截断加法与部分和链点（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 15:24 至 15:44 |
| 工具调用 / agda 编译 (粗数) | 52 / 9 |
| token (usage 字段，按消息去重) | 输出 124829；新写入缓存的输入 238564；读缓存的输入 6197334；其余输入 80 |
| 写过的仓库文件 | `YiTAAdd.lagda.md`, `YiTAChain.lagda.md`, `YiTAReal.lagda.md` |
| 文件前缀 | `YiTA` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0；带吸收的和 ⊞ 的单调与标准形；去掉 HdLe 的 ex-add′、部分和与 limc⁺ 的精确读回（ex-cum、ex-limc、lbl-limc）、Real 与 cofΩ-all 均无前提；与 fsn 字面交换被否定（no-comm） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b72/YiTA.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### YiTA 回报：记号侧截断加法与部分和链点（第七十二批）

##### 1. 判决

**对纲领与目标**：四条纲领都没有触犯。树、折叠、合法性的定义都没改，也没有发现需要改的依据。三个新文件都在验收一侧（读记号），不算 "树自足" 的进展。`YiTAReal` 里的树是沿记号的 `HC` 推导造的，属于记号引导的树，只用来证明验收一侧的命题，不是成品候选。

这一路得到两件与站无关的结果：

- 第 0 层的精确读回 `Ex⁰` 对树的加法和部分和极限 `limc⁺` 都封闭，标签取记号一侧带吸收的和 `⊞`。目标是主项时，`limc⁺` 要满足的条件与 `lim` 结点逐字相同，部分和不再额外要求什么。
- `YiELChain.Real` 原来没有居民，现在是无前提的定理。所以 `YiELOmega.Lblᵒ` 的 `CofΩ` 字段对一切共尾度为 Ω₁ 的 ν 都可以推出（`cofΩ-all`），包括 YiEL 回报说要逐个填的 Ω₁·2。

**各步进度**

- 第 0 步：完成。临时文件 `YiTA0.agda` 退出码 0，定义 `tr`/`⊞`，用 `refl` 检查了 ω⊞ω² = ω²、ω²⊞ω = ω²+ω、1⊞ω = ω、ω⊞1 = ω+1，并找到字面交换的反例。仓库里的实例是 `ex-ω+ω²`、`ex-ω²+ω`。
- 第 1 步：完成，但有一处偏离。右边严格单调、保持标准形、去掉 `HdLe` 的 `ex-add′` 都已证。**"与 `fsn` 交换" 的字面形式不成立**，有编译否定 `no-comm`。实际证的是精确式 `⊞-fsn` 和不等式 `fsn-⊞≤`，`ex-add′` 只需要后者。左边单调没有做，目前用不到。
- 第 2 步：完成，比简报多走了一步。部分和链点见 `ex-cum`、`ex-limc`、`lbl-limc`，实例 `ex-limc-ω²` 的第一步发生吸收，不满足 `HdLe`（`no-hdle`）。`Real` 已证（`real`、`real-exact`），推论 `cofΩ-all`。
- 第 3 步：见第 4 节。这一路本身没有被挡住。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `⊞` 的定义与小例 | `YiTA0.agda`；`YiTAChain.ex-ω+ω²`、`ex-ω²+ω` | 编译定理 |
| 右边严格单调（对一切项，不要 NF） | `YiTAAdd.⊞-<ʳ`、`⊞-≤ʳ` | 编译定理 |
| 保持标准形 | `YiTAAdd.⊞-NF` | 编译定理 |
| 与 `fsn` 字面交换 | `YiTAAdd.no-comm` | 编译否定 |
| 基本列的精确式与上界 | `YiTAAdd.⊞-fsn`、`fsn-⊞≤` | 编译定理 |
| 去掉 `HdLe` 的加法读回 | `YiTAChain.ex-add′` | 编译定理，无前提 |
| 部分和、`limc⁺` 的读回 | `YiTAChain.ex-cum`、`ex-limc`、`lbl-limc` | 编译定理，无前提 |
| `Real` | `YiTAReal.real`、`real-exact` | 编译定理，无前提 |
| 一般 ν 上的 `CofΩ` | `YiTAReal.cofΩ-all` | 编译定理，无前提 |
| 折叠链点 `out (chain n)` 的精确标签 | 没有做 | 判断：主线问题（第 4 节） |
| `⊞` 左边单调 | 没有做 | 用不到 |

##### 2. 文件表

| 文件 | 代码行（代码块内非空行） | 冷编退出码 |
|---|---|---|
| `<仓库>/probes/OCF/Lean/YiTAAdd.lagda.md` | 227 | 0 |
| `<仓库>/probes/OCF/Lean/YiTAChain.lagda.md` | 102 | 0 |
| `<仓库>/probes/OCF/Lean/YiTAReal.lagda.md` | 79 | 0 |

- 冷编：先删这三个模块自己的 `.agdai`，再按依赖次序各编一次，堆上限 6G。每份日志只有自己模块的一行 `Checking`。
- 禁用构造（`postulate`、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、洞、`--cubical`、`--irrelevant-projections`）和本机路径都检索过，结果为 0。选项行都是 `--safe --without-K --lossy-unification`。
- 三个文件都读记号，没有标 "不读记号"，所以没跑 `importclosure.py`。`YiTAAdd` 只导入 `EboLeanDef`、`EboLeanBase`、`EboLean3Base`，不涉及树。
- 日志与第 0 步的临时文件在 `<实验目录>/work/YiTA/`（`*.log`、`*.cold.log`、`YiTA0.agda`）。

##### 3. 定理表（陈述逐字）

`tr y α` 是 α 中第一个低于 y 的项之前的部分；`α ⊞ [] = α`，`α ⊞ (y ∷ ys) = tr y α ++ (y ∷ ys)`；`Σ⊞ γ (suc n) = Σ⊞ γ n ⊞ γ (suc n)`。

**YiTAAdd**（只在记号一侧）

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `⊞-<ʳ` | `∀ α {μ β} → μ <ᵀ β → α ⊞ μ <ᵀ α ⊞ β` | 对右边严格单调，对一切项成立 | 定理 |
| `⊞-≤ʳ` | `∀ α {μ β} → μ ≤ᵀ β → α ⊞ μ ≤ᵀ α ⊞ β` | 弱单调 | 定理 |
| `⊞-NF` | `∀ {α β} → NF α → NF β → NF (α ⊞ β)` | 保持标准形 | 定理 |
| `⊞-cof` | `∀ α y ys → cof (α ⊞ (y ∷ ys)) ≡ cof (y ∷ ys)` | 共尾度随右边 | 定理 |
| `⊞-pred` | `∀ α β → cof β ≡ c1 → pred (α ⊞ β) ≡ α ⊞ pred β` | 前驱随右边 | 定理 |
| `⊞-fsn` | `∀ α y ys n → fsn (α ⊞ (y ∷ ys)) n ≡ tr y α ++ fsn (y ∷ ys) n` | 基本列的精确式 | 定理 |
| `fsn-⊞≤` | `∀ α {y ys} n → NF α → NF (fsn (y ∷ ys) n) → fsn (y ∷ ys) n ≤ᵀ (y ∷ ys) → fsn (α ⊞ (y ∷ ys)) n ≤ᵀ α ⊞ fsn (y ∷ ys) n` | 和的基本列不高于 α 加右边的基本列 | 定理 |
| `no-comm` | `(∀ {α β} → NF α → NF β → cof β ≡ cω → ∀ n → fsn (α ⊞ β) n ≡ α ⊞ fsn β n) → ⊥` | 字面交换不成立（ω⊞ω² 在 0 处：左边是 0，右边是 ω） | 编译否定 |
| `⊞-noabs` | `∀ {p s} → HdLe p s → (p ∷ []) ⊞ s ≡ p ∷ s` | 首项不被吸收时就是拼接 | 定理 |
| `⊞-abs` | `∀ {α y ys} → HdLt α y → α ⊞ (y ∷ ys) ≡ y ∷ ys` | 后项首项更高时整段吸收 | 定理 |
| `⊞-ge` | `∀ α {β} → NF α → NF β → β ≤ᵀ α ⊞ β` | 和不低于后项 | 定理 |
| `⊞-<prin` | `∀ {x} α β → α <ᵀ (x ∷ []) → β <ᵀ (x ∷ []) → α ⊞ β <ᵀ (x ∷ [])` | 主项之下对 `⊞` 封闭 | 定理 |
| `Σ⊞-ge` / `Σ⊞-<prin` | `∀ {γ} → (∀ n → NF (γ n)) → ∀ n → γ n ≤ᵀ Σ⊞ γ n` / `∀ {γ x} → (∀ n → γ n <ᵀ (x ∷ [])) → ∀ n → Σ⊞ γ n <ᵀ (x ∷ [])` | 部分和不低于末项，且留在主项之下 | 定理 |

**YiTAChain**（树侧的读回）

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `ex-add′` | `∀ (b y : Tr zero) {α β} → Ex⁰ α b → Ex⁰ β y → Ex⁰ (α ⊞ β) (b + y)` | 树的加法读作带吸收的和，不要 `HdLe` | 定理，无前提 |
| `ex-add-noabs` | `∀ {p} (b y : Tr zero) {s} → Ex⁰ (p ∷ []) b → Ex⁰ s y → HdLe p s → Ex⁰ (p ∷ s) (b + y)` | `YiELChain.ex-add` 是上一条的推论 | 定理 |
| `ex-cum` | `∀ (G : ℕ → Tr zero) {γ} → (∀ n → Ex⁰ (γ n) (G n)) → ∀ n → Ex⁰ (Σ⊞ γ n) (O.cum G n)` | 部分和读作 `Σ⊞` | 定理 |
| `ex-limc` | `∀ {t} (G : ℕ → O.Tr⁺ zero) {γ} → (∀ n → Ex⁰ (γ n) (proj₁ (G n))) → NF t → E.cof t ≡ E.cω → (∀ n → E.fsn t n ≤ᵀ Σ⊞ γ n) → (∀ n → Σ⊞ γ n <ᵀ t) → Ex⁰ t (proj₁ (O.limc⁺ G))` | 基本列夹在部分和之下时，`limc⁺` 读作 t | 定理 |
| `lbl-limc` | `∀ {x} (G : ℕ → O.Tr⁺ zero) → NF (x ∷ []) → E.cof (x ∷ []) ≡ E.cω → (∀ n → Σ E.T λ μ → Ex⁰ μ (proj₁ (G n)) × (E.fsn (x ∷ []) n ≤ᵀ μ) × (μ <ᵀ x ∷ [])) → Ex⁰ (x ∷ []) (proj₁ (O.limc⁺ G))` | 目标是主项时，`limc⁺` 的条件与 `lbl-lim` 逐字相同 | 定理 |
| `ex-ω+ω²`、`ex-ω²+ω` | `Ex⁰ ω²′ (proj₁ ωtr + proj₁ ω²tr)`；`Ex⁰ (ψ [] (𝟏 ∷ 𝟏 ∷ []) ∷ ωh ∷ []) (proj₁ ω²tr + proj₁ ωtr)` | 小例 | 定理 |
| `ex-limc-ω²`、`no-hdle` | `Ex⁰ ω²′ (proj₁ (O.limc⁺ G₁))`；`HdLe 𝟏 ω′ → ⊥` | `limc⁺`(1, ω, ω, …) 读作 ω²；第一步吸收，旧 `ex-add` 用不上 | 定理 |

**YiTAReal**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `fsn-prin` | `∀ b bs → (E.cof (b ∷ bs) ≡ E.c1 → ⊥) → ∀ n → Σ E.T λ a′ → E.fsn (ψ [] (b ∷ bs) ∷ []) n ≡ ψ [] a′ ∷ []` | a 不是后继时，ψ₀(a) 的基本列每项仍是主项 | 定理 |
| `prin` | `∀ {t} → E.HC t → ∀ a → t ≡ ψ [] a ∷ [] → NF t → Σ (O.Tr⁺ zero) λ d → Ex⁰ t (proj₁ d)` | 主项沿 `HC` 造树：a 后继时用 `next⁺`，否则用 `limc⁺` | 定理 |
| `real-exact` | `∀ {η} → NF η → η E.<ᵀ E.Ωs [] → Σ (Tr zero) (Ex⁰ η)` | 每个可数标准形都有带精确读回的第 0 层树 | 定理，无前提 |
| `real` | `Real` | `YiELChain.Real` 成立（取 η′ = η） | 定理，无前提 |
| `cofΩ-all` | `∀ {ν} (h : Tr zero → L) → E.cof ν ≡ E.cΩ [] → CofΩ h ν` | `Lblᵒ` 的 `CofΩ` 字段一般可推出 | 定理，无前提 |

`real-exact` 用到的 `HC` 来自已有的 `EboLeanTree.hc : ∀ {t} → NF t → Ctbl t → HC t`（文首标无前提），再经 `YiELZero.ctbl<`。

##### 4. 第一个障碍

这一路的三步没有被挡住。往下走，第一个挡住的引理是：**折叠在第 0 层的链点 `out (chain n)` 的精确标签**。按 `lbl-limc` 的接口精确写出来，就是对 Ω 结点行 `output ≡ limc⁺ (λ n → out (chain n))`（目标 t 是主项）要有 `∀ n → Σ μ, Ex⁰ μ (out (chain n)) × (fsn t n ≤ᵀ μ) × (μ <ᵀ t)`。

- 【判断】这是**数学上**挡住的。它等于把 LowKeep 在目标第 0 层的结论从 `H.M⁰` 加强成精确读回，也就是 YiEL 回报第 4 节的 "一般链点"。部分和这一层已经不额外要求什么（`lbl-limc`），剩下的全在每个链点自己的标签上。这一条没有陈述成 Agda 引理，也没有接到具体对象（如 `YiBSClean.row` 或 YiTL 的同步对象）。
- 【判断】"折叠第 0 层的输出都是 ψ₀(·) 主项，所以 `lbl-limc` 适用" 没有逐个对象核过。
- YiEL 提的另一件，把 `Rˣ` 上的族移到 `Rᵉ`（工程量），这一路没有碰。

##### 5. 偏离与事故；没有读、只凭转述的东西

**偏离**
- 简报第 1 步要证 "与 `fsn` 交换"。字面形式被 `no-comm` 否定，改证精确式 `⊞-fsn` 和不等式 `fsn-⊞≤`。YiEL 回报里 "要证它与 `fsn` 交换" 的判断，字面上不成立。
- 第 2 步的 "再试 Real" 做成了无前提定理。办法是借用已有的 `EboLeanTree.hc`，沿记号的 `HC` 推导造树；这些树不是折叠的输出。
- 第 2 步 "对 YiELChain 里的链点形状"，交的是对任意 `G` 的 `limc⁺` 外加一个小实例，没有接具体的折叠对象。
- "百行量级" 的估计：`YiTAAdd` 实际 227 行代码，含小例与反例。

**事故**
- 两次退出 42，都是开了 `--hidden-argument-puns` 后 `{[]}` 被当成双关（`InvalidPun.Constructor`）。改成具名隐式参数 `{β = []}` 后通过。
- 有一次用 `/usr/bin/time -l` 包 agda，被沙盒挡住（`sysctl kern.clockrate`），exit 1 是 `time` 的退出码。agda 本身已经通过：重跑无输出，退出 0；冷编也确认通过。所以峰值内存没有测到，单个模块编译约 15 秒。
- 没有出现 251、124、154。

**没有读证明、只读签名或文首的**
- `EboLeanTree`：只读了文首、`hcA` 与 `hc` 几行；`EboLeanTau.wfNF′` 没有读。
- `EboLeanClosure.cl-fsn-NF`、`trian-fsn` 只看签名；`EboLeanTrian` 只读了 `Trian` 记录。
- `YiELOmega` 只看了文首与 `CofΩ`、`Lblᵒ` 的定义行；`YiBSClean` 与 `YiATStart` 只看了文首与 `row` 的签名。
- 没有遇到性能问题，所以 Bedrock 性能手册和 `EBOHandbook` 4.2、4.6 节都没有打开。
- `AGENTS.md` 全文读了（在上下文中）。

**其余标注**
- 第 4 节的 "数学上挡住" 和 "折叠第 0 层的输出是主项" 都是判断。
- 没有搬任何已有证明。`ex-add′` 的极限一条沿用 `YiELChain.ex-add` 的结构，但内容是新写的。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：记号侧，截断加法与部分和链点的精确读回（前缀 YiTA，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路选项原文 "记号侧：截断加法与部分和链点"。同批另四路与你互不导入。

#### 作者的决定与背景（2026-11-16）
- 作者定：主线停逐项，改攻整体引理（读回域上的 Leaf 加 LowKeep）；参照只用记号关系 M。第七十二批选项原文："构造：塔第 1 项上的 LowKeep (Recommended), 配对否定：找塔第 1 项上的反例 (Recommended), 合流两个关系族 (Recommended), 记号侧：截断加法与部分和链点"；摆脱侧 "右边放宽的底关系 (Recommended)"。同批五路：构造 `YiKT`（Fable 5.2）、配对否定 `YiTF`、合流 `YiMG`、截断加法 `YiTA`、摆脱侧 `YiRR`（Opus 5.5），互不导入。
- **第七十一批的结果**（主审 8G 冷编复核过，读陈述；回报在 `probes/Survey/Reports-2026-11-16/`）：
  - `YiXPExact.lowKeepAt-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtˣ ℓ`、`lowKeepˣ`：精确标签 `YiGLFrame.Lbl` 下 LowKeep 对一切不含 Ω 形状的层号无条件成立；保持引理族的一般各行不用槽位标签的性质（`YiXPRel`、`YiXPRows`、`YiXPFold` 对抽象 `Lab` 参数化），框架只靠 `uniq`、`below`、`YiXPFrame.lbl-path`。`YiXPNeg.no-index-tree-tw1ˣ`：折叠 `YiRWFold.kp` 对 "Ω 形状、槽位在孩子里、路径经 `inc`" 恒为 `nothing`（走链），记号一侧在孩子里更深的槽位处保留，于是逐槽位证据域 `IndexTree` 在塔第 1 项上为空（只否定证据域）。
  - `YiELLim.limAt : ∀ u → cof u ≡ cω → LimAt u`；`YiELZero.no-all`（带下界证据 `M⁰` 的第 0 层树不都有精确标签）→ 第 0 层分支前提要换精确读回 `Ex⁰ η d = Lbl (↑ zero d) η`（`ex→M⁰`、`ex-lower`、`child-lbl`）；`YiELOmega.Lblᵒ`（下标层为第 0 层的 Ω 形状层号有精确标签，带 `CofΩ` 字段）、`uniqᵒ`、`belowᵒ`（要 `PosOk`）、关系族 `Rᵉ`（第 0 层分支前提用 `Ex⁰`）、`topᵉ`、`lbl-layer`；`YiELChain.ex-next`、`ex-add`（要 `HdLe p s`）。`Rˣ` 与 `Rᵉ` 之间没有映射。
  - `YiWBNeg.Neg.no-next`、`no-base`：只放宽左边的底关系（含最宽的 `Ω≼`）给不出两条实际链前缀 2 的底前提；`val-left-right`：值序上成立，用的是右边一个第 1 层槽位结点的**非首分支**（该槽位层号自己的 Ω 树）。
  - `YiTLReduce`：同步对象（`kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`）各孩子层号 `a₁ c` 上 Leaf 无前提（`leaf-a₁`）；`tail-fromᴱ`、`k2′-from-keep : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → Kᴱ′ 2`（`KeepOut c = ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (proj₁ (out c))`）；`no-lbl-a₁`（这些层号没有 `Lbl`）；第一个挡住的引理 `TightStep d`（顶槽位上紧的链的一步，`StepU′ (a₁ (suc d))` 的实例，陈述已编译），三种现有证据在那里都为空（`no-index-top`、`block-frame`、`no-lbl-hh`）。纸面方向（YiTL 判断）：把框架换成只在实际推导的 κ 处检查，量化域限在读回域的推导上（前缀读空，退路行只承载平凡参照）。
- **决定性问题**（主审判断）：塔第 1 项（及以它为前缀的层号）上的 LowKeep 成不成立。成立要一种新证据；不成立就要改折叠的那一行（第 4 层逼出的定义改动，交作者）。
- 其他已编译的事实：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiFOValue.fallback-prefix`（退路保留此前折叠的值）；`YiXUFirst.first-ceiling`（干净对象第一支 ≤ ψ₀(Ω₄)）；`YiORBound.original-neg`（封闭关系下原行仍不过判据）。

#### 本路的问题（YiEL 回报第 4 节）
`YiELChain.ex-add : ∀ {p} (b y : Tr zero) {s} → NFP p → Ex⁰ (p ∷ []) b → Ex⁰ s y → HdLe p s → Ex⁰ (p ∷ s) (b + y)` 要 `HdLe p s`（后项的首项不高于前项，记号一侧不发生吸收）。部分和形式的链点（`limc⁺`、`cum` 的部分和）在后项首项更高时，记号一侧发生吸收，`Ex⁰` 的标签要换成吸收后的项。YiEL 判断：要在记号一侧定义带截断的加法 `α ⊞ β`，证它对 β 单调、与 `fsn` 交换，百行量级，不涉及树的定义。同一条引理也是 `YiELChain.Real` 的缺口。

#### 要做的（按序）
0. **定义与最小检查**：在记号一侧（`OCF/Align/EboLeanDef`、`EboLeanBase` 的 `NF`、`<ᵀ`、`fsn`）定义 `α ⊞ β`（标准形加法，含吸收），写出 `ex-add` 去掉 `HdLe` 后的陈述 `Ex⁰ (p ⊞ s) (b + y)` 一类，在 ω + ω²、ω² + ω 等小例上编译。不成立就停下回报。
1. **证** `⊞` 的单调、与 `fsn` 交换、保持 `NF`，以及去掉 `HdLe` 的 `ex-add`。
2. **部分和链点**：得到 `limc⁺`/`cum` 的部分和的 `Ex⁰`（对 `YiELChain` 里的链点形状），再试 `Real`。
3. 交第一个挡住的引理。

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


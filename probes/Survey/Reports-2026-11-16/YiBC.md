# 换基证据对真实链孩子的覆盖（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 02:46 至 03:20 |
| 工具调用 / agda 编译 (粗数) | 56 / 17 |
| token (usage 字段，按消息去重) | 输出 194060；新写入缓存的输入 311298；读缓存的输入 10634164；其余输入 110 |
| 写过的仓库文件 | `YiBCCover.lagda.md`, `YiBCNeg.lagda.md`, `YiBCReach.lagda.md`, `YiBCSync.lagda.md` |
| 文件前缀 | `YiBC` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0，三件不读记号的导入闭包干净；读回域上换基证据对同步对象、真实链孩子、各站与任意链点孩子都满（full-sync、full-chain、full-kl、full-kl-child）；变量 a 的量化域上给不出（no-sync，谓词太宽）；块一侧：嵌入块到达换基行而不在码域里（reach、yₑ∉，ω 代替链点）；副本与原定义逐字相等（a₁-eq、chain-eq） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b76/YiBC.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### 1. 判决

**对纲领与目标的意味**
- 换基要的证据（`Rb`、`Schema`）只读层号，是树侧自己的字面地板，不引用记号。三个仓库文件不读记号（`importclosure` 退出 0）。
- 在规范读回域上，证据对一切站 n、一切链点都成立（`full-kl`、`full-kl-child`），闭包论证与阶段无关，这符合 "树自足" 的判据。
- 在变量 a 的量化域上证据给不出，有编译否定 `no-sync`。这条否定支持 "量化域先取带证据的读回域" 这条做法。它的反例不在读回域内，读作 "谓词太宽"，不读作数学障碍。
- 本路没有改树、折叠、合法性，也没有值的定理。

**各步进度**
- 第 0 步：完成。临时文件 `YiBC0.agda`，退出 0。
- 第 1 步：完成。仓库文件 `YiBCCover`，副本与实例在 `YiBCSync`。
- 第 2 步：完成。
  - 变量 a 上的编译否定。
  - 码域缺口：换基行收到的嵌入块不在码域里，有编译否定和形状定理。
- 第 3 步：覆盖表见下。

**第 0 步：证据的类型**（在临时文件里以 `refl` 编译，ℓ = `nd (sΩ zero) a`，a 是变量）
- `Ok ℓ ≡ (⊤ × ((c : Tr zero) → zero ≤ a c)) × ((c : Tr zero) → Ok (a c))`
- `Rb ℓ ≡ Maybe (Schema zero a) × ((c : Tr zero) → Rb (a c))`
- `Schema zero a` 的六个字段：
  - `floor : L`
  - `offsets : Tr zero → L`
  - `Ok floor`
  - `zero ≤ floor`
  - `∀ c → OkO floor (offsets c)`
  - `∀ c → a c ≡ floor ⊕ offsets c`
- `floor S ≤ j` 由 `route` 的 `inj₂` 在折叠内部给出；`Ok j` 由 `downOk` 在折叠内部给出。两者都不需要外部证据。
- 真实链孩子的层号：
  - `a₁ c ≡ tw 1 ⊕ (zero ⊕ ↑ (h₁ c) (Ωt (h₁ c)))`。
  - c = `lim f r` 时是 `nd sL _`，它的 `Rb` 第一分量是 `⊤`，顶上不要证据。证据落在它里面的 Ω 形状结点上。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 同步对象 kl 1 上证据满吗 | 满：`full-sync` | 编译定理 |
| 真实链孩子 `a₁ (chain m)` 上呢 | 对一切 m 满。现行链 `full-chain`，换基链 `full-chainᴮ`，`YiSYReduce` 的两个实例 `full-chainᴱ`、`full-chainᶻ` | 编译定理 |
| 各站 kl n，以及孩子是第 `tw n` 层任意树的情形 | 满：`full-kl`、`full-kl-child`、`full-↑` | 编译定理 |
| 变量 a 的同步对象（`YiSYReduce.Sync` 的量化域） | 没有统一构造，缺在孩子上：`no-sync`、`no-uniform` | 编译否定 |
| 顶结点那一份证据用不用得到 | `Fd` 与回灌里用不到：`top-idle`、`top-idle-feed` | 编译定理 |
| `seen` 里重建层 `j ⊕ offsets S c` 的证据 | 条件有：`route` 给 `inj₂` 时为 `rb-row`、`full-row`。`YiBSFold` 那里现在用 `rb-no` | 编译定理 |
| 反变在证据上会不会出现 | 不出现。`Rb` 是层号上的正递归，构造只经 `OkO↑`，对任意树成立 | 构造是编译定理；"不出现" 的读法是判断 |
| V149 那种块在这里会不会出现 | 在 `a₁ ω` 上会（ω 代替链点）：`way` 行嵌入的块 `yₑ` 到达换基行的 `seen` 一支（`reach`），它不在 `Read` 码域里（`yₑ∉`）。在 `oₛ`、`oᴱ`、`oᶻ` 三个 Ok 下同形 | 编译定理（形状档） |
| 同样的块在 `a₁ (chain m)` 本身上会不会出现 | 链点分量未知，未展开 | 判断 |
| 码域在嵌入下封闭吗 | 不封闭：`emb∉read`、`∉dom` | 编译否定 |
| 带任意分支函数的块（真正的方向反变）在同步计算里出现吗 | 未查。候选来源：回灌输出在后继形状层上作块 `suc c` | 判断 |
| 副本与原定义相等吗 | 相等：`a₁-eq`、`feed-eq`、`chain-eq` | 编译定理（验收文件） |

**覆盖表**（层号 × 证据）

| 层号 | Ok | Rb | 每个 Ω 结点都是 just | 块在码域内 |
|---|---|---|---|---|
| kl 1 = `nd (sΩ zero) a₁` | 有 | 有 | 有（顶上那一份用不到） | Ωt 块：有 |
| `a₁ c`，c 是变量 | 有 | 有 | 有 | — |
| `a₁ (chain m)` | 有 | 有 | 有 | ω 代替时，嵌入块：无；chain m 本身：判断 |
| 变量 a 的同步对象 | 作前提 | 无统一构造 | 无 | — |
| kl n 与 `klc n c`，c 是任意树 | 有 | 有 | 有 | 未查 |
| `a ⊕ ↑ k t`，t 是任意树 | 有 | 有 | 条件：要 `Full a` | — |
| `seen` 的重建层 | 有 | 条件：`route` 为 `inj₂` | 条件同左 | — |
| 任意合法层号 | 有 | 无统一构造 | 无 | — |

**两种出路及代价**（都是判断）
- **收量化域，证据一侧：** 给同步模块加参数 `r : Rb (nd (sΩ zero) a)` 与 `Full`，或者把 a 限成读回形 `floor ⊕ ↑ k t`。实例用 `rbₛ`、`full-sync`。约 10 到 30 行，不改定义。
- **收量化域，块一侧：** 给 `Read` 加一个 "沿第一孩子嵌入" 的码，就能包含 `yₑ`。约 50 到 150 行，这个行数是估计。它不覆盖上折（`YiBSUpNeg`），也不覆盖回灌输出作块的情形。
- **改块：** 把 `up` 的嵌入字段在 Ω 形状层上改成族，要动 `YiRWBlock` 的 `T`、`Lt`、`Sig`，以及 Ops、Path、Fold 和全部折叠。有 506 个模块（约 6 万行）导入 `YiRWBlock`。对证据不需要，只在要如实换基非码生成的块时才需要。代价很高，交作者定，本路没做。
- **嵌套换基：** `seen` 里的证据已经有了（`rb-row`）。要用它就得改折叠，开新候选，本路没做。

#### 2. 文件表

| 文件 | 总行 / 非空代码行 | 冷编退出码 | 记号 |
|---|---|---|---|
| `probes/OCF/Lean/YiBCCover.lagda.md` | 238 / 142 | 0 | 不读记号，导入闭包 0 |
| `probes/OCF/Lean/YiBCNeg.lagda.md` | 183 / 131 | 0 | 不读记号，导入闭包 0 |
| `probes/OCF/Lean/YiBCReach.lagda.md` | 167 / 108 | 0 | 不读记号，导入闭包 0 |
| `probes/OCF/Lean/YiBCSync.lagda.md` | 63 / 44 | 0 | 验收文件，导入闭包含记号（1） |

- 冷编时删掉自己的 `.agdai`，按依赖序逐个编，每个日志只有自己模块的 `Checking` 行。
- 禁用构造与本机路径检索为 0。
- 临时文件在 `<实验目录>/work/YiBC/`：`YiBC0.agda`（第 0 步）、`YiBC1.agda`（reach 试验）、`YiBC2.agda`（oᶻ、oᴱ 两个实例），都退出 0。

#### 3. 定理表

档位全部是编译定理或编译否定，形状档。

**YiBCCover**
- `full-rbO : (a b : L) (ra : Rb a) (oa : Ok a) (ob : OkO a b) → Full a ra → Full (a ⊕ b) (rbO a b ra oa ob)`
  白话：`rbO` 保持 "每个 Ω 结点都有证据"。
- `full-tw : (n : ℕ) → Full (tw n) (rb-tw n)`
  白话：塔的每一项证据都满。
- `full-↑ : (a k : L) (ra : Rb a) (oa : Ok a) (ok : Ok k) (v : k ≤ a) (t : Tr k) → Full a ra → Full (a ⊕ ↑ k t) (rb↑ a k ra oa ok v t)`
  白话：任意树读回的偏移都带满证据。
- `top-s : proj₁ rbₛ ≡ just Sₛ`，`floor-s : floor Sₛ ≡ tw 1`
  白话：同步对象顶上的证据存在，地板是 `tw 1`。
- `full-sync : Full ℓₛ rbₛ`；`full-child : ∀ c → Full (a₁ c) (proj₂ rbₛ c)`
  白话：同步对象和它的每个孩子证据都满。
- `Chain.full-chain : ∀ m → Full (a₁ (chain m)) (proj₂ rbₛ (chain m))`；`Sync.full-chainᴮ`（同形）
  白话：真实链孩子证据满。
- `Sync.top-idle : BS.ψ ℓₛ o rb⁻ B zero (z≤ ℓₛ) β (proj₁ (Ωt ℓₛ)) ≡ Fdᴮ`；`top-idle-feed`
  白话：顶上的证据换成 `nothing`，结果不变。
- `kl-shape : (n : ℕ) → kl (suc n) ≡ nd (sΩ (tw n)) (klc n)`；`full-kl : (n : ℕ) → Full (kl n) (rb-kl n)`；`full-kl-child : (n : ℕ) (c : Tr (tw n)) → Full (klc n c) (proj₂ (rb-kl (suc n)) c)`
  白话：各站与任意链点孩子证据都满。
- `split⊑ : (a b : L) (ob : OkO a b) {j : L} (v : j ≤ a ⊕ b) → IsInj₂ (split a b ob v) → j ⊑ a ⊕ b`
  白话：`split` 走 `inj₂` 时，路径不经下标层。
- `rb-row : ∀ {k h} (r : (c : Tr k) → Rb (h c)) (S : Schema k h) j c′ (v : j ≤ h c′) → IsInj₂ (route S j c′ v) → Ok j → floor S ≤ j → (c : Tr k) → Rb (j ⊕ offsets S c)`；`full-row`（同前提，得出 `Full`）
  白话：`seen` 重建层的证据可以由外层证据降下来构造。前提可满足，实例是 `YiBCReach` 那一格。

**YiBCNeg**
- `noS : Schema one hZ → ⊥`，`ok-Z : Ok Z`
  白话：合法层号 Z 上没有公共地板。
- `no-uniform : ((ℓ : L) → Ok ℓ → Σ (Rb ℓ) (Full ℓ)) → ⊥`
  白话：从合法性推不出满证据。
- `no-sync : ((a : Tr zero → L) → Ok (nd (sΩ zero) a) → Σ (Rb (nd (sΩ zero) a)) (Full (nd (sΩ zero) a))) → ⊥`
  白话：变量 a 的同步对象上给不出满证据。
- `read-not-up : (ℓ : L) (d : Read) → IsUp (proj₁ (read ℓ d)) → ⊥`
  白话：码读出的树顶不是嵌入。
- `emb-up : (ℓ : L) (o : Ok ℓ) {k : L} (w : k ≤ ℓ) (y : Tr⁺ k) → Step w → IsUp (proj₁ (emb ℓ o w y))`
  白话：沿非平凡路径嵌入的树，顶是嵌入。
- `emb∉read`；`∉dom : ∀ {k h} (S : Schema k h) c (y : Tr (h c)) → IsUp y → Domain S c y → ⊥`
  白话：嵌入的块不在码域里。

**YiBCReach**（ω 代替链点）
- `G1 : G 1 ≡ nd (sΩ zero) H₁`，`H₁0 : H₁ zero ≡ nd sS (λ _ → G 0)`
  白话：给出这一格要用的层号形状。
- `way-row : (o : Ok ℓω) (r : Rb ℓω) (B : Base ℓω) (β : Tr⁺ (G 0)) → BS.ψ ℓω o r B (G 0) w₀ β x₀ ≡ BS.ψ (G 1) (proj₂ o 1) (proj₂ r 1) (λ i u → B i (inc 1 u)) (G 0) (inc zero (inc tt self)) β (proj₁ (emb (G 1) (proj₂ o 1) (self ∙ proj₁ o 0) (Ωt (G 0))))`
  白话：对任意 Ok，孩子 1 的底把孩子 0 的块嵌进孩子 1。
- `rebase-row : (o′ : Ok (G 1)) (B′ : Base (G 1)) (β : Tr⁺ (G 0)) (c : Tr zero) (y : Tr (H₁ c)) (e : H₁ c ⊢ zero ◃ y) → BS.ψ (G 1) o′ (proj₂ rω 1) B′ (G 0) (inc zero (inc tt self)) β (up zero c y e) ≡ seen S₁ (G 0) (downOk (H₁ zero) (proj₂ o′ zero) (G 0) (inc tt self)) (lift (tw 1) one) β c ⊞ BS.ψ (H₁ c) (proj₂ o′ c) (proj₂ (proj₂ rω 1) c) (B₀ (H₁ c)) zero (z≤ (H₁ c)) (Ωt zero) y`
  白话：对任意块，换基行在这里走 `seen` 一支。
- `reach : (B : Base ℓω) (β : Tr⁺ (G 0)) → BS.ψ ℓω oω rω B (G 0) w₀ β x₀ ≡ seen S₁ (G 0) (downOk (H₁ zero) o₁ (G 0) (inc tt self)) (lift (tw 1) one) β zero ⊞ BS.ψ (H₁ zero) o₁ (proj₂ (proj₂ rω 1) zero) (B₀ (H₁ zero)) zero (z≤ (H₁ zero)) (Ωt zero) yₑ`
  白话：在 `oₛ` 下，到达 `seen` 的块是 `yₑ`。
- `yₑ∉ : Domain S₁ zero yₑ → ⊥`
  白话：这个块不在码域里。
- `R1`、`R2`（用 `kp-z`）、`R2₀`、`R3`、`start`
  白话：`Ωt (a₁ ω)` 的第二个部分和朝第 0 层折时，`reach` 左边就是孩子 1 第 0 支里那条回灌链的起点。

**YiBCSync**（验收文件）
- `a₁-eq : RK.a₁ ≡ SY.a₁`；`feed-eq`；`chain-eq : ∀ m → RK.Real.chain o B m ≡ SY.Sync.chain SY.a₁ o B β m`
  白话：`YiRKChain` 的副本与原定义逐字相等。
- `full-chainᴱ : ∀ m → Full (SY.a₁ (SY.Sᴱ.chain m)) (proj₂ rbₛ (SY.Sᴱ.chain m))`；`full-chainᶻ`
  白话：`YiSYReduce` 两个实例的现行链，每个点的孩子证据都满。
- `reachᴱ`、`reachᶻ`
  白话：`reach` 在 `oᴱ`、`oᶻ` 下同形，块仍是 `yₑ`。

#### 4. 第一个障碍

- **证据一侧：** 在读回域上没有障碍。在变量 a 的域上，障碍是 `YiBCNeg.noS`：合法性给不出公共地板（缺 `shape` 与 `index-floor` 两个字段）。这是量化域太宽，属于定义域的选择，不是数学上挡住。
- **块一侧：** 障碍是 `YiBCReach.yₑ∉`：现在的 `Read` 文法没有嵌入码。我的判断是工程上的缺口，`yₑ` 由码生成，没有碰到分支类型的反变。真正的反变情形在同步计算里是否出现，未查。
- **`a₁ (chain m)` 本身：** 链点的分量未知，`chain₁` 是 opaque，所以只能用 ω 代替。这是工程上的限制。

#### 5. 偏离与事故，未读的东西

- 第一次编译套了 `/usr/bin/time -l`，被沙箱的 sysctl 拦下，退出码 1 来自 time，不来自 agda。去掉之后重跑，退出 0。所有编译都在几秒内完成，没有撞堆；因为 time 被拦，没有量峰值内存。
- 一处偏离：块到达换基行这一格是用 ω 代替真实链点得出的，与 `YiRKCell` 的做法相同。
- 没读，只凭简报转述：`Reports-2026-11-16/YiVA.md`、`AuditD.md`。
- 没读：`EBOHandbook` 4.2、4.6 节，以及 Bedrock 性能手册。本路没有出现性能问题。
- 读过：`IdeaLedger` 的 V149、V158、V290、V293 四条，`Review18.md` 第 80 到 129 行，以及 YiBS*、YiRK*、YiSY*、YiRW* 的源码。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：换基证据对真实链孩子的覆盖（前缀 YiBC，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另三路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者已关闭现行折叠上同步对象那一步链步（`YiKTSlot.Cand` 及其变体，台账 V287），依据是两份先读定义的 Fable 5.2 封存审核（留档 `probes/Survey/Reports-2026-11-16/YiVA.md`、`AuditD.md`）。**主线定义不动**；改树、折叠、合法性只在新文件里做候选。
- 第七十六批作者选四路（选项原文）："换基替身的值 (Recommended), 换基的律接进整体接口 (Recommended), 换基证据对真实链孩子的覆盖 (Recommended), 比较表的对角条目不判等"。前缀 `YiSV`（Fable 5.2）、`YiBL`（Opus 5.5）、`YiBC`（Opus 5.5）、`YiDG`（Opus 5.5），互不导入。
- **第七十五批三路（主审冷编复核过）指向同一处**：折叠在被问到的孩子对上要字面证据。
  - `YiRKCell`（不读记号）：朝目标孩子 d（取 ω）的层号折塔第 1 项的 Ω 树时，顶结点在四种折叠里都保留（`top-ω`、`top₁` 到 `top₃`），一切分支 c 都被问到；三种写法的行都不看 c 是否字面延伸 d（`w1`、`w2`、`w3`）。现行行把孩子树折到第 0 层再加上（`w1`、`ι-free`）；上折回退在原材料任何深度的槽位走链（`w2-never`）；**换基**不用原材料，在 `h₁ d ⊕ ↑c` 上重建 Ω 树沿 `lift` 朝原目标折（`w3`、`w3′`），目标层副本的槽位保留（`keep-lift`、`keep-ω`），换基层号没有 Ω 形状子层号（`noΩ-reb`），后继孩子处替身树的顶走链（`seen-s`）。V50 按 "孩子对" 的提法为否：ω 与偶数列 ω 之间两个方向都没有字面路径（`no-ωᵉ`）；字面延伸给出路径（`ext-path`，`Ext d c = zero ⊢ d ◃ c`）。`YiRKChain`：chain 1 副本顶是 ℕ 极限（`Real.L₁`），链孩子层号是 ℕ 极限形状（`Real.child-L`）；副本照 `YiSYReduce`、`YiSYDesc` 重写，与原定义的相等未编译。
  - `YiCTCall`（不读记号）：候选 (C) 在 `cand₂` 实际路径上丢保留的那一格，槽位与目标同在孩子 3 下（对角），对一切来源表走链（`cell`、`org-P₁`）；只给比较表加 (3,3) 条目就保留（`cf-pos`，有限测试）。
  - `YiFIIface`（不读记号）：对折叠参数化的抽象充分性：保留律 `KeepLaw`、回退律 `FallLaw`、参照出口 `Out` ⇒ 每个状态上保持（`Suff.keepAll`）、LowKeep（`sys→low`）；`YiFIFold.lowᴷ`（上折回退的候选上只剩 `Out`，其结点一条 `Out.nodeE` 就是 V50）；`keepOf`（字面路径保留）；配对否定 `YiFINeg.kp-not-flr`、`kp-not-lit`、`kpᴬ-violates`、`main-nf`、`fb-nf`。
- **换基已有的原型**（`probes/OCF/Lean/`，都是候选、不替换主线；先读文首）：`YiBSBase`（`split : (a b : L) → OkO a b → ∀ {j} → j ≤ (a ⊕ b) → (j ≤ a) ⊎ (a ≤ j)`；`rbO : (a b : L) → Rb a → Ok a → OkO a b → Rb (a ⊕ b)`；`rb-tw : (n : ℕ) → Rb (tw n)`；`seen : ∀ {k h} (S : Schema k h) (j : L) → Ok j → floor S ≤ j → Tr⁺ j → Tr k → Tr⁺ j`），`YiBSFold`（换基折叠 `BS.ψ`，"该行的换基部分固定重建 Ω 树，原孩子树只进入低层尾项"），`YiBSRead`（`Read` 码），`YiBSReadNeg`、`YiBSUpNeg`（字面读回的两条否定，不否定值），`YiBSClean`、`YiBSInner`（干净对象上的闭项与内层整行），`YiBSFam`、`YiBSCrit`（有限读回层的保持；`finite-crit`、`finite-shift` 只到数字孩子），`YiBSAccept`（首链点 ψ₁(Ω₃) 关系，输出 ψ₀(Ω₃) 下界）；更早的 `YiRBSib`、`YiRBCrit`、`YiRBFam`。台账 V149（换基；"对任意一块不可写（纸面判断，方向反变）"，出路是改块的嵌入字段为族或收量化域）、V158、V290、V293。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
换基折叠要证据：`YiBSBase.rbO` 只对形如 `a ⊕ b` 且带 `OkO a b` 的层号给，`rb-tw` 对塔各项给。同步对象的层号是 `nd (sΩ zero) a`（`YiSYReduce`），真实链孩子是 `a (chain m)`，`chain m` 是回灌输出（第 0 层的大树，`YiRKChain.Real.L₁`：顶是 ℕ 极限）。问：换基的证据能不能覆盖同步对象与真实链孩子；V149 记过的 "对任意一块不可写（纸面判断，方向反变）" 在这里会不会出现。

#### 要做的（按序）
0. **最小检查**：列出换基折叠在同步对象上一路要用到的证据（`Rb`、`OkO`、`Schema`、`floor S ≤ j` 等），逐项写出它们在 `nd (sΩ zero) a` 与 `a (chain m)` 上的类型。先在临时文件里对 `a` 的一个孩子（变量）编译。不成立就停下回报。
1. **能给的就构造**（仿 `rbO`、`rb-tw`、`OkO↑`、`OkO⊕`），对同步对象与真实链孩子（变量 `chain m`，或 `YiRKChain` 的副本；副本与原定义的相等能证就证）。
2. **给不出的写成编译否定或精确的缺口**：说明缺的是哪个字段、为什么（例如 Ω 结点分支类型的反变），以及出路是改块（嵌入字段改成族）还是收量化域（规范读回域）；两种出路各要改什么，估代价。改块是定义改动，只写清，不做。
3. 交覆盖表：层号 × 证据 → 有 / 无 / 条件。

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


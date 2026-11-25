# 辅助系统的底取目标层起点（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 07:15 至 07:28 |
| 工具调用 / agda 编译 (粗数) | 39 / 8 |
| token (usage 字段，按消息去重) | 输出 67857；新写入缓存的输入 237520；读缓存的输入 4949266；其余输入 62 |
| 写过的仓库文件 | `YiABCell.lagda.md`, `YiABCost.lagda.md` |
| 文件前缀 | `YiAB` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0，两件不读记号的导入闭包干净；候选变体（替身的底在目标层及以下取外层折叠的值）过停机检查、单调（ψ、mono）；塔第 1 项那一格上链点吸收左项（z1、zS、¬free），较弱链形状对一切前缀成立（weak-tw1ᵛ 条件，三处实例无前提）；槽位层高于目标层处起点仍是 Ω 树（above-start、top-free）；朝第 0 层系统的链的步未证 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b81/YiAB.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiAB 回报：辅助系统的底取目标层起点（候选定义改动，Fable 5.2）

#### 1. 判决

**对纲领与目标意味着什么。** 变体是候选折叠的定义改动，只在新文件里，`YiBSFold` 与主线都没动，进不进主线由作者定。它无公理，过停机检查，合法性仍是类型，`mono` 保持第一位置；不比较孩子，不引入下标上的判定。它在塔第 1 项那一格把 YiWC 的判断变成了编译事实：替身的链点吸收左项，较弱链形状对一切前缀 P 成立，条件是外层折叠在 x 上朝目标层的保持（`mb`）。它没有解决两件事：槽位层严格高于目标层的结点，链的起点仍是 Ω 树；`YiWCWire.StepW`（朝第 0 层的系统）本身没有证。没有新的值定理，终点 ψ₀(Λ) 的状态不变。改动的动机来自验收一侧（参照的 γ 链要求链点支配 ψ_κ(P + ·)），属 "第 4 层逼出"，翻译账单列在下面。

**各步到哪一步。**
- 第 0 步（设计与先验检查）：完成，编译通过。
  - 取哪一个：替身的底 `subB` 在目标层 j 及以下的层 i，取外层折叠在左项 x 上朝 i 的值，即底族经目标孩子 c′ 的那一项 `ψ ℓ o r B i (inc c′ (u′ ∙ v)) (B i (inc c′ (u′ ∙ v))) x`（与孩子回退行 `dn` 同一写法）。严格高于 j 的层仍取 Ω 树。
  - 没有取 β′ 的理由：β′ 只在 j 层有值，底要给 j 以下每一层一棵树；只在 "i 字面等于 j" 处用 β′ 要按层号字面相等派发，先验检查第三条不允许。
  - 先验检查三条：目标经指定孩子 c′，是路径本身带的那个孩子，没有新的孩子比较；孩子下标类型上没有新的证据函数；没有按存在性保留，派发只有对路径的 `split`（读路径字面形状）。不落在 `obs→dec` 一族与 `YiDGDiag.ColW.wdecα` 的前提上（判断，依据是逐条读这几条的陈述；没有为此写探针）。
- 第 1 步（形状）：完成。那一格上第 1 个链点是 `Dˣ j₁ self` 的后继（`z1`，refl），x 取零树与取 1 时链点不同（`¬free`），对照 `zᴬ-free`。
- 第 2 步（链的步）：塔第 1 项那一格完成，是条件定理（`stepᵛ`、`weak-tw1ᵛ`，对一切 P）；前提 `mb` 在 P 空、P = 1、P = Ω₂ 三处实填。一般情形未走通，第一个挡住的引理见第 4 节。
- 第 3 步（代价）：清单见下，部分已编译。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 变体过停机检查，类型即合法性，`mono` 成立 | `YiABFold.ψ`、`mono` | 编译定理 |
| 那一格上变体的换基行逐字是替身状态 `sV` 的像加尾项 | `YiABCell.Tw1V.row-is` | 编译定理 |
| 链点吸收左项：第 1 个链点是外层值的后继；之后是以它为底值的第 1 层自身折叠的后继 | `Tw1V.z1`、`zS` | 编译定理 |
| 链点依赖 x（对照 `zᴬ-free`） | `¬free` | 编译定理 |
| 那一格上较弱链形状对一切 P 成立，前提是起点对着 ψ_1(P) | `Tw1V.Step.weak-tw1ᵛ`、`stepᵛ` | 编译定理（条件） |
| 前提可满足：P 空、P = 1、P = Ω₂（底 `B₀`） | `Inst.mb-nil`、`mb-one`、`InstΩ.mb-Ω₂` | 编译定理 |
| 原替身（底 `B₀`）在 P = Ω₂ 时较弱链形状不成立 | — | 判断（纸面：原链的上确界是 ψ_1(Ω₂)，参照链第 1 项是 ψ_1(Ω₂ + Ω₁)）；没有编译的否定 |
| 替身里槽位层严格高于 j 的结点，起点仍是 Ω 树，与外层无关 | `above-start`、`top-free` | 编译定理 |
| 那些结点上链的步不成立 | — | 判断，未编译 |
| `YiWCWire.StepW`（朝第 0 层的系统）在变体上是否可证 | — | 未走通；判断：它的障碍是不变式不约束槽位层的底（审查 F 路 G1、G2），不由替身的底解除 |
| 换基律、底值不高于像、`Car` 一族的承载结论对变体成立 | `YiABCost` | 编译定理 |
| 变体与 `YiBSFold` 的闭项是否相同 | 第 0 项 `closed0` | 第 0 项编译；第 1 项起未检查（不是 refl） |

**代价清单（第 3 步）**
- 照样成立（编译）：
  - `YiBLFold.Aux`（辅助系统的 `keepᴬ`、`fallᴬ`、`monoᴬ`、`ev-cp`、`top-noEv`）对任意底陈述，原样可用；那一格直接用了 `YiBAEbo.Tw1Neg` 的 `chᴬ`、`sysᴬ`。
  - `YiBLFold.Main` 的 `row-reb`、`rebᴮ′` 在变体上有对应（`row-rebᵛ`、`rebᵛ′`）。
  - `YiSVMono.Mono.Car` 对一切不低于 Ω 树的底量化，所以 `YiSV*`、`YiZS*` 里经 `Car` 得到的承载结论对变体的替身成立，前提是外层的底不低于各层 Ω 树（`seenᵛ-car`、`sub-ok`、`D-ok`）。
- 要重新实例化、没有做（判断：机械工作）：以 `foldᴮ` 为参数的分级实例（`gradedᴮ`、`gradedᴱ`）及其上的 `YiWRZero`、`YiWREnd`、`YiWCWire`、`YiQDFold.lowᴰ`、`YiXTReb`、`YiSOLow`、`YiSOEnd`。直接导入 `YiBSFold` 的模块有 28 个。`YiQDFold` 的域 `KD` 按文首只看 `kp` 的字面结果，与换基行的底无关（判断，只读了文首）。
- 不能直接搬的：凡陈述里逐字写着 `seen S j oj u β c`（底 `B₀`）而不经 `Car` 的定理，如 `YiBSRead` 的 "Ω 行与 seen 定义性相等"、`YiSVCell.cell`、`YiSVOmega` 的具体实例。外层在零树、默认底上时替身的底逐点等于 `B₀`（`sub-B₀`）；但逐点相等不给出两个替身的像相等，那要对底的函数外延，没有做。
- 一处小的不整齐：j 层那一项的路径是 `inc c′ (self ∙ v)`，与 `inc c′ v` 只是命题相等（`∙` 对第二个参数递归）；v 是 `self` 时定义相等，那一格就是这种情形。

**翻译账**
- 新定义行：`Low`、`subB`（共 4 行），`seenᵛ`、`seen-stepᵛ`（各多一个底的参数），换基行与 `mono` 里各多一行交出 `Low`。其余 `ψ`、`mono` 逐字搬自 `YiBSFold`。
- 哪些来自记号的规则：没有一行的字段形状读自基本列；`subB` 的形状是折叠自己孩子回退行的写法。
- 第 4 层逼出：这次改动的动机是验收（参照 γ 链要链点支配 ψ_κ(P + ·)）。树侧能说的理由只有一条编译事实：原写法下替身的链与左项 x 无关（`zᴬ-free`），x 只经底值 β′ 进入。这是不是 "定义本身的缺陷"，由作者定。
- 新增脚手架：无。没有新的自身折叠保持引理，`Self₁.LF` 直接导入。
- 加深还是提供信息（判断）：提供信息的一面是把 "吸收前缀" 写成了对起点的一条条件定理，并划出不吸收的地方（`top-free`）；没有用 `Lab` 验收。

#### 2. 文件表（都在 `<仓库>/probes/OCF/Lean/`）

| 文件 | 总行 / 代码行 | 冷编退出码 | 备注 |
|---|---|---|---|
| `YiABFold.lagda.md` | 145 / 116 | 0 | 不读记号；`importclosure.py` 退出 0，禁用表命中 0 |
| `YiABCell.lagda.md` | 219 / 127 | 0 | 验收（读记号） |
| `YiABCost.lagda.md` | 118 / 72 | 0 | 不读记号；`importclosure.py` 退出 0，禁用表命中 0 |

各文件删自己的 `.agdai` 后冷编（6G），日志里只有自己模块的 `Checking` 行。禁用构造与本机路径检索为 0。日志在 `<实验目录>/work/YiAB/`（`*.cold.log`）。

#### 3. 定理表（都是编译定理；标 "条件" 的带前提）

**YiABFold**
- `subB : (j b : L) → OkO j b → Low j → Base (j ⊕ b)`，`subB j b ob D i q = cW (split j b ob q) (D i) (λ _ → Ωt i)`；`Low j = (i : L) → i ≤ j → Tr⁺ i`。白话：替身的底，j 以下取外层交来的值，以上取 Ω 树。
- `seenᵛ : ∀ {k h} (S : Schema k h) (j : L) → Ok j → floor S ≤ j → Low j → Tr⁺ j → Tr k → Tr⁺ j`。白话：`seen` 多一个底的参数。
- `ψ : (ℓ : L) → Ok ℓ → Rb ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j` 与 `mono : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ proj₁ (ψ ℓ o r B j w β x) ◃ proj₁ (ψ ℓ o r B j w β y)`。白话：变体折叠与单调；只有换基行不同。

**YiABCell**（`module Tw1V (B : Base (tw 1)) (β : Tr⁺ j₁) (x : Tr (tw 1))`；`Dˣ i u′ = V.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B i (inc (suc zero) u′) (B i (inc (suc zero) u′)) x`，`start = Dˣ j₁ self`，`zⱽ = proj₁ (chᴬ sV pᴬ gᴬ tt neV)`）
- `row-is : ∀ y e → V.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B j₁ (inc (suc zero) self) β (up x (suc zero) y e) ≡ Aux.Φᴬ j₁ sV (proj₁ (Ωt (j₁ ⊕ ↑ zero (suc zero)))) ⊞ V.ψ (h₁ (suc zero)) (proj₂ (Ok-tw 1) (suc zero)) (rcₙ 0 (suc zero)) (B₀ _) zero (z≤ _) (Ωt zero) y`。白话：`sV` 确实是变体换基行交给辅助系统的状态。
- `z1 : zⱽ 1 ≡ proj₁ (next⁺ start)`；`zS : ∀ m → zⱽ (suc m) ≡ proj₁ (next⁺ (Fˢ (zⱽ m)))`。白话：链点从外层值起步。
- `Step.stepᵛ : ∀ k m → GR.R j₁ (γ k) (zⱽ m) → GR.R j₁ (γ (suc k)) (zⱽ (suc m))`（条件；`module Step (P : E.T) (mb : GR.R j₁ (E.ψ 𝟙 P ∷ []) (proj₁ start))`，`γ = E.γT (P ++ Ω₂) 𝟙`）。白话：这一格上链的步，下标挪 1。
- `Step.chainᵛ : ∀ k → GR.R j₁ (γ k) (zⱽ (suc k))`（条件）。
- `Step.weak-tw1ᵛ : WeakAt P`，其中 `WeakAt P = RefChainʳ sysᴬ sV (𝟙 , P) pᴬ gᴬ Ω₂ (chᴬ sV pᴬ gᴬ tt neV)`（条件）。白话：前缀 P 任意时较弱链形状成立。
- `Step.Node.seen-node : GR.R j₁ (E.ψ 𝟙 (P ++ Ω₂) ∷ []) (proj₁ (Aux.Φᴬ j₁ sV (Ω pᴬ gᴬ)))`（条件；另要 `mβ : GR.R j₁ (E.ψ 𝟙 P′ ∷ []) (proj₁ β′)` 与 `same : ∀ a → E.ψ 𝟙 (P′ ++ a) ∷ [] ≡ E.ψ 𝟙 (P ++ a) ∷ []`）。白话：替身的像对着 ψ_1(P + Ω₂)。
- `¬free : (β : Tr⁺ j₁) → Tw1V.zⱽ (B₀ (tw 1)) β zero 1 ≡ Tw1V.zⱽ (B₀ (tw 1)) β (suc zero) 1 → ⊥`。白话：链点随 x 变。
- `Inst.mb-nil : GR.R j₁ (E.ψ 𝟙 [] ∷ []) (proj₁ V0.start)`；`Inst.mb-one : GR.R j₁ (E.ψ 𝟙 𝟙 ∷ []) (proj₁ V1.start)`；`InstΩ.mb-Ω₂ : GR.R j₁ (E.ψ 𝟙 Ω₂ ∷ []) (proj₁ V2.start)`（`V0`、`V1`、`V2` 是 x 取 `zero`、`suc zero`、`x₂ = proj₁ (upz (suc zero) (Ωt j₁))`，底 `B₀ (tw 1)`）。
- `Inst.weak-nil : V0.WeakAt []`；`Inst.weak-one : V1.WeakAt 𝟙`；`InstΩ.weak-Ω₂ : V2.WeakAt Ω₂`。白话：三处无前提的实例。
- `leaf-start : ∀ j s (ob : OkO j (nd s (λ _ → zero))) (D : Low j) (c : Ch s) → subB j (nd s (λ _ → zero)) ob D j (inc c self) ≡ D j self`
- `above-start : ∀ j s h (ob : OkO j (nd s h)) (D : Low j) → subB j (nd s h) ob D (j ⊕ nd s h) self ≡ Ωt (j ⊕ nd s h)`
- `top-free : ∀ j s s′ h′ (ob : OkO j (nd s (λ _ → nd s′ h′))) (D : Low j) (c : Ch s) → subB j (nd s (λ _ → nd s′ h′)) ob D (j ⊕ nd s′ h′) (inc c self) ≡ Ωt (j ⊕ nd s′ h′)`。白话：偏移没取尽的层上，起点是 Ω 树，与外层无关。

**YiABCost**（`module Mainᵛ`，参数同 `YiBLFold.Main`；`Dᵛ x i u′ = V.ψ ℓ o r B i (inc c′ (u′ ∙ v)) (B i (inc c′ (u′ ∙ v))) x`）
- `ψ-⊵ᵛ : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ) → proj₁ β ⊴ proj₁ (V.ψ ℓ o r B j w β x)`
- `sub-ok : (j b : L) (ob : OkO j b) (D : Low j) → (∀ i u′ → proj₁ (Ωt i) ⊴ proj₁ (D i u′)) → OKB (subB j b ob D)`
- `sub-B₀ : (j b : L) (ob : OkO j b) (i : L) (q : i ≤ (j ⊕ b)) → subB j b ob (λ i′ _ → Ωt i′) i q ≡ B₀ (j ⊕ b) i q`
- `Mainᵛ.row-rebᵛ : ∀ β x c y e → V.ψ ℓ o r B j w β (up x c y e) ≡ seenᵛ S j oj u (Dᵛ x) (V.ψ ℓ o r B j w β x) c ⊞ V.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y`
- `Mainᵛ.rebᵛ′ : ∀ β c x (y : ChTᵍ ℓ c) → proj₁ (Φᴬ (Srᵛ β c x) (proj₁ (Ωt (j ⊕ offsets S c)))) ⊴ᵗ proj₁ (V.ψ ℓ o r B j w β (upᵍ x c y))`。白话：替身的像低于行的输出（换基律）。
- `Mainᵛ.D-ok : OKB B → ∀ x i u′ → proj₁ (Ωt i) ⊴ proj₁ (Dᵛ x i u′)`
- `Mainᵛ.seenᵛ-car : OKB B → ∀ β x c → Car (offsets S c) → P (proj₁ (V.ψ ℓ o r B j w β x)) → Q (proj₁ (seenᵛ S j oj u (Dᵛ x) (V.ψ ℓ o r B j w β x) c))`（P、Q 及其三条封闭性是模块参数，同 `YiSVMono.Mono`）。白话：`Car` 的承载结论搬到变体。
- `closed0 : V.closed 0 ≡ BS.closed 0`

#### 4. 第一个障碍

**一般情形的链的步，挡在两条引理上，都是数学上的，不是工程上的。**

1. **高于目标层的槽位层没有起点。** 替身层号 `j ⊕ b` 里槽位层是 `j ⊕ b′`（b′ 是没取尽的偏移）时，要的是 `R (j ⊕ b′) (ψ_κ(P)) (起点)`，κ 是该层的读数。外层折叠只朝 `≤ ℓ` 的层折，`j ⊕ b′` 到 ℓ 没有现成的字面路径，所以变体在那里只能交 Ω 树（`top-free`，编译）。P 非空时 Ω 树对不上 ψ_κ(P)（判断，没有编译的否定；R 在 Ω 树上的反演没有做）。那一格之所以通，是因为孩子 1 的偏移只有一层，槽位层就是 j。
   - 候选（判断，未写）：起点取外层折叠经孩子 `c′ + c″`（↑c″ = b′）朝 `j ⊕ b′` 的值。这要 `j ⊕ b′ ≤ h (c′ + c″)` 的字面路径，与 `YiRBSib.Rb` 里的兄弟路径证据同类；写之前要再过一遍先验检查。
2. **前提 `mb` 的一般形式。** 一般的 x 上 `mb` 是主系统朝目标层、沿路径 `inc c′ (u′ ∙ v)` 的保持。这条路径不是 `posW` 形，落在审查 F 路 G6（"证明内部要一般路径上的保持"）里；本路没有证，只在三个具体的 x 上实填。

**`YiWCWire.StepW` 本身**：陈述在朝第 0 层的系统上，链点是 `slotFold`（底取 `B (at a p)`）。变体不改这条链的写法，只改它经过换基行时替身内部的链。它在 `Inv₀`、`Inv₁` 下的障碍是不变式不约束槽位层的底，与替身的底无关（判断）。要在变体上陈述它，先得把 `YiWRZero`、`YiWREnd`、`YiWCWire` 对变体重新实例化，本路没有做。

#### 5. 偏离、事故、未读部分

**偏离。**
- 简报例举 "外层折叠此刻的 β′"；我取的是底族的那一项（理由见第 0 步）。两者在那一格上都从 x 的折叠起步，区别是起点用 `B j₁ …` 还是 β；前提 `mb` 因此说的是底族那一项，不是 β′。
- 第 2 步 "再一般" 没有做成定理，只给了挡住的引理与一条编译的形状事实。
- `YiABCell` 里 `hd`、`Ω≢lim` 是为 `¬free` 写的两个小工具，没有检索是否已有同名引理。

**事故。**
- `YiABCell` 一次退出 42（`nodeʳ` 不在作用域，补 `using` 后通过）。
- `YiABCost` 一次退出 42：`closed1 : V.closed 1 ≡ BS.closed 1` 不是 refl，删去该条并在文首改写。
- 没有 251、124。单次编译最长约 17 秒，没有测堆峰值。
- 第一个文件（`YiABFold`）在开工后约 20 分钟内编译通过（估计，没有记时间戳）。
- `importclosure.py` 各跑了一次，没有核对它内部是否另起了 agda 进程。

**没有读、只凭转述或文首引用的。**
- `YiSOLow`、`YiSOEnd`、`YiSOUp`、`YiSOTw1`、`YiSDRead`、`YiGLDom`、`YiQDFold`、`YiUFDom`、`YiBCCover`、`YiXCIface` 一族：只读了文首或没有打开；关于 `NodeMis`、`RebRow`、`RootBd`、`KD` 的说法来自简报与文首。
- `YiAbsObs`、`YiDGDiag`：只读了文首与 `obs→dec`、`viaE→dec`、`full→dec`、`wdecα` 的签名。
- `YiSVCell`、`YiSVOmega`、`YiSVStep`、`YiSVRed`、`YiZSTower`、`YiBSRead`、`YiBSClean`、`YiBSCrit`、`YiUFFold`：只读了文首；"经 `Car` 的结论可搬" 依据的是 `YiSVMono` 里 `Car`、`seen-car` 的定义体。
- `YiXTReb` 只读了 `chᴬ` 一段；`YiBAEbo` 读了文首、`KeepAt`、`Tw1Neg`、`AuxNode`。
- EBOHandbook 4.2、4.6 节与 Bedrock 性能手册没有打开（本路没有遇到性能问题）。
- 审查 F 路、YiWC 的结论取自留档 `probes/Survey/Reports-2026-11-16/AuditF.md`、`YiWC.md`，附件 `.agda` 没有重编。
- "原替身在 P = Ω₂ 时不成立" 是纸面的序数估计，没有编译。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：辅助系统的底取目标层起点（候选定义改动）（前缀 YiAB，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同批另三路与你互不导入。**这是候选折叠的定义改动，只在新文件里做，进主线由作者定**（AGENTS "第 4 层不反过来改前 3 层"，理由来自树侧，翻译账单列）。

#### 作者的决定与背景（2026-11-17）
- 作者要求（原文）："更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。作者选项原文："统一收量化域的检验 (Recommended), 合并同类接口 (Recommended), 出口条件与核心证明的耦合, 辅助系统的底取目标层起点（改候选定义）"。前缀 `YiQV`（Fable 5.2）、`YiMI`（Opus 5.5）、`YiXC`（Opus 5.5）、`YiAB`（Fable 5.2），互不导入。**主线定义不动**；换基折叠 `YiBSFold` 是候选。
- **现状（主审复核过，都在 `probes/OCF/Lean/`）**：换基候选上的终点条件定理有两版：`YiWREnd.Wire.ebo-endˢ`（前提 `LowSlot` 与出口条件；两个具体不变式下 `LowSlot` 被审查 F 路编译否定，加强不变式后接线合上，见留档 `probes/Survey/Reports-2026-11-16/AuditF.md` 与附件 `attachments/AuditF-*.txt`），以及不经原接线、带域的 `YiSOEnd.End.ebo-endᴬ`、`YiSOTw1.EndU.ebo-endᵁ`（前提：域 `Domˢ`、`NodeMis`、`RebRow`、`RootBd`、`RootIn`、`UpMis`，加出口条件）。`YiSOLow.Sys.Main.lowAll`、`YiSOUp.UpAll.upAll`：多目标系统里保留判定与参照一致的格对一切层号一次归纳证出。
- **剩下的义务（判断：都出自量化域太宽，第四、五次同形出现）**：`YiSOLow.Sys.NodeMis`（树走链而参照保持 Ω 余尾：审查 F 路 FCross 那一格、`YiXTIface.stuck` 的情形；树保留而参照坍缩：读法允许取空时出现）、`YiSOUp.UpMis`（上折同类一格）、`YiSOLow.Sys.RebRow`（换基行：路由落在地板之上时替身加第 0 层尾项，域取全体时判断为假；`YiSDRead.CellRaise` 未走通）、`YiSOEnd.RootBd`（塔第 2 项起根状态每个槽位每个读法上的 Leaf；全域 Leaf 在 Ω 形状上有否定 `YiLLLeafNeg.noLeafOk`）、`YiWCWire` 的 `StepW`（链的步：上下文前缀可以超出链的上确界）。出口条件 `YiHCRel.Exᴴ` 要求推导里每个向下封闭步 `mc` 两边是标准形、较大一边可数，与核心证明里 `mc` 的用法耦合（审查 F 路 G5）。
- 可用的读回域工具：`YiGLDom`（`Dom`、`dom-top`、`leafᴰ`、`liftᴰ`、`dom-keel`；`rd-not-dom`）、`YiQDFold`（树的域 `KD`、`kd-dw`、`Ωt-in`/`Ωt-out`）、`YiUFDom.QDTw.Ωt-tw`、`YiBCCover`（证据在读回域上处处满）、`YiSDRead.sub-read`/`top-read`（读回形式）、`YiBAEbo.BelowE`（参照取 ψ_ν、条件 `KeepAt`）、`YiSOTw1.root-bd1`（塔第 1 项根状态无前提）。

#### 本路的问题
YiWC 判断（未编译）：换基替身的底取默认底 `B₀`（`YiBLFold.Main.Srᴮ`），所以替身的链点不吸收上下文前缀；依据 `YiWCTw1.zᴬ-free`（这一格的树链与主系统的底、左项无关）。若在目标层取起点（例如外层折叠此刻的 β′），链能吸收前缀，链的步 `StepW`（`YiWCWire`）可能变得可证。

#### 要做的（按序）
0. **设计与先验检查**：在新文件里写换基折叠的变体，替身的底与起点取目标层上外层折叠的值（说明取哪一个：β′、底族的哪一项）；查停机检查、合法性（类型）、`mono`；按 AGENTS "开新行前的先验检查" 对照 `YiAbsObs` 的 `obs→dec` 一族与 `YiDGDiag.ColW.wdecα`。不成立就停下回报。
1. **形状**：在 `YiWCTw1` 那一格上给编译事实：变体的链点是否吸收上下文前缀（对照 `zᴬ-free`）。
2. **链的步**：在变体上试证 `StepW` 的对应陈述（先塔第 1 项那一格，再一般），或给出第一个挡住的引理。
3. **代价**：变体是否破坏已证的东西（`YiBLFold` 的律、`YiQDFold` 的域、`YiSV*`/`YiZS*` 的值），列清单；翻译账。

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


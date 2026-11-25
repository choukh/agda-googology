# 换基替身的值（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 02:46 至 03:07 |
| 工具调用 / agda 编译 (粗数) | 35 / 9 |
| token (usage 字段，按消息去重) | 输出 115130；新写入缓存的输入 297424；读缓存的输入 6169342；其余输入 64 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `YiSV` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 5 件全部退出 0，禁用构造 0，两件不读记号的导入闭包干净；替身对偏移沿字面路径单调（YiSVMono.mono-path、seen-mono，不读记号）；目标孩子 ω 时，换基折叠下塔第 1 项 Ω 树的一切非零分支承载 ψ_ω(Ω_{ω+1})（seen-ω、branch-nz，实际证据）；顶结点承载 ψ_ω(Ω_{Ω₁}) 只归约到未证的后继一步 StepS（top-red），StepS 的结论在 η ≤ ω+1 处成立（step-low） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b76/YiSV.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiSV 回报：换基替身的值

#### 1. 判决

**对纲领与目标意味着什么。** 换基替身 `seen` 现在有了第一批无前提的值定理，而且树一侧用到的只有一条不读记号的事实：替身对偏移沿字面路径单调。目标孩子取 ω 时，替身在一切非零孩子处承载 ψ_ω(Ω_{ω+1})；c = ω+1 时这正是简报要的参照 ψ_d(Ω_c)。参照随 c 增长的那一族（ψ_ω(Ω_c)）与上确界没有做出来，只归约到一条未证的后继一步 `StepS`。主线定义没有动，记号只出现在验收文件里。

**各步到哪里。**

| 步 | 结果 | 档 |
|---|---|---|
| 0 最小检查 | c = d+1 = ω+1 成立：`step0` | 编译定理 |
| 1 `seen` 的值，d = ω | 一切非零 c（含一切字面延伸 ω 的 c）承载 ψ_ω(Ω_{ω+1})；一切 c 承载 ψ_ω(Ω_ω)。参照不随 c 增长 | 编译定理 |
| 1 一般非零 d | 写成目标层 j 上的接口 `Step`，结论 ψ_ν(Ω_{ν+1})；实例只有 ω 层与有限层 | 条件定理，两个实例已填 |
| 2 上确界 | 未走通。`top-red : StepS → 顶结点承载 ψ_ω(Ω_{Ω₁})`；`StepS` 未证，也没有否定 | 条件定理 |
| 3 chain 1 | 只有在变量上的陈述：`YiSVMono` 对任意 j，`Step` 对任意带接口的 j。`h₁ (chain 1)` 上的接口没有填 | 未做实例 |
| 4 翻译账 | 见下 | 判断 |

**参照关系的选择（偏离简报的三个选项）。** 用的是 `YiHCLim.Lim.Mω`，即 `YiHCRel.Mᴴ` 在 `h₁ ωᶜ` 上的封闭族。理由如下：
- `YiKVRel` 的关系只到第 0、1 层。
- `YiBSFam` 用的 `YiCLFam.M` 只到有限层 `fn n`，在 `h₁ ωᶜ` 上写不出陈述。
- `YiGIRel.R` 在一切层有类型，但据 `YiGLFrame` 文首，ℕ 极限目标上没有无前提的折叠保持。
- `Mω` 有现成的 `leafω` 与 `Self.PFω`，折叠正是 `seen` 用的 `YiRBSib.ψ`。

**问题表。**

| 问题 | 位置 | 档 |
|---|---|---|
| 换基层上的折叠对层号单调吗 | `YiSVMono.Mono.mono-path`：对偏移，沿不含 Ω 形状的字面路径，以 "承载谓词" 的形式成立 | 编译定理 |
| `seen` 在字面延伸 d 的 c 处读成什么 | d = ω：下界 ψ_ω(Ω_{ω+1})（`seen-ext`）。替身折的是 `h₁ d ⊕ ↑c` 的 Ω 树，c = ω+1 时层号是 ω+ω+1，读法应在 ψ_ω(Ω_{ω+ω+1}) 一带 | 前半编译定理，后半判断 |
| 一族分支的上确界承载链步参照吗 | 只归约到 `StepS`；其结论在 η ≤ ω+1 成立（`step-low`），第一处没有的是 η = ω+2 | 条件定理 |
| 字面延伸是不是必要条件 | 对值的下界不是：`seen-ω` 的前提只是 c 非零，`ωᵉ` 与 `nat 1` 也在内 | 编译定理 |
| 原材料只进低层尾项是否丢值 | 塔第 1 项 Ω 树的各支材料就是 `Ωt (h₁ c)`，替身的层号 `h₁ d ⊕ ↑c` 字面上在 `h₁ c` 的偏移之上，我判断这里不丢。y 一般时（回灌链里出现的嵌入），y 只贡献第 0 层的加项，我判断会丢。`cell` 的陈述里替身不含 y，但没有关于丢值的定理 | 判断 |

**翻译账。**
- 新增定义为零；树、折叠、合法性不改。
- `YiSVMono`、`YiSVCell` 不读记号：只用第一位置序、`Ωt` 的形状、折叠的后继行与 ℕ 极限行。
- 由树的要求逼出的：`Car` 必须对一切底与起点量化。ℕ 极限行第 n 项的底与起点是左项的折叠，固定底时单调写不出（判断，没有编译的否定）。
- 来自记号的只在验收一侧：参照项 ψ_ω(Ω_{ω+1})、ψ_ω(Ω_{Ω₁})，共尾与基本列引理，`StepS` 的形状（照 `YiLTLift`）。

#### 2. 文件表

全部在 `<仓库>/probes/OCF/Lean/`。删自己的接口后冷编，日志里只有自己模块的 `Checking` 行。

| 文件 | 代码行 | 冷编退出码 | 性质 |
|---|---|---|---|
| `YiSVMono.lagda.md` | 131 | 0 | 不读记号，`importclosure.py` 命中 0 |
| `YiSVCell.lagda.md` | 26 | 0 | 不读记号，`importclosure.py` 命中 0 |
| `YiSVStep.lagda.md` | 163 | 0 | 验收，读记号 |
| `YiSVOmega.lagda.md` | 106 | 0 | 验收，读记号 |
| `YiSVRed.lagda.md` | 78 | 0 | 验收，读记号 |

禁用构造与本机路径检索为 0。临时文件 `T0.agda` 到 `T5.agda` 在 `<实验目录>/work/YiSV/`。

#### 3. 定理表

记号约定：`Lω = nd sL G`，`G n = h₁ (nat n)`，`lvl : h₁ ωᶜ ≡ nd sL G` 是 `refl`；`ψω = ψᵘ ωᵀ`；`Qη η = ψω (E.Ωt η)`；`Fᴬ B β x = BS.ψ (tw 1) (Ok-tw 1) (rb-tw 1) B (h₁ ωᶜ) (inc ωᶜ self) β x`；`blk c = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))`。

**`YiSVMono`**（模块 `Mono (j : L) (oj : Ok j) (P Q : Tr j → Set) (P↑) (Q↑) (Q+)`，后三个是 P、Q 对 `◃` 向上封闭与 Q 对左加封闭）

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `Car` | `Car u = (ob : OkO j u) (r : R.Rb (j ⊕ u)) (B : Base (j ⊕ u)) (β : Tr⁺ j) → OKB B → P (proj₁ β) → Q (proj₁ (R.ψ (j ⊕ u) (Ok⊕ j u oj ob) r B j (lift j u) β (proj₁ (Ωt (j ⊕ u)))))` | 偏移 u 上，Ω 树朝 j 的折叠对一切底与起点落在 Q | 定义 |
| `liftS` | `(h : ⊤ → L) → Car (h tt) → Car (nd sS h)` | 后继形状上行 | 编译定理 |
| `liftL` | `(g : ℕ → L) (n : ℕ) → Car (g n) → Car (nd sL g)` | ℕ 极限形状从第 n 个孩子上行 | 编译定理 |
| `mono-path` | `∀ {u u′} → u ⊑ u′ → NoΩ u′ → Car u → Car u′` | 沿字面路径上行 | 编译定理 |
| `seen-mono` | `∀ {k h} (S : Schema k h) (u : floor S ≤ j) (β : Tr⁺ j) {c′ c : Tr k} → offsets S c′ ⊑ offsets S c → NoΩ (offsets S c) → Car (offsets S c′) → P (proj₁ β) → Q (proj₁ (seen S j oj u β c))` | 替身对偏移单调，任意模式 | 编译定理 |
| `seen◃` | `(u : zero ≤ j) (β : Tr⁺ j) {d c : Tr zero} → zero ⊢ d ◃ c → Car (↑ zero d) → P (proj₁ β) → Q (proj₁ (seen Sᶻ j oj u β c))` | c 字面延伸 d 时，d 处承载的 c 处也承载 | 编译定理 |
| `seen-self` | `(c : Tr zero) (u : zero ≤ j) (β : Tr⁺ j) → Car zero → P (proj₁ β) → Q (proj₁ (seen Sᶻ j oj u β c))` | 自身折叠承载的，每个替身都承载 | 编译定理 |
| `one⊑`（模块外） | `(c : Tr zero) → zero ⊢ zero ◃ c → ↑ zero (suc zero) ⊑ ↑ zero c` | 第 0 层每棵非零树的读回层号字面上在 1 之上 | 编译定理 |

**`YiSVCell`**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `cell` | `∀ {d} (nz : NZ d) (o : Ok (tw 1)) (Q : Tr (h₁ d) → Set) → (∀ {x y} → Q x → h₁ d ⊢ x ◃ y → Q y) → ∀ c (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y) → Q (proj₁ (seen Sᶻ (h₁ d) (proj₂ o d) (lift zero (↑ zero d)) (BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β x) c)) → Q (proj₁ (BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β (up x c y e)))` | 换基那一格把替身上的谓词交给整行 | 编译定理 |

**`YiSVStep`**（模块 `Step (j) (oj) (ν) (Low) (Chd) (Nu) (gtν : cmpᵀ (sucT ν) ν ≡ gt) (cofS : cof (E.Ωt (sucT ν)) ≡ cΩ ν) (fsS : ∀ η → fsT (E.Ωt (sucT ν)) η ≡ η) (pen : (p : Pos j) {ν′ : E.T} → Nu p ν′ → Pen (cmpᵀ (sucT ν′) ν)) (leaf : Mᴴ (Sig j) Low Chd Nu (E.Ωt ν) (proj₁ (Ωt j))) (selfP : 折到自身的保持)`；`Mj = Mᴴ (Sig j) Low Chd Nu`，`ℓ₊ = nd sS (λ _ → j)`）

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `Mβ₊` | `M₊ (E.Ωt (sucT ν)) (proj₁ (Ωt ℓ₊))` | 后继层的 Ω 树对着 Ω_{ν+1} | 条件定理 |
| `Fold₊.LFw` | `(β : Tr⁺ j) → Mj (ψᵘ ν t₀) (proj₁ β) → ∀ {a x} → M₊ a x → Mj (ψᵘ ν (t₀ ++ a)) (proj₁ (Fw β x))` | 后继层沿指定孩子路径折到 j 的保持 | 条件定理 |
| `Fold₊.LFu` | 同上，`Fw` 换成 `Fu`（路径 `inu (λ _ → self)`） | 沿一致路径的保持；`seen` 用的是这条 | 条件定理 |
| `seen-all` | `(c : Tr zero) (u : zero ≤ j) (β : Tr⁺ j) → P₀ (proj₁ β) → Q₀ (proj₁ (seen Sᶻ j oj u β c))`，`P₀ = Mj (ψᵘ ν [])`，`Q₀ = Mj (ψᵘ ν (E.Ωt ν))` | 每个替身承载 ψ_ν(Ω_ν) | 条件定理 |
| `seen-nz` | `(c : Tr zero) → zero ⊢ zero ◃ c → (u : zero ≤ j) (β : Tr⁺ j) → P₀ (proj₁ β) → Q₁ (proj₁ (seen Sᶻ j oj u β c))`，`Q₁ = Mj (ψᵘ ν (E.Ωt (sucT ν)))` | 非零孩子处的替身承载 ψ_ν(Ω_{ν+1}) | 条件定理 |

**`YiSVOmega`**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `seen-ω` | `(oc : (k : ℕ) → Ok (G k)) (c : Tr zero) → zero ⊢ zero ◃ c → (u : zero ≤ Lω) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → Mω (ψω (E.Ωt (sucT ωᵀ))) (proj₁ (seen Sᶻ (h₁ ωᶜ) (Rr , oc) u β c))` | 目标孩子 ω，一切非零 c：ψ_ω(Ω_{ω+1}) | 编译定理 |
| `seen-ext` | 同上，前提换成 `Ext ωᶜ c` | 字面延伸 ω 的 c | 编译定理 |
| `step0` | `(oc) (u : zero ≤ Lω) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → Mω (ψω (E.Ωt (sucT ωᵀ))) (proj₁ (seen Sᶻ (h₁ ωᶜ) (Rr , oc) u β (suc ωᶜ)))` | 第 0 步：c = ω+1 | 编译定理 |
| `seen-ω₀` | `(oc) (c : Tr zero) (u) (β) → Mω (ψω []) (proj₁ β) → Mω (ψω (E.Ωt ωᵀ)) (proj₁ (seen Sᶻ (h₁ ωᶜ) (Rr , oc) u β c))` | 一切 c（含零）：ψ_ω(Ω_ω) | 编译定理 |
| `okᴬ` | `proj₂ (Ok-tw 1) ωᶜ ≡ (Rr , ocᴬ)`（`refl`） | 实际层号证据就是定理里用的形状 | 编译定理 |
| `branch-nz` | `(B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → (c : Tr zero) → zero ⊢ zero ◃ c → Mω (ψω (E.Ωt (sucT ωᵀ))) (proj₁ (Fᴬ B β (blk c)))` | 实际证据下，塔第 1 项 Ω 树的非零各支承载 ψ_ω(Ω_{ω+1}) | 编译定理 |
| `branch-all` | 同上，无非零前提，结论 `Mω (ψω (E.Ωt ωᵀ)) …` | 各支承载 ψ_ω(Ω_ω) | 编译定理 |
| `top-shape` | `proj₁ (Fᴬ B β (proj₁ (Ωt (tw 1)))) ≡ Ω q₀ (λ z → proj₁ (Fᴬ B β (blk z)))`（`refl`） | 顶结点保留在 `q₀`，各支是 `blk` 的折叠 | 编译定理 |
| `top-from-branch` | `(B) (β) {t ν : E.T} → cof t ≡ cΩ ν → ν ≡ natT 0 → (∀ η c → HF.M 0 η c → Mω (fsT t η) (proj₁ (Fᴬ B β (blk c)))) → Mω t (proj₁ (Fᴬ B β (proj₁ (Ωt (tw 1)))))` | 各支承载 t[η] 时顶结点承载 t；前提未判定 | 条件定理 |
| `fin-nz` | `∀ N (oj : Ok (fn (suc N))) (c : Tr zero) → zero ⊢ zero ◃ c → (u : zero ≤ fn (suc N)) (β : Tr⁺ (fn (suc N))) → HF.M (suc N) (ψᵘ (natT (suc N)) []) (proj₁ β) → HF.M (suc N) (ψᵘ (natT (suc N)) (E.Ωt (sucT (natT (suc N))))) (proj₁ (seen Sᶻ (fn (suc N)) oj u β c))` | 接口的第二个实例：有限目标层，ψ_n(Ω_{n+1}) | 编译定理 |

**`YiSVRed`**（模块 `Red oc`；`Car t u` 是 `Mono` 取 `P = Mω (ψω [])`、`Q = Mω t`）

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `StepS` | `∀ {η x} → cof η ≡ c1 → HF.M 0 (pred η) x → Car (Qη (pred η)) (↑ zero x) → Car (Qη η) (↑ zero (suc x))` | 后继一步，未证 | 陈述 |
| `liftC` | `StepS → ∀ {η c} → HF.M 0 η c → Car (Qη η) (↑ zero c)` | 推导的其余四行无前提，`mw` 一行用 `mono-path` | 条件定理 |
| `step-low` | `∀ {η} → η ≤ᵀ sucT ωᵀ → ∀ x → Car (Qη η) (↑ zero (suc x))` | `StepS` 的结论在 η ≤ ω+1 时成立，不用归纳前提 | 编译定理 |
| `cof-top`, `fs-top` | `cof (Qη Ω₁ᵀ) ≡ cΩ (natT 0)`；`∀ η → fsT (Qη Ω₁ᵀ) η ≡ Qη η`（都是 `refl`） | 参照 ψ_ω(Ω_{Ω₁}) 的共尾与 Ω-基本列 | 编译定理 |
| `branch-red` | `Rᴬ.StepS → (B) (β) → Mω (ψω []) (proj₁ β) → ∀ η c → HF.M 0 η c → Mω (Qη η) (proj₁ (Fᴬ B β (blk c)))` | 给了 `StepS`，各支承载 ψ_ω(Ω_η) | 条件定理 |
| `top-red` | `Rᴬ.StepS → (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → Mω (Qη Ω₁ᵀ) (proj₁ (Fᴬ B β (proj₁ (Ωt (tw 1)))))` | 给了 `StepS`，顶结点承载 ψ_ω(Ω_{Ω₁}) | 条件定理 |

前提的可满足性：
- 起点前提 `Mω (ψω []) (proj₁ β)` 由 `leafω` 在 β = `Ωt Lω` 上满足（`ψω []` 定义上就是 `E.Ωt ωᵀ`）。
- `Step` 的接口有 ω 层与有限层两个实例。
- `StepS` 没有居民也没有否定，只知道其结论在 η ≤ ω+1 上成立。

#### 4. 第一个障碍

`YiSVRed.Red.StepS` 在 η = ω+2 处：要 `Car (ψ_ω(Ω_{ω+2})) (↑ zero (suc x))`，例如 x = `suc zero`，层号是 `Lω` 之上两层后继，目标仍是 `Lω`。`YiSVStep` 只给目标层正上方一层。再上一层缺两件：
1. `ℓ₊` 上折到自身的保持：`M₊` 上的 `selfP`，其中嵌入行要 "把 j 层的树上折进 `ℓ₊`" 的保持，即 `YiHCOmega.Tω.upB` 那一类引理，顶层换成 `ℓ₊`。
2. 跨两层的下折保持：`ℓ₊₊ → Lω`，其中 `ℓ₊` 槽位走链、`Lω` 以下槽位保留。这是 `YiBSFam.LF` 那一族在 ℕ 极限底座上的对应物。

归类：
- 对 c = `nat n` 这一段（层号 ω+n），我判断是工程量：有限底座上的同一族已编译（`YiBSFam.LF`），没有发现新的数学障碍。但没有编译，只写 "未走通"。
- 对字面延伸 ω 的 c，要的参照是 ψ_ω(Ω_c)，而换基层号是 `h₁ ωᶜ ⊕ ↑c`。c = ω+1 时是 ω+ω 之上的后继，ω+ω 是孩子不是有限层的 ℕ 极限层。这类层号上现在没有关系族与保持定理（`YiHCLim.Lim` 要求孩子是 `fn (d n)`）。是否有数学障碍没有判断依据，只写 "未走通"。

#### 5. 偏离与事故

- **参照关系**不在简报列的三个里，理由见第 1 节。
- **第 1 步只完成一半**：对一切字面延伸 ω 的 c 给了一致的下界 ψ_ω(Ω_{ω+1})，没有给 ψ_ω(Ω_c)。"一般的非零 d" 写成了接口，实例只有 ω 与有限层。
- **第 2 步只有条件定理**；第 3 步没有在 `YiRKChain.Real` 上实例化。
- **来源**：`liftS`、`liftL` 是先写出并编译的，之后才读到 `YiLTLift.upS`、`upL`、`up◃`、`liftQ`，两者同形，文首已注明；按 "同类引理第二次出现就合并"，`YiSVMono` 是对目标层与谓词抽象的写法，但没有回头把 `YiLTLift` 接到它上面（那边是比较表折叠 `YiTBRow.ψ`，这里是 `YiRBSib.ψ`）。`YiSVStep` 的 `LFw`、`chain`、`LFu` 照 `YiHCPlus.Fold₊` 改写。
- **两个 `nat`**：`YiTBTab.ωᶜ` 用 `YiTBRow.nat`，`YiHCLim` 一族用 `YiCLFam.nat`，两者不定义相等。实例用 `G n = h₁ (YiTBRow.nat n)` 加逐点相等 `eG` 解决，所以定理说的是 `YiRKCell` 的那个 `ωᶜ`。
- **编译**：五个仓库文件与六个临时文件，除 `T3.agda` 三次退出 42（两个同名 `MB`、一个未解的元变量、两处下划线参数）改后通过外，都是首次通过。没有 251。没有跑 `--profile`，没有量峰值内存。
- **没有读、只凭文首或简报转述引用的**：
  - `probes/Survey/Reports-2026-11-16/YiVA.md`、`AuditD.md`；
  - `EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册（没有遇到性能问题，没有查）；
  - 台账 V149、V158、V290、V293；
  - `YiRKChain`、`YiBSRead`、`YiBSReadNeg`、`YiBSUpNeg`、`YiBSClean`、`YiBSInner`、`YiGLFrame`、`YiGT*`、`YiFI*`、`YiKTSlot`、`YiKFValue` 只读了文首；
  - `YiRBSib` 只读了证据一段与签名；`YiHCLim`、`YiHCOmega`、`YiLTLift` 只读了用到的段落。
- "ω+n 一段是工程量"、"固定底时单调写不出"、"材料 y 一般时丢值"、"替身的读法在 ψ_ω(Ω_{ω+ω+1}) 一带" 都是判断，没有编译。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：换基替身的值（前缀 YiSV，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同批另三路与你互不导入。

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
换基在真实链孩子上把被问到的孩子对变成带 `lift` 证据的对（`YiRKCell.w3`），但替身的值没有定理：现有换基的值定理只到数字孩子（`YiBSCrit.finite-crit`）。要的是：目标孩子 d 取 ω（`YiRKCell` 的 `ωᶜ`），对字面延伸 d 的分支 c，换基行里的 `seen S₁ (h₁ d) … c` 不低于参照 ψ_d(Ω_c) 一类的读法，从而这一族分支的上确界承载链步需要的参照（d = ω 时 sup_c ψ_ω(Ω_c) 一类）。YiRK 判断需要两件：换基层上的折叠对层号单调；`seen` 的读法。

#### 要做的（按序）
0. **最小检查**：写出要证的陈述（参照一侧用 `YiKVRel`、`YiGIRel` 或 `YiBSFam` 的关系 `M`，选一个并说明理由），先对 c = d+1 在临时文件里编译类型并试证。不成立就停下回报。
1. **证 `seen` 的值引理**：对字面延伸 d 的 c（变量），先 d = ω，再一般的非零 d。复用 `YiBSFam`、`YiBSCrit` 的有限读回层证明（搬来的写明来源）。
2. **上确界**：由 1 得到朝 `h₁ d` 折塔第 1 项 Ω 树的输出承载参照（链步的那一项，例如 d = ω 时的 γ 链第 1 项）。注意原材料只进低层尾项（`w3`），说明这是否丢值（判断标档）。
3. 若有余力，chain 1（`YiRKChain` 的副本，或在变量上陈述）上的同一件事。
4. 说明换基这一步的翻译账（哪些来自记号、哪些由树的要求逼出）。

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


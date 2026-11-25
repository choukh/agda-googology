# 替身值的后继一步 StepS（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 03:57 至 04:34 |
| 工具调用 / agda 编译 (粗数) | 35 / 12 |
| token (usage 字段，按消息去重) | 输出 199574；新写入缓存的输入 356816；读缓存的输入 6744944；其余输入 62 |
| 写过的仓库文件 | `YiZSLev.lagda.md`, `YiZSLit.lagda.md`, `YiZSTower.lagda.md` |
| 文件前缀 | `YiZS` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 6 件全部退出 0，禁用构造 0，YiZSUni 导入闭包干净；StepS 在 η = ω+n+1 对一切 n 成立（StepS-ωn），各支到 ψ_ω(Ω_{ω·2})（branch-ω2）；ω·2+1 起前提对任意树量化，未走通；ℕ 极限层号接口四条；同形引理合并（genS、genL） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b77/YiZS.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiZS 回报: 替身值的后继一步 StepS

#### 1. 判决

**对纲领与目标.** 本路全部在验收一侧 (第 4 层), 树、折叠、合法性一行未改, 只新建 6 个 `YiZS*` 文件. 翻译账: 新增的是参照关系与保持证明, 没有新构造子或结点字段; `YiZSLev` 把 "一个层号上要的保持" 写成一条记录 (`Laws`), 后继层号写成对结构参数的一步定理, ω+n 一段由同一条一步定理迭代得到, 不按阶段定制. 这一步新用到的字段: `selfP₊` 用 `upP`, `df₊` 的嵌入行用 `selfP` 与 `df`, 链行用 `leafᵗ`. 接口里读法是记号项, 所以不算树自足.

**各步到哪里.**
- 第 0 步: 做完. η = ω+2 那一格的两条保持 (ℓ₁ 折到自身; ℓ₂ 跨两层折到 ω 层) 的陈述在临时文件里编译通过 (退出 0).
- 第 1 步: 做完, 编译定理. 两条保持对一切 n 成立 (接口迭代); `StepS` 在 η = ω+n+1 处对一切 n, x 成立, 且是原前提形状 (`StepS-ωn`).
- 第 2 步: 部分. `StepS` 在 η = ω·2+1 起确实要 ℕ 极限层号上的关系族. 最小形状已写出并在塔上实例化; 接口的四条 (`leafλ`, `hi-penλ`, `selfPλ`, `upPλ`) 已编译, `kc`, `df` 两条未做.
- 第 3 步: 未到. `StepS` 整体未证, 没有否定, 状态是 "未走通". `top-red` 仍是条件定理, 顶结点承载 ψ_ω(Ω_{Ω₁}) 没有得到.
- 第 4 步: 做完, 编译定理. `YiSVMono.liftS`, `liftL` 与 `YiLTLift.upS`, `upL` 都由同一条定理 (`Lift.genS`, `genL`) 推出, 重推出的陈述与原文逐字相同.

**值的现状 (编译定理).** 换基折叠下, 塔第 1 项 Ω 树朝 `h₁ ω` 折时:
- 孩子 c 字面含 n+1 (`nat (suc n) ⊴ c`) 的那一支承载 ψ_ω(Ω_{ω+n+1}) (`branch-seg`);
- 字面延伸 ω 的孩子 (`ωᶜ ⊴ c`) 的那一支承载 ψ_ω(Ω_{ω·2}) (`branch-ω2`). 此前这些支是 ψ_ω(Ω_{ω+1}) (`branch-nz`).
- 顶结点没有新结论.

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 目标层之上两层的两条保持陈述是否成立 | `<实验目录>/YiZSStep0.agda` (类型); `YiZSLev.Step₊.selfP₊`, `Fold.LF` (证明) | 编译定理 |
| 两条保持对一切 n | `YiZSTower.Base.pk` | 编译定理 |
| `StepS` 在 η = ω+n+1 | `YiZSLit.Seg.StepS-ωn` | 编译定理 |
| `StepS` 是否要 ℕ 极限层号的关系族 | η = ω·2+1 处: 是 | 判断 (依据: x 承载 ω·2 时偏移 `suc x` 的层号是 ℕ 极限层号的后继, 一步定理要该极限层号的完整接口) |
| ℕ 极限层号的接口 | `YiZSLim.Lim₊` 四条已编译; `kc`, `df` 未做 | 编译定理 (四条) / 未走通 (两条) |
| `StepS` 对一切推导 `M⁰ (pred η) x` | 未证, 无否定 | 未走通; 障碍分析是判断 (见第 4 节) |
| `top-red` 无前提化 | 未做 | 未走通 |
| 合并同形引理 | `YiZSUni`, `YiZSUniT` | 编译定理 |

#### 2. 文件表

都在 `probes/OCF/Lean/`. 删自己的接口后逐个冷编, 堆上限 6G, 日志里只有自己模块的 `Checking` 行.

| 文件 | 代码行 | 冷编退出码 | 堆峰值 |
|---|---|---|---|
| `YiZSLev.lagda.md` | 325 | 0 | 1.35G |
| `YiZSTower.lagda.md` | 204 | 0 | 1.36G |
| `YiZSLit.lagda.md` | 191 | 0 | 1.45G |
| `YiZSLim.lagda.md` | 135 | 0 | 1.37G |
| `YiZSUni.lagda.md` | 98 | 0 | 0.16G |
| `YiZSUniT.lagda.md` | 43 | 0 | 1.30G |

- 禁用构造与本机路径检索: 0 命中.
- `importclosure.py OCF.Lean.YiZSUni`: 禁用表命中 0, OK. 只有这一个文件标 "不读记号", 其余五个是验收文件, 读记号.
- 临时文件: `<实验目录>/work/YiZS/YiZSStep0.agda` (退出 0), 日志在同目录.

#### 3. 定理表

记号: `νᵀ n = E.ψ [] (E.𝟏 ∷ []) ∷ natT n` 是 ω+n (`νᵀ 0 ≡ ωᵀ`, `νᵀ 1 ≡ sucT ωᵀ` 都是 `refl`); `ω2ᵀ` 是 ω·2; `R.Car` 即 `YiSVRed.Red.Car`; `Qη η = ψω (E.Ωt η)`. 全部是编译定理档.

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `Step₊.W₊` | `W₊ : Laws D₊ o₊ ν₊` (模块前提: `D : Data j`, `W : Laws D oj ν`, `cofS : cof (E.Ωt ν₊) ≡ cΩ ν`, `fsS : ∀ η → fsT (E.Ωt ν₊) η ≡ η`, `gtν : cmpᵀ (sucT ν) ν ≡ gt`, `loν : Data.Lo D ν`, `hiν : Data.Hi D ν₊`, `penT : Pen (cmpᵀ (sucT ν) ν₊)`) | 一步定理: j 满足接口则 `nd sS (λ _ → j)` 满足接口, 前提只有六条记号一侧的比较与共尾式 | YiZSLev |
| `Step₊.selfP₊` | `(r : Rb ℓ₊) (B : Base ℓ₊) (β : Tr⁺ ℓ₊) (P₀ : E.T) → M₊ (ψᵘ ν₊ P₀) (proj₁ β) → ∀ {a x} → M₊ a x → M₊ (ψᵘ ν₊ (P₀ ++ a)) (proj₁ (ψ ℓ₊ o₊ r B ℓ₊ self β x))` | 上折到自身的保持 | YiZSLev |
| `Step₊.Fold.LF` | `∀ {b} (τ : Tg₊ b) (β : Tr⁺ (lv₊ τ)) → Mᵗ₊ τ (ψᵘ (νᵗ₊ τ) t₀) (proj₁ β) → ∀ {a x} → M₊ a x → Mᵗ₊ τ (ψᵘ (νᵗ₊ τ) (t₀ ++ a)) (proj₁ (F τ β x))` | 朝每个登记目标 (跨任意多层) 的下折保持 | YiZSLev |
| `Top.Ω-fold` | `∀ {b} (τ : Tg b) (r : Rb j) (B : Base j) → ((i : L) (u : i ≤ j) → proj₁ (Ωt i) K.⊴ proj₁ (B i u)) → (β : Tr⁺ (lv τ)) → Mᵗ τ (ψᵘ (νᵗ τ) []) (proj₁ β) → Mᵗ τ (ψᵘ (νᵗ τ) (E.Ωt ν)) (proj₁ (ψ j oj r B (lv τ) (pth τ) β (proj₁ (Ωt j))))` | 满足接口的层号的 Ω 树朝任一目标折, 承载 ψ_目标(Ω_ν) | YiZSLev |
| `Base.W₀` | `W₀ : Laws D₀ (Rr , oc) ωᵀ` | ω 层满足接口 (新证的只有 `upω`: 上折进任意高层) | YiZSTower |
| `Base.pk` | `pk : ∀ n ob → Pk n ob` (字段 `W : Laws D (oJ n ob) (νᵀ n)`) | ω 层加偏移 n 的层号满足接口, 读法 ω+n | YiZSTower |
| `Base.carN` | `∀ n → R.Car (Qη (νᵀ (suc n))) (↑ zero (nat (suc n)))` | 偏移 n+1 的 Ω 树朝 ω 层折, 承载 ψ_ω(Ω_{ω+n+1}) | YiZSTower |
| `Base.seg` | `∀ n {η c} → η ≤ᵀ νᵀ (suc n) → nat (suc n) ⊴ c → R.Car (Qη η) (↑ zero c)` | 字面含 n+1 的偏移 c 同样 | YiZSTower |
| `Base.ext-ω2` | `∀ {c} → ωᶜ ⊴ c → R.Car (Qη ω2ᵀ) (↑ zero c)` | 字面延伸 ω 的偏移承载 ψ_ω(Ω_{ω·2}) | YiZSTower |
| `branch-seg` | `∀ n (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → ∀ c → nat (suc n) ⊴ c → Mω (Qη (νᵀ (suc n))) (proj₁ (Fᴬ B β (blk c)))` | 实际证据下塔第 1 项 Ω 树的第 c 支承载 ψ_ω(Ω_{ω+n+1}) | YiZSTower |
| `branch-ω2` | `(B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β) → ∀ c → ωᶜ ⊴ c → Mω (Qη ω2ᵀ) (proj₁ (Fᴬ B β (blk c)))` | 字面延伸 ω 的各支承载 ψ_ω(Ω_{ω·2}) | YiZSTower |
| `dec` | `∀ n (x : Tr zero) → (Σ ℕ λ k → (x ≡ nat k) × (suc k ≤ⁿ n)) ⊎ (nat n ⊴ x)` | 第 0 层的树要么是小于 n 的字面自然数, 要么字面含 `nat n` (树侧, 不读记号) | YiZSLit |
| `sound` | `∀ {t x} → M⁰ t x → ∀ k → x ≡ nat k → Σ ℕ λ i → (t ≡ natT i) × (i ≤ⁿ k)` | 字面自然数 k 只承载不超过 k 的自然数项 (对一切推导, 含 `mc`) | YiZSLit |
| `no-nat` | `∀ n k → M⁰ (νᵀ n) (nat k) → ⊥` | 字面自然数不承载 ω+n | YiZSLit |
| `Seg.StepS-ωn` | `∀ n {x} → M⁰ (pred (νᵀ (suc n))) x → R.Car (Qη (pred (νᵀ (suc n)))) (↑ zero x) → R.Car (Qη (νᵀ (suc n))) (↑ zero (suc x))` | `StepS` 在 η = ω+n+1 的实例 (第三个前提没有用到) | YiZSLit |
| `Seg.StepS-fin` | `∀ n N {η x} → η ≤ᵀ νᵀ (suc N) → M⁰ (νᵀ n) x → R.Car (Qη η) (↑ zero (suc x))` | x 承载某个 ω+n 时, 结论对一切 η ≤ ω+N+1 成立 | YiZSLit |
| `Seg.StepS-ω2` | `∀ n {x} → M⁰ (νᵀ n) x → R.Car (Qη ω2ᵀ) (↑ zero (suc x))` | 同上, 到 ω·2 | YiZSLit |
| `Lim₊.leafλ` | `leafλ : Mλ (E.Ωt λᵀ) (proj₁ (Ωt ℓ))` (前提: `cofL : cof (E.Ωt λᵀ) ≡ cω`, `fsL : ∀ k → fsn (E.Ωt λᵀ) k ≤ᵀ E.Ωt (ν k)`) | ℕ 极限层号的 Ω 树承载 Ω_λ, 孩子读法与 λ 的基本列只要逐项不低 | YiZSLim |
| `Lim₊.selfPλ` | `(r : Rb ℓ) (B : Base ℓ) (β : Tr⁺ ℓ) (P₀ : E.T) → Mλ (ψᵘ λᵀ P₀) (proj₁ β) → ∀ {a x} → Mλ a x → Mλ (ψᵘ λᵀ (P₀ ++ a)) (proj₁ (ψ ℓ o r B ℓ self β x))` | ℕ 极限层号折到自身的保持 | YiZSLim |
| `Inst.lvl2`, `leaf2` | `L2.ℓ ≡ Wω.Lω ⊕ ↑ zero ωᶜ` (`refl`); `L2.Mλ (E.Ωt ω2ᵀ) (proj₁ (Ωt (Wω.Lω ⊕ ↑ zero ωᶜ)))` | 实例: 塔作孩子, λ = ω·2; `Lim₊` 的前提可满足 | YiZSLim |
| `Lift.genS` | `∀ {h : ⊤ → L} (o : Ok (nd sS h)) (r : RbT (nd sS h)) (ws : (c : ⊤) → j ≤ h c) → SΩ (h tt) (proj₂ o tt) (rc r tt) (ws tt) → SΩ (nd sS h) o r (inu ws)` | 合并后的共同陈述, 后继形状; 对任何满足 `FoldLaws` (`f⊵`, `fm`, `fu`, `fs`) 的折叠 | YiZSUni |
| `Lift.genL` | `∀ {g : ℕ → L} (o : Ok (nd sL g)) (r : RbT (nd sL g)) (ws : (n : ℕ) → j ≤ g n) (n : ℕ) → SΩ (g n) (proj₂ o n) (rc r n) (ws n) → SΩ (nd sL g) o r (inu ws)` | 同上, ℕ 极限形状 | YiZSUni |
| `lawsᴿ`, `MonoU.liftS′`, `liftL′` | `lawsᴿ : FoldLaws R.Rb (λ r c → proj₂ r c) R.ψ`; `liftS′ : (h : ⊤ → L) → M.Car (h tt) → M.Car (nd sS h)`; `liftL′ : (g : ℕ → L) (n : ℕ) → M.Car (g n) → M.Car (nd sL g)` | 换基核的折叠满足四条律; `YiSVMono` 的两条由定理推出 | YiZSUni |
| `lawsᵀ`, `upS′`, `upL′` | `lawsᵀ : FoldLaws TB.Rb (λ r c → proj₂ r c) TB.ψ`; `upS′ : ∀ {h : ⊤ → L} → Q t (h tt) → Q t (nd sS h)`; `upL′ : ∀ {g : ℕ → L} (n : ℕ) → Q t (g n) → Q t (nd sL g)` | 比较表折叠满足同样四条律; `YiLTLift` 的两条由同一定理推出 | YiZSUniT |

前提可满足: `ωᶜ ⊴ c` 取 c = `ωᶜ`; `nat (suc n) ⊴ c` 取 c = `nat (suc n)`; `Mω (ψω []) (proj₁ β)` 取 β 为 ω 层的 Ω 树 (与 `YiSVOmega` 的用法相同); `M⁰ (νᵀ n) x` 取 x = `ωᶜ` 加 n 个后继 (未单独编译成实例, 这一条是判断).

#### 4. 第一个障碍

**精确位置.** `StepS` 在 η = ω·2+1: 要 `R.Car (Qη (ω·2+1)) (↑ zero (suc x))`, 其中 `M⁰ ω2ᵀ x`. 挡住的有两层.

1. **工程上挡住 (未做, 无否定).** ℕ 极限层号 `nd sL g` 的接口缺 `kc` 与 `df`. 做法已知是 `YiHCLim.Lim.Fold.LFU`, `LFΩ` 的对应物, 孩子从有限层 `fn (d n)` 换成带接口的层. 具体要:
   - 定目标集 (各孩子的目标经 `inc n`; 一致路径上各孩子共有的目标);
   - 嵌入行里孩子编号的比较 `way` 两支: 路径 `v ∙ u` 仍是登记的目标; 低孩子的树经 `emb` 搬进高孩子后仍在高孩子的关系里. 后一条对塔是一行 `mU mz`, 这是判断, 未编译.
   - 估计 300 行以上, 本轮没有动手.

2. **数学上挡住 (判断, 无编译否定).** 即使极限层号的一步做成, `StepS` 的前提是任意推导 `M⁰ (pred η) x`, x 是任意树.
   - ω+n 一段能绕过, 靠的是 `dec`: 非字面自然数的树字面含每个 `nat n`. 这对有限 n 成立.
   - 到 ω·2 没有对应物. 例: x = `lim f`, 其中 `f n = ω′ + n`, `ω′ = lim (0, 2, 4, …)`. x 承载 ω·2, 但不字面含 `ωᶜ`. 所以要的是 "ω 层 ⊕ ↑ x" 对任意树 x 的接口.
   - 接口的读法是记号项, 任意 `lim f` 没有项可读. 沿推导构造接口在 `mz`, `mw`, `mc` 三行不成立 (读法低于层号实际高度时, 槽位的保留与走链对不上).
   - 所以按现在的陈述 (顶结点的分支关系是 `M⁰`, 对一切树量化), `StepS` 在 ω·2+1 以上我没有看到证法.
   - 这与 AGENTS "量化域先取带证据的读回域" 同形; 同批 `YiQD` (按读回域的充分性与参照出口) 若把顶槽位的分支关系限到读回域, 本路的 `pk` 与 `Lim₊` 可以直接接上. 这是判断, 穷尽性未经挑战.

**附带观察 (判断).** 顶结点在 `Mω` 里只能由 `mΩ` (对一切分支), `mL`, `mw` (只经第一分支), `mc` 得到承载. 第一分支 c = 0 只承载 ψ_ω(Ω_ω), 所以 "各支承载 ψ_ω(Ω_{ω·2})" 在这个参照关系里推不出 "顶结点承载 ψ_ω(Ω_{ω·2})".

#### 5. 偏离与事故; 没有读的东西

- **没有读** `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册. 简报要求先读; 本轮没有遇到性能问题 (堆峰值 1.45G, 无 251), 所以没有查.
- **没有读, 只凭简报转述引用的**: `YiHCPlus.Fold₊`, `YiHCFold` (`Self.PF`, `liftU`), `YiBL*`, `YiBC*`, `YiBSFold`, `YiBSBase`, `YiBSRead`, `YiRKCell`, `YiCTCall`, `YiDG*`, `YiQD`/`YiEM` 两路的内容, 台账 V287. `YiTBRow`, `YiTBFam`, `YiLTLift` 只读了用到的片段.
- 第一个文件 (第 0 步临时文件) 是在读完定义之后才写的, 很可能超过简报的 30 分钟; 没有计时.
- 第 1 步的形状与简报字面不同: 没有逐条证 "上折到自身" 与 "跨两层下折" 再对 n 归纳, 而是把它们并进一条接口记录, 对接口做一步定理再迭代. 两条保持是接口的 `selfP` 与 `df` 字段.
- 来源说明都在各文件文首. 没有用 `YiSVStep.Step` 模块本身 (它的 `LFw`, `LFu` 是 `Fold.LF` 在目标 `nothing` 处的特例, 未合并, 原文件未动).
- 事故: 一次冷编用 `/usr/bin/time -l` 包装, 沙箱不许 `sysctl`, 六个文件都报退出 1 (agda 本身通过); 去掉包装改用 `+RTS -s` 重跑, 上表是重跑的结果. 编译中出过四次退出 42 (`{true}` 被 `--hidden-argument-puns` 当作双关; 模块名 `T` 与局部名 `P` 重名; 一个隐式参数未解), 都已改.
- `YiZSTower` 在首次通过后又改过一次 (给 `Pk` 加字段 `hi2`, 把 `ω2ᵀ` 提到顶层), 之后全部重新冷编.
- 没有改任何已有文件, 没有提交, 没有动 `README`, `LOG`, 台账.

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：替身值的后继一步 StepS（前缀 YiZS，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同批另三路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者已关闭现行折叠上同步对象那一步链步（台账 V287），依据是两份先读定义的 Fable 5.2 封存审核。**主线定义不动**；改树、折叠、合法性只在新文件里做候选；换基进主线由作者定。
- 第七十七批作者选四路（选项原文）："替身值的后继一步 StepS (Recommended), 按读回域的充分性与参照出口 (Recommended), 替身码域加嵌入码 (Recommended), Fable 先读定义审查换基候选"。前缀 `YiZS`（Fable 5.2）、`YiQD`（Opus 5.5）、`YiEM`（Opus 5.5），以及审查 E 路（Fable 5.2，只在临时目录），互不导入。
- **换基候选的现状（第七十五、七十六批，主审冷编复核过；都在 `probes/OCF/Lean/`）**：
  - 换基折叠 `YiBSFold`（`BS.ψ`；换基行在 `route` 落在地板之上时对一切孩子 c 同形：在 `j ⊕ offsets S c` 上重建 Ω 树经 `seen` 沿 `lift` 朝原目标折，原孩子树只进低层尾项，`YiBLFold.row-reb`）；证据 `YiBSBase`（`Schema`、`split`、`rbO`、`rb-tw`、`seen`）；替身码 `YiBSRead`（`Read`、`read`、`Domain`）；核 `YiRBSib`。
  - 证据覆盖（`YiBCCover`）：读回域上处处满（`full-sync`、`Chain.full-chain`、`full-kl`、`full-kl-child`、`full-rbO`、`full-↑`、`rb-row`、`full-row`）；变量层号上给不出（`YiBCNeg.no-sync`，谓词太宽）；嵌入块到达换基行而不在码域里（`YiBCReach.reach`、`yₑ∉`，ω 代替链点；`YiBCNeg.emb∉read`、`∉dom`）。`YiBCSync.a₁-eq`、`chain-eq`：`YiRKChain` 的副本与原定义逐字相等。
  - 律（`YiBLIface`、`YiBLFold`，不读记号）：换基律 `RebAt`、嵌入律 `EmbLaw`、出口 `OutR`；`SuffR.keepAll`、`sys→low`、`SuffRA`；换基折叠满足树一侧全部律（`rebᴮ`、`keepᴮ`、`keepᴬ`、`fallᴬ`、`monoᴬ`、`monoᴮ`）；`lowᴮ`、`lowᵗ`（LowKeep，前提只剩参照一侧：`OutR`、辅助系统的 `Out`、`Gen⁺`、`Weak`、`Lim`、`Node`）；`ev-cp`、`nodeE-cp`（目标槽位副本由 `lift` 实填）；`top-noEv`、`main-noEv`（替身自己孩子层号的槽位、主系统孩子槽位不保留）。YiBL 判断的下一处障碍：(1) 主系统 `OutR.nodeE` 在 ℓ 层孩子槽位上只能走链，而 `SuffR` 对一切树陈述，要改成按读回域陈述；(2) 辅助系统 `Out.nodeE` 走链一支要 `∀ k → Φ s (g (z k)) ⊴ Φ s (nd p g)`，对部分和极限在 k ≥ 1 处可能不成立。底层接口 `YiFIIface`（`Suff.keepAll`、`sys→low`、`Out`）与 `YiAbsG*`。
  - 值（`YiSV*`）：替身对偏移沿字面路径单调（`YiSVMono.Mono.mono-path`、`seen-mono`、`seen◃`，不读记号；与 `YiLTLift.upS`、`upL` 同形，未合并）；目标孩子 ω 时非零各支承载 ψ_ω(Ω_{ω+1})（`YiSVOmega.branch-nz`、`seen-ω`，参照关系 `YiHCLim.Lim.Mω`）；顶结点承载 ψ_ω(Ω_{Ω₁}) ⇐ 后继一步 `YiSVRed.Red.StepS`（`top-red`、`branch-red`、`liftC`），`StepS` 的结论在 η ≤ ω+1 成立（`step-low`），η = ω+2 处缺 "目标层之上两层" 的保持（`ℓ₊` 上折到自身的保持，`YiHCOmega.Tω.upB` 一类；跨两层的下折保持，`YiBSFam.LF` 在 ℕ 极限底座上的对应物）；字面延伸 ω 的分支要 ω+ω 一类 ℕ 极限层号上的关系族（`YiHCLim.Lim` 只要有限孩子 `fn (d n)`）。
  - 比较表一路的否定：`YiRKCell.no-ωᵉ`、`YiCTCall.cell`、`YiDGDiag.ColW.wdecα`、`YiDGCell.cell→wdecα`。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
证 `YiSVRed.Red.StepS`：`∀ {η x} → cof η ≡ c1 → HF.M 0 (pred η) x → Car (Qη (pred η)) (↑ zero x) → Car (Qη η) (↑ zero (suc x))`，从而经 `top-red` 得到换基折叠下塔第 1 项 Ω 树朝 `h₁ ω` 折时顶结点承载 ψ_ω(Ω_{Ω₁})。

#### 要做的（按序）
0. **最小检查**：η = ω+2、x = `suc zero` 那一格，写出要的 "目标层之上两层" 的两条保持（上折到自身、跨两层的下折）的陈述，在临时文件里编译类型。已有同族：`YiHCOmega.Tω.upB`、`YiBSFam.LF`、`YiHCPlus.Fold₊`、`YiSVStep`（先 `grep`，不重证，搬来的写明来源）。不成立就停下回报。
1. **层号 ω+n 一段**：对一切 n 证这两条保持（对 n 归纳，阶段无关），得到 `StepS` 在 η = ω+n 一段成立。
2. **字面延伸 ω 的分支**：看 `StepS` 是否要 ω+ω 一类 ℕ 极限层号上的关系族；若要，写出该关系族的最小形状并试证，或写清缺的是哪一条。
3. 若 `StepS` 全成立：`top-red` 无前提化，报出顶结点承载 ψ_ω(Ω_{Ω₁})（编译定理）。
4. 合并：把 `YiSVMono` 与 `YiLTLift.upS`、`upL` 的同形引理合成一条（新文件里的共同陈述，两边都由它推出），按 AGENTS "同类引理以不同名字第二次出现时, 合并成一条并写进接口"。

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


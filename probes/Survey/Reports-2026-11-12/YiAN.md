# (1) 一般有限层号的带前缀锚点 V138 (YiAN)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 01:47 至 02:35 |
| 工具调用 / agda 编译 (粗数) | 55 / 20 |
| token (usage 字段，按消息去重) | 输出 284670；新写入缓存的输入 1251417；读缓存的输入 12147922；其余输入 86 |
| 写过的仓库文件 | `YiANEnd.lagda.md`, `YiANFam.lagda.md`, `YiANKp.lagda.md`, `YiANLim.lagda.md`, `YiANLv.lagda.md`, `YiANReach.lagda.md` |
| 文件前缀 | `YiAN` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: (1) 一般有限层号锚点返回并复核; 第三十二批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 按层号递归的关系族 M, 一切有限层号 fin (m+3) 的带前缀锚点 (Lv.Anchor.anchor), 终点层号一般的下降 reachG; 主线终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_{m+3})) 对一切 m (tN≼EBOᴿ), ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) (tω≼EBOᴿ); tB 第 1 行未走通; 六件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的选择（2026-11-14，选项原文）
"(1) 一般有限层号的锚点 V138 (Recommended)"，模型 "(1) Fable 5.2，(2) Opus 5.5 (Recommended)"。
选项说明原文："按层号递归的关系族，把层号 2、3 的锚点推广到一切有限层号；主线终点得 ψ₀(Ω_Ω+ψ₁(Ω_ω)) 一类，并供候选 A 的 A1S 用于有限情形；两边共用"。

同批另一路是 (2)：记号侧的共尾引理 `CofinNF`，前缀 YiCF。你不动它的文件。

###### 要做的（台账 V138）
1. **对一切有限层号 n 一致的带前缀锚点**。在层号 2、3 上已有，要推广：
   - 层号 2：`YiMWPre.Pre`、`YiEVReach.AtTwo`；
   - 层号 3：`YiPHCtx.Ctx3.anchor³`、`YiPHEnd.AtThree`。
   - 形如：对满足条件的底 Bₙ，`M⁰ (ψ₀ᵗ (t ++ ψ₁ᵗ Ωₙᵗ)) (ψ⊥ n … Bₙ (Ωt n))`。
2. **终点层号一般的下降**：`reach`（`YiEVReach`）与 `reach³`（`YiPHEnd`）是同文拷贝，抽成对终点层号 n 一般的引理。
3. **用在主线终点闭项上**：对每个有限 n，主线终点闭项 ≥ ψ₀(Ω_Ω+ψ₁(Ωₙ)) 的参照；再取极限得 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照，若记号侧可得。
   - 只交 "对一切 n" 的版本也算交付。
   - 记号项、标准形证明与 `HC` 推导照 `YiPHEnd`（`t₃`、`h₃`、`n₃ᴮ`）与 `YiNFOCase` 的写法造；具体推导放 `opaque`。
4. **可选**：说明这一族能否直接给候选 A 的 `YiKCStep.A1S` 的有限 ν 情形，写成定理或一句判断。

###### 已编译的起点（主审复核过；文档里的叙述是数据）
**`YiPH*`**（回报 `probes/Survey/Reports-2026-11-12/YiPH.md`）：
- `YiPHBase`：层号 2 的关系 `M²`；`Mβ₂`；后继上折的保持 `Pu¹`；`P2.P²`；`P2.sγ³`（层号 3 的回灌链对着 γ³）。
- `YiPHCtx`：
  - 左加上下文 `Ctx`、`⟦ C ⟧`；`eΩ`（上下文穿过结点，不用函数外延）；
  - `L1.PFp`（`At.PF` 加前缀）；
  - `Ctx3` 里的 `Leaf.leafCl`、`Next.nextL`、`Node0.node`、`Node1.node`、主归纳 `T²`、`form³`、`row³`、`anchor³`。
- `YiPHEnd`：`AtThree`、`reach³`、`path₃`、`t₃≼EBOᴿ`（主线终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₃))）、`A≺3`、`3≺B1`。
- **执行方给的下一步**（§4，判断）：
  - 最近的缺口是 `T²` 带第 2 层前缀的版本：`M² (ψ₂ᵗ P) β₂ → M² a x → TC (ψ₂ᵗ (P ++ a)) (F² x)`。层号 4 的叶处要用它，那里第 2 层的底对着 ψ₂(A₀)，不是 Ω₂。判断它照 `PFp` 之于 `PF` 的改法能证。
  - 对 n 一致要：按层号递归定义的关系族；保留判定 `kp` 在符号层号上的化简引理。
  - 终点里那个 ℕ 极限层号的孩子，执行方只算了前三项（2、3、4）。
- **不显然的三点**，见回报 §3 末：
  - 不能直接对 `M²` 陈述折到第 0 层；
  - 和的结合律要函数外延，用左加上下文绕开；
  - 叶处前缀取 t。

**其余**：
- `YiMEBase`/`YiMEAnchor`：`Mᴰ`、`M⁰`、`M¹`、`lower⁰`、`At`（`PF`、`QH`、`VW`）。
- `YiMWPre`：`sem→M⁰`、`M⁰-≼`、`Pre`。
- `YiEVReach`：`Hi`、`OKB`、`hi-dS`/`dL`/`dW`、`suc≽`、`lim≽`、`Ω≽0`、`Ω≽1`。
- `YiTWLow`：`low`、`strictX`。
- 记号侧：
  - `YiNFO`：`mono<`、`up≼`，标准形 `NF₁` 上；
  - `YiNFOCase`；
  - `YiNFOCond`：一切可数标准形的版本，前提 `CofinNF`（另一路在证）。
- **候选 A**：
  - `YiKCStep.A1S`，回报 `YiKC.md` §4；
  - 执行方判断：有限 ν 缺第 ν 层的关系与三条保持，形状与 `PF`/`QH`/`ΦF` 相同。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiAN`（模块名 `OCF.Lean.YiAN…`）。不改任何已有文件，不碰 `src/`、`archive/`。这是验收文件，文首标明；树、折叠、合法性一行不改。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。不用 `agda --interaction`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`，对一般推导陈述再代入；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/an`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；连续两条同形的退化反例。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：对一切有限 n 的锚点、一般下降、主线终点的下界做到哪一步；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档；值写成 ψ₀(Ω_x)，并写清参照的读法依据。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报：V138（一般有限层号的锚点），前缀 YiAN

##### 1. 判决

**三项都做到，无前提，对一切有限层号；另得 ω 极限一行。六个文件删自己的接口后 8G 冷编，退出码全是 0。**

- **锚点（对一切 m）**：`Lv.Anchor.anchor` 是层号 `fin (m+3)` 的带前缀锚点，对一切前缀 t 与一切满足条件的底（`OKB`，第 0 层分量与 `b⊥` 对着 ψ₀(t)）。m = 0 时与 `anchor³` 同陈述。层号 2 仍是已有的 `YiMWPre.Pre`，本批没有重做。
- **一般下降**：`Reach.reachG` 对终点层号 n₀ 与记号项 t 一般。`reach`、`reach³` 是它的两个实例（`reach₂`、`reach₃`）。
- **主线终点**：
  - `tN≼EBOᴿ : ∀ m (h : HC (tN m)) → R2.Rt h ≼ readRW RW.EBOᶜ`，即对每个 m，终点闭项 ≥ ψ₀(Ω_Ω+ψ₁(Ω_{m+3})) 的参照。
  - `tω≼EBOᴿ : (h : HC tω) → R2.Rt h ≼ readRW RW.EBOᶜ`，即 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照。
  - 前提可满足：`hN m : HC (tN m)`（一切 m）与 `hΩω : HC tω` 都已造出，放在 `opaque` 里。
- **未做到的**：第一目标 `fsn tB 1`（ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₁)) 一行）仍未走通，没有编译的否定。

**对纲领与目标：**
- 六个文件都是验收文件（读记号），不进成品；树、折叠、合法性一行未改。
- 翻译账：新增的全是验收侧脚手架，没有新的树侧定义或合法性判据，不算 "树自足" 的进展。
- 只给下界，不涉及上界，不给终点的值。

**与上一路判断不同的一处（判断，未编译否定）：**
- YiPH 回报 §4 说缺口是 "`T²` 带前缀的版本，前提 `M² (ψ₂ᵗ P) β₂`"。
- 我用的前提更强：`TC (ψ P) β`，即底值 β 本身在一切上下文里满足三条结论。
- 结论 `Cl` 也多带一项遗传条件 `Her`：折到中间层号 i 的树，在层号 i 上对任意满足条件的底、任意上下文仍满足 `TC`。层号 4 起的叶处用它；层号 3 时它是 `⊤`。
- 只用 `M²` 那个较弱前提是否够，我没有试，也没有否定。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 层号 `fin (m+3)` 的带前缀锚点，一切 m、底、前缀 | `YiANLv.Lv.Anchor.anchor` | 编译定理，无前提 |
| 终点层号一般的下降 | `YiANReach.Reach.reachG` | 编译定理，无前提 |
| 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_{m+3}))，一切 m | `YiANEnd.tN≼EBOᴿ` | 编译定理，无前提 |
| 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) | `YiANLim.tω≼EBOᴿ` | 编译定理，无前提 |
| `HC` 实例 | `YiANEnd.hN`、`YiANLim.hΩω` | 编译定理 |
| 层号 `h₁ c₁` 里那个 ℕ 极限层号的第 k 个孩子是 `fin (k+2)`，一切 k | `YiANEnd.gk` | 编译定理（上一路只算过前三项） |
| 只用 `M (ψ P) β` 作前缀前提是否够 | 无 | 未试 |
| 第一目标 `fsn tB 1` | 无 | 未走通 |
| ψ₀(Ω_Ω+ψ₁(Ω_c))，c > ω | 无 | 未做（见 §4） |
| 候选 A 的 `A1S` 有限 ν 情形 | 无 | 判断：不能直接给（见 §3 末） |

##### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。六个接口一起删掉后按依赖顺序冷编，每份日志只有本模块一行 `Checking`。禁用构造、函数外延、本机路径检索为 0。文首各 3 行。

| 文件 | 总行 / 代码行 | 冷编退出码 | 内存（`+RTS -s` total in use） |
|---|---|---|---|
| `YiANFam.lagda.md` | 297 / 214 | 0 | 1098 MiB |
| `YiANKp.lagda.md` | 332 / 226 | 0 | 2155 MiB |
| `YiANLv.lagda.md` | 785 / 588 | 0 | 2459 MiB |
| `YiANReach.lagda.md` | 66 / 40 | 0 | 1939 MiB |
| `YiANEnd.lagda.md` | 245 / 166 | 0 | 2136 MiB |
| `YiANLim.lagda.md` | 163 / 116 | 0 | 2148 MiB |

冷编日志在 `<实验目录>/agents/an/` 下，文件名是 `<模块名>.cold.log`。

##### 3. 定理表

**记号与读法依据：**
- `fin n` 是有限层号；`ψᴺ i a = ψ (natT i) a ∷ []`（ψ_i(a)）；`Ωᴺ i = ψᴺ i []`（Ω_i）。
- `tN m = ψ [] (ΩΩ ∷ ψ (natT 1) (ψ (natT (m+3)) [] ∷ []) ∷ []) ∷ []`。由 `refl` 确认 `tN m ≡ ψᴺ 0 (tΩ ++ ψᴺ 1 (Ωᴺ (m+3)))` 与 `tN 0 ≡ t₃`。
- `tω = ψ [] (ΩΩ ∷ ψ (natT 1) (ψ ω′ [] ∷ []) ∷ []) ∷ []`，ω′ = ψ₀(1)。由 `refl` 确认 `fsn tω n` 是 ψ₀(Ω_Ω+ψ₁(Ω_n))，下标写成 n 个 1 的和。
- `R2.Rt h` 是 `HC` 推导沿记号基本列造的树；ψ₀(Ω_x) 的写法来自项本身。

| 名字 | 逐字的陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `M` | `M zero = M⁰`；`M (suc n) = Mᴰ (Sig (fin (suc n))) (Lw n) (λ _ → M n) (Nw n)` | 按层号递归的记号直连关系族 | Fam | 定义 |
| `Mβ` | `∀ n → M (suc n) (Ωᴺ (suc n)) (Ωt (fin (suc n)))` | Ω 树对着 Ω_{n+1} | Fam | 编译定理 |
| `cmp-gt` / `cmp-pen` | `∀ {b a} → b ≤ⁿ a → cmpᵀ (sucT (natT a)) (natT b) ≡ gt`；`∀ {a b} → suc a ≤ⁿ b → Pen (cmpᵀ (sucT (natT a)) (natT b))` | 层号是自然数时，规则 6 与规则 5Ω 的分界 | Fam | 编译定理 |
| `Pu` | `∀ {N} j (d : FD (suc N) j) (b : Tr (fin (suc N))) (nb : fin (suc N) ⊢ zero ◃ b) {t} → M (suc N) (ψᴺ (suc N) t) b → ∀ {s y} → M j s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (Up (fin j) (dn d) b nb y)` | 任意深度的上折保持 | Fam | 编译定理 |
| `Self.PF` | `∀ {P₀} → M (suc N) (ψᴺ (suc N) P₀) β → ∀ {a x} → M (suc N) a x → M (suc N) (ψᴺ (suc N) (P₀ ++ a)) (F x)` | 折到自身带前缀的保持，一切层号 | Fam | 编译定理 |
| `Self.sγ` | `∀ {P₀} → M (suc N) (Ωᴺ (suc N)) β → M (suc N) (ψᴺ (suc N) P₀) β → ∀ k → M (suc N) (gch P₀ k) (z (suc k))` | 回灌链对着 γ-链 | Fam | 编译定理 |
| `kpDrop` | `… → slot n p ≤ⁿ slot n p₀ → {X : Set} (K : …) (d : X) → kp (fin (suc n)) ε ρ p₀ (posW (fin (suc n)) p) K d ≡ d` | 目标层号不超过结点槽位层号时不保留 | Kp | 编译定理 |
| `kpKeep` | 结论 `atP Fam n p (kp (fin (suc n)) ε ρ p₀ (posW (fin (suc n)) p) (λ q cv → Ω q (λ z → Zf (cv z))) d)`，前提 `suc (slot n p₀) ≤ⁿ slot n p` 与在目标层号上造 Ω 结点的 `step` | 目标层号更高时保留 | Kp | 编译定理 |
| `Tm.gCof` / `gFsn` | `∀ i i₀ q → i ≤ⁿ i₀ → cof q ≡ cΩ (natT i₀) → cof (trmS i q) ≡ cω`；`… → fsn (trmS i q) k ≡ trmS i (fsT q (ĉ i₀ q k))` | 目标项的基本列统一沿链 `ĉ` | Kp | 编译定理 |
| `Lv.rootΩ` | `∀ n ε ρ D → Gd n D → (K : Ctx (suc n)) (V : Tr (fin (suc n))) → ⟦ K ⟧ (Ωt (fin (suc n))) ⊴ V → B0 n ε ρ D [] V` | 上下文里 Ω 树之上的 V，折到第 0 层对着 ψ₀(t+Ω₁) | Lv | 编译定理 |
| `Lv.Th` / `Lv.th` | `th : ∀ m → Th m`；`Th m` 的字段是 `tcUp`、`tcLim`、`tcLimc`、`tcNode`、`tcLeaf`、`tcMain` | 层号 `fin (m+2)` 上对一切满足条件的底的六条，经强归纳 `thB` | Lv | 编译定理 |
| `Th.tcMain` | `∀ ε ρ D → Gd (suc m) D → ∀ ε₀ ρ₀ D₀ β nβ → Ωt (fin (suc (suc m))) ⊴ β → ∀ {P₀} → TC (suc m) ε ρ D (ψᴺ (suc (suc m)) P₀) β → ∀ {a x} → M (suc (suc m)) a x → TC (suc m) ε ρ D (ψᴺ (suc (suc m)) (P₀ ++ a)) (Self.F (suc m) ε₀ ρ₀ D₀ β nβ x)` | 主归纳，带前缀；折到自身的底与折到低层的底无关 | Lv | 编译定理 |
| `Lv.Anchor.anchor` | `M⁰ (ψᴺ 0 (t ++ ψᴺ 1 (Ωᴺ (suc N)))) (ψ⊥ (suc ℓ) ε ρ B′ (Ωt (suc ℓ)))`，`N = suc (suc m)`，`ℓ = fin N` | ψ₀(t+ψ₁(Ω_{m+3})) 对着层号 `fin (m+3)` 的 Ω 树以 B′ 为底的折叠 | Lv | 编译定理（模块前提见下） |
| `Reach.reachG` | `Anchor → ∀ {ℓ} → n₀ ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → LoG ℓ ε ρ B` | 终点层号一般的下降 | Reach | 编译定理 |
| `AtN.atN` | `(h : HC (tN m)) → R2.Rt h ≼ read (ψ⊥ (fin (suc (suc (suc m)))) ε ρ B₃ (Ωt (fin (suc (suc (suc m))))))` | 对满足 `OKB` 与 `Hi` 的底，前缀 Ω_Ω | End | 编译定理 |
| `gk` | `∀ k → G k ≡ fin (suc (suc k))` | 那个 ℕ 极限层号的第 k 个孩子是 `fin (k+2)` | End | 编译定理 |
| `pathN` | `∀ m → fin (suc (suc (suc m))) ⇐ h₁ c₁` | 走到层号 `fin (m+3)` 的路径 | End | 编译定理 |
| `tN≼EBOᴿ` | `(h : HC (tN m)) → R2.Rt h ≼ readRW RW.EBOᶜ`（外层 `∀ m`） | 主线终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_{m+3})) 的参照 | End | 编译定理 |
| `A≺N` / `N≺N` | `∀ m (h : HC tA) (h′ : HC (tN m)) → O.suc (R2.Rt h) ≼ R2.Rt h′`；`∀ m (h : HC (tN m)) (h′ : HC (tN (suc m))) → O.suc (R2.Rt h) ≼ R2.Rt h′` | 参照随 m 严格递增，且都严格高于 tA 的 | End | 编译定理（对任意推导） |
| `tω≼EBOᴿ` | `(h : HC tω) → R2.Rt h ≼ readRW RW.EBOᶜ` | 主线终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照 | Lim | 编译定理 |
| `N≺ω` | `∀ m (h : HC (tN m)) (h′ : HC tω) → O.suc (R2.Rt h) ≼ R2.Rt h′` | 每个 `tN m` 的参照严格低于 tω 的 | Lim | 编译定理 |

**`Anchor` 的模块前提与可满足性：**
- 前提：`m`；`ε`、`ρ`；`B′ : Base (fin (m+3))`；`ok : OKB … B′`；`hp⊥ : M⁰ (ψᴺ 0 t) (b⊥ B′)`；`hp0 : (w : zero ≤ fin (m+3)) → M⁰ (ψᴺ 0 t) (bs B′ zero w)`。
- 实填：`AtN` 由 `OKB` 与 `Hi` 经 `sem0` 给出（t = `tΩ`）；`lowN` 在 `YiEVEnd` 的底 `B₁` 的后代上实填。

**tω 一行的证法：** `fsn tω n` 在项序上低于 `tN n`（`lt`），由 `mono<` 与 `tN≼EBOᴿ` 逐项给界，再用 `l≼` 取极限。没有用 ℕ 极限层号上的关系。

**可选项 4（判断，不是定理）：** 这一族不能直接给 `YiKCStep.A1S` 的有限 ν 情形。
- `Cl`、`Her`、`TC` 是对主线块的 `ψs`、`ψ⊥` 与 `Base` 陈述的；`A1S` 说的是候选 A 的 `φ`，层号是 `h₁ x`，与 `fin n` 只在命题意义上相等。
- 不提折到低层的部分可以复用：`M n`、`Mβ`、`Pu`、`Self.PF`、`cmp-gt`、`cmp-pen`、`gCof`、`gFsn`。
- 我只读了 `A1S` 的陈述与 `YiKC.md` §4，没有读 `φ` 的定义。

##### 4. 第一个障碍

**本批范围内没有被检查器挡住的引理。** 往上的两处没有做，以下是判断（纸面）：

1. **ψ₀(Ω_Ω+ψ₁(Ω_c))，c > ω。** 要 `Mᴰ` 在 ℕ 极限层号 `lim g` 上的实例，以及折叠穿过 `way` 两行的保持。本批的位置递归（`slot`、`atP`、`kpKeep`、`kpDrop`）只对 `fin n` 写；`kp` 在 `lim g` 上按 `way` 分支，没有对应的化简引理。
2. **第一目标 `fsn tB 1`。** 仍在 1 之后，还要 `tw 1` 层号上回退一行的分析，与 YiPH 回报 §4 第 3 条相同。我没有新的信息。

##### 5. 偏离与事故；没有读、只凭转述引用的东西

- **偏离：**
  - 第一个文件（`YiANReach`）没有在 30 分钟内写出：前面读定义与设计遗传结论用时较长。
  - 层号 2 没有并进 `Lv`，那里用的是层号 1 的一般陈述，形状不同。
- **事故，都已改正，都不是数学问题，没有堆耗尽：**
  - `InvalidPun`：隐式参数写成 `{zero}`，与 `--hidden-argument-puns` 冲突。
  - `AmbiguousName Rt`；`ClashingDefinition`：`P`、`c1`、`Good`、`b₀` 与已有名字重名，改成 `PF`、`cq1`、`Gd`、`bΩ`。
  - `TerminationIssue`：对 `M j s y`（j 是变量）做结构归纳时，检查器不认 `h k` 是子项。拆成 `M⁰` 与 `M (suc j)` 两个函数后通过；`Pu`、`Tu` 都这样写。
  - `YiANLim` 一处括号多写了一个。
- **操作：**
  - 用 `python3` 脚本改过自己的文件。
  - 临时目录里有两个试验文件 `T1.agda`、`T2.agda`（查终止性与孩子层号的形状）。没有用 `agda --interaction`。
  - `rm` 只删了自己的六个 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/`）。没有提交，没有碰别人的文件。
- **没有读或只读了一部分：**
  - 没有读：`EBOHandbook.md` 第 4 节、`IdeaLedger.md`、`YiNFOCond`、`YiTWLow`、`YiMEStep`、`YiG0*`、`YiBR*`、`YiEBShape`、`YiLSTw1` 全文、`φ` 的定义。
  - 只读了一部分：`YiKC.md` 只读 §4；`YiLSFold` 只读 `OKB`、`ok-dS`、`ψ⊥-⊵`、`ψs-⊵`；`StandardOmega`、`EboLeanBase` 只检索了用到的构造子；`EBO.lagda.md` 只读 `cmpᵀ`、`cof`、`fsT`、`γT` 几段。
  - `R2.Rt` 与 `YiMEBase.Rt` 可互换、`sem0` 的读回与 `YiLSRead.read` 一致，都是照 `YiPHEnd` 的用法由类型检查确认的，没有读定义。
  - "终点可能越过 tB"、最小见证的数值估计：没有核。

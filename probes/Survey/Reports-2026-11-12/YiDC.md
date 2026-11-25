# 封闭的关系与第 0 层出口的记号引理 (YiDC)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 06:09 至 06:18 |
| 工具调用 / agda 编译 (粗数) | 26 / 6 |
| token (usage 字段，按消息去重) | 输出 44335；新写入缓存的输入 164921；读缓存的输入 2691565；其余输入 46 |
| 写过的仓库文件 | `YiDCCheck.lagda.md`, `YiDCExit.lagda.md`, `YiDCRel.lagda.md` |
| 文件前缀 | `YiDC` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第三十七批 YiDC 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 封闭的关系 M̃ 上 Leaf (leafᴰ, 连同 rd0ᴰ, rdSᴰ, 即 no-leaf 的三条前提同时成立), LowKeep (lowKeepᴰ, 由 lowKeepᶠ 加 app≤); 出口只交带条件的 exitᴰ (见证项标准形且可数), 接口的 Base 记录没有填 (inv1 未走通); 记号引理走路 a: nf-app, 规范前缀下 nf-low; 两步折叠的见证项 ψ₀(ψ₁(Ω₃)) 不是标准形 (¬nf₂); 值 valᴰ, valᶜ 是重证, 没有新下界; 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定与原则（2026-11-14，原话）
- 战略："(c) 中间形态"；脉络 "FGH → BTBO → 更高层"。
- 本批（选项原文）："先做验收一侧，换基暂不定 (Recommended)"；"封闭的关系 + 第 0 层出口的记号引理 (Recommended)"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"。所以本路只在验收一侧工作，不改树、折叠、合法性。
- 作者对上一轮的批评："刚才花了这么多token审出来一个'不同步'问题, 然后又推翻了它, 兜兜转转原地踏步"。本路要直奔目标，不做没有必要的诊断。

###### 已知的编译事实（主审复核过）
- **有限层号上 "折到低层的保持" 已实填**：`probes/OCF/Lean/YiASProofLow`（`LFᶠ`、`lowKeepᶠ : LowKeepᶠ`，实例 `YiASIface.gradedᴬ`：上下文是前缀 t₀，`app t₀ a = ψᴺ j (t₀ ++ a)`，`Bd` 是 `GBᶠ`）。回报 `probes/Survey/Reports-2026-11-12/YiAS.md`。
- **障碍在 `Leaf`**：`YiASProofPair.no-leaf`（关系取 `YiANFam.M` 时，读法的零、后继两条与 `Leaf` 不相容）；`no-Ω₁`、`no-Ω₂`（松弛对不在 `M` 里）。机制：`M` 的结点规则要求槽位层与余尾下标字面相等，`M` 对参照一侧不向下封闭。
- **主审的自查**（临时文件，附件 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC1.agda.txt`，退出码 0）：
  - 定义 `M̃ n s x = Σ t, (s ≤ᵀ t) × M n t x`，其中 `≤ᵀ` 是 `<ᵀ ⊎ ≡`；
  - `leaf₁ : M̃ 3 (Ωᴺ 1) (Ωt (fin 3))` 成立，见证是 `Mβ 2`；
  - `app-mono : a <ᵀ b → ψᴺ j (t₀ ++ a) <ᵀ ψᴺ j (t₀ ++ b)`，用 `OCF.Align.Standard.++-mono` 加 `ar<`。
  - 读法（判断）：高层的向下封闭是语法上的，`LowKeep` 可由 `lowKeepᶠ` 加 `app-mono` 组合得到。
- **出口的要求**：
  - `YiMEBase.lower⁰ : M⁰ t x → (h : HC t) → Rt h ≼ read x`：要见证项 t 有推导 `HC`；
  - `YiCFMono.mono≤ⁿ`：要 s、t 都是标准形 `NF`，且 t 可数 `Ctbl`；
  - `EboLeanTree.hc : NF t → Ctbl t → HC t`；
  - 标准形的构造：`EboLeanBase.nf-ψ : NF u → NF a → GB u a a → NF (ψ u a ∷ [])`、`nf-Ω`、`nf-pred`；`EboLeanClosure.cl-fsn-NF`、`Ctbl-fsn`。
  - 难处：`LowKeep` 产出的见证项 ψ_j(t₀ ++ t′) 未必是标准形。

###### 要做的（按序；推进的是 "接口律在具体块上实填"）
1. **封闭的关系上实填三项**（有限层号，实例照 `gradedᴬ`，关系换成 `M̃`）：
   - `Leaf` 对松弛读法成立，读法取 "ν 是不超过 n 的自然数"，即 `no-leaf` 里的那类读法；
   - `LowKeep`（由 `lowKeepᶠ` 与 `app-mono` 组合）；
   - `Base`（第 0 层出口）。
   - 前两项预计很短，先做完交编译。
2. **第 0 层出口的记号引理**（本路的主要工作，属记号一侧的外部理论）：给出能让 `Base` 对 `M̃` 成立的引理。两条可能的路，由你选：
   - (a) **见证项的标准形封闭**：对规范的前缀（先说清哪一类前缀算规范），`ψ_j(t₀ ++ Ωᴺ n)` 一类的见证项是 `NF` 且 `Ctbl`，从而有 `HC`，再用 `mono≤ⁿ`；
   - (b) **非标准形项上的项序推出值序**：例如两边都有 `HC` 时，`s ≤ᵀ t` 推出参照值序，至少对 `LowKeep` 产出的那一类项。
   - 先在最小实例上核对：参照取 ψ₀(Ω_m)、m ≤ n，见证取有限层号塔上的项。做不到一般形式，就交最大可证的子类，以及第一个挡住的引理。
3. **用一处检验**：把三项连起来，在有限层号上得到一条值的下界。例如对每个 n，第 n 层 Ω 树折到第 0 层的值不低于 ψ₀(Ω_m) 的参照（m ≤ n），并说明它与已有的 `YiANLim`/`YiAN*` 结果的关系：是新的，还是重证。

**纪律**（作者同意的，必须照做）：
- 动手证一般形式之前，先用几十行的临时文件检查陈述的前提可满足、最小实例有意义。
- 已有引理先检索再写，不重证。
- 若发现某一步要改树、折叠或合法性的定义，停下回报，不改。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiDC`（模块名 `OCF.Lean.YiDC…`）。不改任何已有文件（包括 `YiASIface`），不碰 `src/`、`archive/`。这是验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/dc`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：三项（`Leaf`、`LowKeep`、`Base`）在封闭的关系上各到哪一步；出口引理走了哪条路、到哪一步；检验那一处的值；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**对纲领与目标的意义**：本路只在验收一侧加了三个新文件，树、折叠、合法性没有改，也没有发现需要改的地方。"不同步"在一步折叠这一类上由记号一侧的引理处理掉了（见证项是标准形）；两步折叠这一类没有处理，挡在记号一侧（见证项不是标准形），不在树一侧。值上没有新的下界。

**三项在封闭的关系 `M̃` 上各到哪一步**（实例 `gradedᴰ` = `gradedᴬ` 把 `R` 换成 `M̃`、`Rd` 换成 "ν 是不超过 n 的自然数"；`Bd`、上下文不变）：

- `Leaf`：编译定理 `leafᴰ`，无前提。同一读法下 `Rd0`、`RdS` 也是编译定理（`rd0ᴰ`、`rdSᴰ`），所以 `no-leaf` 的三条前提在 `M̃` 上同时成立。
- `LowKeep`：编译定理 `lowKeepᴰ`，无前提，由 `lowKeepᶠ` 加 `app≤` 组合，见证项从 t 变成 ψ_j(t₀ + t)。
- `Base`：**接口里的 `Base` 记录没有填**。交的是它在 `YiAbsGSuff` 里唯一的用途（`base-lower` 的结论）的带条件版本 `exitᴰ`：s 与见证项是标准形、见证项可数时，s 的参照值不高于 x 的值。

**出口引理**：走路 (a)，见证项的标准形封闭。
- 一般形式 `nf-app`（和的标准形 `nf-++` 加 `GB` 的拼接 `gb-++`）。
- 规范前缀 `Pre t₀ n`：t₀ 是标准形，`GB [] t₀ t₀`，t₀ 的末项不低于 Ω_n。其下 ψ₀(t₀ + Ω_m)（m ≤ n）是可数标准形（`nf-low`）。
- 前提可满足：空前缀 `pre[]`，前缀 Ω_k（k ≥ n）`preΩ`。
- 路 (b) 没有试。

**检验那一处**：`valᴰ` 把 `leafᴰ`、`lowKeepᴰ`、`exitᴰ` 连起来：第 n+1 层 Ω 树折到第 0 层的值不低于 ψ₀(t₀ + Ω_m) 的参照，对一切 m ≤ n+1；闭的一例 `valᶜ`（标准底、空前缀，参照 ψ₀(Ω_m)，推导 `hΩ m` 存在）。
- 与已有结果的关系：**值上是重证**。m = n+1 时就是 `lowKeepᶠ` 接 `lower⁰`；m ≤ n 时是它再接 `mono≤ⁿ`。
- 它正是 `Suff.Tower.K` 在 `M̃` 上对有限层号的内容。
- 与 `YiANLim`/`YiANEnd` 的闭项不同（那里是 `EBOᶜ`），界也低得多（ψ₀(Ω_{n+1})），不并列。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `Laws.Base` 记录在 `M̃` 上没有填；`inv1` 要交出一棵值严格更低的第 0 层树，手头没有把参照树读回 `Tr zero` 的构造 | `YiDCExit` 文首 | 未走通（没有编译否定） |
| 裸的 `M̃ 0` 上 `base-lower` 的结论对非标准形的参照不成立，例：s = ψ₀(ψ₀(Ω₅)) <ᵀ ψ₀(Ω₁) | 无 | 判断（纸面，未编译） |
| 两步折叠的见证项 ψ₀(ψ₁(Ω₃)) 有 `M⁰` 关系，但不是标准形，`exitᴰ` 用不上 | `YiDCCheck.Two.wit₂`、`YiDCExit.¬nf₂` | 编译定理 |
| `M̃` 上其余的律（`Succ`、`Node`、`Emb`、`SelfKeep`、`UpKeep`、`RdL`、`RdΩ`、`Lift`）没有填；`Zero`、`Weak`、`Lim` 没有写 | `YiDCRel` 文首 | 未做 |
| `valᴰ` 在非空前缀下没有闭的实例：`preΩ` 给出 `Pre`，但没有构造满足 `GBᶠ n B (Ω_k)` 的底 | `YiDCCheck` | 未做 |
| `gradedᴰ` 的 `Bd` 仍用 `M` 陈述，没有换成 `M̃`（换了以后 `lowKeepᶠ` 接不上） | `YiDCRel` | 设计选择，判断 |

#### 2. 文件表

路径都在 `<仓库>/probes/OCF/Lean/`。冷编是删掉自己的三个接口后依次编译，日志里各只有自己模块的一行 `Checking`。

| 文件 | 代码行（非空） | 冷编退出码 | 最大驻留 / 总内存 |
|---|---|---|---|
| `YiDCRel.lagda.md` | 60 | 0 | 1.14G / 2190 MiB |
| `YiDCExit.lagda.md` | 88 | 0 | 1.32G / 2230 MiB |
| `YiDCCheck.lagda.md` | 54 | 0 | 1.28G / 2159 MiB |

禁用构造检索为 0，文件里没有本机路径。

#### 3. 定理表

全部是编译定理，无前提。

| 名字 | 陈述（逐字） | 白话 | 文件 |
|---|---|---|---|
| `M̃` | `M̃ n s x = Σ E.T λ t → (s ≤ᵀ t) × M n t x` | 封闭的关系（定义） | Rel |
| `Rdᴰ` | `Rdᴰ n ν = Σ ℕ λ m → (ν ≡ natT m) × (m ≤ⁿ n)` | 松弛读法（定义） | Rel |
| `rd0ᴰ` / `rdSᴰ` | `Rd0` / `RdS`（`Laws gradedᴰ domsᴬ`） | 读法的零、后继两条 | Rel |
| `leafᴰ` | `Leaf`（`Laws gradedᴰ domsᴬ`） | Ω_m（m ≤ n）对着第 n 层 Ω 树，见证是 Ω_n | Rel |
| `lowKeepᴰ` | `LowKeep`（`Laws gradedᴰ domsᴬ`） | 折到低层在 `M̃` 上保持 | Rel |
| `app≤` | `∀ j t₀ {a b} → a ≤ᵀ b → ψᴺ j (t₀ ++ a) ≤ᵀ ψᴺ j (t₀ ++ b)` | 前缀下折叠项沿项序单调 | Rel |
| `exitᴰ` | `∀ {s x} (m : M̃ 0 s x) → NF s → NF (proj₁ m) → Ctbl (proj₁ m) → (h : HC s) → Rt h ≼ read x` | 第 0 层出口，条件在见证项上 | Exit |
| `nf-++` | `∀ {s a} → NF s → NF a → Join s a → NF (s ++ a)` | 末项不低于首项时和是标准形 | Exit |
| `gb-++` | `∀ {u} s a → GB u s s → GB u a (s ++ a) → GB u (s ++ a) (s ++ a)` | `GB` 的拼接 | Exit |
| `nf-app` | `∀ {u} s a → NF u → NF s → GB u s s → NF a → Join s a → GB u a (s ++ a) → NF (ψ u (s ++ a) ∷ [])` | 见证项标准形封闭的一般形式 | Exit |
| `nf-low` | `∀ {t₀ n m} → Pre t₀ n → m ≤ⁿ n → NF (ψᴺ 0 (t₀ ++ Ωᴺ m))` | 规范前缀下 ψ₀(t₀+Ω_m) 是标准形 | Exit |
| `pre[]` / `preΩ` | `∀ n → Pre [] n` / `∀ {n k} → n ≤ⁿ k → Pre (Ωᴺ k) n` | 规范前缀的两个实例 | Exit |
| `¬nf₂` | `NF (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) → ⊥` | ψ₀(ψ₁(Ω₃)) 不是标准形 | Exit |
| `lowᴰ` | `∀ n {m} → m ≤ⁿ suc n → (t₀ : E.T) (ε …) (ρ …) (B …) → GBᶠ n B t₀ → (β : Tr zero) (nβ : zero ⊢ zero ◃ β) → M⁰ (ψᴺ 0 t₀) β → M̃ 0 (ψᴺ 0 (t₀ ++ Ωᴺ m)) (ψs (fin (suc n)) ε ρ B zero (ins (pthᶠ (sb0 n))) β nβ (Ωt (fin (suc n))))` | `Leaf` 接 `LowKeep` | Check |
| `valᴰ` | 同上前提，加 `Pre t₀ (suc n)` 与 `(h : HC (ψᴺ 0 (t₀ ++ Ωᴺ m)))`，结论 `Rt h ≼ read (ψs (fin (suc n)) ε ρ B zero (ins (pthᶠ (sb0 n))) β nβ (Ωt (fin (suc n))))` | 三项连起来的值下界 | Check |
| `valᶜ` | `∀ n {m} → m ≤ⁿ suc n → (ε …) (ρ …) (h : HC (ψᴺ 0 (Ωᴺ m))) → Rt h ≼ read (ψs (fin (suc n)) ε ρ (B₀ (fin (suc n))) zero (ins (pthᶠ (sb0 n))) (Ωt zero) (Ωt-nz zero) (Ωt (fin (suc n))))` | 闭的一例 | Check |
| `hΩ` | `∀ m → HC (ψᴺ 0 (Ωᴺ m))`（`opaque`） | 参照的推导存在 | Check |
| `Two.wit₂` | `M⁰ (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) (ψs (fin 1) ε′ ρ′ (B₀ (fin 1)) zero (ins self) (Ωt zero) (Ωt-nz zero) y₁)`，`y₁` 是第 3 层 Ω 树以标准底折到第 1 层 | 两步折叠的见证项有关系 | Check |

#### 4. 第一个障碍

`LowKeep` 复合两次（3 → 1 → 0）时见证项是 ψ₀(ψ₁(Ω₃))。它有 `M⁰` 关系（`wit₂`），但不是标准形（`¬nf₂`：Ω₃ 是它的 `InG [] ` 元素，而 Ω₃ 不低于 ψ₁(Ω₃)）。

所以 `exitᴰ` 用到的两条引理都接不上：
- `EboLeanTree.hc : NF t → Ctbl t → HC t` 给不出见证项的推导；
- `YiCFMono.mono≤ⁿ` 的前提 `NF t` 不成立。

要过这一类，需要路 (b) 的引理："t 非标准形但有 `HC` 时，标准形的 s ≤ᵀ t 推出 `Rt hs ≼ Rt ht`"，至少对 t = ψ₀(t₀ + ψ_j(…)) 这一形状，并先要有这类 t 的 `HC`。没有试，写 "未走通"。

龙骨 `Tower.K` 对每一行只用一次 `LowKeep`（从 `tw n` 直接到 `ℓ₀`），那一类落在 `nf-low` 之内（判断：只在有限层号上核对过）。

#### 5. 偏离与事故

- **偏离**：任务写 "`Base`（第 0 层出口）实填"，交的不是 `Base` 记录，而是带标准形条件的出口定理 `exitᴰ`。条件放在见证项上（`proj₁ m`），没有放进关系里；判断是放进一个对层号一致的关系里以后 `LowKeep` 不再成立（见 §4），没有编译。
- 多做了一条任务外的边界定理（`¬nf₂` 与 `wit₂`，约 20 行），用来把 §4 精确到引理。
- 事故：`YiDCRel` 头两次编译退出 42（`pred-suc` 在 `OCF.Align.EBO` 里而不在 `EboLeanDef` 里；`cong Ωᴺ` 的类型写错），改后通过。另两个文件一次通过。没有堆耗尽，没有超时。
- 纪律上的偏离：一般形式 `nf-app` 没有先放临时目录试，直接写进仓库文件并在同一文件里给了前提的实例（`pre[]`、`preΩ`）。
- **没有读、只凭签名或转述引用的**：`mono≤ⁿ`、`lower⁰`、`hc` 的证明；`flatG`、`flatN`、`natB`、`z<`、`mΩt`、`gbᶜ` 只读了陈述与几行定义；`YiANLim`/`YiANEnd` 只读了文首与签名，"与它们的闭项不同" 依据文首。简报里提到的 `cl-fsn-NF`、`Ctbl-fsn` 没有用到。
- `G-++⁻` 是新写的 5 行：已有的同名引理在 `WfFsnBase`，针对另一份 `InG` 数据类型，不能直接用。

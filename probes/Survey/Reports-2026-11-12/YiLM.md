# 阶段 3：LowKeep 推到 ℕ 极限层号 (YiLM)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 06:28 至 06:40 |
| 工具调用 / agda 编译 (粗数) | 26 / 4 |
| token (usage 字段，按消息去重) | 输出 70518；新写入缓存的输入 243751；读缓存的输入 3471173；其余输入 44 |
| 写过的仓库文件 | `YiLMCheck.lagda.md`, `YiLMLow.lagda.md` |
| 文件前缀 | `YiLM` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第三十八批 YiLM 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: ω 层 lim fin (F2 块, 主线折叠) 上的关系 Mω, Leaf (leafω, leafω̃), LowKeep (LFω, lowKeepω: 从 ω 层折到任一有限层); 量化域收窄在路线 R₀, 路径, 底, 不在树上; 值 valω: ω 层 Ω 树折到第 0 层不低于 ψ₀(Ω_ω) 的参照 (F2 上新陈述, 不是新高度); 一般的 lim g 没有做, 塔上的 Λ = lim tw 的孩子是 Ω 形状层号, 要阶段 2; 两件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定与原则（2026-11-14，原话或选项原文）
- 本批（选项原文）："(3) 阶段 3：LowKeep 推到 ℕ 极限层号"，选项说明是 "与阶段 2 在数学上互不依赖，可并行；要先收窄量化域（no-least：ω 处没有公共规范树）"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"。所以本路只在验收一侧工作，不改树、折叠、合法性。
- 作者批评过上一轮："兜兜转转原地踏步"。本路要直奔目标，不做没有必要的诊断。

###### 背景：路线图（主审的判断）
终点的值定理归结为抽象接口的四项律（`Leaf`、`Lift`、`LowKeep`、`Base`），在主线的三种层号形状上都要填满：
- 已编译的骨架：`probes/OCF/Lean/YiAbsGSuff`（`Suff.Tower.K`、`endpoint`）、`YiAbsGEbo`（`ebo-end`）；带条件出口的改写 `YiExSuff`（`ExSuff.TowerE`，出口 `Exit₀`）及其实例 `YiExInst`（`exitᶠ`）。
- 律的陈述：`YiAbsGIface`（`Laws` 模块：`LowKeep`、`Leaf`、`Rd0`、`RdS`、`RdL`、`RdΩ`、`Lift`）。
- **有限层号已填**（F2 块 `YiLeg*` + 主线折叠，层号 `YiANFam.fin n`）：
  - `YiASIface`（实例 `gradedᴬ`、`domsᴬ`）；
  - `YiASProofLow`（`LFᶠ`：折到任一真子层号保持关系；`lowKeepᶠ`）；
  - `YiDCRel`（封闭的关系 `M̃ n s x = Σ t, (s ≤ᵀ t) × M n t x`；实例 `gradedᴰ`；`leafᴰ`、`lowKeepᴰ`、`rd0ᴰ`、`rdSᴰ`、`app≤`）；
  - `YiDCExit`（`exitᴰ`、`nf-low`、`¬nf₂`）。
  - 回报 `probes/Survey/Reports-2026-11-12/YiAS.md`、`YiDC.md`。
- **本路：ℕ 极限层号。** F2 的层号有 `lim : (ℕ → L) → L`（`YiLegBlock`），最小实例是 ω 层 `lim fin`。
- 已知的相关事实：
  - `YiCLCrit.no-least : ∀ y → y ⊴ ωᶜ → y ⊴ ωᵉ → M⁰ ωᵀ y → ⊥`（候选 A、精简块上：ω 处没有公共规范树）；
  - 台账 `probes/Survey/IdeaLedger.md` V139（ℕ 极限层号上的关系实例；`YiKC` 执行方判断任意 `M⁰` 推导的层号配对可能不保序，量化域要先收窄）、V143；
  - `YiANLim` 只处理记号一侧的极限（ψ₀(Ω_Ω+ψ₁(Ω_ω))），不涉及 ℕ 极限层号，和本路不重复。

###### 要做的（按序；推进的是 "LowKeep 在第二种层号形状上实填"）
0. **先做最小实例检查**，在临时目录，几十行：
   - 在 F2 块上，对 ω 层 `lim fin` 写出关系 `M̃` 的延拓应有的样子：第 ω 层的树对着记号项。
   - 写出 `Leaf`（第 ω 层的 Ω 树对着 Ω_ω，或封闭后对着 Ω_m）与 `LowKeep`（从第 ω 层折到有限的第 j 层）在这一处的陈述，确认类型正确、前提可满足。
   - 说清量化域怎样收窄才避开 `no-least` 那类反例：按形状分族的规范实例，或只取塔上实际出现的树。
   - 若陈述不出，或前提矛盾，就停下回报。
1. **关系在 ℕ 极限层号上的实例**：对 `lim g`（先 g = fin，再看一般的 g）给出关系，与有限层号上的 `M̃` 接得上。
2. **在这一类层号上证 `LowKeep`**（折到有限的低层），或给出第一个挡住的引理。若 `Leaf` 顺手可得，一并交。
3. 用一处检验：第 ω 层的 Ω 树折到第 0 层，值不低于 ψ₀(Ω_ω) 一类的参照（用 `exitᴰ` 或 `YiExInst.exitᶠ` 的出口）；说明它与已有结果的关系（新的还是重证）。

**纪律**（作者同意的，必须照做）：
- 动手证一般形式之前，先用临时文件检查前提可满足。
- 已有引理先检索再写，不重证。
- 若发现某一步要改树、折叠或合法性的定义，停下回报，不改。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiLM`（模块名 `OCF.Lean.YiLM…`）。不改任何已有文件，不碰 `src/`、`archive/`。这是验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。另一路执行方也在编译，不用 `--ignore-interfaces`，只删自己模块的 `.agdai`。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/lm`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步触发的停止条件。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：第 0 步的结论（陈述、量化域）；关系在 ℕ 极限层号上的实例到哪一步；`LowKeep`（与 `Leaf`）到哪一步；检验那一处的值；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报：ℕ 极限层号（ω 层 `lim fin`）上的关系、`Leaf`、`LowKeep`

##### 1. 判决

**对纲领与目标的意义**：`LowKeep` 与 `Leaf` 在第二种层号形状的最小实例（ω 层 `lim fin`，F2 块，主线折叠）上实填，都是无前提的编译定理。只在验收一侧新建了两个文件；树、折叠、合法性没有改，过程中也没有遇到需要改的地方。这是台账 V139 在 g = fin 上的内容。一般的 `lim g` 没有做。

**第 0 步的结论**（临时文件 `Step0.agda`，退出码 0）
- 关系的延拓：`Mω` 是 `YiMEBase.Mᴰ` 在 `Sig (lim fin)` 上的实例。槽位 (m, t) 的分支关系取 `Lw m t`，第 m 个孩子的关系取 `M m`，余尾下标取 `Nw m t`。能这样写是因为 `Pos (lim fin)` 的 (m, t) 与 `Pos (fin (suc m))` 的 t 有同一个分支类型。
- `Leaf`：参照是 Ω_ω = ψ_ω(0)，ω = ψ₀(1)。它在未封闭的 `Mω` 上就成立：Ω 树是 Ω_0+…+Ω_n 的极限，每个 Ω_n 由 "零加第 n 个孩子"（`mU mz`）对上。
- `LowKeep`：陈述类型正确；前提可满足（标准底 `B₀`、空前缀：`gbω₀`）。
- 量化域：收窄在三处，都不在树 x 上；对一切 `Mω` 推导（含 `mw`）成立。
  - 路线取相邻一步 `R₀ n = ins self`；
  - 路径取 `inl n (pthᶠ s)`；
  - 底满足 `GBω`（`GBᶠ` 的对应物）。
- 与 `no-least` 的关系（判断，只读了它的陈述与文首）：`no-least` 说的是满足 `M⁰ ω y` 的第 0 层的树没有最小元，属于把树读成层号那一处（`Lift`/`Rd`）。本路的 `Leaf` 与 `LowKeep` 不经过那一处，所以没有碰到。

**关系在 ℕ 极限层号上的实例**
- g = fin：做完（`Mω`）。
- 与有限层号接上：`gradedω` 的层号取 "有限的 n 或 ω"；有限层的关系逐字是 `YiDCRel.M̃`，ω 层取同一种封闭。
- 一般的 g：没有做。

**`LowKeep` 与 `Leaf`**
- `LFω`：从 ω 层折到任一有限层 j，编译定理，无前提。
- 接口上：`lowKeepω : Laws.LowKeep gradedω domsω`。有限层那一半是 `lowKeepᶠ` 加 `app≤`，ω 层那一半是 `LFω` 加 `app≤`。
- `leafω̃ : Laws.Leaf gradedω domsω`，ω 层的读法是 "ν 是自然数或 ω"；另有 `rd0ω`。

**检验那一处的值**
- `valω`：第 ω 层 Ω 树折到第 0 层（标准底，路径 `inl 0 self`），值不低于 ψ₀(Ω_ω) 的参照；推导 `hΩω` 存在。
- `valωᴰ`：同一闭项不低于每个 ψ₀(Ω_m) 的参照，经接口上的两条与 `exitᴰ`。
- 与已有结果的关系：
  - 在 F2 块上这是新的陈述，此前 F2 上的关系只到有限层号。
  - 界 ψ₀(Ω_ω) 不是新高度。`YiLeanValFin` 文首称另一个块上有 ψ₀(Ω_ω)（只读了文首）。
  - 与 `YiANLim` 的闭项、块、界都不同，不并列。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 一般的 `lim g` 没有做；证明用到每个孩子层上的关系族、孩子层上按路径合并的保持（`LFA`）、路线复合仍落在一族有名字的路径里（`∙≡`、`wv`）、`emb` 保持关系（`embM`） | `YiLMLow` | 未做；所需四项是判断 |
| 塔上实际出现的 ℕ 极限层号是 `Λ = lim tw`，孩子是 Ω 形状层号，要先有 Ω 形状层号上的关系族（阶段 2） | 无 | 判断 |
| ω 层作目标（折到自身 `SelfKeep`、`inlu` 路径、上折）不在量化域里：`Wlω ω _ = ⊥`，`Dn` 取空 | `YiLMCheck` | 未做 |
| `gradedω` 上其余的律没有填，包括 `RdS`、`RdL`、`RdΩ`、`Lift`、`Succ`、`Node`、`Emb`、`Base` | `YiLMCheck` | 未做 |
| `rowsω` 的 `sucL ω = ω`、`ΩL`、`lift` 是占位值（后两个与 `rowsᶠ` 相同） | `YiLMCheck.rowsω` | 设计选择 |
| 路线限定为 `R₀`（接口里是 `Gbω ω b = proj₂ (proj₁ (proj₂ b)) ≡ R₀`）；别的路线没有试 | `YiLMCheck.Gbω` | 设计选择 |
| `valωᴰ` 只在空前缀、标准底上有闭的实例 | `YiLMCheck` | 未做 |

##### 2. 文件表

| 文件 | 代码行（agda 块非空行） | 冷编退出码 | 最大驻留内存 |
|---|---|---|---|
| `probes/OCF/Lean/YiLMLow.lagda.md` | 238（全文 323） | 0 | 约 1.26 GB，14 秒 |
| `probes/OCF/Lean/YiLMCheck.lagda.md` | 159（全文 225） | 0 | 约 1.27 GB，14 秒 |

- 两个文件都是删掉自己的 `.agdai` 后冷编，日志里只有自己模块的 `Checking` 行。
- 禁用构造与本机路径检索为 0。
- 绝对路径：`<仓库>/probes/OCF/Lean/YiLMLow.lagda.md`、`<仓库>/probes/OCF/Lean/YiLMCheck.lagda.md`。
- 临时目录：`<实验目录>/agents/lm`，内有 `Step0.agda` 与各次日志。

##### 3. 定理表（都是编译定理，无前提）

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `Mω`（定义） | `Mω = Mᴰ (Sig ωL) (λ p → Lw (proj₁ p) (proj₂ p)) (λ m → M m) (λ p → Nw (proj₁ p) (proj₂ p))` | ω 层的记号直连关系 | YiLMLow |
| `leafω` | `Mω Ωω (Ωt ωL)` | ω 层 Ω 树对着 Ω_ω（未封闭的关系上） | YiLMLow |
| `gbω₀` | `GBω (B₀ ωL) []` | 标准底、空前缀满足底的条件 | YiLMLow |
| `wv` | `∀ m n → WV m n (way fin R₀ m n)` | 路线 `R₀` 下孩子之间的路径都是 `pthᶠ` | YiLMLow |
| `kcaseω` | 结论 `Q (kp ωL ε (ρc , R₀) (m , pos⁼ si) (inl n (pthᶠ s)) K d)`，两个前提与 `YiASProofLow.kcase` 相同（j ≤ i 时给 `Q d`；保留时给 `Q (K q cv)`） | ω 层槽位朝有限目标的保留判定与有限层号相同：j ≤ i 不保留，否则保留 | YiLMLow |
| `LFA` | `∀ {m j} (s : Sbᶠ m j) (t₀ : E.T) (ε : Ev (fin m)) (ρ : Rt (fin m)) (B : Base (fin m)) → GBᴬ′ m B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β → ∀ {a x} → M m a x → M j (ψᴺ j (t₀ ++ a)) (ψs (fin m) ε ρ B (fin j) (pthᶠ s) β nβ x)` | 有限层上 `LFᶠ`、`Self.PF`、`Qu` 按路径合成一条（不是新内容） | YiLMLow |
| `LFω` | `∀ {n j} (s : Sbᶠ n j) (t₀ : E.T) (ε : Ev ωL) (ρc : (k : ℕ) → Rt (fin k)) (B : Base ωL) → GBω B t₀ → (β : Tr (fin j)) (nβ : fin j ⊢ zero ◃ β) → M j (ψᴺ j t₀) β → ∀ {a x} → Mω a x → M j (ψᴺ j (t₀ ++ a)) (Fω ε ρc B s β nβ x)`，其中 `Fω ε ρc B s β nβ x = ψs ωL ε (ρc , R₀) B (fin j) (inl n (pthᶠ s)) β nβ x` | 主线折叠把 ω 层的关系送到 ψ_j(t₀ + a)，对一切推导 | YiLMLow |
| `rd0ω` | `Laws.Rd0 gradedω domsω` | 读法的零 | YiLMCheck |
| `leafω̃` | `Laws.Leaf gradedω domsω` | 接口上的 `Leaf`，有限层加 ω 层 | YiLMCheck |
| `lowKeepω` | `Laws.LowKeep gradedω domsω` | 接口上的 `LowKeep`，源是有限层或 ω 层，目标有限 | YiLMCheck |
| `hΩω` | `HC (ψᴺ 0 Ωω)` | ψ₀(Ω_ω) 的推导存在（它是可数标准形 `nfΩω`） | YiLMCheck |
| `valω` | `(ε : Ev ωL) (ρc : (k : ℕ) → Rtᴸ (fin k)) (h : HC (ψᴺ 0 Ωω)) → Rt h ≼ read (ψs ωL ε (ρc , R₀) (B₀ ωL) zero (inl 0 self) (Ωt zero) (Ωt-nz zero) (Ωt ωL))` | ω 层 Ω 树折到第 0 层的值不低于 ψ₀(Ω_ω) 的参照 | YiLMCheck |
| `valωᴰ` | `∀ m (ε : Ev ωL) (ρc : (k : ℕ) → Rtᴸ (fin k)) (h : HC (ψᴺ 0 (Ωᴺ m))) → Rt h ≼ read (同一闭项)` | 同一闭项不低于每个 ψ₀(Ω_m) 的参照，经接口两条与 `exitᴰ` | YiLMCheck |

`LFω` 的四个互递归部分：`LFω`（主体）、`gbL`（孩子层的底满足 `GBᴬ′`）、`LFU`（嵌入一行，按 `way` 的两支）、`LFΩω` 与 `chainω`（结点一行与回灌链，与 `LFᶠ` 同形）。

##### 4. 第一个障碍

本路范围内（g = fin，目标有限）没有挡住的引理，两个文件都是第一次编译就通过。

往下走的第一处缺口是把 `LFU` 推到一般的 `lim g`。那时要在孩子层 `g n` 上有 `LFA` 的对应物，即孩子层的关系族连同沿复合路径 `w ∙ rt g R l` 的 `LowKeep`。对 `Λ = lim tw`，这就是 Ω 形状层号上的 `LowKeep`（阶段 2）。这一条是判断，没有编译的否定。

##### 5. 偏离与事故

- 没有事故，没有改任何已有文件，没有提交。
- 偏离一：简报说 "先收窄量化域（no-least）"。实际 `LowKeep` 的量化域不必在树上收窄，收窄的是路线、路径、底；`no-least` 没有被用到。
- 偏离二：检验一处除了简报要求的 `exitᴰ` 出口（`valωᴰ`），多交了直接接 `lower⁰` 的 `valω`（精确对着 ψ₀(Ω_ω)，不经封闭）。
- 没有通读、只凭文首或检索引用的：
  - `YiCLCrit`（只读文首与 `no-least` 的陈述）；
  - `YiLeanValFin`（只读文首三行）；
  - `YiANLim`（只读了 ω 的标准形那几段）；
  - 台账 V139、V143（只读这两行）；
  - `YiAbsGSuff`、`YiExSuff`、`YiExInst` 没有读，本路没有接到 `Suff.Tower.K` 或 `exitᶠ`；
  - `probes/Survey/EBOHandbook.md` 第 4 节没有读（没有遇到堆墙）。

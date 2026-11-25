# 关系族的遗传封闭 (YiHC)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 09:09 至 09:28 |
| 工具调用 / agda 编译 (粗数) | 28 / 10 |
| token (usage 字段，按消息去重) | 输出 100794；新写入缓存的输入 283076；读缓存的输入 4729384；其余输入 52 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `YiHC` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第四十一批 YiHC 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 关系族的遗传封闭 Mᴴ (Mᴰ 加构造子 mc : s ≤ᵀ t → Mᴴ t x → Mᴴ s x, 低层作分支关系与孩子关系时自带封闭); 孩子取 ω+1 时兄弟孩子那一支对着 ψ₂(Ω_{ω+1}) (crit₊), 孩子取 ω 时对着 ψ₂(Ω_ω) (critω); YiLRNeg 否定的回灌链第 0 步在封闭族上成立 (chain0₊); 律全部在新族上重证 (LF, Self.PF, Qu, LFω), ω 层作目标的一组新写 (PFω, LFw, chainω, leafω); 带条件出口 exitᴴ; 写法与简报字面不同 (加构造子而非 Low/Chd 取 M̂); 八件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定与原则（2026-11-14，选项原文或原话）
- 本批本路（选项原文）："(1) 关系族的遗传封闭 V162 (Recommended)"，说明是 "结点规则里的分支关系与孩子关系都用封闭后的关系；用它重做孩子取 ω+1；核律与出口仍成立。各种写法共用"。之后作者选 "(1) 照派"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"。本路只在验收一侧，不改树、折叠、合法性。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

###### 背景：同一障碍已经三次
三次都是同一机制：余尾为 Ω₁ 的参照项（`cΩ []`），在关系里只能由槽位在第 0 层的 Ω 结点给出（`YiMEBase.Mᴰ` 的 `mΩ`），于是关系 "太严"。
- `YiASProofPair.no-leaf`（读法的零、后继与 `Leaf` 不相容）；
- `YiRLNeg.negˢ`（塔第 1 项判据在孩子取 1 处为假）；
- `YiLRNeg.chain0₊`、`noFeedᶜ`（孩子取 ω+1 时回灌链第 0 步不成立：要 `Mω (Ω_ω) (第一个回灌值)`）。
- 已有的修法：`YiMHRel.M̂ R`，即项序封闭加 ℕ 极限规则（构造子 `ĉ : s ≤ᵀ t → R t x → M̂ R s x`、`l̂ : cof s ≡ cω → (∀ k → M̂ R (fsn s k) x) → M̂ R s x`）。但它只包在最外层：`Mᴰ` 结点规则里的分支关系 `Low` 与孩子关系 `Chd` 仍是未封闭的，所以 `chain0₊` 仍挡（台账 `probes/Survey/IdeaLedger.md` V162，主审的判断）。
- 另一件事实（`YiSMValue.tw-norow`）："经指定孩子" 那一行在塔各项上不触发。本路与那一行无关，不要碰它。

###### 已有的东西（主审复核过；先读，不重证）
- `YiMEBase.Mᴰ S Low Chd Nu`（构造子 `mz`、`m1`、`mL`、`mΩ`、`mU`、`mw`）；`lower⁰`。
- 精简块上的族：`YiCLFam.M n`（读回层号 `fn n`）、`YiLRLow`（`Lim`、`Mω`、`Fold.LFω`；ℕ 极限读回层号）、`YiLRBridge`、`YiLRNeg`（`M₊`、`Mβ₊`、`keep₊`、`feed₊`、`chain0₊`）。
- 新折叠上的保持：`YiRBFam`（`Self.PF`、`LF`、`Qu`）。主线候选折叠是 `YiSMFold`（重导出 `YiRBSib`），对塔它与原折叠逐字相同。
- `YiMHRel`（`M̂`、`keep`、`weak`、`Ex`、`exit̂`）、`YiMHLean`（`lowKeep̂`、`exitᴺ`、`synˢ`）、`YiMHFin`（F2 上的接口实例）。
- 回报：`probes/Survey/Reports-2026-11-12/YiMH.md`、`YiLR.md`。

###### 要做的（按序；推进的是 "律在 Ω 形状与 ℕ 极限层号上不被 '关系太严' 挡住"）
0. **最小实例检查**，在临时目录：
   - 写出遗传封闭的族：每一层的 `Mᴰ` 里，`Low` 与 `Chd` 取低层关系的封闭（`M̂` 那样），最外层再封闭一次。
   - 在 `chain0₊` 那一处，即 `ℓ₊` 的 ω 槽位、回灌链第 0 步，确认新族下这一步可证。
   - 注意：封闭使 `Low` 变大，`mΩ` 的前提（对一切满足 `Low` 的 η、c）也随之变强。核对 `Mβ₊` 一类的 Ω 树对着 Ω_ν 是否仍可证。
   - 若有一处不成立，就停下回报，精确到引理。
1. **重做孩子取 ω+1**：兄弟孩子写法（`gˢ`），孩子 `suc ωᶜ`，判据对着 ψ₂(Ω_{ω+1})（在新族上陈述）。
2. **律与出口**：在新族上证折到低层的保持（照 `YiRBFam.LF`、`YiLRLow.LFω`）与 Ω 树对着 Ω_ν；第 0 层出口照 `YiMHRel.exit̂`。说明哪些证明能整段复用，哪些要改。
3. 说明与已有结果的关系（新的、重证、还是替代）。

**纪律**（作者同意的，必须照做）：
- 动手证一般形式之前，先用临时文件检查前提可满足。
- 已有引理先检索再写，不重证；搬来的证明在文首写明来源。
- 若某一步要改树、折叠或合法性的定义，停下回报。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiHC`（模块名 `OCF.Lean.YiHC…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰另一路的前缀 `YiNR`。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。另一路也在编译，不用 `--ignore-interfaces`，只删自己模块的 `.agdai`。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量，执行前核对路径。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/hc`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步触发的停止条件。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：第 0 步的结论；ω+1、律、出口各到哪一步；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

### YiHC 回报：关系族的遗传封闭 (V162)

#### 1. 判决

**对纲领与目标的意义**：本路只在验收一侧，树、折叠、合法性一行未改，没有新增树侧定义。新增的是一条验收关系 `Mᴴ` 和它上面的保持定理。它让 "余尾 Ω₁ 的参照项只能由第 0 层槽位的 Ω 结点给出" 这一机制不再挡住 Ω_ω 与 Ω_{ω+1} 形状的判据。对 "让树自足" 不加分也不减分。判据是封闭关系里的陈述，还不是序数值的陈述：值要经出口，出口带条件 `Exᴴ`（见问题表）。

**第 0 步（临时文件 `Step0.agda`，退出码 0）**：通过，没有触发停止条件。
- `chain0₊` 那一处在新族下可证：`Mω (Ω_ω) (next⁺ (ω 层的 Ω 树))`，由 `mL` 加每项一次封闭（Ω_k ≤ Ω_{k+2}）给出。
- 封闭使 `mΩ` 的前提变强之后，Ω 树对着 Ω_ν 仍可证：`Mβ`（Ω_{n+1}）、`MβB`、`Mβ₊`（Ω_{ω+1}）都编译通过。原因是孩子关系同样封闭，`mU mz (mw l ◃s)` 原样成立。

**采用的写法与简报字面不同（偏离，见 §5）**：没有用 "`Mᴰ` 的 `Low`、`Chd` 取 `M̂`，最外层再包一次"，而是给 `Mᴰ` 加一条构造子 `mc : s ≤ᵀ t → Mᴴ t x → Mᴴ s x`。低层的 `Mᴴ` 作分支关系与孩子关系时自带封闭；`ĉ` 即 `mc`，`l̂` 即 `mL`，外层再包 `M̂` 不增加什么（`ofM̂`，编译）。

**ω+1（第 1 步）：做成，编译定理，无前提。**
- `crit₊ : M 2 (ψᴺ 2 (E.Ωt (sucT ωᵀ))) (proj₁ (gˢ (suc ωᶜ)))`，即兄弟孩子写法在孩子 `suc ωᶜ` 处的那一支对着 ψ₂(Ω_{ω+1})。
- 为此新写了 ω 层作目标的部分（`YiLR` 回报里标 "未做" 的那几条）：上折进 ω 层、ω 层折到自身、ω+1 层折到 ω 层、ω+1 层折到有限层、ω 槽位的回灌链。
- 顺带得到 `critω`：孩子 `ωᶜ` 处对着 ψ₂(Ω_ω)，由 `leafω` 经 `LFω` 一步给出。

**律与出口（第 2 步）：做成。**
- 折到低层与折到自身的保持在新族上全部成立：`Qu`、`Self.PF`、`LF`、`Lim.Fold.LFω`，陈述与原定理逐字相同，只是 `M` 换成封闭族。
- 复用情况：原证明整段照搬，每个对推导的归纳加一行 `mc`（用 `YiDCRel.app≤`）；`YiLRBridge` 的对应物一行不加；与关系无关的定义（路径、槽位视图、`feedF`、`cb`、`τ` 等）直接引用原文件。
- 出口 `exitᴴ` 对推导直接归纳，条件 `Exᴴ` 是每个 `mc` 结点上两项为标准形且较大者可数。条件可满足的一例：`exit-ωᴴ`。

**与已有结果的关系（第 3 步）**
- 新的：`Mᴴ` 与族；`crit₊`、`critω`、`chain0₊`（肯定）；ω 层作目标的 `PuT`、`upB`、`PFω`、`LFw`、`chainω`、`leafω`。
- 重证（陈述同形，关系换成封闭族）：`Mβ`、`Pu`、`Qu`、`Self.PF`、`LF`、`sΩ-LF`、`liftC`、`liftU`、`LFAB`、`LFω`、`valᶜ`、`valᵉ`。
- 替代：`YiMHRel.M̂` 加 `YiMHLean` 的 `lowKeep̂`、`selfKeep̂`、`synˢ` 这条 "只包最外层" 的路，在需要封闭的分支关系处由本族替代。
- 不冲突：`YiLRNeg.chain0₊`、`noFeedᶜ`、`noLeafᶜ` 否定的是未封闭的 `Mω`，仍然成立；本路的 `chain0₊`、`leafω` 是同一陈述在封闭族上的肯定。
- 没有碰 "经指定孩子" 那一行。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `crit₊`、`critω` 折到第 0 层之后的推导上 `Exᴴ` 是否成立没有查；`YiMHLean.¬ex-low0` 的同类边界（见证项如 ψ₀(ψ₂(Ω₃)) 不是标准形）预计同样出现 | `YiHCRel.Exᴴ` | 判断，未查 |
| 高层未封闭族 `YiCLFam.M (suc n)` 到封闭族没有映射（封闭使 `mΩ` 前提变强），旧族上的高层判据（`YiRBCrit.sib-at`、`YiRLCrit.finˢ` 等）不能直接搬，要在新族上重证；本路没有重证这些 | `YiHCCheck` 文首 | 未做 |
| 简报字面的写法（`Low`、`Chd` 取 `M̂`）没有做；我的纸面分析是它在 `m-next` 与 `mU` 行走不通 | §4 | 判断，未走通（无编译否定） |
| `crit₊` 只对具体的树 `suc ωᶜ`；一般 `Can` 的孩子、ω·2 以上未做；`Plus` 的量化域是 "孩子为有限读回层号的 ℕ 极限层，且 k ≤ d k" | `YiHCPlus.Plus` 的参数 | 未做 |
| `Mᴴ` 与 "`M̂` 插在 `Low`、`Chd`" 的族之间的包含关系没有比较 | — | 未做 |
| 保持引理现在又多一份副本（V163 的合并更有必要）；`UpT.PuT` 已按顶层参数化，可吸收 `YiHCFam.Pu` | `YiHCOmega.UpT` | 判断 |

#### 2. 文件表

全部在 `<仓库>/probes/OCF/Lean/`。代码行按 agda 块内非空行计。八个文件删掉自己的 `.agdai` 后按依赖顺序冷编，日志各只有自己模块的一行 `Checking`。禁用构造与本机路径检索为 0。

| 文件 | 代码行（总行） | 冷编退出码 | 内存（max residency / total in use） | 时间 |
|---|---|---|---|---|
| `YiHCRel.lagda.md` | 123 (166) | 0 | 1.02 GB / 1702 MiB | 11.0 s |
| `YiHCFam.lagda.md` | 130 (172) | 0 | 1.32 GB / 2286 MiB | 14.0 s |
| `YiHCFold.lagda.md` | 250 (307) | 0 | 1.36 GB / 2399 MiB | 15.9 s |
| `YiHCBridge.lagda.md` | 110 (160) | 0 | 1.33 GB / 2334 MiB | 15.9 s |
| `YiHCLim.lagda.md` | 202 (264) | 0 | 1.36 GB / 2342 MiB | 15.7 s |
| `YiHCOmega.lagda.md` | 171 (222) | 0 | 1.32 GB / 2243 MiB | 15.7 s |
| `YiHCPlus.lagda.md` | 245 (304) | 0 | 1.40 GB / 2355 MiB | 16.1 s |
| `YiHCCheck.lagda.md` | 62 (93) | 0 | 1.40 GB / 2352 MiB | 15.7 s |

临时文件：`<实验目录>/agents/hc/Step0.agda`（退出码 0），同目录下有各文件的日志（`*.cold.log` 是冷编日志）。

#### 3. 定理表

档位全部是编译定理，无前提，除非注明。

**`YiHCRel`**
- `data Mᴴ S Low Chd Nu`：构造子 `mz`、`m1`、`mL`、`mΩ`、`mU`、`mw` 逐字同 `YiKVRel.Mᴰ`，另加 `mc : ∀ {s t x} → s ≤ᵀ t → Mᴴ S Low Chd Nu t x → Mᴴ S Low Chd Nu s x`。
- `Gen.m-add : ∀ {p b s y} → M (p ∷ []) b → M s y → M (p ∷ s) (b + y)`，以及 `m-next`、`m-cum`、`m-right`、`m-zl`（陈述同 `YiKVRel.Gen`）。白话：加法、`next`、累加对封闭关系仍成立。
- `exitᴴ : ∀ {s x} (m : M⁰ s x) → Exᴴ m → (h : HC s) → Rt h ≼ readRW x`。白话：第 0 层出口；`Exᴴ (mc {s} {t} _ m) = NF s × NF t × Ctbl t × Exᴴ m`，其余结点递归。

**`YiHCFam`**
- `M : (n : ℕ) → E.T → Tr (fn n) → Set`，`M (suc n) = Mᴴ (Sig (fn (suc n))) (LwP (suc n)) (λ _ → M n) (Nw n)`。
- `Mβ : ∀ n → M (suc n) (Ωᴺ (suc n)) (proj₁ (Ωt (fn (suc n))))`。白话：Ω 树对着 Ω_{n+1}。
- `Pu : ∀ {N} j (d : FD (suc N) j) (b : Tr⁺ (fn (suc N))) {t} → M (suc N) (ψᴺ (suc N) t) (proj₁ b) → ∀ {s y} → M j s y → M (suc N) (ψᴺ (suc N) (t ++ s)) (proj₁ (Up (fn j) (dn d) b y))`。

**`YiHCFold`**
- `Self.PF : ∀ {P₀} → M (suc N) (ψᴺ (suc N) P₀) (proj₁ β) → ∀ {a x} → M (suc N) a x → M (suc N) (ψᴺ (suc N) (P₀ ++ a)) (F x)`
- `LF : ∀ {n j} (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (s : Tp n j) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀ → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β) → ∀ {a x} → M (suc n) a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) o r B (fn j) (tp s) β x))`
- `Qu`、`kcase`、`kcaseT`、`chain`、`sΩ-LF`、`liftC`、`liftU`：陈述同 `YiRBFam`。

**`YiHCBridge`**：`LFAB`、`embB`、`kcaseB`、`kcaseB₂`、`feedB`、`MβB`、`mkGBB`，陈述同 `YiLRBridge`。

**`YiHCLim`**
- `Lim.Fold.LFω : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β) → ∀ {a x} → Mω a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (F (inc n v) β x))`
- `valᶜ : ∀ n → M 2 (ψᴺ 2 (Ωᴺ (sh n))) (proj₁ (gˢ ωᶜ))`，`valᵉ` 同形。

**`YiHCOmega`**
- `UpT.PuT : ∀ j (d : FD N j) (b : Tr⁺ Λ) {t : E.T} → MT (ψᵘ u t) (proj₁ b) → ∀ {s y} → M j s y → MT (ψᵘ u (t ++ s)) (proj₁ (Up (fn j) (dnT d) b y))`。模块参数：顶层 Λ 与其上的关系、下标 u、链 `D₀ : Dn Λ (fn N)`，以及前提 `hN`、`hL`（`fn N` 的槽位搬进 Λ 后的读法）、`hP : ∀ k → Pen (cmpᵀ (sucT (natT k)) u)`。前提可满足：`Tω.upB` 的实例里三条分别是恒等、恒等、`penω`。
- `Tω.leafω : (∀ k → k ≤ⁿ d k) → Mω (E.Ωt ωᵀ) (proj₁ (Ωt Lω))`。白话：Ω_ω 对着 ω 层的 Ω 树。前提由 `le-sh` 满足。
- `Tω.upB : ∀ m (b : Tr⁺ Lω) {t : E.T} → Mω (ψω t) (proj₁ b) → ∀ {s y} → MB (G m) (eG m) s y → Mω (ψω (t ++ s)) (proj₁ (Up (G m) (down stop m) b y))`
- `Tω.Self.PFω : ∀ {P₀} → Mω (ψω P₀) (proj₁ β) → ∀ {a x} → Mω a x → Mω (ψω (P₀ ++ a)) (F x)`，其中 `F x = proj₁ (ψ Lω (R , oc) r B Lω self β x)`，`ψω = ψᵘ ωᵀ`。白话：ω 层折到自身，ψ_ω(P₀+a) 的下界被保持。

**`YiHCPlus`**（`Plus` 的参数：`Lim` 的五个参数加 `dk : ∀ k → k ≤ⁿ d k`、`oc : (k : ℕ) → Ok (G k)`；`Fold₊` 的参数：`r : Rb ℓ₊`、`B : Base ℓ₊`、`t₀`、`gb : GB₊ B t₀`）
- `Plus.Mβ₊ : M₊ (E.Ωt (sucT ωᵀ)) (proj₁ (Ωt ℓ₊))`
- `Plus.gb₊₀ : GB₊ (B₀ ℓ₊) []`。白话：标准底满足底的条件。
- `Fold₊.LFf : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β) → ∀ {a x} → M₊ a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (Ff v β x))`，`Ff v β x = ψ ℓ₊ o₊ r B (fn j) (inc tt (inc n v)) β x`。
- `Fold₊.LFw : (β : Tr⁺ Lω) → Mω (ψω t₀) (proj₁ β) → ∀ {a x} → M₊ a x → Mω (ψω (t₀ ++ a)) (proj₁ (Fw β x))`，`Fw β x = ψ ℓ₊ o₊ r B Lω (inc tt self) β x`。
- `Fold₊.chainω : ∀ {a ν} {g : Tr Lω → Tr ℓ₊} → cof a ≡ cΩ ν → ν ≡ ωᵀ → (∀ η c → Mω η c → M₊ (fsT a η) (g c)) → ∀ k → Mω (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k))`。白话：ω 槽位的回灌链对着 γ-链，对一切 k。
- `lvl₊ : ℓˢ (suc ωᶜ) ≡ P₊.ℓ₊`，`ok₊ : oˢ (suc ωᶜ) ≡ P₊.o₊`，`path₊ : wˢ (suc ωᶜ) ≡ inc tt (inc 0 self)`，都是 `refl`。
- `chain0₊ : Wᶜ.Mω (E.Ωt ωᵀ) (proj₁ (next⁺ (Ωt Wᶜ.Lω)))`。白话：`YiLRNeg.noFeedᶜ` 否定的那一条，在封闭族上成立。
- `crit₊ : M 2 (ψᴺ 2 (E.Ωt (sucT ωᵀ))) (proj₁ (gˢ (suc ωᶜ)))`

**`YiHCCheck`**
- `of⁰ : ∀ {s x} → K.M⁰ s x → M⁰ s x`，`ex-of⁰ : ∀ {s x} (m : K.M⁰ s x) → Exᴴ (of⁰ m)`。白话：第 0 层旧推导进封闭族，且出口条件自动成立。
- `ofM̂ : ∀ n {s x} → M̂ (M n) s x → M n s x`
- `critω : M 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gˢ ωᶜ))`
- `ωᴴ : M⁰ ωᵀ ωᶜ`，`ex-ωᴴ : Exᴴ ωᴴ`，`exit-ωᴴ : (h : HC ωᵀ) → Rt h ≼ readRW ωᶜ`

#### 4. 第一个障碍

本路的三步里没有被检查器挡住的引理。剩下的第一个障碍在出口一侧，不在封闭：

- `crit₊` 要变成序数值的陈述，需把它经 `LF` 折到第 0 层，再对所得推导证 `Exᴴ`。每个 `mc` 结点被 `app≤` 推成 ψ_j(t₀ + s) ≤ ψ_j(t₀ + t)，这两项须是标准形。`YiMHLean.¬ex-low0` 已对 `M̂` 的同类推导给出反例（ψ₀(ψ₂(Ω₃)) 不是标准形）。本路没有在 `Mᴴ` 上重查这一条，所以写成判断。

关于简报字面的写法（`Low`、`Chd` 取 `M̂`），我的纸面分析（未编译，只能写 "未走通"）：
- 保持定理的 `mU` 行里孩子的证据是 `M̂ (M n) s₁ y`；拆出 `ĉ le m` 后只得到关于较大项 t 的结论，而未封闭的外层关系不向下封闭，所以结论只能落在 `M̂` 里。
- 结论落在 `M̂` 后，`m1` 行的 `m-next` 要从 `M̂ (p ∷ []) b` 造出 `replicate k p` 对着 b·k。叶子的见证项 t 只知道 p ∷ [] ≤ᵀ t；t = p ∷ r（r 非空）时 p ∷ p 与 t ++ t 的比较取决于 r 的首项，一般不成立。
- 把 `mc` 放进归纳定义后，归纳始终在 "a" 的推导上做，`mc` 与 p ∷ ·、ψ_j(t₀ + ·) 这两个单调的上下文交换（`∷≤`、`app≤`），这个问题不出现。

#### 5. 偏离与事故；没有读、只凭转述的东西

**偏离**
- 关系的写法与简报字面不同（见 §1、§4）。它仍只在验收一侧，没有改树、折叠、合法性。若主审要字面的那一种，需另派，并先处理 §4 的 `m-next`。
- 简报第 1 步只要求 ω+1 的判据；为它新写了 ω 层作目标的一组引理（`YiHCOmega`），这是 `YiLR` 回报里列为 "未做" 的部分。
- `critω`、`of⁰`、`ofM̂`、`exit-ωᴴ` 是简报外加的小检验。

**事故**
- `Step0.agda` 第一次编译退出 42：我随手写的一个 `pos⁰` 草稿类型不对，与第 0 步无关，删掉后通过。仓库里的八个文件都是第一次编译即通过。
- 六个搬运文件由脚本从原文件生成：截取原代码段、换导入、插入 `mc` 行。生成后逐个编译；文字段落保留了原文件的小节说明。
- 最后的冷编命令超过 120 秒被转到后台跑完（退出码 0），期间没有并行启动第二个 agda。
- 没有改任何已有文件；只删过自己八个模块的 `.agdai`（字面路径）。

**没有读或只读了一部分**
- 未读：`Reports-2026-11-12/YiMH.md`；`YiMHFin`；`YiSMFold`、`YiSMValue`（只依简报所述 "对塔与原折叠逐字相同"、`tw-norow`）；`EBOHandbook.md` 第 4 节（没有遇到堆墙）。
- 只检索了签名：`YiRBCrit`、`YiRLCrit`、`YiDCRel`、`YiANFam`、`YiCFMono`、`EboLeanBase`、`EBO`。
- `IdeaLedger.md` 只读了 V162 到 V164 三行。
- 没有把结果填进抽象接口（`YiAbsGIface.Laws` 一类），也没有碰 `YiNR` 前缀。

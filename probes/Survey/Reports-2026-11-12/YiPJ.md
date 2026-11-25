# 用带等式的写法重做路径接口（攀爬） (YiPJ)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十五批；外部模型，作者转发 |
| 前缀 | `YiPJ` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：用带等式的写法重做路径接口，补完整的后继一步（攀爬，前缀 YiPJ）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 本路（选项原文）："(1) 攀爬：用带等式的写法重做路径接口"，说明是 "照 YiLRBridge.LFAB 把层号写成带等式、对等式作 J，补 '任意有限路径交给保持引理'，再证完整的 Q 与后继一步在 ω+1 处、一般 ℕ 极限孩子与 ω+n"。
- 主线：精简块 `YiRW*` 加最小比较表（`YiTBRow.ψ` 配 `YiMTTab.rbᶻ`）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状"。本路只在验收一侧，不改树、折叠、合法性。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **目标陈述**（`probes/OCF/Lean/YiLTLift`）：
  - `Q t ℓ`：层 ℓ 的 Ω 树，以任一 `OKB` 的底、沿一致路径折到第 0 层，对着记号项 t，**对一切合法性证据 `Ok` 与表**。
  - `StepS`（第 191–193 行）是后继一步；`lift-red : StepS → Lift₁`。
- **上一批（YiSS，回报 `probes/Survey/Reports-2026-11-12/YiSS.md`）**：
  - 已证：主线实际孩子 ω+1 那一支（`YiSSCheck.Main.kidω+1`）；ω 层折到自身对任意 `Ok`（`YiSSOmega.Omega.Self.PFω`）；ω+1 沿一致路径到 0，条件是 `Down vs`（`YiSSUniform.Uniform.FoldU.LFu`），规范实例由 `YiSSCheck.Canon.child` 满足。
  - 未走通：完整 `Q`（量化一切 `Ok`，其中相邻路径未必是规范形）。
  - 卡点：把**任意实际有限路径**交给按数字 n, j 索引的保持接口。两次设计（附件 `probes/Survey/Reports-2026-11-12/attachments/YiSS-YiSSPath.agda.txt` 的 `CP n j u`、`YiSS-YiSSPath2.agda.txt` 的 `FP u`）都在 `self` 分支报 `SplitError.UnificationStuck`（`fn j`、`fn n` 的端点反演）。
  - 编译否定 `YiSSScope.no-all-Sb`：任意相邻路径不能都读成字面的 `Sb` 路径。所以不能先把路径读成规范形式。
- **摆脱侧上一批（YiTS）**：一般情形的桥带条件 `Low`（下层沿相应路径折到第 0 层的保持），卡在同一接口（`YiTSBridge.AtStep`）。
- **主审建议的写法**（判断，未编译）：`YiLRBridge.LFAB`（第 102–105 行）把层号写成 `(ℓ : L) (e : ℓ ≡ fn N)`，对等式作 J（`LFAB _ refl … = LFA …`），回避在 `fn n` 上合一。但 `LFAB` 仍要求 `τ e v ≡ pth s`，即路径读成规范形式。本路要做的是：**层号与目标都写成带等式的抽象层号**（例如 `(ℓ : L) (e : ℓ ≡ fn N)`、`(j′ : L) (e′ : j′ ≡ fn j)`），**直接对任意路径 `v : j′ ≤ ℓ` 结构归纳证保持**，不先读成 `Sb`。

#### 要做的（按序）
0. **最小实例检查**，在临时目录（纯 `.agda`）：在 `self` 分支（以前卡住的地方）上，按带等式的写法写出接口的那一个子句，确认通过检查器。再在 `inc`、`inu` 各一个子句上确认。不通过就停下回报，附首个错误。
1. **接口**：任意有限路径的保持（有限读回层号之间，对一切路径），按带等式的写法证完。
2. **完整 Q 在 ω+1 处**：`Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc ωᶜ))`，即对一切 `Ok`。
3. **后继一步的推广**：x 为一切 ℕ 极限形状的树（`lim f a`）时 η = ω+1 的 `StepS`；再推到 ω+n。做到哪一步算哪一步。
4. 若 `StepS` 对 `lift-red` 所需的全部情形成立，给出 `Lift₁` 与塔第 1 项那条值下界（`k1-redᶻ` 的前提去掉）；否则交第一个挡住的引理，精确到 x 的形状。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiPJ`（模块名 `OCF.Lean.YiPJ…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行的另两路前缀 `YiCD`、`YiDD`。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - 同时只跑一个 agda，堆上限 8G（另两路也在编译）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
- 不在你的临时目录与你前缀的新文件之外删除任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步不通过。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；接口、完整 Q、推广、`Lift₁` 各到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理与 x 的形状。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。



## 本会话主审复核（2026-11-14）

13 件、796 同口径代码行；主审分两批逐件删自身接口、5G 独立冷编全 0，各仅自身 Checking，源码冻结期间哈希不变。禁用构造、洞、本机路径、Funext 命中 0。已读全部源码及完整原文回报；全称有限路径、任意实际 Ok 的 qω+1、有限读回分支的 FinLim.step 均成立，非有限分支缺口与 ω+2 精确列出。no-finite-readback 只否定有限读回字段，不否定 StepS；Check.closed-bound 只为 M⁰ 关系，没有增补 Exᴴ 或冒称序数值出口。本路按第 3 步“做到哪一步算哪一步”和第 4 步允许交首个引理结束，未触发数学停止条件。

## 回报原文（本会话执行）

### YiPJ 完整回报（原文）

本路在验收一侧补上了上一批所缺的任意有限实际路径保持，并得到 ω+1 处对一切 Ok、比较表、OKB 底及一致路径的完整 Q。树、折叠、合法性没有改。它消除了这一站的路径规范形前提，没有把验收证明变成不读记号的定义；本路全部模块明确属于验收一侧。

第 0 步已在纯 Agda 临时文件 YiPJ0.agda 中完成：源与目标均为抽象层号加等式，self/inc/inu 结构子句通过；后续完整关系保持 all 也使用同一双端点写法，未把实际路径先重化为 Sb。Point 的 proof-irrel 只证明“等于同一有限读回层号”的等式证书唯一性，由该有限相等命题可判定性构造，不是全局 K 或函数外延。

#### 任务判决与问题表

| 问题 | 位置 | 判决 | 档 |
|---|---|---|---|
| 第 0 步 self/inc/inu | 临时 YiPJ0；仓库 Path | 三种子句均通过，未触发第 0 步停止 | 编译定理；闭实例为有限测试 |
| 任意有限路径保持 | All.all / Pres | 完成；两端均抽象带等式，直接递归实际路径 | 编译定理 |
| 完整 Q 在 ω+1 | Q.qω+1 | 完成；实际 Ok 中的 R 任意 | 编译定理 |
| 一般 ℕ 极限孩子 | LimStep.FinLim.step | 对一切合法 f/a，若每个孩子有有限读回等式，则完成后继结论；共尾界由合法性导出 | 编译定理，范围见参数 |
| 含非有限孩子的一般 lim | Gap.x = lim(ωᶜ, suc ωᶜ, …) | M⁰ω 和 Q 前提可满足；缺相应非有限孩子的保持接口 | 未走通（不是否定 StepS） |
| ω+n | n=1 的完整 Q 已得；n=2 为 Gap.Missingω+2 | 未得对所有 n 的后继归纳 | 判断/未证命题；不称否定 |
| Lift₁ / k1-redᶻ | YiLTLift 的 StepS 归约 | 未取得完整 StepS，所以没有消去此前提 | 未走通 |

“无有限读回”仅否定本次有限接口的一个字段，绝不推出 MissingLimStep 或 StepS 为假。未把两个不同命题混写。

闭项和值分开：Check.closed 是最小比较表下的合法第 0 层闭项；closed-bound 是它对 ψ₀(Ω_{ω+1}) 的 M⁰ 关系定理。没有补 Exᴴ 出口证据，没有声称 Rt ≼ readRW 的无条件序数值定理、互相 ≼、逐项基本列一致或整棵塔第 1 项达到 EBO。无完整 StepS，故也没有新交 k1-redᶻ 的无前提版本。

#### 文件与自冷编

代码行数只计 Agda 围栏内非空且非整行注释行。每件均单独删自己的确切接口文件后编译，-M5G，退出码 0，Checking 只有该模块本身，无警告。前三件冻结后未再修改，主审另已独立冷编通过；其余从 cold-final.json 取数。

| 文件（OCF.Lean 前缀） | 代码行 | 冷编退出码 | 最大驻留字节 | 冷编日志 |
|---|---:|---:|---:|---|
| YiPJAcross.lagda.md | 51 | 0 | 1,427,770,544 | YiPJAcross-cold.log |
| YiPJAll.lagda.md | 43 | 0 | 1,393,639,680 | YiPJAll-cold.log |
| YiPJCase.lagda.md | 52 | 0 | 1,388,643,728 | YiPJCase-cold.log |
| YiPJCheck.lagda.md | 41 | 0 | 1,450,300,032 | YiPJCheck-cold.log |
| YiPJDown.lagda.md | 113 | 0 | 1,363,567,008 | YiPJDown-cold.log |
| YiPJEmb.lagda.md | 37 | 0 | 1,406,376,736 | YiPJEmb-cold.log |
| YiPJGap.lagda.md | 42 | 0 | 1,398,699,064 | YiPJGap-cold.log |
| YiPJLim.lagda.md | 187 | 0 | 1,347,100,400 | YiPJLim-cold.log |
| YiPJLimStep.lagda.md | 82 | 0 | 1,406,064,048 | YiPJLimStep-cold.log |
| YiPJPath.lagda.md | 31 | 0 | 975,177,176 | YiPJPath-cold.log |
| YiPJPoint.lagda.md | 43 | 0 | 1,379,097,128 | YiPJPoint-cold.log |
| YiPJQ.lagda.md | 44 | 0 | 1,450,327,184 | YiPJQ-cold.log |
| YiPJRef.lagda.md | 30 | 0 | 1,421,639,888 | YiPJRef-cold.log |

仓库目录：<仓库>/probes/OCF/Lean/。实验与全部日志：<实验目录>/。汇总：cold-core.json、cold-final.json、audit.json。源码 SHA256 在 audit.json。没有修改前缀外的文件，也没有提交或推送。

#### 定理表

下列编译定理的关键签名逐字放在后文；模块参数同样列出，不能省去有限读回范围或底条件。

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| bound | 任意实际有限路径给出数字端点界 | Path | 编译定理 |
| proof-irrel / index-eq | 固定有限终点的等式证书唯一；两个有限读回数字相同 | Point | 编译定理 |
| cases | 对实际路径的保留/取极限分派给出准确层级与分支关系 | Case | 编译定理 |
| DLF | 后继源的一步保持，使用子路径保持作为参数 | Down | 编译定理 |
| all | 对任意有限实际路径保持 MB | All | 编译定理 |
| liftM / slotJ | 任意有限实际嵌入路径保持关系与槽位读法 | Emb | 编译定理 |
| caseK / acrossK | 分派接到记号比较 gt/keep，不要求实际路径规范形 | Across | 编译定理 |
| Reference.Rref / canRef | 从任意实际路径只取数字界，另造一个参考路径 | Ref | 编译定理；不宣称 R=Rref |
| Generic.Fold.LFω / FoldU.LFu | 有限读回孩子的极限层，沿任意实际 R 下折保持 | Lim | 编译定理 |
| qω+1 | ω+1 处完整 Q，对一切 Ok | Q | 编译定理 |
| FinLim.step | 有限读回分支的任意合法 lim 的后继，完整 Q | LimStep | 编译定理 |
| q-even | ωᵉ=lim(0,2,4,…) 的后继处同样完整 Q | Check | 编译定理（实例） |
| gb₀ | GBB 的基底 B₀、空前缀实例可满足 | Check | 编译定理 |
| closed / closed-bound | 最小表合法闭项及其 M⁰ 关系 | Check | 闭项/编译定理 |
| input / inputQ | 非有限分支例子具备原问题前提 | Gap | 编译定理 |
| no-finite-readback | 同一个例子没有逐孩子有限读回字段 | Gap | 编译否定，仅否定该字段 |
| MissingLimStep / Missingω+2 | 精确标记尚未证明的两个目标 | Gap | 命题类型定义，不是证明 |

##### 关键逐字签名

###### YiPJPath

```agda
bound : (N : ℕ) (ℓ : L) → ℓ ≡ fn N → (j : ℕ) (j′ : L) → j′ ≡ fn j → j′ ≤ ℓ → j ≤ⁿ N

```

###### YiPJPoint

```agda
proof-irrel : ∀ n ℓ (e e′ : ℓ ≡ fn n) → e ≡ e′

index-eq : ∀ N j ℓ → ℓ ≡ fn N → ℓ ≡ fn j → N ≡ j

```

###### YiPJCase

```agda
cases : ∀ N ℓ (e : ℓ ≡ fn N) j j′ (e′ : j′ ≡ fn j) o t v → Case N ℓ e j j′ e′ o t v

```

###### YiPJDown

```agda
  DLF : ∀ {n j} (mode : Mode) (u : fn j ≤ fn n) (child : Child n j u) (o : Ok (fn (suc n))) (r : Rb (fn (suc n))) (t₀ : E.T) (B : Base (fn (suc n))) → GB n B t₀
     → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
     → ∀ {a x} → M (suc n) a x
     → M j (ψᴺ j (t₀ ++ a)) (proj₁ (ψ (fn (suc n)) o r B (fn j) (top mode u) β x))

```

###### YiPJAll

```agda
Pres : (N : ℕ) (ℓ : L) → ℓ ≡ fn N → (j : ℕ) (j′ : L) → j′ ≡ fn j → j′ ≤ ℓ → Set

all : ∀ N ℓ (e : ℓ ≡ fn N) j j′ (e′ : j′ ≡ fn j) v → Pres N ℓ e j j′ e′ v

```

###### YiPJEmb

```agda
liftM : ∀ B (ℓ′ : L) (e′ : ℓ′ ≡ fn B) A (ℓ : L) (e : ℓ ≡ fn A) (o : Ok ℓ′) (u : ℓ ≤ ℓ′)
      → (y : Tr ℓ) (ey : ℓ ⊢ zero ◃ y) → ∀ {a} → MB ℓ e a y
      → MB ℓ′ e′ a (proj₁ (emb ℓ′ o u (y , ey)))

slotJ : ∀ B ℓ′ (e′ : ℓ′ ≡ fn B) A ℓ (e : ℓ ≡ fn A) (u : ℓ ≤ ℓ′) t → Slot A ℓ e B ℓ′ e′ u t

```

###### YiPJAcross

```agda
caseK : ∀ A ℓ (e : ℓ ≡ fn A) j (o : Ok ℓ) (t : Pos⁼ ℓ) (v : fn j ≤ ℓ) {ν}
  → ν ≡ natT (levB A ℓ e t) → (Q : Keep (fn j) (Br⁼ ℓ t) (bz⁼ ℓ t) → Set)
  → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
  → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ ℓ t) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ ℓ t)
    → ν ≡ natT (levPB j (fn j) refl q)
    → (∀ η c → LwP j q η c → LwB ℓ e t η (cv c)) → Q (just (q , cv , eq)))
  → Q (kp⁼ ℓ o t v)

acrossK : ∀ A ℓ (e : ℓ ≡ fn A) B ℓ′ (e′ : ℓ′ ≡ fn B) j (o : Ok ℓ′)
  (u : ℓ ≤ ℓ′) (t : Pos⁼ ℓ) (v : fn j ≤ ℓ′) {ν} → ν ≡ natT (levB A ℓ e t)
  → (Q : Keep (fn j) (Br⁼ ℓ t) (bz⁼ ℓ t) → Set)
  → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
  → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ ℓ t) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ ℓ t)
    → ν ≡ natT (levPB j (fn j) refl q)
    → (∀ η c → LwP j q η c → LwB ℓ e t η (cv c)) → Q (just (q , cv , eq)))
  → Q (mapK (pshBr u t) (pshFirst u t) (kp⁼ ℓ′ o (psh u t) v))

```

###### YiPJRef

```agda
module Reference (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : ∀ n → G n ≤ G (suc n)) where

  Rref : ∀ n → G n ≤ G (suc n)

  canRef : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (Rref n) ≡ pth s

```

###### YiPJLim

```agda
module Generic (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n))
  (R₀ : ∀ n → G n ≤ G (suc n))
  (canR₀ : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R₀ n) ≡ pth s)
  (R : ∀ n → G n ≤ G (suc n)) where

      LFω : ∀ {n j} (v : fn j ≤ G n) (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → ∀ {a x} → Mω a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (F (inc n v) β x))

    LFu : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
        → ∀ {a x} → Mω a x → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (Fu β x))

```

###### YiPJQ

```agda
qω+1 : Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc ωᶜ))

```

###### YiPJLimStep

```agda
module FinLim (f : ℕ → Tr zero) (a : ∀ n → zero ⊢ f n ◃ f (suc n))
  (d : ℕ → ℕ) (eG : ∀ n → h₁ (f n) ≡ fn (d n)) where

  step : Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc x))

```

###### YiPJCheck

```agda
q-even : Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc ωᵉ))

closed : Tr zero
closed = proj₁ (ψ (h₁ (suc ωᶜ)) (proj₂ (Ok-tw 1) (suc ωᶜ)) (rbᶻ (h₁ (suc ωᶜ)))
  (B₀ (h₁ (suc ωᶜ))) zero (z≤ (h₁ (suc ωᶜ))) (Ωt zero) (proj₁ (Ωt (h₁ (suc ωᶜ)))))
closed-bound : M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) closed
closed-bound = qω+1 (proj₂ (Ok-tw 1) (suc ωᶜ)) (rbᶻ (h₁ (suc ωᶜ))) (z≤ (h₁ (suc ωᶜ)))
  (zp-z (h₁ (suc ωᶜ))) (B₀ (h₁ (suc ωᶜ))) (λ i u → ⊴r) (Ωt zero) (m1 refl mz)

closed-bound : M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) closed

gb₀ : ∀ n → GBB (fn n) refl (B₀ (fn n)) []

```

###### YiPJGap

```agda
input : M⁰ ωᵀ x

inputQ : Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ x)

ω-not-finite : ∀ n → h₁ ωᶜ ≡ fn n → ⊥

no-finite-readback : ((n : ℕ) → Σ ℕ λ j → h₁ (f n) ≡ fn j) → ⊥

MissingLimStep : Set
MissingLimStep = Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc x))

input₂ : M⁰ (E.sucT ωᵀ) (suc ωᶜ)

inputQ₂ : Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc ωᶜ))

Missingω+2 : Set
Missingω+2 = Q (ψᴺ 0 (E.Ωt (E.sucT (E.sucT ωᵀ)))) (h₁ (suc (suc ωᶜ)))

```

#### 第一障碍与精确的 x 形状

一般 lim 的具体未证目标是 Gap.MissingLimStep，x = lim f a，f 0 = ωᶜ，f(n+1)=suc(f n)，a n = ◃s。input : M⁰ ωᵀ x 与 inputQ : Q(ψᴺ 0 (Ωt ωᵀ))(h₁ x) 已编译，所以不是矛盾前提。应用当前 Lim.Generic 时，第一步要取得每个 G n=h₁(f n) 的有限读回等式；n=0 时该字段由 ω-not-finite 否定。不能把 Generic 的有限孩子保持直接应用在此例。

下一条实际待证引理（不是当前 no-finite-readback 的否定对象）是：为该非有限孩子形状给一条能和自身折叠保持共用关系的 Low，下折到 0 后保持 ψ₀(t₀+a)。现有 Generic.LFu 的输入关系是 Mω，其孩子关系由有限 MB 给出，不能承载这里的第 0 个孩子。需要能承载这个孩子的关系/保持定理，或者不走该接口的证明；本回报没有穷尽替代办法。

ω+2 的具体未证目标是 Gap.Missingω+2：η = sucT(sucT ωᵀ)，x = suc ωᶜ。input₂、inputQ₂ 已给出 StepS 所需两个前提。现有 YiHCPlus.Plus.M₊ 可以描述 h₁(suc ωᶜ)，但未接齐该层对一切 Ok 的自身保持与一致下折。首先需要的自身保持形状为：

```agda
(o : Ok ℓ₊) (r : Rb ℓ₊) (B : Base ℓ₊) (β : Tr⁺ ℓ₊) →
∀ {P₀} → M₊ (ψᵘ (sucT ωᵀ) P₀) (proj₁ β) →
∀ {a x} → M₊ a x →
M₊ (ψᵘ (sucT ωᵀ) (P₀ ++ a))
  (proj₁ (ψ ℓ₊ o r B ℓ₊ self β x))
```

其中 ℓ₊=h₁(suc ωᶜ)，M₊ 为既有 Plus 的关系。此签名在这里只是精确的后续义务，不冒充编译定理。完整 Lift₁ 还要求任意 η、任意 x，不由以上两个目标直接覆盖。

#### 前提可满足、复用与翻译账

在写 FinLim 一般形式之前先编 YiPJPrem.agda：取 f=dbl、d(0)=0、d(n+1)=d n+2，递归得到 eG，并给出 n≤d n。之后正式 theorem 里的 n≤d n 从 nat⊴f 自动推出。正式 Check.q-even 给出非 canonical 0,2,4,… 实例。有限保持的 GBB 由 Check.gb₀ 实填；完整 Q 的 OKB 由 B₀/⊴r，β 取 Ωt zero、hβ 取 m1 refl mz 实填为 closed-bound。一般 lim、ω+2 的原 StepS 前提分别由 Gap.input/inputQ 与 input₂/inputQ₂ 实填。

所有搬来的数学归纳均在文首标来源：有限 Down 复用 YiLTFold 的 M 推导步骤、gbS 与链；Lim 复用 YiLTLim 的推导与链；Omega 自身保持、leafω、上折保持直接用 YiSSOmega/YiHCOmega；后继出口沿用 YiTSMachine 的既有抽象 Chain，不再重证链接口。Ref 从实际 R 得数字界后另造参考 R₀，实际 ψ 始终使用原 R。这样也避开 no-all-Sb 所否定的实际路径规范化断言。

翻译账：新内容是验收关系的端点等式、实际路径的保持及槽位引理；没有新树节点、没有更改折叠行、没有为新节点增加闭包前提。新增脚手架服务于既有有限读回/记号关系，不是树定义本身的新序数构造；本路仍用 Mω、记号 γ 与后继基本列出口，所以不声称树已自足。构造方面实际折叠的 Ok、表、底及路径量化没有缩成规范版本。

#### 偏离、事故与停止条件

没有触发三条数学停止条件：第 0 步通过；无同一处两次数学重新设计仍不过；无 5G 或 8G 堆耗尽。按主审并行预算后续全部使用 5G，最大驻留远低于此；未把 5G 改写成原简报的 8G 停止条件。

临时编译中修正过普通作用域导入、Case 的 Set₁、recompute 的相关参数 eta 包装，以及有限源层抽象等式的换型参数。Lim 泛化后的第一次仓库 Q 编译指出 GBω 记录保留了参考 R 参数：自动选择 Rref 的 GBω 与既有 Wω 的 GBω 不是同一记录实例。改为显式参考 R₀/canR₀ 与独立的实际 R 后编译通过；实际 R 未加 canR 前提。FinLim 自动导出 dk 时补上 h₁ 所含的 zero⊕ 路径映射；Gap 从未封闭 ωᶜ-M 转入封闭关系时，复用既有 of⁰。均保留失败日志，没有删失败证据。

本路按简报第 3 步“做到哪一步算哪一步”和第 4 步“否则交第一个挡住的引理”交付。一般 lim 与 ω+2 记为未走通，没有否定或关闭路线。

已读而复用：AGENTS.md、EBOHandbook §4、任务简报；YiLTFold、YiHCLim、YiLTLim、YiHCBridge、YiHCOmega、YiSSOmega、YiTSBridge/Orbit/Machine/Step/Exit 及本文引用的局部签名。未把仅由他人转述的任何新数学结果算作本路定理；YiCD 的摆脱先手门槛由主审独立复核后通知，本路不将此通知当作自己的复核结论。

#### 临时源码与日志

所有临时文件均在 <实验目录>：YiPJ0.agda（第0步），YiPJProof.agda（端点证书），YiPJKCase.agda，YiPJDown.agda，YiPJAll.agda，YiPJEmb.agda，YiPJAcross.agda，YiPJRef.agda，YiPJLim.agda，YiPJQ.agda，YiPJPrem.agda（泛化前前提检查），YiPJLimStep.agda，YiPJCheck.agda，YiPJGap.agda。临时版本可能保留此前模块名或早期特殊化；最终权威源码为上述仓库 13 件冻结文件。

最终通过日志：YiPJ0.log，YiPJProof.log，YiPJKCase.log，YiPJDown.log，YiPJAll.log，YiPJEmb.log，YiPJAcross.log，YiPJRef.log，YiPJLim-generic.log（初次自动参考版）、YiPJQ-repo2.log（显式参考参数修正后）、YiPJPrem2.log，YiPJLimStep3.log，YiPJCheck.log（gb₀ 加入前；最终见自冷编），YiPJGap2.log。最终自冷编日志和摘要见文件表。失败日志亦完整留在同目录，回报未隐去。

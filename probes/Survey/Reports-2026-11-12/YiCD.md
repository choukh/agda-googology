# 用树侧的规范读回域刻画量化域（摆脱侧） (YiCD)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十五批；外部模型，作者转发 |
| 前缀 | `YiCD` |
| 回报 | 2026-11-14 已返回并由本会话主审复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：用树侧的规范读回域刻画量化域（摆脱翻译一侧，前缀 YiCD）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`（尤其 "目标"、"树的语言"、"量化域先取带证据的读回域"、"攀爬与摆脱翻译要平衡"），以及 `probes/Survey/EBOHandbook.md` 第 4 节。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 本路（选项原文）："(2) 摆脱侧：用树侧的规范读回域刻画量化域"，说明是 "Lift₁ 量化 '一切与 η 有第 0 层关系的孩子'，两路都疑它太宽；不看记号地定义 '规范读回的孩子'，编译出后继一步在这个域上的形式、以及它是否够接龙骨"。
- 作者 2026-11-14："“记作以后 \"摆脱翻译\" 那一侧的候选” 这个务必落实"。AGENTS："开一个攀爬模块前, 先有已编译的摆脱侧结果说明这一站要加的是哪一种"。与本路并行的攀爬路（前缀 `YiPJ`）在补同一处的记号版。
- AGENTS "量化域先取带证据的读回域"：封闭与保持定理先对规范构造的读回域陈述，不对 "一切合法树"；反例对象不在读回域内的否定，读作 "谓词太宽"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状"。本路不改树、折叠、合法性。
- 本路只交编译事实；判断只写在 "未走通" 的原因里，并标为判断。

#### 背景（主审复核过的编译事实）
- **现在的量化域**：`probes/OCF/Lean/YiLTLift` 的 `Lift₁` 与 `StepS` 量化 "一切满足 `M⁰ η c` 的第 0 层树 c"。`M⁰` 是下界式的记号关系。
  - `YiSSScope.no-exact-child : (∀ {x} → M⁰ ωᵀ x → x ≡ ωᶜ) → ⊥`：从关系读不出精确的孩子。
  - `YiCLCrit.no-least`：满足 `M⁰ ω y` 的树没有公共的规范树。
  - YiLT、YiSS 两路的执行方都判断量化域可能太宽（未编译）。
- **龙骨要用到哪些孩子**：充分性定理 `YiAbsGSuff.Suff.Tower.K` 每行只折一次（从塔第 n 项直接到第 0 层）。塔第 1 项那一层的保持编译地归约到孩子层的接口（`YiKPRel`：接口 `Kid`、`Top.Fold.LF¹`、`chain`、量化域 `Sp`），再到 `Lift₁`。回灌链的下标是折叠的输出（`YiKPRel.Top.Fold.chain`、`YiTSStep` 的 `chain`/`parts`）。
- **树侧已有的不按阶段的陈述**：`YiLTLift.up◃`（沿第 0 层树的序上行）、`upS`、`upL`；`YiTSStep.tree-step`（后继层号上 Ω 树的折叠按定义等于下层 "自身折叠再 next" 的链的部分和极限，`refl`）。
- 主线折叠：`YiTBRow.ψ` 配 `YiMTTab.rbᶻ`。读回层号 `h₁ c` 只有后继与 ℕ 极限形状（`YiRWBlock` 第 81 行 `Pos zero = ⊥`，第 137–142 行 `↑`）。

#### 要做的（按序）
0. **最小实例检查**，在临时目录（纯 `.agda`）：
   - **不读记号**地写出 "规范读回的孩子" 的谓词 `Canon : Tr zero → Set`（例如由零、后继、以及字面单调的自然数序列的极限生成；或者 "塔的计算里实际出现的下标"，即折叠输出的闭包。你选一种并说明理由）。
   - 确认 `ωᶜ`、`suc ωᶜ`、`nat n` 在内；确认塔第 1 项回灌链的前两个下标在内（`refl` 或构造）。
   - 不成立就停下回报。
1. **域上的后继一步**：写出 `StepS` 限到 `Canon` 上的形式 `StepSᶜ`，并证明 `StepSᶜ` 加已有的引理推出 `Lift₁` 限到 `Canon` 上的形式（照 `YiLTLift.liftQ`、`lift-red` 的归纳）。
2. **够不够接龙骨**：检查塔第 1 项那一层的保持（`YiKPRel.Top.Fold.LF¹` 及 `Kid`）实际只用到 `Canon` 里的孩子，或者编译出它还要哪些孩子（精确到构造）。目标是给出 "龙骨只需要 `Lift₁` 在 `Canon` 上" 的编译定理，或第一个反例。
3. **翻译账的信息**：说出这个域的定义只用到树的哪些构造与哪些字段；若某种更宽的域被编译否定（例如在更宽的域上某条保持不成立），写成否定定理。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiCD`（模块名 `OCF.Lean.YiCD…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行的另两路前缀 `YiPJ`、`YiDD`。定义 `Canon` 的文件文首标明 "不读记号"，用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包没有记号模块；其余文件标明 "验收文件"。
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
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么（尤其 "让树自足"：量化域能不能不看记号定出）；第 0 步；域上的后继一步、够不够接龙骨、翻译账信息各到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然"、"更好" 一类形容；不给方向推荐。



## 本会话主审复核（2026-11-14）

主审读过 Canon、StepSᶜ、liftQᶜ/lift-redᶜ、实际链对齐和下标 2 的反例及其 γ 关系见证；3 件独立删接口冷编均 0、各仅自身 Checking。Canon 全域导入闭包无记号，编译器本地依赖图与静态闭包 7 项逐一相同。总体 StepSᶜ 未实填；该具体域不足以覆盖实际链的反例已编译，不否定其他规范域。

临时源码：[YiCD0.agda](attachments/YiCD-YiCD0.agda.txt)、[YiCDCounter0.agda](attachments/YiCD-YiCDCounter0.agda.txt)。原文只机械替换本机路径、降低标题层级；执行方的阶段统计保留，主审确认以本节为准。

## 回报原文（本会话执行）

### YiCD 回报：有限分支极限的读回域与实际链反例

#### 1. 判决与问题表

对纲领与“让树自足”的意义：本路把量化域写成不读记号的树谓词 Canon，并编译出前驱及第一位置下行闭包；域上的后继归约能不改变树、折叠或合法性来陈述。这个具体域没有覆盖实际龙骨计算的全部下标：主线塔第 1 项实际回灌的下标 0、1 在内，下标 2 不在。下标 2 仍满足该链所用的 M⁰ 关系。这里交的是具体树域的反例，不是对一切规范域或一切接龙骨办法的否定；没有新增终点值下界。

第 0 步已通过。临时纯 Agda YiCD0 的 Canon/Fin、原 YiCLFam.nat、原 YiCLCrit.ωᶜ、suc ωᶜ，以及实际 idx 0、idx 1 均已构造并编译 0。第一个文件在 30 分钟内写出并编译。选取的域只用零、后继、合法的 ℕ 极限及每个分支是字面自然数的证据；不固定某一个自然数序列。相邻条件是原树的第一位置步进，不是序数值严格递增的额外假设。

第 1 步已交条件形式：StepSᶜ 把原 StepS 限到 Canon x；liftQᶜ 与 Restricted.lift-redᶜ 给出 StepSᶜ → Lift₁ᶜ。m1 用 suc-inv，mw 用 below，mL/mc 保持同一域证据。没有直接对受限前提调用原 liftQ。一般 StepSᶜ 本身未实填；本路不声称其全域前提已有居留，也不把这个条件函数作为无条件封闭或强度结果。已知有限精确对仍有实际实例 step-finite，restriction 说明原 StepS 一旦给出可限制到本域。

第 2 步交“第一个反例”分支：YiCDKeel.actual-chain k = refl 对齐原 YiLTKid.Sem、最小表 rbᶻ、B₀、gb₀ˢ 的 Fold.feed G。not-idx2、not-positive-chain-domain 否定当前实际正项链的下标全都属于 Canon。idx2-gamma 另证 M⁰ (γT ΩΩ [] 1) (idx 2)，这不是任意挑的一棵域外树，也没有借未证明的全域 Lift₁。因而没有把原保持中的所有实际链点直接限制成这个 Canon；没有交 Lift₁ᶜ → 完整 Lift₁ 或 k1 的新出口。

第 3 步的翻译账：Canon 的构造子不引用记号、序数值或折叠；Fin 只识别字面的 zero/suc；cl 的唯一额外字段是逐分支 Fin。合法相邻步进 a 已在树里，Canon 没有改它。fold/Ok/Rb 只出现在同模块的实际计算见证与另一个验收模块，不进入 Canon 的构造子。所选域确实不是全域：not-outside 排除以一个 ℕ 极限为首分支的合法 ℕ 极限。没有对更宽的域给出新保持否定，也没有按“读法低”关闭候选。

| 问题 | 位置 | 档与状态 |
|---|---|---|
| 不读记号的域、有限数与两类 ω 实例 | YiCDCanon；原 ωᶜ 在 YiCDLift | 编译定义/定理 |
| 前驱及第一位置下行封闭 | suc-inv、below | 编译定理 |
| 域上后继一步归约 | liftQᶜ、Restricted.lift-redᶜ | 编译条件函数；StepSᶜ 未实填 |
| 实际链前两个下标在域内 | idx0、idx1 | 编译定理；下标指 iter 的 0、1 |
| 第三个实际下标越域且关系前提成立 | not-idx2、idx2-gamma | 编译定理 |
| 当前正项链的全域覆盖失败 | not-positive-chain-domain | 编译否定；仅针对本次 Canon |
| 其他 Canon 或其他接龙骨办法 | 未实施 | 本路不作否定 |

#### 2. 文件、自查与编译表

三件共 169 代码行。口径为 Agda 代码块中非空、非整行注释行；含选项、模块、导入、定义与签名，不是定义依赖切片。三件均自删自身接口冷编，退出 0、日志仅自身 Checking、warning 0。禁用构造、洞、本机路径和 Funext 扫描均 0。

| 文件 | 代码行 | 冷编退出 | max residency (bytes) | total memory (MiB) |
|---|---:|---:|---:|---:|
| YiCDCanon | 71 | 0 | 164,215,344 | 276 |
| YiCDLift | 54 | 0 | 1,408,453,288 | 2356 |
| YiCDKeel | 44 | 0 | 1,349,287,064 | 2519 |

maximum residency 与 total memory 都取 +RTS -s 的原字段，不称为进程 RSS。三次最终冷编在主审调整并行预算之前已启动并按原 8G 上限串行完成。收到后续先用 5G 的协调要求后，没有再启动新的 8G 编译；Canon 编译器依赖图以 5G 成功生成。Canon 的 importclosure 全域审计无 --only，退出 0、禁用表命中 0。主审已另行独立复核 Canon；其余待主审复核。

临时目录和路径仅供主审，留档时应脱敏：
- 第 0 步：<实验目录>/YiCD0.agda；YiCD0.log，0。
- 反例最小检查：<实验目录>/YiCDCounter0.agda；YiCDCounter0.log，0。
- 三件首次日志：YiCDCanon.log、YiCDLift.log、YiCDKeel.log；最后一个已修复导入后为 0。
- 三件冷日志：<实验目录>/YiCDCanon-cold.log、YiCDLift-cold.log、YiCDKeel-cold.log。
- 闭包：YiCDCanon-closure.log；图：YiCDCanon.dot、YiCDCanon-graph.log，0。
- 静态与统计：<实验目录>/audit.json。
- 完整回报：<实验目录>/report.md。

#### 3. 定理表与逐字陈述

以下签名直接从定稿源码提取。嵌套声明的参数按所给模块上下文保留。M⁰、Kdˢ 是验收关系，不把关系见证另说成已过 Exᴴ 的序数值下界。

##### YiCDCanon：域及实际下标

```agda
data Fin : Tr zero → Set where
  fz : Fin zero
  fs : ∀ {x} → Fin x → Fin (suc x)

data Canon : Tr zero → Set where
  cz : Canon zero
  cs : ∀ {x} → Canon x → Canon (suc x)
  cl : ∀ {f a} → (∀ n → Fin (f n)) → Canon (lim f a)
```

白话：Fin 只认字面自然数；Canon 由零、后继和有限分支的合法极限生成。档：编译定义。

```agda
fin-canon : ∀ {x} → Fin x → Canon x
```
字面有限数在域内。档：编译定理。

```agda
nat-in : ∀ n → Canon (nat n)
```
所有自然数实例在域内。档：编译定理。

```agda
omega-in : Canon ω₀
```
模块自身的标准自然数极限在域内。档：编译定理。

```agda
suc-omega-in : Canon (suc ω₀)
```
其后继在域内。档：编译定理。

```agda
suc-inv : ∀ {x} → Canon (suc x) → Canon x
```
从后继域证据取回前驱。档：编译定理。

```agda
below : ∀ {x y} → Canon y → zero ⊢ x ◃ y → Canon x
```
域沿第一位置序向下遗传。档：编译定理。

```agda
lim-finite : ∀ {f a} → Canon (lim f a) → ∀ n → Fin (f n)
```
域内的极限每一支都为字面有限数。档：编译定理。

```agda
idx0 : Canon (idx 0)
```
实际回灌下标 0 在域内。档：编译定理。

```agda
idx1 : Canon (idx 1)
```
实际回灌下标 1 在域内。档：编译定理。

```agda
not-outside : Canon outside → ⊥
```
域不是所有第 0 层树。档：编译定理。

```agda
G : Tr zero → Tr (tw 1)
G c = up zero c (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))

feed : Tr zero → Tr zero
feed c = proj₁ (ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (B₀ (tw 1)) zero (ink self) (Ωt zero) (G c))

idx : ℕ → Tr zero
idx = iter feed zero
```
这段定义精确指定主线的表、底、路径和被折叠的 Ω 树分支；没有取任意折叠输出作为 Canon 构造子。

##### YiCDLift：原实例与域上归约

```agda
fin-CF : ∀ n → Fin (CF.nat n)
```
原 YiCLFam.nat 的有限证据。档：编译定理。

```agda
ω-in : Canon ωᶜ
```
原 YiCLCrit.ωᶜ 在域内。档：编译定理。

```agda
sω-in : Canon (suc ωᶜ)
```
原 ωᶜ 的后继在域内。档：编译定理。

```agda
StepSᶜ : Set
StepSᶜ = ∀ {η x} → Canon x → cof η ≡ c1 → M⁰ (pred η) x
       → Q (ψᴺ 0 (E.Ωt (pred η))) (h₁ x)
       → Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc x))
```
域上的后继一步只加 Canon x；它本身尚未实填，不冒称已有无条件 Lift₁。

```agda
restriction : StepS → StepSᶜ
```
原 StepS 的限制映射。档：编译定理；liftQᶜ 带 StepSᶜ 条件。

```agda
liftQᶜ : StepSᶜ → ∀ {η c} → Canon c → M⁰ η c → Q (ψᴺ 0 (E.Ωt η)) (h₁ c)
```
域上的后继一步推出域上的 Q。档：编译定理；liftQᶜ 带 StepSᶜ 条件。

```agda
step-finite : ∀ n → Q (ψᴺ 0 (E.Ωt (natT (suc n)))) (h₁ (suc (CF.nat n)))
```
精确有限对的已知无条件实例。档：编译定理；liftQᶜ 带 StepSᶜ 条件。

```agda
module Restricted (r : Rb ℓ¹) where
  open Sem r
  Lift₁ᶜ : Set
  Lift₁ᶜ = ∀ {η c} → Canon c → M⁰ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₁ c)))

  lift-redᶜ : StepSᶜ → Lift₁ᶜ
  lift-redᶜ st cc m = Red.Q→Kd r (liftQᶜ st cc m)
```
白话：每个具体表 r 上，域上的后继一步推出同一表的域上 Lift₁。代码里只用 Red.Q→Kd 接出口；前驱/下行证据已经在 liftQᶜ 中检查。档：编译条件函数，未实填全域 StepSᶜ。

##### YiCDKeel：当前龙骨实际链的反例

```agda
module M = Sem (rbᶻ ℓ¹)
module F = M.Fold (B₀ ℓ¹) M.gb₀ˢ
```
模块 F 是原保持接口的实际最小表/标准底实例，GB₀ˢ 是已给出的证据。

```agda
actual-chain : ∀ k → idx k ≡ iter (F.feed G) zero k
```
本路 idx 与原保持证明使用的迭代逐字对齐。档：编译定理。

```agda
not-idx2 : Canon (idx 2) → ⊥
```
实际下标 2 不在所选域内。档：编译定理。

```agda
not-feed-closed : (∀ {c} → Canon c → Canon (feed c)) → ⊥
```
这个具体域对实际更新不封闭。档：编译定理。

```agda
not-keel-domain : (∀ k → Canon (iter (F.feed G) zero k)) → ⊥
```
实际完整链不全在这个域内。档：编译定理。

```agda
not-positive-chain-domain : (∀ k → Canon (iter (F.feed G) zero (suc k))) → ⊥
```
原保持使用的正项链也不全在域内。档：编译定理。

```agda
one-below : zero ⊢ suc zero ◃ idx 1
```
有限孩子 1 是实际下标 1 的第一位置前驱。档：编译定理。

```agda
kid-one : M.Kdˢ (idx 1) (E.Ωt (natT 1)) (proj₁ (Ωt (h₁ (idx 1))))
```
由已有有限实例沿序上行提供所需孩子保持。档：编译定理。

```agda
branch-one : M.M¹ (E.Ωt (natT 1)) (G (idx 1))
```
实际分支有原 M¹ 关系。档：编译定理。

```agda
idx2-related : M⁰ (ψᴺ 0 (E.Ωt (natT 1))) (idx 2)
```
越域点仍有 ψ₀(Ω₁) 的关系见证。档：编译定理。

```agda
idx2-gamma : M⁰ (γT ΩΩ [] 1) (idx 2)
```
同一点对着原回灌链的 γ 第 1 项。档：编译定理。

#### 4. 第一个反例的精确范围

所选域在 lim 节点上要求每个分支有 Fin 证据。实际 idx 1 已经是一个自然数列极限；下一次 feed 给出 idx 2，它仍是 lim，首分支本身又是 lim。not-idx2 的证明在 cl q 后读取 q 0，得到 Fin (lim … …)，没有可用的 Fin 构造子，故由空模式结束。此结论已编译，不是有限样本的观察。

反例的参数都实际给定：F 是 Sem (rbᶻ ℓ¹) 的 Fold (B₀ ℓ¹) gb₀ˢ；actual-chain 是 refl。idx0、idx1 提供域内起点，one-below 与已有 Qfin 1 提供 kid-one，LF¹ 由 branch-one 和 Sp 的 tt 给出 idx2-related，最后定义性等式得到 idx2-gamma。没有借尚未实填的 StepSᶜ 或 Lift₁ 得到这个关系。

编译否定的逐字对象是“这个 Canon 包含当前实际正项链的每个下标”，不是“任何读回域都不能接龙骨”。本路没有换题去定义第二个域，也没有宣称不存在利用别的外部定理的接法。按简报交首个反例分支，因此没有触发两次设计失败、8G 堆耗尽或第 0 步不成立的停止条件。一般 StepSᶜ 的可满足性仍未解决，不能当作已有的全域前提。

#### 5. 偏离、事故与未读材料

- 未改已有文件，未写 src/archive、YiPJ/YiDD 前缀或任何台账/留档正文；没有安装、提交、推送或派子智能体。
- 先用纯 Agda 完成第 0 步，再写一般归约。已将 Canon 的冻结文件与冷编/闭包结果发给主审，主审确认门槛后才放行 YiPJ。
- 一度考虑固定 f n 为 nat n 的极限模板，未写入代码也未编译；实际采用每支均 Fin 的所有合法序列。该未实施模板没有作为否定结论，本路不据此关闭它。
- 初次 Canon 的 fin-below 写了三个多余的不可达模式，产生 UnreachableClauses 警告，删除后最终冷编 warning 0；不靠关闭告警通过。Keel 首次缺 h₁ 的显式导入，NotInScope，补 using 后通过；这些不是数学重新设计。
- 一次写文件编排的 JavaScript 字符串语法错误发生在工具执行前，没有写入或编译。随后直接写入新文件，未影响其他路线。
- 实际检索/读取了本路调用的 YiLTKid、YiLTLift、YiKPRel 相应接口与链、YiRWBlock/RWOps/Path、YiTBRow、YiMTTab、HCRel 的构造子，以及原 nat/ω 的定义。手册 §4 与简报已读。关于更高塔的一般充分性只按背景指引检查所用签名，本路没有用其未重审内容作新结论；没有作外部文献或外部代码调查。
- 自身没有记录 token 用量。自冷编的三个结果与主审独立复核的范围分别说明，不冒称所有主审检查已经完成。

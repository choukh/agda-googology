# 后继一步的树侧陈述（摆脱侧） (YiTS)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 改派外部模型（原话 “额度告急, 从现在开始派发外部模型, 请给每路都写任务breif并给出路径, 以便我直接复制”）；作者转发 |
| 前缀 | `YiTS` |
| 回报 | 2026-11-14 已返回；本会话主审独立复核，见文末 |

## 简报原文（本机路径换成占位）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`（尤其 "目标"、"树的语言"、"攀爬与摆脱翻译要平衡" 三处），以及 `probes/Survey/EBOHandbook.md` 第 4 节。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

## 作者的决定与原则（2026-11-14，选项原文或原话）
- 本路（选项原文）："(2) 摆脱侧：StepS 的树侧陈述"，说明是 "把后继一步写成不看记号的树侧关系（类似 up◃），记号只在出口；给出这一站要加的是哪一种"。
- 作者 2026-11-14："“记作以后 \"摆脱翻译\" 那一侧的候选” 这个务必落实"。AGENTS 规定攀爬与摆脱 1:1 交替："开一个攀爬模块前, 先有已编译的摆脱侧结果说明这一站要加的是哪一种"。与本路并行的攀爬路（前缀 `YiSS`）做的是同一处（后继一步，孩子 ω+1）的记号版。
- AGENTS 的 "提供信息的标志"："写成对结构参数的一步定理, 并说出这一站新用到哪个字段; 用序数值验收, 并给出树的基本列与记号的差; 用否定定理划出不能有的字段"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状"。本路不改树、折叠、合法性。
- 本路只交编译事实；判断只写在 "未走通" 的原因里，并标为判断。

## 背景（主审复核过的编译事实）
- 新主线折叠：`YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`（`probes/OCF/Lean/`）。读回层号 `h₁ c`（第 0 层的树 c 读回的层号）只有后继与 ℕ 极限形状，没有 Ω 形状（`YiRWBlock` 第 81 行 `Pos zero = ⊥`，第 137–142 行 `↑`）。
- **记号版的后继一步**（`YiLTLift`）：`StepS = ∀ {η x} → cof η ≡ c1 → M⁰ (pred η) x → Q (ψᴺ 0 (E.Ωt (pred η))) (h₁ x) → Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc x))`，其中 `Q t ℓ` 是 "层 ℓ 的 Ω 树以任一 `OKB` 的底、沿一致路径折到第 0 层，对着记号项 t"。`lift-red : StepS → Lift₁`。
- **已有的树侧、不按阶段的陈述**：`YiLTLift.up◃ : ∀ {t} {x c : Tr zero} → zero ⊢ x ◃ c → Q t (h₁ x) → Q t (h₁ c)`（沿第 0 层树的序上行）；`upS`、`upL`（沿后继、ℕ 极限形状上行）。它们只是 "对着同一个 t"，没有说层号变大时值变大多少。
- **后继形状的层号上的 Ω 树**：层 `nd sS (λ _ → ℓ)` 的 Ω 树是结点，朝第 0 层取回灌链 z_{k+1} = next（层 ℓ 上 z_k 的自身折叠）（`YiLT.md` §4 的机制说明）。树侧这一步的内容就是：后继层号上 Ω 树的折叠 = 在下面那一层上 "自身折叠再 next" 的迭代的极限。
- 回灌链与它对着记号 γ 链的引理：`YiKPRel` 的 `Top.Fold.chain`，`YiHCPlus.Fold₊.chainω`，`YiLTFold` 的 `chain`。
- 记号一侧：`EboLeanDef`（`cof`、`fsn`、`fsT`、`E.Ωt`）、`YiCFCofin`、`YiCFMono`、`YiMENote`。

## 要做的（按序）
0. **最小实例检查**，在临时目录（纯 `.agda`）：
   - 写出一条**不读记号**的陈述 `TreeStep`：对第 0 层的树 x，层 `h₁ (suc x)` 的 Ω 树朝第 0 层的折叠，与层 `h₁ x` 上的折叠之间的树侧关系（例如：前者不低于后者以 "自身折叠再 next" 迭代所得的极限；用 `⊴`、`◃` 或读回值 `≼` 表达，选你能证的那一种）。
   - 在 x = `nat n` 与 x = `ωᶜ` 两处确认它类型正确、可证或给出反例。不成立就停下回报。
1. **证 `TreeStep`**：先对 x 为有限与 ℕ 极限形状，再看一般的 x。陈述里只出现树、层号、折叠、序；不出现记号。
2. **桥**：证 "`TreeStep` 加一条记号一侧的引理 ⟹ `StepS`"。记号一侧那条引理只说记号的事（例如 ψ₀(Ω_{η+1}) 的基本列与 ψ₀(Ω_η) 的 γ 链的关系），写清它的陈述；能证就证，不能就作为条件。目标是让记号只出现在出口。
3. **翻译账的信息**：
   - 说出这一步新用到折叠的哪几行、哪些字段（例如后继形状的结点规则、回灌链、`next`）。
   - 给出树一侧这一步的基本列与记号一侧基本列的差（在 x = `nat n` 处对几项写出，`refl` 或有限测试）。
   - 若能编译出某种字段不能有（例如 "不读回灌值的写法过不了这一步"），写成否定定理。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

## 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiTS`（模块名 `OCF.Lean.YiTS…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行的另两路前缀 `YiSS`、`YiPM`。树侧陈述的文件文首标明 "不读记号"；桥与验收的文件标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 树侧陈述的文件要用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包里没有记号模块。
- 仓库文件里不写本机路径。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库的 .agda-lib 路径>
  <cubical 的 .agda-lib 路径>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - 同时只跑一个 agda，堆上限 8G（另两路也在编译）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
- 不在你的临时目录与你前缀的新文件之外删除任何东西，不 `pkill`，不装包，不提交，不推送。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

## 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么（尤其 "让树自足"：这一步的判据能不能不看记号写出）；第 0 步；`TreeStep`、桥、翻译账信息各到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然"、"更好" 一类形容；不给方向推荐。

## 本会话主审复核（2026-11-14）

7 件独立删接口、8G 冷编均为 0，日志各只有自身 Checking；已读树等式、抽象链实填、纯记号公式、Orbit 与 Bridge 的逐字陈述。Step/Seq/Machine 的全域闭包与编译器依赖图均无记号；规范桥所有参数实填的闭实例已独立复跑为 0。完整 StepS 未得，任意 Ok 的局部桥仍带 Low；按当前证明链同处接口两次失败停止，不构成 Low 或 StepS 的否定，也没有证明 Low 必须经该接口。

本会话按作者指令用 Codex 协作工具直接派发三路；未采集可核对的 token 用量。回报原文仅机械替换本机路径、降低标题层级，保留阶段性统计与原判断；后续确认以本节为准。

临时源码留档：[第 0 步](attachments/YiTS-YiTSCheck.agda.txt)、[抽象接口检查](attachments/YiTS-YiTSIfaceCheck.agda.txt)、[局部桥检查](attachments/YiTS-YiTSBridgeCheck.agda.txt)、[所有参数实填的闭实例](attachments/YiTS-YiTSClosedCheck.agda.txt)。第 0 步和最终闭实例已由主审独立复跑为 0。

## 回报原文（Codex 协作子智能体）

### YiTS 回报：后继一步的树陈述、既有链接口与 ω+1 局部桥

#### 1. 判决与问题表

对纲领与“让树自足”的进展：后继层 Ω 树朝第 0 层的折叠，已能不看记号写成下层“自身折叠再 next”的回灌链，经下折、next 后取部分和极限的精确树等式。`YiTSStep` 的 `TreeStep` 对一切第 0 层树 x、证据、比较表、底及孩子路径成立；`branch` 给出每个部分和到总折叠的第一位置序。导入闭包不含记号。

完整桥仍未走通。不是声称 `TreeStep` 加一条纯记号引理已经推出完整 `StepS`。本路证明了纯记号引理 `note`，把既有抽象链定理实填到当前折叠（`YiTSMachine`），并在 ω 层任意 `Ok` 上实填自身保持、得到实际回灌链对 γ 链的保持（`YiTSOrbit.Atω.orbit-ok`）。`YiTSBridge.AtStep.result` 在孩子 ω+1 处还带混合条件 `Low`；该条件在相邻路径固定为 `inc tt self` 的 `Canon` 上由已有 `Uω.FoldU.LFu` 实填。这个实例是编译定理；没有把它写成量化任意 `Ok` 的 `Q`，也没有完整 `StepS`。

第 0 步：临时文件 `YiTSCheck.agda` 的有限 n 与 ω 树实例编译退出 0，底、证据、路径均为闭项；之后 `YiTSBridge` 使用原 `YiCLCrit.ωᶜ`，并在 `YiTSClosedCheck.agda` 把规范 ω+1 桥的所有参数实填为闭项，编译退出 0。最初临时文件自己的 `ωᶜ` 由 `YiTBRow.nat` 生成；原仓库 `ωᶜ` 由 `YiCLFam.nat` 生成。本路没有把这两个函数或两棵极限树说成字面相等；通用 `TreeStep` 对两者分别适用，最终桥使用后者。

未新增树、折叠或合法性定义；没有新的否定定理。没有新增 `Exᴴ` 值出口，不把关系见证说成新的序数值下界；FGH 比较也没有新增。

| 问题 | 位置 | 档与状态 |
|---|---|---|
| 后继层折叠的精确树侧陈述 | `YiTSStep.Step.tree-step`、`branch` | 编译定理；一般 x |
| 只说记号的基本列公式 | `YiTSNote.note` | 编译定理；η 后继形状 |
| 当前自身折叠接既有链接口 | `YiTSMachine.Machine.Keep.Orbit` | 编译的模块实填；链归纳复用已有定理 |
| ω 层任意 Ok 的实际回灌链 | `YiTSOrbit.Atω.orbit-ok` | 编译定理；保留底值对着 Ω_ω 的前提 |
| TreeStep 到 ω+1 的局部出口 | `YiTSBridge.AtStep.result` | 编译条件定理；额外需要 Low |
| 规范相邻路径的 ω+1 出口 | `YiTSBridge.Canon.result` | 编译定理；Low 已实填 |
| 任意 Ok 的 Low、完整 StepS | `YiTSBridge.AtStep.Low` 与原 `YiLTLift.StepS` | 未走通；不是否定 |
| 有限孩子处双方前三项 | `YiTSSeq`、`YiTSNote.fs-*` | 编译展开等式；用作有限测试，不作跨口径值比较 |

停止依据：主审要求对同一接口复用 YiSS 已触发的停止条件。本路读了其两个失败源码和日志，并核对到当前实现 Low 的证明链确实触及同一子义务：`YiLTLim.LFu` 的 `mΩ` 行经槽位回灌 `sf/chain` 调用源 ω 层到有限层的 `LFω`；其 `LFU` 在 `way G R′` 分出兄弟路径后，需要把任意实际有限路径 u（及复合 v ∙ u）交给按 n、j 索引的有限层保持。YiSS 对这个消去接口的两种设计都在 self 分支被检查器拒绝。本路不作同处第三次设计。这里只说当前证明链遇到同处接口失败，不声称 Low 必须经过它，不否定 Low、Q、StepS 或 Lift₁。

#### 2. 文件、自查与编译表

七件共 311 代码行；口径为 Agda 代码块中的非空、非整行注释行。每件均删自身 `.agdai` 冷编，`+RTS -M8G -s -RTS`，退出码 0，日志仅自身一条 Checking。内存栏是 RTS 的 maximum residency，另列 total memory in use；不是把总分配字节数当作堆峰值。

| 文件 | 代码行 | 冷编退出 | maximum residency (bytes) | total memory in use |
|---|---:|---:|---:|---:|
| `YiTSStep.lagda.md` | 37 | 0 | 136,323,624 | 267 MiB |
| `YiTSNote.lagda.md` | 36 | 0 | 663,345,912 | 1108 MiB |
| `YiTSSeq.lagda.md` | 34 | 0 | 136,258,136 | 262 MiB |
| `YiTSExit.lagda.md` | 56 | 0 | 1,353,058,056 | 2279 MiB |
| `YiTSMachine.lagda.md` | 51 | 0 | 161,923,296 | 274 MiB |
| `YiTSOrbit.lagda.md` | 41 | 0 | 1,393,197,024 | 2314 MiB |
| `YiTSBridge.lagda.md` | 56 | 0 | 1,437,188,312 | 2477 MiB |

不读记号的三件分别运行 `importclosure.py`（未加 `--only`，即全域）：`YiTSStep` 本地 6 模块、`YiTSSeq` 本地 7 模块、`YiTSMachine` 本地 11 模块，退出码均 0、禁用表命中 0。前两件闭包只有 YiRWBlock/YiRWFold/YiRWOps/YiRWPath/YiTBRow 及自身；Machine 另含 YiAbsObs/Frame/Sim/GIface/GSuff。源码逐件扫描禁用构造、本机路径结果均 0，文首均不超过 5 行。主审另外做的编译器依赖图检查不冒记为本路自查。

临时目录与确切路径供主审复核，归档时请脱敏：

- 临时目录 `<实验目录>`，库文件 `<实验目录>/libraries`。
- 第 0 步源码 `<实验目录>/YiTSCheck.agda`，最终日志 `<实验目录>/check.log`，退出 0。
- 接口最小检查 `<实验目录>/YiTSIfaceCheck.agda`、`iface-check.log`，退出 0。
- 局部桥最小检查 `<实验目录>/YiTSBridgeCheck.agda`、`bridge-check.log`，退出 0。
- 所有参数实填的闭实例 `<实验目录>/YiTSClosedCheck.agda`、`closed-check.log`，退出 0。
- 冷日志：`step-cold.log`，以及 `YiTSNote-cold.log`、`YiTSSeq-cold.log`、`YiTSExit-cold.log`、`YiTSMachine-cold.log`、`YiTSOrbit-cold.log`、`YiTSBridge-cold.log`，均在上述临时目录。
- 闭包日志：`closure.log`、`seq-closure.log`、`machine-closure.log`，同目录。

#### 3. 定理表与逐字陈述

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `Step.tree-step` | 后继层 Ω 树的折叠正是下层回灌链经下折、next 后的部分和极限 | YiTSStep | 编译定理 |
| `Step.branch` | 每个部分和都是总折叠的第一位置前驱 | YiTSStep | 编译定理 |
| `Step.part-zero`、`feed-zero` | 给出首输出与首回灌点 | YiTSStep | 编译定理 |
| `note` | 后继下标的 ψ₀(Ω_η) 的基本列由其 γ 链给出 | YiTSNote | 编译定理 |
| `covered`、`note-covered` | 链点覆盖给出总折叠关系；后者另用纯记号公式 | YiTSExit | 编译条件定理；ZeroCase 实填 |
| `Machine.Keep.Orbit` | 当前 ψ 的自身行接入既有抽象 Chain；不重复链归纳 | YiTSMachine | 编译模块实填 |
| `Atω.self-law`、`weak-law` | ω 层任意 Ok 上满足接口的 SelfKeep、Weak | YiTSOrbit | 编译定理 |
| `Atω.orbit-ok` | 实际回灌链逐点对着 γ 链 | YiTSOrbit | 编译定理 |
| `AtStep.cover`、`result` | 给定朝 0 的 Low，TreeStep 与纯记号公式接成 ω+1 出口 | YiTSBridge | 编译条件定理 |
| `Canon.low`、`result` | 规范相邻路径上 Low 实填，得到不再带 Low 的结果 | YiTSBridge | 编译定理 |

以下按文件逐字摘录签名；嵌套签名的参数上下文按源码模块保留。辅助定义 childBase/feed/chain/parts、单层框架记录与各实例的完整参数在相应源码中，不在签名中用省略号代替。

##### YiTSStep

```agda
module Step (x : Tr zero) (o : Ok (h₁ (suc x))) (r : Rb (h₁ (suc x)))
            (B : Base (h₁ (suc x))) (w : zero ≤ h₁ x) (β : Tr⁺ zero) where
  TreeStep : Set
  TreeStep = proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x))))) ≡ proj₁ (limc⁺ parts)
  tree-step : TreeStep
  branch : (k : ℕ) → zero ⊢ cum (λ n → proj₁ (parts n)) k ◃ proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x)))))
  part-zero : proj₁ (parts 0) ≡ proj₁ (next⁺ β)
  feed-zero : chain 1 ≡ proj₁ (next⁺ (childBase (h₁ x) self))
fin : (n : ℕ) → Step.TreeStep (nat n) (proj₂ (Ok-tw 1) (suc (nat n))) (rb-no (h₁ (suc (nat n)))) (B₀ (h₁ (suc (nat n)))) (z≤ (h₁ (nat n))) (Ωt zero)
om : Step.TreeStep ωᶜ (proj₂ (Ok-tw 1) (suc ωᶜ)) (rb-no (h₁ (suc ωᶜ))) (B₀ (h₁ (suc ωᶜ))) (z≤ (h₁ ωᶜ)) (Ωt zero)
```

##### YiTSNote

```agda
cofΩS : ∀ η → cof η ≡ c1 → cof (E.Ωt η) ≡ cΩ (pred η)
fsTΩS : ∀ η → cof η ≡ c1 → ∀ ζ → fsT (E.Ωt η) ζ ≡ ζ
gt0 : ∀ ν → cmpᵀ (sucT ν) [] ≡ gt
note : ∀ η → cof η ≡ c1 →
       (cof (ψᴺ 0 (E.Ωt η)) ≡ cω) ×
       (∀ k → fsn (ψᴺ 0 (E.Ωt η)) k ≡ ψᴺ 0 (γT (E.Ωt η) (pred η) k))
fs-00 : fsn (ψᴺ 0 (Ωᴺ 1)) 0 ≡ ψᴺ 0 (Ωᴺ 0)
fs-01 : fsn (ψᴺ 0 (Ωᴺ 1)) 1 ≡ ψᴺ 0 (ψᴺ 0 (Ωᴺ 0))
fs-02 : fsn (ψᴺ 0 (Ωᴺ 1)) 2 ≡ ψᴺ 0 (ψᴺ 0 (ψᴺ 0 (Ωᴺ 0)))
fs-10 : fsn (ψᴺ 0 (Ωᴺ 2)) 0 ≡ ψᴺ 0 (Ωᴺ 1)
fs-11 : fsn (ψᴺ 0 (Ωᴺ 2)) 1 ≡ ψᴺ 0 (ψᴺ 1 (Ωᴺ 1))
fs-12 : fsn (ψᴺ 0 (Ωᴺ 2)) 2 ≡ ψᴺ 0 (ψᴺ 1 (ψᴺ 1 (Ωᴺ 1)))
```

##### YiTSSeq

```agda
module FinSeq (n : ℕ) where
  fs₀ : cum (λ k → proj₁ (F.parts k)) 0 ≡ piece₀
  fs₁ : cum (λ k → proj₁ (F.parts k)) 1 ≡ piece₀ + piece₁
  fs₂ : cum (λ k → proj₁ (F.parts k)) 2 ≡ (piece₀ + piece₁) + piece₂
```

##### YiTSExit

```agda
module Exit (x : Tr zero) (o : Ok (h₁ (suc x))) (r : Rb (h₁ (suc x)))
            (B : Base (h₁ (suc x))) (w : zero ≤ h₁ x) (β : Tr⁺ zero) where
  covered : ∀ t → cof t ≡ cω →
            (∀ k → Σ ℕ λ m → M⁰ (fsn t k) (proj₁ (parts m))) →
            M⁰ t (proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x))))))
  note-covered : ∀ η → cof η ≡ c1 →
                 (∀ k → Σ ℕ λ m → M⁰ (ψᴺ 0 (γT (E.Ωt η) (pred η) k)) (proj₁ (parts m))) →
                 M⁰ (ψᴺ 0 (E.Ωt η))
                   (proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x))))))
module ZeroCase where
  chain-ok : ∀ k → M⁰ (γT (Ωᴺ 1) [] k) (Z.chain (suc k))
  cover : ∀ k → Σ ℕ λ m → M⁰ (ψᴺ 0 (γT (Ωᴺ 1) [] k)) (proj₁ (Z.parts m))
  result : M⁰ (ψᴺ 0 (Ωᴺ 1))
    (proj₁ (ψ (fn 1) o r Bs zero (inu (λ _ → self)) (Ωt zero) (proj₁ (Ωt (fn 1)))))
```

##### YiTSOrbit

```agda
base-ok : Wω.Mω (E.Ωt ωᵀ) (proj₁ (Ωt Wω.Lω))
module Atω (o : Ok Wω.Lω) (r : Rb Wω.Lω) (B : Base Wω.Lω) (β : Tr⁺ Wω.Lω) where
  self-law : K.SelfKeep
  weak-law : K.Weak
  γ-eq : ∀ k → C.γ k ≡ E.γT (E.Ωt (E.sucT ωᵀ)) ωᵀ k
  orbit-ok : Wω.Mω (E.Ωt ωᵀ) (proj₁ β) → ∀ k →
             Wω.Mω (E.γT (E.Ωt (E.sucT ωᵀ)) ωᵀ k) (z k)
```

##### YiTSBridge

```agda
module AtStep (o : Ok (h₁ (suc ωᶜ))) (r : Rb (h₁ (suc ωᶜ))) (B : Base (h₁ (suc ωᶜ)))
              (w : zero ≤ Wω.Lω) (β : Tr⁺ zero) where
  Low : Set
  Low = ∀ {a z} → Wω.Mω a z → M⁰ (ψᴺ 0 a)
    (proj₁ (ψ Wω.Lω (proj₂ o tt) (proj₂ r tt) TS.childBase zero w β z))
  cover : Wω.Mω (E.Ωt ωᵀ) (proj₁ (TS.childBase Wω.Lω self)) → Low →
          ∀ k → Σ ℕ λ m → M⁰ (ψᴺ 0 (E.γT (E.Ωt (E.sucT ωᵀ)) ωᵀ k)) (proj₁ (TS.parts m))
  result : Wω.Mω (E.Ωt ωᵀ) (proj₁ (TS.childBase Wω.Lω self)) → Low →
    M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ)))
      (proj₁ (ψ (h₁ (suc ωᶜ)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc ωᶜ))))))
module Canon (oc : ∀ n → Ok (fn n)) (r : Rb (h₁ (suc ωᶜ))) (B : Base (h₁ (suc ωᶜ)))
             (ok : OKB B) (ws : ∀ n → zero ≤ fn n) (zw : ∀ n → ZP (fn n) (ws n))
             (β : Tr⁺ zero) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) where
  gb : Wω.GBω A.TS.childBase []
  hΩ : Wω.Mω (E.Ωt ωᵀ) (proj₁ (A.TS.childBase Wω.Lω self))
  low : A.Low
  result : M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ)))
      (proj₁ (ψ (h₁ (suc ωᶜ)) o r B zero (inu (λ _ → inu ws)) β (proj₁ (Ωt (h₁ (suc ωᶜ))))))
```

##### Machine 的复用而非重证

`Machine` 的折叠字段逐字是 `proj₁ (ψ ℓ o r B ℓ self β x)`；轨道 `z k` 是该自身折叠后 next 的迭代第 k+1 项。`zs k = ◃l zero`。模块实填为：

```agda
module Chain = S.Suff.Chain graded doms sk wk tt β tt P g₀ z zs
open Chain public using (γ; chain)
```

`chain` 的原始声明仍在 `YiAbsGSuff.Chain`，本路没有再写一份归纳：

```agda
chain : R ℓ (cl ℓ P) (bt β) → R ℓ g₀ (z 0) → ∀ k → R ℓ (γ k) (z k)
```

前提可满足：`Atω.self-law`、`weak-law` 以实际封闭族 `Wω.Mω` 填两个律；`base-ok` 给 Ω_ω 起点，其后 `mw h (◃l zero)` 给首轨道点。`Canon` 以 `Uω.FoldU.LFu` 实填 Low。`YiTSClosedCheck` 用 rb-no、B₀、Ωt zero、字面的 inc 相邻路径以及 z≤/zp-z，把整个 Canon 的参数全部实填后仍编译为 0；没有靠矛盾前提。

#### 4. 第一个障碍、翻译账与停止范围

第一个未完成的字段是 `YiTSBridge.AtStep.Low` 在孩子 ω、任意实际相邻证据 `proj₂ o tt` 上的版本。`TreeStep` 自身没有这个条件；它是一条对任意树的树等式。为了从它推出记号关系，实际链已由自身保持给出，仍要把链点沿一致路径折到第 0 层。

按当前保持证明，`YiLTLim.LFu` 的 mΩ 行进入 `Fold.chain`。回灌用 `sf`，其目标路径是 `inc m (posW⁼ ... t)`；保持从 `LFω` 进入 `LFU`，在那里 `way G R′` 产生路径 u 或 v ∙ u。任意 R′ 下，这些不再自带字面 `Sb`。这与 YiSS 两个失败设计试图提供的“任意 u : fn j ≤ fn n 进入 n,j 索引的保持”相同。已读的原文件与日志：

- `<YiSS实验目录>/YiSSPath.agda`、`YiSSPath.log`：`CP n j u` 直接保留 self/inc/inu；`canon n .n self = cs` 第 17 行，`SplitError.UnificationStuck`，退出 42。
- `<YiSS实验目录>/YiSSPath2.agda`、`YiSSPath2.log`：先用无数字索引的 `FP u`，再用 `Elim.run` 回到 n,j；`run n .n self fs = same n` 第 25 行，同类首错，退出 42。前面的 finite 未独立编译，不算成功定理。

主审已复跑这两个失败文件。本路读源码、陈述、错误日志后，按主审明确要求对同处接口复用停止条件；没有在本路再设计第三种消去。失败记录不是否定定理；没有说所有 Low 的证明只能经该接口，也没有否定完整 Q、StepS 或 Lift₁。

这一站实际用了原折叠的哪些行、字段：

1. `YiRWOps.Ωt (nd sS h)` 的结点与孩子嵌入 `upz tt (suc c,...)`。
2. `YiTBRow.ψ` 的 Ω 结点行，配合 `kp`/`node⁺`：这里槽位恰是孩子层自身，`kp⁼` 为 nothing，故取回灌链的部分和极限。
3. 嵌入的 `inu` 行把结果交给孩子，并把零左项的底原样交接；后继行给 `next⁺`。
4. 槽位回灌中的 `posW` 进入孩子的自身折叠；`next⁺` 的第 0 个分支给 `zs`，也给每一步的放宽。
5. `limc⁺` 提供部分和与其合法步进；原 `mono` 仍负责合法性。没有新增树字段或合法性字段，也没有按 η 定制树定义。

树基本列与记号基本列的已测区别只按各自的等式陈述：树的第 0 项恒为 `next⁺ (Ωt zero)`，第 1、2 项分别是 `piece₀ + piece₁` 与 `(piece₀ + piece₁) + piece₂`；piece₁/piece₂ 含孩子层的自身折叠与下折。记号侧 n=0 的前三项是 ψ₀(Ω₀)、ψ₀(ψ₀(Ω₀))、ψ₀(ψ₀(ψ₀(Ω₀)))，n=1 的前三项是 ψ₀(Ω₁)、ψ₀(ψ₁(Ω₁))、ψ₀(ψ₁(ψ₁(Ω₁)))。这些是双方各自编译过的展开等式，不能把跨类型的符号形状直接当作值比较，也没有断言两边基本列逐项相同。

翻译账：TreeStep 与机器适配的陈述、证明、闭包不读记号；具体 `Mω`、自身保持的记号解释与 γ 对照仍在验收侧。它们给出这一站对既有 SelfKeep、LowKeep 的需要与规范实例，不算已经树自足。新增适配只用于复用接口，不新增树、折叠或合法性的数学内容；无“第 4 层逼出”改定义。

#### 5. 偏离、事故与引用范围

- 本路开始时四件文件只能交树等式、纯记号公式、条件出口和展开测试，尚没有完成原桥。主审要求继续后，新增 Machine、Orbit、Bridge，实际接通了树等式到规范 ω+1 的局部桥；完整 StepS 仍未填。没有将四件阶段成果当作原题完成。
- 修复过 C/b₀ 与底座字段撞名、module T 与数据类型模块撞名、逗号构造子漏导入；这些是 scope 错误，没有计作数学重新设计。桥的临时文件曾混用 YiTBRow.fn 与 YiCLFam.fn，出现 nat 函数的定义性相等失败，改为隐藏前者、统一引用后者；没有加入 Funext，也没有把两个函数说成相等。
- 每路一个 Agda；每次均 8G。未用 ignore-interfaces，未删共享底座接口，未修改旧文件或另两路前缀；不装包、不提交、不推送。最终七份冷日志均仅自身 Checking；临时桥早轮曾因主审正在冷编其依赖而重检 YiSSOmega，该轮不充作最终冷日志。
- 没有触发本路堆耗尽或第 0 步不成立。最后停止只据同一证明链接口在 YiSS 的两次已复核失败，未冒称本路又尝试了两次，也未称数学否定。
- 实际读了所引用的 YiAbsGIface/GSuff/GRow、YiTBRow、YiRWFold、YiRWOps、YiLTLift、YiLTLim、YiHCRel、YiTS 自己全部代码，以及 YiSSOmega 的 Self 保持、YiSSCheck 的规范实例、YiSSScope 的否定陈述和上述两个失败源码/日志。较早 YiHCPlus/YiHCOmega 的背景只查了相关签名与相关证明段，没有宣称整模块独立审计；本路实际复用 SS 的新折叠 Self 证明。没有仅凭转述而记成已证明的新结论。

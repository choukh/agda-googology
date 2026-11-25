# 记号基本列情形 × 树侧折叠行与上下文的对照表（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 04:11 至 04:22 |
| 工具调用 / agda 编译 (粗数) | 33 / 5 |
| token (usage 字段，按消息去重) | 输出 66478；新写入缓存的输入 203670；读缓存的输入 4201840；其余输入 56 |
| 写过的仓库文件 | `CompareTable.md` |
| 文件前缀 | `YiCM` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0，导入闭包干净；保留判定对一切层号、证据、槽位、目标只有三个出口（kp-exit）；表里所有值上低与未知的格都落在分叉出口（判断，依据逐格填表）；分叉出口上的缺陷对参数一般地写成形状陈述（diag-slot、fallᶻ、drop-idx、drop-tw）；对照表 probes/Survey/CompareTable.md；有限测试未做 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b77/YiCM.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "额外的规则"、"规则" 与 "回报" 各节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件与简报允许的那一个调查文档，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiCM 回报：记号基本列情形 × 树侧折叠行与上下文的对照表

#### 1. 判决

**对纲领与目标意味着什么。**
- 对照表给出一条不按站、不按塔项数的结构结论：保留判定 `kp` 对一切层号、证据、槽位、目标路径只有三个出口（保留 / 同层或高于 / 分叉），这是编译定理 `YiCMExit.kp-exit`。前两个出口上树的效果按 "低于目标保留、同层对角、高于走链"。
- 表里所有 "值上低" 与 "未知" 的格都落在第三个出口 "分叉"：Ω 形状结点上，材料在孩子 c 之下，目标在孩子 c′ 之下。这一句是判断，依据是逐格填表，没有编译成一条定理。
- 记号侧没有这个区分。记号的和是平的列表，不记 "材料在哪个孩子"，ν+1 与 u 的比较推迟到展开时由可判定的 `cmpᵀ` 做；树在折叠当下要交出 `Tr j` 的值。这是第一处分歧（判断）。
- 对 "让树自足"：分叉这一类缺陷在所有 Ω 形状层号上同形，已写成对参数一般的形状陈述（下文定理表）。这给 "闭包定理与阶段无关" 提供了陈述的形状，但没有值的定理。
- 没有改任何定义，没有新的值定理，没有否定任何路线。

**各步到哪一步。**

| 步 | 状态 |
|---|---|
| 0 骨架（记号情形表、树侧行、上下文种类） | 完成，在 `CompareTable.md` §1–§3 |
| 1 对照（两张表） | 完成，§4 现行折叠、§5 换基折叠 |
| 2 判定件 | 完成两个文件，均冷编退出 0 |
| 3 有限测试（贴标签找分叉点） | **没有做** |
| 4 交付 (a)–(e) | 完成，§4–§9 |

**"上下文的种类是否有限"。** 派发字母表有限；上下文本身（槽位，目标路径）是不限长的词，不有限。`kp` 在词上只有三个出口（编译）。够用的有限分类是 "出口 × 层号字面带的证据"（§3.3，判断）。分叉出口不能按孩子再细分到效果确定：同一孩子的对角上，槽位是孩子层号自身（同层）与槽位字面就是目标的槽位（低于目标），结果都是 `nothing`（`diag-same`、`diag-slot`，编译）。

**问题表。**

| 问题 | 位置 | 档 |
|---|---|---|
| 分叉出口上孩子侧槽位一律不保留，含槽位字面就是目标槽位的情形 | `kp` 的 R77 行；现行与换基共用 | 形状：编译（`YiFINeg.kp-drop`、`YiCMExit.diag-slot`）；值低：判断（YiVA、AuditD，作者已关闭 V287） |
| 嵌入行在两个孩子都非零时回退到第 0 层，对一切 Ω 形状层号 | `YiTBRow.ψ` 配 `rbᶻ` 的 R95 行 | 形状：编译（`YiCMExit.fallᶻ`）；值低：判断 |
| 下标侧槽位推进后在偏移里的 Ω 形状结点上分叉，槽位层有到目标的字面路径仍走链；塔第 n+1 项对一切 n | `kp` 的 R79 行之后到 R77；现行与换基共用 | 形状：编译（`YiCMCross.drop-idx`、`drop-tw`、`chain-twᴮ`）；值与是否在实际链上被问到：判断 |
| 换基折叠的值全在 "有证据且目标在地板之上" 一格，未证 | `YiBSFold.ψ` 的换基行 | 未知（`YiSVRed.StepS` 未证，`YiBLFold.lowᴮ` 条件于 `OutR`） |
| `seen` 内部用 `rb-no`，再遇分叉就回退 | `YiBSBase.seen` | 定义事实；后果是判断 |
| 表里 "值上不低" 的多数格只有接口上的行引理与形状引理 | §4、§5 | 判断；具体折叠的值只在第 0 到 2 站是定理 |

**换基候选在表上还剩的格（§9）。** R77 未改；下标侧分叉未改（证据自己能给保留，`keepS` 没有接进折叠）；地板之上一格的值；`seen` 内部；替身单调在偏移含 Ω 形状时没有；与现行折叠没有比较定理；y 一般时只进尾项。

#### 2. 文件表

| 文件 | 代码行（非空） | 总行 | 冷编退出码 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiCMExit.lagda.md` | 116 | 164 | 0 |
| `<仓库>/probes/OCF/Lean/YiCMCross.lagda.md` | 67 | 118 | 0 |
| `<仓库>/probes/Survey/CompareTable.md` | — | 240 | — |

自查：两个模块删自己的接口后冷编，日志各只有自己一行 `Checking`；禁用构造与本机路径检索为 0；`importclosure.py` 对两个模块均 "禁用表命中: 0，OK"。堆上限 6G，没有撞墙。

#### 3. 定理表

全部是编译定理，无前提，不读记号。除 `kp-exit`、`kept-below`、`psh-at` 外都是形状档（输出是哪个构造子），不是值的定理。

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `kp-exit` | `(ℓ : L) (o : Ok ℓ) (p : Pos ℓ) → ∀ {j} (w : j ≤ ℓ) → Exit (at ℓ p) (kp ℓ o p w)` | 保留判定的结果是三种出口之一 | YiCMExit |
| `Exit`（构造子） | `kept : ∀ q cv e → at j q ≡ a₀ → Exit a₀ (just (q , cv , e))`；`high : j ≤ a₀ → Exit a₀ nothing`；`cross : ∀ {k′} {h′ : Tr k′ → L} (c c′ : Tr k′) → a₀ ≤ h′ c → j ≤ h′ c′ → Exit a₀ nothing` | 保留时目标槽位与原槽位同层号；不保留时或者目标有到槽位层的字面路径，或者在 Ω 形状结点的两个孩子下分叉 | YiCMExit |
| `kept-below` | `Exit a₀ {j} {X} {x₀} (just (q , cv , e)) → a₀ ≤ j` | 保留时槽位层号有到目标的字面路径 | YiCMExit |
| `diag-same` | `∀ k h (o : Ok (nd (sΩ k) h)) c → (kp (nd (sΩ k) h) o (inj₂ (c , inj₁ tt)) (inc c self) ≡ nothing) × (at (nd (sΩ k) h) (inj₂ (c , inj₁ tt)) ≡ h c)` | 对角上槽位是孩子层号自身（同层）：不保留 | YiCMExit |
| `diag-slot` | `∀ k h (o : Ok (nd (sΩ k) h)) c (p′ : Pos (h c)) → (kp (nd (sΩ k) h) o (inj₂ (c , inj₂ p′)) (inc c self) ≡ nothing) × (Br (h c) p′ ≡ Br (nd (sΩ k) h) (inj₂ (c , inj₂ p′))) × (at (h c) p′ ≡ at (nd (sΩ k) h) (inj₂ (c , inj₂ p′)))` | 对角上槽位字面就是目标的槽位：仍不保留，对一切 Ω 形状层号 | YiCMExit |
| `tb-nz` | `∀ k (h : Tr k → L) {c c′ : Tr k} → NZ c → NZ c′ → tbᶻ k h c c′ ≡ nothing` | 最小比较表在两个非零孩子上没有条目 | YiCMExit |
| `fallᶻ` | `∀ k h (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j {c c′} (v : j ≤ h c′) β x (y : Tr (h c)) e → NZ c → NZ c′ → TB.ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B j (inc c′ v) β (up x c y e) ≡ TB.ψ (nd (sΩ k) h) o (rbᶻ (nd (sΩ k) h)) B j (inc c′ v) β x ⊞ TB.ψ₀ʳ (h c) (proj₂ o c) (rbᶻ (h c)) y` | 现行嵌入行在非零孩子对上逐字回退，对一切 Ω 形状层号 | YiCMExit |
| `fallᴮ` | `… → BS.ψ (nd (sΩ k) h) o (nothing , rc) B j (inc c′ v) β (up x c y e) ≡ BS.ψ … β x ⊞ BS.ψ (h c) (proj₂ o c) (rc c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y` | 换基折叠无证据时回退 | YiCMExit |
| `rebᴮ-lo` / `rebᴮ-hi` | 前提 `BB.route S j c′ v ≡ inj₁ u`（或 `inj₂ u`），结论是换基行等于 "经 `back S c u` 进孩子 c 朝 j 折 y"（或 `seen … c ⊞` 第 0 层尾项） | 有证据时按地板上下二分；前提的实例见 `YiBLFold.route-tw1`、`AuditEKeep.above` | YiCMExit |
| `cross-drop` | `Cross a u v → (o : Ok a) (t : Pos⁼ k) → kp⁼ a o (psh u t) v ≡ nothing` | 推进路径与目标路径分叉时不保留 | YiCMCross |
| `drop-idx` | `∀ k h (o : Ok (nd (sΩ k) h)) (t : Pos⁼ k) c′ {j} (v : j ≤ h c′) → Cross (h c′) (proj₂ (proj₁ o) c′) v → kp (nd (sΩ k) h) o (inj₁ t) (inc c′ v) ≡ nothing` | 下标侧槽位推进后分叉：不保留 | YiCMCross |
| `drop-tw` | `∀ n (p : Pos (tw n)) (g : Br (tw n) p → Tr (tw n)) (t : Pos⁼ (tw n)) (c″ : Tr (at (tw n) p)) {j} (v : j ≤ tw n ⊕ ↑ (tw n) (g (fromBr (tw n) p c″))) → kp (tw (suc n)) (Ok-tw (suc n)) (inj₁ t) (inc (Ω p g) (inc c″ v)) ≡ nothing` | 审查 E 路 `drop₂` 的一般形式：塔第 n+1 项，一切 n | YiCMCross |
| `c′-inst` | `∀ n → Σ (Pos (tw (suc n))) λ p → Σ (…) λ g → proj₁ (Ωt (tw (suc n))) ≡ Ω p g` | `drop-tw` 的前提在 n ≥ 1 时可满足（n = 0 时空真） | YiCMCross |
| `below-tw` | `∀ n (b : L) → tw n ≤ tw n ⊕ b` | 那一格上槽位层有到目标的字面路径 | YiCMCross |
| `chainᴿ` / `chainᵀ` / `chainᴮ` | `… → kp ℓ o p w ≡ nothing → IsL (proj₁ (ψ ℓ o … B j w β (Ω p g)))`（三个折叠各一条） | 不保留时三个折叠的输出都是 ℕ 极限 | YiCMCross |
| `chain-twᴮ` | `∀ n p g c″ {j} v (B : Base (tw (suc n))) β → IsL (proj₁ (BS.ψ (tw (suc n)) (Ok-tw (suc n)) (rb-tw (suc n)) B j (inc (Ω p g) (inc c″ v)) β (proj₁ (Ωt (tw (suc n))))))` | 换基折叠在塔各项的那一格上是链，对一切 n、底、起点 | YiCMCross |
| `keepS` | `∀ {k h} (S : Schema k h) (t : Pos⁼ k) {j} → floor S ≤ j → Keep j (Br (nd (sΩ k) h) (inj₁ t)) (fromBr (nd (sΩ k) h) (inj₁ t) zero)` | 换基证据给出的保留；搬自留档附件 AuditEKeepFix，没有接进折叠 | YiCMCross |
| `keepS-lift` | `∀ {k h} (S : Schema k h) (t : Pos⁼ k) s (b : Ch s → L) → IsJust (keepS S t (lift (floor S) (nd s b)))` | 目标是地板加非零偏移时 `keepS` 确实保留 | YiCMCross |

`Cross` 只含后继形状与一致目标的共同下行，不含 ℕ 极限形状与下标层侧的共同下行（那两种要层号证据）。

#### 4. 第一个障碍

没有撞到检查器或堆的障碍。数学上没有做成的一步是：把 "缺陷都在分叉出口" 写成定理，即把 `kp-exit` 接到 `YiFIIface.KeepLaw` 的证据域上，证明保留律的义务只落在 `cross` 出口。这一步没有尝试，不是被挡住；它需要先读 `YiFIIface` 的 `Ev` 与 `KeepLaw` 的定义体，本路只读了文首。

值的一侧（任何一格 "掉值" 的编译定理）本路没有碰，状态与之前相同：没有。

#### 5. 偏离与事故

- **第 3 步没有做。** 简报标为可选；表里没有新的 "测" 档条目，分叉点的定位全靠定义子句与形状定理，不是靠贴标签。
- **§6 的先后顺序是判断。** 按留档回报里的描述排（第 3 站链步 → 塔第 1 项换基 → 塔第 2 项起），没有在实际链点上展开核对。
- **没有读、只凭转述或文首引用的：**
  - `YiVA.md` 没有读，只用了 AuditD 与 README 对它的转述。
  - `YiAbsGRow`、`YiAbsGSuff`、`YiFIIface`、`YiBLIface`、`YiSVRed`、`YiSVMono`、`YiBCCover`、`YiMTHit`、`YiBSCrit`、`YiFYRef` 只读了文首，并用检索确认被引名字存在；陈述没有逐条核。
  - `RR3-Backward.md` 只读了 §2；`Review11-R11Exit.agda.txt` 没有读。
  - `AtomInventory.md` 读了 §0–§4，§5 以后没有读。
  - Bedrock 性能手册与 `EBOHandbook` §4.2、§4.6 没有读（没有遇到性能问题）。
- 表 A 里 "值上不低" 的若干格引用的是 F2 有限层号实例或抽象接口上的行引理（`succᶠ`、`leafᶠ`、`row-node-diag` 等），不是现行折叠上的值定理；表内已逐格标出。
- 没有改任何已有文件，没有碰其他前缀，只删过自己两个模块的 `.agdai`。临时目录里只有编译日志。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：记号基本列情形 × 树侧折叠行与上下文的对照表（前缀 YiCM，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同时在跑的第七十七批三路（前缀 `YiZS`、`YiQD`、`YiEM`）与你互不导入、不碰它们的前缀。

#### 作者的话（原文）与决定
作者 2026-11-17："我现在更担心的是我们的研究方法，比路线更元一层。真的只有这样一站一站吗？能否借助记号搞清楚内在结构，然后对比树的定义（包括整个归纳类型的规则）在树的生成上，和记号+基本列定义加终止证明生成的树，在什么节点和站上有区别。我的意思是更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。作者选项原文："派一路做对照表，第七十七批照跑 (Recommended)"。

#### 为什么要这张表（主审核过的事实）
- 11-14 的原子清单 `probes/Survey/AtomInventory.md` 已把主线折叠逐行列出（R01 到 R103），对照 "低于目标保留、同层对角、高于走链" 标注；其中 R77 行 `kp (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = nothing` 当时标 "效果未达：地板以下的槽位也不保留"，LowKeep 栏 "未知"。11-17 两份先读定义的 Fable 审核（留档 `probes/Survey/Reports-2026-11-16/YiVA.md`、`AuditD.md`）判定掉值的正是这一行，作者已关闭现行折叠上的那一格（台账 V287）。当中十几批是一站一站深挖。原子清单缺两样：记号那一半（每个基本列情形由哪一行生成），和每格对参数一般的判定。
- 不走站的证明形状早就有：`probes/Survey/RR3-Backward.md` §2（终点只要对一切记号项的两条一步不等式）、`Reports-2026-11-12/attachments/Review11-R11Exit.agda.txt`（`R11Exit.ebo-lower`）、`YiAbsGSuff.endpoint`、`YiAbsGRow.gen→low`（关系由六条规则生成时，保持归到折叠像对六条封闭）、`YiFIIface`、`YiBLIface`（对折叠参数化的保留律、回退律、换基律、出口）。它们都把难点归到 Ω 共尾处那一步。
- 刚回来的审查 E 路（留档 `AuditE.md`，判定件附件 `attachments/AuditE-AuditEKeep.agda.txt`、`AuditE-AuditEKeepFix.agda.txt`）：换基候选 `YiBSFold` 的测试全在塔第 1 项；塔第 2 项上顶结点的下标槽位低于目标仍走链（`drop₂`、`chain₂`）；换基证据自己给出保留路径（`keepS`）；替身内部用 `rb-no`；替身单调只对不含 Ω 形状的偏移（`YiSVMono.mono-path` 的前提）。这又是 "取样只在最低一层" 的同一类问题。

#### 要做的（按序）
0. **骨架（先写出）**：
   - **记号侧情形表**：按 `probes/OCF/Align/EBO.lagda.md`（`cof`、`pred`、`fsT`、`γT`、`Ωs`）与 `probes/OCF/Align/EboLeanDef.lagda.md`（`fsn`）的定义子句，把基本列按项的形状列全（零、后继、ω 共尾、ψ_ν(α) 中 α 共尾为 Ω_μ 时按 μ 与 ν 的关系细分、和、Ω 的下标等），每个情形写出 "这一步要生成什么分支"。
   - **树侧行 × 上下文**：现行折叠（`YiRWFold.kp`、`YiTBRow.ψ`、`YiMTTab.rbᶻ`）与换基折叠（`YiBSFold`、`YiBSBase.seen`、`YiRBSib`）各列全行；再定义 "上下文的种类"（结点种类、目标路径的种类 `self`/`inu`/`ink`/`inc`、比较表或换基证据的状态、槽位是下标侧还是孩子侧、槽位层号与目标的字面关系）。**先回答：上下文的种类是否有限**；若不有限，说明原因，并给出一个够用的有限分类（或说明为什么没有）。
   - 写进 `probes/Survey/CompareTable.md`（像 `AtomInventory.md` 那样的调查文档；这是本路唯一允许的非 Agda 文件）。
1. **对照**：每个记号情形 × 上下文种类 → 由哪一行或哪几行的复合生成对应的分支；分四档：**逐项相同**、**值上不低**、**值上低**、**未知**。两张表：现行折叠、换基折叠。每格标依据（已编译的定理名，或判断）。注意：对应只按值（≼），不按逐项；"值上不低" 的差别是树自己的形状，保留，不建议改成逐项相同（AGENTS "规则形状不从记号的基本列细规则读出"；作者 11-14："不能以'追求同步'为名改树的定义形状"）。
2. **判定件**：对 "值上低" 与 "未知" 的格，按它们在终点归约里被问到的先后排序（站 → 里程碑 → 链步 → 塔各项），给最靠前的几格写对参数一般的判定件（对一切孩子、一切层号变量的编译定理或否定，放 `probes/OCF/Lean/YiCM*.lagda.md`；不在具体闭项上展开）。已有的不重证，引用名字（例如 `YiRQDom.drop`、`YiFINeg.kp-drop`、`YiDGDiag.ColW.wdecα`、`YiRKCell.w1`/`w2`/`w3`、`YiBLFold.top-noEv`/`main-noEv`；E 路的 `drop₂` 在附件里，可在你的文件里重写成对参数一般的形式）。
3. **辅助（有限测试，可选）**：在一批小项上同时展开记号生成的参照树（`EboLeanTree`、`YiRefTw2.Rt`、`YiExInst`）与树侧折叠，用标签工具（`OCF.Align.OrdLabZCorrespond.Lab`、`AccTreeLab`、`YiGLFrame.Lbl`）给树的结点贴记号标签，第一个贴不上的结点就是分叉点；只用来填表，标 "有限测试"。
4. **交付**：(a) 两张表；(b) 缺陷格的排序；(c) 对每个缺陷，修它要动哪一行、树侧理由是什么（不做定义改动，交作者）；(d) 如果表里有一类缺陷在所有层号上同形，写出那条对参数一般的陈述（这是 "阶段无关" 的判据）；(e) 换基候选在表上还剩哪些格。

#### 额外的规则
- `probes/Survey/CompareTable.md` 不受 "文首不超过 5 行" 的限制，但写成表格，不写散文；判断与定理分开标档。
- 不改任何已有文件；不碰其他前缀。

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


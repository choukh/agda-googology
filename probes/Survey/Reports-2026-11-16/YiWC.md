# 较弱链形状对 EBO 参照（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 06:36 至 07:07 |
| 工具调用 / agda 编译 (粗数) | 64 / 11 |
| token (usage 字段，按消息去重) | 输出 165469；新写入缓存的输入 340302；读缓存的输入 12205380；其余输入 108 |
| 写过的仓库文件 | `YiWCIface.lagda.md`, `YiWCTw1.lagda.md`, `YiWCWire.lagda.md` |
| 文件前缀 | `YiWC` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0，YiWCIface 导入闭包干净；较弱链形状给出结点出口（outʳ），塔第 1 项那一格 P 空时成立（weak-tw1），原形状不成立（¬strong-tw1）；全量化的较弱形状因参照不坍缩的点不成立（¬aboveʳ-tw1）；接线变体去掉了链从第 1 项起的移位（ebo-endʳ⁰）；链的步 StepW 未证，执行方判断与 LowSlot 同因（量化域太宽） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b80/YiWC.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### YiWC 回报（较弱链形状对 EBO 参照，Opus 5.5）

##### 1. 判决

**对纲领与目标意味着什么。** 较弱链形状（`RefChainʳ`：参照链第 k 项只要不高于树的链上的某一项）是树侧的放宽，已经写成编译过的抽象定理，不读记号（`YiWCIface.outʳ`）。它的作用是让树直接用 node⁺ 自己的链（从第 0 个链点起），不必再为对齐记号的 γ 链（从 Ω_κ 起）加 `YiWRZero` 里"链从第 1 项起"那一步移位。这算摆脱翻译的一小步：去掉一处为对齐记号而加的脚手架。它没有触及两处真正的障碍：
- 链的步：槽位层要支配上下文前缀 K，这是 `LowSlot` 那一类要求；
- 辅助系统无证据结点上的不坍缩参照，即 κ = 0 的情形。

不改树、折叠、合法性。

**各步到哪一步。**
- 第 0 步：陈述已写出并编译。第一个临时文件在开工约 15 分钟时编译通过。
  - 在辅助系统上，全量化的 `AboveLʳ` 不成立（`¬aboveʳ-tw1`，下面"偏离"一节有说明）。
  - 在 `YiWRZero` 的系统上，较弱形状没有被否定：目标是第 0 层，一切参照都坍缩。
- 第 1 步：
  - 塔第 1 项那一格，P 空时较弱形状成立，是编译定理（`weak-tw1`）。
  - "一般"未走通：只把它化成第 0 项 `BaseW` 加步 `StepW`；步没有证，也没有否定。
- 第 2 步：接线变体 `Wireʳ` 已编译。
- 分级实例的选择：
  - 辅助那一格用 `YiBAEbo.gradedᴱ`。这一格需要 ν = 1，主系统的 `Below` 才成立；`gradedᵍ` 只有 ψ₀ 上下文，在那里 `main-¬below₀` 成立。
  - 接线用 `YiWREnd.gradedᴮ`。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| Tw1 格，精确参照 Ω₂，P 空：较弱形状成立，下标取 m = k+1 | `YiWCTw1.Tw1W.weak-tw1` | 编译定理 |
| 同一格上原形状（逐项对齐）对一切 P 不成立 | `Tw1W.¬strong-tw1` | 编译定理 |
| 同一格上全量化的 `AboveLʳ` 对一切 P 不成立（κ = 0 的 Ω₁，与 `¬nodeout` 同一机制，与链形状无关） | `Tw1W.¬aboveʳ-tw1` | 编译定理 |
| 这一格的树链与主系统的底、底值、左项都无关（辅助状态的底是 `B₀`） | `zᴬ-free` | 编译定理 |
| P 非空：P < Ω₂ 时较弱形状成立（链点往后挪），P ≥ Ω₂ 时不成立；实际上下文 P′ = K ++ t 可以 ≥ Ω₂ | — | 判断 |
| 较弱形状给出结点出口 | `YiWCIface.XW.outʳ` | 编译定理 |
| 链从 0 起与从 1 起两种写法下，较弱形状等价 | `to⁰`, `from⁰` | 编译定理 |
| `ChainRel` 与 `LowSlot` 都推出较弱形状 | `chain→ʳ`, `slot→ʳ` | 编译定理 |
| 接线终点 | `ebo-endʳ`, `ebo-endʳ⁰` | 编译定理（条件） |
| 较弱形状由第 0 项加步给出；`LowSlot` 推出两者 | `bs→ʳ⁰`, `slot→base`, `slot→step` | 编译定理 |
| 在 `Inv₁` 下，第 0 项只要槽位层上逐点的 Leaf，不经 `LowSlot` | `base₁`, `base₁-tw1` | 编译定理 |
| `ChainRelʳ` 严格弱于 `ChainRel` | — | 判断（未证） |
| `StepW` 在 `Inv₀`、`Inv₁` 下量化域太宽，与 `LowSlot` 同因 | — | 判断 |

**翻译账**
- 新增的定义行没有一行来自记号；γT 只出现在两个验收文件里。
- `outʳ`、`reidx` 是由树的要求逼出的：`NodeRes` 的链一支不要求用 XTree 给的那条链，所以可以按下标重排。
- 脚手架减少一处：`YiWRZero` 的链移位（`ptᶻ`、`domPt (suc k)`）不再需要，见 `xt⁰`。
- 增加一处同类引理：`Self₁.LF` 是自身折叠保持的第二份。第一份是 `YiGTSelf.Self.LF`，对 `YiTBRow.ψ`；这一份对 `YiRBSib.ψ`。按 AGENTS 应合并成对折叠参数化的接口，本路没有做。
- 新的信息（判断）：辅助系统里链点不吸收左项，原因在 `YiBLFold.Main.Srᴮ` 取的底是 `B₀`。若在目标层取 β′，链能吸收 P′。这要改折叠定义，交作者定，可记入 IdeaLedger。

##### 2. 文件表（都在 `<仓库>/probes/OCF/Lean/`）

| 文件 | 总行 / 代码行 | 冷编退出码 | 备注 |
|---|---|---|---|
| `YiWCIface.lagda.md` | 69 / 45 | 0 | 不读记号；`importclosure.py` 退出码 0 |
| `YiWCTw1.lagda.md` | 142 / 91 | 0 | 验收（读记号） |
| `YiWCWire.lagda.md` | 227 / 152 | 0 | 验收（读记号） |

其他检查：
- 冷编日志里只有各自模块的 `Checking` 行。
- 禁用构造与本机路径检索结果为 0。
- 临时文件 WC0–WC4.agda 在 `<实验目录>/work/YiWC/`。

##### 3. 定理表（编译定理；带"条件"的是条件定理）

**YiWCIface**（`module XW 𝔾 𝔻`，内层参数为 𝒮, 𝓀, D, xt）
- `weakenA : AboveL 𝒮 𝓀 D xt → AboveLʳ`
  白话：原形状推出较弱形状。
- `reidx : ∀ {a} {s : S.St a} {K p g t κ} (c : Chain 𝒮 s p g) → RefChainʳ 𝒮 s K p g t c → NodeRes 𝒮 𝓀 s K p g t κ`
  白话：按 `RefChainʳ` 给的下标重排树的链，得到结点的结论。
- `outʳ : Below 𝒮 → AboveLʳ → At 𝒮 𝓀 D xt PartXʳ → NodeOut 𝒮 𝓀 D`
  白话：`XT.out` 的变体，链一支只要较弱形状。

**YiWCTw1**
- `Self₁.LF : ∀ {a x} → GR.R j₁ a x → GR.R j₁ (E.ψ 𝟙 (t ++ a) ∷ []) (proj₁ (F x))`
  - 模块参数：o, r, B, t, β，以及 `mb : GR.R j₁ (E.ψ 𝟙 t ∷ []) (proj₁ β)`；`F x = RB.ψ j₁ o r B j₁ self β x`。
  - 白话：第 1 层上 ψ₁ 的自身折叠保持关系。证明照搬 `YiGTSelf.Self.LF`。
- `top₁ : GR.R j₁ (E.ψ 𝟙 [] ∷ []) (proj₁ (Ωt j₁))`
  白话：Ω₁ 不高于第 1 层的 Ω 树。
- `Tw1W.chain₁ : ∀ k → GR.R j₁ (E.γT Ω₂ 𝟙 k) (zᴬ (suc k))`
  白话：参照链第 k 项不高于树链第 k+1 项。
- `Tw1W.weak-tw1 : RefChainʳ sysᴬ sA (𝟙 , []) pᴬ gᴬ Ω₂ (chᴬ sA pᴬ gᴬ tt neᴬ)`
  白话：这一格上，P 空时较弱形状成立。
- `Tw1W.¬strong-tw1 : (P : E.T) → XT.RefChain gradedᴱ domsᴱ sysᴬ sA (𝟙 , P) pᴬ gᴬ Ω₂ (chᴬ sA pᴬ gᴬ tt neᴬ) → ⊥`
  白话：同一点上原形状不成立。
- `Tw1W.¬aboveʳ-tw1 : (P : E.T) → AboveLʳ sysᴬ keepᴬ Dᴬ xtᴬ → ⊥`
  白话：全量化的较弱形状因 κ = 0 的参照不成立。
- `zᴬ-free : ∀ (B : Base (tw 1)) (β : Tr⁺ j₁) (x : Tr (tw 1)) (B′ : Base (tw 1)) (β′ : Tr⁺ j₁) (x′ : Tr (tw 1)) (k : ℕ) → Tw1W.zᴬ B β x k ≡ Tw1W.zᴬ B′ β′ x′ k`
  白话：树链与 B、β、x 无关，证明是 refl。

**YiWCWire**（`module Wireʳ Inv inv-zero inv-step inv-root`，参数同 `YiWREnd.Wire`）
- `chain→ʳ : Wi.ChainRel → ChainRelʳ`
- `slot→ʳ : Wi.LowSlot → ChainRelʳ`
- `to⁰ : ChainRelʳ → ChainRelʳ⁰`
- `from⁰ : ChainRelʳ⁰ → ChainRelʳ`
  白话：第 0 个链点是零树，参照链各项非空，所以下标 0 从不被用到（用 `R-zero`）。
- `aboveᴱʳ : ChainRelʳ → AboveLʳ sysᶻ keepᶻ Dᶻ xtᶻ`
- `aboveᴱʳ⁰ : ChainRelʳ⁰ → AboveLʳ sysᶻ keepᶻ Dᶻ xt⁰`
- `ebo-endʳ : (cr : ChainRelʳ) → ExitOn xtᶻ (λ _ _ _ _ _ _ _ _ _ → tt) (aboveᴱʳ cr) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`（条件）
- `ebo-endʳ⁰ : (cr : ChainRelʳ⁰) → ExitOn xt⁰ (λ _ _ _ _ _ _ _ _ _ → tt) (aboveᴱʳ⁰ cr) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`（条件）
  白话：树侧用 node⁺ 自己的链也接到终点。
- `bs→ʳ⁰ : BaseW → StepW → ChainRelʳ⁰`
- `slot→base : Wi.LowSlot → BaseW`
- `slot→step : Wi.LowSlot → StepW`
- `base₁ : ∀ {a} (o : Ok a) r (B : Base a) (β : Tr⁺ zero) → (∀ i u → proj₁ (O.Ωt i) ⊴ proj₁ (B i u)) → (p : Pos a) (g : Br a p → Tr a) {κ : E.T} → GR.R (at a p) (E.Ωt κ) (proj₁ (O.Ωt (at a p))) → GR.R (at a p) (E.Ωt κ) (slTᵍ a p (pt⁰ (o , r , B , β) p g 1))`
  白话：底不低于 Ω 树、且槽位层上有 Leaf 时，第 1 个链点不低于 Ω_κ。

**前提可满足**
- `Wʳ₀`：用 `Inv₀` 实例化 `Wireʳ`。
- `base₁-tw1`：塔第 1 项，底取 `B₀`。
- `Self₁` 的 `mb` 由 `top₁` 给出。
- `ebo-endʳ` 的前提（`ChainRelʳ` 与 `ExitOn`）未实填，与 `YiWREnd.ebo-end` 同档。

##### 4. 第一个障碍

**`YiWRZero` 系统上的 `StepW`。** 在状态 s、上下文 K 的结点上，要从"γT_k 不高于某个链点"推出"ψ_κ(K ++ t[γT_k]) 不高于某个链点"。链点只依赖槽位层的底与 g，不依赖 K（这一格的 `zᴬ-free` 是编译实例）。判断：下标可以往后挪，但只能吸收低于链上确界的 K；`Inv₀`、`Inv₁` 允许超出确界的 K。这是数学上的阻碍，不是工程上的。

**辅助系统。** 先挡住的是 κ = 0 的不坍缩参照（`¬aboveʳ-tw1`，与 `YiBAEbo.¬nodeout` 同一机制）。它与链形状无关，也是数学上的阻碍（属于当前量化域）。

##### 5. 偏离、事故、未读部分

**偏离。** 简报说第 0 步"不成立就停下"。辅助系统上全量化的 `AboveLʳ` 不成立（`¬aboveʳ-tw1`），但原因是已知的 κ = 0 机制，与本路要问的链对齐无关。所以我继续做了按点、只取精确参照的陈述。是否应当停下，请主审判断。

**事故。**
- WC3 第一次编译退出 42（`NotInScope xtᶻ`），加一行 `open` 后通过。
- 没有出现 251 或 124。
- 堆峰值没有测到：`/usr/bin/time` 被沙箱拦下（`sysctl kern.clockrate` 无权限）。单次编译都在一分钟左右。

**只读了部分或没有读、凭转述引用的：**
- `YiSDIface`、`YiSDRead`：只看了文首与签名。
- `YiAbsGEbo.refᴱ`、`YiGIInst`、`YiExSuff`、`H.Exᴴ` 的定义体：未读，只经由 `YiWREnd` 的用法引用。
- `YiUF*`、`YiFIGen.genᴷ`、`YiGLDom.rd-not-dom`、`YiGIEnd.Assembly`、`YiMXEnd`、`CompareTable.md`：未读。
- `YiLLLeafNeg`：只读了反例一段。
- `EBOHandbook` 4.2、4.6 与 Bedrock 性能手册：未读，因为没有遇到性能问题。

**复用与搬运。**
- `Wire.restᴱ` 是经实例化 `Wire` 复用的，没有拷贝。
- `refparts` 逐字取自 `Wire.aboveᴱ`。
- `Self₁` 照搬 `YiGTSelf.Self.LF`，已在文首写明来源。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：较弱链形状对 EBO 参照（前缀 YiWC，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另两路（`YiSO`、审查 F 路）与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者对方法的要求（原文）："更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。对照表 `probes/Survey/CompareTable.md` 之后，换基候选（`YiBSFold`，主线定义不动）在读回域里的义务压成了一条核心陈述。
- 作者选项原文："Fable 先读定义：LowSlot 会不会重蹈覆辙 (Recommended), 核心：证 LowSlot (Recommended), 较弱链形状对 EBO 参照 (Recommended)"。前缀 `YiSO`（Fable 5.2）、`YiWC`（Opus 5.5），以及审查 F 路（Fable 5.2，只在临时目录），互不导入。
- **核心陈述**：`YiWREnd.Wire.LowSlot`（状态 s 在槽位 p 上朝槽位层的折叠 `YiWRZero.slotFold` 把关系 `GR.R a η y` 变成以 ψ_κ(K ++ η) 为参照的关系，κ 来自 `GR.Nu a p κ`，不变式 `Inv s K`）。条件定理 `Wire.ebo-endˢ : LowSlot → ExitCondition → toL EBO-tree′ ≼ readRW EBOᴮ`（换基折叠上 Λ 的闭项，对一切站一次成立）。YiWR 判断：在现有不变式 `Inv₀`、`Inv₁`（`ebo-end₀`、`ebo-end₁`）下 `LowSlot` 量化域太宽；要换成记下各层底对上下文支配的不变式，那时 `inv-step` 是朝各层的保持，要一个同时覆盖回退行（`inu`、`ink`、后继与 ℕ 极限上的 `inc`、路由落在地板之下的 `back`）与换基行（路由落在地板之上）的多目标系统，上下文随目标取 ψ_κ。终点那条递归里换基行不出现（`YiWRZero.fallᶻ′`），换基行只在结点链的链步与孩子的底里。出口条件与主线同状态（`YiHCRel.Exᴴ`）。
- **主审核对过的一点**：同形的条件定理主线早有（`YiGIEnd.Assembly`、`YiMXEnd`：Leaf、Lift、全域律 LowKeep 推出终点），此后的站与格都是在拆那条律；`LowSlot` 与它同类。
- **周边已编译（主审复核过，都在 `probes/OCF/Lean/`）**：
  - 参照一侧结点前提：`YiXTIface.XT.Below`、`AboveL`、`split`、`exact`、`stuck`；`YiBAEbo.BelowE`（参照取 ψ_ν、ν 高于目标真槽位层读法时 `Below` 成立，条件 `KeepAt`；`gradedᴱ` 的上下文是对子 (ν, P)，参照 ψ_ν(P ++ a)），`main-¬below₀`（对一切目标用 ψ₀ 在非零目标上不行），`¬above`（`AboveL` 要求逐项对齐，第 0 项对不上），`YiBAWeak.RefChainʳ`、`nodeʳ`（较弱链形状对结点一行够用）。
  - 嵌入行：`YiSDIface`（`SD.Split.need`/`give`、`AtΩ.lowΩ`：顶槽位保留时 Ω 树上的保持不经主系统的生成原理）、`YiSDRead`（`sub-read`、`top-read`、`Tw.sub-readᵗ`、`Tw.cap-domᵗ`、`Tw.hand₁ᵗ` 无前提；`Tw.lowΩᵗ` 条件；一般参照的抬高 `CellRaise` 未走通）。
  - 树一侧与读回域：`YiBLIface`/`YiBLFold`（换基律）、`YiQDIface`/`YiQDFold`（`SuffD`、`SuffRD`、`KD`、`kp-good`、`AddR.chain-dom`）、`YiXTReb`（换基在读回域里无分叉出口，`lowˣ`）、`YiFIGen.genᴷ`、`YiGLDom`（`Dom`、`leafᴰ`、`liftᴰ`；`rd-not-dom`）。
  - 合成候选 `YiUF*`（带深度 d 的一族，下标侧分叉格在地板之上已覆盖）。

#### 本路的问题
`YiBAEbo.¬above` 否定了 `AboveL` 的原形状（参照链与树链逐项对齐；参照链第 0 项 Ω_κ，树链第 0 项是零树，`YiBALemma.R-zero`）。`YiBAWeak.RefChainʳ`（第 k 个参照链点只要不高于树链上的某一点 `Σ m, R (γ k) (slT (z m))`）对结点一行够用（`nodeʳ`）。YiWR 独立碰到同一点，把链改成从第 1 项起（`YiWRZero.ptᶻ`、`YiWREnd.Wire.ChainRel`）。

#### 要做的（按序）
0. 先读 `YiBAWeak`、`YiXTIface`（`AboveL`、`RefChain`）、`YiWRZero`、`YiWREnd`（`ChainRel`、`aboveᴱ`、`chain←slot`）的定义体；写出 "较弱形状在 EBO 参照上成立" 的陈述（在换基辅助系统与 `YiWRZero` 的系统上），临时文件编译类型。不成立就停下回报。
1. 证它：对 EBO 记号参照（`YiAbsGEbo.refᴱ`，`YiBAEbo.gradedᴱ` 或 `YiGIInst.gradedᵍ`，说明选哪个），在读回域上；先塔第 1 项那一格（`YiBAEbo.Tw1Keep` 的点），再一般。
2. 在新文件里写一个接线变体：把 `aboveᴱ` 换成较弱形状的版本，说明这样 `ChainRel`/`LowSlot` 的要求是否变弱（例如不再需要从第 1 项起的那一步，或第 0 项的那一条）。不改 `YiWREnd`。
3. 交：较弱形状的状态（成立 / 条件 / 否定），接线变体的陈述，翻译账。

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


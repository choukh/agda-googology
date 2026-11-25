# 接线：拼成一条对一切站的条件定理（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 05:41 至 06:09 |
| 工具调用 / agda 编译 (粗数) | 87 / 10 |
| token (usage 字段，按消息去重) | 输出 139273；新写入缓存的输入 341802；读缓存的输入 16503781；其余输入 152 |
| 写过的仓库文件 | `YiWREnd.lagda.md`, `YiWRZero.lagda.md` |
| 文件前缀 | `YiWR` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0，YiWRZero 导入闭包干净；条件定理 Wire.ebo-endˢ：朝槽位层的保持 LowSlot 与出口条件推出换基闭项 EBOᴮ 的读法不低于 EBO 参照，对一切站一次成立；朝第 0 层的树一侧与五条非结点出口实填；主审核对：同形的条件定理主线早有（YiGIEnd.Assembly、YiMXEnd），主前提 LowSlot 与主线的 LowKeep 同类，未证，执行方判断现不变式下太宽 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b79/YiWR.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-17 06:00 (UTC)：

主审补充信息（同批 YiSD 刚回来，主审已 8G 冷编两件退出 0，可以导入）：嵌入行出口要的一般形式 `SubDom` 没有证出来，也没有否定。读回形式成立：`YiSDRead.sub-read`、`top-read`，塔各项上 `Tw.sub-readᵗ`、`Tw.cap-domᵗ`、`Tw.hand₁ᵗ`（无前提）。YiSD 判断 `YiQDIface.SuffRD` 经生成原理会走到一般形式，所以现接口不能只靠读回形式。它给的出路是：在 Ω 树上不经主系统的生成原理，直接用 `YiSDIface.SD.AtΩ.lowΩ`（前提是顶槽位保留、余尾 Ω、`Nu`、分支上的 `RefBr`、辅助系统上的保持 `auxK`）、`Prefix.lowΩᵖ`，以及塔上的 `YiSDRead.Tw.lowΩᵗ`。`YiAbsGSuff.Tower.K` 只在参照 `Ωr (kt n)`、树 `Ωt (tw n)` 上用 LowKeep，这一点 YiSD 读了代码，但没有接进去。另外 `YiSDRead.gradedˢ : Graded blkᵍ foldᴮ rowsᴮ refᴱ 𝕍` 已经写了（只检验了关系、`Weak`、`Node`）；你若也写了这个实例，请在回报里说明两份的关系。你的简报与停止条件不变；这条信息仅供参考，按你的判断决定用不用。

## 回报原文

#### 1. 判决

**对纲领与目标意味着什么.** 这是换基候选 `YiBSFold` 一侧的验收文件。树、折叠、合法性一处未改，主线定义没有动。现在有一条编译过的条件定理：前提成立，则 `YiBSFold` 上 Λ 闭项 `EBOᴮ` 的读法不低于 EBO 参照树 (`toL EBO-tree′ ≼ readRW EBOᴮ`)。它对塔的每一项 n 一次成立，没有按站的引理。朝第 0 层那一侧的前提，树一侧全部实填，参照一侧的五条非结点出口与结点的余尾、基本列也实填了。剩下的前提不全在参照一侧：主要的一条 `LowSlot` 是"朝槽位层的保持"，树和参照两侧都有。所以"尽量只剩参照一侧的引理"没有做到。

**关键事实（与简报第 2 步的设想不同）.**
- 终点只在第 0 层、路径 `z≤` 上用 LowKeep。在 `YiBSFold.ψ` 里，这条路径在每个非零层号上都是 `inu`，所以递归里每一行嵌入都逐字回退到孩子（`fallᶻ′` 是 `refl`，对一切层号成立）。
- 换基一行（`route` 给 `inj₂`）在这条递归里不出现，只出现在两处：结点链的链步（朝槽位层的折叠）和孩子的底（经 `inc c u` 的折叠）。
- 所以 `YiXTReb.lowˣ`、`YiQDFold.WithRules.lowᴰ`（换基根状态上的保持）不能直接交给终点。我改为新建朝第 0 层的回退系统，换基行留在前提 `LowSlot` 和 `inv-step` 里。

**各步进度.**
- 第 0 步完成：`gradedᴮ : Graded blkᵍ foldᴮ rowsᴮ refᴱ 𝕍` 编译通过，目标类型已写出。
- 第 1 步部分完成：读回域 `Dom` 用在龙骨读法上（`dom-keel` 配 `Leaf = dom-top`）。朝第 0 层的系统取树的域为全体，用不到 `KD`。`KD` 只在用换基根系统去证 `LowSlot` 时才会用到，那一步没有做。
- 第 2 步完成：拼成了条件定理，但走的不是简报设想的路线（见上）。
- 第 3、4 步：见下文。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 终点递归里每一行嵌入都是孩子回退 | `YiWRZero.fallᶻ′` | 编译定理 |
| 朝第 0 层的树一侧全部实填（保留律空真，`Below` 空真，结点一律走链） | `YiWRZero` | 编译定理 |
| 五条非结点出口在 EBO 记号上实填 | `YiWREnd.Wire.restᴱ` | 编译定理 |
| `ChainRel` 由 `LowSlot` 推出 | `Wire.chain←slot` | 编译定理 |
| 链若从第 0 个链点（零树）起，k = 0 时要零树不低于 Ω_κ，不能成立；所以链取第 1 个起 | `YiWRZero.ptᶻ` | 判断 |
| 在 `Inv₀`、`Inv₁` 下 `LowSlot` 的量化域太宽：上下文 K 只受第 0 层约束，而取 y = 0 时 `LowSlot` 要求槽位层的底不低于 ψ_κ(K) | `YiWREnd` 文首 | 判断（没有编译否定） |
| 出口条件 `ExitCondition` 是否成立 | `Wire.ExitCondition` | 未证（与主线 `YiGIEnd` 同状态） |
| `gradedᴮ` 的 `app` 恒为 ψ₀，所以打包好的 `lowˣ` 不能直接用于槽位层的 ψ_κ 上下文；可绕开（直接用 `keepAllᴰ`，上下文取 ψ_κ(K ++ ·)） | — | 判断（工程） |

#### 2. 文件表

| 文件 | 总行 / 代码行 | 冷编退出码 | 说明 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiWRZero.lagda.md` | 166 / 98 | 0（日志只有本模块的 `Checking`） | 不读记号；`importclosure.py` 结果 OK（禁用表命中 0） |
| `<仓库>/probes/OCF/Lean/YiWREnd.lagda.md` | 289 / 194 | 0（日志只有本模块的 `Checking`） | 验收文件，读记号 |
| `<实验目录>/work/YiWR/YiWRStep0.agda` | 临时 | 0 | 第 0 步检查 |

两个仓库文件里禁用构造与本机路径的检索结果都是 0。

#### 3. 定理表（全部为编译定理）

**`YiWRZero`（不读记号）**
- `fallᶻ′ : ∀ {a} (s : Stᶻ a) (c : CH a) (x : Tr a) (y : ChTᵍ a c) → proj₁ (Φᶻ (stepᶻ s c x) (chTᵍ a c y)) ⊴ᵗ proj₁ (Φᶻ s (upᵍ x c y))`
  白话：朝第 0 层时，嵌入的像就是孩子材料在孩子状态下的像。
- `Zero.WithRules.lowᶻ : OutDN sysᶻ Le fallᶻ → AboveL sysᶻ keepᶻ Dᶻ xtᶻ → ∀ {ℓ} (s : Stᶻ ℓ) (K : Cxtᶻ) → Bdᶻ s K → ∀ {a x} → Rᵍ ℓ a x → Rᵍ zero (apᶻ K a) (proj₁ (Φᶻ s x))`
  白话：五条非结点出口加 `AboveL`，给出任何状态、一切树上朝第 0 层的保持。
- `ModelZ.modelZ-low`
  白话：平凡模型里 `lowᶻ` 的全部前提成立。

**`YiWREnd`（读记号）**
- `leafᴮ : Leaf`（即 `dom-top`）；`genᴮ : ∀ ℓ → Gen⁺ _≤ᵀ_ ℓ`；`zeroᴮ`、`succᴮ`、`limᴮ`、`weakᴮ`、`nodeᴮ`、`embᴮ`、`leRᴮ`
  白话：主线关系在 `foldᴮ` 的实例上满足生成原理与各条规则。
- `upperᴮ : ∀ n → K.readRW (twcᴮ n) ≼ K.readRW EBOᴮ`
  白话：塔第 n 项的闭项是 `EBOᴮ` 的第 n 项（只用定义展开）。
- `Wire.restᴱ : OutDN sysᶻ _≤ᵀ_ fallᶻ`
  白话：五条非结点出口在 EBO 记号上成立（给定 `inv-zero`、`inv-step`）。
- `Wire.aboveᴱ : ChainRel → AboveL sysᶻ keepᶻ Dᶻ xtᶻ`
  白话：结点出口里余尾与基本列的部分已实填，只剩链上的关系。
- `Wire.chain←slot : LowSlot → ChainRel`
- `Wire.ebo-end`（在 `module _ (cr : ChainRel)` 里）`: ExitCondition → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`
- `Wire.ebo-endˢ : (ls : LowSlot) → ExitCondition (chain←slot ls) → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`
- `ebo-end₀ : (cr : W₀.ChainRel) → W₀.ExitCondition cr → toL ET.EBO-tree′ ≼ K.readRW EBOᴮ`；`ebo-end₁` 同形（不变式取 `Inv₁`）
- `chain₀→₁ : W₀.ChainRel → W₁.ChainRel`
  白话：`Inv₁` 下的前提比 `Inv₀` 下的弱。

**前提清单**

| 前提 | 状态 |
|---|---|
| `Leaf` | 已实填（`dom-top`） |
| `Lift` | 没用到：龙骨读法直接取 `dom-keel`，因为 `Dom` 上没有 `Keel⁻.tw-step` |
| 朝第 0 层的树一侧（`KeepLaw`、`FallLaw`、`Monoˢ`、`XTree`、`Below`、`At PartX`） | 已实填 |
| 五条非结点出口 `zeroE`、`succE`、`limE`、`upE`、`leE` | 已实填 |
| 七条生成规则 | 已实填 |
| `AboveL` 的余尾与基本列部分 | 已实填 |
| `AboveL` 的关系部分 | 化成 `ChainRel`，再化成 `LowSlot`，留作前提（树一侧与参照一侧混合，即朝各槽位层的保持；换基行在这里） |
| 不变式 `Inv` | `Inv₀`、`Inv₁` 的三条（`inv-zero`、`inv-step`、`inv-root`）都实填；更强的 `Inv`（各层的底不低于 ψ_κ(K)）没有写，它的 `inv-step` 是朝各层的保持，留作前提（接线） |
| `ExitCondition` | 留作前提（接线，同 `YiGIEnd.Assembly`） |
| `Below`（主系统）、`Hand₁`、`SubDom`、`OutRDN` | 这条定理里不出现；它们属于换基根系统，只在用换基根系统去证 `LowSlot` 时才会出现 |

可满足性：抽象的 `lowᶻ` 有平凡模型（`ModelZ`）。在 EBO 记号上，`inv-root` 已证；`LowSlot`、`ExitCondition` 没有给出实例。

**对一切站的含义（第 4 步）.** 定理对一切 n 一次成立，前提对一切层号、状态、结点陈述，不用任何按站或按塔项数的引理。它没有说：
- `LowSlot` 或 `ExitCondition` 成立；
- 换基折叠与主线之间的任何比较（`EBOᴮ` 与 `EBOᶻ` 之间没有定理）；
- 任何一站的值；
- 换基可以进主线（它仍是候选）。

#### 4. 第一个障碍

`Wire.LowSlot`（`Inv₀`、`Inv₁` 下判断为太宽）。要能成立，必须换成记下"各层的底不低于 ψ_κ(K)"的 `Inv`。那样 `inv-step` 就成了：任意的树 x 经 `inc c u` 朝任意层 i 折叠时保持关系。这需要一个"多目标系统"：同时覆盖回退行（`inu`、`ink`、sS 与 sL 上的 `inc`、`route` 给 `inj₁` 的 `back`）和换基行（`route` 给 `inj₂`），上下文随目标取 ψ_κ。

- 这个系统现在不存在，挡在这里的首先是工程（接线）。现有的充分性只对换基根状态（`YiQDFold`、`YiXTReb`；YiSD 的 `lowΩ` 只对 Ω 树）。
- 其后还有数学上未决的两项：
  - 换基行出口的一般形式：YiSD 回报 `SubDom` 一般形式未证。
  - k = 0 那一步要 Ω_κ 不高于槽位层的 Ω 树，而 κ 来自 `GR.Nu`，即 `GR.Rd` 上的读法。`Leaf` 在 `GR.Rd` 上一般不成立（`YiGLDom.rd-not-dom`），所以这一步要求 `Nu` 的读法落在 `Dom` 里。这一点是判断，没有编译否定。

#### 5. 偏离与事故；只凭转述引用的东西

**偏离.**
- 简报第 2 步要把 `lowˣ`/`lowᴰ` 交给终点。我没有这样做（理由见第 1 节），改为新建朝第 0 层的系统。
- 没有经 `Laws.LowKeep` 与 `YiAbsGSuff.endpoint`，塔与终点照 `YiGIEnd.Assembly` 写（同 `YiExSuff.TowerE`），龙骨读法用 `dom-keel`。
- `gradedᴮ` 的 `Bd` 只取第 0 层底条件，这一项不进最后的定理。

**与 YiSD 的关系.** 我的 `gradedᴮ` 与 `YiSDRead.gradedˢ` 的 R、Nu、v、cl、Cx、app 相同；`Rd` 不同（我取 `Dom`，以便 `Leaf` 成立），`Bd` 与 `Doms.Wl` 也不同。两份互不导入。YiSD 的 `lowΩ` 在换基根状态的 Ω 树上；它在这条定理里只能间接用到（证 `LowSlot` 或 `inv-step` 时），我没有接。

**事故.**
- 三次编译退出 42，都已修好：一个错名；`inv₀-step` 不展开；`chain₀→₁` 卡在模块参数上（把链点提到顶层 `ptᶻ` 解决）。
- 没有退出 251 的情况，各次编译约一分钟以内，堆上限 6G。但峰值内存没有测到：沙箱拦了 `/usr/bin/time -l`（sysctl 不允许），所以"峰值超过 4G 先改形状"这条无法核对。

**没有读或只读了一部分的.**
- 未读：`EBOHandbook` §4.2、§4.6 与 Bedrock 性能手册（没有遇到性能问题）、`YiXTKp`、`YiUFDom`。
- 只读一部分：`YiXTCur` 只读了 `refA`；`YiSDIface`、`YiSDRead` 只读了文首与 `gradedˢ`、`Bdˢ`；`YiKVRel.lower⁰` 只读签名，最终没用（第 0 层出口用 `exitᵍ`，即 `H.exitᴴ`）；`YiHCRel`、`YiMENote`、`YiMWPre`、`EboLeanDef`、`EBO` 只检索了用到的签名；`CompareTable` 只读了 §6 到 §10；`probes/README.md` 只读了首段。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：接线，拼成一条对一切站的条件定理（前缀 YiWR，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另两路（`YiBA`、`YiSD`）与你互不导入；它们证的参照引理在你这里是前提。

#### 作者的决定与背景（2026-11-17）
- 作者对方法的要求（原文）："更加结构化地高屋建瓴地分析，而不是盲目地一站一站深入"。对照表 `probes/Survey/CompareTable.md` 与第七十八批之后，换基在读回域里要做的事已列成一张有限的、不按站分的清单（"已经穷尽" 是主审的判断）。
- 作者选项原文："接线：拼成一条对一切站的条件定理 (Recommended), 参照一侧：Below 与 AboveL (Recommended), 参照一侧：替身支配原材料 (Recommended)"。前缀 `YiWR`（Opus 5.5）、`YiBA`（Opus 5.5）、`YiSD`（Fable 5.2），互不导入。**主线定义不动**；换基折叠是候选。
- **已编译（主审复核过，都在 `probes/OCF/Lean/`）**：
  - 终点充分性 `YiAbsGSuff`（`Leaf`、`Lift`、`LowKeep`、`Base` ⇒ 塔每一项与终点 `endpoint`）；EBO 记号参照的实例 `YiAbsGEbo`（`refᴱ`、`ebo-end`）；主线的分级结构 `YiGIInst.gradedᵍ`。读回域上 `YiGLDom.leafᴰ`、`liftᴰ`、`dom-top`（`Dom`：层号与读法的域，验收文件）；`YiKVRel.lower⁰`（第 0 层 `Base`）。
  - 换基折叠 `YiBSFold`；律与充分性 `YiBLIface`（`RebAt`、`SuffR`）、`YiBLFold`（`lowᴮ`）；按读回域 `YiQDIface`（`SuffD`、`SuffRD.sys→lowᴰ`、`OutD`、`OutRD`、`NodeTree`/`NodeRef`）、`YiQDFold`（树的域 `KD`，`kd-dw`、`Ωt-in`/`Ωt-out`、`kp-good`、`AddR.chain-dom`、`ntᴮ`、`ntᴬ`、`SubstDom.embEᴮ : Hand₁ → SubDom → …`、`raise→SubDom`、`WithRules.lowᴰ`、`QDTw1.low-tw1`；YiQD 回报：缺 `Graded blkᵍ foldᴮ rowsᴮ` 的实例，可照 `gradedᵍ` 的 `Bdᵍ` 写）、`YiQDNeg.Min.no-chain₁`。
  - 出口分解 `YiXTIface`（`XT.Below`、`AboveL`、`split`、`need`、`exact`、`out`、`stuck`）、`YiXTKp`（`apart`：两条前提作用点不相交）、`YiXTReb`（`nodeᴮ : Below sysᴮ → NodeOut …`、`nodeᴬ`、`lowˣ`：换基上的 LowKeep 只要非结点各条出口 `OutRDN`/`OutDN` 加 `Below`×2 与 `AboveL`）、`YiXTCur`（现行折叠对角点 `diag-stuck`）。主线关系上的生成与几条律：`YiFIGen`（`genᴷ`、`weakᴷ`、`limᴷ`、`nodeᴷ`）。
  - 合成候选 `YiUF*`（带深度 d 的一族；`YiUFDom.QDTw.Ωt-tw`：塔各项 Ω 树在 `KD` 里）。替身值 `YiSV*`、`YiZS*`（`StepS` 在 ω+n+1 成立，ω·2+1 起未走通）。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；现行折叠上同步对象那一格已关闭（V287）。

#### 本路的问题
得到一条条件定理："参照一侧的那几条引理成立 ⇒ 换基折叠的 EBO 闭项（`YiBSFold` 上的 Λ 闭项）的读法不低于 EBO 的参照"，对一切站一次成立；前提逐条列出，并尽量只剩参照一侧的引理。

#### 要做的（按序）
0. **最小检查**：写出 `Graded blkᵍ foldᴮ rowsᴮ refᴱ 𝕍` 的实例（照 `YiGIInst.gradedᵍ`），在临时文件里编译。写出目标陈述的类型（经 `YiAbsGEbo.ebo-end` 或 `YiAbsGSuff.endpoint`）。不成立就停下回报。
1. **两个域接起来**：`YiGLDom.Dom`（层号与读法）与 `YiQDFold` 的 `KD`（树）。证明充分性里用到的树都在 `KD` 里、用到的读法都在 `Dom` 里（例如塔各项与 Λ 的 Ω 树、链点；`YiUFDom.QDTw.Ωt-tw` 一类可参考），或写清哪里接不上。
2. **拼**：`Leaf`（`leafᴰ`）、`Lift`（`liftᴰ`）、`Base`（`lower⁰`）、换基上的 LowKeep（`YiXTReb.lowˣ` / `YiQDFold.WithRules.lowᴰ`）交给终点充分性，得到条件定理。验收部分（读记号）放验收文件。
3. **前提清单**：逐条列出剩下的前提（`Below`、`AboveL`、`Hand₁`、`SubDom`、`OutRDN`/`OutDN` 的非结点各条、关系的律等），每条标：已实填 / 留作前提（参照一侧）/ 留作前提（树一侧或接线）；能实填的就实填（例如 `zeroE`、`succE`、`limE` 一类若可由已有定理给出）。给前提可满足的说明。
4. 说明这条定理对一切站成立的含义，以及它没有说什么（例如换基折叠不是主线，与主线没有比较定理）。

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


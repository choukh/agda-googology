# 参照一侧：Below 与 AboveL（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 05:41 至 06:31 |
| 工具调用 / agda 编译 (粗数) | 80 / 19 |
| token (usage 字段，按消息去重) | 输出 227936；新写入缓存的输入 437238；读缓存的输入 21039467；其余输入 146 |
| 写过的仓库文件 | `YiBAEbo.lagda.md`, `YiBALemma.lagda.md`, `YiBAModel.lagda.md`, `YiBAWeak.lagda.md` |
| 文件前缀 | `YiBA` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0，两件不读记号的导入闭包干净；非平凡模型里两条同时成立（YiBAModel）；Below 在参照下标随目标层号走（ψ_ν）时条件成立（BelowE），主线 ψ₀ 参照下不成立（main-¬below₀；主审核过主线读回域只到第 0 层，不受影响）；AboveL 原形状在读回域里被否定（¬above、¬above-tw1：参照链第 0 项 Ω_κ 对树链第 0 项零树），较弱形状对结点一行够用（YiBAWeak.nodeʳ），对 EBO 未查 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b79/YiBA.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### 回报 YiBA：参照一侧的两条前提 Below 与 AboveL

#### 1. 判决

**对纲领与目标意味着什么**
- 纲领：树、折叠、合法性一行没改。读记号的内容只放在验收文件 `YiBAEbo`、`YiBALemma` 里。`YiBAModel` 与 `YiBAWeak` 不读记号，导入闭包检查干净（`importclosure.py`：禁用表命中 0，--only 之外 0，OK）。
- 目标（让树自足）：
  - `Below` 能由 EBO 参照满足，条件是参照的坍缩下标随目标层号走（ψ_ν，ν 读出目标）。主线 `gradedᵍ`/`gradedᴷ` 的写法对一切目标都用 ψ₀，在换基行（目标 j ≠ 0）上不行。
  - `AboveL` 按现在的写法要求参照链与树自己的链逐项对齐。参照链第 0 项是 Ω_κ，树的链从零树起，所以对不上。这是基本列层面的要求，相当于 Lab 档。去掉逐项对齐后的形状只要求每个参照链点不高于树链上的某一点，这属于序数值层面（判断）。

**各步进度**
- 第 0 步完成。
- 第 1 步：`Below` 条件成立。
- 第 2 步：`AboveL` 是编译否定，反例在读回域里；另给出一个较弱形式，并证明它对结点一行仍够用。
- 第 3 步：两条前提的状态与用到的参照一侧引理见下文。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 余尾不相交的模型里 Below 与 AboveL 同时成立，两个结点出口成立 | `YiBAModel` | 编译定理 |
| 主线 ψ₀ 参照下，主系统的 `Below` 与 `NodeRef` 不成立（塔第 1 项，标准根） | `YiBAEbo.Tw1Main` | 编译定理（否定） |
| 按层号的参照 ψ_ν：在 `KeepAt` 之下，`XReb` 的一切实例上两个系统的 `Below` 都成立，主系统结点出口也成立 | `YiBAEbo.BelowE` | 编译定理（条件） |
| `KeepAt` 在塔第 1 项（目标 `h₁ 1`，ν = 1）上成立 | `keep-tw1`、`Tw1Keep` | 编译定理 |
| 对一切 ψ_ν(P+·) 形状的上下文，`AboveL` 在替身的顶结点上不成立 | `¬above`、`¬above-tw1` | 编译定理（否定） |
| 参照 Ω_1（κ=0）、ν ≥ 1 时，辅助系统的结点出口本身不成立 | `¬nodeout`、`¬node-tw1ᴬ` | 编译定理；读作谓词太宽（判断） |
| 链一支去掉逐项对齐后，对结点一行仍够用 | `YiBAWeak.nodeʳ` | 编译定理 |
| 较弱形式 `RefChainʳ` 在 EBO 参照上是否成立 | — | 未检查 |
| Ω_2 是槽位层（第 1 层）的精确参照 | — | 判断 |
| 实际运行中 `SubDom` 能否只送精确参照，从而避开 Ω_1 那一类点 | — | 判断，未检查 |

**两条前提的状态**
- `Below`：条件成立。
  - 条件 `KeepAt j ν`：目标每个真槽位层读出的 μ 都满足 μ+1 ≤ ν。它只看层号的读法和记号的字面比较，不判定树。
  - 主线 ψ₀ 下被否定。
- `AboveL`：被否定。
  - 反例是塔第 1 项换基行在孩子 1 上的替身，即 `subᴮ 1 x`，换基层号的 Ω 树（`sub-is` 由 refl 给出）。用的参照是槽位层的精确读法 Ω_2。

**用到的参照一侧引理**
- `YiGIRel`：`R`、`Rd`、`Nu`、`c0`、`ca`
- `YiHCRel`：`Mᴴ` 的各构造子
- `YiGLDom`：`dC`、`dz`、`dom-top`
- `YiNLCtx`：`prefix`
- `YiAbsGEbo`：`refᴱ`
- `YiFIGen`：`Ind`、`→low`、`low→`
- `YiKVRel`：`¬◃z`、`readRW`、`⊴`
- `EboLeanDef`：`cof`、`fsT`、`fsn`、`γT`、`cmpᵀ`
- 新写在 `YiBALemma`：`keepψ`、`collψ`、`R-zero`、`rd0`、`nu→rd`、`rd→nu`、`fsn1`、`cons≢c0`

#### 2. 文件表

全部在 `<仓库>/probes/OCF/Lean/` 下。每个文件都删掉自己的接口后冷编，日志里只有本模块的 Checking 行。

| 文件 | 代码行 / 总行 | 冷编退出码 | 时间 / 最大驻留 |
|---|---|---|---|
| `YiBAModel.lagda.md` | 110 / 168 | 0 | 3 秒 / 0.22G |
| `YiBALemma.lagda.md` | 155 / 225 | 0 | 12 秒 / 0.98G |
| `YiBAEbo.lagda.md` | 235 / 360 | 0 | 17 秒 / 1.54G |
| `YiBAWeak.lagda.md` | 30 / 44 | 0 | 1 秒 / 0.17G |

禁用构造（postulate、洞、TERMINATING、POSITIVITY、trustMe）与本机路径的检索均为 0。

#### 3. 定理表

**`YiBAModel`**（编译定理，不读记号）
- `dωᴹ : ∀ {u κ} → Cωᴹ u → CΩᴹ u κ → ⊥`：模型里余尾 ω 与余尾 Ω 不相交，由 `no-cyc` 给出。
- `belowᴮᴹ : Below sysᴮ`、`belowᴬᴹ : Below sysᴬ`、`aboveᴬᴹ : AboveL sysᴬ keepᴬ Dᴬ xtᴬ`：对 `XReb` 的一切实例，两条前提都成立。
- `nodeᴮᴹ : NodeOut sysᴮ keepᴮ Dᴮ`、`nodeᴬᴹ : NodeOut sysᴬ keepᴬ Dᴬ`：两个结点出口成立。
- `tw1-below : CΩᴹ (col (h₁ (suc zero)) (om (lv zero))) (lv zero)`：塔第 1 项上 Below 的前提有实例，结果的余尾是 Ω。
- `tw1-above : Cωᴹ (col (h₁ (suc zero)) (om (lv (h₁ (suc zero)))))`：塔第 1 项上 AboveL 的前提有实例，结果的余尾是 ω。

**`YiBALemma`**（编译定理，读记号）
- `keepψ : ∀ ν P t {κ} → E.cof t ≡ E.cΩ κ → NotGt (E.cmpᵀ (E.sucT κ) ν) → (E.cof (E.ψ ν (P ++ t) ∷ []) ≡ E.cΩ κ) × (∀ η → E.fsT (E.ψ ν (P ++ t) ∷ []) η ≡ E.ψ ν (P ++ E.fsT t η) ∷ [])`：κ+1 ≤ ν 时，ψ_ν(P+t) 保持余尾，并与代入交换。
- `collψ : ∀ ν P t {κ} → E.cof t ≡ E.cΩ κ → E.cmpᵀ (E.sucT κ) ν ≡ E.gt → (E.cof (E.ψ ν (P ++ t) ∷ []) ≡ E.cω) × (∀ n → E.fsn (E.ψ ν (P ++ t) ∷ []) n ≡ E.ψ ν (P ++ E.fsT t (E.γT (P ++ t) κ n)) ∷ [])`：κ+1 > ν 时坍缩成余尾 ω，第 n 项沿 γ 链走。
- `R-zero : ∀ ℓ {τ} → GR.R ℓ τ zero → τ ≡ []`：与零树有关系的参照项只有 0。
- `rd0 : ∀ {μ} → GR.Rd zero μ → μ ≡ []`：第 0 层只读出 0。

**`YiBAEbo`**（读记号）
- `BelowE.belowᴱᴮ : Below sysᴮ`、`BelowE.belowᴱᴬ : Below sysᴬ`、`BelowE.nodeᴱᴮ : NodeOut sysᴮ keepᴮ Dᴮ`。编译定理，条件写在上下文的条件 `KeepAt j (proj₁ K)` 里。白话：参照取 ψ_ν、ν 高于目标真槽位层的读法时，Below 成立。
- `keep-tw1 : KeepAt (h₁ (suc zero)) (E.𝟏 ∷ [])`：编译定理。塔第 1 项上 ν = 1 满足条件。
- `¬below : (β : Tr⁺ j₁) (K : Cxtᴮ) → Bdᴮ (Mn.rt β) K → (ν P : E.T) → (∀ a → apᴮ K a ≡ E.ψ ν (P ++ a) ∷ []) → E.cmpᵀ (E.𝟏 ∷ []) ν ≡ E.gt → Below sysᴮ → ⊥`：编译否定。ν 不够大（1 > ν）时，主系统的 Below 不成立。
- `¬noderef`：前提与 `¬below` 相同，结论是 `NodeRef sysᴮ keepᴮ Dᴮ ntᴮ → ⊥`。编译否定。白话：同样条件下，`KD` 里 Ω 树 `Ωt (tw 1)` 的保留顶槽位上 NodeRef 不成立。
- `Tw1Main.root-ok : BdM (Mn.rt (Ωt j₁)) ([] , [])`：标准根满足根条件。
- `Tw1Main.main-¬below₀ : Below sysᴮ → ⊥`、`main-¬noderef₀ : NodeRef sysᴮ keepᴮ Dᴮ ntᴮ → ⊥`：编译否定，无前提。白话：主线 ψ₀ 参照下两者都不成立。
- `¬above : (K : Cxtᴬ) → Bdᴬ sA K → (ν P : E.T) → (∀ a → apᴬ K a ≡ E.ψ ν (P ++ a) ∷ []) → (t κ : E.T) → E.cof t ≡ E.cΩ κ → (∀ η → E.fsT t η ≡ η) → GR.Rd j₁ κ → AboveL sysᴬ keepᴬ Dᴬ xtᴬ → ⊥`：编译否定，对 `WithR` 的一切参数成立。白话：任意 ν，替身顶结点上 AboveL 不成立。
- `Tw1Keep.below-tw1ᴮ : Below sysᴮ`、`node-tw1ᴮ : NodeOut sysᴮ keepᴮ Dᴮ`：编译定理。
- `Tw1Keep.¬above-tw1 : (P : E.T) → AboveL sysᴬ keepᴬ Dᴬ xtᴬ → ⊥`：编译否定，参照用 Ω_2，`WithR` 填 `gradedᴱ` 的各条律。
- `¬nodeout`：前提同 `¬above`，再加 `NotGt (E.cmpᵀ (E.sucT κ) ν)`，结论是 `NodeOut sysᴬ keepᴬ Dᴬ → ⊥`。白话：参照不坍缩时，辅助系统的结点出口本身不成立。
- `Tw1Keep.¬node-tw1ᴬ : (P : E.T) → NodeOut sysᴬ keepᴬ Dᴬ → ⊥`：编译否定，参照用 Ω_1。我读作谓词太宽（判断）。
- `hand-form`：`Hand₁` 的上下文交接把根上下文的 ν 原样交给辅助系统，前缀接上 t。编译定理。

**`YiBAWeak`**（编译定理，不读记号）
- `weaken : … → XT.RefChain 𝔾 𝔻 𝒮 s K p g t c → RefChainʳ s K p g t c`：原形状推出较弱形状。
- `nodeʳ : Lim → ∀ {a} (s : S.St a) K (p : Sl a) {t} (g : SlT a p → Tr a) (c : Chain 𝒮 s p g) → RefChainʳ s K p g t c → (∀ η x → R (slL a p) η (slT a p x) → S.Q s K (fsT t η) (g x)) → S.Q s K t (nd p g)`：较弱形状对结点一行仍够用。
- `RefChainʳ` 的第 k 项只要求 `Σ m, R (γ k) (slT (z m))`。

#### 4. 第一个障碍（数学上挡住，不是工程问题）

挡住的是 `AboveL` 的链一支：`∀ k → R (slL a p) (γ k) (slT a p (z k))`。
- 参照一侧：`fsn` 的等式加上 `ψ∷-canc` 把 γ 固定成 `E.γT (P ++ t) κ`。按 `EBO.γT` 的定义，第 0 项是 `Ωt κ`。
- 树一侧：链 z 是 `YiXTKp.chainK` 给出的 `iter S′ x₀`，第 0 项是 `fromBr … zero`，即零树。
- `R-zero` 说只有参照项 0 与零树有关系，所以 k = 0 处矛盾。

这是接口形状与记号基本列之间的不一致。另一类点，即参照不坍缩的点（Ω_1，κ 低于槽位层的读法），落在参照一侧量化过宽的地方，不作为路线否定。

#### 5. 偏离与事故；没有读、只凭转述引用的东西

**事故：编译撞堆墙**
- `YiBAEbo` 第一次整篇编译退出 251（6G 堆耗尽），没有原样重跑。
- 在临时目录二分：截到 A 到 D 四个位置都是 0，用时 17 到 18 秒，最大驻留 1.38G 到 1.58G。只加上 `¬nodeout` 的截段是 251，63 秒。
- 原因是在 `NodeOut` 的应用上用了 `with`（Bedrock 手册 E-2）。改成通用的 `refute` 辅助函数后，同一 6G 上限下 17 秒、1.57G 通过；全文 18 秒、1.4G 通过。

**偏离与自己的设计**
- 新写了换基折叠上的分级结构 `gradedᴱ`：上下文是对子 (ν, P)，参照是 ψ_ν(P ++ a)。这是验收一侧的设计，ν 取空就回到主线。`Bd` 与 `Doms` 没有被用到。
- `KeepAt` 是我定的上下文条件。
- 模型的关系取 ⊤，非平凡只体现在余尾与 `Nu` 上。
- 生成规则从 `YiFIGen` 照搬，文首已注明来源。

**没有读、或只读了一部分的东西**
- 没有读：`CompareTable.md`、`YiAbsGSuff`、`YiKVRel.lower⁰`、`YiQDNeg`、`YiUF*`、`YiSV*`、`YiZS*`、`YiFYRef`、V287。
- `YiRBSib.ψ`、`YiBSFold.ψ`、`Up` 的函数体没有读，只经 `Pack`/`QDPack` 使用。
- `kp` 只查了 `kp⁼` 的几个子句。
- Bedrock 手册只读了 E-2 和 H-6，其余规则经 EBOHandbook 4.6 节的转述。

**临时文件**：二分用的截段与日志在 `<实验目录>/work/YiBA/`。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：参照一侧的两条前提 Below 与 AboveL（前缀 YiBA，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另两路（`YiWR`、`YiSD`）与你互不导入。

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
`YiXTIface` 的两条参照前提（先读定义体）：
- `Below`：目标有一个与槽位同层的真槽位时，参照保留 Ω 余尾（`RefKeepAt`）。
- `AboveL`：无证据且目标到槽位层号有字面路径时，参照沿树的链走（`RefChain`）。
两者作用点不相交（`YiXTKp.apart`）。YiXT 只在平凡模型（关系取 ⊤）里实填了它们；二值模型里只有 `Below`。问：对 EBO 记号参照（`YiAbsGEbo.refᴱ` 与主线的分级结构，例如 `YiGIInst.gradedᵍ` / `YiFIGen.gradedᴷ`，以及换基折叠的系统 `YiBLFold`/`YiQDFold`），在读回域上它们成立吗。

#### 要做的（按序）
0. **非平凡模型**：先在一个带余尾不相交的非平凡模型里让两条同时成立（编译），说明前提可满足。
1. **对 EBO 记号参照**：在验收文件里，对换基折叠的主系统与辅助系统、读回域上，证 `Below` 与 `AboveL`（先 `Below`）。复用 `YiAbsGEbo`、`YiGIRel`、`YiHCRel` 一类已有的参照一侧引理。注意：参照要能 "按目标有没有同层真槽位" 取值，这一点只按字面层号，不判定树（YiXT 判断这是验收文件的工作）。
2. 若某条不成立：写成编译否定（反例落在读回域里才算对这条路线的否定；不在域里的读作 "谓词太宽"），并说明最弱的可用形式。
3. 交：两条前提的状态（成立 / 条件成立 / 否定），用到的参照一侧引理。

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


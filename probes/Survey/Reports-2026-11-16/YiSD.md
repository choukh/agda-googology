# 参照一侧：替身支配原材料（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 05:41 至 05:58 |
| 工具调用 / agda 编译 (粗数) | 29 / 5 |
| token (usage 字段，按消息去重) | 输出 98145；新写入缓存的输入 272891；读缓存的输入 3749845；其余输入 46 |
| 写过的仓库文件 | `YiSDIface.lagda.md`, `YiSDRead.lagda.md` |
| 文件前缀 | `YiSD` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0，YiSDIface 导入闭包干净；嵌入出口在域里恰是两棵 Ω 树之间的形式（need、give）；读回形式对一切层号成立（sub-read、top-read，无前提），可疑一格 c = ω、d = 1 上成立（cell-read、cell-cap）；一般参照的抬高（SubDom）未走通无否定；Ω 树上不需要一般形式（lowΩ、lowΩᵗ，条件定理） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b79/YiSD.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiSD 回报（Fable 5.2，参照一侧：替身支配原材料，嵌入行出口）

#### 1. 判决

**对纲领与目标意味着什么。** 纲领四条都没有碰：树、折叠、合法性一行没改，只新建两个文件，没有公理。`YiSDIface` 不读记号（导入闭包检查：禁用表命中 0）；`YiSDRead` 是验收文件。对 "不按站分" 的要求：嵌入出口在读回域里要的那条参照引理，对一切层号 k、j 与一切孩子 c 一次成立（`sub-read`），不是逐站做的。它是记号一侧已有引理 `YiNLRaise.raiseR` 取前缀上下文的实例，没有新的数学。

结论分三条：

- **读回形式成立（编译定理，无前提）。** 孩子 c 的每个读法 η（`R k η c`）给出替身层号 `j ⊕ ↑ k c` 的 Ω 树的参照 Ω_η；j 有域内读法 t 时给出 Ω_{t++η}。这一条不用 "地板 ≤ j"，也不看 c 的形状。所以 "层号值相同而结构不同" 的那一格（c = ω、d = 1）在读回形式下成立。
- **一般参照上的 `SubDom` 未走通，也没有否定。** 现接口的 `EmbOutD` 第二分量对任意孩子参照 s 量化；这一形式在可疑的一格上既没证出也没否定。
- **Ω 树上不需要一般形式（编译定理，条件见第 4 节）。** `Ωt ℓ` 只有顶结点和每个分支上一个嵌入，顶槽位保留时，换基折叠在它上面的保持可以不经主系统的生成原理直接证（`lowΩ`）：分支上只用读回形式，`Hand₁` 只在 x = zero 处用到。

**各步到哪。**
- 第 0 步完成：临时文件 `YiSD0.agda` 22 分钟内写出，编译退出 0。可疑一格上读回形式成立；一般参照的陈述 `CellRaise` 写成了类型，未判定。
- 第 1 步完成：`YiSDIface` 的 `Split`（`need`/`give`，`same`/`cap`/`stuck`）。
- 第 2 步部分完成：`Hand₁` 对前缀上下文成立（`hand₁`，只用 ⊕ 的结合律）；`SubDom` 只证了最弱可用形式（带盖的 `CapDom`、读回的 `SubRead`），一般形式未走通，没有编译否定。
- 第 3 步：见第 4、5 节。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 可疑一格（c = ω、d = 1）上读回形式是否成立 | `YiSDRead.Cell.cell-read`、`cell-cap` | 编译定理，成立 |
| 同一格上一般参照的抬高（`raise→SubDom` 的前提） | `YiSDRead.CellRaise`（只有陈述） | 未走通，无否定 |
| 第 0 个孩子（层号 zero 抬到 `h₁ 1`）上一般参照的抬高 | `YiSDRead.raise₀` | 编译定理，成立 |
| 嵌入出口第二分量是否恰是两棵 Ω 树之间的形式 | `YiSDIface.SD.Split.need`、`give` | 编译定理（互推；比 `SubDom` 多一个前提 `KD x`） |
| 逐点义务在什么字面条件下成立、何处无解 | `same`、`cap`、`stuck` | 编译定理；`stuck` 的前提没有实例 |
| 读回形式对一切站 | `sub-read`、`top-read`、`Tw.sub-readᵗ`、`Tw.cap-domᵗ` | 编译定理，无前提 |
| `Hand₁` | `Prefix.hand₁`、`Tw.hand₁ᵗ` | 编译定理；条件是上下文取前缀形、`Bd` 取 "底值对着 F x P" |
| Ω 树上的保持是否需要一般的 `SubDom` | `SD.AtΩ.lowΩ`、`Prefix.lowΩᵖ`、`Tw.lowΩᵗ` | 条件定理：不需要 |
| 域外（原材料高于孩子层号的 Ω 树）在该格上无解 | 无 | 判断，未编译 |
| 现接口能否只消费读回形式 | 无 | 判断：不能，见第 4 节 |

#### 2. 文件表

| 文件 | 代码行 / 总行 | 冷编退出码 | 峰值内存 |
|---|---|---|---|
| `probes/OCF/Lean/YiSDIface.lagda.md` | 131 / 212 | 0 | 620 MiB |
| `probes/OCF/Lean/YiSDRead.lagda.md` | 95 / 160 | 0 | 2693 MiB |

- 冷编时只删自己两个 `.agdai`，日志里各只有自己模块一行 `Checking`，无警告。
- 禁用构造与本机路径检索为 0。
- `importclosure.py OCF.Lean.YiSDIface`：禁用表命中 0。`YiSDRead` 文首标验收文件，未查。
- 没有退出 251。
- 临时文件：`<实验目录>/work/YiSD/YiSD0.agda`，日志在同一目录。

#### 3. 定理表

`YiSDIface.SD` 的参数同 `YiQDFold.QDPack`。记 `Lrᶜ c = j ⊕ offsets S c`，`Ωˢ c = proj₁ (Ωt (Lrᶜ c))`，`Tᵣ = Ref.T 𝕋`，下面的 `⊕` 指 `Ref._⊕_ 𝕋`。

**`YiSDIface`（不读记号，全部编译定理）**

- 定义 `SubAt c t s = Σ Tᵣ λ s″ → Rᵍ (Lrᶜ c) s″ (Ωˢ c) × Le (t ⊕ s) (t ⊕ s″)`
  白话：一点上的义务。
- 定义 `Dominate = (c : Tr k) → ∀ {t s x} (y : ChTᵍ ℓ c) → KD (upᵍ x c y) → Rᵍ ℓ t x → Rᵍ (h c) s (chTᵍ ℓ c y) → SubAt c t s`
  白话：`EmbOutD` 的第二分量。
- 定义 `SubDomᴷ = ∀ (c : Tr k) {t s : Tᵣ} {x : Tr ℓ} → KD x → Rᵍ ℓ t x → Rᵍ (h c) s (proj₁ (Ωt (h c))) → SubAt c t s`
- `need : Dominate → SubDomᴷ`，`give : SubDomᴷ → Dominate`，`weaken : SubDom → SubDomᴷ`
  白话：域里的嵌入出口恰是两棵 Ω 树之间的形式。
- `toOut : Hand₁ → Dominate → ∀ {a} (s : Stᴮ a) K → Bdᴮ s K → EmbOutD sysᴮ sysᴬ keepᴬ embᴮ Le Dᴮ s K (inj₂ (rebᴮ s))`，另有 `fromOut` 取回第二分量。
- `same : (∀ {t} → Le t t) → ∀ c {t s} → Rᵍ (Lrᶜ c) s (Ωˢ c) → SubAt c t s`
  白话：参照已对着替身时义务成立。
- `cap : (∀ t {s s″} → Le s s″ → Le (t ⊕ s) (t ⊕ s″)) → ∀ c {t s s″} → Le s s″ → Rᵍ (Lrᶜ c) s″ (Ωˢ c) → SubAt c t s`
  白话：参照沿 Le 不高于替身的某个参照时义务成立。
- `stuck : ∀ c {t s} (H : Tᵣ → Set) → (∀ {s″} → Rᵍ (Lrᶜ c) s″ (Ωˢ c) → H s″) → (∀ {s″} → H s″ → Le (t ⊕ s) (t ⊕ s″) → ⊥) → SubAt c t s → ⊥`
  白话：参照越过替身的一切参照时无解。
- 定义 `SubRead ρ top = ∀ c {η} → ρ c η → Rᵍ (Lrᶜ c) (top η) (Ωˢ c)`，`CapDom ρ top = ∀ c {t s η} → ρ c η → Le s (top η) → SubAt c t s`
- `read→cap : (∀ t {s s″} → Le s s″ → Le (t ⊕ s) (t ⊕ s″)) → ∀ {ρ top} → SubRead ρ top → CapDom ρ top`
- 定义 `RefBr β c a′ = Σ Cxtᴬ λ K″ → Σ Tᵣ λ s″ → Bdᴬ (Srᴮ β c zero) K″ × Rᵍ (Lrᶜ c) s″ (Ωˢ c) × (apᴬ K″ s″ ≡ a′)`
- `AtΩ.low-branch : (β : Tr⁺ j) (c : Tr k) {a′ : Tᵣ} → RefBr β c a′ → Rᵍ j a′ (proj₁ (Φᴮ (rt β) (proj₁ (upz c (Ωt (h c))))))`
  白话：Ω 树的一个分支上的保持。模块前提是 `Weak`、`Node` 与辅助系统上的保持 `auxK`。
- `AtΩ.lowΩ : (β : Tr⁺ j) (K : Cxtᴮ) (ev : Kept (inj₁ (inj₁ tt))) {a κ : Tᵣ} → Ref.CΩ 𝕋 (apᴮ K a) κ → Graded.Nu 𝔾 j (proj₁ ev) κ → (∀ η c → Rᵍ k η c → RefBr β c (Ref.fsT 𝕋 (apᴮ K a) η)) → Rᵍ j (apᴮ K a) (proj₁ (Φᴮ (rt β) (proj₁ (Ωt ℓ))))`
  白话：顶槽位保留时 Ω 树上的保持。不要求 `Rᵍ ℓ a (Ωt ℓ)`，不用主系统的生成原理。
- `FromAux.auxKᴬ`：`auxK` 由辅助系统的 `OutDT` 经 `YiQDIface.SuffD.keepAllᴰ` 给出。
- `Prefix.hand₁ : Hand₁`
  白话：上下文 `(x , P) ↦ F x (P ⊕ t)`、`Bd` 取 `Rᵍ j (F x P) (proj₁ β)` 时，`Hand₁` 对一切 t、x 成立。
- `Prefix.refBr : ∀ {ρ top} → SubRead ρ top → (β : Tr⁺ j) (K : Cxtᵖ) → Bdᴮᵖ (rt β) K → ∀ c {η a′} → ρ c η → apᵖ K (top η) ≡ a′ → RefBr β c a′`
- `Prefix.lowΩᵖ : ∀ {top} → SubRead (λ c η → Rᵍ k η c) top → (β : Tr⁺ j) (K : Cxtᵖ) → Bdᴮᵖ (rt β) K → (ev : Kept (inj₁ (inj₁ tt))) {a κ : Ref.T 𝕋} → Ref.CΩ 𝕋 (apᵖ K a) κ → Graded.Nu 𝔾 j (proj₁ ev) κ → (∀ η → apᵖ K (top η) ≡ Ref.fsT 𝕋 (apᵖ K a) η) → Rᵍ j (apᵖ K a) (proj₁ (Φᴮ (rt β) (proj₁ (Ωt ℓ))))`

**`YiSDRead`（验收文件，读记号；`Top a ν` 即 `GR.R a (E.Ωt ν) (proj₁ (O.Ωt a))`）**

- `sub-read : ∀ k j (c : Tr k) {η} → GR.R k η c → Top (j ⊕ ↑ k c) η`（编译定理）
  白话：孩子的读法 η 给出替身 Ω 树的参照 Ω_η，对一切 k、j、c。
- `top-read : ∀ k j {t} → GR.Rd j t → Top j t → (c : Tr k) → ∀ {η} → GR.R k η c → Top (j ⊕ ↑ k c) (t ++ η)`（编译定理）
  白话：j 读成 t 时，替身支配 Ω_{t++η}。
- `fs-top : ∀ μ η → E.fsT (E.Ωt (E.Ωs μ)) η ≡ E.Ωt η`（编译定理）
- `Tw.sub-readᵗ : SubRead ρ E.Ωt`，`Tw.sub-read⁺ : ∀ {t} → Dom j t → SubRead ρ (λ η → E.Ωt (t ++ η))`，`Tw.cap-domᵗ : CapDom ρ E.Ωt`，`Tw.hand₁ᵗ : Hand₁`，其中 `ρ c η = GR.R (tw n) η c`（编译定理）
  白话：塔每一项、每个目标 j 上，读回形式、带盖的支配、`Hand₁` 成立。Le 取 `≤ᵀ`，上下文取 `(ν , P) ↦ ψ_ν(P ++ t)`。
- `Tw.lowΩᵗ : ∀ μ (β : O.Tr⁺ j) (K : Cxtᵖ) → Bdᴮᵖ (rt β) K → (ev : Kept (inj₁ (inj₁ tt))) {κ : E.T} → E.cof (apᵖ K (E.Ωt (E.Ωs μ))) ≡ E.cΩ κ → GR.Nu j (proj₁ ev) κ → (∀ η → E.fsT (apᵖ K (E.Ωt (E.Ωs μ))) η ≡ apᵖ K (E.fsT (E.Ωt (E.Ωs μ)) η)) → GR.R j (apᵖ K (E.Ωt (E.Ωs μ))) (proj₁ (Φᴮ (rt β) (proj₁ (O.Ωt (tw (suc n))))))`（条件定理，另有模块前提 `auxK`）
  白话：塔第 n+1 项的 Ω 树上换基折叠的保持，参照取 Ω_{Ω_{μ+1}}。
- `CellRaise : Set`（只有陈述）
  `∀ {s} → GR.R (h₁ ω⁰) s (proj₁ (O.Ωt (h₁ ω⁰))) → GR.R (h₁ (nat 1) ⊕ ↑ zero ω⁰) s (proj₁ (O.Ωt (h₁ (nat 1) ⊕ ↑ zero ω⁰)))`
- `Cell.cell-read : ∀ {η} → GR.R zero η ω⁰ → Top (h₁ (nat 1) ⊕ ↑ zero ω⁰) (E.natT 1 ++ η)`（编译定理）
- `Cell.cell-cap : ∀ {t s η} → GR.R zero η ω⁰ → s ≤ᵀ E.Ωt η → SubAt ω⁰ t s`（编译定理）
- `Cell.cell-same : CellRaise → ∀ {t s} → GR.R (h₁ ω⁰) s (proj₁ (O.Ωt (h₁ ω⁰))) → SubAt ω⁰ t s`（编译定理，归约）
- `Cell.kept₁ : Kept (inj₁ (inj₁ tt))`（该格顶槽位保留，取自 `kept-tw1`）
- `raise₀ : ∀ {s} → GR.R zero s (proj₁ (O.Ωt zero)) → GR.R (h₁ (nat 1)) s (proj₁ (O.Ωt (h₁ (nat 1))))`（编译定理）
  白话：第 0 层的 Ω 树嵌在 `h₁ 1` 的 Ω 树第一分支下面，所以一般参照也能抬高。
- `gradedˢ : Graded blkᵍ foldᴮ rowsᴮ refᴱ 𝕍`、`weakˢ`、`nodeˢ`
  各字段照 `YiFIGen.gradedᴷ`，`Bdˢ` 照 `YiGIInst.Bdᵍ`。我只用到关系、`Weak`、`Node`；别的字段没有检验过。同批 YiWR 若也写这个实例，两份应合并。

#### 4. 第一个障碍

**障碍：一般参照上的抬高，在后继形状的孩子层号上。精确到引理：**

`∀ {s} → GR.R (h₁ (nat 1)) s (proj₁ (O.Ωt (h₁ (nat 1)))) → GR.R (h₁ (nat 1) ⊕ ↑ zero (nat 1)) s (proj₁ (O.Ωt (h₁ (nat 1) ⊕ ↑ zero (nat 1))))`

这是 `CellRaise` 的第 1 个孩子。这一条我没有写进文件，也没有编译。

- **性质：数学上挡住，不是工程问题。** 后继形状层号的 Ω 树，顶槽位在被抬高的那一层（低处 `Tr zero`，高处 `Tr (h₁ 1)`）。推导用 `mΩ` 时，低处的前提只对低层的 (η, c) 给出结论，高处要对高层的 (η′, c′) 给出结论，方向相反。高处的 Ω 树又只有第一分支在它下面，嵌入加放宽的证法（`raise₀` 用的）只在第 0 个孩子上可用。
- **没有否定。** 反例只能来自非标准形的参照项。这类项不在读回域里，即使找到也只说明谓词太宽。我没有找到，也没有排除。
- **判断：这是参照一侧量化域太宽，不是值的障碍。** 依据是读回形式对一切站成立，以及 `lowΩ` 不用一般形式。

**对接线（YiWR）的后果（判断）。** `YiQDIface.SuffRD` 经生成原理走遍 `R ℓ a x` 的一切推导，嵌入规则里孩子参照是任意的，所以 `OutRDT.embE` 要的是一般形式，现接口不能只消费读回形式。两条出路：
- 读回域取 `Gx = Ω 树`（主线 `domsᵍ` 就是这样）时，用 `lowΩ` 代替主系统的 `OutRDT`。主系统的参照义务就只剩顶槽位三项（同 `Below` 的内容）和分支上的 `RefBr`。
- 或给接口的嵌入规则加参照一侧的域。这要改 `SuffRD` 的证明，我没有做。

`YiAbsGSuff.Tower.K` 只在参照 `Ωr (kt n)`、树 `Ωt (tw n)` 上用 LowKeep；这一点我读了代码，但没有把 `lowΩ` 接进 `Suff`。

**`lowΩᵗ` 剩下的前提（都没有实填，可满足性未证）：**
- 辅助系统上的保持 `auxK`。它由辅助系统的 `OutDT` 给出，辅助系统自己的嵌入行是回退行，不经过换基。
- 上下文保持余尾 Ω：`E.cof (apᵖ K (Ωt (Ωs μ))) ≡ cΩ κ`。
- 与代入交换。
- 目标槽位允许 κ。

后三项就是 `YiXTIface.Below` 的三项，属 YiBA 那一路。`Kept` 在塔第 1 项有实例（`kept-tw1`）；塔第 2 项起顶槽位可以不保留（`AuditEKeep.drop₂`，我只读了留档，没读代码）。

**翻译账。**
- 新定义全在接口与验收侧。没有新构造子，没有改折叠，没有用 `Lab`。
- `SubAt`、`SubRead`、`CapDom`、`RefBr` 的形状来自换基行自己的出口（`EmbOutD`）与 Ω 树的形状，不读自基本列。
- 受记号引导、如实记账的两处：替身的参照取 Ω_η（记号的 `E.Ωt`）；前缀上下文 `ψ_ν(P ++ t)` 是参照一侧的选择。
- `sub-read` 给的是把 j 读成空的参照，`top-read` 才带上 j 的读法；前者对下界够用，是否精确没有陈述。
- 没有新增闭包定理的专属前提。`lowΩ` 的前提比 `lowᴰ` 少：不要主系统的 `zeroE`、`succE`、`limE`、`leE`、一般的 `embE`。

#### 5. 偏离与事故；没有读、只凭转述的东西

- **偏离 1：** 简报第 2 步要 "在读回域上证 `SubDom`"。`SubDom` 的量化（任意孩子参照）不能按读回域限制而保持原类型，我交的是 `CapDom` 与 `SubRead`，另加 `lowΩ` 说明 Ω 树上它们够用。这改了被证陈述的形状，请主审核对是否合用。
- **偏离 2：** 自建了 `gradedˢ`（简报没有要求）。
- **没有事故。** 一次类型错误（把构造子名 `up` 用作变量名），改名后通过；一次导入警告，已去掉。
- **没有做的：** `stuck` 的实例；域外无解的编译否定；`lowΩ` 接进 `YiAbsGSuff`；Bedrock 性能手册没有读（没有遇到性能问题）。
- **只凭转述或留档引用的：** `AuditEKeep.drop₂`、`YiBCReach`、`YiSV*`、`YiZS*`、`YiUF*`、`YiXTKp`、`YiXTReb`、`YiXTCur` 的代码都没有读。`YiNLRaise.raiseR` 只读了签名与证明体，没有重新核它的前提。`CompareTable.md` 没有读。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：参照一侧，替身支配原材料（嵌入行出口）（前缀 YiSD，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。同批另两路（`YiWR`、`YiBA`）与你互不导入。

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
换基行的嵌入出口：`YiQDFold.SubstDom.embEᴮ : Hand₁ → SubDom → …`；`raise→SubDom` 把 `SubDom` 归到 "Ω 树上的关系沿层号抬高保持"：`∀ (c : Tr k) {u} → Rᵍ (h c) u (proj₁ (Ωt (h c))) → Rᵍ (j ⊕ offsets S c) u (proj₁ (Ωt (j ⊕ offsets S c)))`（Le 自反时）。YiQD 判断最可疑的是 "层号值相同而结构不同" 的格，例如 c = ω、目标 d = 1 时的 `h₁ ω` 与 `h₁ 1 ⊕ ↑ω`。另：审查 E 路判断，在读回域里替身对嵌入块是高估不是丢值（`Reports-2026-11-16/AuditE.md`）。

#### 要做的（按序）
0. **最小实例**：在可疑的那一格（c = ω、d = 1）上写出 `raise` 那条保持的陈述，在临时文件里编译并试判定（成立或编译否定）。
1. **出口分解**：仿 `YiXTIface`，把嵌入行的出口也做一次分解：在什么字面条件下义务是什么，哪些点上无解。
2. **一般形式**：对 EBO 记号参照，在读回域上证 `SubDom`（或它的充分形式）与 `Hand₁`；若一般形式不成立，写成编译否定（反例在读回域里才算），并给出最弱的可用形式（例如只对读回域里的原材料、或只要求不低于原材料的读法）。
3. 交：嵌入出口的状态与用到的参照一侧引理；翻译账。

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


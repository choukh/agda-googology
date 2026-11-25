# 比较表的对角条目不判等（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 02:46 至 03:13 |
| 工具调用 / agda 编译 (粗数) | 81 / 19 |
| token (usage 字段，按消息去重) | 输出 156076；新写入缓存的输入 305065；读缓存的输入 13462958；其余输入 134 |
| 写过的仓库文件 | `YiDGCell.lagda.md`, `YiDGDiag.lagda.md` |
| 文件前缀 | `YiDG` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0，导入闭包干净；现行行的两个孩子下标是独立变量，对角只能由下标的函数给出（row-diag、kp-diag）；任何表、一列或逐孩子的可缺路径在一个 ℕ 极限孩子的对角上有条目就对康托族弱判等（wdecα、all→wdecα、cell→wdecα、cellP→wdecα，无前提），加函数外延得 WLPO（条件）；数字对角可满足（diag-nat） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b76/YiDG.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### YiDG 回报：比较表的对角条目不判等（Opus 5.5）

##### 1. 判决

**对纲领与目标意味着什么**
- 纲领：没有触犯。全部在树侧，不读记号，不改树、折叠、合法性，无公设。函数外延只作为显式前提 `FunextB` 出现在否定定理里，用到它的结论标 "条件"。
- 目标（树自足）：得到一条树侧判据，已编译。
  - 现行折叠里，"同一个孩子" 的对角只能由下标的函数给出。
  - 塔第 1 项上，任何 "孩子 c ↦ 两层之间可缺的字面路径" 的列，只要在一个 ℕ 极限孩子 c⋆ = sᵐ ωᵉ 处有条目，就对康托族弱判等；加 `FunextB` 得 WLPO。ωᵉ 是偶数列的 ω，sᵐ 是 m 次后继。
  - 所以，`YiCTCall` 那一格对一般孩子（d 取极限）不能靠表的对角条目来救，也不能靠 "沿目标逐孩子带一条可缺路径" 来救。
  - 能救它的写法必须对孩子一致、不经这类列（换基一类）。这一句是判断。
- 与 `YiTBObs.exact→wdec` 的关系：那里 "别处为空" 是前提，且在 `Tr zero` 上没有实例。这里 "别处为空" 在康托族上由 "没有字面路径" 逼出，所以只要对角那一个条目。

**各步到哪一步**
- 第 0 步：完成。临时文件 `DG0.agda` 编译退出 0，从派出算起约 14 分钟。
  - 类型分三种：表 `TabW k h`（逐字就是 `RbS (sΩ k) h`，`tab-is-RbS` 由 refl 给出）；相等 `EqW`（即 `ViaE` 的 E）；携带 `CarW`。
  - 行的子句里，嵌入的孩子 c（来自树 `up x c y e`）与路径的孩子 c′（来自 `inc c′ v`）是两个独立的模式变量。比较只经 `proj₁ r c c′`；同一个变量给两边时卡在 `proj₁ r c c` 上（`row-diag`）。`kpʳ` 在槽位孩子与路径孩子的对角上恒为空（`kp-diag`）。
  - 结论：现行树与折叠里，见证只能从下标算出（读定义的判断，加上面的形状定理）。按简报改写成编译否定，已完成。
- 第 1 步：没有做，前提不成立。
  - 现行树与折叠里没有可带着走的见证。要让槽位或路径带上 "出处"，就得改 `Pos`、`Pth` 或折叠状态，按规则停下回报。
  - 不改树、只加一个参数的两种 "带着走" 写法（表的一列；目标逐孩子的可缺路径，即 `inu` 的可缺版本）也已编译否定：`pth→wlpo`、`cellP→wlpo`。
  - 代替简报要的两格事实：
    - `YiCTCall` 那一格（d = 1）：用现成闭项表 `YiTBRow.tb` 时保留在 q′（`tb-pos`，有限测试）。
    - 变量 c 的对角：`row-diag`（形状定理）。
    - 这两条都不是 "带见证的保留判定" 候选。
- 第 2 步：给出判断，见问题表末两行。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 见证在现行折叠里是数据还是两下标的函数 | `DG0`；`YiDGDiag.row-diag`、`kp-diag` | 形状定理 + 读定义的判断 |
| 表或列在 sᵐ ωᵉ 的对角有条目 ⇒ 弱判等 | `YiDGDiag.ColW.wdecα`、`Diag`、`all→wdecα` | 编译定理，无前提 |
| 同上 ⇒ WLPO | `col→wlpo`、`wlpo`、`all→wlpo`、`pth→wlpo` | 编译定理，条件（`FunextB`） |
| 前提不自相矛盾 | `diag-nat`、`dec→tab`、`dec→pth` | 编译定理 |
| `YiCTCall` 那一格对一切 d 路径经 d+2；d = ωᵉ 时分支 z 查 (z, ωᵉ+2)，最小表在对角上无条目 | `YiDGCell.CellD.v-form`、`br-ω`、`row-ω`、`min-ω` | 编译定理（refl，形状档） |
| 那一格（d = ωᵉ）任何表或逐孩子路径有对角条目 ⇒ 弱判等 / WLPO | `cell→wdecα`、`cell→wlpo`、`cellP→wdecα`、`cellP→wlpo` | 编译定理；WLPO 为条件 |
| 数字对角：现成闭项表 `tb` 在 d = 1 那一格保留在 q′ | `YiDGCell.tb-pos` | 有限测试 |
| 对角见证只救对角那一类格，不碰非对角对 (ω, ωᵉ) | 已有的 `YiRKCell.no-ωᵉ`（两方向都没有字面路径，表在那里只能为空） | 编译定理（已有）+ 判断 |
| 与换基互补还是被换基覆盖 | 已有的 `YiRKCell.w3′`、`seen-s`、`keep-lift` | 判断（见下） |

**与换基的关系（判断，未编译值）**
- 已编译的事实：
  - 换基在同步路径（经 d+1）上的行，对一切 c 是同一个式子（`w3′`），不读表。对角 c = d+1 不特殊，本路的否定对它不适用。
  - 后继孩子处替身树的顶走链（`seen-s`），这包括对角 c = d+1。目标层副本的槽位在更深处保留（`keep-lift`）。
- 判断：
  - 在数字对角上，两者不是谁覆盖谁：表条目让顶在 q′ 保留（`tb-pos`、`cf-pos`），换基的顶走链。注意这是两种折叠之间的比较。
  - 在极限对角上，表与逐孩子路径都被否定，剩下的只有换基这类对孩子一致的行。所以两者在数字孩子上互补，在极限孩子上只剩换基。
  - 换基在对角那一格的值够不够，没有定理。

**量化域（判断）**：康托族 cα α 都是 tw 1 的合法孩子。Ω 结点的每个分支都会被折叠问到（`br-ω`），表是全函数，这是折叠的要求，不是谓词取得太宽。真实链孩子（`YiRKChain.Real.child-L`）不是本文的 c⋆，没有编译覆盖。同一论证对 "字面数字项且有间隔" 的极限孩子成立，这一句是判断。

##### 2. 文件表

| 文件 | 总行 / 非空代码行 | 冷编退出码 | 峰值驻留 | 导入闭包 |
|---|---|---|---|---|
| `probes/OCF/Lean/YiDGDiag.lagda.md` | 232 / 146 | 0（日志只有自己的 Checking 行） | 166 MB | OK，禁用表命中 0 |
| `probes/OCF/Lean/YiDGCell.lagda.md` | 202 / 135 | 0（同上） | 179 MB | OK，禁用表命中 0 |

两个文件里禁用构造与本机路径的检索结果都是 0。

临时文件（纯 `.agda`，都退出 0）：
- `<实验目录>/work/YiDG/DG0.agda`（第 0 步：类型与形状）
- `<实验目录>/work/YiDG/DG1.agda`（v-form）
- `<实验目录>/work/YiDG/DG2.agda`（一般 d 的展开）
- `<实验目录>/work/YiDG/DG3.agda`（tb-pos）

##### 3. 定理表

记号约定：
- `Tab = RbS (sΩ zero) h₁`
- `Col m = (c : Tr zero) → Maybe ((h₁ (sᵐ m ωᵉ) ≤ h₁ c) ⊎ (h₁ c ≤ h₁ (sᵐ m ωᵉ)))`
- `Pth⋆ m = (c : Tr zero) → Maybe (h₁ (sᵐ m ωᵉ) ≤ h₁ c)`
- `FunextB = {α β : ℕ → Bool} → (∀ n → α n ≡ β n) → α ≡ β`
- `cα α = lim (fα α) (λ n → stp (α n) (α (suc n)) (dbl n))`，其中 `fα α n = sh (α n) (dbl n)`

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `row-diag` | `∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (pv : Pv (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c (v : j ≤ h c) ot β x y e → Σ _ λ F → Σ _ λ G → Σ _ λ H → FC.ψ (nd (sΩ k) h) o r pv B j (inc c v) ot β (up x c y e) ≡ dW (proj₁ r c c) F G H` | 同一个孩子变量给两边时，行卡在表的对角 `proj₁ r c c` 上 | YiDGDiag | 编译（形状） |
| `kp-diag` | `∀ k h (o : Ok (nd (sΩ k) h)) (pv : Pv (nd (sΩ k) h)) c t {j} (v : j ≤ h c) → kpʳ (nd (sΩ k) h) o pv (inj₂ (c , t)) (inc c v) ≡ nothing` | 槽位与路径同在孩子 c 时，`kpʳ` 也走链 | YiDGDiag | 编译（形状） |
| `cα-α₀` | `cα (λ _ → false) ≡ ωᵉ` | 康托族在全假处字面是 ωᵉ | YiDGDiag | 编译 |
| `pathA` / `pathB` | `∀ {b j ℓ} → Pth b j ℓ → j ≡ h₁ ωᵉ → ℓ ≡ h₁ (cα α) → AllF α`（`pathB` 两端对调） | ωᵉ 层与 cα α 层之间有字面路径，α 就处处为假 | YiDGDiag | 编译 |
| `peelᵐ` | `∀ {b} (m : ℕ) (x x′ : Tr zero) → Pth b (h₁ (sᵐ m x′)) (h₁ (sᵐ m x)) → Pth b (h₁ x′) (h₁ x)` | 剥掉两边相同层数的后继 | YiDGDiag | 编译 |
| `ColW.wdecα` | `IsJust (col c⋆) → ∀ α → AllF α ⊎ (c⋆ ≡ sᵐ m (cα α) → ⊥)`（模块参数 `m`、`col : Col m`，`c⋆ = sᵐ m ωᵉ`） | 一列在 c⋆ 有条目就弱判等 | YiDGDiag | 编译，无前提 |
| `col→wlpo` | `FunextB → (m : ℕ) (col : Col m) → IsJust (col (sᵐ m ωᵉ)) → WLPO` | 加函数外延得 WLPO | YiDGDiag | 编译，条件 |
| `wlpo` | `FunextB → (t : Tab) (m : ℕ) → IsJust (t (sᵐ m ωᵉ) (sᵐ m ωᵉ)) → WLPO` | 表在一个极限对角有条目 ⇒ WLPO | YiDGDiag | 编译，条件 |
| `all→wdecα` | `(t : Tab) → (∀ c → IsJust (t c c)) → ∀ α → AllF α ⊎ (ωᵉ ≡ cα α → ⊥)` | 处处有对角的表弱判等 | YiDGDiag | 编译 |
| `all→wlpo` | `FunextB → (t : Tab) → (∀ c → IsJust (t c c)) → WLPO` | 同上，得 WLPO | YiDGDiag | 编译，条件 |
| `pth→wlpo` | `FunextB → (m : ℕ) (o : Pth⋆ m) → IsJust (o (sᵐ m ωᵉ)) → WLPO` | 目标逐孩子的可缺路径在对角有条目 ⇒ WLPO | YiDGDiag | 编译，条件 |
| `diag-nat` | `∀ n → IsJust (tb (nat n) (nat n))` | 数字对角可满足 | YiDGDiag | 编译 |
| `dec→tab` | `∀ c → IsJust (tabD c c)`（模块参数 `D : (c c′ : Tr zero) → Dec′ (c ≡ c′)`） | 能判定字面相等，就有处处对角的表 | YiDGDiag | 编译 |
| `CellD.v-form` | `vᵈ ≡ inc (suc (suc d)) (inc tt self)`（对一切 `d : Tr zero`） | `YiCTCall` 那一格的路径恒经孩子 d+2 | YiDGCell | 编译（refl） |
| `CellD.R-form`、`kp-top`、`E0`–`E4` | `proj₁ Rᵈ ≡ tbᶻ zero h₁`；`IsJust (kpᶜ (tw 1) Oᵈ PVᵈ (inj₁ (inj₁ tt)) vᵈ OTᵈ)`；`brᵍ d zero ≡ proj₁ (next⁺ β) + t₀`；E1 到 E4 | `YiCTCall` 的展开对一切 d 成立 | YiDGCell | 编译（refl） |
| `br-ω` | `∀ z → brΩ (pr Cω.t₀) Cω.hd₀ z ≡ proj₁ (Cω.Fch 0) + proj₁ (FC.ψ (tw 1) Cω.Oᵈ Cω.Rᵈ Cω.PVᵈ Cω.Btᵈ (h₁ (suc ωᵉ)) Cω.vᵈ Cω.OTᵈ Cω.βtᵈ (Cω.Y z))` | d = ωᵉ 时，被保留结点的分支 z 是 tw 1 上那次折叠 | YiDGCell | 编译（refl） |
| `row-ω` | `∀ (Rv : Rb (tw 1)) z → Σ _ λ F → Σ _ λ G → Σ _ λ H → FC.ψ (tw 1) Cω.Oᵈ Rv Cω.PVᵈ Cω.Btᵈ (h₁ (suc ωᵉ)) Cω.vᵈ Cω.OTᵈ Cω.βtᵈ (Cω.Y z) ≡ dW (proj₁ Rv z (suc (suc ωᵉ))) F G H` | 换成任意表，查的都是 (z, ωᵉ+2) | YiDGCell | 编译（refl） |
| `min-ω` | `proj₁ Cω.Rᵈ (suc (suc ωᵉ)) (suc (suc ωᵉ)) ≡ nothing` | 最小表在对角上没有条目 | YiDGCell | 编译 |
| `cell→wdecα` | `(Rv : Rb (tw 1)) → IsJust (proj₁ Rv (suc (suc ωᵉ)) (suc (suc ωᵉ))) → ∀ α → AllF α ⊎ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) (suc (suc (cα α))) → ⊥)` | 那一格的对角条目弱判等 | YiDGCell | 编译 |
| `cell→wlpo` | `FunextB → (Rv : Rb (tw 1)) → IsJust (proj₁ Rv (suc (suc ωᵉ)) (suc (suc ωᵉ))) → WLPO` | 同上，得 WLPO | YiDGCell | 编译，条件 |
| `cellP→wdecα` | `(o : (c : Tr zero) → Maybe (h₁ (suc ωᵉ) ≤ h₁ c)) → IsJust (o (suc (suc ωᵉ))) → ∀ α → AllF α ⊎ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) (suc (suc (cα α))) → ⊥)` | 目标 h₁(ωᵉ+1) 带着逐孩子的可缺路径，要在对角保留就弱判等 | YiDGCell | 编译 |
| `cellP→wlpo` | 与 `cellP→wdecα` 前提相同，前面加 `FunextB →`，结论 `WLPO` | 同上，得 WLPO | YiDGCell | 编译，条件 |
| `dec→pth` | `IsJust (oD (suc (suc ωᵉ)))`（模块参数 `D : (c : Tr zero) → Dec′ (_≡_ {A = Tr zero} (suc (suc ωᵉ)) c)`） | 有判定时前提可满足 | YiDGCell | 编译 |
| `tb-pos` | `posΩ (pr newᵗ) tt ≡ q′`，其中 `Rᵗ = tb , λ c → rbᶻ (h₁ c)` | 数字表在 d = 1 那一格保留在 q′ | YiDGCell | 有限测试 |

##### 4. 第一个障碍
- 第 1 步被 `ColW.wdecα` 挡住，同时依据 `row-diag` 这个定义事实，属于数学上挡住。
  - 现行行的两个孩子下标是独立的模式变量。
  - 不改树时能带的见证只有 "列"（表的一列，或逐孩子的可缺路径），而列在极限孩子 c⋆ 处有条目就弱判等。
  - 再往外，就要让槽位或路径带出处（改 `Pos`、`Pth` 或折叠状态），这改的是树或折叠，按规则停下，未做，也不否定。
- 工程上没有障碍：峰值不到 200 MB，没有 251 或 124。

##### 5. 偏离与事故
- 第一次编译套了 `/usr/bin/time -l`，被沙盒拦下（sysctl 不允许），打印的 "exit 1" 是 time 自己的退出码。之后直接跑 agda，另加 `+RTS -s<文件>` 记录驻留。
- 退出 42 共五次，都是普通类型错误，改后通过：
  - 仓库文件三次：`c₀` 与 `YiRWOps.c₀` 撞名，改名为 c⋆；`noHL` 递归里隐式 b 未解，改成显式；`_≡_` 里 `suc` 有 ℕ 与树构造子两种重载，加 `{A = Tr zero}`。
  - 临时文件两次：一般 d 时保留结点的分支类型卡在 `Br⁼ …` 上，改为只在 d = ωᵉ 陈述；`YiCTCall` 不导出 `j`。
- 简报第 1 步要的 "带见证的候选与两格事实" 没有交，原因见第 1 节。交的是形状定理 `row-diag` 与有限测试 `tb-pos`，它们不是候选。
- `YiDGCell` 的 `CellD` 取自 `YiCTCall` 第 137–205 行，`Y` 即第 230 行的 `y₃`，`n1` 换成变量 d，已在文首写明。`noHL` 推广自 `YiTBObs.noL`。
- 没有读、只凭转述或签名引用的：
  - 只凭签名或陈述：`YiBSFold`（只读文首）；`YiBSBase.seen`（只经 `YiRKCell.seen-s`、`w3′` 的陈述）。
  - 只凭简报转述：`YiRKChain`（`Real.child-L`）、`YiFIIface` 与 `keepOf`、`YiFINeg`、`AuditD.md` 正文（只读了附件 `AuditDFin`）、`YiVA.md`。
  - 没有读：`EBOHandbook` 4.2、4.6 节与 Bedrock 性能手册。全程没有出现性能问题，所以没有去查。
- AGENTS.md 全文在上下文中读过。没有改任何已有文件，没有提交。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：比较表的对角条目不判等（前缀 YiDG，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。同批另三路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者已关闭现行折叠上同步对象那一步链步（`YiKTSlot.Cand` 及其变体，台账 V287），依据是两份先读定义的 Fable 5.2 封存审核（留档 `probes/Survey/Reports-2026-11-16/YiVA.md`、`AuditD.md`）。**主线定义不动**；改树、折叠、合法性只在新文件里做候选。
- 第七十六批作者选四路（选项原文）："换基替身的值 (Recommended), 换基的律接进整体接口 (Recommended), 换基证据对真实链孩子的覆盖 (Recommended), 比较表的对角条目不判等"。前缀 `YiSV`（Fable 5.2）、`YiBL`（Opus 5.5）、`YiBC`（Opus 5.5）、`YiDG`（Opus 5.5），互不导入。
- **第七十五批三路（主审冷编复核过）指向同一处**：折叠在被问到的孩子对上要字面证据。
  - `YiRKCell`（不读记号）：朝目标孩子 d（取 ω）的层号折塔第 1 项的 Ω 树时，顶结点在四种折叠里都保留（`top-ω`、`top₁` 到 `top₃`），一切分支 c 都被问到；三种写法的行都不看 c 是否字面延伸 d（`w1`、`w2`、`w3`）。现行行把孩子树折到第 0 层再加上（`w1`、`ι-free`）；上折回退在原材料任何深度的槽位走链（`w2-never`）；**换基**不用原材料，在 `h₁ d ⊕ ↑c` 上重建 Ω 树沿 `lift` 朝原目标折（`w3`、`w3′`），目标层副本的槽位保留（`keep-lift`、`keep-ω`），换基层号没有 Ω 形状子层号（`noΩ-reb`），后继孩子处替身树的顶走链（`seen-s`）。V50 按 "孩子对" 的提法为否：ω 与偶数列 ω 之间两个方向都没有字面路径（`no-ωᵉ`）；字面延伸给出路径（`ext-path`，`Ext d c = zero ⊢ d ◃ c`）。`YiRKChain`：chain 1 副本顶是 ℕ 极限（`Real.L₁`），链孩子层号是 ℕ 极限形状（`Real.child-L`）；副本照 `YiSYReduce`、`YiSYDesc` 重写，与原定义的相等未编译。
  - `YiCTCall`（不读记号）：候选 (C) 在 `cand₂` 实际路径上丢保留的那一格，槽位与目标同在孩子 3 下（对角），对一切来源表走链（`cell`、`org-P₁`）；只给比较表加 (3,3) 条目就保留（`cf-pos`，有限测试）。
  - `YiFIIface`（不读记号）：对折叠参数化的抽象充分性：保留律 `KeepLaw`、回退律 `FallLaw`、参照出口 `Out` ⇒ 每个状态上保持（`Suff.keepAll`）、LowKeep（`sys→low`）；`YiFIFold.lowᴷ`（上折回退的候选上只剩 `Out`，其结点一条 `Out.nodeE` 就是 V50）；`keepOf`（字面路径保留）；配对否定 `YiFINeg.kp-not-flr`、`kp-not-lit`、`kpᴬ-violates`、`main-nf`、`fb-nf`。
- **换基已有的原型**（`probes/OCF/Lean/`，都是候选、不替换主线；先读文首）：`YiBSBase`（`split : (a b : L) → OkO a b → ∀ {j} → j ≤ (a ⊕ b) → (j ≤ a) ⊎ (a ≤ j)`；`rbO : (a b : L) → Rb a → Ok a → OkO a b → Rb (a ⊕ b)`；`rb-tw : (n : ℕ) → Rb (tw n)`；`seen : ∀ {k h} (S : Schema k h) (j : L) → Ok j → floor S ≤ j → Tr⁺ j → Tr k → Tr⁺ j`），`YiBSFold`（换基折叠 `BS.ψ`，"该行的换基部分固定重建 Ω 树，原孩子树只进入低层尾项"），`YiBSRead`（`Read` 码），`YiBSReadNeg`、`YiBSUpNeg`（字面读回的两条否定，不否定值），`YiBSClean`、`YiBSInner`（干净对象上的闭项与内层整行），`YiBSFam`、`YiBSCrit`（有限读回层的保持；`finite-crit`、`finite-shift` 只到数字孩子），`YiBSAccept`（首链点 ψ₁(Ω₃) 关系，输出 ψ₀(Ω₃) 下界）；更早的 `YiRBSib`、`YiRBCrit`、`YiRBFam`。台账 V149（换基；"对任意一块不可写（纸面判断，方向反变）"，出路是改块的嵌入字段为族或收量化域）、V158、V290、V293。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
`YiCTCall` 里丢保留的那一格，槽位所在的孩子与路径所经的孩子是同一个（3 与 3），最小表 `YiMTTab.rbᶻ` 在后继对后继时缺项，加上 (3,3) 条目就保留（`cf-pos`，有限测试）。对数字孩子可以字面填（`AuditDFin.colFin`，附件 `attachments/AuditD-AuditDFin.agda.txt`）。问：对一般孩子，能否不判定两个孩子下标相等，而让 "同一个孩子" 的对角由同一份证据字面给出（例如槽位的孩子下标与路径的孩子下标都取自同一份 `Ok` 证据或同一个构造，YiRQ 回报里提过 "同一孩子的见证"）。

#### 要做的（按序）
0. **先验检查**（AGENTS "开新行前的先验检查"）：对照 `YiAbsObs` 的 `obs→dec` 一族，尤其 `viaE→dec`（经证据函数派发则判等）、`rowE-same`、`rowE-off`，以及 `YiAbsFrame.hand→wdec`、`branch→wdec`；写清 "同一孩子的见证" 的类型是数据（随结构携带）还是要从两个下标算出（后者撞 `viaE→dec`）。在临时文件里编译这个类型。若只能从两个下标算出，就写成编译否定或停下回报。
1. 若能随结构携带：在新文件里写出带见证的保留判定或表的变体（只是候选），在 `YiCTCall` 那一格与一个非数字孩子（变量 c 的对角 (c, c)）上各给一格编译事实。
2. 说明它只救对角那一类格，不解决真实链孩子上的非对角对（`YiRKCell.no-ωᵉ`）；判断（标档）它与换基是否互补或被换基覆盖。

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


# 对位调整：同步对象 L*（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 12:30 至 13:26 |
| 工具调用 / agda 编译 (粗数) | 86 / 20 |
| token (usage 字段，按消息去重) | 输出 255583；新写入缓存的输入 420167；读缓存的输入 18084810；其余输入 154 |
| 写过的仓库文件 | `YiSYDesc.lagda.md`, `YiSYFrame.lagda.md`, `YiSYReduce.lagda.md`, `YiSYSmall.lagda.md` |
| 文件前缀 | `YiSY` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0；ebo-from-stations′（松一层的逐站目标推出 EBO 下界）、k1′、Uᴱ、chain-two、k2′-from-tail : Tail → Kᴱ′ 2 陈述已读；第 3 站下界归约到同步对象上 γ 链从第 1 项起的 Tail，未证 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b70/YiSY.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiSY 回报：对位调整，把第 3 站改在同步对象上

#### 1. 判决

**对纲领与目标意味着什么。** 四个新文件都是验收文件（读记号），没有改树、折叠、表和合法性的任何一行，第 4 层没有反过来改前 3 层，也没有用 Funext。强度没有提高：本轮没有新的无前提序数值下界，`start-sync` 给出的第 3 行第 0 项就是 ψ₀(Ω_Ω)，`YiFRStations.k2` 已经有了。

本轮的收获在结构上：
- 第 3 站（`Kᴱ′ 2`：ψ₀(Ω_{Ω_Ω}) ≼ `twc keelᴱ 2`）的上界一半已无前提编译。
- 下界一半归约到一个对象上的一条对变量的前提。这个对象是树自己的龙骨层号 `kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`，即审核件里的 L*。它的回灌链在第 0 层，是可数的。
- 前提在 γ = 1 处的两半都已无前提成立，剩下的是 γ 链从第 1 项起的 `Tail`。

"树自足"这个目标没有直接推进：同步映射 S 与 γ 链取自记号的规则 6，只出现在验收文件里。选 `kl 1` 作对象靠的是树的龙骨和第一孩子下降，不是记号的基本列。

**翻译账（本路未提升强度，只记来源）：** 没有新的树侧定义；S、γ 读自记号的基本列，只在验收侧；`kl 1` 是龙骨层号，按作者 11-14 的说法不算翻译。

**各步到哪里：**
- **第 0 步完成。** 我选 `keelᴱ`，因为只有它接得上 `upperᴱ`：`keelᵍ` 的站就是 `twᶻ n`，检索没有找到 `twᶻ n ≼ EBOᶻ` 或 `twᶻ n ≼ twc keelᴱ n`。
  - `Kᴱ′ 1` 用 `k1′` 填，这是 `YiFRStations.k2` 去掉末尾的 `station-step 1`。
  - `k1-value` 只能填标准底的 `Kᶻ′ 1`，要经 `Bridge` 才接到 `keelᴱ`。
  - 组装的前提族从 n = 1 起，第 0、1 行仍用 `k0`、`k1`。原因（判断，手算）：`Kᴱ′ 0` 要 ψ₀(Ω) ≼ `twc keelᴱ 0`，而后者约为 ω。若把 `Kᴱ′ 0` 放进前提族，前提就矛盾了。
- **第 1 步完成，两份：**
  - 继承底：`k2′-from-sync : Sᴱ.SyncLow → Kᴱ′ 2`，不需要 `Bridge`。
  - 标准底：`k2ᶻ-from-sync : Sᶻ.SyncLow → Kᶻ′ 2`，上界就是 `keelᶻ 1`。
- **第 2 步：** γ = 1 的两半已编译（`sf₁ᴱ`、`so₁ᴱ`），由此得到无前提的 `chain-two` 和条件定理 `k2′-from-tail : Gᴱ.Tail → Kᴱ′ 2`。γ = 2 挡住（见第 4 节）。
- **第 3 步：** 上界一半对一切 n 已编译（`Uᶻ-all`，标准底）。同步只在 n = 1 成立：编译事实 `kl-index` 表明 `kl (suc n)` 的下标层是 `tw n`。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `Kᴱ′ 0` 不成立（第 0 站约为 ω），前提族改为 `∀ n → Kᴱ′ (suc n)` | `YiSYFrame.part` | 判断（手算），代码已避开 |
| 标准底的塔接不到终点：检索未见 `twᶻ n ≼ EBOᶻ` 或 `twᶻ n ≼ twc keelᴱ n`（`Bridge`） | `YiSYFrame.Bridge` | 判断（检索），无否定 |
| `Tail` 和其中的 `FirstMissing`（ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) ≼ 第 2 个链点的输出）未实填 | `YiSYSmall` | 判断，无否定 |
| 对一切 γ 的 `SyncLow` 含非标准形项；只对链上的值，`Tail` 才是需要的最小前提 | `YiSYReduce.Sync.Low` | 判断 |
| 被上界的是沿 `p*` 降下来的底 `Bᴱ` 上的折叠，不是 `Step 1` 在 c* = Ωt (tw 1) 处的输出（c* 不是链点） | `YiSYReduce` | 判断（没有跨孩子的引理） |
| 标准底实例的 γ = 1 未做：要在 `a₁ e` 里降到 `tw 1`，还要一条 Ok 证明无关性 | `YiSYSmall` | 判断 |
| n ≥ 2 时 `kl n` 的链在 `Tr (tw (n-1))`，不可数，不与 γ 链同步 | `YiSYSmall.kl-index` | 形状是编译定理，后果是判断 |

#### 2. 文件表

四个文件都在 `<仓库>/probes/OCF/Lean/` 下。冷编方式：删掉自己的四个 `.agdai`，8G 上限，从仓库根编译 `YiSYSmall`，退出 0，耗时 18.7 秒。日志里只有这四个模块的 `Checking` 行。禁用构造和本机路径检索都是 0。

| 文件 | 代码行（非空、非注释） | 冷编 |
|---|---|---|
| `YiSYFrame.lagda.md` | 48 | 0 |
| `YiSYDesc.lagda.md` | 52 | 0 |
| `YiSYReduce.lagda.md` | 96 | 0 |
| `YiSYSmall.lagda.md` | 127 | 0 |

文首都不超过 5 行。没有文件标"不读记号"。`YiSYDesc` 的导入闭包经 `OCF.Align.Value` 碰到记号模块（importclosure 退出 1），文首已如实写明。

#### 3. 定理表（全部是编译定理）

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `ebo-from-stations′` | `(∀ n → Kᴱ′ (suc n)) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；其中 `Kᴱ′ n = (h : SI.E.HC (E.EBOψ (suc n))) → SI.E.tree h ≼ K.readRW (twcᴱ n)`，`twcᴱ n = Keel⁻.twc keelᴱ n` | 松一层的逐站目标（第 n 站对第 n+1 行）推出 EBO 下界 | Frame |
| `k1′` | `Kᴱ′ 1` | ψ₀(Ω_Ω) 不高于实际第 1 站 | Frame |
| `k1ᶻ′` | `Kᶻ′ 1`；`Kᶻ′ n = … ≼ K.readRW (MT.twᶻ n)` | 同上，标准底塔 | Frame |
| `bridged` | `∀ {n} → Bridge n → Kᶻ′ n → Kᴱ′ n` | 标准底的站经 `Bridge` 接到实际站 | Frame |
| `descᴮ` | `∀ {j ℓ} (p : j ⊑¹ ℓ) (o : Ok ℓ) (B : Base ℓ) (β : Tr⁺ zero) → Hi B → readRW (Fd j (ok¹ p o) (dn¹ p B) β) ≼ readRW (Fd ℓ o B β)` | 第一孩子下降不升值，对任意不低于 Ω 树的底成立 | Desc |
| `Node.rowsᴮ` | `∀ n → readRW (proj₁ (out (chain n))) ≼ readRW (Fd (nd (sΩ k) h) o B β)` | Ω 结点折到第 0 层不低于每个链点的行 | Desc |
| `fs-S`、`γ-S` | `E.fsn (E.EBOψ 3) m ≡ S (γ m)`、`γ (suc m) ≡ S (γ m)`；`S γ = E.ψ [] (E.fsT (E.ΩTower 3) γ) ∷ []`，`γ = E.γT (E.ΩTower 3) []` | 第 3 行的基本列是 S 沿 γ 链 | Reduce |
| `kl-shape` | `kl 1 ≡ nd (sΩ zero) a₁` | 同步对象的下标层是第 0 层 | Reduce |
| `p*` | `nd (sΩ zero) a₁ ⊑¹ FR.Step.child 1 c₁`，`c₁ = FR.Step.chain 1 1` | 实际第 2 站第 1 个链点的孩子沿第一孩子降到 `kl 1` | Reduce |
| `Uᴱ` | `K.readRW (D.Fd (nd (sΩ zero) a₁) oᴱ Bᴱ (betaᴱ 2)) ≼ K.readRW (twcᴱ 2)` | 同步对象（继承底）在实际第 2 站之下 | Reduce |
| `Uᶻ` | `K.readRW (D.Fd (nd (sΩ zero) a₁) oᶻ (B₀ (nd (sΩ zero) a₁)) (Ωt zero)) ≼ K.readRW (twᶻ 2)` | 审核件的 L*（标准底）在 `twᶻ 2` 之下 | Reduce |
| `Sync.sync-bound` | `SyncLow → (h : E.HC (E.EBOψ 3)) → Rt h ≼ K.readRW (D.Fd (nd (sΩ zero) a) o B β)`；`SyncLow = Low feed × Low (λ e → proj₁ (out e))`，`Low X = ∀ γ e → K.M⁰ γ e → (h : E.HC (S γ)) → Rt h ≼ K.readRW (X e)` | 回灌与输出都保持 γ ↦ ψ₀(Ω_{Ω_γ}) 时，第 3 行不高于该层号的折叠（对层号、底、起点都是变量） | Reduce |
| `k2′-from-sync` | `Sᴱ.SyncLow → Kᴱ′ 2` | 条件定理 | Reduce |
| `k2ᶻ-from-sync` | `Sᶻ.SyncLow → Kᶻ′ 2` | 条件定理 | Reduce |
| `fb` | `K.readRW (twᶻ 1) ≼ K.readRW (proj₁ (Bᴱ zero (ink self)))` | 继承底在第 0 层的分量走 `tw 2` 那一行的回退分支，含 `twᶻ 1` | Small |
| `sf₁ᴱ`、`so₁ᴱ` | `Gᴱ.SF₁`、`Gᴱ.SO₁`；`SF₁ = Low-at (γ 0) feed`，`SO₁ = Low-at (γ 0) (λ e → proj₁ (out e))` | γ = 1 时两半成立（S 1 = ψ₀(Ω_Ω)） | Small |
| `chain-two` | `Gᴱ.Two`；`Two = K.M⁰ (γ 1) (chain 2)` | 同步对象的第 2 个链点不低于 ψ₀(Ω_Ω)，无前提 | Small |
| `start-sync` | `(h : E.HC (E.fsn (E.EBOψ 3) 0)) → Rt h ≼ K.readRW (twcᴱ 2)` | 第 3 行第 0 项经同步对象在第 2 站之下（值已知） | Small |
| `k2′-from-tail` | `Gᴱ.Tail → Kᴱ′ 2`；`Tail = ∀ m → Low-at (γ (suc m)) feed × Low-at (γ (suc m)) (λ e → proj₁ (out e))` | 只剩 γ 链第 1 项起的条件定理 | Small |
| `first-missingᴱ` | `Gᴱ.Tail → Gᴱ.FirstMissing`；`FirstMissing = (h : E.HC (S (γ 1))) → Rt h ≼ K.readRW (proj₁ (out (chain 2)))` | 第一个缺口是 `Tail` 的一个实例 | Small |
| `two-shape` | `Σ (Tr (nd sS (λ _ → zero)) → L) λ hh → a₁ (suc (suc zero)) ≡ nd (sΩ (nd sS (λ _ → zero))) hh` | γ = 2 处输出层号的下标层是 `one` | Small |
| `kl-index` | `∀ n → Σ (Tr (tw n) → L) λ hh → kl (suc n) ≡ nd (sΩ (tw n)) hh` | `kl (suc n)` 的链在 `Tr (tw n)` | Small |
| `Uᶻ-all` | `∀ n → K.readRW (D.Fd (kl n) (okl n) (B₀ (kl n)) (Ωt zero)) ≼ K.readRW (twᶻ (suc n))` | 各站上界一半（标准底） | Small |

**前提可满足的情况。** `Low-at` 的前件有实例：`chain-two` 给出 `M⁰ (γ 1) (chain 2)`，`hω-inv (hc-tower 3) refl 1` 给出 `HC (S (γ 1))`。所以 `FirstMissing` 不是空真。`Tail` 本身有没有实例，是判断：语义上 out e ≈ ψ₀(Ω_{Ω₁+Ω_e})，看起来成立。

#### 4. 第一个障碍

- **在链上：** `FirstMissingˢ`，即 `Tail 0` 的输出一半在第 2 个链点处（`Gᴱ.FirstMissing`）。也就是要证 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) ≼ `out (chain 2)`。
- **在有限 γ 上：** γ = 2，要证 ψ₀(Ω_{Ω_2}) ≼ `out e`。

判断：两者都挡在数学上，不是工程。依据是 `two-shape`（编译）：e ≥ 2 时，输出层号 `a₁ e = tw 1 ⊕ (zero ⊕ ↑ (h₁ e) (Ωt (h₁ e)))` 的 Ω 下标层是 `one` 或更高，其中的回灌链在不可数层上。所以需要一条在前缀 `tw 1 ⊕` 下、目标为 `one` 一类层的下标保持（LowKeep），并把 `↑ zero e` 读回成不低于 γ 的层号（Leaf）。这正是整体引理（读回域上的 Leaf 加 LowKeep）在可数下标读回层号上的实例。它和 YiC0 干净对象未完成的 ψ₀(Ω_{Ω₂}) 里程碑形状相同，只多一个 `tw 1` 前缀（判断）。没有编译的否定，只能写"未走通"。

**一切站（第 3 步，判断）：**
- 上界一半：标准底对一切 n 已编译（`Uᶻ-all`）。继承底的下降路 `p*` 只做了 n = 1，是闭项计算；一般 n 要对 `way`、`emb` 归纳，看来可行，但没有做。
- 下界一半：n ≥ 2 时 `kl n` 的链在 `tw (n-1)`（`kl-index`），不与可数的 γ 链同步。要么继续往下走"链点孩子加下降"若干次，降到下标为第 0 层的层号；要么直接用不可数层上的关系。两条路都落在整体引理上。

#### 5. 偏离与事故

**偏离：**
- 简报说"用 `k1-value` 填 `Kᴱ′ 1`"。`k1-value` 只给 `twᶻ 1`，接不上 `keelᴱ`，所以我用 `row₂-btbo` 那条链填 `Kᴱ′ 1`；`k1-value` 用来填标准底的 `Kᶻ′ 1`，并用在 `sf₁ᴱ` 里。
- 简报设想的 L* 是"`Step 1` 的孩子 c*"。实际被上界的是沿 `p*` 降到同一层号上的另一个底 `Bᴱ`，c* 处的输出没有上界。
- "`station-step` 一类"实际用的是 `FR.Step.branch-upper` 与 `keelᶻ`。

**事故（两次 251，都在 8G）：**
1. **`YiSYFrame` 初版。** 把 `k0` 与 `upperᴱ zero` 在闭指标 0 上复合，两个模块的 `Keel⁻` 副本相遇。二分：scratch `SYa` 163 秒 251。改成变量 n 上的 `stage`（C-9）后 18 秒 0。
2. **`YiSYSmall`。**
   - 初版 251（101 秒）。
   - 第一次改形状（移进变量模块 `Gen`）没有先二分，仍 251（84 秒）。按简报"改过形状后同一上限仍撞墙才停"的字面，这里本应停下回报；我没有停，而是先二分定位，再做第二次针对性改形状。如实记为偏离。
   - 二分前缀：A 0，C 0，D 251，定位到实例的签名混用模块副本的名字（`Low-at (γ 0) Gᴱ.feed`、`K.M⁰ (γ 1) (Gᴱ.chain 2)`）。
   - 改成在 `Gen` 里定义 `SF₁`、`SO₁`、`Two`（C-1），D2 前缀 17.6 秒 0，全文件 0。
   - 两次的 profile 都没有做；定位只靠前缀二分。

**只凭签名或转述引用、没有通读的：**
- `YiKSRead.fs-sup`、`YiKCSem.sem→M⁰`、`YiExInst.back/tree-back`、`YiEXRow.row₂-btbo`、`YiMTValue.btbo-br1ᶻ` 只看了签名。
- `YiC0Accept`、`YiC0Node`、`YiC0Reduce` 只读了文首。
- Bedrock 性能手册原文没有读，只经 `EBOHandbook` §4.6 的对照转述。
- "站的对位松一层"的来源是简报与 `AuditA-plan` 附件，我用 `k1′` 的编译核实了第 1 站的那一半。

临时文件都在 `<实验目录>/work/YiSY/`（scratch 的 `.agda` 与日志）。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：对位调整，把第 3 站改在同步对象上（前缀 YiSY，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。作者 2026-11-16 定：主线停止在具体链点上的逐项攻法（停工，不是否定），改攻一条整体引理；本路是同批四路之一，选项原文 "对位调整：同步对象 L* (Recommended)"。另三路（整体引理、配对否定、摆脱侧）与你互不导入。

#### 背景（事实，已编译，你自己核对）
- 终点归结为站值：`YiS1Accept.Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)`，`ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；`YiGIEnd.row-eq : ∀ n → Keel⁻.row keelᴱ n ≡ E.EBOψ n`（参照：第 1 站 ψ₀(Ω₁)，第 2 站 ψ₀(Ω_Ω)，第 3 站 ψ₀(Ω_{Ω_Ω})）；`YiGIEnd.upperᴱ`、`standard-closed : ∀ n → Keel⁻.twc keelᵍ n ≡ MT.twᶻ n`；`YiFRStations.station-step : ∀ n → K.readRW (Keel⁻.twc keelᴱ n) ≼ K.readRW (Keel⁻.twc keelᴱ (suc n))`；`YiFRStations.k0`、`k1`、`k2`。
- **站的对位松一层**（Fable 审核 A 路发现，主审核对）：`YiPCKeel.k1-value : (h : E.HC (E.EBOψ 2)) → Rt h ≼ readRW (twᶻ 1)`，即第 1 站的闭项已不低于第 2 站的参照；而 `YiFRStations.k2` 的证明是 `row₂-btbo`、`btbo-br1ᶻ`、`rr≼ (brᶻ 1)`、`station-step 1` 的传递，`tw 2` 的折叠没有贡献新值。
- **同步对象**：`L* = tw 1 ⊕ ↑ (tw 1) (proj₁ (Ωt (tw 1)))`。审核 A 路的判定件（主审冷编通过，全文在 `probes/Survey/Reports-2026-11-16/attachments/AuditASync.agda.txt`）：`is-child : L* ≡ FR.Step.child 1 c*`，`shape : L* ≡ nd (sΩ zero) a*`（`a* e = tw 1 ⊕ (zero ⊕ ↑ (zero ⊕ ↑ zero e) (proj₁ (Ωt (zero ⊕ ↑ zero e))))`），`o*`，`row* : Q.collapse (L* , o* , rbᶻ L* , B₀ L*) (Ωt zero) ≡ limc⁺ (λ n → In.out (In.chain n))`，其中内层链在 `Tr zero` 里。判断（A 路，未编译）：`L*` 的 Ω 树折到第 0 层是第 0 层上的对角链，与 ψ₀(Ω_{Ω_Ω}) 的基本列（γ_{m+1} = ψ₀(Ω_{Ω_{γ_m}})，可数）同步；没有继承底，没有不可数层上的回灌链；它的孩子层号对后继 e 仍是含 Ω 结点的形状。
- 已有工具：`YiE4Base`、`YiE4Inner`（`Inner`：`g`、`feed`、`out`、`chain`、`row`）、`YiKCSem.sem→M⁰`、`YiKVRel`（`readRW`、`M⁰`、`lower⁰`、`G⁰` 的累计构造子）。

#### 要做的（按序）
0. **对位的框架**（最小检查）：写出 `Kᴱ′ n = (h : SI.E.HC (E.EBOψ (suc n))) → SI.E.tree h ≼ K.readRW (MT.twᶻ n)` 一类的陈述（先核 `keelᴱ` 与 `keelᵍ` 的闭项差别，选能接上 `upperᴱ` 的那一个），编译 `ebo-from-stations′ : (∀ n → Kᴱ′ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；用 `k1-value` 填 `Kᴱ′ 1`。不成立就停下回报。
1. **把 `Kᴱ′ 2` 归约到同步对象上的一条值引理**：编译 "`L*` 的 Ω 树折到第 0 层的输出不高于 `twᶻ 2`"（经 `Step 1` 的孩子与 `station-step` 一类已有引理），并把 "ψ₀(Ω_{Ω_Ω}) ≼ 该输出" 写成显式前提 `SyncLow`，最好写成对变量的形式（`∀ γ e → K.M⁰ γ e → …ψ₀(Ω_{Ω_γ})… ≼ K.readRW (In.out e)` 一类）。得到条件定理 `SyncLow → Kᴱ′ 2`。
2. **试 `SyncLow` 的小实例**：γ 有限时能否由已有结果（第 2 站一类、`YiC0Accept` 的颈结点办法）给出；挡住就交第一个挡住的引理，说明它与整体引理（读回域上的 Leaf 加 LowKeep）的关系。
3. 说明对位调整对 "一切站" 的推广意味着什么：`Kᴱ′ (suc n)` 是否都能同样归约到 `tw n ⊕ ↑ (tw n) (Ωt (tw n))` 上的同步对象。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 8G（另有三路与主审在编）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
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


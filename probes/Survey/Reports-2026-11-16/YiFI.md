# 对折叠参数化的整体接口（Fable 5.2）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-17 01:56 至 02:14 |
| 工具调用 / agda 编译 (粗数) | 45 / 15 |
| token (usage 字段，按消息去重) | 输出 103437；新写入缓存的输入 261649；读缓存的输入 5840460；其余输入 66 |
| 写过的仓库文件 | `YiFIFold.lagda.md`, `YiFIGen.lagda.md`, `YiFIIface.lagda.md`, `YiFINeg.lagda.md`, `YiFIToy.lagda.md` |
| 文件前缀 | `YiFI` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 5 件全部退出 0，禁用构造 0，四件不读记号的导入闭包干净；对折叠参数化的抽象充分性（keepAll、sys→low）与候选折叠上的条件 LowKeep（lowᴷ，前提只剩出口 Out，其结点一条即 V50）；保留律与回退律两侧的配对否定（kp-not-flr、kp-not-lit、kpᴬ-violates、main-nf、fb-nf）；不比较孩子的保留写法 keepOf（候选 A 是它的特例）；main-¬low 的前提 Gen 在主线块上无实例 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b75/YiFI.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiFI 回报：对折叠参数化的整体接口（律带字面证据），摆脱侧（Fable 5.2）

临时目录（下称 `<W>`）：`<实验目录>/work/YiFI/`，只放编译日志。新建 5 个仓库文件，都在 `probes/OCF/Lean/`，前缀 `YiFI`。没有改任何已有文件。

#### 1. 判决

**对纲领与目标意味着什么。**
- 合并后的那条引理现在是一条编译过的抽象定理，不读记号，对折叠参数化：保留律、回退律加参照一侧的出口，推出 Ω 形状层号上折到低层的保持（`keepAll`、`sys→low`、`lowᴷ`）。
- 它没有证明主线上任何一个新的值。出口 `Out` 在主线关系上没有实填，其中结点一条 `nodeE` 就是台账 V50（参照保留的槽位是否都带字面证据）。本路没有判定 V50，只把它写成了接口的一个字段。
- 树一侧有一条不看孩子下标的保留写法 `keepOf`：给出槽位层号到目标的字面路径 `at ℓ p ≤ j` 就保留。`YiDXFold.flr`（候选 A）是它在路径取 `z≤` 时的特例（`flr-keepOf`，`refl`）。它是 `KeepFn` 的候选，未经作者采纳，不进主线。
- 回退行 (B) 的树一侧律对一切孩子、一切保留判定成立（`fallᴷ`），不比较孩子；这一条覆盖非数字孩子。

**各步到哪一步。**

| 步 | 状态 |
|---|---|
| 0 接口与最小检查 | 完成。主线块与 `Fold K lifted` 填进 `Block`/`Fold`/`Rows`（`foldᴷ`、`rowsᴷ`），连同主线关系填进 `Graded`（`gradedᴷ`）。两条律写成 `KeepLaw`、`FallLaw`。 |
| 1 充分性 | 抽象定理完成（`keepAll`、`sys→low`）；具体折叠接上后是 `lowᴷ`，前提里 `Weak`、`Lim`、`Node`、`Gen⁺` 在主线关系上已填（`YiFIGen`），余下的前提只有 `Out`，未填。没有搬 `YiGTNode.Core.node-at`，抽象的结点一行 `Suff.rules` 里的 `node` 与它同形。 |
| 2 两个实例与配对否定 | 保留律：现行 `kp` 违反，`kpᴬ` 在地板域满足、在字面路径域违反，`kpˢ src` 在来源覆盖的域满足，(C) 的 `kpᶜ` 在 `AuditDCand` 一格走链。回退律：`lifted = true` 满足；现行回退行在底值不含结点时输出不含结点。接口上的否定 `main-¬low` 编译了，但前提 `Gen` 在主线块上没有实例。 |
| 3 清单、翻译账、覆盖范围 | 见下。 |

**律与 `YiAbsGRow` 的行的对应。**
- `KeepLaw.keep` 是 `row-node-keep` 的树一侧前提 `tr`，槽位与换型由字面证据 `Ev` 给出。
- `FallLaw.fall` 是 `row-up` 里 `HandU` 的替代：孩子层不用孩子自己的折叠，用同一个系统在孩子层的状态，目标不变。`Out.upE` 是 `row-up` 的 `bstep`。
- `Out.nodeE` 的第二支是 `row-node-diag`；`limE` 是 `row-lim`；`zeroE` 是 `row-zero` 的结论；后继行同 `YiAbsGRow`，作前提。

**填不进的字段。**
- `Fold.dn`、`Hand`、`HandU` 只描述 "进孩子层用孩子自己的 `ψ`" 的行。Ω 形状层号上经指定孩子的回退行输出是 `ψˡ`（前缀的折叠作状态），所以这一行写成 `Sys` 的状态（`Stᴷ` 的 `rt`、`lf`），不走 `dn`。
- 路径的 `ink` 在 `Block` 里没有对应字段。
- 六条规则的 `Row.Gen`：主线关系 `YiHCRel.Mᴴ` 有第七个构造子 `mc`（参照一侧向下封闭）。本路在接口里加了 `Gen⁺ Le`，对主线关系证了 `Gen⁺ _≤ᵀ_`；六条的 `Gen` 对主线关系成立与否没有判定。

**律的清单。**

| 律 | 定义域 | 字面证据从哪里来 |
|---|---|---|
| `KeepLaw`（抽象） | 系统的每个状态 s 与槽位 p，带 `Ev s p` | 具体实例 `Evᴷ`：K 在搬到本层的槽位 `mv d p` 上返回 `just` |
| `KeepLawᶜ K Lit` | 路径 `u : at ℓ p ≤ j`，且 `psh u` 落在 j 的真槽位上 | 律的前提自带；K 自己拿不到 |
| `KeepLawᶜ K Flr` | `at ℓ p ≡ zero` 且 j 非零 | `z≤ j`，K 可以自己算（`flr`） |
| `KeepLawᶜ (kpˢ src) (Cov src)` | 来源 `src` 在这一格给出路径 | 来源表 `Src`（谁来填没有解决） |
| `FallLaw` | 每个状态、每个孩子 c、每棵 x 与孩子树 y；不出现目标所在的孩子 | 不需要 |
| `Out.nodeE` | `Bdˢ s K` 之下，每个带 `CΩ t κ`、`Nu a p κ` 的槽位 | 第一支要 `Ev s p`；这是 V50 |

**能否覆盖真实链孩子（非数字）。**
- 回退律：能，树一侧已编译（`fallᴷ` 对一切 c）。限制：`Tree` 模块要求表整行缺项（字面的 `λ _ _ → nothing`）。主线表 `rbᶻ` 在孩子为 `zero` 时有条目，那些行进孩子层自己的 `ψ`，不在 `Stᴷ` 里。
- 保留律：只在有字面路径的格上。已编译的非数字格：孩子 c+2 里层号 `h₁ (c+1)` 的槽位对目标 `h₁ (c+2)`（经同一孩子或经孩子 c+3，c 是变量）；ℕ 极限孩子 `lim f a` 第 n 个分量里的槽位对该孩子的层号。这些格上 `kp` 与 `kpᴬ` 都走链，`keepOf` 保留。
- 还缺的（判断，未编译）：
  1. `Out.nodeE` 对关系的 `Node` 规则里 **一切** 分支 c 都要二选一。对与目标孩子没有字面关系的 c，没有路径可给。要只对字面延伸的那一族要求证据，得把关系的结点规则改成共尾子族的形式；这是验收侧关系的改动，对应换基（V149、V158）。
  2. 来源 `Src` 由谁构造。`kpᶜ` 的来源表在 `tw 1` 的孩子里是空的（`cand`）。
  3. 表有条目的行与其余路径形状（`inu`、`ink`、`sS`、`sL`）要并进 `St`。

**翻译账。**
- 来自记号的规则：无。`YiFIIface`、`YiFIFold`、`YiFINeg`、`YiFIToy` 的导入闭包对禁用表命中 0。
- 由树的要求逼出：`keepOf`（路径经 `psh`、`pshBr`、`pshFirst`，都是块里已有的运算）；`Stᴷ` 的两种状态（照 `ψ` 与 `ψˡ` 的参数）。
- 记号出现处：`Out`（接口的出口，抽象参照系统）与验收文件 `YiFIGen`。
- 新增脚手架：`Sys` 的 `Cxt`、`ap`、`Bdˢ` 三个字段是参照一侧的，序数值验收需要，不是翻译带来的。
- 没有加深翻译；也没有带来新的值。

**问题表。**

| 问题 | 位置 | 档 |
|---|---|---|
| `Out` 在主线关系上未实填，`lowᴷ` 是条件定理 | `YiFIFold.lowᴷ` | 编译定理（条件）；前提只在玩具模型里满足 |
| `main-¬low` 的前提 `Gen j` 在主线块上无实例 | `YiFINeg.MainNeg` | 编译定理；前提可满足性只有抽象实例 `YiAbsGToy.drop-¬low` |
| 带 `mc` 时 `Inv.inv` 的论证过不去：`s ≤ᵀ t` 时 s 的余尾 Ω 不传给 t | `YiHCRel.mc` | 判断；要值的上界读法才能补，属已关闭的值否定线 |
| 底值含结点（如默认底 `Ωt j`）时 `main-nf` 不适用 | `YiFINeg.main-nf` | 定理的定义域限制 |
| 是否存在某个 K 在整个 `Lit` 域上满足保留律 | `KeepLawᶜ K Lit` | 未定；没有对 `obs→dec` 一族编译核对，我判断不撞（`Lit` 是带证据的数据，不要求反向） |
| 玩具模型里保留律与 `nodeE` 是空真 | `YiFIToy` | 编译定理；非空的保留律只有树一侧（`keepᴷ`） |

#### 2. 文件表

| 文件 | 代码行 | 冷编退出码 | 峰值驻留 | 读记号 |
|---|---|---|---|---|
| `probes/OCF/Lean/YiFIIface.lagda.md` | 118 | 0 | 0.15G | 否（只导入 `YiAbs*`） |
| `probes/OCF/Lean/YiFIFold.lagda.md` | 119 | 0 | 0.21G | 否 |
| `probes/OCF/Lean/YiFIToy.lagda.md` | 83 | 0 | 0.16G | 否 |
| `probes/OCF/Lean/YiFINeg.lagda.md` | 176 | 0 | 0.18G | 否 |
| `probes/OCF/Lean/YiFIGen.lagda.md` | 82 | 0 | 1.37G | 是（验收文件） |

冷编：删自己的 5 个 `.agdai` 后按依赖顺序逐个编，每份日志只有自己模块的一行 `Checking`。禁用构造与本机路径检索为 0。`importclosure.py`：前四个 OK；`YiFIGen` FAIL，它是验收文件。

#### 3. 定理表

| 名字 | 陈述（逐字或逐字的主干） | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `Suff.keepAll` | `∀ {a} → WfL a → (s : St a) (K : Cxt) → Bdˢ s K → ∀ {t x} → R a t x → Q s K t x`（模块参数：`Weak`、`Lim`、`Node`、`Monoˢ`、`KeepLaw`、`FallLaw`、`Out Le 𝓀 𝒻`、`∀ a → Gen⁺ Le a`） | 两条律加出口，每个状态上保持成立 | `YiFIIface` | 编译定理 |
| `Suff.sys→low` | `WfL ℓ → (s : St ℓ) (K : Cxt) → Bdˢ s K → (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (Kc : Cx ℓ j) → (∀ x → Φ s x ≡ ψ ℓ b j w β x) → (∀ t → ap K t ≡ app Kc t) → ∀ {a x} → R ℓ a x → R j (app Kc a) (ψ ℓ b j w β x)` | 状态对上折叠，就是这一点上的 LowKeep，对该层一切树 | `YiFIIface` | 编译定理 |
| `NoKeep.nokeep→¬` | `∀ {a} (s : St a) (K : Cxt) {t x} → CΩ (ap K t) κ → (H (Φ s x) → ⊥) → Q s K t x → ⊥` | 参照保持余尾 Ω 而像不含结点，保持不成立 | `YiFIIface` | 编译定理 |
| `NoKeep.laws→¬` | 同一前提下，两条律、出口、`Gen⁺`、`R a t x` 不能同时成立 | 配对否定的汇总 | `YiFIIface` | 编译定理 |
| `gen→gen⁺` | `Gen a → Gen⁺ Le a` | 六条生成推出带向下封闭的生成 | `YiFIIface` | 编译定理 |
| `keepOf` | `(ℓ : L) (p : Pos ℓ) {j : L} → at ℓ p ≤ j → Keep j (Br ℓ p) (fromBr ℓ p zero)` | 字面路径给出保留 | `YiFIFold` | 定义候选 |
| `flr-keepOf` | `flr zero f (nd s h) ≡ keep⁼ zero f (psh (z≤ (nd s h)) (inj₁ tt)) (pshBr …) (pshFirst …)` | 候选 A 的地板是路径取 `z≤` 的情形 | `YiFIFold` | 编译定理（`refl`） |
| `Tree.keepᴷ`、`fallᴷ`、`monoᴷ` | `KeepLaw`、`FallLaw`、`Monoˢ` 的居民，对任何 `K : KeepFn`、任何 `Graded`，`lifted = true`，表整行缺项 | 上折回退的系统满足树一侧的律 | `YiFIFold` | 编译定理 |
| `Tree.lowᴷ` | `(Le) → Weak → Lim → Node → Out Le keepᴷ fallᴷ → (∀ a → Gen⁺ Le a) → (β : Tr⁺ j) (K₀ : Cxtᴷ) → Bdᴷ (rt β) K₀ → (Kc : Graded.Cx 𝔾 ℓ j) → (∀ t → apᴷ K₀ t ≡ app Kc t) → ∀ {a x} → Rᵍ ℓ a x → Rᵍ j (app Kc a) (proj₁ (F.ψ ℓ o r B j w β x))` | 候选折叠在 Ω 形状层号、目标经指定孩子时的 LowKeep，条件是出口 | `YiFIFold` | 编译定理（条件） |
| `toy-low` | `(β K : ℕ) → K ≤ β → ∀ {a x} → a ≤ x → K + a ≤ β + x`（由 `sys→low` 得出） | 充分性的前提在两层模型里全部可满足 | `YiFIToy` | 编译定理 |
| `lawˢ` | `(src : Src) → KeepLawᶜ (kpˢ src) (Cov src)` | 带来源的判定在来源覆盖处保留 | `YiFINeg` | 编译定理 |
| `lawᴬ` | `KeepLawᶜ kpᴬ Flr` | 候选 A 在地板域满足 | `YiFINeg` | 编译定理 |
| `kp-drop` | `∀ k h (o : Ok (nd (sΩ k) h)) c t c′ {j} (v : j ≤ h c′) → kp (nd (sΩ k) h) o (inj₂ (c , t)) (inc c′ v) ≡ nothing` | 现行判定在这类格上一律走链（`kp*`、`drop` 的一般形式） | `YiFINeg` | 编译定理（`refl`） |
| `kp-not-flr`、`kp-not-lit` | `KeepLawᶜ kp Flr → ⊥`、`KeepLawᶜ kp Lit → ⊥` | 现行判定违反两个域上的保留律 | `YiFINeg` | 编译定理 |
| `kpᴬ-violates` | `KeepLawᶜ kpᴬ Lit → ⊥` | 候选 A 在字面路径域违反 | `YiFINeg` | 编译定理 |
| `cand` | `(ot : Org (h₁ three) (tw 1)) → IsNothing (kpᶜ (tw 1) (Ok-tw 1) (pvT 1) p₃ w₃ ot)` | 候选 C 在同一格走链（搬自 `AuditDCand`） | `YiFINeg` | 编译定理 |
| `litˢ`、`litˢ′`、`kpᴬ-dropˢ′`、`keepOfˢ`、`litᴸ`、`kp-dropᴸ`、`keepOfᴸ` | 对变量 c 与任意合法基本列 f 的格：`Lit` 有居民，`kp`/`kpᴬ` 是 `nothing`，`keepOf` 是 `just` | 非数字孩子上也有带字面路径的格 | `YiFINeg` | 编译定理 |
| `main-nf` | `NZ c → NZ c′ → (o) (B) (j) (v : j ≤ h₁ c′) (β) (y) (e) → NF (proj₁ β) → NF (proj₁ (ψ (tw 1) o (rbᶻ (tw 1)) B j (inc c′ v) β (up zero c y e)))` | 现行回退行在底值不含结点时输出不含结点（`fall-diag` 的一般形式） | `YiFINeg` | 编译定理 |
| `fb-nf` | 同上，对 `DX.Fold.ψ K false`，任何 K，任何 Ω 形状层号，表缺项 | 同上，对折叠参数化 | `YiFINeg` | 编译定理 |
| `no-node` | `(Ω q G ≡ t) ⊎ Lt S (Ω q G) t → NF t → ⊥` | 不含结点的树不低于任何结点 | `YiFINeg` | 编译定理 |
| `lift-node` | `K (nd (sΩ k) h) o (mv (down stop c) p) (inc c′ v) ≡ just (q , cv , eq) → Σ (Br j q → Tr j) λ G → Ω q G ≡ proj₁ (DX.Fold.ψ K true … (up x c (Ω p g) e))` | 上折回退在 K 保留处输出就是结点 | `YiFINeg` | 编译定理 |
| `MainNeg.main-¬low` | 对任何 `𝔾 : Graded blkᵍ foldᵍ rowsᵍ 𝕋 𝕍`：`NZ c → NZ c′ → … → NF (proj₁ β) → Gen j → (κ) → 三条余尾互斥 → Gb、Wl、Bd、Gx → W.R (tw 1) a (up zero c y e) → W.CΩ (W.app Kc a) κ → W.LowKeep → ⊥` | 现行折叠上，六条生成的关系在这一点的 LowKeep 不成立；否定的是接口，不是值 | `YiFINeg` | 编译定理；前提 `Gen` 在主线块上无实例 |
| `genᴷ` | `∀ ℓ → Gen⁺ _≤ᵀ_ ℓ`（对 `gradedᴷ K lifted`） | 主线关系每层满足带向下封闭的生成原理 | `YiFIGen` | 编译定理 |
| `weakᴷ`、`limᴷ`、`nodeᴷ` | `Weak`、`Lim`、`Node` | 主线关系上这三条成立 | `YiFIGen` | 编译定理 |

#### 4. 第一个障碍

**`Out.nodeE` 在主线关系上的实填，是数学上挡住的。**
- 陈述：`Bdˢ s K` 之下，对每个带 `CΩ t κ`、`Nu a p κ` 的槽位 p 与一切满足 `R (slL a p) η (slT a p c)` 的分支 c，要么有 `Ev s p` 且上下文保持余尾 Ω，要么上下文降到 ω 且有回灌链。
- 第一支要的 `Ev` 在具体实例里是 "K 在该槽位返回保留"；K 只能靠字面路径。参照一侧保持余尾 Ω 与否由 κ 与目标下标的大小定，不由字面路径定。两者是否总一致，就是 V50。
- 第二支的回灌链是 `StepU′`/`ChainAt` 那一类前提，本路没有碰。
- 工程上没有挡住：五个文件峰值 1.4G，没有撞堆。

**第二个障碍（否定侧）**：`main-¬low` 搬不到主线关系上，卡在 `mc`。`Inv.inv` 在 `mc` 一条上需要 "s ≤ᵀ t 且 s 余尾 Ω，则 t 对着的树含结点"，这要值的上界读法。

#### 5. 偏离与事故；没有读、只凭转述引用的东西

**偏离。**
- 简报第 1 步写 "复用 `node-at`（改成对折叠参数化，在新文件里）与 `gen→low`"。我没有搬 `node-at`（它读记号、固定在 `E.ψ ν (t ++ a)` 的上下文上），改在抽象层重写了结点一行；`gen→low` 的做法（对 `Rules` 用生成原理）沿用了，但 `Low` 模块里的 `row-*` 引理固定 `F = ψ`，回退之后的像是 `ψˡ`，所以这几行在 `Suff.rules` 里重写了（各三到五行）。这算在已有理论上加一层，不是重写 `Rules`/`Gen`/`Inv`，三者都直接引用。
- 简报没有要求的两件：玩具模型 `YiFIToy`（为了 "前提要可满足"；`YiAbsGToy` 的孩子层等于本层，不满足 `WfL`）；验收文件 `YiFIGen`。
- 新增了一个定义候选 `keepOf`/`kpˢ`（只在新文件里，未进主线）。

**事故。**
- 接口第一版把参照上下文做成状态的函数（`cx : St a → T → T`），编译通过，但写模型时发现 `upE` 要求上下文对一切满足 `R a t x` 的 t 相同，不可满足。改成上下文 `Cxt` 与状态分开、用 `Bdˢ` 连接（同 `row-up` 的 `bstep`）后重编。回报里的陈述都是改后的。
- 其余是重名一类的编译错误（`Mono`、`Exit`、`R`、`cx`），各一次。
- 第一个文件写出并编译在开工后约半小时，没有量过精确时间。

**没有读、只凭简报或文首转述的。**
- 要避开的八条否定（`no-index-tree-tw1ˣ`、`no-chain-neck`、`no-above`、`no-stepU′-tw1`、`no-tight′`、`YiCompatDl*`、`no-value-index-mono≈`、`no-root-cover`）：陈述都没有读。"律的定义域没有落进它们的前提" 是判断，依据只是本路的律不含跨层单调、不含索引树、每条律至多一个孩子下标。
- 简报列为同一条引理的九个陈述（`Cand`、`TightStep`、`TightDom`、`Branch`、`FirstExact`、`NeckLabChain`、`StepChain`、`GMono`、塔第 1 项上的 LowKeep）：只看了 `Cand` 的签名行，没有逐条核它们是 `Sys` 的哪个实例。"合成一条" 在本路的含义是给出了统一的抽象陈述，不是证明了这九条各自由它推出。
- `YiKFFold`、`YiKFValue`、`YiBS*`、`YiBT*`、`YiXPNeg`、`YiMGFrame`、`YiSYReduce`、`YiAbsObs`、`YiAbsGSuff` 正文：没有读。`YiRQDom`、`YiKTSlot` 只看了签名行。
- `EBOHandbook` 第 4 节与 Bedrock 性能手册：没有读（没有撞堆）。
- `AuditD.md` 读了全文；其中的值估计是该路的判断，本路没有复核。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：对折叠参数化的整体接口（律带字面证据），兼作摆脱侧（前缀 YiFI，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Fable 5.2。本路不读记号（验收文件除外），是这一批的摆脱侧（AGENTS "攀爬与摆脱翻译要平衡"）。同批另两路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- Fable 5.2 的路线审核 D 路（先读定义、封存后再读结论；留档 `probes/Survey/Reports-2026-11-16/AuditD.md`，判定件附件 `attachments/AuditD-*.txt`）与此前的独立审核 YiVA（`Reports-2026-11-16/YiVA.md`）两份封存件独立判断：现行折叠在 "Ω 形状结点下、材料在一个孩子里、目标在另一个孩子下面" 时没有实现 "低于目标保留"（`YiRWFold.kp` 的 `(inj₂ _) (inc _ _) = nothing` 一行与 `YiTBRow.ψ` 的退路行），同步对象上的那一步链步（`YiKTSlot.Cand`）不成立。**作者据此定（选项原文）："按两份审核关闭 (Recommended)"**：现行折叠上 `Cand` 这一格及其值否定线关闭，不再派它的任何变体（它在第七十一到七十四批以 `TightStep 1`、`TightDom`、`Top₁`、`Refute`、`single`、`Branch`、`cand₁` 七个名字出现过；台账 V287）。
- 第七十五批作者选三路（选项原文）："真实链孩子上的最小实例 (Recommended)"、"对折叠参数化的整体接口 (Recommended)"、"候选的两个有限测试"。前缀 `YiRK`（Opus 5.5）、`YiFI`（Fable 5.2）、`YiCT`（Opus 5.5），互不导入。**主线定义不动**；改树、折叠、合法性只在新文件里做候选。
- D 路审核要点（判断，未编译）：决定成败的是台账 V50（读回域上被问到的 "目标孩子 c′、材料孩子 c" 的对，是否都带字面证据）。真实同步对象的链在第 0 层（`YiSYReduce`：层号 `nd (sΩ zero) a`，`chain` 是 `feed` 的迭代），真实链孩子是 `a (chain m)`，`chain m` 是回灌输出，不是数字；第七十二到七十四批的测试都在数字孩子 `a₁ (suc d)` 上。数字孩子是可判定的特例：比较表在 "任一端是数字" 的整列可字面填满（`AuditDFin.colFin`、`col-total`），换表后那一格如实进孩子层朝原目标折（`AuditDRow.honest`；现行表下是 `fallᶻ`）。对一般孩子，任何表都不能让每一支如实，只能指望与目标孩子字面共尾的那一族如实；这是换基（台账 V149、V158）要做的，11-14 选比较表而不选换基的决定要重看（V290）。
- 已编译的机制（主审复核过）：`YiVALeaf.fall-diag`、`leaf-branch`（不读记号）；`YiRQDom.drop`、`fall`、`start-form`、`kp*ᵍ`、`kp₀ᵍ`；`YiUSBound.base-form`、`leaf-node₂`；候选原型 `YiDXFold`（`Fold (K : KeepFn) (lifted : Bool)`，(A) `kpᴬ`，(B) 上折回退 `ψˡ`）、`YiKFKeep`/`YiKFFold`（(C) 来源表 `Pv`、`Org`、`kpʳ`、`kpᶜ`），`YiKFValue`（值定理用标准底 `B₀`，不是 `Cand` 的继承底）；`AuditDCand.cand`（候选在塔第 1 项、目标层 ≥ 2 时对层号非零的槽位仍走链）。换基原型：`YiBSFold`、`YiBSBase`（`split`、`seen`）、`YiBSReadNeg`、`YiBSClean`、`YiBSCrit`（只到数字孩子）、`YiBTZero`、`YiBTOne`。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
D 路审核指出，下列陈述的核心都是 "跨 Ω 形状结点、目标在另一个孩子下面时，折叠保持下界读法"：`Cand`、`TightStep`、`TightDom`、塔第 1 项上的 LowKeep、`YiKFValue.Branch`、`YiNCFirst.FirstExact`、`YiMGNeck.NeckLabChain`、摆脱侧的 `YiCAStep.StepChain` 与 `YiVRRead.GMono`（V120、V281）。按 AGENTS "同类引理以不同名字第二次出现时, 合并成一条并写进接口"，把它合成一条，写成对折叠参数化的接口。

**不要重写已有的抽象理论**，在它上面做（先读各文首）：
- `YiAbsGIface`（V145：`Rows`、`Ref`、`Graded`、`Doms`；律 "不比较两个指定孩子"）、`YiAbsGSuff`（`Leaf`、`Lift`、`LowKeep`、`Base` ⇒ 塔每一项与终点）、`YiAbsGRow`（`gen→low`：关系由六条规则生成时，折到低层的保持归约到行的封闭；`row-node-keep`、`row-node-diag`、`row-up`、`row-self-up`）、`YiAbsGNeg`（`cap→¬low`；`unkept→¬low`：槽位不保留则 LowKeep 在这一点不成立，不经过值）、`YiAbsGFin`（有限层号的实例，`LowKeep` 未填）、`YiAbsFrame`（`Hand`、`HandU`；`hand→wdec`、`branch→wdec`）、`YiAbsObs`（`obs→dec` 一族）。
- 折叠参数化已有形状：`YiDXFold.Fold (K : KeepFn) (lifted : Bool)`；`YiKFFold` 多带来源表。
- 现行折叠上的结点引理：`YiGTNode.Core.node-at`（对任意保留结果，但折叠固定为旧的）；读回域 `YiGLDom.Dom`、`dom-top`；LowKeep `YiXPExact.lowKeepAt-noΩ`、`YiMGFrame.lowKeepAtᵐ-noΩ`。
- 要避开的否定（律的定义域不能落进它们的前提）：`YiXPNeg.no-index-tree-tw1ˣ`、`YiMGNeck.no-chain-neck`、`YiKTSlot.no-above`、`YiTFTw1.no-stepU′-tw1`、`YiTFTight.no-tight′`、`YiCompatDl*`（跨层单调接口）、`YiVNIdx.Gen.no-value-index-mono≈`、`YiCVDomain.no-root-cover`。
- AGENTS "律带公共上界, 构造与否定配对"、"量化域先取带证据的读回域"：律里出现的每一对下标都要带字面公共上界的证据；量化域先取规范读回域。

#### 要做的（按序）
0. **接口与最小检查**：把主线块与 `YiDXFold.Fold K lifted` 填进 `YiAbsGIface` 的 `Block`/`Fold`/`Rows`（只要能填的部分；填不进的地方写清是哪个字段、为什么）。写出保留判定 K 与回退行各一条律（带字面证据：例如 "槽位层号 b 与目标 j 之间有字面路径证据就保留"；"回退行把孩子上的材料朝原目标折"），说明它们对应 `YiAbsGRow` 的哪一行（`row-node-keep`、`row-up` 等）。在临时文件里先编译类型。不成立就停下回报。
1. **充分性**：证 "K 与回退行满足这两条律 ⇒ 读回域上 Ω 形状层号的 LowKeep"（至少塔第 1 项为前缀的那一类层号），复用 `node-at`（改成对折叠参数化，在新文件里）与 `gen→low`。
2. **两个实例与配对否定**：现行折叠违反哪条律（编译否定；预计是 `fall-diag` 与 `kp*` 的一般形式，可经 `unkept→¬low` 得到 "LowKeep 在这一点不成立"，注明否定的是接口上的 LowKeep 而不是值）；候选 (A)+(B)、(C) 满足不满足（已知 `AuditDCand.cand` 一格不满足）。
3. 交律的清单（哪条律、定义域、字面证据从哪里来）与翻译账；说明这条接口能否覆盖真实链孩子（非数字）的情形，或还缺什么。

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


# (3) 抽象理论：按层号分级的模拟接口 (YiAbsG)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 04:05 至 04:29 |
| 工具调用 / agda 编译 (粗数) | 48 / 15 |
| token (usage 字段，按消息去重) | 输出 126576；新写入缓存的输入 228213；读缓存的输入 6331020；其余输入 76 |
| 写过的仓库文件 | `YiAbsGEbo.lagda.md`, `YiAbsGFin.lagda.md`, `YiAbsGFinInv.lagda.md`, `YiAbsGIface.lagda.md`, `YiAbsGNeg.lagda.md`, `YiAbsGRow.lagda.md`, `YiAbsGSuff.lagda.md`, `YiAbsGToy.lagda.md` |
| 文件前缀 | `YiAbsG` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: (3) 分级模拟接口返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 抽象部分无前提: 接口 GSim (十五条律, 量化域作参数), 充分性 (满足 Leaf, Lift, LowKeep, Base 四项 ⇒ 一切 K(n) ⇒ 终点下界; EBO 实例 ebo-end), 玩具模型满足全部律, 配对否定 (值封顶与 '槽位不保留' 各与 LowKeep 不相容, 前提可满足); 部分实例: 合法块有限层号满足十条律; LowKeep 与 Lift 在具体块上未填; 判断: 接口是充分条件不是必要条件; 八件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的话与选择（2026-11-14，原话）
- 作者问："'卡在同一条未证引理上：层号读自任意可数树时，记号关系该怎样写，以及折叠对它的两条保持性' 之前都没发现需要这个吗? 之前我让你评估抽象理论, 就是想尽可能网罗这种关于'怎样的定义是好的'这种定理级判断标准. 这个没法提前专项分析出来? 只能具体地探索到那一步才能明了吗?"
- 作者更早提出抽象理论时的原话："基于Agda的归纳/ 归纳归纳/归纳递归类型本身的规则, 基于我们目前发现的各种关键(虽然可能不都是必要,也不知道哪些合起来是充分的)性质(如嵌入一致, 单调与保持合法等等), 直接建立抽象理论, 分析最终的形态可能的充分必要条件, 做成定理, 以此指导树的定义"
- 作者的选择（选项原文）："现在加派（Fable 5.2） (Recommended)"。
- 选项说明原文："把 YiAbsSim 的第 0 层模拟推广成分级接口（各层关系、层号读法、折到自身 / 折到低层 / 上折与嵌入的律）；证充分性（满足接口 ⇒ 一切 K(n) ⇒ 终点 ≥ EBO）；把 YiAN 的有限层号族填成实例；配对否定：哪种行形状违反哪条律"。
- 作者的另一条看法（原话）："我不认为树对'龙骨' 形态 Ω，Ω_Ω，Ω_{Ω_Ω}... 的反映是翻译加深的标志. Ω下标层级这种大的结构应该是任何良好定义的序数，不管是记号还是树，都理应具有的自然形态"。

同批在跑两路：YiCL 在具体块上证这条引理；第十七次审查判断它成不成立。你不动它们的文件，也不必读。

###### 已有的抽象理论（编译定理，`probes/OCF/Lean/` 下）
- `YiAbsObs`：`obs→dec`、`obs→wdec`、`sep→wdec`、`rowE-same`、`viaE→dec`、`full→dec`、`sig→lpo`。
- `YiAbsFrame`：
  - 记录 `Block`（层号、各层的树、孩子下标与孩子层、目标路径、嵌入、头部观察、第一位置序、合法）与 `Fold`（带底的折叠 ψ 与孩子的底 dn）；
  - 律 `Hand`、`HandU`、`Mono`、`Pres`；
  - 定理 `hand→wdec`、`branch→wdec`、`rowOf`。
- `YiAbsAdd`：`add-model` 说明只由这四条律推不出超过加法的值。文首原话："值的下界要用到结点行的链与自身行这两类行律"。
- `YiAbsSim`：
  - `Val`；`Exit`（`exit`：对基本列封闭的一族给出下界）；
  - `Sim.lower`：第 0 层的对应 R 加两种步给出下界；`FromMono`；`Fin`。
  - 实填只在第 0 层（`YiMEBase` 文首："`Sim` 的实填取 ψ 为恒等，源层就是第 0 层的树"）。
- `YiAbsSimInst`：EBO 参照是 `Exit` 的参照系统。
- `YiAbsInst`、`YiAbsLeg`：具体块填进框架。
- `YiKidCrit`（冻结）：判据 `KidMono`，量化域是参数。

###### 具体侧已编译、可作实例或反例的（回报在 `probes/Survey/Reports-2026-11-12/`）
- **有限层号的分级关系**（实质上是分级模拟在 `fin n` 上的实例，但是在具体块上做的）：
  - `YiANFam`（关系族 `M zero = M⁰`、`M (suc n) = Mᴰ …`；`Pu` 上折保持；`Self.PF` 折到自身带前缀；`Self.sγ` 回灌链）；
  - `YiANKp`（`kpDrop`、`kpKeep`）；`YiANLv`（`th`：`tcUp`、`tcLim`、`tcLimc`、`tcNode`、`tcLeaf`、`tcMain`；`Anchor.anchor`）；
  - `YiANReach.reachG`。回报 `YiAN.md`。
- **第 0、1 层的记号直连关系**：`YiMEBase`（`Mᴰ`、`M⁰`、`lower⁰`）、`YiMEAnchor`（`At`：`PF`、`QH`、`VW`）、`YiMWPre`（`sem→M⁰`、`Pre`）。
- **龙骨**：
  - `YiKSDesc.keel`（树侧一半）；
  - `YiKSRead`（层号读法 `Rd` 的四条规则：零、后继、ℕ 极限、Ω 形状；`Q₀`、`kl→K`）；
  - `YiKDKeel`（龙骨塔 `rb`、`Ok-rb`、`keel-chain`）；
  - `YiKDStep`（`Fam`、`Famᴵ`、`end-fam`、`Blk`）。
- **终点**：`YiRefTw2.endpoint`（终点 ≥ EBO 归约到对一切行）；`YiCFMono`（`mono<ⁿ`、`below-rowⁿ`）。
- **反例形状**（判断或编译的形状）：
  - 主线分支侧一行（`YiRWFold` 第 94 至 95 行）：第 1 层底的分支是 Ω₁ + 可数；第十六次审查判断它掉值。
  - 空白页 `YiKB*`：上确界结点缺 "孩子位置上的全值分支"，`restart` 是编译的诊断。
- **已编译的边界**：壁垒（`probes/OCF/Barrier.lagda.md`）；`YiCompatDlLPO` 一族（跨层单调派发前提含塔的两项推出 LPO）；`top-branch→lpo`。

###### 要做
1. **分级模拟接口**（抽象文件，只导入标准库与 `YiAbs*`）：在 `YiAbsFrame` 的 `Block`/`Fold` 与 `YiAbsSim` 的参照系统之上，写记录：
   - 层号读法（层号到参照下标）；
   - 每层的关系 Rℓ（参照项 × 该层的树）；
   - 律，至少：折到自身的保持（带前缀）、折到低层的保持、上折与嵌入的保持、结点行与回灌链的律、读法沿零 / 后继 / ℕ 极限 / Ω 形状的四条；
   - 量化域作参数（照 `YiKidCrit` 的写法）。
2. **充分性定理**：满足接口的块，对塔的每一项有龙骨对应，并由 `exit`/`endpoint` 一类的出口得终点下界。形式由你定；先给对抽象参照系统的版本，再给 EBO 参照的实例。
3. **前提要可满足**：给一个满足接口全部律的模型（照 `YiAbsAdd.add-model` 的做法，可以是玩具），或者说明为什么可满足；同时检查律本身不触发 `obs→dec`/`hand→wdec`/壁垒一族，即接口的律不能要求比较两个指定孩子。
4. **实例**：把 `YiAN*` 的有限层号族、`YiMEBase` 的第 0、1 层关系，填成接口在相应层号范围上的（部分）实例；至少一个。
5. **配对否定**：哪种行形状违反哪条律，写成抽象定理。例如 "分支侧对孩子层的底若只是 '本层 Ω 树 + 可数偏移'，则折到低层的律在 Ω 形状层号上不成立"；"上确界结点若无孩子位置上的全值分支，则……"。至少一条。
6. **判断**（回报里写，不进文件）：这一接口是否也是必要条件（任何记号下界的证明都要经过它），还是只是充分条件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiAbsG`（模块名 `OCF.Lean.YiAbsG…`）。不改任何已有文件，不碰 `src/`、`archive/`。
  - 抽象文件只导入标准库与 `YiAbs*`（`importclosure.py` 检查）。
  - 实例与验收文件可以导入具体块与记号，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。不用 `agda --interaction`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/absg`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0；抽象文件 `importclosure.py` 只含标准库与 `YiAbs*`。

###### 回报格式（只在回报里交一次）
1. 判决：接口、充分性、可满足性、实例、配对否定各到哪一步；对纲领与目标的意义（尤其 "怎样的定义是好的" 的判据）；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存、importclosure。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 接口的律逐条：每条律在主线、候选 A、龙骨原型、空白页样本上是成立（编译）、不成立（编译的否定）、还是未知（判断）。
5. 必要性的判断与第一个障碍。
6. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-14 04:12 (UTC)：

主审转告：第十七次独立审查（Fable 5.2）已回来。下面只是数据，可作为你配对否定的候选形状；你的目标与简报不变。

审查者的判断（纸面，未编译；形状有 `refl` 试验）：
- 候选 A 与龙骨原型共有一行：`kpA a oa kk v (ab q f) (inj₁ _) = nothing`，即地板之上、目标之内的源层槽位不保留（缺口 D2）。
  - 它经两处进入：`kp` 的 Ω 形状行，以及 φ 的结点行。
  - `cut (ab q f) self = inj₂ tt` 把嵌入送进 φ。
  - 后果：目标在第 ≥ 2 层、经地板 κ 0 = `tw 1` 的折叠里，只有 `Tr zero` 上的 Ω 结点。龙骨原型的 `Fam 1` / `Blk`（z ≥ 2）因此不成立，并逐层累积。
- 目标只到第 1 层时（候选 A 的 `A1S`），没有 "地板之上、目标之下" 的槽位，判断成立。
- 对照：主线分支侧一行（`YiRWFold` 第 94 至 95 行，第十六次审查）是另一种形状。

所以，"地板之上、目标之下的槽位不保留 ⇒ 折到低层的律在目标第 ≥ 2 层的 Ω 形状层号上不成立" 可能是一条配对否定的候选。审查者还提了一个设计方向（猜测，未试）："让被折进第 z 层的树所在的层号以目标层为字面地板"。

## 回报原文

### 回报: 分级模拟接口 (YiAbsG*)

八个新文件全部冷编退出码 0。抽象部分 (接口、充分性、行律、否定、玩具模型) 是无前提的编译定理；具体侧只填成了部分实例，`LowKeep` (折到低层的保持) 没有在任何具体块上实填。

#### 1. 判决

| 项 | 到哪一步 | 档 |
|---|---|---|
| 接口 | `Ref`、`Rows`、`Graded`、`Doms`、十五条律汇总成 `GSim`，另有 `Base`、`Keel`；量化域是参数 | 编译 (记录与陈述) |
| 充分性 | `keel`、`keelᴿ`、`K`、`endpoint` 对任意块与参照成立；EBO 参照的实例 `ebo-end` | 编译定理，无前提 |
| 可满足性 | 玩具模型满足十五条律、`Base`、`Keel` 与每层 `Gen`；模型里余尾 ω 与 Ω 为空，`Lim`、`Node`、`RdL`、`RdΩ` 是空真 | 编译定理 |
| 实例 | 合法块 (`YiLegBlock`) 限制到有限层号，关系取 `YiANFam.M`：十条律加 `Base` 与 `Gen`，结点与 Ω 余尾非空；不是 `GSim` 的实例 | 编译定理，部分 |
| 配对否定 | 值封顶一族与 "槽位不保留"，各带前提可满足的实例；后者另在 `M` 上陈述 | 编译定理 |

**对纲领与目标的意义** ("怎样的定义是好的" 的判据)：

- **充分性只用四项**：`Leaf` (Ω 树对着 Ω_ν)、`Lift` (树读成层号)、`LowKeep`、`Base` (第 0 层)。其余十一条律是导出这四项的行律。
- **`Lift` 是塔归纳里唯一把层号读法接回关系的一步**。`keel` 的归纳步就是 `tw-step n (li (gl n) (lf (keel n)))`。"层号读自任意可数树时关系怎样写" 对应的就是这条律。
- **判断**：这一项可以不碰具体块、只从塔的归纳形状分析出来。依据是上面的定理结构，不是对历史的复核。
- **读法四条不够，要六条** (`gen→lift`)：另需 "嵌入读成和" (`lU`) 与 "沿第一位置序放宽" (`lw`)。第 0 层没有孩子，所以 `YiKSRead.rd↑` 四条就够；有嵌入的层号起要第五条。
- **结点读成 Ω 形状层号有两个条件** (`node-read`)：分支下标取遍槽位层的一切树 (`slT` 有截面)；槽位允许的余尾下标不高于槽位层。
- **保持按行验收** (`YiAbsGRow`)：每条规则对应 "参照一侧一条等式 + 树一侧一条不等式"。
- **嵌入行只在一致目标 (`HandU`) 下有一步定理** (`row-up`)，另需 "底沿嵌入交接" `bstep`：孩子的底对着带前缀的上下文。
- **律不比较两个指定孩子**：每条律至多出现一个孩子下标，没有 `hd` 与 `Off`。玩具模型的孩子下标取 `ℕ → Bool`，全部律仍成立。这只说明律在该模型里不要求孩子判等，不是一般的元定理。

**问题**：

| 问题 | 位置 | 档 |
|---|---|---|
| `LowKeep` 在具体块上没有实例：`YiANLv` 的结论是带上下文、对一切槽位同时成立的遗传形式 (`TC`/`Cl`)，没有化成本接口单目标的形状 | `YiAbsGFin` (`Bd` 取空) | 事实 |
| 结点对角行要 "回灌进槽位层" 的另一个目标上的保持，`row-node-diag` 把链当前提；接口可能要改成对一族目标的合取 | `YiAbsGRow` | 判断 |
| 后继行没有分解，直接作规则前提 | `YiAbsGRow` | 事实 |
| 值封顶否定的前提 (某行的值有上界 U) 在主线分支侧一行与空白页样本上未编译 | `YiAbsGNeg.Cap` | 判断 |
| `Keel` 的塔步取 "本项 Ω 树读成层号"，只凭 `YiKDKeel` 文首的 `rb` 写成；主线 `tw` 与龙骨塔都没有实填 | `YiAbsGIface.Keel` | 事实 |
| `ebo-end` 以第 0 行 ψ₀(1) 的界作前提 | `YiAbsGEbo` | 事实 |
| `Lift` 与读法四条在具体块上没有实例 (`Rd` 只取字面 `natT n`) | `YiAbsGFin` | 事实 |

#### 2. 文件表

目录 `<仓库>/probes/OCF/Lean/`。删自己的接口后冷编，日志里各只有自己模块一行 `Checking`。禁用构造与本机路径检索为 0。

| 文件 | 代码行 | 冷编 | 内存 | importclosure |
|---|---|---|---|---|
| `YiAbsGIface.lagda.md` | 146 | 0 | 299 MiB | 0；只含 `YiAbsFrame`、`YiAbsObs`、`YiAbsSim` |
| `YiAbsGSuff.lagda.md` | 45 | 0 | 257 MiB | 0；同上加 `YiAbsGIface` |
| `YiAbsGRow.lagda.md` | 121 | 0 | 255 MiB | 0；同上 |
| `YiAbsGNeg.lagda.md` | 55 | 0 | 300 MiB | 0；加 `YiAbsGSuff`、`YiAbsGRow` |
| `YiAbsGToy.lagda.md` | 187 | 0 | 258 MiB | 0；只含 `YiAbs*` |
| `YiAbsGEbo.lagda.md` (验收，读记号) | 38 | 0 | 1136 MiB | 未跑 |
| `YiAbsGFin.lagda.md` (验收，读记号与合法块) | 134 | 0 | 1195 MiB | 未跑 |
| `YiAbsGFinInv.lagda.md` (验收) | 45 | 0 | 1162 MiB | 未跑 |

importclosure 用的是 `--only OCF.Lean.YiAbs`；内存是 `+RTS -s` 的 total memory in use。

#### 3. 定理表

| 名字 | 陈述 (逐字) | 白话 | 文件 |
|---|---|---|---|
| `base-lower` | `(𝔟 : Base) → ∀ {t x} → R ℓ₀ t x → Base.G₀ 𝔟 x → (h : HC t) → tree h ≼ v x` | 第 0 层的对应给出值下界 | Suff |
| `low-lower` | `LowKeep → (𝔟 : Base) → ∀ {ℓ} (b : Bs ℓ) (w : ℓ₀ ⊑ ℓ) (β : Bt ℓ₀) (K : Cx ℓ ℓ₀) → Gb ℓ b → Wl w → Bd b w β K → ∀ {a x} → Gx ℓ x → R ℓ a x → Base.G₀ 𝔟 (ψ ℓ b ℓ₀ w β x) → (h : HC (app K a)) → tree h ≼ v (ψ ℓ b ℓ₀ w β x)` | 高层的对应给出折叠值下界 | Suff |
| `Tower.keel` | `∀ n → Rd (tw n) (kt n)` (模块参数 `Leaf`、`Lift`、`Keel`) | 塔每项的层号读作龙骨下标 | Suff |
| `Tower.keelᴿ` | `∀ n → R (tw n) (Ωr (kt n)) (Ωt (tw n))` | 塔每项的 Ω 树对着 Ω_{kt n} | Suff |
| `Tower.K` | `LowKeep → ∀ n (h : HC (row n)) → tree h ≼ v (twc n)` | 一切 K(n) | Suff |
| `Tower.endpoint` | `LowKeep → (Y : V) → (∀ n → v (twc n) ≼ Y) → (hs : ∀ n → HC (row n)) → vl (λ n → tree (hs n)) ≼ Y` | 终点不低于各行参照的上确界 | Suff |
| `Chain.chain` | `R ℓ (cl ℓ P) (bt β) → R ℓ g₀ (z 0) → ∀ k → R ℓ (γ k) (z k)` (参数 `SelfKeep`、`Weak`、`zs : ∀ k → ψ ℓ b ℓ self β (z k) ◃ z (suc k)`) | 回灌链由折到自身的保持导出 | Suff |
| `Low.gen→low` | `Gen ℓ → Rules ℓ Q → ∀ {a x} → R ℓ a x → R j (app K a) (ψ ℓ b j w β x)` | 关系由六条规则生成时，保持归约到折叠像封闭 | Row |
| `row-zero`、`row-weak`、`row-lim`、`row-node-keep`、`row-node-diag` | 见文件 | 各行一步的充分条件 | Row |
| `UpRow.row-up` | `HandU ℓ → (bstep …) → (孩子层同一保持) → (c : Ch ℓ) {t s : T} {x : Tr ℓ} (y : ChT ℓ c) → R ℓ t x → Q t x → R (chL ℓ c) s (chT ℓ c y) → Q (t ⊕ s) (up x c y)` | 嵌入行经一致目标的交接与底的交接 | Row |
| `SelfRow.row-self-up` | `UpKeep → … → Qs t x → R (chL ℓ c) s (chT ℓ c y) → Qs (t ⊕ s) (up x c y)` | 折到自身的嵌入行经上折 | Row |
| `LiftRow.gen→lift` | `Gen k → Rd0 → RdS → RdL → (ls) → (lΩ) → (lU) → (lw) → ∀ {s x} → R k s x → Rd (lift k x) s` | 读法对六条规则封闭就有 `Lift` | Row |
| `LiftRow.node-read` | `RdΩ → (p : Sl k) (un : Tr (slL k p) → SlT k p) → (∀ c′ → slT k p (un c′) ≡ c′) → (∀ {κ} → Nu k p κ → Rd (slL k p) κ) → …` | 结点读成 Ω 形状层号要分支取遍槽位层 | Row |
| `Cap.cap→¬low` | `… → (h : HC (app K a)) (U : V) → v (ψ ℓ b ℓ₀ w β x) ≼ U → vs U ≼ tree h → LowKeep → ⊥` (前提 `irr : ∀ {a} → vs a ≼ a → ⊥`) | 输出值封顶而参照行更高，则 `LowKeep` 不成立 | Neg |
| `Cap.branch-cap→¬` | `… → Emb → LowKeep → ⊥` | 分支侧一行掉值，`Emb` 与 `LowKeep` 不相容 | Neg |
| `Cap.node-cap→¬` | `… → Node → LowKeep → ⊥` | 结点一行掉值，`Node` 与 `LowKeep` 不相容 | Neg |
| `Inv.inv` | `∀ {s o} → R j s o → CΩ s κ → H o` (参数 `Gen j`、余尾互斥、H 的三条封闭) | 余尾 Ω 的项只能对着含结点的树 | Neg |
| `Inv.unkept→¬low` | `… → ∀ {a x} → Gx ℓ x → R ℓ a x → CΩ (app K a) κ → (H (ψ ℓ b j w β x) → ⊥) → LowKeep → ⊥` | 参照保留余尾而输出不含结点，`LowKeep` 不成立，不经过值 | Neg |
| `Good.gsim`、`keel`、`toy-K`、`toy-end` | `toy-end : (Y : V) → (∀ n → val (suc n) ≼ Y) → vl (λ n → tree (hc (row n))) ≼ Y` | 玩具模型满足全部律 | Toy |
| `Bad.bad-¬low`、`Drop.drop-¬low` | `LowKeep → ⊥` | 两条否定的前提各自可满足 | Toy |
| `ebo-end` | `(Y : V) → toL (ET.tree (ET.hc-tower zero)) ≼ Y → (∀ n → v (twc n) ≼ Y) → toL ET.EBO-tree′ ≼ Y` (参数 `Leaf`、`Lift`、`LowKeep`、`Keel`、`κ₀ ≡ natT 1`、`app (K₀ n) a ≡ ψ [] a ∷ []`) | 满足四项的块终点 ≥ EBO 参照 | Ebo |
| `zeroᶠ`、`succᶠ`、`limᶠ`、`weakᶠ`、`nodeᶠ`、`embᶠ`、`selfᶠ`、`upᶠ`、`leafᶠ`、`baseᶠ`、`genᶠ` | 接口各律在 `gradedᶠ` 上 | `YiANFam`/`YiMEBase` 的结论填进接口 | Fin |
| `invᶠ` | `∀ n {s o} → M n s o → cof s ≡ cΩ κ → Hᶠ n o` | 余尾 Ω 的记号项只对着含 Ω 结点的树 | FinInv |
| `no-node→¬M` | `∀ n {s o} → (Hᶠ n o → ⊥) → cof s ≡ cΩ κ → M n s o → ⊥` | 不含结点的树与余尾 Ω 的项没有 `M` 关系 | FinInv |

全部是编译定理；`Bad`、`Drop` 是前提可满足的实例。

#### 4. 接口的律逐条

我没有在主线 (`YiRW*`)、候选 A、龙骨原型、空白页的块上实填任何一条，这四列全部是未知。编译过的只有玩具模型与合法块有限层号两列。

| 律 | 玩具 | 合法块有限层号 (`YiAN`) | 主线 / 候选 A / 龙骨原型 / 空白页 |
|---|---|---|---|
| `Zero`、`Succ`、`Lim`、`Weak` | 成立 (`Lim` 空真) | 成立 | 未知 |
| `Node` | 空真 | 成立 (`mΩ`) | 未知；空白页上确界结点缺全值分支的说法只凭转述 |
| `Emb` | 成立 | 成立 (`mU`) | 未知 |
| `SelfKeep` | 成立 | 成立，后继层号 (`PF`) | 未知 |
| `UpKeep` | 成立 | 成立 (`Pu`) | 未知 |
| `LowKeep` | 成立 | 未填 | 未知。主线分支侧一行对应 `row-up` 的 `bstep` 或 `branch-cap→¬` 的前提 (判断，第十六次审查)；候选 A 与龙骨原型的 "地板之上、目标之下槽位不保留" 对应 `unkept→¬low` 的形状 (判断，第十七次审查；`no-node→¬M` 只在合法块的 `M` 上编译) |
| `Rd0`、`RdS`、`RdL`、`RdΩ` | 成立 (后两条空真) | 未填 | 主线 `YiKSRead.Rd` 以这四条为构造子，但那里的 `Rd` 没有填进本接口 |
| `Leaf` | 成立 | 成立 (`Mβ`，第 0 层 `pos⁰`) | 未知 |
| `Lift` | 成立 | 未填 | 未知；主线第 0 层有 `rd↑` |
| `Base` | 成立 | 成立 (`r1⁰`、`rω⁰`) | 未知 |
| `Gen` | 成立 | 成立 (`Mᴰ` 的归纳) | 未知 |

#### 5. 必要性的判断

判断：接口只是充分条件，不是必要条件。

- **`Gen` 不必要。** `K 1` 在主线上是经值的比较得到的 (`row₂-btbo`、`btbo-tw1ᴿ`)，没有经过生成的关系。`Inv` 一族否定只对生成的关系成立。
- **弱形式的四项近于必要，但没有内容。** 取 R 为 "对一切对着上下文的底，折到第 0 层的值不低于参照" 这个最大关系，`LowKeep` 按定义成立，K(n) 就等价于塔上的 `Leaf`。负担全部移到引入规则 (`Node`、`Emb`、`Leaf`) 上，这正是 `YiANLv` 的 `TC`/`Cl` 形状。未编译。
- **第一个障碍：** 第 0 层以上没有独立于折叠的值语义，"第 ℓ 层的树不低于参照项" 在折叠之前说不出来。必要性定理因此无法对 "任何下界证明" 陈述，只能对某个选定的 R。第 0 层则不同，典范一族对基本列封闭 (`YiRefTw2.closed-PH`)，`Exit` 的形式在那里是必要的。

#### 6. 偏离与事故

- **中途消息：** 主审转告第十七次审查的数据后，我把 "槽位不保留" 写成 `Inv.unkept→¬low`，并加了 `YiAbsGFinInv`。它没有 "目标第 ≥ 2 层" 这一限定，也不在候选 A 或龙骨原型的块上。
- **事故：** `YiAbsGEbo` 第一版编译超过 2 分钟未结束。我用 TaskStop 停了自己的后台任务。原因是判断：模式 λ 里字面 `0` 与 `zero` 使检查器去规约 `hc-tower` 的闭项。改成对任意 `hs` 的 `ebo-row` 后数秒通过。
- **多出简报的文件：** `YiAbsGFinInv` (否定在 `M` 上的陈述)。
- **改自己文件的方式：** 对自己前缀的新文件用过 `sed -i` 与一次 python 重写。没有改任何已有文件，没有提交。
- **没有读、只凭转述或文首引用的：** `YiKB*`、`YiRWFold` 第 94 至 95 行、`YiCompatDlLPO`、`top-branch→lpo`、`YiKSDesc`、`YiKDFold`、`YiMEAnchor`、`YiMWPre`、`YiANKp`、`YiCFMono`、`Reports-2026-11-12/`、壁垒文件；`YiKDKeel`、`YiKDStep`、`YiRefTw2`、`YiANLv`、`YiANReach` 只读了文首与检索到的签名。
- **与简报的差别：** `KidMono` 没有接进接口；`Hand`/`HandU` 只在 `row-up` 里用到 `HandU`。

临时目录 (日志)：`<实验目录>/agents/absg`

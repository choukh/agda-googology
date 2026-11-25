# 摆脱侧：阶段无关的前驱闭包域族 (YiPF)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十九批；外部模型，作者转发 |
| 前缀 | `YiPF` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：摆脱侧：阶段无关的前驱闭包域族（前缀 YiPF）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十九批四路之一（选项原文 "摆脱侧：阶段无关的前驱闭包域族 (Recommended)"），与在跑的 YiXV、YiFM、YiLL、YiMX 在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- **再上一批**（主审复核过）：`YiLKSlot.steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ`（`YiLKIface`、`YiLKFold`、`YiLKSlot`；回报 `probes/Survey/Reports-2026-11-12/YiLK.md`）：折向第 0 层的各行对一切层号证完，剩每层一条槽位回灌的步进 `StepU`。第一档交付（合法闭项、内部 View、FGH）已在新主线上编译（`YiVW*`）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- 作者 2026-11-14："“记作以后 \"摆脱翻译\" 那一侧的候选” 这个务必落实"。AGENTS "量化域先取带证据的读回域"、"攀爬与摆脱翻译要平衡"（1:1）。本路是本批的摆脱侧。
- **上一路（YiPC）**，回报 `probes/Survey/Reports-2026-11-12/YiPC.md`：`YiPCDom.Pre x = Σ ℕ λ k → x ⊴ idx k`（塔第 1 项那一层实际回灌链各项的第一位置前驱的自反闭包，不读记号；`idx-in`、`below`、`suc-inv`、`lim-inv`、`least`）；`YiPCLift`：`StepSᴾ`、`lift-redᴾ`；`YiPCKeel.k1ᴾ : Lift₁ᴾ → M⁰ (E.EBOψ 2) (twᶻ 1)`（塔第 1 项只需域内的 `Lift₁`）；`not-Canon-cover`。只做了塔第 1 项那一层，没有阶段无关的域族。
- **要收窄的陈述**：`YiLKIface.StepU`（任意底、任意分支函数 g、任意前缀），以及 `YiLKIface.PresU`（任意输入树）。`YiLKSlot.steps→lowKeep : Leaf → (∀ ℓ → StepU ℓ) → LowKeep`。并行的 YiSU 在查 `StepU` 全域是否可满足。
- **终点实际要的**：`domsᵍ`（`YiGIInst` 第 46–49 行）里 `Gx = λ ℓ x → x ≡ proj₁ (O.Ωt ℓ)`，即 `eboᵍ` 的 `LowKeep` 只对每层的 Ω 树要求；但证明它时，折叠会经过 Ω 树的子树、回灌链的各项及其前驱。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：不读记号地写出对一切层号的域族 `D ℓ : Tr ℓ → Set`，例如 "从 `Ωt ℓ` 出发，对子树、回灌输出（`YiLKIface.feed`）与第一位置前驱封闭的最小族"（用归纳族定义；你可以选别的，说明理由）。确认：塔第 1 项那一层上它包含 `YiPCDom.Pre` 的全部链项；对塔第 2 项那一层，回灌链的前两项在内（构造）。不成立就停下回报。
1. **限域的归约**：写出 `StepU` 与 `PresU` 限到 `D` 的版本，照 `YiLKFold`、`YiLKSlot` 编译限域的 `steps→lowKeep`，结论是 `eboᵍ` 要的 `LowKeep`（`Gx` 只要 Ω 树，所以限域应当够；若中途需要域外的树，交第一个反例）。
2. **翻译账的信息**：域族只用到树的哪些构造与字段（子树、回灌、第一位置前驱）；它与 `domsᵍ` 的关系；若更宽或更窄的域被编译否定，写成否定定理。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiPF`（模块名 `OCF.Lean.YiPF…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiFM`、`YiLL`、`YiMX`、`YiGT`、`YiSU`、`YiPX`）。定义域族的文件文首标明 "不读记号"，用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包没有记号模块；其余文件标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有八路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；5G 仍耗尽（先在回报里说明）；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。



## 首次回报原文（原任务仍继续）

主审复核与续作原因另见 LOG；首次报告的结束判断不自动成为主审结论。

### YiPF 完整回报

冻结时间：2026-11-14 14:24:27 UTC。六个仓库源码、全部临时源码和日志均已列在文末；未提交、未推送，等待主审独立复核。

#### 1. 判决与各步

对目标的含义：得到一条树侧的、与塔阶段无关的域闭包限制，以及一个按实际回灌链访问的域族和统一条件归约。没有新增无条件序数值强度，未证明全层槽位律可满足，也未证明新域是真子域。

1. **原候选 D 的限制（编译定理）**：任意域族 Q 若包含每层 Ω 树、对 Ω 的每个分支、嵌入孩子和后继反演封闭，就包含每层的每棵树。一般定理为 `seed-children-total`；`closed-total`、`no-exclusion` 对包含回灌的完整 Closed 接口给出同一限制。证明不使用回灌，不读记号。它否定的是“同组闭包要求能给真子域”这一候选，不是否定所有阶段无关域。
2. **第 0 步（编译定理）**：原 D 和后续 W 均包含 `YiPCDom.Pre` 全部项；塔第 2 项那一层的实际回灌链不止前两项，而是所有项均在域内。覆盖证明直接走回灌输出与前驱构造子，不调用 D 的总性。
3. **续指示下的 W（编译定义及定理）**：移去任意 Ω 分支闭包，改为只访问有 Ω 点态下界的底所生成的实际回灌链；第一位置前驱与嵌入孩子闭包保留。`OKᵀ` 只用树的等式、第一位置序及 Ω 树。W 的定义与归约没有按塔阶段分情况。
4. **第 1 步（编译条件定理）**：`YiPFReachFold.slots→lowKeepᵂ` 将全层限域起点 `Startᵂ`、只在实际链第 suc n 项上要求的一步 `Stepᵂ` 归约到实际 gradedᵍ/domsᵍ 的 LowKeep。Fold.LF 每个递归调用均显式传 W 证据；没有中途要求任意 Ω 分支的域证据。全层两律未实填；零层各有实例。
5. **原 Leaf 箭头**：`steps→lowKeepᵂ` 按任务保留“全域 Leaf 加全层 Stepᵂ ⇒ LowKeep”的形式箭头。全域 Leaf 已被主审给出的 YiLLLeafNeg.noLeaf 否定，所以这一箭头不能报告为强度成果。本路没有组装 EBO 终点。独立的 `slots→lowKeepᵂ` 不以 Leaf 为前提，但其两条全层前提是否可满足仍未证明。
6. **第 2 步**：翻译账与量化域关系见 §4；域文件导入闭包审计通过。

| 问题 | 精确位置 | 状态 / 档 |
|---|---|---|
| 原闭包是否收窄量化域 | YiPFDom.seed-children-total、all-in | 否；编译定理 |
| 第 0 步实际链是否覆盖 | YiPFReachCover.pre-in、idx₂-in | 是，对所有 n；编译定理 |
| 只用实际链分支能否完成统一归约 | YiPFReachFold.Fold.LF、slots→lowKeepᵂ | 条件归约已编译；不等于前提已实填 |
| W 是否真子域 | YiPFReach.W | 未知，未给否定或严格性声称 |
| 全层 Startᵂ 与 Stepᵂ 是否可满足 | YiPFReachFold.Startᵂ、Stepᵂ | 未证；目前实例仅在零层 |
| 是否得到 LowKeep 的闭项或 EBO 值下界 | 全路 | 否；未实填全层律 |
| 是否否定全部阶段无关域 | 全路 | 否；没有这样的结论 |

本路没有把有限样本当作证明。两条链覆盖都是对任意 n 的编译定理；“可作后续候选”的定位只是判断。

#### 2. 文件、冷编与内存

每件都逐字删除自己的 `probes/_build/2.8.0.2/agda/OCF/Lean/<名字>.agdai` 后单独编译。所有冷编退出码由 Agda 原始命令记录为 0，未经过管道；每份日志只有本模块的一行 Checking，另有 RTS 统计，无依赖 Checking、警告或错误。代码行数为代码块内非空行数。各列保留 RTS 的原始口径。

| 文件 | 非空代码行 | 冷编退出码 | maximum residency（bytes） | total memory in use（MiB） | 冷编日志 |
|---|---:|---:|---:|---:|---|
| [YiPFCover](../../OCF/Lean/YiPFCover.lagda.md) | 36 | 0 | 158,584,360 | 269 | [YiPFCover.cold.log](<实验目录>/YiPFCover.cold.log) |
| [YiPFDom](../../OCF/Lean/YiPFDom.lagda.md) | 61 | 0 | 162,166,704 | 270 | [YiPFDom.cold.log](<实验目录>/YiPFDom.cold.log) |
| [YiPFReach](../../OCF/Lean/YiPFReach.lagda.md) | 43 | 0 | 154,454,880 | 259 | [YiPFReach.cold.log](<实验目录>/YiPFReach.cold.log) |
| [YiPFReachCover](../../OCF/Lean/YiPFReachCover.lagda.md) | 30 | 0 | 158,643,056 | 270 | [YiPFReachCover.cold.log](<实验目录>/YiPFReachCover.cold.log) |
| [YiPFReachFold](../../OCF/Lean/YiPFReachFold.lagda.md) | 116 | 0 | 1,332,085,784 | 2335 | [YiPFReachFold.cold.log](<实验目录>/YiPFReachFold.cold.log) |
| [YiPFReduce](../../OCF/Lean/YiPFReduce.lagda.md) | 67 | 0 | 1,411,103,704 | 2417 | [YiPFReduce.cold.log](<实验目录>/YiPFReduce.cold.log) |

`YiPFDom`、`YiPFReach` 是不读记号的域文件；其余文首均标为验收文件。原 D 的 YiPFCover/YiPFReduce 保留为候选检查与“等价包装没有收窄”的可复查记录，正式的后续候选入口是 YiPFReach、YiPFReachCover、YiPFReachFold。

统一配方（按本路要求单路 5G）：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<名字>.lagda.md > <实验目录>/<名字>.cold.log 2>&1
print "exit $?"
```

临时纯 Agda 另有 `-l standard-library -i <实验目录>`，文件头显式带仓库的 infective 选项。

#### 3. 定理表与逐字陈述

以下均是编译定理；条件结论连同完整前提一起报告。接口的完整定义一并列出，避免把类型别名当作已实填的律。

| 名字 | 白话 | 文件 |
|---|---|---|
| seed-children-total | 任意满足所列四条要求的域族都会包含全部树；不需要回灌 | YiPFDom |
| closed、least | D 满足闭包接口，并被每个满足该接口的域族包含 | YiPFDom |
| all-in、closed-total、no-exclusion | D 总化，完整 Closed 接口也不能排除任何树 | YiPFDom |
| pre-in、idx₂-in | D 覆盖 Pre 全域与塔 2 实际链 | YiPFCover |
| pres-toᴰ/fromᴰ、start-toᴰ/fromᴰ、step-toᴰ/fromᴰ | D 上三种限域接口与原全域律各有两个方向的蕴含，不能算完成收窄 | YiPFReduce |
| base-ok、zero-in、suc-inv、lim-inv | W 的底实例、零与必要前驱闭包 | YiPFReach |
| w-to-d | W 的证据可送到 D；不声称真包含 | YiPFReach |
| idx-in、pre-in、idx₂-in | W 覆盖实际两层链及 Pre 全域 | YiPFReachCover |
| ⊴-tree、ok-tree | 原下界证据可转为干净域使用的树侧下界证据 | YiPFReachFold |
| pres-zero、start-zero、step-zero | 三个限域接口的零层实例；后两条因零层无槽位成立 | YiPFReachFold |
| fromSlots、slots→lowKeepᵂ | 限域全层槽位起点与步进足够得到实际 LowKeep | YiPFReachFold |
| start-from-full、step-from-full | 原全域接口推出链上接口；未给逆方向或严格性结论 | YiPFReachFold |
| steps→lowKeepᵂ | 保留原 Leaf 条件箭头；Leaf 前提已假，不能作为强度成果 | YiPFReachFold |

##### 3.1 原候选的总化限制

```agda
seed-children-total : (Q : (ℓ : L) → Tr ℓ → Set)
  → (∀ ℓ → Q ℓ (proj₁ (Ωt ℓ)))
  → (∀ {ℓ p g} → Q ℓ (Ω p g) → ∀ c → Q ℓ (g c))
  → (∀ {s h x c y e} → Q (nd s h) (up x c y e) → Q (h c) y)
  → (∀ {ℓ x} → Q ℓ (suc x) → Q ℓ x)
  → ∀ ℓ x → Q ℓ x

closed : Closed D

least : ∀ {Q} → Closed Q → ∀ {ℓ x} → D ℓ x → Q ℓ x

all-in : ∀ ℓ (x : Tr ℓ) → D ℓ x

closed-total : ∀ {Q} → Closed Q → ∀ ℓ x → Q ℓ x

no-exclusion : ∀ {Q} → Closed Q → ∀ {ℓ x} → (Q ℓ x → ⊥) → ⊥
```

`Closed D` 的闭项为 `closed`，故接口本身非空。否定不是从一个未实例化的接口开始；它说该接口与“排除某棵树”不能同时成立。四条要求的机制很具体：对任意 ℓ、x，后继形状的源 `nd sS (λ _ → ℓ)` 的 Ω 树在 x 分支上是 `up zero tt (suc x) (z◃ x ◃s)`；抽取孩子后继并反演就得到 x。没有使用折叠，也没有值结论，不归类为值壁垒。

##### 3.2 W 的定义、下界与链

```agda
OKᵀ : ∀ {ℓ} → Base ℓ → Set
OKᵀ B = ∀ i u → (proj₁ (Ωt i) ≡ proj₁ (B i u)) ⊎ (i ⊢ proj₁ (Ωt i) ◃ proj₁ (B i u))

base-ok : ∀ ℓ → OKᵀ (B₀ ℓ)
base-ok ℓ i u = inj₁ refl

chain : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → ℕ → Br ℓ p
chain ℓ o r B p g = iter (feedᴰ ℓ o r B p g) (fromBr ℓ p zero)

data W : (ℓ : L) → Tr ℓ → Set where
  root : ∀ ℓ → W ℓ (proj₁ (Ωt ℓ))
  below : ∀ {ℓ x y} → W ℓ y → ℓ ⊢ x ◃ y → W ℓ x
  child : ∀ {s h x c y e} → W (nd s h) (up x c y e) → W (h c) y
  visit : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
    → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
    → ∀ n → W ℓ (g (chain ℓ o r B p g n))
  output : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
    → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
    → ∀ n → W (at ℓ p) (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p)
        (B (at ℓ p) (posW ℓ p)) (g (chain ℓ o r B p g n))))

base-ok : ∀ ℓ → OKᵀ (B₀ ℓ)

w-to-d : ∀ {ℓ x} → W ℓ x → Wide.D ℓ x
```

##### 3.3 实际链覆盖（两份文件中左侧域分别为 D 与 W）

```agda
idx-in : ∀ n → W zero (PC.idx n)

pre-in : ∀ {x} → PC.Pre x → W zero x

idx₂-in : ∀ n → W (tw 1) (idx₂ n)
```

塔 2 的链在该文件中逐字定义为：

```agda
p₂ : Pos (tw 2)
p₂ = inj₁ (inj₁ tt)

G₂ : Br (tw 2) p₂ → Tr (tw 2)
G₂ c = proj₁ (upz c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))

idx₂ : ℕ → Tr (tw 1)
idx₂ = chain (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) p₂ G₂
```

##### 3.4 W 上的限域接口与归约

```agda
Presᵂ : L → Set
Presᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
  → ∀ {a x} → W ℓ x → GR.R ℓ a x
  → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (ψ ℓ o r B zero (z≤ ℓ) β x))

Startᵂ : L → Set
Startᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
  → GR.Low ℓ p (E.γT (t ++ a) ν zero) (D.chain ℓ o r B p g 1)

Stepᵂ : L → Set
Stepᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g) → (n : ℕ)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) (D.chain ℓ o r B p g (suc n))
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g (D.chain ℓ o r B p g (suc n)))
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (D.chain ℓ o r B p g (suc (suc n)))

⊴-tree : ∀ {S} {x y : T S} → x ⊴ y → (x ≡ y) ⊎ Lt S x y

ok-tree : ∀ {ℓ} {B : Base ℓ} → OK B → OKᵀ B

pres-zero : Presᵂ zero

start-zero : Startᵂ zero

step-zero : Stepᵂ zero

fromSlots : (∀ ℓ → Startᵂ ℓ) → (∀ ℓ → Stepᵂ ℓ) → ∀ ℓ → Presᵂ ℓ

slots→lowKeepᵂ : (∀ ℓ → Startᵂ ℓ) → (∀ ℓ → Stepᵂ ℓ) → Laws.LowKeep gradedᵍ domsᵍ

start-from-full : ∀ ℓ → StartU ℓ → Startᵂ ℓ

step-from-full : ∀ ℓ → StepU ℓ → Stepᵂ ℓ

steps→lowKeepᵂ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → Stepᵂ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

这些全层起点/步进前提仍然量化所有 o、r、满足下界的 B、t、a 和有 W 证据的源节点；Stepᵂ 去掉了任意 c 的量化，c 固定为当前 feed 链的第 suc n 项。**并未证明这两条全层前提的可满足性。**第 0 步与零层实例通过，不能替代全层实例。

##### 3.5 原 D 的限域包装（诊断记录）

```agda
Presᴰ : L → Set

Startᴰ : L → Set

Stepᴰ : L → Set

pres-toᴰ : ∀ ℓ → PresU ℓ → Presᴰ ℓ

pres-fromᴰ : ∀ ℓ → Presᴰ ℓ → PresU ℓ

start-toᴰ : ∀ ℓ → StartU ℓ → Startᴰ ℓ

start-fromᴰ : ∀ ℓ → Startᴰ ℓ → StartU ℓ

step-toᴰ : ∀ ℓ → StepU ℓ → Stepᴰ ℓ

step-fromᴰ : ∀ ℓ → Stepᴰ ℓ → StepU ℓ

pres→lowKeepᴰ : (∀ ℓ → Presᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ

slots→lowKeepᴰ : (∀ ℓ → Startᴰ ℓ) → (∀ ℓ → Stepᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ

steps→lowKeepᴰ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → Stepᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

这些箭头保留用于复查“包装本身没有收窄”；不记作完成目标，也不作为强度。

#### 4. 第一个障碍、翻译账与范围

**第一个精确障碍**是 `seed-children-total`：若要求任意 Ω 分支闭包，同时保留全部层的 Ω 种子、嵌入孩子和后继反演，那么聚合后的域不能是用来排除树的子域。这是编译过的限制，范围不扩张为所有阶段无关方案。

续指示后的 W 没有遇到域外孩子：

- `m1` 用 W.suc-inv；`mL` 和 `mc` 保留同一域证据。
- `mΩ` 只需 `W.visit ... (suc n)`，链律依次给所需 Low；不调用任意分支闭包。
- `mU` 的左项用第一位置 `◃u` 向下闭包，孩子用 W.child；底更新的下界复用 YiLKIface.updated-ok。
- `mw` 用 W.below。

当前第一个未填的数学输入是 `∀ ℓ → Startᵂ ℓ`，其后还有 `∀ ℓ → Stepᵂ ℓ`。没有这两个全层闭项，就没有本路无条件 LowKeep。没有相应编译否定，不判为路线已否定。

W 使用的树侧构造/字段为 L、各层 Tr、Ωt、第一位置 Lt、up 的孩子与孩子树、槽位 p/at/fromBr/posW、Ok、Rb、Base、ψ 和 iter。域文件不含 EboLean 的项、序、基本列；没有阶段 n 的分支定义，链内 n 只是自然数迭代次数。W 对所有有 Ω 下界的 B 与所有 Rb 表收集实际链，尚不限于主线 rbᶻ 的规范来源，这是一项保留的宽度，不能说它已经等于最小主线可达域。

`domsᵍ.Gx` 是 `x ≡ proj₁ (Ωt ℓ)`，所以 W.root 加等式运输立即给该输入的 W 证据；孩子/链访问发生在外部保持证明里，不改变 domsᵍ、树、折叠或合法性。所需保持证明沿 YiLKFold 的记号验收关系归纳，因此“统一归约”的证明是验收层的；域本身没有记号依赖。未由此声称树已自足。

导入闭包审计未使用 --only：YiPFDom 总计 14 模块、本地 6；YiPFReach 总计 15 模块、本地 7；禁用表命中均为 0。见 importclosure.final.log。域的全部本地导入都在本路域文件及 YiRWBlock/YiRWOps/YiRWPath/YiRWFold/YiTBRow 内。禁用构造及本机路径检索对六件仓库源码命中 0；没有使用 Funext、K、无关投射或编译器绕行指示。

#### 5. 偏离、事故及未独立复核的背景

- 首次第 0 步临时检查已在开始后 30 分钟以内完成；初始 YiPFCheck.log 的结束修改时刻为 2026-11-14 14:06:13 UTC。未触发 5G 堆耗尽或同一数学位置两次重新设计仍失败的停止条件。
- 初始 D 满足覆盖却总化，已经向主审汇报；续指示明确要求继续实际可达分支，本路按该指示增加 W。没有悄悄替换原结论。
- 一次临时 scope 错误：YiPFReachCheck 缺 proj₂ 导入，退出 42，补导入后通过；保留失败日志。
- 一次 without-K 下直接对 `gb i u` 的 ⊴r 匹配卡住，退出 42；改为对任意 x、y 的通用转换 `⊴-tree`，没有开启 K。
- 随后 W.visit 处 `ok-tree gb` 留下一个隐式底函数元，退出 42；显式写 `{ℓ = nd s h} {B = B}` 后通过。它们是证明参数/合一修正，没有改树、折叠、合法性或数学域条件。
- 全程仅一个 Agda 进程，全部 -M5G；无堆耗尽、超时或内部错误；未派子路、未装包、未改他路文件，未提交/推送。未修改 README、LOG 或台账。
- 读取过 AGENTS.md、简报、手册 §4、YiLKFold/YiLKIface/YiLKSlot/YiPCDom/YiCDCanon、相关树/折叠/关系签名；YiLLLeafNeg 源码读过，但本路没有独立删除其接口冷编。其 noLeaf 的主审冷编结果来自最新委派事实；因此不把它当成本路新增复核。
- YiGIEnd.eboᵍ、YiPCKeel.k1ᴾ、YiPCLift 的背景结论只按简报引用，未在本路独立复核；没有把这些背景当作本路的新成果。已有依赖使用共享接口，未运行 --ignore-interfaces。

#### 6. 全部交付与实验目录

仓库源码：

- [YiPFCover.lagda.md](../../OCF/Lean/YiPFCover.lagda.md)
- [YiPFDom.lagda.md](../../OCF/Lean/YiPFDom.lagda.md)
- [YiPFReach.lagda.md](../../OCF/Lean/YiPFReach.lagda.md)
- [YiPFReachCover.lagda.md](../../OCF/Lean/YiPFReachCover.lagda.md)
- [YiPFReachFold.lagda.md](../../OCF/Lean/YiPFReachFold.lagda.md)
- [YiPFReduce.lagda.md](../../OCF/Lean/YiPFReduce.lagda.md)

私有实验目录：`<实验目录>`。最初读取的任务简报是 `<临时目录>`。本回报路径为 `<临时目录>`。

临时源码、库文件、生成脚本及完整日志清单：

- [YiPFCheck.agda](<实验目录>/YiPFCheck.agda)
- [YiPFCheck.agdai](<实验目录>/YiPFCheck.agdai)
- [YiPFCheck.log](<实验目录>/YiPFCheck.log)
- [YiPFCover.cold.log](<实验目录>/YiPFCover.cold.log)
- [YiPFCover.first.log](<实验目录>/YiPFCover.first.log)
- [YiPFDom.cold.log](<实验目录>/YiPFDom.cold.log)
- [YiPFDom.extend.log](<实验目录>/YiPFDom.extend.log)
- [YiPFDom.first.log](<实验目录>/YiPFDom.first.log)
- [YiPFReach.cold.log](<实验目录>/YiPFReach.cold.log)
- [YiPFReachCheck.agda](<实验目录>/YiPFReachCheck.agda)
- [YiPFReachCheck.agdai](<实验目录>/YiPFReachCheck.agdai)
- [YiPFReachCheck.fixed.log](<实验目录>/YiPFReachCheck.fixed.log)
- [YiPFReachCheck.log](<实验目录>/YiPFReachCheck.log)
- [YiPFReachCover.cold.log](<实验目录>/YiPFReachCover.cold.log)
- [YiPFReachCover.first.log](<实验目录>/YiPFReachCover.first.log)
- [YiPFReachFold.cold.log](<实验目录>/YiPFReachFold.cold.log)
- [YiPFReachFold.first.log](<实验目录>/YiPFReachFold.first.log)
- [YiPFReduce.cold.log](<实验目录>/YiPFReduce.cold.log)
- [YiPFReduce.first.log](<实验目录>/YiPFReduce.first.log)
- [YiPFRestrict.agda](<实验目录>/YiPFRestrict.agda)
- [YiPFRestrict.agdai](<实验目录>/YiPFRestrict.agdai)
- [YiPFRestrict.log](<实验目录>/YiPFRestrict.log)
- [YiPFWeakFold.agda](<实验目录>/YiPFWeakFold.agda)
- [YiPFWeakFold.agdai](<实验目录>/YiPFWeakFold.agdai)
- [YiPFWeakFold.explicit.log](<实验目录>/YiPFWeakFold.explicit.log)
- [YiPFWeakFold.fixed.log](<实验目录>/YiPFWeakFold.fixed.log)
- [YiPFWeakFold.log](<实验目录>/YiPFWeakFold.log)
- [forbidden-scan.log](<实验目录>/forbidden-scan.log)
- [importclosure.final.log](<实验目录>/importclosure.final.log)
- [importclosure.log](<实验目录>/importclosure.log)
- [libraries](<实验目录>/libraries)
- [make-report.py](<实验目录>/make-report.py)

仓库源码 SHA-256（冻结后未改）：

```text
2b21291a52ec8da59d84b56151c3d81244f7c6e48296e067579f45bce82c3653  probes/OCF/Lean/YiPFCover.lagda.md
194bbff7f88f4308a45e615d62774a584548eb2b12ed1a2472dc39a435b01f77  probes/OCF/Lean/YiPFDom.lagda.md
394dd6dffaaf4d2c093b6d59cbc2f7baefa88c13aa79520359d3ac25bfd241a5  probes/OCF/Lean/YiPFReach.lagda.md
6758628b0fb4ca9cfe5255a5c9ad83b042c2b728e4607ae3ded83e7dd88399ec  probes/OCF/Lean/YiPFReachCover.lagda.md
458cc1df2aee23d1932d3945369da05dd5d68b62d3ff1bc1e2166798cec7852d  probes/OCF/Lean/YiPFReachFold.lagda.md
310be78532d5f607f13be56fcc8e210faa3ef6a6a0e8eeee22a608d8be0d4f78  probes/OCF/Lean/YiPFReduce.lagda.md
```

## 主审最终复核

七件均逐件删自身接口5G冷编0、仅自身Checking，扫描0；三个域文件脚本闭包与编译器图逐一相同且干净。W在所有Ok层总化，因此不能收窄Pres/Start输入；Stepᵂ仍只限实际链位置。两组闭包的总化均不否定所有阶段无关域，详见LOG和台账V187。

## 最终回报原文（含复核补充）

### YiPF 复核补充：W 在 Ok 层总化

冻结时间：2026-11-14 14:42:05 UTC。新源码仅 `YiPFReachTotal.lagda.md`，原六件源码 SHA-256 核对全部未变。新文件已单路 5G、自删自身接口冷编 0，等主审独立复核。

#### 1. 判决与范围

编译定理：`w-total-ok : ∀ ℓ → Ok ℓ → ∀ (x : Tr ℓ) → W ℓ x`。因此前一回报中“W 是否为真子域未知”已被本补充收窄为：**在每个 Ok 层，W 包含全部树，不能借 W 成员证据缩小该层的输入树范围。**规范塔层全部由 `Ok-tw` 覆盖。

一般版本 `output-total-ok` 对任意满足 OutputClosed 四个字段的域族成立。四个字段是全层 Ω 种子、第一位置前驱、嵌入孩子和对所有满足 OKᵀ 的底的回灌输出闭包；不需要任意 Ω 分支，也不需要 W.visit。`closedᵂ : OutputClosed W` 给出接口的实际实例，条件不是空的。

这只否定当前这组 W 闭包能够在 Ok 层给真子域，不否定所有阶段无关域。`Presᵂ`、`Startᵂ` 的参数中已经有 `o : Ok ℓ`，其 W 输入证据因而可直接由 `w-total-ok ℓ o x` 提供；这两个接口中的 W 输入限制不能缩小所量化的树。`Stepᵂ` 的 W 输入证据同样可提供，但它的“只在实际链第 suc n 项要求一步”的链位置限制没有被消除，没有证明它与 StepU 等价。这里是已编译总化定理的应用读法，未另列编译过的接口互推引理。旧的限域条件归约继续成立，但不能再把源树的 W 证据说成完成了量化域收窄。没有序数值或 EBO 强度成果。

连续 D、W 两个总化结果后，按最新指示停下查量化域；没有增添第三种域或字段。

零层 `start-zero`、`step-zero` 因 `Pos zero` 为空而成立，属于无槽位的空实例；它们没有实填全层有槽位处的 `Startᵂ` 或 `Stepᵂ`，后者的可满足性仍未证明。

| 问题 | 位置 | 档与结论 |
|---|---|---|
| 给出的具体反例机制是否可构造 | Proof.B、Proof.B-ok、Proof.first-output、Proof.result | 编译定理，是 |
| W 在 Ok 层是否排除树 | w-total-ok、w-total-tw | 编译定理，不排除任何树 |
| 该机制是否依赖任意 Ω 分支闭包 | OutputClosed、Proof.result | 编译定理，无该字段 |
| 是否否定所有阶段无关域 | 新模块 | 否，无此结论 |
| Stepᵂ 的链位置限制是否等价全域 StepU | 全路 | 未证，未作否定 |

#### 2. 文件、检查与内存

| 新源码 | 非空代码行 | 冷编退出码 | maximum residency（bytes） | total memory（MiB） |
|---|---:|---:|---:|---:|
| [YiPFReachTotal.lagda.md](../../OCF/Lean/YiPFReachTotal.lagda.md) | 76 | 0 | 157,767,384 | 265 |

冷编逐字只删除 `probes/_build/2.8.0.2/agda/OCF/Lean/YiPFReachTotal.agdai`；日志只有新模块的一行 Checking，另有 RTS 数字。命令：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiPFReachTotal.lagda.md > <实验目录>/YiPFReachTotal.cold.log 2>&1
print "exit $?"
```

`importclosure.py OCF.Lean.YiPFReachTotal` 未使用 --only，退出 0、禁用表命中 0。禁用构造及本机路径扫描命中 0。原六件没有重编或修改。

#### 3. 逐字定理与接口

```agda
record OutputClosed (Q : (ℓ : L) → Tr ℓ → Set) : Set where
  field
    rootᵒ : ∀ ℓ → Q ℓ (proj₁ (Ωt ℓ))
    belowᵒ : ∀ {ℓ x y} → Q ℓ y → ℓ ⊢ x ◃ y → Q ℓ x
    childᵒ : ∀ {s h x c y e} → Q (nd s h) (up x c y e) → Q (h c) y
    outputᵒ : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
      → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → Q ℓ (Ω p g)
      → ∀ n → Q (at ℓ p) (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p)
          (B (at ℓ p) (posW ℓ p)) (g (W.chain ℓ o r B p g n))))

closedᵂ : OutputClosed W
closedᵂ = record { rootᵒ = W.root ; belowᵒ = W.below ; childᵒ = W.child ; outputᵒ = W.output }

output-total-ok : ∀ {Q} → OutputClosed Q → ∀ ℓ → Ok ℓ → ∀ (x : Tr ℓ) → Q ℓ x
output-total-ok {Q} cl ℓ o x = Proof.result Q cl ℓ o x

w-total-ok : ∀ ℓ → Ok ℓ → ∀ (x : Tr ℓ) → W ℓ x
w-total-ok = output-total-ok closedᵂ

w-total-tw : ∀ n (x : Tr (tw n)) → W (tw n) x
w-total-tw n = w-total-ok (tw n) (Ok-tw n)

no-exclusion-ok : ∀ {Q} → OutputClosed Q → ∀ ℓ → Ok ℓ → ∀ x → (Q ℓ x → ⊥) → ⊥
no-exclusion-ok cl ℓ o x outside = outside (output-total-ok cl ℓ o x)
```

| 定理 | 白话 | 文件 | 档 |
|---|---|---|---|
| closedᵂ | W 实填这四个闭包字段 | YiPFReachTotal | 编译定理 |
| Proof.first-output | 指定的合法底使首次输出为 next⁺ b，对任意 Rb H 都成立 | YiPFReachTotal | 编译定理 |
| output-total-ok | 任何满足这四个字段的域在 Ok 层包含全部树 | YiPFReachTotal | 编译定理 |
| w-total-ok | 当前 W 在 Ok 层包含全部树 | YiPFReachTotal | 编译定理 |
| w-total-tw | 当前 W 在所有规范塔层包含全部树 | YiPFReachTotal | 编译定理 |
| no-exclusion-ok | 同组闭包与排除某个 Ok 层树不能同时成立 | YiPFReachTotal | 编译否定定理 |

前提可满足：`closedᵂ` 是接口实例；`Ok-tw n` 对全部 n 实填层号前提。没有用 Funext、K 或其他额外假设。

#### 4. 具体机制与量化域检查

固定任意 `ℓ`、`o : Ok ℓ`、`x : Tr ℓ`。令 `a = S ℓ`、`H = S a`，其中 `S k = nd sS (λ _ → k)`。定义：

```agda
  e : ℓ ⊢ zero ◃ suc x
  e = z◃ x ◃s

  b : Tr⁺ a
  b = up (proj₁ (Ωt a)) tt (suc x) e , ◃t (proj₂ (Ωt a)) (◃u (proj₁ (Ωt a)) tt (suc x) e)

  Ba : Base a
  Ba .a self = b
  Ba j (inc c u) = Ωt j
  Ba j (inu us) = Ωt j

  Ba-ok : OKᵀ Ba
  Ba-ok .a self = inj₂ (◃u (proj₁ (Ωt a)) tt (suc x) e)
  Ba-ok j (inc c u) = inj₁ refl
  Ba-ok j (inu us) = inj₁ refl

  B : Base H
  B .H self = Ωt H
  B j (inc c u) = Ba j u
  B j (inu us) = Ωt j

  B-ok : OKᵀ B
  B-ok .H self = inj₁ refl
  B-ok j (inc c u) = Ba-ok j u
  B-ok j (inu us) = inj₁ refl

  p : Pos H
  p = inj₂ (tt , inj₁ tt)

  g : Br H p → Tr H
  g c = up zero tt (suc c) (z◃ c ◃s)

  first-output : (r : Rb H) → Q a (proj₁ (next⁺ b))
  first-output r = outputᵒ H oh r B B-ok p g (rootᵒ H) 0

  b-in : Q a (proj₁ b)
  b-in = belowᵒ (first-output (rb-no H)) (◃l 0)

  result : Q ℓ x
  result = belowᵒ (childᵒ b-in) ◃s
```

`e` 实际取 `z◃ x ◃s`，所需条件是 `0 ◃ suc x`；不要求也没有使用 `Ωt ℓ ◃ suc x`。`b` 的左项就是 Ωt a，故 `Ωt a ◃ b` 由 ◃u 给出，与任意孩子 x 的大小无关。

B 的定义只匹配路径构造子：外层 inc 进入 Ba，Ba 的 self 给 b，其余给 Ω；不需要层号判等或三歧。`B-ok` 每条路径都实填，首次输出等于 next⁺ b 是类型检查中的定义相等。抽取极限第 0 支、嵌入孩子、后继前驱后得到任意 x 的域证据。

精确触发字段是 `outputᵒ` 对**全部**满足 Ω 点态下界的底 B 量化；这样的底可以在保留 Ω 第一位置前驱的同时，携带任意孩子 suc x。W 的子树闭包再把 x 读出来。它不是来自 Ω 任意分支访问，也不是第 n 很大时的回灌行为：n = 0 即成立。Proof.first-output 对任意比较表 r 成立，因此该步不利用比较表的额外条目。

这轮到此停止，不提出第三组补丁字段。后续若继续，应先审查需要量化哪些源、哪些有来源证据的底、以及希望保留哪些实际使用闭包；此处只是定位当前量化域的宽度，没有给出可行的新接口，更没有关闭全部阶段无关路线。

#### 5. 偏离与事故

- 原六件源码及原冻结回报的内容快照均保存。新源码仅同前缀的 YiPFReachTotal。
- 临时文件首次因局部名字 B 与块签名字段 B 撞名，退出 42；隐藏导入字段后编译 0。这是作用域修正，没有改变构造或闭包字段。
- 正式一般化版本初编 0；将 first-output 显式量化任意 Rb H 后，删自身接口冷编仍为 0。
- 全程单 Agda、5G，未遇到堆耗尽、超时或停止检查问题；未派子路、未提交、未推送，未改 src、archive、地图、日志或台账。
- 反例机制来源是主审转来的独立只读复核；收到时是纸面判断，本路实际写出底、下界与总化证明并编译，才改报为编译定理。没有读取该独立复核者的其他文件，没有凭未读报告追加结论。

#### 6. 交付与完整实验清单

- 新源码：[<仓库>/probes/OCF/Lean/YiPFReachTotal.lagda.md](../../OCF/Lean/YiPFReachTotal.lagda.md)
- 原六件源码及先前全部实验列表仍见总回报的历史快照。
- 新实验目录：`<实验目录>`。

- [YiPF-report.initial.md](<实验目录>/YiPF-report.initial.md)
- [YiPFReachTotal.cold.log](<实验目录>/YiPFReachTotal.cold.log)
- [YiPFReachTotal.first.log](<实验目录>/YiPFReachTotal.first.log)
- [YiPFWTotalCheck.agda](<实验目录>/YiPFWTotalCheck.agda)
- [YiPFWTotalCheck.agdai](<实验目录>/YiPFWTotalCheck.agdai)
- [YiPFWTotalCheck.fixed.log](<实验目录>/YiPFWTotalCheck.fixed.log)
- [YiPFWTotalCheck.log](<实验目录>/YiPFWTotalCheck.log)
- [forbidden-scan.log](<实验目录>/forbidden-scan.log)
- [importclosure.log](<实验目录>/importclosure.log)
- [libraries](<实验目录>/libraries)
- [make-total-report.py](<实验目录>/make-total-report.py)

新源码 SHA-256：

```text
c4f0afbf9641e0d8a989abf64a170e474f5f9539023abb38a50a79f1bcb4630a  probes/OCF/Lean/YiPFReachTotal.lagda.md
```


---

### 原冻结回报（历史快照；W 的总性状态以上方补充为准）

### YiPF 完整回报

冻结时间：2026-11-14 14:24:27 UTC。六个仓库源码、全部临时源码和日志均已列在文末；未提交、未推送，等待主审独立复核。

#### 1. 判决与各步

对目标的含义：得到一条树侧的、与塔阶段无关的域闭包限制，以及一个按实际回灌链访问的域族和统一条件归约。没有新增无条件序数值强度，未证明全层槽位律可满足，也未证明新域是真子域。

1. **原候选 D 的限制（编译定理）**：任意域族 Q 若包含每层 Ω 树、对 Ω 的每个分支、嵌入孩子和后继反演封闭，就包含每层的每棵树。一般定理为 `seed-children-total`；`closed-total`、`no-exclusion` 对包含回灌的完整 Closed 接口给出同一限制。证明不使用回灌，不读记号。它否定的是“同组闭包要求能给真子域”这一候选，不是否定所有阶段无关域。
2. **第 0 步（编译定理）**：原 D 和后续 W 均包含 `YiPCDom.Pre` 全部项；塔第 2 项那一层的实际回灌链不止前两项，而是所有项均在域内。覆盖证明直接走回灌输出与前驱构造子，不调用 D 的总性。
3. **续指示下的 W（编译定义及定理）**：移去任意 Ω 分支闭包，改为只访问有 Ω 点态下界的底所生成的实际回灌链；第一位置前驱与嵌入孩子闭包保留。`OKᵀ` 只用树的等式、第一位置序及 Ω 树。W 的定义与归约没有按塔阶段分情况。
4. **第 1 步（编译条件定理）**：`YiPFReachFold.slots→lowKeepᵂ` 将全层限域起点 `Startᵂ`、只在实际链第 suc n 项上要求的一步 `Stepᵂ` 归约到实际 gradedᵍ/domsᵍ 的 LowKeep。Fold.LF 每个递归调用均显式传 W 证据；没有中途要求任意 Ω 分支的域证据。全层两律未实填；零层各有实例。
5. **原 Leaf 箭头**：`steps→lowKeepᵂ` 按任务保留“全域 Leaf 加全层 Stepᵂ ⇒ LowKeep”的形式箭头。全域 Leaf 已被主审给出的 YiLLLeafNeg.noLeaf 否定，所以这一箭头不能报告为强度成果。本路没有组装 EBO 终点。独立的 `slots→lowKeepᵂ` 不以 Leaf 为前提，但其两条全层前提是否可满足仍未证明。
6. **第 2 步**：翻译账与量化域关系见 §4；域文件导入闭包审计通过。

| 问题 | 精确位置 | 状态 / 档 |
|---|---|---|
| 原闭包是否收窄量化域 | YiPFDom.seed-children-total、all-in | 否；编译定理 |
| 第 0 步实际链是否覆盖 | YiPFReachCover.pre-in、idx₂-in | 是，对所有 n；编译定理 |
| 只用实际链分支能否完成统一归约 | YiPFReachFold.Fold.LF、slots→lowKeepᵂ | 条件归约已编译；不等于前提已实填 |
| W 是否真子域 | YiPFReach.W | 未知，未给否定或严格性声称 |
| 全层 Startᵂ 与 Stepᵂ 是否可满足 | YiPFReachFold.Startᵂ、Stepᵂ | 未证；目前实例仅在零层 |
| 是否得到 LowKeep 的闭项或 EBO 值下界 | 全路 | 否；未实填全层律 |
| 是否否定全部阶段无关域 | 全路 | 否；没有这样的结论 |

本路没有把有限样本当作证明。两条链覆盖都是对任意 n 的编译定理；“可作后续候选”的定位只是判断。

#### 2. 文件、冷编与内存

每件都逐字删除自己的 `probes/_build/2.8.0.2/agda/OCF/Lean/<名字>.agdai` 后单独编译。所有冷编退出码由 Agda 原始命令记录为 0，未经过管道；每份日志只有本模块的一行 Checking，另有 RTS 统计，无依赖 Checking、警告或错误。代码行数为代码块内非空行数。各列保留 RTS 的原始口径。

| 文件 | 非空代码行 | 冷编退出码 | maximum residency（bytes） | total memory in use（MiB） | 冷编日志 |
|---|---:|---:|---:|---:|---|
| [YiPFCover](../../OCF/Lean/YiPFCover.lagda.md) | 36 | 0 | 158,584,360 | 269 | [YiPFCover.cold.log](<初始实验目录>/YiPFCover.cold.log) |
| [YiPFDom](../../OCF/Lean/YiPFDom.lagda.md) | 61 | 0 | 162,166,704 | 270 | [YiPFDom.cold.log](<初始实验目录>/YiPFDom.cold.log) |
| [YiPFReach](../../OCF/Lean/YiPFReach.lagda.md) | 43 | 0 | 154,454,880 | 259 | [YiPFReach.cold.log](<初始实验目录>/YiPFReach.cold.log) |
| [YiPFReachCover](../../OCF/Lean/YiPFReachCover.lagda.md) | 30 | 0 | 158,643,056 | 270 | [YiPFReachCover.cold.log](<初始实验目录>/YiPFReachCover.cold.log) |
| [YiPFReachFold](../../OCF/Lean/YiPFReachFold.lagda.md) | 116 | 0 | 1,332,085,784 | 2335 | [YiPFReachFold.cold.log](<初始实验目录>/YiPFReachFold.cold.log) |
| [YiPFReduce](../../OCF/Lean/YiPFReduce.lagda.md) | 67 | 0 | 1,411,103,704 | 2417 | [YiPFReduce.cold.log](<初始实验目录>/YiPFReduce.cold.log) |

`YiPFDom`、`YiPFReach` 是不读记号的域文件；其余文首均标为验收文件。原 D 的 YiPFCover/YiPFReduce 保留为候选检查与“等价包装没有收窄”的可复查记录，正式的后续候选入口是 YiPFReach、YiPFReachCover、YiPFReachFold。

统一配方（按本路要求单路 5G）：

```sh
agda +RTS -M5G -s -RTS --library-file=<初始实验目录>/libraries -i src -i probes probes/OCF/Lean/<名字>.lagda.md > <初始实验目录>/<名字>.cold.log 2>&1
print "exit $?"
```

临时纯 Agda 另有 `-l standard-library -i <初始实验目录>`，文件头显式带仓库的 infective 选项。

#### 3. 定理表与逐字陈述

以下均是编译定理；条件结论连同完整前提一起报告。接口的完整定义一并列出，避免把类型别名当作已实填的律。

| 名字 | 白话 | 文件 |
|---|---|---|
| seed-children-total | 任意满足所列四条要求的域族都会包含全部树；不需要回灌 | YiPFDom |
| closed、least | D 满足闭包接口，并被每个满足该接口的域族包含 | YiPFDom |
| all-in、closed-total、no-exclusion | D 总化，完整 Closed 接口也不能排除任何树 | YiPFDom |
| pre-in、idx₂-in | D 覆盖 Pre 全域与塔 2 实际链 | YiPFCover |
| pres-toᴰ/fromᴰ、start-toᴰ/fromᴰ、step-toᴰ/fromᴰ | D 上三种限域接口与原全域律各有两个方向的蕴含，不能算完成收窄 | YiPFReduce |
| base-ok、zero-in、suc-inv、lim-inv | W 的底实例、零与必要前驱闭包 | YiPFReach |
| w-to-d | W 的证据可送到 D；不声称真包含 | YiPFReach |
| idx-in、pre-in、idx₂-in | W 覆盖实际两层链及 Pre 全域 | YiPFReachCover |
| ⊴-tree、ok-tree | 原下界证据可转为干净域使用的树侧下界证据 | YiPFReachFold |
| pres-zero、start-zero、step-zero | 三个限域接口的零层实例；后两条因零层无槽位成立 | YiPFReachFold |
| fromSlots、slots→lowKeepᵂ | 限域全层槽位起点与步进足够得到实际 LowKeep | YiPFReachFold |
| start-from-full、step-from-full | 原全域接口推出链上接口；未给逆方向或严格性结论 | YiPFReachFold |
| steps→lowKeepᵂ | 保留原 Leaf 条件箭头；Leaf 前提已假，不能作为强度成果 | YiPFReachFold |

##### 3.1 原候选的总化限制

```agda
seed-children-total : (Q : (ℓ : L) → Tr ℓ → Set)
  → (∀ ℓ → Q ℓ (proj₁ (Ωt ℓ)))
  → (∀ {ℓ p g} → Q ℓ (Ω p g) → ∀ c → Q ℓ (g c))
  → (∀ {s h x c y e} → Q (nd s h) (up x c y e) → Q (h c) y)
  → (∀ {ℓ x} → Q ℓ (suc x) → Q ℓ x)
  → ∀ ℓ x → Q ℓ x

closed : Closed D

least : ∀ {Q} → Closed Q → ∀ {ℓ x} → D ℓ x → Q ℓ x

all-in : ∀ ℓ (x : Tr ℓ) → D ℓ x

closed-total : ∀ {Q} → Closed Q → ∀ ℓ x → Q ℓ x

no-exclusion : ∀ {Q} → Closed Q → ∀ {ℓ x} → (Q ℓ x → ⊥) → ⊥
```

`Closed D` 的闭项为 `closed`，故接口本身非空。否定不是从一个未实例化的接口开始；它说该接口与“排除某棵树”不能同时成立。四条要求的机制很具体：对任意 ℓ、x，后继形状的源 `nd sS (λ _ → ℓ)` 的 Ω 树在 x 分支上是 `up zero tt (suc x) (z◃ x ◃s)`；抽取孩子后继并反演就得到 x。没有使用折叠，也没有值结论，不归类为值壁垒。

##### 3.2 W 的定义、下界与链

```agda
OKᵀ : ∀ {ℓ} → Base ℓ → Set
OKᵀ B = ∀ i u → (proj₁ (Ωt i) ≡ proj₁ (B i u)) ⊎ (i ⊢ proj₁ (Ωt i) ◃ proj₁ (B i u))

base-ok : ∀ ℓ → OKᵀ (B₀ ℓ)
base-ok ℓ i u = inj₁ refl

chain : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → ℕ → Br ℓ p
chain ℓ o r B p g = iter (feedᴰ ℓ o r B p g) (fromBr ℓ p zero)

data W : (ℓ : L) → Tr ℓ → Set where
  root : ∀ ℓ → W ℓ (proj₁ (Ωt ℓ))
  below : ∀ {ℓ x y} → W ℓ y → ℓ ⊢ x ◃ y → W ℓ x
  child : ∀ {s h x c y e} → W (nd s h) (up x c y e) → W (h c) y
  visit : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
    → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
    → ∀ n → W ℓ (g (chain ℓ o r B p g n))
  output : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OKᵀ B
    → (p : Pos ℓ) (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
    → ∀ n → W (at ℓ p) (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p)
        (B (at ℓ p) (posW ℓ p)) (g (chain ℓ o r B p g n))))

base-ok : ∀ ℓ → OKᵀ (B₀ ℓ)

w-to-d : ∀ {ℓ x} → W ℓ x → Wide.D ℓ x
```

##### 3.3 实际链覆盖（两份文件中左侧域分别为 D 与 W）

```agda
idx-in : ∀ n → W zero (PC.idx n)

pre-in : ∀ {x} → PC.Pre x → W zero x

idx₂-in : ∀ n → W (tw 1) (idx₂ n)
```

塔 2 的链在该文件中逐字定义为：

```agda
p₂ : Pos (tw 2)
p₂ = inj₁ (inj₁ tt)

G₂ : Br (tw 2) p₂ → Tr (tw 2)
G₂ c = proj₁ (upz c (Ωt (tw 1 ⊕ ↑ (tw 1) c)))

idx₂ : ℕ → Tr (tw 1)
idx₂ = chain (tw 2) (Ok-tw 2) (rbᶻ (tw 2)) (B₀ (tw 2)) p₂ G₂
```

##### 3.4 W 上的限域接口与归约

```agda
Presᵂ : L → Set
Presᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
  → ∀ {a x} → W ℓ x → GR.R ℓ a x
  → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (ψ ℓ o r B zero (z≤ ℓ) β x))

Startᵂ : L → Set
Startᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g)
  → GR.Low ℓ p (E.γT (t ++ a) ν zero) (D.chain ℓ o r B p g 1)

Stepᵂ : L → Set
Stepᵂ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → W ℓ (Ω p g) → (n : ℕ)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) (D.chain ℓ o r B p g (suc n))
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g (D.chain ℓ o r B p g (suc n)))
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (D.chain ℓ o r B p g (suc (suc n)))

⊴-tree : ∀ {S} {x y : T S} → x ⊴ y → (x ≡ y) ⊎ Lt S x y

ok-tree : ∀ {ℓ} {B : Base ℓ} → OK B → OKᵀ B

pres-zero : Presᵂ zero

start-zero : Startᵂ zero

step-zero : Stepᵂ zero

fromSlots : (∀ ℓ → Startᵂ ℓ) → (∀ ℓ → Stepᵂ ℓ) → ∀ ℓ → Presᵂ ℓ

slots→lowKeepᵂ : (∀ ℓ → Startᵂ ℓ) → (∀ ℓ → Stepᵂ ℓ) → Laws.LowKeep gradedᵍ domsᵍ

start-from-full : ∀ ℓ → StartU ℓ → Startᵂ ℓ

step-from-full : ∀ ℓ → StepU ℓ → Stepᵂ ℓ

steps→lowKeepᵂ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → Stepᵂ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

这些全层起点/步进前提仍然量化所有 o、r、满足下界的 B、t、a 和有 W 证据的源节点；Stepᵂ 去掉了任意 c 的量化，c 固定为当前 feed 链的第 suc n 项。**并未证明这两条全层前提的可满足性。**第 0 步与零层实例通过，不能替代全层实例。

##### 3.5 原 D 的限域包装（诊断记录）

```agda
Presᴰ : L → Set

Startᴰ : L → Set

Stepᴰ : L → Set

pres-toᴰ : ∀ ℓ → PresU ℓ → Presᴰ ℓ

pres-fromᴰ : ∀ ℓ → Presᴰ ℓ → PresU ℓ

start-toᴰ : ∀ ℓ → StartU ℓ → Startᴰ ℓ

start-fromᴰ : ∀ ℓ → Startᴰ ℓ → StartU ℓ

step-toᴰ : ∀ ℓ → StepU ℓ → Stepᴰ ℓ

step-fromᴰ : ∀ ℓ → Stepᴰ ℓ → StepU ℓ

pres→lowKeepᴰ : (∀ ℓ → Presᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ

slots→lowKeepᴰ : (∀ ℓ → Startᴰ ℓ) → (∀ ℓ → Stepᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ

steps→lowKeepᴰ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → Stepᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
```

这些箭头保留用于复查“包装本身没有收窄”；不记作完成目标，也不作为强度。

#### 4. 第一个障碍、翻译账与范围

**第一个精确障碍**是 `seed-children-total`：若要求任意 Ω 分支闭包，同时保留全部层的 Ω 种子、嵌入孩子和后继反演，那么聚合后的域不能是用来排除树的子域。这是编译过的限制，范围不扩张为所有阶段无关方案。

续指示后的 W 没有遇到域外孩子：

- `m1` 用 W.suc-inv；`mL` 和 `mc` 保留同一域证据。
- `mΩ` 只需 `W.visit ... (suc n)`，链律依次给所需 Low；不调用任意分支闭包。
- `mU` 的左项用第一位置 `◃u` 向下闭包，孩子用 W.child；底更新的下界复用 YiLKIface.updated-ok。
- `mw` 用 W.below。

当前第一个未填的数学输入是 `∀ ℓ → Startᵂ ℓ`，其后还有 `∀ ℓ → Stepᵂ ℓ`。没有这两个全层闭项，就没有本路无条件 LowKeep。没有相应编译否定，不判为路线已否定。

W 使用的树侧构造/字段为 L、各层 Tr、Ωt、第一位置 Lt、up 的孩子与孩子树、槽位 p/at/fromBr/posW、Ok、Rb、Base、ψ 和 iter。域文件不含 EboLean 的项、序、基本列；没有阶段 n 的分支定义，链内 n 只是自然数迭代次数。W 对所有有 Ω 下界的 B 与所有 Rb 表收集实际链，尚不限于主线 rbᶻ 的规范来源，这是一项保留的宽度，不能说它已经等于最小主线可达域。

`domsᵍ.Gx` 是 `x ≡ proj₁ (Ωt ℓ)`，所以 W.root 加等式运输立即给该输入的 W 证据；孩子/链访问发生在外部保持证明里，不改变 domsᵍ、树、折叠或合法性。所需保持证明沿 YiLKFold 的记号验收关系归纳，因此“统一归约”的证明是验收层的；域本身没有记号依赖。未由此声称树已自足。

导入闭包审计未使用 --only：YiPFDom 总计 14 模块、本地 6；YiPFReach 总计 15 模块、本地 7；禁用表命中均为 0。见 importclosure.final.log。域的全部本地导入都在本路域文件及 YiRWBlock/YiRWOps/YiRWPath/YiRWFold/YiTBRow 内。禁用构造及本机路径检索对六件仓库源码命中 0；没有使用 Funext、K、无关投射或编译器绕行指示。

#### 5. 偏离、事故及未独立复核的背景

- 首次第 0 步临时检查已在开始后 30 分钟以内完成；初始 YiPFCheck.log 的结束修改时刻为 2026-11-14 14:06:13 UTC。未触发 5G 堆耗尽或同一数学位置两次重新设计仍失败的停止条件。
- 初始 D 满足覆盖却总化，已经向主审汇报；续指示明确要求继续实际可达分支，本路按该指示增加 W。没有悄悄替换原结论。
- 一次临时 scope 错误：YiPFReachCheck 缺 proj₂ 导入，退出 42，补导入后通过；保留失败日志。
- 一次 without-K 下直接对 `gb i u` 的 ⊴r 匹配卡住，退出 42；改为对任意 x、y 的通用转换 `⊴-tree`，没有开启 K。
- 随后 W.visit 处 `ok-tree gb` 留下一个隐式底函数元，退出 42；显式写 `{ℓ = nd s h} {B = B}` 后通过。它们是证明参数/合一修正，没有改树、折叠、合法性或数学域条件。
- 全程仅一个 Agda 进程，全部 -M5G；无堆耗尽、超时或内部错误；未派子路、未装包、未改他路文件，未提交/推送。未修改 README、LOG 或台账。
- 读取过 AGENTS.md、简报、手册 §4、YiLKFold/YiLKIface/YiLKSlot/YiPCDom/YiCDCanon、相关树/折叠/关系签名；YiLLLeafNeg 源码读过，但本路没有独立删除其接口冷编。其 noLeaf 的主审冷编结果来自最新委派事实；因此不把它当成本路新增复核。
- YiGIEnd.eboᵍ、YiPCKeel.k1ᴾ、YiPCLift 的背景结论只按简报引用，未在本路独立复核；没有把这些背景当作本路的新成果。已有依赖使用共享接口，未运行 --ignore-interfaces。

#### 6. 全部交付与实验目录

仓库源码：

- [YiPFCover.lagda.md](../../OCF/Lean/YiPFCover.lagda.md)
- [YiPFDom.lagda.md](../../OCF/Lean/YiPFDom.lagda.md)
- [YiPFReach.lagda.md](../../OCF/Lean/YiPFReach.lagda.md)
- [YiPFReachCover.lagda.md](../../OCF/Lean/YiPFReachCover.lagda.md)
- [YiPFReachFold.lagda.md](../../OCF/Lean/YiPFReachFold.lagda.md)
- [YiPFReduce.lagda.md](../../OCF/Lean/YiPFReduce.lagda.md)

私有实验目录：`<初始实验目录>`。最初读取的任务简报是 `<临时目录>`。本回报路径为 `<临时目录>`。

临时源码、库文件、生成脚本及完整日志清单：

- [YiPFCheck.agda](<初始实验目录>/YiPFCheck.agda)
- [YiPFCheck.agdai](<初始实验目录>/YiPFCheck.agdai)
- [YiPFCheck.log](<初始实验目录>/YiPFCheck.log)
- [YiPFCover.cold.log](<初始实验目录>/YiPFCover.cold.log)
- [YiPFCover.first.log](<初始实验目录>/YiPFCover.first.log)
- [YiPFDom.cold.log](<初始实验目录>/YiPFDom.cold.log)
- [YiPFDom.extend.log](<初始实验目录>/YiPFDom.extend.log)
- [YiPFDom.first.log](<初始实验目录>/YiPFDom.first.log)
- [YiPFReach.cold.log](<初始实验目录>/YiPFReach.cold.log)
- [YiPFReachCheck.agda](<初始实验目录>/YiPFReachCheck.agda)
- [YiPFReachCheck.agdai](<初始实验目录>/YiPFReachCheck.agdai)
- [YiPFReachCheck.fixed.log](<初始实验目录>/YiPFReachCheck.fixed.log)
- [YiPFReachCheck.log](<初始实验目录>/YiPFReachCheck.log)
- [YiPFReachCover.cold.log](<初始实验目录>/YiPFReachCover.cold.log)
- [YiPFReachCover.first.log](<初始实验目录>/YiPFReachCover.first.log)
- [YiPFReachFold.cold.log](<初始实验目录>/YiPFReachFold.cold.log)
- [YiPFReachFold.first.log](<初始实验目录>/YiPFReachFold.first.log)
- [YiPFReduce.cold.log](<初始实验目录>/YiPFReduce.cold.log)
- [YiPFReduce.first.log](<初始实验目录>/YiPFReduce.first.log)
- [YiPFRestrict.agda](<初始实验目录>/YiPFRestrict.agda)
- [YiPFRestrict.agdai](<初始实验目录>/YiPFRestrict.agdai)
- [YiPFRestrict.log](<初始实验目录>/YiPFRestrict.log)
- [YiPFWeakFold.agda](<初始实验目录>/YiPFWeakFold.agda)
- [YiPFWeakFold.agdai](<初始实验目录>/YiPFWeakFold.agdai)
- [YiPFWeakFold.explicit.log](<初始实验目录>/YiPFWeakFold.explicit.log)
- [YiPFWeakFold.fixed.log](<初始实验目录>/YiPFWeakFold.fixed.log)
- [YiPFWeakFold.log](<初始实验目录>/YiPFWeakFold.log)
- [forbidden-scan.log](<初始实验目录>/forbidden-scan.log)
- [importclosure.final.log](<初始实验目录>/importclosure.final.log)
- [importclosure.log](<初始实验目录>/importclosure.log)
- [libraries](<初始实验目录>/libraries)
- [make-report.py](<初始实验目录>/make-report.py)

仓库源码 SHA-256（冻结后未改）：

```text
2b21291a52ec8da59d84b56151c3d81244f7c6e48296e067579f45bce82c3653  probes/OCF/Lean/YiPFCover.lagda.md
194bbff7f88f4308a45e615d62774a584548eb2b12ed1a2472dc39a435b01f77  probes/OCF/Lean/YiPFDom.lagda.md
394dd6dffaaf4d2c093b6d59cbc2f7baefa88c13aa79520359d3ac25bfd241a5  probes/OCF/Lean/YiPFReach.lagda.md
6758628b0fb4ca9cfe5255a5c9ad83b042c2b728e4607ae3ded83e7dd88399ec  probes/OCF/Lean/YiPFReachCover.lagda.md
458cc1df2aee23d1932d3945369da05dd5d68b62d3ff1bc1e2166798cec7852d  probes/OCF/Lean/YiPFReachFold.lagda.md
310be78532d5f607f13be56fcc8e210faa3ef6a6a0e8eeee22a608d8be0d4f78  probes/OCF/Lean/YiPFReduce.lagda.md
```


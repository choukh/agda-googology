# 主线上的分级实例（基础） (YiGI)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十六批（“外部模型额度很充足，我们可以多线并行”）；外部模型，作者转发 |
| 前缀 | `YiGI` |
| 回报 | 尚未返回；作者转回后附在下面 |

## 简报原文（本机路径换成占位）

### 任务简报：主线上的分级实例（基础）（前缀 YiGI）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十六批六路之一（选项原文 "主线上的分级实例 (Recommended)"），与并行的其他各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。原主线 `YiRWFold` 的值定理保留作参照。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **抽象骨架**：`YiAbsGIface`（记录 `Graded`、`Doms`、`Laws` 模块、`Base`、`Keel`）、`YiAbsGSuff`（`Suff.Tower.K`、`endpoint`）、`YiAbsGEbo`（`ebo-end`，参照 `refᴱ`）、`YiAbsSimInst`（值 `𝕍`、`conv`、`toL-tree`）；带条件出口的版本 `YiExSuff`（`ExSuff.Exit₀`、`Keel⁻`、`TowerE.K`、`endpoint`）。
- **现有实例只在 F2 块上**：`YiAbsGFin`（`blkᶠ`、`foldᶠ`、`rowsᶠ`）、`YiASIface`（`gradedᴬ`、`domsᴬ`）、`YiDCRel.gradedᴰ`、`YiMHFin.gradedᴴ`、`YiExInst.exitᶠ`。YiMH 回报指出 "精简块没有 `Graded` 实例"。
- 主审的总概率评估（`probes/Survey/GoalOdds.md` 第八份）把 "组装：精简块上的分级实例、龙骨与终点" 列为一步，依据就是这个缺口。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：为精简块加最小比较表（`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiTBRow.ψ` 配 `rbᶻ`）写出 `Block`、`Fold`、`Rows` 的实例骨架，确认类型正确（层号是 `YiRWBlock.L`，各层的树 `Tr`，折叠带 `Ok`、表与底）。若记录的字段与精简块的折叠签名对不上，先停下回报，写清是哪个字段。
1. **实例**：`Block`、`Fold`、`Rows` 的完整实例；`Graded` 实例（关系取遗传封闭的族 `YiHCRel.Mᴴ`，可先对有限读回层号，其余层号上的关系作参数）；`Doms`。
2. **龙骨与出口**：用主线的塔 `tw n` 与标准底填 `YiExSuff.ExSuff.Keel⁻` 的各字段（`tw`、`κ₀`、`rd-tw0`、`tw-step`、`gl`、`b₀`、`w₀`、`β₀`、`K₀`、`gb`、`wl`、`bd`、`gx`）；照 `YiExInst` 给出主线上的 `Exit₀`。
3. **组装成一条条件定理**：在实际主线上陈述并编译 "律 `Leaf`、`Lift`、`LowKeep`（主线实例）与出口条件 → 终点闭项 `EBOᶻ` 的值不低于 EBO 参照"（经 `TowerE.K`、`endpoint`、`ebo-end`）。前提写成具名的假设，越少越好；每条前提说明现有哪些文件已部分实填它。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiGI`（模块名 `OCF.Lean.YiGI…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiCD`、`YiDD`、`YiKQ`、`YiSP`、`YiNX`、`YiXV`、`YiVF`）。定义接口实例的文件若只用树与折叠，用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包；读记号的文件标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有九路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
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



## 本会话主审复核（2026-11-14）

5 件，322 同口径代码行。主审逐件删自身接口、5G 冷编均 0，各仅自身 Checking；禁用构造、洞、本机路径与 Funext 命中 0。读过全部记录、R/Rd 互递归、双 Keel⁻、Ex 条件、终点逐支上界与 eboᵍ。blk/fold/rows 与两份龙骨实填；条件值定理落在实际 EBOᶻ。三全域律与全塔出口的联合可满足性未证，规范局部实例不能充作全域见证。YiGIBlock 导入闭包全域审计本地 10 件、记号禁用表命中 0；其余四件明确为验收文件。

## 回报原文（本会话执行）

### YiGI 完整回报（2026-11-14）

#### 1. 判决、范围与问题表

对纲领与目标：没有修改树、折叠、合法性或旧文件。精简主线 `YiTBRow.ψ` 配 `YiMTTab.rbᶻ` 已接入抽象分级框架，主线闭项仍是 `twᶻ n`、`EBOᶻ`。本路提供的是外部验收关系与条件组装，不声称树已经自足，也不把条件下界计作无条件强度提升。

第 0 步通过：临时 `YiGIMin.agda` 的 `Block`、`Fold`、`Rows` 完整字段检查退出 0，首个文件在开始后的前几次操作中完成，满足 30 分钟要求；该次 Agda 总 elapsed 1.873 秒。折叠的 `Bs` 携带 `Ok`、表 `Rb` 与原底 `Base`，`Bt` 取非零树 `Tr⁺`，没有字段签名不匹配导致的停止。

第 1 步：`Block`、`Fold`、`Rows`、`Graded`、`Doms` 均已实填。关系在全层号 `L` 上互递归，每层使用 `YiHCRel.Mᴴ`，槽位与孩子递归回同一族；槽位余尾用新读法 `Rd`。六条生成律 `Zero`、`Succ`、`Lim`、`Weak`、`Node`、`Emb` 实填。**没有证明这个新族在有限层等于 `YiHCFam.M`**；原有限族的高层保持定理不能直接搬用。记录的 `cl` 固定采用 ψ₀，本路只使用朝零层的 `LowKeep`，不主张 `SelfKeep` 或 `UpKeep`。

第 2 步：标准底的 `keelᵍ : Keel⁻` 全部 13 个字段已实填，`tw` 逐字是主线塔，起点 `κ₀ = []`。同时实填 `keelᴱ`：同一塔、同一路径与表，底与起点取 `EBOᶻ` 各支实际继承的折叠。这些继承底的 Ω 下界来自现有 `YiTBFam.ψ-⊵`。`exitᵍ : Exit₀` 调用现有 `YiHCRel.exitᴴ`，条件为推导上的 `Exᴴ`。

第 3 步：`eboᵍ` 已编译，四个具名前提为 `lf : Leaf`、`li : Lift`、`lk : LowKeep`、`ex : Assembly.ExitCondition lf li lk`；结论逐字是 `toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`。经 `TowerE.K`、`TowerE.endpoint`，并按 `YiAbsGEbo.ebo-end` 的逐行论证接到 EBO 参照。**三条全域律与全塔出口条件的同时可满足性仍未证明**；有编译的规范实例，不把它们冒充全域前提的实例。

| 问题 | 精确位置、已有实填与范围 | 档 |
|---|---|---|
| `Leaf` 全域未证 | `YiGIEnd.eboᵍ` 的 `lf`。`YiGICheck.rd-fin`、`leaf-fin` 对所有有限读回层 n 给出指定读法与对应 Ω 树关系；没有处理任意 `Rd` 推导。来源 `YiHCFam.Mβ` 已读，改槽位余尾后在本路重编。 | 具名未证假设；局部实例为编译定理 |
| `Lift` 全域未证 | 同处 `li`。`YiGICheck.lift-start` 是零层 Ω 树对下标 1 的指定实例。`YiLTLift.lift-red`、`lift-ω` 等已读，但其 `Q`/孩子关系不是本路新族，未声称直接填入本接口。 | 具名未证假设；指定实例为编译定理 |
| `LowKeep` 全域未证 | 同处 `lk`。`YiGICheck.low-zero` 对零层任意输入树与底值实填，直接引用 `YiLTFold.Qu`。`YiLTFold.LF` 等的高层关系是旧有限族，尚无本路转换。 | 具名未证假设；零层情形为编译定理 |
| 全塔 `Exᴴ` 未证 | `Assembly.ExitCondition = ∀ n → H.Exᴴ (T.folded lk n)`。`fold-start`、`fold-start-ex` 给首个主线折叠输出的一份推导及出口证书；未证明它就是任意传入 `lk` 所产生的证明。 | 具名未证假设；指定推导为编译定理 |
| 新关系的有限族一致性未证 | `YiGIRel.Nu` 用低层 `Rd`，原族用指定自然数等式；没有偷用类型不一致的旧律。 | 未提供定理，不作路线否定 |

没有有限数值采样结论；`leaf-fin` 是对所有自然数 n 的编译定理。没有否定路线、没有把任何障碍归到某堵已知墙。

#### 2. 文件、冷编与内存

冷编含义：逐个删除该文件自己的 `.agdai`，依赖保持缓存；不使用 `--ignore-interfaces`。每次只运行一个 Agda，均带 `+RTS -M5G -s -RTS`。各日志恰有一条本模块 `Checking` 行。代码行口径为 Agda 代码块内非空、非整行注释行（含导入和选项）；另列物理总行。

| 文件 | 代码行 / 总行 | 冷编退出码 | maximum residency（bytes） | total memory in use（MiB） | 冷编日志 |
|---|---:|---:|---:|---:|---|
| `OCF.Lean.YiGIBlock` | 56 / 78 | 0 | 161,905,576 | 282 | `<实验目录>/YiGIBlock-cold.log` |
| `OCF.Lean.YiGIRel` | 67 / 90 | 0 | 1,085,653,184 | 1821 | `<实验目录>/YiGIRel-cold.log` |
| `OCF.Lean.YiGIInst` | 69 / 91 | 0 | 1,259,673,360 | 2263 | `<实验目录>/YiGIInst-cold.log` |
| `OCF.Lean.YiGIEnd` | 52 / 73 | 0 | 1,397,618,792 | 2468 | `<实验目录>/YiGIEnd-cold.log` |
| `OCF.Lean.YiGICheck` | 78 / 103 | 0 | 1,469,121,104 | 2555 | `<实验目录>/YiGICheck-cold.log` |

`YiGIBlock` 是唯一不读记号的实例文件；`python3 probes/Survey/scripts/importclosure.py OCF.Lean.YiGIBlock`（没有 `--only` 缩窄）退出 0，闭包本地模块 10 个、禁用表命中 0。日志见 `<实验目录>/YiGIBlock-importclosure-final.log`。其余四文件均在文首标明验收文件。

最终自查：五文件禁用构造命中 0、本机路径命中 0；没有公设、洞、停机/正性指示、K、函数外延参数或无关投影选项。机器可读记录见 `<实验目录>/YiGI-audit.json`。内存数是 RTS 报告，未称作系统 RSS；并行环境的时间不用于性能比较。

#### 3. 定理表与逐字陈述

以下表列主要结果；后附从定稿源码直接提取的签名，保留限定名与隐式参数。`Leaf`、`Lift`、`LowKeep` 均指 `Laws gradedᵍ domsᵍ` 的命题。

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `blkᵍ`、`foldᵍ`、`rowsᵍ` | 精简主线完整填入三个记录 | `YiGIBlock` | 编译实例 |
| `rd-child`、`rd-add` | 层号读法可进入孩子，并可在左边加任意前缀；不按塔阶段定制 | `YiGIRel` | 编译定理 |
| `rd-tw0`、`tw-step` | 填出原主线塔的读法起点和推进 | `YiGIRel` | 编译定理 |
| `gradedᵍ`、`domsᵍ` | 全层关系与规范量化域的记录 | `YiGIInst` | 编译实例 |
| `exitᵍ` | 带 `Exᴴ` 的零层关系推出值下界 | `YiGIInst` | 编译实例 |
| `keelᵍ`、`keelᴱ` | 标准底与终点各支继承底的两份塔记录 | `YiGIInst` | 编译闭项 |
| `standard-closed` | 标准塔记录的闭项逐字等于 `twᶻ n` | `YiGIEnd` | 编译定理 |
| `omega-kt`、`row-eq` | 起点取 0 后，第 n 行恰是 `EBOψ n` | `YiGIEnd` | 编译定理 |
| `upperᴱ` | 各支的实际闭项低于原 `EBOᶻ` | `YiGIEnd` | 编译定理 |
| `Assembly.Kᴱ`、`endpoint`、`ebo-end`、`eboᵍ` | 三律和具体折叠推导的出口条件，推出原终点的 EBO 值下界 | `YiGIEnd` | 带具名假设的编译定理 |
| `rd-fin`、`leaf-fin` | 任意有限读回层的指定读法与 Ω 树关系 | `YiGICheck` | 编译定理 |
| `lift-start` | `Lift` 在零层 Ω 树、下标 1 的实例 | `YiGICheck` | 编译定理 |
| `low-zero` | 当前关系与折叠上朝零层的保持，在源层也是零时成立 | `YiGICheck` | 编译定理 |
| `fold-start`、`fold-start-ex` | 原主线第 0 项的折叠输出有关系推导及出口证书 | `YiGICheck` | 编译闭项及定理 |
| `zeroᵍ`、`succᵍ`、`limᵍ`、`weakᵍ`、`nodeᵍ`、`embᵍ` | 全层关系的六条生成规则成立 | `YiGICheck` | 编译定理 |

##### 从定稿源码提取的签名

`OCF.Lean.YiGIBlock`：

```agda
blkᵍ : Block

foldᵍ : Fold blkᵍ

rowsᵍ : Rows blkᵍ foldᵍ
```

`OCF.Lean.YiGIRel`：

```agda
  R : (ℓ : L) → E.T → Tr ℓ → Set

  Low : (ℓ : L) (p : Pos ℓ) → E.T → Br ℓ p → Set

  Nu : (ℓ : L) (p : Pos ℓ) → E.T → Set

  Rd : L → E.T → Set

rd-child : ∀ s h c {ν} → Rd (h c) ν → Rd (nd s h) ν

  rd-add : ∀ a b {ν} → Rd b ν → Rd (a ⊕ b) ν

rd-tw0 : Rd (tw 0) []

tw-step : ∀ n {ν} → Rd (↑ (tw n) (proj₁ (O.Ωt (tw n)))) ν → Rd (tw (suc n)) ν
```

`OCF.Lean.YiGIInst`：

```agda
Bdᵍ : ∀ {ℓ j} → Bsᵍ ℓ → j P.≤ ℓ → O.Tr⁺ j → E.T → Set

gradedᵍ : Graded blkᵍ foldᵍ rowsᵍ refᴱ 𝕍

domsᵍ : Doms blkᵍ foldᵍ

exitᵍ : Exit₀

keelᵍ : Keel⁻

startᴿ : GR.R zero (E.natT 1) (proj₁ (O.Ωt zero))

start-ex : H.Exᴴ startᴿ

baseᴱ : ∀ n → F.Base (tw n)

betaᴱ : ∀ n → O.Tr⁺ zero

keelᴱ : Keel⁻
```

`OCF.Lean.YiGIEnd`：

```agda
standard-closed : ∀ n → Keel⁻.twc keelᵍ n ≡ MT.twᶻ n

omega-kt : ∀ n → E.Ωt (Keel⁻.kt keelᴱ n) ≡ E.ΩTower n

row-eq : ∀ n → Keel⁻.row keelᴱ n ≡ E.EBOψ n

upperᴱ : ∀ n → K.readRW (Keel⁻.twc keelᴱ n) ≼ K.readRW MT.EBOᶻ

transport-tree : ∀ {a b} (e : a ≡ b) (h : E.HC a)
  → toL (ET.tree h) ≼ SI.E.tree (subst SI.E.HC e (SI.conv h))

hs : ∀ n → SI.E.HC (Keel⁻.row keelᴱ n)

reference : toL ET.EBO-tree′ ≼ L.lim (λ n → SI.E.tree (hs n))

  ExitCondition : Set

    Kᴱ : ∀ n (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)

    endpoint : L.lim (λ n → SI.E.tree (hs n)) ≼ K.readRW MT.EBOᶻ

    ebo-end : toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ

eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk)
  → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
```

`OCF.Lean.YiGICheck`：

```agda
rd-fin : ∀ n → GR.Rd (fn n) (E.natT n)

leaf-fin : ∀ n → GR.R (fn n) (E.Ωt (E.natT n)) (proj₁ (O.Ωt (fn n)))

lift-start : GR.R zero (E.natT 1) (proj₁ (O.Ωt zero))
  → GR.Rd (↑ zero (proj₁ (O.Ωt zero))) (E.natT 1)

low-zero : (b : Bsᵍ zero) (β : O.Tr⁺ zero) (t₀ : E.T) → Bdᵍ b P.self β t₀
  → ∀ {a x} → GR.R zero a x
  → GR.R zero (E.ψ [] (t₀ ++ a) ∷ []) (proj₁ (ψᵍ zero b zero P.self β x))

raw-start : K.M⁰ (E.EBOψ 0) (proj₁ (ψᵍ zero (tt , tt , F.B₀ zero) zero P.self (O.Ωt zero) (proj₁ (O.Ωt zero))))

fold-start : GR.R zero (E.EBOψ 0) (proj₁ (ψᵍ zero (tt , tt , F.B₀ zero) zero P.self (O.Ωt zero) (proj₁ (O.Ωt zero))))

fold-start-ex : H.Exᴴ fold-start

zeroᵍ : Zero

succᵍ : Succ

limᵍ : Lim

weakᵍ : Weak

nodeᵍ : Node

embᵍ : Emb
```

`Assembly` 的模块参数与出口条件定义逐字为：

```agda
module Assembly (lf : Leaf) (li : Lift) (lk : LowKeep) where
  module T = TowerE lf li keelᴱ

  ExitCondition : Set
  ExitCondition = ∀ n → H.Exᴴ (T.folded lk n)
```

没有这四个前提的闭项。上述 `eboᵍ` 是条件定理，不是 `toL EBO-tree′ ≼ readRW EBOᶻ` 的无条件证明。

#### 4. 第一个障碍，精确到引理

完成记录组装后，第一个未填的数学接口是 `Laws.Leaf gradedᵍ domsᵍ` 的全域版本：从任意 `YiGIRel.Rd ℓ ν` 推到 `YiGIRel.R ℓ (E.Ωt ν) (proj₁ (Ωt ℓ))`。当前 `leaf-fin n` 只消费指定有限读法的结论，未给任意 `Rd` 证明的归纳保持。`Lift` 和 `LowKeep` 的全域情形随后仍未证；没有编译的否定，故只能说这些保持未实填，不能说路线被否定。

`Rd` 与关系是验收侧的新设计；它们还没有语义适切性的独立总定理。全域三律的联合可满足性与此有关，不能由记录通过类型检查或几个规范实例推出。

#### 5. 设计选择、偏离、事故与引用范围

- 允许先做有限层并把其余层关系作参数；本路选择了全层互递归的 `Mᴴ` 族和外部读法 `Rd`。这没有改主线定义，但增加了一个新的验收关系候选；其高层正确性仍由具名前提承担。请把它按候选记录，不能把旧 `YiHCFam` 的结论自动归到它名下。
- 既有 `YiAbsGEbo.ebo-end` 要求无条件 `Base` 且起点为 1，不能直接用于 `Exit₀`。本路没有修改旧接口，而在新文件中按原证明改接 `TowerE.endpoint`，起点取 0；`row-eq` 检查了准确索引。终点使用实际支底，避免引入一个尚未证出的标准塔 `Into` 前提。
- 临时检查顺序：先完成记录与两份龙骨的闭项检查，再编条件组装，最后补全六生成律及三保持律的规范实例检查。三全域律及全塔 `Exᴴ` 的联合可满足性没有完成，不能把规范检查报告成它的替代。
- 未触发停止条件：没有 5G 堆耗尽、超时或内部错误；没有同一数学方案两次重新设计仍过不了检查器。出现的 42 均是名称、具体来源或隐式参数问题，已在新文件范围内修正。

| 日志 | 退出码 | 事故及修正 |
|---|---:|---|
| `YiGIRel.log` | 42 | 自定义 `R` 与导入 `Sg.R` 撞名；`open B hiding (R)`，数学定义未改 |
| `YiGIRel-2.log` | 0 | 临时全层关系及 `tw-step` 通过 |
| `YiGICheck.log` | 42 | 检查器不能从变量 `fn n` 看出 `Mᴴ` 的头；按实际层号包装现有 `mw` 为 `rw-weak` |
| `YiGICheck-2.log` | 42 | 误用兄弟孩子折叠的 `YiHCFold.Qu`；检索后改用已有比较表折叠的 `YiLTFold.Qu`，没有重证 |
| `YiGICheck-3.log` | 42 | `raw-start` 的参照前缀与源项经非单射头推不出；显式写 `{t = []}`、`{s = E.natT 1}` 及构造子的下标 |
| `YiGICheck-4.log` | 0 | 所有规范检查及六条生成律通过 |

所有引用的接口、源码和用于复制/改写的证明均已实际读取；未凭转述引用一个尚未看的定理。简报所述主审历史判断与 GoalOdds 背景未独立复核，未作为本路定理依据。没有读外部论文、没有外部网络调查、没有派子路、没有提交或推送。只新建下列五个 YiGI 文件，README、LOG、台账、旧文件、src、archive 均未写入。

#### 6. 全部交付与实验路径

仓库新增源码：

- `<仓库>/probes/OCF/Lean/YiGIBlock.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGIRel.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGIInst.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGIEnd.lagda.md`
- `<仓库>/probes/OCF/Lean/YiGICheck.lagda.md`

临时目录：`<实验目录>`。全部临时纯 Agda 源码：

- `<实验目录>/YiGICheck.agda`
- `<实验目录>/YiGIEnd.agda`
- `<实验目录>/YiGIInst.agda`
- `<实验目录>/YiGIMin.agda`
- `<实验目录>/YiGIRel.agda`

库文件：`<实验目录>/libraries`。全部日志与审计文件：

- `<实验目录>/YiGI-audit.json`
- `<实验目录>/YiGIBlock-cold.log`
- `<实验目录>/YiGIBlock-importclosure-final.log`
- `<实验目录>/YiGIBlock-importclosure.log`
- `<实验目录>/YiGIBlock.log`
- `<实验目录>/YiGICheck-2.log`
- `<实验目录>/YiGICheck-3.log`
- `<实验目录>/YiGICheck-4.log`
- `<实验目录>/YiGICheck-cold.log`
- `<实验目录>/YiGICheck.log`
- `<实验目录>/YiGIEnd-cold.log`
- `<实验目录>/YiGIEnd.log`
- `<实验目录>/YiGIInst-2.log`
- `<实验目录>/YiGIInst-cold.log`
- `<实验目录>/YiGIInst.log`
- `<实验目录>/YiGIMin.log`
- `<实验目录>/YiGIRel-2.log`
- `<实验目录>/YiGIRel-cold.log`
- `<实验目录>/YiGIRel.log`

完整回报：`<回报原文>`。上述源码已定稿，不再改动，交主审独立冷编复核。


## 后续核定（2026-11-14，YiLL）

YiLLLeafNeg.noLeaf 已由主审独立冷编通过：本实例的全域 Leaf 为假，Ok 限制仍不足。因此这里 eboᵍ 的四个前提在当前全域实例上不能同时满足，不能把该条件组装当作可实填的主线下界方案。原编译定理保留；规范塔域上的 Leaf 未被否定。

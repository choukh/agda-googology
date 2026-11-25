# YiS1 第1站保持连出口：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | 继承执行方模型；接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；本文由原始简报与完整回报封装留档，表内0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiS1Shape、YiS1Exit、YiS1Low、YiS1Accept |
| 文件前缀 | `YiS1` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiS1 第1站实际保持连出口与值下界独立复核” 一节 |
| 主审复核后的一句结论 | 四件独立冷编全0；LowAt1及Kᴱ1无外部前提，整族Kᴱ仍未填。 |

## 简报原文

### 任务简报：第 1 站的保持连出口（数学）（前缀 YiS1）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十一批四路之一（选项原文 "第 1 站的保持连出口 (Recommended)"），与本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **旧的组装**（主审复核过；它的全域 Leaf 前提已被 `YiLLLeafNeg.noLeaf` 否定，所以它本身什么也没说）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- **当前的组装**（主审复核过）：`YiCNAccept.ebo-rest : LeafRest → LiftRest → LowRest → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，三族前提是沿龙骨的具体陈述（`YiCNKeel` 的 `LeafAt`、`LiftAt`、`LowAt`，分别从第 3、2、1 站起未证）。
- **共同的目标陈述**（主审 2026-11-15 在临时文件里编译通过，源码留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC3Ends.agda.txt`；正式文件里请自己重写一遍并编译）：
  ```agda
  open ExSuff gradedᵍ domsᵍ using (Keel⁻)        -- YiExSuff, YiGIInst
  Kᴱ : ℕ → Set
  Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
  ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  ebo-from-stations k = ≼-trans reference (l≼ (λ n → ≼-trans (k n (hs n)) (upperᴱ n)))   -- reference, hs, upperᴱ 取自 YiGIEnd
  ```
  即终点等于 "对一切 n，第 n 站（`Keel⁻.row keelᴱ n` 即 `EBOψ n`，`Keel⁻.twc keelᴱ n` 是 `EBOᶻ` 的第 n 支）的值下界"。Leaf、Lift、保持这几族律只是证它的一种办法。已知的值：`YiMTValue.k1ᶻ : Kᶻ 1`（对 `twᶻ 1`），`YiMTValue.Kᶻ n = (h : HC (E.ψ [] (E.Ωt (ΩTower n)) ∷ [])) → Rt h ≼ readRW (twᶻ n)`；`YiVTTw2Hi.tω≼twᶻ`（塔第 2 项起 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))）。`Keel⁻.twc keelᴱ n` 与 `twᶻ n` 的关系请自己核对（`keelᴱ` 的底取 `EBOᶻ` 各支实际继承的折叠）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **目标**（`YiCNKeel` 第 33–36 行，逐字）：
  ```agda
  LowAt n = GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n))) → Σ (GR.R B.zero (row n) (twc n)) H.Exᴴ
  ```
  `low0 : LowAt 0` 已证。YiCN 回报（`probes/Survey/Reports-2026-11-12/YiCN.md`）："LowAt1 尚缺在实际 baseᴱ1/betaᴱ1 上的关系推导与 Ex 对，不能把 B₀ 版本或单纯值下界直接当实例"；建议（判断）"直接为指定输出构造该对而不是先证全域保持"。
- **出口条件**：`YiHCRel.Exᴴ` 只在 `mc` 结点上要求两项都是标准形、较大者可数；`¬Mono`、`¬Exit′`（`YiMXNote`、`YiMXNeg`）说明不能去掉这个条件。
- **可用的已有结果**（先检索，能复用就复用）：`YiPCKeel.k1ᴾ : Lift₁ᴾ → M⁰ (E.EBOψ 2) (twᶻ 1)`（不读记号的域 `Pre` 上）；`YiLTLift`（`Q`、`StepS`、`lift-red`）；`YiPJQ.qω+1`、`YiPJLimStep`；`YiNXFull.Out.exit-low0`；`YiMXEnd.LowKeepᴱ`；`YiMTValue.k1ᶻ`（值）。

#### 要做的（按序）
0. **最小检查**，在临时目录：把 `keelᴱ` 的第 1 行（`row 1`、`twc 1`、底、起点 β、路径）展开出来，确认 `LowAt 1` 的类型，并核对 `twc 1` 与 `twᶻ 1` 的关系。不成立就停下回报。
1. **直接构造**：不先证全域保持，直接为 `twc 1` 构造 `GR.R B.zero (row 1) (twc 1)` 的推导，并让每个 `mc` 结点满足标准形条件（`Exᴴ`）。可以照 `k1ᴾ` 的链与根行，换成实际的底。
2. 得到 `LowAt 1` 后，经出口给出 `Kᴱ 1`（与 `k1ᶻ` 对照）。做不到就交第一个挡住的地方：哪个 `mc` 结点不是标准形，或哪个孩子 c 要 `Lift₁`，精确到项。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiS1`（模块名 `OCF.Lean.YiS1…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiFR`、`YiSX`、`YiNL`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库的 .agda-lib 路径>
  <cubical 的 .agda-lib 路径>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 8G**：同时最多五路在编译，机器共 64G。若某个文件确实要超过 8G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽（先在回报里说明）；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

### YiS1 完整回报（待主审独立复核）

#### 1. 判决与问题表

对纲领与目标的意义：本路只新增第四层验收定理，树、折叠、合法性与闭项定义均未改。实际第 1 站的保持连出口已经构造出来，不再依赖全域保持或整族 `Lift₁`。新增的是局部律 `LowAt 1` 的实填及其值出口；未给更高站或无条件 EBO 强度。全部正式文件都是读记号的验收文件，不把它们称作树自足的定义。

第 0 步在私有临时文件 `YiS1Check0.agda` 完成，第一次编译退出 0，RTS elapsed 15.378 秒，最大驻留 1,576,238,512 bytes；首次编译在派发后 30 分钟内。具体核对：

- `row 1 = ψ [] (Ωt (natT 1)) ∷ []`，即 ψ₀(Ω₁)。
- 底为 `baseᴱ 1 = YiMTValue.B1ᶻ`，起点为 `betaᴱ 1 = YiMTValue.β1ᶻ`，路径为 `z≤ (tw 1)`。
- `twc 1 = YiMTValue.brᶻ 1`，是终点第 1 支。它与使用 `B₀` 和 `Ωt zero` 的 `twᶻ 1` 不是相等的树：`actual≢standard` 已编译；没有据此声称序数值不相等或比较其值。
- `LowAt 1` 的输入与输出按原定义逐字展开，见 `YiS1Shape.low1-type`。
- `YiMTValue.k1ᶻ` 的目标是标准闭项 `twᶻ 1` 上的 `EBOψ 2`；本题实际 `row 1` 为 `EBOψ 1`。两者的底与参照项都不同，故没有拿 `k1ᶻ` 替代本题的关系推导。

第 1 步完成：`YiS1Low.folded¹` 是无外部前提的实际关系与出口条件对；`YiS1Low.low1 : CN.LowAt 1` 忽略输入关系，直接返回该对。第 2 步完成：`YiS1Accept.k1ᴱ : Kᴱ 1` 通过原出口 `exitᵍ` 给出值下界。共同目标 `ebo-from-stations` 已在正式文件中重写并编译，保留整族逐站值前提。

| 问题 | 位置 | 结果与档 |
|---|---|---|
| 实际底与标准底能否混用 | `YiS1Shape.actual≢standard` | 不能当同一闭树；编译定理，不是序数值比较 |
| 实际链第 1 点的形状 | `YiS1Low.index1-shape` | `idx 1 ≡ proj₁ (next⁺ (next⁺ (Ωt zero)))`；编译定理 |
| 实际输出的关系和出口 | `YiS1Low.folded¹`、`low1` | 已给闭构造；编译定理 |
| 第 1 站值 | `YiS1Accept.k1ᴱ` | 已从同一推导过出口；编译定理 |
| 全部站的值 | `YiS1Accept.ebo-from-stations` 的前提 | 本路只实填 n=1；其他站不在本路交付内 |

没有有限样本代替证明的结果。形状等式为精确编译等式；树不等为由布尔观察推出的编译否定，不是否定路线。

#### 2. 文件表与自身冷编

代码行口径：Agda 代码块中非空、非注释行，含 OPTIONS、模块头与导入。正式文件共 185 行，均为验收层。

| 文件 | 代码行 | 冷编退出码 | RTS 最大驻留 bytes | RTS 总占用 MiB | elapsed 秒 | Checking |
|---|---:|---:|---:|---:|---:|---|
| `YiS1Shape` | 55 | 0 | 1,543,375,648 | 2575 | 15.628 | 1，只有自身 |
| `YiS1Exit` | 30 | 0 | 1,463,462,312 | 2494 | 14.482 | 1，只有自身 |
| `YiS1Low` | 75 | 0 | 1,353,832,048 | 2384 | 15.036 | 1，只有自身 |
| `YiS1Accept` | 25 | 0 | 1,554,797,592 | 2585 | 15.733 | 1，只有自身 |

冷编操作只删除各件自身的字面接口路径，依赖保持热；从未使用 `--ignore-interfaces`。每路同时一个 Agda，每次均 `+RTS -M8G -s -RTS`。逐件日志为 `<实验目录>/<模块名>-cold.log`，退出码另存对应 `.exit`；源码冻结见 `<实验目录>/YiS1-freeze.sha256`。表中的最大驻留是 GHC RTS 的 maximum residency，不冒称操作系统 RSS。

#### 3. 定理表与逐字陈述

以下简称与源码相同：`CN=YiCNKeel`，`GR=YiGIRel`，`H=YiHCRel`，`K=YiKVRel`，`MT=YiMTTab`，`SI=YiAbsSimInst`；`Keel⁻` 来自 `ExSuff gradedᵍ domsᵍ`。

| 名字 | 白话 | 文件 | 档 |
|---|---|---|---|
| `row1`, `base1`, `beta1`, `path1`, `closed1`, `low1-type` | 核对实际第 1 站的参数与目标 | `YiS1Shape` | 编译定理 |
| `actual≢standard` | 实际闭树不是标准底的闭树 | `YiS1Shape` | 编译定理 |
| `ex-upL0`, `ex-right` | 已有取第 0 支与右加推导传递出口证据 | `YiS1Exit` | 编译定理 |
| `index1-shape` | 实际根链第 1 点是两次 next | `YiS1Low` | 编译定理 |
| `folded¹`, `low1` | 实际第 1 站的关系与出口条件已实填 | `YiS1Low` | 编译定理，无外部前提 |
| `k1ᴱ` | 实际第 1 站的序数值下界 | `YiS1Accept` | 编译定理，无外部前提 |
| `ebo-from-stations` | 全部逐站值下界推出终点下界 | `YiS1Accept` | 编译条件定理，整族前提未填 |
| `k1-standard` | 原标准塔第 1 项的值定理作对照 | `YiS1Accept` | 复用已有编译定理 |

主要陈述逐字如下；全部新定义与辅助定理的逐字签名另存 `<实验目录>/YiS1-statements.md`。

```agda
low1-type : CN.LowAt 1 ≡ (GR.R (B.tw 1) (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (B.tw 1))) → Σ (H.M⁰ (E.ψ [] (E.Ωt (E.natT 1)) ∷ []) (Keel⁻.twc keelᴱ 1)) H.Exᴴ)
actual≢standard : Keel⁻.twc keelᴱ 1 ≡ MT.twᶻ 1 → ⊥
index1-shape : idx 1 ≡ proj₁ (next⁺ (next⁺ (Ωt zero)))
folded¹ : Σ (GR.R zero (Keel⁻.row keelᴱ 1) (Keel⁻.twc keelᴱ 1)) H.Exᴴ
low1 : CN.LowAt 1
Kᴱ : ℕ → Set
Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
k1ᴱ : Kᴱ 1
ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
k1-standard : MV.Kᶻ 1
```

构造的关键：实际根链第 1 点 `idx 1` 是 `next⁺ (next⁺ 1)`；其孩子层取两次第 0 支到有限层 `fn 1`。在该有限层调用不带 `mc` 的 `YiTBFam.sΩ-LF`，用 `YiHCCheck.of⁰/ex-of⁰` 同时取得关系与出口；再用已有的 `YiLTLift.upL 0` 两次传回该孩子层，最后用已有 `YiHCRel.G⁰.m-cum` 的第 1 项传到根。`YiS1Exit` 只证明这几个已有推导的出口性质，未重证它们的关系保持结论。

前提的可满足性：`folded¹`、`k1ᴱ` 都是无外部前提的闭构造。`q1K` 的底条件在实际孩子底上由 `YiTBFam.ψ-⊵` 实填，起点由 `K.pos⁰` 从合法非零起点实填；路径由 `zp-z` 实填。`QEx q1`、`QEx q-idx` 分别有闭证据 `ex-q1`、`ex-q-idx`。`low1` 直接返回无条件闭对，故不靠输入前提可能为空而成立。终点条件定理的整族 `∀ n → Kᴱ n` 没有被本路宣称可满足；本路实填的只是 n=1，不以该组装声称达到 EBO。

#### 4. 第一个障碍

本题指定的第 1 站没有遗留障碍，`LowAt 1` 与 `Kᴱ 1` 均已给出；没有遇到非标准形的 `mc` 结点，也没有出现需要 `Lift₁` 的孩子。更高站没有继续尝试，不能把本路的有限取支证明外推到它们。

#### 5. 偏离、事故、引用与停止条件

- 没有改题、改树、改折叠、改合法性、改已有定义。只新增四个 `YiS1` 前缀文件；README、LOG、台账、留档、其他路文件未改。未提交、未推送、未装包、未开子路。
- 相对简报所建议的 `k1ᴾ` 根行方案，本路在第 0 步确认实际 `row 1` 的目标较低后，仍针对原目标直接选根链第 1 项；没有先做全域保持。这里记录的是证明组织的选择，没有换题。
- 临时开发的首个失败为误写私有导入名 `TF.OKB`，改从其原模块导入后通过。补出口时一轮未解隐式参数（`g`、`q`）失败，显式写出两层分支族及参数后通过。这两处都是代码与参数修正，没有重新设计数学接口。首次完整关系连出口临时编译退出 0。
- 曾尝试只读进程状态，运行环境拒绝 `ps`；没有请求提权或绕过，改读自身编译会话。该事故未影响数学检查。
- 未发生 8G 堆耗尽、超时、Agda 内部错误；第 0 步成立；同处两次实质重新设计停止条件未触发。
- 只读了 `YiPCKeel`、`YiMTValue`、`YiCNKeel`、`YiGIInst`、`YiGIEnd`、`YiGIRel`、`YiHCRel`、`YiHCCheck`、`YiLTLift`、`YiTBFam`、`YiLTKid` 等相关声明或片段；证明中用的关键引理都读了代码与陈述。`YiNXFull`、`YiPJQ` 等仅检索相关片段，未把它们作为本路证明依赖。简报转述的外部独立复核状态未由我重新验证。
- 已读 AGENTS.md、手册 §4 与当前 README 导航；没有外部文献或网络调查。`YiMTValue.k1ᶻ` 是复用依赖，没有重证其旧证明；本路交付的自身冷编也不等于独立从头复核所有依赖。
- 禁用构造与本机路径扫描在四个正式文件中均为 0；选项只有规定的 `--safe --without-K --lossy-unification` 加库既有选项。冻结后没有继续修改源码。

所有结果等待主审按冻结表独立复核，复核前不算交付。

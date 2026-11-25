# YiFR 先读定义的独立审查：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | gpt-6-astra，high，独立新上下文 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiFRStations、YiFRStep、YiFRKeep |
| 文件前缀 | `YiFR` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiFR 独立计划、实际前三站与真实链归约复核” 一节 |
| 主审复核后的一句结论 | 干净阶段0先封存；三件独立冷编0，Kᴱ0/1/2与链第0项成立；Tail整族未填，V173只补后继部分。 |

## 简报原文

### 任务简报：先读定义的独立审查：对一切站的值下界（前缀 YiFR）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十一批四路之一（选项原文 "先读定义的独立审查 (Recommended)"），与本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **共同的目标陈述**（主审 2026-11-15 在临时文件里编译通过，源码留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC3Ends.agda.txt`；正式文件里请自己重写一遍并编译）：
  ```agda
  open ExSuff gradedᵍ domsᵍ using (Keel⁻)        -- YiExSuff, YiGIInst
  Kᴱ : ℕ → Set
  Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
  ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  ebo-from-stations k = ≼-trans reference (l≼ (λ n → ≼-trans (k n (hs n)) (upperᴱ n)))   -- reference, hs, upperᴱ 取自 YiGIEnd
  ```
  即终点等于 "对一切 n，第 n 站（`Keel⁻.row keelᴱ n` 即 `EBOψ n`，`Keel⁻.twc keelᴱ n` 是 `EBOᶻ` 的第 n 支）的值下界"。已知的值：`YiMTValue.k1ᶻ : Kᶻ 1`（对 `twᶻ 1`），`YiMTValue.Kᶻ n = (h : HC (E.ψ [] (E.Ωt (ΩTower n)) ∷ [])) → Rt h ≼ readRW (twᶻ n)`；`YiVTTw2Hi.tω≼twᶻ`（塔第 2 项起 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))）。`Keel⁻.twc keelᴱ n` 与 `twᶻ n` 的关系请自己核对（`keelᴱ` 的底取 `EBOᶻ` 各支实际继承的折叠）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 本路的做法（务必照此顺序）
本路是独立审查：**先读定义，不先读我们的结论**。主审的经验（11-11）：多批只交条件归约之后，一路先读定义的审查约 290 行就给出了无前提的 BTBO 下界。

#### 要做的（按序）
0. **只读定义，写自己的计划**（在临时目录写一页以内的笔记，不进仓库）：
   - 树、层号与塔：`probes/OCF/Lean/YiRWBlock`（`L`、`Tr`、`tw`、`Λ`、`↑`、`⊕`）、`YiRWOps`、`YiRWPath`（`Ok`）、`YiRWFold`（`Base`）、`YiTBRow`（折叠 `ψ`，以及与它互递归的 `mono`）、`YiTBFam`（`ψ-⊵`）、`YiMTTab`（比较表 `rbᶻ`、`twᶻ`、`EBOᶻ`）、`YiGIInst`（`keelᴱ`）。
   - 参照一侧：`OCF/Align/EboLeanDef`（记号项、`ψ`、`Ω`、塔）、`EboLeanTree`（`HC`、`tree`、`EBO-tree′`）、`OCF/Align/Value`（`≼`）、`YiKVRel.readRW`。
   - 目标：上面的 `Kᴱ n` 对一切 n。写出你认为可行的证法（对 n 归纳要怎样的一步；需要关于折叠的哪些性质；哪一步读记号）。
1. **再对照已编译的否定**，检索这些名字读陈述，确认计划没有用到被否定的东西，必要时调整：`YiLLLeafNeg.noLeaf`、`YiSUNeg.no-step`、`YiSUBridge.no-whole`、`YiGTIndexNeg.no-frame₂`、`YiMXNote.¬Mono`、`YiMXNeg.¬Exit′`、`YiPFReachTotal.w-total-ok`、`YiCNDirectNeg.no-NuFromChild`，以及 `probes/OCF/Barrier.lagda.md`（壁垒定理）与 AGENTS "开新行前的先验检查" 里的 `obs→dec` 一族。
2. **编译计划的前几步**：`Kᴱ 0`；`Kᴱ 1`（先查能否由现有的 `k1ᶻ` 得到）；归纳一步的精确陈述；尽量往下证。
3. **挑战台账**：读 `probes/Survey/IdeaLedger.md`，挑出与 `Kᴱ` 有关、凭未编译的判断搁下的条目（状态写 "判断"、"暂停"、"未走通" 而没有编译否定的），至多三条，各用一个最小的编译检查重新看。
回报里先交第 0 步的计划原文（不改写），再交后面各步。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiFR`（模块名 `OCF.Lean.YiFR…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiS1`、`YiSX`、`YiNL`）。验收文件，文首标明。
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

### YiFR 阶段0独立证法计划

档位：纸面计划，尚无编译结论。目标是每站 Kᴱ，再推出 EBOᶻ 的序数值下界；不改树、折叠或证书，不宣称 FGH 比较。仅阅读指定提取材料及请求所得的直属定义补充。

1. **先核对两端。** 写 κ₀=[]、κₙ₊₁=Ωt κₙ，则 row n=ψ₀(Ωt κₙ)，与 EBOψ n 的塔指标一致。twc 使用 baseᴱ n、betaᴱ n；twᶻ 使用 B₀、Ωt zero，不能直接认作相等。由 cum、加法的 up 方程，cum FΛ n 应等于 up (pre n) n (Ωt(tw n))；再展开 ψ 的 inu 分支，得到其折叠值为 twc n。因此先编译读值层的逐点等式，把 readRW EBOᶻ 写成 lim (λ n → readRW(twc n))。这一步只读树定义。

2. **基站与归纳目标。** n=0 时 pre 0=zero，baseᴱ 0=B₀、betaᴱ 0=Ωt zero，twc 0 化为 next⁺(Ωt zero) 的树，按 HC 的各分支证明 row 0 的树值受它支配。裸 Kᴱ n 只给一个可数输出的比较，不足以直接应用于 tw(n+1) 的任意 Tr(tw n) 分支；归纳命题需增加实际回灌链的读回证据，以及层 tw n ⊕ ↑(tw n)c 上递归折叠的模拟。量化域先只包含规范 Ωt、实际迭代产生的 c、它们的子树和实际更新过的基底；不先要求一切合法树或所有路径等价。

3. **n→n+1 的一步。** 展开 Ωt(tw(n+1)) 的根 Ω 节点。目标层为 zero，Keep 无可保留的位置，node⁺ 取从 zero 开始的迭代回灌，再作累加极限。为每个参照基本列项构造一个链位置及值比较；链初项用实际基底支配 Ωt，后继项用递归折叠模拟，把输出重新读作下一次分支下标。随后用 ≼l 选该累加项，用 l≼ 合成参照极限。层 tw n ⊕ ↑c 的辅助归纳必须随 c 的构造子写出，不能从 Kᴱ n 本身跳过去。

4. **待证的折叠性质。** 零行保底、next⁺ 对参照后继行的有限重复支配、lim⁺ 的逐点模拟、累加项容纳单项，以及回灌链对应参照 γT 的一步。up 分支逐条保留真实路径、rbᶻ 结果、更新后的基底；特别检查 nothing 分支重置为 B₀ 后是否仍足以支持所选参照子项。若所需模拟无法由该分支给出，记录确切缺口，不把它补作公理，也不据纸面困难关闭路线。

5. **出口与记号边界。** 由各 Kᴱ n、第一步逐点等式和两次极限规则，给出 EBO 参照树 ≼ readRW EBOᶻ。记号只在 row/EBOψ 对齐、HC 与 fsn/fsT/γT 模拟、最终参考树的出口出现；树侧运算与闭项仍按原定义。首次编译依次做终点逐点桥、基站、首个回灌链步的小模块；本计划不把尚未构造的加强不变量称作已成立接口。


---

#### 阶段1–3回报

判决：不改前三层，指定 Kᴱ 的第0、1、2站已证；实际继承底把上一站送入下一站回灌链第0点。尚无全塔值定理或新增高于既有BTBO的具名强度。归纳正编号参照项的覆盖未走通，没有否定这条路线。

阶段0计划原文如上，SHA256：0ed818528ea3de4140e2e94fcde277b42fc2f0da08458a3744289d59c81f3dc0。只读了许可材料与补给定义；阶段0未运行Agda。阶段1后才读仓库、既有验收和否定，未回读受污染首轮计划。

##### 否定对照（读陈述后的判断）

| 已读定理 | 实际否定/证明的范围 | 对本计划的处理 |
|---|---|---|
| YiLLLeafNeg.noLeaf / noLeafOk | 任意Rd层号的全域Leaf，即使加Ok也假 | 不调用全域Leaf；本路已交结果直接用值关系 |
| YiSUNeg.no-step、YiSUBridge.no-whole | OK B不能保证非空前缀所需的槽位基底关系，补整支律仍假 | 链定义保留真实baseᴱ；未把Ω支配冒充前缀关系 |
| YiGTIndexNeg.no-frame₂ | fn2的两个槽位余尾同为0，但kp动作不同，不能统一为NodeFrame | 不要求NodeFrame或同余尾同动作 |
| YiMXNote.¬Mono、YiMXNeg.¬Exit′ | 非标准参照上的项序不保值，带mc关系没有无条件出口 | k0用不带mc的基础M⁰出口；其余站直接复用已有值界 |
| YiPFReachTotal.w-total-ok | 种子/前驱/孩子/任意合格底输出闭包的W在Ok层总化 | 未创建这样的输入域；链按实际n和实际基底固定 |
| YiCNDirectNeg.no-NuFromChild | 从任意孩子后继读法抽取下标层前驱读法为假 | 没有抽取这种字段；直接列每个实际链点的值义务 |
| Barrier.barrier | 精确初始段+Ω共尾元+有界三歧推出LPO | 不引入这样的下标序或三歧 |
| obs→dec / hand→wdec / branch→wdec / viaE→dec / full→dec | 可观察的同支/存在性派发律导出判定 | 没有修改派发或要求这些律；使用原kp/rbᶻ |

这些对照没有证明Tail可满足，也没有否定Tail。noLeaf等对照在本轮未重新冷编，仅读原陈述和证明；它们不是本路的新交付。

##### 结果与边界

- branch-form逐站核对twc就是EBOᶻ第n支的实际折叠。twᶻ的标准底不同，本路未证两者相等或不等。
- k0按基础M⁰出口；k1和k2利用已有btbo-br1ᶻ。k1ᶻ不能直接当作本题Kᴱ1：它指向EBOψ2且使用标准底。k2是本题ψ₀(Ω_Ω)下界，不是旧Kᶻ2。
- station-step是实际终点各支的值单调；它不比较不同层的槽位，也没有给参照升阶。
- Step.feed/out/chain逐字使用baseᴱ(suc n)、betaᴱ(suc n)。branch-upper给实际链分支在本站之下；prior-upper给上一站在本链第0点之下。row-zero对一切n证明参照第0项是上一行，合成start-match；start0实填其前提。
- Step.step只有条件归约。Step.Tail n要求每个正编号参照项有一个实际链点的值上界，整族没有实例。Tail0、Tail1也未构造；Kᴱ1/2来自既有BTBO界，不是由Tail归纳得来。Remaining和FirstMissing只是待证类型，不是其居留者。不把这些条件归约计作可实填接口或强度。
- ebo-from-stations按作者指定陈述重写、编译；全站前提未填。

##### 台账复查（只选一条）

V173：原Fin.Keep/Shift的任意推导版本未走通，没有整体否定。本次keep-suc证明Keep对m1封闭；gb0实填标准底；keep-one给非零左项suc zero实例（表r任意，因而可取实际rbᶻ）。这是编译定理，不是有限运行测试。没有证明mΩ/mU等剩余构造子的Keep，也没有证明实际塔回灌调用都落在此接口域，故V173仍不能改记为完整做成或已否定。

##### 第一个障碍

独立计划所说“实际回灌链的读回及带前缀模拟”没有构造成一般定理。归纳需要Remaining（∀n → Kᴱn → Step.Tail n），本轮没有居留者。若从已知Kᴱ2进攻下一未知站Kᴱ3，首先需要FirstMissing：row3第1基本列项在某个实际chain2点的out值之下。该参照项是ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})。这一项没有值证明，也没有否定；原n归纳计划的第0项成立，正编号项没有完成。

##### 文件和冷编

每个最终文件均删除自己的.agdai后编译；依赖使用已有接口。每次只有一个Agda，堆上限不超过8G；复核去重复后的YiFRKeep用-M5G冷编，其余两件保留原-M8G冷编。最终日志只有本文件Checking行。下表代码行包含空行，括号内为非空代码行。内存为RTS maximum residency，不当作进程RSS。

| 文件 | 代码行 | 冷编退出码 | maximum residency | RTS总内存 |
|---|---:|---:|---:|---:|
| probes/OCF/Lean/YiFRStations.lagda.md | 47 (44) | 0 | 1,469,538,872 bytes | 2538 MiB |
| probes/OCF/Lean/YiFRStep.lagda.md | 96 (89) | 0 | 1,714,155,192 bytes | 2952 MiB |
| probes/OCF/Lean/YiFRKeep.lagda.md | 42 (42) | 0 | 1,477,722,976 bytes | 2413 MiB |

##### 定理逐字陈述

以下均为编译定理；step、match→station、ebo-from-stations的未填前提按上文单列，不能读成无前提强度。Remaining与FirstMissing另列为待证陈述。

YiFRStations：

```agda
Kᴱ : ℕ → Set
Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
branch-form : ∀ n → Keel⁻.twc keelᴱ n ≡ proj₁ (TB.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (O.cum FΛ n))
branch-form zero = refl
branch-form (suc n) = refl
k0 : Kᴱ 0
k0 h = ≼-trans (tree-back h) (K.lower⁰ (K.G⁰.m-next (O.Ωt B.zero) refl (λ n → refl) (K.m1 refl K.mz)) (back h))
k1 : Kᴱ 1
k1 h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 1)) (≼-trans down₁ (≼-trans row₂-btbo (≼-trans btbo-br1ᶻ (rr≼ (brᶻ 1))))))
branch-form : ∀ n → Keel⁻.twc keelᴱ n ≡ proj₁ (TB.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (O.cum FΛ n))
k0 : Kᴱ 0
k1 : Kᴱ 1
station-step : ∀ n → K.readRW (Keel⁻.twc keelᴱ n) ≼ K.readRW (Keel⁻.twc keelᴱ (suc n))
k2 : Kᴱ 2
ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
```

YiFRStep：

```agda
ref-zero : ∀ n → E.fsn (E.EBOψ (suc n)) 0 ≡ E.EBOψ n
row-zero : ∀ n → E.fsn (Keel⁻.row keelᴱ (suc n)) 0 ≡ Keel⁻.row keelᴱ n
  branch-upper : ∀ m → K.readRW (proj₁ (out (chain m))) ≼ K.readRW (Keel⁻.twc keelᴱ (suc n))
  prior-upper : K.readRW (Keel⁻.twc keelᴱ n) ≼ K.readRW (proj₁ (out (chain 0)))
  start-match : Kᴱ n → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ (suc n)) 0))
    → SI.E.tree h ≼ K.readRW (proj₁ (out (chain 0)))
  step : Kᴱ n → Tail → Kᴱ (suc n)
start0 : (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 1) 0))
Remaining : Set
Remaining = ∀ n → Kᴱ n → Step.Tail n
FirstMissing : Set
FirstMissing = Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → SI.E.tree h ≼ K.readRW (proj₁ (Step.out 2 (Step.chain 2 q)))
```

YiFRKeep：

```agda
  keep-suc : ∀ B t {a x} (e : E.cof a ≡ E.c1) (m : M¹ (E.pred a) x)
    → Keep B t m → Keep B t (m1 e m)
  gb0 : GB¹ (B₀ ℓ¹) []
  keep-one : Keep (B₀ ℓ¹) [] oneM
```

##### 偏离与事故

1. 首次小文件编译42：把YiBRValue.readRW与YiKVRel.readRW当作定义性相等，错误发生在btbo-br1ᶻ接线。检索并复用YiKCSem.rr≼后退出0；没有改数学陈述或树定义。初轮其余编译均0，无堆耗尽、超时或内部错误；后续去重复的编译调整见末节。
2. 未证明计划中的全层加强不变量；交付其真实链目标与已证第0项，而不添加假设到主线证书。没有关闭路线。
3. 首个小文件在阶段1开始后约十分钟内编译通过；完整仓库3文件均冷编0。没有装包、提交、推送、改已有文件、改前三层或台账。全部仓库改动只有YiFR前缀3新文件。
4. 对外部模型/其他路线没有据转述认定的新结果。本文复用定理均读过相应代码或签名；未重新编译既有依赖，仅对新模块冷编。主审仍须独立复核。
5. 禁用构造与本机路径扫描对三个新文件为0。报告和日志留在本路实验目录；阶段0原文哈希未变。


##### 主审复核后的去重复

仅修改YiFRKeep：gb0c的重复递归证明改为旧YiKPInst.Std.gb₀c的调用。

```agda
  gb0c : ∀ n → GBf n [] (B₀ (fn n))
  gb0c zero = KP.Std.gb₀c (RS.rb-no ℓ¹) zero
  gb0c (suc n) = KP.Std.gb₀c (RS.rb-no ℓ¹) (suc n)
```

旧Std的参数是YiRBSib.Rb，新Recheck参数是YiTBRow.Rb，二者不能混传。旧gb₀c的类型和证明不使用该表，故明确用旧rb-no实例化Std，不改本路新r。两个GBf是各自对n递归的函数，变量n时不定义性相等；按zero/suc展开后分别都是⊤和同一个HCFold.GB，调用旧定理即可。未改任何旧模块或Keep新命题。

编译过程：清理导入时误删仍被路径使用的tt，恢复导入；直接传新r产生表类型不匹配；以旧表实例化后的整体别名产生两个GBf在变量n处不归约的类型不匹配。分构造子调用旧证明后通过；删自身接口再用5G冷编退出0，只有YiFRKeep的Checking。代码仍为42行（42非空）；不是原递归构造证明的复制。

Stations/Step/阶段0原文均核哈希不变。更新后的源码冻结表如下。

| 文件 | SHA256 |
|---|---|
| probes/OCF/Lean/YiFRStations.lagda.md | 3df76539a789221065e7fecc4303b1332b0274a75d4a62a235e3d32e399d06d6 |
| probes/OCF/Lean/YiFRStep.lagda.md | 92fc9be1f29312db6d0d0032808f585b4b561438194e362d0da18f2201a8c619 |
| probes/OCF/Lean/YiFRKeep.lagda.md | ee71d45ce06949af985e3408fe9ea2edc20ada7b7281f1340d99002266c1b680 |

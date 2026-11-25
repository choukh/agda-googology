# YiND 新终点保持既有下界：实际第2支验收：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiNDTower、Top、Bridge、Accept |
| 文件前缀 | `YiND` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiND 新终点不倒退目标完成复核” 一节 |
| 主审复核后的一句结论 | 4件主审8G逐件冷编0；全HC的tω≼EBOᵗ已证，走新实际第2支零孩子；206非空代码行。未证整个旧终点≤新终点或EBO参照验收。 |

主审补注：四件源码逐件8G独立冷编0，Checking仅自身，合计53.79秒、最大RTS驻留1670349664B；源码与实际接线已独立审查。`tω≼EBOᵗ`覆盖全部HC证书，无困难值界参数；使用新实际第2支零孩子输出，不从标准塔相等推终点。`topΩ`根表任意但孩子固定rbᶻ，右侧用YiVTFold，不能读成旧YiLegFold定理的无条件推广。一般跨底(a)、整体终点比较(c)未尝试，全局F2重实例化未采用，均未被否定。新候选保住已知下界；全旧终点值序、第3站与完整EBO参照验收仍未证，本次不改主线定义。

计数纠正：原回报“209代码/233物理”实际是代码物理行/文件物理行；统一非空非整行注释口径为206行，代码物理209、文件物理233。原回报保留不改。私有Probe日志与接口支持通过，但未另存原始退出码机器表；四件正式冷编0均有直接返回码记录。

工件：[原冻结TSV](attachments/YiND-Producer-Freeze-Codex.tsv)、[完整陈述](attachments/YiND-Signatures-Codex.md)、[执行方冷编](attachments/YiND-Producer-Cold-Codex.json)、[主审接受表](attachments/YiND-Root-Accepted-Codex.json)。

## 简报原文

### 任务简报：新终点不倒退：把旧终点的下界搬到按龙骨比较表的新终点上（数学，验收）（前缀 YiND）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十九批（选项原文 "新终点不倒退 (Recommended)"），与在跑的 YiE4（第 3 站的工程层续做）在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **终点归结为各站的值下界**（编译定理）：`YiS1Accept.Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)`，`YiS1Accept.ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`。各行的参照：第 1 站 ψ₀(Ω₁)，第 2 站 ψ₀(Ω_Ω)，第 3 站 ψ₀(Ω_{Ω_Ω})。第 0、1、2 站在实际底上已成立（`YiFRStations.k0`、`k1`、`k2`；第 1、2 站由已有的 BTBO 下界得到）。已知的无条件终点值是 ψ₀(Ω_Ω+ψ₁(Ω_ω))，低于第 3 站的参照。
- **站间归约**（`YiFRStep`，先读定义的独立审查交的，编译过）：`module Step (n : ℕ)` 里 `ℓ = tw (suc n)`，`k = tw n`，`child c = k ⊕ ↑ k c`，`g c` 是孩子 c 处的 Ω 树，`feed c` 是 `g c` 经路径 `ink self` 折到槽位层 k 的输出，`chain = iter feed zero`（实际回灌链，住在槽位层 `tw n` 上），`out c` 是 `g c` 折到第 0 层的输出（`baseᴱ (suc n)`、`betaᴱ (suc n)` 是终点第 n+1 支实际继承的底与起点）；`branch-upper`：每个链点的输出不高于第 n+1 支；`step : Kᴱ n → Tail → Kᴱ (suc n)`，`Tail = (m : ℕ) → Σ ℕ λ q → (h : HC (E.fsn (row (suc n)) (suc m))) → tree h ≼ readRW (proj₁ (out (chain q)))`。
- **第一个缺口**（`YiFRStep` 末尾，逐字）：
  ```agda
  FirstMissing = Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
    → SI.E.tree h ≼ K.readRW (proj₁ (Step.out 2 (Step.chain 2 q)))
  ```
  主审用一个故意失败的等式让检查器展开了左边那一项（留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC4Row.agda.txt`）：`E.fsn (row 3) 1` 是 `E.ψ [] (E.fsT Ω_{Ω_Ω} (E.γT Ω_{Ω_Ω} [] 1)) ∷ []`，其中 Ω_{Ω_Ω} 写作 `E.ψ (E.ψ (E.ψ (E.ψ [] [] ∷ []) [] ∷ []) [] ∷ []) [] ∷ []`。这正是很早就卡住的 "K(2) 第 1 行"（`YiMTValue.K2-redᶻ`、`YiKQSuff.K2` 都停在这里）。
- **先验教训**（这几批编译的否定）：凡写成 "对一类对象全称成立" 的保持律都被否定了（`YiLLLeafNeg.noLeaf`、`YiSUNeg.no-step`、`YiGTIndexNeg.no-frame₂`、`YiMXNeg.¬Exit′` 等）；正面结果都是对实际对象的直接构造（`YiS1Low.folded¹`、`YiCNTw1.leaf-tw1`、`YiPJQ.qω+1`）。本路只对实际的链点与实际的那一项陈述，不写全域律。
- **上一批之后的事实**（主审复核过）：
  - 每一站的关系推导连同出口证据都可由该站的值下界经语义反射得到（`YiS2Low.station→certificate`），关系路线与值路线合成一条；终点只差从第 3 站起的站值下界。
  - 目标项 `E.fsn (row 3) 1` 展开为 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})（YiMS 回报），已知不低于 ψ₀(Ω_{Ω_ω})（`YiFNTarget.lower`）；是标准形，G 集成员已实填（`YiLBStart`）。
  - 实际链点：第 2 个链点的输出不低于 ψ₀(Ω_Ω+1)（`YiMSValueRef.bound`，沿第 0 支展开 22 次；再推到 ψ₀(Ω_Ω+2) 时 8G 堆耗尽）；一切链点的输出都严格低于第 3 支（`YiFNUpper.strict-upper`，相对上界，不是记号上界）；各链点孩子在非零层上的关系对一切链点成立（`YiLBActual.child-gamma`、`g-gamma`）；第 2 站的链在塔第 1 项那一层上的关系（`YiS2Chain.actual-chain`）。
  - 文献式不变量（`YiLBInv`）：`Inv q`（第 q 个链点的输出支配一切参数为标准形、G 集低于参数、参数不超过第 q 个参数的 ψ₀ 项），`inv0` 成立，`step→first : InvStep → FirstMissing`。
  - **三路停在同一条具体的闭项不等式上**（YiLB 回报第 4 节，逐字）：
    ```agda
    missing-child-low₁ :
      (h : SI.E.HC (E.fsn (Keel⁻.row GI.keelᴱ 3) 1)) →
      SI.E.tree h ≼ K.readRW (proj₁
        (TB.ψ h₁ (proj₂ (P.Ok-tw 3) c₁) (MT.rbᶻ h₁)
          (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
          B.zero (P.z≤ h₁) (GI.betaᴱ 3)
          (proj₁ (O.Ωt h₁))))
    -- c₁ = FR.Step.chain 2 1，h₁ = FR.Step.child 2 c₁ = tw 2 ⊕ ↑ (tw 2) c₁（Ω 形状）
    ```
    `YiLBActual.out-child 1` 把右边与 `Step.out 2 (Step.chain 2 1)` 逐字接上；有了它，`FirstMissing` 以链点 1 为见证成立。
- **上一批之后的新事实**（主审复核过）：`YiUPBase.base-form : ∀ i u → proj₁ (baseᴱ 3 i (inc c₁ u)) ≡ ((Ωt i + ι δ0) + ι δ1) + ι δ2`（`refl`，δ 取自标准底下的 `twᶻ`）：第 3 站链点 c₁ 的孩子折叠时拿到的底只是 Ω 树加三段固定的可数尾项，不随实际回灌链增长。原因（纸面审计 YiPA，回报 `probes/Survey/Reports-2026-11-12/YiPA.md`）：塔第 3 项根上最小比较表的（源孩子 `zero`，目标孩子 c₁）一项是 `lo (h zero) (h c₁)`，而 `lo (nd _ _) b = nothing`（`YiMTTab` 第 29–41 行），于是走退路行，把底与起点重置为标准底 `B₀` 与 `Ωt zero`。能否达到目标、定义是否丢值都未判定（YiFN、YiUP 均未得到独立的记号上界）。
- **性能**（作者 2026-11-15："内存等性能问题参考手册"）：具体闭项先封进 `opaque`、引理在变量上陈述再实例化（Bedrock `<主目录>/Agentic/Bedrock/dev/cubical-agda-performance.md` 的 C-9、C-10、S-1、S-3），先用 `--profile=definitions` 或二分定位（Q-1、Q-23）；手册 `probes/Survey/EBOHandbook.md` 4.2 节第 1 至 8 条。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（另见上面的共同陈述）
- **新候选**（YiCW，主审复核过，回报 `probes/Survey/Reports-2026-11-12/YiCW.md`）：按龙骨的比较表 `YiCWTable.rbᵗ`、`rbΛ`，新闭项 `YiCWTable.twᵗ`、`EBOᵗ`；`tw-same : ∀ n → twᵗ n ≡ twᶻ n`（`refl`，按标准底算的塔各项两张表下相同）；`YiCWActual.hit₁`、`old-miss₁`、`base-form`（新表下第 3 站孩子的底由继承的底折出）；`YiCWStations.k0`、`k1`、`k2`、`floor`。作者的规矩：新候选要替换主线，至少不能让已有的终点值倒退。
- **旧终点已有的下界**：`YiVTANLim.tω≼EBOᴿ : (h : HC tω) → R2.Rt h ≼ readRW EBOᶻ`，tω = ψ₀(Ω_Ω+ψ₁(Ω_ω))；证法是 `l≼` 加一族中间项 `tN≼EBOᴿ`（`YiVTANEnd` 第 211 行，`tN≼EBOᴿ h = up≼ EBOᶻ-R (tN≼EBO h)`：在 F2 对照块上证，再经关系 `EBOᶻ-R` 搬到新主线的终点，走的是终点实际各支）。另有按表参数化的版本 `YiPMMinANLim.tω≼EBOᴿ`（F2 一侧按表参数化，`YiPMFold.F tb`、`YiPMTable.tbᶠ`、`YiPMInst` 的 `Minimum` 实例）。塔第 2 项起：`YiVTTw2Hi.tω≼twᶻ`，经 `tw-same` 直接搬到 `twᵗ`。

#### 要做的（按序）
0. **侦察**（在临时目录）：读 `tN≼EBOᴿ` 的证明依赖链（检索，不整篇读），判断下面三条路哪条最便宜，在回报里写出理由；并编译出 `tω≼twᵗ : ∀ n (h : HC tω) → … ≼ readRW (twᵗ (suc (suc n)))`（由 `tw-same` 与 `tω≼twᶻ`）。
1. **目标**：编译 `tω≼EBOᵗ : (h : HC tω) → R2.Rt h ≼ readRW EBOᵗ`。三条可选的路：
   - (a) 证 "新终点的第 n 支不低于塔的标准项 `twᵗ n`"（继承底对标准底的单调一类），再接 `tω≼twᵗ`；
   - (b) 照 `YiVTANLim` 的证法在新终点的实际各支上重做 `tN≼EBOᴿ`（必要时用 `YiPM*` 的按表参数化，在 F2 一侧配一张与 `rbᵗ` 对应的表）；
   - (c) 直接证 `readRW EBOᶻ ≼ readRW EBOᵗ`（"表回答得更多，输出不变小" 一类）；先在小例子上检查它是否成立，"无法比较" 时的退路行是加法，未必比比较分支小，不成立就交编译的反例并换路。
2. 回报：交目标定理或第一个挡住的引理；说明用的是哪条路、为什么。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiND`（模块名 `OCF.Lean.YiND…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiE4`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库目录>/standard-library.agda-lib
  <Cubical库目录>/cubical.agda-lib
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
- **停下的条件（本路特别规定，覆盖上面的通用写法）**：退出 251 时不原样重跑（Bedrock H-6），先按 C-9、C-10、S-1 改形状并定位；改过形状后在同一上限下仍撞墙才停，附二分或 profile 数据；要加堆在回报里写明，由主审安排。同一处两次重新设计仍过不了检查器也停。没有编译的否定时只写 "未走通"。
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

### YiND 完整回报（待主审独立复核）

#### 1. 判决、范围与路线

本路编译达成作者指定的“新终点不倒退”：已有参照 `YiVTANLim.tω` 的全部 `HC` 证书都不高于 `YiCWTable.EBOᵗ` 的读回。只新建第四层验收定理；树、折叠、合法性、比较表、新旧闭项及公共文档均未改动。结果给新候选保持旧已知下界的编译依据；不自行采用候选，不声称完成 EBO 参照的终点验收，也不声称提高了已知强度或让定义达到树自足。

第 0 步先完成：`YiNDTower.tω≼twᵗ` 覆盖任意 `n` 与任意 `HC tω`，标准项为 `twᵗ (suc (suc n))`。本件是由 `tw-same` 搬运的标准底独立塔项界。最终终点证明没有使用它来代替实际支。

目标的逐字陈述（`YiNDAccept` 第 67 行）：

```agda
tω≼EBOᵗ : (h : HC AL.tω) → R2.Rt h ≼ readRW CT.EBOᵗ
```

这里 `HC = OCF.Align.EboLeanDef.HC`，`AL = OCF.Lean.YiVTANLim`，`R2 = OCF.Lean.YiRefTw2`，`CT = OCF.Lean.YiCWTable`。结论中的 `readRW` **明确来自 `OCF.Lean.YiBRValue`**。`YiCWStations` 使用的 `YiKVRel.readRW` 通过 `YiKCSem.rr≼` 与 `YiKQSuff.read≤` 显式搬运，不按同名当作字面相等。`YiNDAccept.inst` 以 `AL.hΩω` 给出闭实例；没有 Funext、未填条件或附加公理。

问题表：

| 问题 | 位置 | 结果与档 |
|---|---|---|
| 全 n 标准塔下界 | YiNDTower:17 | 编译定理，全部 n、全部 HC 证书 |
| 新实际第 2 支的局部底是否可接旧证明 | YiNDAccept:46、50 | 编译定理，same-local/rBr0 |
| 新实际第 2 支起点关系 | YiNDAccept:56 | 编译定理，beta2-R |
| 全 tN 的新终点下界 | YiNDAccept:64 | 编译定理，全部 m、全部 HC 证书 |
| tω 的新终点下界 | YiNDAccept:67 | 编译定理，全部 HC 证书 |
| 整个 EBOᶻ 是否不高于 EBOᵗ | 未陈述、未尝试 | 未判断，不是本路目标 |
| 第 3 站或 EBO 参照验收 | 本路未处理 | 不由本结果给出 |

##### 侦察所读链与 a/b/c 成本判断

实际检索并读取了 `YiVTANLim.tω≼EBOᴿ` 的极限出口、`YiVTANEnd.tN≼EBOᴿ/tN≼EBO/tN≼br2/lowN/pathN/AtN.atN`、`YiVTANReach.Reach.reachG`、`YiVTANLv.Lv.Anchor` 的声明、row/anchor 出口及其有限层定理入口。旧链为：`Lv.Anchor.anchor → MB.lower⁰ + rd≼ → AtN.atN → reachG(pathN, OKB, Hi) → lowN → Ω≽1 → Ω≽0 → br≼ 2 → up≼ EBOᶻ-R → tN≼EBOᴿ → l≼`。`pathN` 是实际 `h₁ c₁` 上的四层 ℕ 孩子路径，`Hi` 与 `OKB` 已由旧模块实填。

也读取了按表版的类型：`YiPMTable.Table = (k : L) (h : Tr k → L) (c c′ : Tr k) → Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))`；`YiPMFold.F tb`；`YiPMANEnd.F tb.AtN.atN`；`YiPMANReach.F tb.Reach`；`YiPMMinANEnd` 的实填与 `YiPMMinANLim.tω≼EBOᴿ`；`YiPMInst.Minimum` 的实例。按表参数化现有证明的下标是全局 F2 `Table`；CW 的表是在塔根按龙骨提供、孩子仍取 rbᶻ。因此没有把 `rbᵗ` 直接冒充此全局参数。

成本判断（是判断，不是路线否定）：(a) 需要标准底向实际底的模拟，现成 `ψ-⊵` 只给起点不高于输出，不提供这一跨底结论；(c) 比目标强，要控制整个新旧终点及回灌链，表的退路含加法，不能凭“回答更多”断言单调。本路选 (b)，但不重做整套按表 F2：先检查实际零孩子的底，发现 `same-local` 为 refl，便仅重接旧证明真正经过的局部输出。没有对 (c) 作尝试，也没有宣称 (a)/(c) 被否定。

##### 实际证明接线

1. `YiNDBridge.emb-zlift` 对**嵌入结果**归纳，连接 `z≤ (zero ⊕ a)` 与 `lift zero a`；没有要求路径相等或函数外延。
2. 以 `YiCWBTBO.shape`、`YiMTValue.B1-shape` 证明 `base1-same`，再由现成 `YiVTRel.cL` 得新第 1 支底的 `rB1`。此规范实例已先在私有临时文件编译，之后才写一般根表引理。
3. `YiNDTop.upA/upS/topΩ` 来源为 `YiMTRel` 的同名证明。唯一的递归改动是孩子调用 `YiVTRel.A/S`、孩子表字面取 `rbᶻ`；因此不用原文件的 NoΩ 前提，根表可以任意。左项为零的嵌入直接进孩子，回灌链仍由完整的树/推导关系搬运。没有改写折叠。
4. `same-local` 证明新旧第 2 支零孩子以下的实际底逐点相等；`rBr0` 连到旧 `YiVTEVEnd.Br0`。`beta1-R/beta2-R` 对实际起点连同非零证明给出关系。
5. `out0-R` 将**新实际** `C.Step.out 1 zero` 接到旧证明使用的 `F.ψ⊥ (F.tw 1) VE.ε′ VE.ρ′ VE.Br0 (F.Ωt (F.tw 1))`。`AN.lowN` 接 `EV.Ω≽1` 得全 `tN≼out0`；不需要旧终点与新终点的整体关系。
6. `rr≼`、`CS.branch-upper 1 0`、`CS.upper 2`、`read≤` 将它送到新终点；`C.Step.chain 1 0` 定义上是 zero，使用的是实际链点 q=0。最后照 `YiVTANLim` 对任意 HC 证书分情况并取 `l≼`，得目标。

#### 2. 文件、冷编与资源

全部编译从仓库根目录运行，命令及退出码直接由 Python subprocess 读取，没有经过管道。每次 `+RTS -M8G -s -RTS`，本路同时仅一个 Agda；没有查询或声称取得全局进程数。每件仓库文件冷编前只检查并移除其自身字面路径的接口，依赖热。每个冷编日志恰有该模块自己一条 Checking，没有 warning/error。

| 模块 | 代码行（含导入和选项） | 物理行 | 冷编 exit | 外部墙钟秒 | RTS elapsed 秒 | RTS maximum residency 字节 |
|---|---:|---:|---:|---:|---:|---:|
| YiNDTower | 16 | 22 | 0 | 14.685 | 14.593 | 1409592768 |
| YiNDTop | 81 | 87 | 0 | 4.787 | 4.704 | 342042664 |
| YiNDBridge | 45 | 51 | 0 | 17.193 | 17.095 | 1583998096 |
| YiNDAccept | 67 | 73 | 0 | 19.672 | 19.569 | 1665592752 |

合计 209 代码行、233 物理行。资源是单次构建观察；RTS maximum residency 不是 OS RSS，未作提速或稳定基准结论。首件是私有 `YiNDProbe.agda`，先于仓库文件编译，exit 0、RTS elapsed 13.438 秒、maximum residency 1387552608 字节；已在 30 分钟要求内写出并编译。没有 251、124、154；没有加堆或原样重跑堆墙。

具体命令、源 SHA、日志 SHA、Checking 行与资源原始值见 `cold-measurements.json`；复核脚本是 `verify.py`，原始输出是 `verify-output.jsonl`。最终源与冷编日志逐字副本在 `frozen/`。

#### 3. 定理表与全部前提实例

以下是索引；每个定理的**逐字完整陈述**、源码绝对路径、行号及白话读法统一在 `theorem-signatures.md`，其中泛化的 upA/upS/topΩ 也保留全部前提。

| 定理 | 源码行 | 白话 | 档 |
|---|---:|---|---|
| `YiNDTower.tω≼twᵗ` | 17 | 第 0 步：全部 n 的新标准塔第 n+2 项均支配全部 HC tω 证书。 | 编译定理 |
| `YiNDTower.inst` | 20 | 以已有闭证书 hΩω 实例化，证明 HC tω 的量化域非空。 | 编译定理 |
| `YiNDTop.upA` | 33 | 根表任意而孩子表为 rbᶻ 时，零左项嵌入折到第 0 层的模拟。 | 编译定理 |
| `YiNDTop.upS` | 43 | 同一零左项嵌入沿下标层侧路径折叠的模拟。 | 编译定理 |
| `YiNDTop.topΩ` | 54 | 上述分支的 Ω 树模拟，连同回灌链与非零证明。 | 编译定理 |
| `YiNDBridge.emb-zlift` | 33 | 两条零层嵌入路径在嵌入的结果上相等，不要求路径函数相等。 | 编译定理 |
| `YiNDBridge.base1-same` | 37 | 新旧第 1 支的孩子路径底逐点相等。 | 编译定理 |
| `YiNDBridge.old-rB1` | 42 | 旧第 1 支底与带表 F2 底的关系；复用已有 cL。 | 编译定理 |
| `YiNDBridge.rB1` | 44 | 新第 1 支实际底与带表 F2 底的关系，无未填前提。 | 编译定理 |
| `YiNDAccept.same-local` | 46 | 新旧终点第 2 支、零孩子以下的实际继承底逐点相等。 | 编译定理 |
| `YiNDAccept.old-rB2` | 48 | 旧第 2 支实际底与带表 F2 的底的关系。 | 编译定理 |
| `YiNDAccept.rBr0` | 50 | 新第 2 支零孩子的实际底与旧证明所用 F2 Br0 的关系。 | 编译定理 |
| `YiNDAccept.beta1-R` | 54 | 新第 1 支的实际起点及其非零证明的关系。 | 编译定理 |
| `YiNDAccept.beta2-R` | 56 | 新第 2 支的实际起点及其非零证明的关系。 | 编译定理 |
| `YiNDAccept.out0-R` | 59 | 新第 2 支实际零孩子输出与旧 tN 证明所用局部 F2 输出相关。 | 编译定理 |
| `YiNDAccept.tN≼out0` | 62 | 全部 tN 的全部 HC 证书均不高于新第 2 支实际零孩子输出。 | 编译定理 |
| `YiNDAccept.tN≼EBOᵗ` | 64 | 全部 tN 的全部 HC 证书均不高于新终点读回。 | 编译定理 |
| `YiNDAccept.tω≼EBOᵗ` | 67 | 目标：全部 HC tω 证书均不高于新终点读回。 | 编译定理 |
| `YiNDAccept.inst` | 71 | 以已有闭证书 hΩω 实例化，证明 HC tω 的量化域非空。 | 编译定理 |

前提实例逐项如下：

| 被调用的前提 | 本路提供的规范实例 |
|---|---|
| `HC AL.tω` | `AL.hΩω`，由 `YiNDAccept.inst` 与 `YiNDTower.inst` 实例化 |
| 全部 `HC (AN.tN m)` 的辅助取极限证书 | `AN.hN m`，用在 tω≼EBOᵗ 的逐项证明 |
| emb-zlift 的层与 Ok、零层非零树 | `↑ zero c`、`proj₂ (Ok-tw 1) c`、`MV.one⁺`，用在 base1-same |
| 新第 1 支的 `RelBase` | `YiNDBridge.rB1`，在一般 topΩ 编写前已通过临时检查 |
| topΩ 的根表、层关系 | `proj₁ (CT.rbᵗ 1)`、`tw-E 1`；孩子表由 CT.rbᵗ 定义字面为 rbᶻ |
| topΩ 的起点树及非零关系 | `C.betaᴱ 1`、`proj₁ beta1-R`、`proj₂ beta1-R` |
| topΩ 的全部零左项分支 | `λ z → u0 z _ _`，对 Ωt 的每一支实填 U0 |
| topΩ 的输入 Ω 树关系 | `Ωt-R (tw-L 1)` |
| 旧第 1、2 支底的关系 | `old-rB1`、`old-rB2` 都以 `VR.cL Λ-E ... (cumΩ-R Λ-L k)` 实填 |
| VR.A 用于实际零孩子输出的底 | `rBr0`，由 same-local 和 old-rB2 在零孩子路径上限制得到 |
| VR.A 用于实际零孩子输出的起点关系 | `beta2-R` 的两投影 |
| AN.lowN 的 OKB/Hi/路径 | 原 `YiVTANEnd.lowN` 的闭实现，使用 VE.ok0、VE.hi1、pathN 及 AtN.atN；没有在本路作为未填参数再假定 |
| 实际支的上界 | `YiCWStations.branch-upper 1 0` 与 `upper 2`，明确作用于新候选 |
| 两份 readRW 的关系 | `rr≼ (proj₁ (C.Step.out 1 zero))` 与 `read≤ CT.EBOᵗ`，没有直接混用 |

#### 4. 第一个障碍

原目标已经编译完成，无未填引理。第 3 站与 EBO 参照验收不在本路任务范围内；本路不将它们记为失败或否定。

曾尝试直接把 `YiCWBTBO.br1-R` 填成指向 `YiVTEBShape.br 1` 的关系，临时文件 `YiNDLocal.agda` exit 42。错误是目标模块不同：前者的 F2 侧为 `YiLegFold` 配手写 `MV.Bᶻᶠ`，后者使用 `YiVTFold`。没有把两个同名 ψ 或读回当成字面相同；后续用新 rB1 与 YiNDTop 的局部模拟完成了带表 F2 的接线。这个类型错误不是值反例。

#### 5. 偏离、事故、未采用的办法与阅读范围

没有偏离原目标；没有改旧文件、src/archive、公共导航、台账、表、闭项；没有提交、推送、安装、pkill、派子路；没有引用 E4 的未验收结果或重启 XV。

临时试验还出现一次 u0 未从 YiNDTop 导出的作用域错误（YiNDAccept 首轮 exit 42），改为从原 `YiMTRel` 显式导入后通过。原始失败日志保留；并无堆墙。未进行依赖切片或宣称导入闭包无记号：这些全是允许读记号的验收文件。

候选与放下办法供主审记台账：一般跨底单调（a）未尝试；整体新旧终点比较（c）未尝试；按表 F2 全局重实例化未采用，原因是可通过新实际零孩子底相等与局部根表模拟复用旧低层证明。直接套 CW.br1-R 到带表 F2 的尝试因上述准确类型不匹配放下，并已由新关系证明替代；没有关闭任何数学路线。`YiNDTop.topΩ` 可供以后考察“只变根表且分支为零左项嵌入”的局部接线，不提供一般表单调。

完整读了原简报、AGENTS、补充护栏、EBOHandbook 第 4 节及 Bedrock 指定 C-9/C-10/S-1/S-3/Q-1/Q-23/H-6 条目。对大数学依赖按简报检索签名和所用证明链，没有整篇重读 YiVTANLv 的内部归纳；没有对旧定理给出独立冷编复核。未凭转述使用 YiLB/YiUP/YiFN/E4 等结论；它们只在原简报背景出现，本路证明不导入其未验收成果。最终新模块全部本路冷编通过，仍待主审逐件独立冷编、查禁项和陈述后认可。

#### 6. 交付与冻结

私有目录：`<实验目录>/`。本报告为 `YiND-report.md`。`freeze.tsv` 列最终源码、冷编日志、报告、完整陈述、资源和检查文件的 SHA-256；`freeze.json` 提供相同机器可读列表。`frozen/` 有最终源与日志副本；库文件为 `libraries`。`self-check.json` 记录四件源文件的禁项与本机路径匹配均为 0。

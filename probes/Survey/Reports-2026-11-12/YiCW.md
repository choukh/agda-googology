# YiCW 龙骨部分表候选、实际新底与前三站：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiCWTable、Actual、Check、BTBO、Stations |
| 文件前缀 | `YiCW` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiCW 新候选先验、指定格及前三站复核” 一节 |
| 主审复核后的一句结论 | 5件主审8G冷编0；新真实格/完整底、0–2站下界及所有标准tw树等式；第3站/终点值序未证。保留候选暂不换主线。 |

## 简报原文

### 任务简报：作者的想法 V230 的先验检查：按龙骨的比较表（定义一侧，新候选）（前缀 YiCW）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十七批两路之一（选项原文 "现在派先验检查 (Recommended)"），与在跑的 YiE3（第 3 站的工程层）、YiXV（收尾中）在数学上互不依赖。
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
- **作者的想法**（2026-11-15，台账 `probes/Survey/IdeaLedger.md` V230）："把我们现在能让它进行比较的手段重新封装成一个类似 ω 的形式……然后再按原来的套路，把它作为下标"。主审的分析见 V230：壁垒定理（`probes/OCF/Barrier.lagda.md`）的三条前提只能放弃一条；能做的是 "带证据的比较"，在需要对角的地方按回灌链的结构给出比较。
- **主审的派前自查 SC6**（临时文件编译通过，留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC6Table.agda.txt`）：按定义 `↑ k zero = zero`、`k ⊕ zero = k`，所以塔的孩子层号函数 `hᵗ n c = tw n ⊕ ↑ (tw n) c` 在 `zero` 上就是 `tw n`；而 `lift (tw n) (↑ (tw n) c′) : tw n ≤ tw n ⊕ ↑ (tw n) c′`。于是有一张只在龙骨上改动的比较表：
  ```agda
  tbᵗ : (n : ℕ) (c c′ : Tr (tw n)) → Maybe ((hᵗ n c′ ≤ hᵗ n c) ⊎ (hᵗ n c ≤ hᵗ n c′))
  tbᵗ n zero zero = just (inj₁ self)
  tbᵗ n zero c′   = just (inj₂ (lift (tw n) (↑ (tw n) c′)))
  tbᵗ n c    zero = just (inj₁ (lift (tw n) (↑ (tw n) c)))
  tbᵗ n _    _    = nothing
  rbᵗ : (n : ℕ) → Rb (tw n)
  rbᵗ zero    = tt
  rbᵗ (suc n) = tbᵗ n , λ c → rbᶻ (hᵗ n c)
  rbΛ : Rb Λ
  rbΛ = tt , rbᵗ
  ```
  它只在 "源或目标是 `zero`" 时给出字面路径，不判定任何东西；正是第 3 站重置底的那一项。折叠 `YiTBRow.ψ` 本身以表为参数，不用改。**这是新候选，不改现有定义与闭项**；采用与否由作者定（AGENTS "第 4 层不反过来改前 3 层"）。
- 已有的按表参数化的工具：`YiTBRow`（以表为参数的折叠）、`YiPM*`（F2 一侧按表参数化，`YiPMFold.F tb`）、`YiTBCrit.tb-crit`（比较表那一行的判据）、`YiTBObs.no-total`（全序的表不可能）。

#### 要做的（按序）
0. **先验检查**（在临时目录）：
   - 对照壁垒定理的三条前提，说明 `rbᵗ` 不满足哪一条；
   - 回答 AGENTS "开新行前的先验检查" 三问（目标是指定孩子的还是对一切孩子一致的；孩子下标类型上有没有证据函数；有没有按存在性保留），并对照 `obs→dec` 一族（`YiAbsObs`、`YiAbsFrame` 里的 `branch→wdec`、`hand→wdec`、`viaE→dec`、`full→dec`）说明 `rbᵗ` 碰不碰它们。
   - 不成立就停下回报。
1. **新闭项**：用 `rbᵗ`、`rbΛ` 写出新的塔与终点闭项（照 `YiMTTab.twᶻ`、`EBOᶻ`，只换表），确认合法性（`Ok-tw`、`Ok-Λ` 照旧）。
2. **第 3 站的那一项**：编译出塔第 3 项根上（源孩子 `zero`，目标孩子 c₁）一项在新表下返回 `just`；写出新闭项下 c₁ 孩子折叠拿到的底（照 `YiUPBase.base-form`），说明它与旧的有何不同（是否带上实际回灌链的增长）。
3. **旧结论能否搬过来**：新闭项上第 0、1、2 站的值下界（照 `YiFRStations`），能复用就复用（以表为参数的证明）；做不到就交第一个挡住的地方。
4. **纸面估算**（判断档）：新闭项在第 3 站的那个对象上能否达到目标项 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})，与旧闭项比是否更容易证；若能编译出新闭项上的 `FirstMissing` 或更高的链点值，更好。
5. **翻译账**：`rbᵗ` 用到树的哪些构造（`⊕`、`↑`、`lift`、塔的定义），是否读了记号；按作者的说法 "龙骨不算翻译"，说明它是否只用了龙骨的结构。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiCW`（模块名 `OCF.Lean.YiCW…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiE3`、`YiXV`、`YiUD`）。新比较表与新闭项的文件若只用树与层号，文首标明 "不读记号" 并用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包；读记号的文件标明 "验收文件"。
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

### 主审复核与采用决定

五件主审逐件8G自身接口冷编0，Checking仅自身；全文查源/报告，另两组只读审查。新增235同口径代码行。全导入闭包Table/Actual/Check本地7/8/11，禁用表0；Table/Actual编译器图142/143总节点，其本地集合与脚本集合逐项相同。源码和私有冻结副本首尾SHA一致，禁用构造/洞/本机路径0。资源见[原自测表](attachments/YiCW-Resources-Codex.json)，审计见[Table闭包](attachments/YiCWTable-Root-Closure-Codex.txt)、[Actual闭包](attachments/YiCWActual-Root-Closure-Codex.txt)、[Check闭包](attachments/YiCWCheck-Root-Closure-Codex.txt)、[编译器图核对](attachments/YiCW-Root-Graphs-Codex.json)。

已核新真实c₁而非旧链点：指定格just与旧表nothing、新孩子底的完整Tr⁺等式、实际第0–2站下界均成立。floor只指新第3站全部q对第2站参照的下界，不外推全部站。tw-same对所有n成立，但不推出新旧终点相等或值序。表侧否定与机制判断严格分开；[私有预检](attachments/YiCW-Precheck-Codex.md)中“全Same/on”只应读成表的全对角on，不能当折叠Same/Hand否定。[Goal私有源码](attachments/Experiment-YiCW-Goal-Codex.agda.txt)只有Missing₁/FirstMissingᵗ类型及既有目标HC实例，不是该值界的证明。

采用决定（主审判断）：保留为开放候选，暂不替换既有主线。理由是指定格的计算改变尚未连成第3站目标下界，亦未给新终点保留主线已有终点值验收的定理或新旧终点值序。该决定不是候选被否定；没有据“tw-same”否定它，后续可从新继承底的值继续。树的定义、折叠、合法性、原闭项均未改。FΛ/pre与干净SLStart可别名复用是进一步正式化的工程判断，尚未编译该重构，不改已测冻结源。

### 执行方完整原回报

### YiCW 完整回报（待主审复核，不自行采用）

#### 1 判决与问题表

本路交了不读记号的合法新塔和新终点；所有数学文件仍用原树、原折叠、原合法性，没有改任何已有定义。新表能够在第 3 站新真实链点 c₁ 的指定格返回字面路径，并保留经该路径送入的 Ω 树及继承底。第 0、1、2 站的值下界搬运完成。没有证明第 3 站的目标下界，也没有证明候选达不到目标；候选采用与否交主审判断。

对“让树自足”的意义：新增比较条目来自树自身的龙骨和 lift，而非记号规则。它是一个不判定地补充指定比较项的闭构造。未证明阶段无关的完整闭包，也未完成 EBO 值验收，不能把该候选称为树已自足。

第 0 步通过，依据如下。第 1、2、3 步完成；第 4 步交判断与精确未填式；第 5 步翻译账见下。五个仓库文件均删自身接口后冷编 0，日志的 Checking 只含本件。全部位于 YiCW 前缀，未改 README/LOG/台账/旧文件；未派子路，未提交或推送。

| 问题 | 位置 | 档与结果 |
|---|---|---|
| 是否触及壁垒/观察否定的机制 | precheck.md、YiCWCheck | 表侧事实为编译定理；机制对应为读类型的判断，允许继续 |
| 新塔/终点是否合法 | YiCWTable.tw-legal/EBO-legal | 编译定理，无未填前提 |
| 新标准塔是否改变 | YiCWTable.tw-same | 编译定理：所有 n 上 twᵗ n ≡ twᶻ n |
| 第 3 站源 zero、目标新 c₁ 的格 | YiCWActual.hit₁/old-miss₁ | 编译定理：新表 just 指定 lift，同一新点上旧表 nothing |
| c₁ 孩子的实际底 | YiCWActual.base-form | 编译定理：完整 Tr⁺ 相等，不限于 proj₁；有 prior 和嵌入的 Ωt(tw2) |
| 新实际第 0、1、2 站值下界 | YiCWStations.k0/k1/k2 | 编译定理；第 1、2 站为 ψ₀(Ω₁)、ψ₀(Ω_Ω) 的原参照下界 |
| 新真实各链点已知值下界 | YiCWStations.floor | 编译定理：各点至少有第 2 站 ψ₀(Ω_Ω)；没有新增强度 |
| 新第 3 站 FirstMissing | 私有 Goal.Missing₁/FirstMissingᵗ | 类型检查通过，证明未填；没有把类型的编译计为值定理 |
| 是否带上“增长” | base-form | 构造式确实保留新 c₁ 参数及继承底；序数值随 q 增长未证明 |
| 能否达到 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) | 第 4 节 | 判断：目前没有可交的达到或达不到的推导 |

#### 2 第 0 步逐条核机制

##### 壁垒三前提

1. **精确 Ordᴰ 初始段**：本路不新建下标类型，用原 L。本路没有构造 Ω-Extension.ι/ι-exact，不能声称此项已实填，也不靠变动这一项解释候选。
2. **Ω-共尾元**：本路没有删掉原层号中的 Ω 形状、塔或 Λ；没有在本路证明整个 Ordᴰ 嵌入像之上的 top。本路不靠削去 Ω 分支规避。
3. **有界三歧性**：这是明确放弃的字段。RbS 的类型为 Maybe ((h c′ ≤ h c) ⊎ (h c ≤ h c′))；它不是严格序三歧，允许 nothing，也不交等号支。YiCWCheck.empty-diagonal 在两个后继孩子上返回 nothing，即使是同一个后继孩子也如此。两个孩子均有字面公共上界 tw(suc n)：common n c = inc c self。不能把这一表当 Barrier.Ω-Extension.<ᴵ-dec。YiCWCheck.no-full 引原 YiTBObs.no-total，进一步否定塔 1 上全字面路径二选一的填表方式；该否定不关闭部分表候选。

##### 开新行的三问

1. 受影响的行是 inc c′ v：目标经指定孩子 c′。inu 一致目标行没有改变。这里只给指定格提供路径，不要求任意指定孩子都交接。
2. 表是一张孩子**层号路径**的证据函数。它不是孩子下标相等的 Maybe(c≡c′)；非零对角可空，没有全自反相等证据函数。零构造子是否出现是可观察的，且这本来可判；没有对任意两棵树判等。
3. 没有按“层号字面相等”或“槽位存在”要求保留；kp 原样。新条目从已知处于塔根这个构造入口、再读孩子是否为 zero 来构造 lift。没有测试任意层号是否等于一座塔，也没有提供 full 完整性。

##### obs→dec 一族

- viaE→dec：缺少 ViaE 的 Maybe(c≡c′) 数据；RbS 的路径和不是这种证据。
- full→dec：没有“能保留处都保留”的律；保留判定没有改。
- hand→wdec：没有全 Hand 加可观察回退 Offᴾ。表在非零对角可空，不能从该表读出全 Hand。
- branch→wdec：没有在折叠输出头部实填所需的 on/off。表的观察也不是恰在一个孩子为真：off-fails 在零与后继零处直接反驳 off。这里是表数据的编译反例，不能替代折叠头部上的否定。

先验最小实例 Pre.agda 已在写仓库新文件前编译：rbᵗ、rbΛ 可构造；n=2 的零对后继零返回 just，非零对角返回 nothing。第一次因无歧义类型注解缺失退出 42，补 _≡_ {A = Tr(tw2)} 后退出 0；不是路线重新设计或堆墙。

#### 3 文件、资源与审计

计数口径：新文件 Agda 代码围栏内非空行，含选项、模块头、导入，共 235 行；不是成品成本结论。所有编译单进程、堆上限 8G、带 +RTS -s。下表为最终自身接口冷编，依赖接口保留。maximum residency 是 GHC 的数，不能叫进程峰值 RSS。

| 文件 | 代码行 | 冷编退出 | GHC maximum residency（bytes） | total memory in use（MiB） | 墙钟秒 |
|---|---:|---:|---:|---:|---:|
| YiCWTable.lagda.md | 43 | 0 | 136,288,104 | 265 | 1.780 |
| YiCWActual.lagda.md | 57 | 0 | 152,293,328 | 258 | 1.802 |
| YiCWCheck.lagda.md | 26 | 0 | 161,868,344 | 273 | 1.759 |
| YiCWBTBO.lagda.md | 57 | 0 | 1,446,559,528 | 2435 | 15.623 |
| YiCWStations.lagda.md | 52 | 0 | 1,597,321,256 | 2712 | 18.269 |

日志为同目录 <模块>-cold.log，退出码另存 <模块>-cold.exit，原始 JSON 为 cold-results.json。每件 Checking 只有自身；没有 251、124、154，也没有加堆、原样墙后重跑或 ignore-interfaces。最高 GHC total memory in use 为 2712 MiB。

完整 importclosure（没有 --only 缩窄）通过：Table 本地 7/脚本总 15，Actual 本地 8/脚本总 16；Check 本地 11/脚本总 19。编译器 dependency-graph 的总节点分别为 Table 142、Actual 143；本地集合与脚本集合逐项相同，集合差为空，无 Align/Notation/Free.Lab 模块。脚本与编译器的库计数口径不同。原始图、集合比对 JSON 及完整闭包都留本目录。

五件的禁用构造/洞标记/本机路径检索命中为 0；所有文首都是 4 行。安全与停机仍由 safe 检查器保证。未做 depslice：本路定义侧已经编译器级完整导入闭包干净；验收文件刻意读记号，不拿其闭包当成品。

操作系统进程 RSS/全局进程数：未取得。只读 ps 被沙箱拒绝（operation not permitted）；没有申请绕过，不能把它报告成 0。冷编资源均为 +RTS -s 的原始数。本路同时只运行过一个 Agda。

#### 4 第一个余项、估值与翻译账

##### 精确未填式

下面的 Missing₁ 和 FirstMissingᵗ 均在私有 Goal.agda 作为 Set 的定义检查通过，但未给它们的 inhabitant。目标域的闭 HC 由 target-inhabited=YiFNTarget.target-hc 编译通过，因此不是空域命题。第 0–2 站的 HC 实例可用 YiGIEnd.hs 0/1/2；新底/链本身为闭构造，无附加存在性前提。

```agda
h₁ : B.L
h₁ = C.Step.child 2 C.c₁
Target : Set
Target = SI.E.HC (E.fsn (Keel⁻.row GI.keelᴱ 3) 1)
target-inhabited : Target
target-inhabited = target-hc
Missing₁ : Set
Missing₁ = (h : SI.E.HC (E.fsn (Keel⁻.row GI.keelᴱ 3) 1)) →
  SI.E.tree h ≼ K.readRW (proj₁
    (TB.ψ h₁ (proj₂ (P.Ok-tw 3) C.c₁) (MT.rbᶻ h₁)
      (λ i u → C.baseᴱ 3 i (P.inc C.c₁ u))
      B.zero (P.z≤ h₁) (C.betaᴱ 3)
      (proj₁ (O.Ωt h₁))))
FirstMissingᵗ : Set
FirstMissingᵗ = Σ ℕ λ q → (h : SI.E.HC (E.fsn (Keel⁻.row GI.keelᴱ 3) 1)) →
  SI.E.tree h ≼ K.readRW (proj₁ (C.Step.out 2 (C.Step.chain 2 q)))
```

C=YiCWActual，GI=YiGIInst，h₁=C.Step.child 2 C.c₁，C.c₁=C.Step.chain 2 1。Missing₁ 的 RHS 用 MT.rbᶻ h₁，正是新候选的孩子表，不能擅换 rbᵗ。YiCWActual.Step.out-child 2 1 把这项与新 out(chain1) 接上。第一个未填的是这个值不等式，未遇到需要改树、折叠或合法性的地方。

Goal.agda 编译 0，GHC maximum residency 1,292,522,920 bytes，total memory 2451 MiB。它只确认陈述与目标域可构造，不是 Missing₁ 或 FirstMissingᵗ 的证明。

##### 纸面估算（判断档）

已证的新公式是：base3 在新 c₁ 的限制分量，等于在 h₁ 上折叠经 lift(tw2,↑tw2 c₁) 嵌入的完整 Ωt(tw2)，起点是 prior 在同一路径上的分量，底也是 prior 的相应限制。这个指定格不再执行 row-no 的“标准零层折叠再嵌回”分支。old-miss₁ 还确认了在同一个新 c₁ 上，旧表会返回 nothing；没有把旧链点拿来代替新链点。

因此新式保留了 c₁ 决定的嵌入路径、目标孩子层以及已继承的 prior。这里的“带上”是计算式的事实，不是“值随链增长”的定理，更不是已经达到目标。没有证明 base3 不等于某个旧 Ω 加尾项表达式，也没有证明两个新旧输出在 ≼ 上严格分开。旧 YiUPBase.base-form 只适用于旧 q1，本路没有外推到别的 q 或新链。

对目标 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})：该记号读法沿简报；本路未独立证明这个记号展开，精确义务始终使用 fsn(row3)1。已编译的新输出下界仍为 ψ₀(Ω_Ω)。目前没有独立记号上界，也没有得到达到该目标的纸面推导。修复该格消除了一个确定的标准底回退，但孩子内部仍用 rbᶻ；其余比较或保持不能由 hit₁ 推出。“是否更容易证明整个目标”尚未判定。没有把未证写成路线否定，没有计为新强度。

另一个编译事实限制了对此候选的读法：tw-same 对所有 n 给出 twᵗ n≡twᶻ n。标准底下的单独塔项只沿一致/下标路径作用于左项为 zero 的嵌入，根表不影响它们；本候选可能改变的地方是终点各支的继承底。本路未证明 EBOᵗ 与 EBOᶻ 相等或不等，也未证明二者值的次序。

##### 翻译账

- 新数据使用 tw 的龙骨结构 hᵗ n c=tw n⊕↑(tw n)c。由 ↑k zero=zero 和 k⊕zero=k 得 hᵗ n zero=tw n，已有 lift 给 tw n≤hᵗ n c；common 明示公共上界 tw(suc n)。
- 不读记号：新表文件没有 fsn、fsT、γT、NF、记号项或标签；完整导入闭包也没有这些模块。rbᵗ 是在已知塔根的入口填表，不是判断任意层号是不是塔。
- 按作者“龙骨不算翻译”的口径，本次新增表只用了龙骨结构、树的 zero、⊕、↑、lift 和原部分表；没有从记号基本列读取新字段。实际底和链的定义照原终点配新表，未新加树构造子、折叠分支或合法性前提。
- 仍有来源信息：新候选是作者 V230、SC6 针对已发现回退位置提出的试验，不能把研究动机的记号指引抹去；干净闭包只保证定义不引用记号。
- 第 4 层没有逼出前三层修改。0–2 站验收只新增关系/值定理，复用 topΩ、lift-W 与原 BTBO 界。没有为了同步记号改树的基本列。
- 未完成：全站值、FirstMissingᵗ、独立上界、整个终点与旧终点的值比较。没有新增强度结论。

#### 5 偏离、事故、候选与放下的办法

- 数学工作按作者顺序：Pre 最小实例→新表/闭项→新 c₁ 指定格和新底→StationProbe 规范底实填→0–2 站→估值与账→冷编。首个 Pre 成功编译在文件建立后约 17 秒（15:59:54 建立，16:00:11 成功日志建立，本机时区）；任务开始的独立时间戳未取得，不另报精确启动耗时。
- 阅读补项：EBOHandbook §4.6 后半与 AbsObs.Slot.full→dec 的完整段落在收尾补读；开工时已读 §4.1–4.5、§4.6 前半及先验接口的其余陈述。原简报、AGENTS、batch57 护栏是开工前完整读的。
- 唯一类型错误：Pre.not-exact 的 zero/suc 重载缺少类型。以 _≡_ {A=Tr(tw2)} 补齐后通过；保留原失败日志及成功日志。
- 工具事故：ps 只读查询被沙箱拒绝。未扩大权限。一次私有检索脚本的正则误把等号行计为洞，纠正检索表达式后完整重扫 0；没有据该误报改数学代码。
- 没有堆墙、超时或 Agda 内部错误；没有采用额外公理、Funext、K 或无关投影选项。没有改、移动、删除任何旧源码；删除只限五件自身接口。
- 新增规范证明中的 from⊴ 直接复用 YiLBInv，未再次复制；rB1/br1-R 改接的是新路径形状，文首记录来源。
- 候选仅 rbᵗ/rbΛ 这一套。没有另派候选，也没有把孩子表递归换成 rbᵗ 或扩张为全表。未尝试一般完整保持律、全下标判等或按存在性保留。
- 标准塔不变首先临时验证 n=1、3（TowerSame.agda），再写并编译一般 tw-same；临时两项是有限检查，一般式才是交付定理。
- 原 SC6 附件、YiPA 原报告、YiMS 的目标记号展开证明、YiXV/YiE3/YiUD 在研代码未在本路独立阅读或复核；涉及背景的说法来自原简报，本回报不把它们升级成新定理。已完整读 AGENTS、原简报、batch57 护栏、EBOHandbook §4（特别 4.2 的 1–8）以及 Bedrock C-9/C-10/S-1/S-3/H-6/Q-1/Q-23；Barrier/AbsObs/AbsFrame 按接口与所引用引理逐条读陈述，非文献重调研。

#### 6 定理表与逐字陈述

下表均为本路编译结果；“构造”与“值定理”分开。每条的逐字签名及其局部上下文在紧随表后的五件完整源文中，不依赖本回报的缩写重述。

| 名字 | 白话 | 文件 | 档 |
|---|---|---|---|
| rbᵗ、rbΛ、tw⁺ᵗ、EBO⁺ᵗ | 部分比较表及非零合法闭构造 | YiCWTable | 编译构造 |
| tw-legal、EBO-legal | 新闭项满足原第一位置非零证书 | YiCWTable | 编译定理 |
| tw-same | 标准底的新旧独立塔项对每个 n 相等 | YiCWTable | 编译定理 |
| branch-form | station 确是新终点的实际第 n 支 | YiCWActual | 编译定理 |
| Step.out-child | 新链点输出等于新继承底下的孩子折叠 | YiCWActual | 编译定理 |
| hit₁ | 指定格返回所写 lift | YiCWActual | 编译定理 |
| old-miss₁ | 同一个新 c₁ 上旧表返回空 | YiCWActual | 编译定理 |
| base-form | 新 c₁ 孩子底的完整 Tr⁺ 展开 | YiCWActual | 编译定理 |
| common | 各孩子到同一个字面上界的路径 | YiCWCheck | 编译构造 |
| empty-diagonal、on-zero | 表有的空对角与零正格 | YiCWCheck | 编译定理 |
| off-fails、not-reflexive | 排除两条表侧观察假设 | YiCWCheck | 编译定理 |
| no-full | 原全路径表否定在新 hᵗ0 的引用 | YiCWCheck | 编译定理，复用 |
| shape、rBc、rB1、br1-R | 新第 1 支实际底与 F2 参照对应 | YiCWBTBO | 编译定理 |
| btbo | 新第 1 支不低于 BTBO | YiCWBTBO | 编译值下界 |
| k0、k1、k2 | 新实际前三站的参照值下界 | YiCWStations | 编译值下界 |
| station-step、upper | 相邻实际站单调及每站在新终点下 | YiCWStations | 编译值定理 |
| branch-upper | 新实际各链点的输出在所属站下 | YiCWStations | 编译值定理 |
| floor | 新第 3 站每个链点输出不低于第 2 站参照 | YiCWStations | 编译值下界 |

##### YiCWTable（逐字源文）

### 龙骨零孩子的比较表与闭项
不读记号；新候选，不替换主线。来源：作者 V230 与 SC6 的表，闭项照 YiMTTab 仅换表。
表只对龙骨根的零孩子提供路径，孩子内部仍用 rbᶻ；合法性由原 ψ 的返回类型保证。
不声称有站值下界；先验对照见 YiCWCheck，实际底与链见 YiCWActual。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWTable where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
hᵗ : (n : ℕ) → Tr (tw n) → L
hᵗ n c = tw n ⊕ ↑ (tw n) c
tbᵗ : (n : ℕ) (c c′ : Tr (tw n)) → Maybe ((hᵗ n c′ ≤ hᵗ n c) ⊎ (hᵗ n c ≤ hᵗ n c′))
tbᵗ n zero zero = just (inj₁ self)
tbᵗ n zero c′ = just (inj₂ (lift (tw n) (↑ (tw n) c′)))
tbᵗ n c zero = just (inj₁ (lift (tw n) (↑ (tw n) c)))
tbᵗ n _ _ = nothing
rbᵗ : (n : ℕ) → Rb (tw n)
rbᵗ zero = tt
rbᵗ (suc n) = tbᵗ n , λ c → rbᶻ (hᵗ n c)
rbΛ : Rb Λ
rbΛ = tt , rbᵗ
ψ₀ᵗ : (n : ℕ) → Tr (tw n) → Tr⁺ zero
ψ₀ᵗ n = ψ (tw n) (Ok-tw n) (rbᵗ n) (B₀ (tw n)) zero (z≤ (tw n)) (Ωt zero)
tw⁺ᵗ : ℕ → Tr⁺ zero
tw⁺ᵗ n = ψ₀ᵗ n (proj₁ (Ωt (tw n)))
twᵗ : ℕ → Tr zero
twᵗ n = proj₁ (tw⁺ᵗ n)
EBO⁺ᵗ : Tr⁺ zero
EBO⁺ᵗ = ψ Λ Ok-Λ rbΛ (B₀ Λ) zero (z≤ Λ) (Ωt zero) (proj₁ (Ωt Λ))
EBOᵗ : Tr zero
EBOᵗ = proj₁ EBO⁺ᵗ
tw-legal : ∀ n → zero ⊢ zero ◃ twᵗ n
tw-legal n = proj₂ (tw⁺ᵗ n)
EBO-legal : zero ⊢ zero ◃ EBOᵗ
EBO-legal = proj₂ EBO⁺ᵗ
tw-same : ∀ n → twᵗ n ≡ twᶻ n
tw-same zero = refl
tw-same (suc n) = refl
```

##### YiCWActual（逐字源文）

### 新终点的继承底与真实链
不读记号；来源：YiGIInst 的底和 YiFRStep 的链，仅换为 YiCWTable 的表。
本文件的 chain 是 EBOᵗ 各支的实际回灌链；不借用旧链点，不提供值验收。
第 3 站的指定格与继承底等式见文末；等式不声称值随链严格增长。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWActual where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
open import OCF.Lean.YiCWTable
FΛ : ℕ → B.Tr B.Λ
FΛ n = proj₁ (O.upz {s = B.sL} {h = B.tw} n (O.Ωt (B.tw n)))
pre : ℕ → B.Tr B.Λ
pre zero = B.zero
pre (suc n) = O.cum FΛ n
baseᴱ : ∀ n → F.Base (B.tw n)
baseᴱ n i u = TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) (pre n)
betaᴱ : ∀ n → O.Tr⁺ B.zero
betaᴱ n = TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (pre n)
station : ℕ → B.Tr B.zero
station n = proj₁ (TB.ψ (B.tw n) (P.Ok-tw n) (rbᵗ n) (baseᴱ n) B.zero (P.z≤ (B.tw n)) (betaᴱ n) (proj₁ (O.Ωt (B.tw n))))
branch-form : ∀ n → station n ≡ proj₁ (TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (O.cum FΛ n))
branch-form zero = refl
branch-form (suc n) = refl
module Step (n : ℕ) where
  ℓ = B.tw (suc n)
  k = B.tw n
  child = hᵗ n
  g : B.Tr k → B.Tr ℓ
  g c = proj₁ (O.upz {s = B.sΩ k} {h = child} c (O.Ωt (child c)))
  feed : B.Tr k → B.Tr k
  feed c = proj₁ (TB.ψ ℓ (P.Ok-tw (suc n)) (rbᵗ (suc n)) (baseᴱ (suc n)) k (P.ink P.self)
    (baseᴱ (suc n) k (P.ink P.self)) (g c))
  out : B.Tr k → O.Tr⁺ B.zero
  out c = TB.ψ ℓ (P.Ok-tw (suc n)) (rbᵗ (suc n)) (baseᴱ (suc n)) B.zero (P.z≤ ℓ) (betaᴱ (suc n)) (g c)
  chain : ℕ → B.Tr k
  chain = O.iter feed B.zero
  out-child : ∀ q → out (chain q) ≡ TB.ψ (child (chain q)) (proj₂ (P.Ok-tw (suc n)) (chain q)) (MT.rbᶻ (child (chain q)))
    (λ i u → baseᴱ (suc n) i (P.inc (chain q) u)) B.zero (P.z≤ (child (chain q))) (betaᴱ (suc n)) (proj₁ (O.Ωt (child (chain q))))
  out-child q = refl
c₁ : B.Tr (B.tw 2)
c₁ = Step.chain 2 1
hit₁ : proj₁ (rbᵗ 3) B.zero c₁ ≡ just (inj₂ (P.lift (B.tw 2) (B.↑ (B.tw 2) c₁)))
hit₁ = refl
old-miss₁ : proj₁ (MT.rbᶻ (B.tw 3)) B.zero c₁ ≡ nothing
old-miss₁ = refl
prior : F.Base (B.tw 3)
prior i u = TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) i (P.inc 3 u) (O.Ωt i) (pre 2)
base-form : ∀ i (u : i P.≤ hᵗ 2 c₁) → baseᴱ 3 i (P.inc c₁ u) ≡
  TB.ψ (hᵗ 2 c₁) (proj₂ (P.Ok-tw 3) c₁) (MT.rbᶻ (hᵗ 2 c₁))
    (λ j v → prior j (P.inc c₁ v)) i u (prior i (P.inc c₁ u))
    (proj₁ (P.emb (hᵗ 2 c₁) (proj₂ (P.Ok-tw 3) c₁) (P.lift (B.tw 2) (B.↑ (B.tw 2) c₁)) (O.Ωt (B.tw 2))))
base-form i u = refl
```

##### YiCWCheck（逐字源文）

### 龙骨表的先验观察检查
验收文件，不读记号；表的有无不分离零与其余孩子，非零对角可为空。
来源：YiMTObs/YiTBObs 的表侧观察测试；全表否定直接引用 no-total。
这些定理只谈表数据；不把它们当作折叠头部的 Hand 或 branch→wdec 的否定。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWCheck where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Maybe using (nothing)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCWTable
open import OCF.Lean.YiTBObs using (isJ; no-total)
common : ∀ n c → hᵗ n c ≤ tw (suc n)
common n c = inc c self
empty-diagonal : ∀ n (c c′ : Tr (tw n)) → tbᵗ n (suc c) (suc c′) ≡ nothing
empty-diagonal n c c′ = refl
on-zero : ∀ n → isJ (tbᵗ n zero zero) ≡ true
on-zero n = refl
off-fails : ∀ n → ((c : Tr (tw n)) → (zero ≡ c → ⊥) → isJ (tbᵗ n c zero) ≡ false) → ⊥
off-fails n off with off (suc zero) (λ ())
... | ()
not-reflexive : ∀ n → ((c : Tr (tw n)) → isJ (tbᵗ n c c) ≡ true) → ⊥
not-reflexive n on with on (suc zero)
... | ()
no-full : ((c c′ : Tr zero) → (hᵗ 0 c′ ≤ hᵗ 0 c) ⊎ (hᵗ 0 c ≤ hᵗ 0 c′)) → ⊥
no-full = no-total
```

##### YiCWBTBO（逐字源文）

### 新终点第 1 支的 BTBO 下界
验收文件，读记号；新支不低于 BTBO，不提供第 3 站下界。
来源：YiMTValue.rBc/rB1ᶻ/br1-Rᶻ，改用 lift-W 对应新表的路径；topΩ 已对表参数化。
rB1 与 br1-R 均无未填前提；规范实例先在临时 StationProbe 编译。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWBTBO where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiCWTable
import OCF.Lean.YiCWActual as C
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiMTValue as MV
import OCF.Lean.YiSMValue as SM
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiMTRel using (topΩ; S; u0)
open import OCF.Lean.YiNRHit using (noΩ↑)
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; emb-R)
open import OCF.Lean.YiBRFold using (W→L; B₀-R)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; ↑-L; lift-W)
open import OCF.Lean.YiEBShape using (Fn)
open import OCF.Lean.YiBRValue using (up≼; readRW)
open import OCF.Lean.YiEBBtbo using (module Btbo)
import OCF.Lean.YiLSTw1 as T1
open import OCF.Align.Value using (_≼_)
open import OCF.Align.YiBtValBT using (module D)
Bc : (c : Tr zero) (j : L) → j ≤ hᵗ 0 c → Tr⁺ j
Bc c j v = ψ (hᵗ 0 c) (proj₂ (Ok-tw 1) c) (MT.rbᶻ (hᵗ 0 c)) (B₀ _) j v (Ωt j)
  (proj₁ (emb (hᵗ 0 c) (proj₂ (Ok-tw 1) c) (lift zero (↑ zero c)) MV.one⁺))
shape : ∀ c j v → C.baseᴱ 1 j (inc c v) ≡ Bc c j v
shape zero j v = refl
shape (suc c) j v = refl
shape (lim f a) j v = refl
rBc : ∀ {c c′} (rcc : RelT zero F.zero c c′) {j j′} {v : j ≤ hᵗ 0 c} {v′ : F._≤_ j′ (T1.h₁ c′)} → RelW v v′
  → RelT j j′ (proj₁ (Bc c j v)) (MV.bsᶻ j′ (F.inb c′ v′)) × RelD j j′ (proj₂ (Bc c j v)) (MV.nsᶻ j′ (F.inb c′ v′))
rBc {c} {c′} rcc {j} {j′} rv =
  let rec = SM.chE (tw-E 1) c c′ rcc
      rlj = W→L (E→L rec) rv
      em = emb-R rec (lift-W (↑-L lz rcc)) MV.one⁺ (is iz) ds
  in S rec (noΩ↑ c) (B₀ _) (F.B₀ _) (B₀-R (E→L rec)) rv (Ωt j) (Ωt-R rlj) (Ωn-R rlj) (proj₁ em)
rB1 : RelBase (tw 1) (F.tw 1) (C.baseᴱ 1) MV.Bᶻᶠ
rB1 j j′ w w′ rw@wself = SM.cΛ j j′ w w′ rw
rB1 j j′ w w′ rw@(winuΩ _) = SM.cΛ j j′ w w′ rw
rB1 j j′ w w′ rw@(wink _) = SM.cΛ j j′ w w′ rw
rB1 j j′ w w′ (wincΩ {c = c} {c′ = c′} {v = v} {v′ = v′} rcc rv) =
  subst (λ Z → RelT j j′ (proj₁ Z) (MV.bsᶻ j′ (F.inb c′ v′)) × RelD j j′ (proj₂ Z) (MV.nsᶻ j′ (F.inb c′ v′)))
    (sym (shape c j v)) (rBc rcc rv)
br1-R : RelT zero F.zero (C.station 1) (Fn 1 MV.Bᶻᶠ)
br1-R = proj₁ (topΩ {tb = rbᵗ 1} (tw-E 1) noΩ↑ (C.baseᴱ 1) MV.Bᶻᶠ rB1 (C.betaᴱ 1) (proj₁ SM.β1-R) (proj₂ SM.β1-R) (λ z → u0 z _ _) (Ωt-R (tw-L 1)))
btbo : D.BTBOᴵ ≼ readRW (C.station 1)
btbo = up≼ br1-R (Btbo.btbo-B MV.Bᶻᶠ MV.okᶻ MV.stᶻ)
```

##### YiCWStations（逐字源文）

### 新终点的前三站
验收文件，读记号；新终点实际底上第 0、1、2 站的值下界均实填。
来源：YiFRStations，BTBO 入口换 YiCWBTBO，其余参照与语义接线复用原证明。
Kᵗ 的左边沿用原参照 row（仅为记号参照）；右边为新终点的实际 station，未声称全站成立。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWStations where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; cong; sym; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l)
open import OCF.Lean.YiGIInst
open import OCF.Lean.YiExSuff
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiRefTw2 using (tree-≼)
open import OCF.Lean.YiEXRow using (down₁; row₂-btbo)
open import OCF.Lean.YiKCSem using (rr≼)
open import OCF.Lean.YiCWTable using (rbΛ; rbᵗ; EBOᵗ)
import OCF.Lean.YiCWActual as C
open import OCF.Lean.YiCWBTBO using (btbo)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiLBInv using (from⊴)
open import OCF.Lean.YiKQSuff using (read≤)
open import OCF.Lean.YiKSDesc using (rowN)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
Kᵗ : ℕ → Set
Kᵗ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (C.station n)
k0 : Kᵗ 0
k0 h = ≼-trans (tree-back h) (K.lower⁰ (K.G⁰.m-next (O.Ωt B.zero) refl (λ n → refl) (K.m1 refl K.mz)) (back h))
k1 : Kᵗ 1
k1 h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 1)) (≼-trans down₁ (≼-trans row₂-btbo (≼-trans btbo (rr≼ (C.station 1))))))
station-step : ∀ n → K.readRW (C.station n) ≼ K.readRW (C.station (suc n))
station-step n = subst₂ _≼_ (cong K.readRW (sym (C.branch-form n))) (cong K.readRW (sym (C.branch-form (suc n))))
  (K.◃→≼ (TB.mono B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero)
    (O.+-mono (O.cum C.FΛ n) (proj₂ (O.upz (suc n) (O.Ωt (B.tw (suc n))))))))
k2 : Kᵗ 2
k2 h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 2))
  (≼-trans row₂-btbo (≼-trans btbo (≼-trans (rr≼ (C.station 1)) (station-step 1)))))
upper : ∀ n → K.readRW (C.station n) ≼ K.readRW EBOᵗ
upper zero = ≼l zero (≼-refl _)
upper (suc n) = ≼l (suc n) (≼-refl _)
branch-upper : ∀ n q → K.readRW (proj₁ (C.Step.out n (C.Step.chain n q))) ≼ K.readRW (C.station (suc n))
branch-upper n q = ≼-trans (rowN (F.kp (B.tw (suc n)) (P.Ok-tw (suc n)) (inj₁ (inj₁ tt)) (P.z≤ (B.tw (suc n))))
  (C.Step.out n) (C.Step.feed n) q (read≤ (proj₁ (C.Step.out n (C.Step.chain n q))))) (rr≼ (C.station (suc n)))
floor : ∀ q → (h : SI.E.HC (Keel⁻.row keelᴱ 2)) → SI.E.tree h ≼ K.readRW (proj₁ (C.Step.out 2 (C.Step.chain 2 q)))
floor q h = ≼-trans (k2 h) (from⊴ (ψ-⊵ (B.tw 3) (P.Ok-tw 3) (rbᵗ 3) (C.baseᴱ 3)
  B.zero (P.z≤ (B.tw 3)) (C.betaᴱ 3) (C.Step.g 2 (C.Step.chain 2 q))))
```

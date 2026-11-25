# YiUD 同编号配对否定与原q0两次原生折叠：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiUDQ0Align、YiUDQ0Update |
| 文件前缀 | `YiUD` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiUD 原生展开、同编号否定与未证独立界复核” 一节 |
| 主审复核后的一句结论 | 2件主审8G冷编0；同编号内部配对否定、原q0两次原生更新成立；独立q0界/控制律/FirstMissing仍缺，连续受阻部分交付、非路线否定。 |

## 简报原文

### 任务简报：上界判定（续）：直接在新折叠上建上界，不从旧块搬（数学，否定方向）（前缀 YiUD）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十七批两路之一（选项原文 "再派一路"），与在跑的 YiE3（第 3 站的工程层）、YiXV（收尾中）在数学上互不依赖。
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
- **上一路（YiUP，回报 `probes/Survey/Reports-2026-11-12/YiUP.md`）**：`YiUPBase.base-form`；从旧块搬上界的几种桥与结构前提被编译否定（临时源码在附件 `YiUP*-Codex.agda.txt`），所以**本路不再从旧块搬**，直接在主线折叠 `YiTBRow.ψ`（表 `rbᶻ`）上建上界。
- 上一路的配对否定（YiFN）：目标项不低于 ψ₀(Ω_{Ω_ω})（`YiFNTarget.lower`），链点输出只有相对上界（`YiFNUpper.strict-upper`）。
- 第 0 层的上界工具：`YiCeilRead`（`plus≼`、`next≼`、`limc≼`、`fold₀≼`、`ε₀-upper`、`chain≼`）、`YiCeilWit`、`YiCeilSmall`。YiXV（精确值一路，收尾中）的上界框架只读，且主审已核过它没有可以直接用到本题对象上的结论；它的阶段报告会列 "可复用技巧"，若已交回可参考。
- 判断：底已经是 "Ω 树加三段固定尾项"，增长只经孩子层号 h₁ 里的 c₁ 进入；上界的关键是把 "Ω 形状孩子层号上 Ω 树折到第 0 层" 的值用 c₁ 的某个上界控制住。

#### 要做的（按序）
0. **纸面估值与最小检查**：先写出你对 `Step.out 2 (Step.chain 2 q)`（q = 0、1）值的纸面上界估计（判断档）；在临时目录里，按性能手册把具体对象封装、对变量陈述，编译出 q = 0 的一条独立记号上界。不成立就停下回报。
1. **一条控制引理**：对 Ω 形状的孩子层号 `tw 2 ⊕ ↑ (tw 2) c`（c 是变量，带 "c 不高于某参照 u" 的前提），证 "Ω 树带这种形状的底折到第 0 层，值不高于 F(u)"，F 是你给的记号函数。
2. **沿链推**：由控制引理与链的递推（`Step.feed`）对一切 q 给出统一的上界 U，并与目标项比较：
   - U 低于目标项：编译 `¬FirstMissing`，再检查错位配对；若错位也被否定，是定义层面的问题，写成编译定理后停下，交作者。
   - U 不低于目标项：交 U 与比较，说明到这里判定不了。
3. 回报里纸面估计与编译结论分开写。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiUD`（模块名 `OCF.Lean.YiUD…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiE3`、`YiXV`、`YiCW`）。验收文件，文首标明。
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

### 主审复核说明

两件主审逐件8G自身接口冷编0，Checking仅自身；全文查源/报告及私有尝试，另独立只读审查。新增100同口径代码行，源与冻结快照首尾一致，正式源码禁项/洞/本机路径0。原q0、底所有目标分量及β均保留；q0-twice只是proj₁树等式，不称完整证据对或底函数相等。

no-same-index仅否定原q0内层“部分和第n项≤指定参照基本列第n项”，首项已矛盾；不否定自适应m(n)、原独立上界、其他q、FirstMissing或终点后支错位。目标HC、原底及起点均有闭实例。三种具体接线已实际尝试，停止是AGENTS允许连续受阻交精确余项，不援引第二次251、两次重设计被否定或上界为假；原控制引理/统一U等后续尚未完成。

原回报资源表的“墙钟秒”需更正：该列取RTS Total elapsed，不是独立外部计时；主审独立墙钟另记。原数据见[资源表](attachments/YiUD-Resources-Codex.json)。保留[原冻结估值](attachments/YiUD-Estimates-Codex.md)、[耗尽具体框架](attachments/Experiment-YiUD-DirectFrame-Codex.agda.txt)、[成功删减定位](attachments/Experiment-YiUD-ShapeFloor-Codex.agda.txt)、[变量化草稿](attachments/Experiment-YiUD-AtVariables-Codex.agda.txt)；私有草稿含设计洞，不是通过的数学模块。失败源没有主审原样重跑；跨线程通知拒绝后已从原任务线程取回材料，没有重试或绕过。

### 执行方完整原回报

### YiUD 完整回报：第 0 步未走通；同编号配对已否定

1. 判决与范围

对纲领与目标：本轮没有取得原 q=0 输出的独立记号上界，没有判断 FirstMissing，也没有证明主线定义丢值。没有改树、折叠、合法性、原底、原起点、原闭项或比较表。按简报的先后顺序，本路停在第 0 步，未开展变量 c 的控制引理、统一 U、U 与目标比较、¬FirstMissing 或后支错位检查。第 0 步“未走通”不等于估计为假，不关闭路线。

另有原生更新的编译等式：原 q0 等于 tw2 上从原 baseᴱ2、betaᴱ2 出发，先更新所有底分量和起点，再折一次同层 Ω 树；这不是独立上界，也不是改定义。

新增的编译否定只针对一种具体接线：把原 q=0 内链的第 n 个部分和，配给独立参照 ψ₀(Ω_{Ω+1}) 的第 n 个基本列项。n=0 已产生反例：原首行严格高于原 betaᴱ3，而参照的第 0 项 ψ₀(Ω_Ω) 不高于 betaᴱ3。允许错开或自适应选择参照编号的原上界仍未判定。这里是 q0 内部的配对，不是终点后支的错位配对；后者尚未开展。

纸面估值先保存于 YiUD-estimates-frozen.md，再写首个 Agda 文件：q=0 候选上界 ψ₀(Ω_{Ω+1})，q=1 候选上界 ψ₀(Ω_{Ω_{Ω+1}})。两者均为判断档。q1 的估计有意保守，不声称它低于 FirstMissing。没有把 base-form 外推到 q≠1，没有证明或声称三个 δ 的界，也没有删去原 β3 或孩子内 κ。

首个私有目录创建于 2026-11-15 16:00:23 +0800；YiUDMin.agda 写入于 16:01:41，首件编译日志完成于 16:01:58，耗时 16.957 秒。工具没有提供精确的任务启动时间，故不虚构启动耗时；首件在首次读完约定、简报与列明手册后即写出并编译。

| 问题 | 位置 | 档与状态 |
|---|---|---|
| 原 q0 在实际底、β3 上的 tw2 调用 | YiUDMin.out₀-form；仓库 actual-form | 编译等式 |
| 原 q0 的实际内层回灌链和部分和极限 | Rows.feed/chain/row/raw-form，Actual | 编译构造与等式 |
| 原 q0 等于两次 tw2 原生折叠 | YiUDQ0Update.q0-twice | 编译等式，不含值上界 |
| 原 q0 的独立上界 ψ₀(Ω_{Ω+1}) | 下述 upper₀ | 未填，判断/研究命题 |
| 同编号的部分和到参照项配对 | no-same-index | 编译否定定理 |
| 可选择参照编号的配对 | YiUDAtVariables.Actual.Match | 充分接线未填；不声称等价 |
| q1 独立界、变量 c 控制、统一 U、FirstMissing 否定及后支错位 | 原简报后续步骤 | 按序未进入 |

没有有限数值测试。语法 refl 等式是编译定理，不将框架的类型检查说成上界已证。

2. 文件、冷编与资源

新增仓库文件共两件：

| 文件 | 物理行 | 代码物理行（含空行） | 非空代码行 | 冷编退出码 | 最大驻留字节 |
|---|---:|---:|---:|---:|---:|
| probes/OCF/Lean/YiUDQ0Align.lagda.md | 84 | 78 | 69 | 0 | 1583573736 |
| probes/OCF/Lean/YiUDQ0Update.lagda.md | 41 | 35 | 31 | 0 | 1577919376 |

两件文首各4行。未修改任何已有仓库文件；README、LOG、台账、留档、src、archive 和并行前缀均未编辑。本回报与冻结表留私有目录，由主审决定留档和台账更新。

所有 Agda 运行均为 +RTS -M8G -s -RTS；本路同一时刻只跑一个。依赖保持缓存。两件分别只删除自身 probes/_build/2.8.0.2/agda/OCF/Lean/YiUDQ0Align.agdai 与 YiUDQ0Update.agdai 后冷编；每份日志只有自身模块的 Checking 行。未使用 --ignore-interfaces。以下驻留数字直接来自 RTS 的 bytes maximum residency，不当作进程 RSS；并行环境下耗时只作本次测量。

| 日志 | 退出码 | RTS 最大驻留字节 | 墙钟秒 | 内容 |
|---|---:|---:|---:|---|
| YiUDMin.log | 0 | 1408507448 | 16.957 | 首次规范对象与冻结目标 |
| YiUDDirectFrame.log | 42 | 1540006120 | 16.697 | 路径省写造成 UnequalTerms |
| YiUDDirectFrame-v2.log | 251 | 8431210288 | 158.804 | 修正路径后的具体同编号接线 |
| YiUDShapeFloor.log | 0 | 1405194696 | 17.07 | 删除上界接线的二分 |
| YiUDAtVariables.log | 42 | 1659658984 | 17.884 | 变量化，自适应 Match 留一个设计洞 |
| YiUDRefStart.log | 0 | 983121344 | 11.781 | 参照第0项的语法等式 |
| YiUDAlignNeg.log | 0 | 1592640056 | 17.013 | 同编号接线否定的私有试稿 |
| YiUDQ0Align-first.log | 0 | 1583573736 | 17.459 | 仓库文件首次编译 |
| YiUDQ0Align-cold.log | 0 | 1583573736 | 17.442 | 只删除自身接口的最终冷编 |
| YiUDUpdate.log | 0 | 1393946288 | 14.637 | 原 β3 与 q0 限制底的原生更新展开 |
| YiUDUpdate-v2.log | 0 | 1579104368 | 21.314 | 原 q0 两次原生折叠的私有检查 |
| YiUDQ0Update-first.log | 0 | 1577919376 | 21.007 | 原生更新仓库文件首次编译 |
| YiUDQ0Update-cold.log | 0 | 1577919376 | 20.987 | 原生更新文件只删除自身接口的最终冷编 |

最终源码 SHA256：

- probes/OCF/Lean/YiUDQ0Align.lagda.md：160c3ab3f632d173575badd7cdf228701210c2ab5169e42d4ee40b833c9dcd36
- probes/OCF/Lean/YiUDQ0Update.lagda.md：1ec3738c084316604d3aa9bf2ee6b4dc56257d7ad4b907998481e3f1d290c6a2
编译器：Agda 2.8.0.2。完整资源机器表：compile-runs.json；自查：audit-final.json。

3. 定理逐字陈述

以下代码的模块别名均按仓库文件：B/O/P 为 YiRWBlock/YiRWOps/YiRWPath，TB 为 YiTBRow，MT 为 YiMTTab，GI 为 YiGIInst，FR 为 YiFRStep，R 为 YiRefTw2，K 为 YiKVRel。全部档位为编译定理，最终冷编退出 0。

Rows 的变量前提可满足：A₀ 与 GI.betaᴱ3 是规范闭实例，Actual 已实填；reference-inhabited 给出参照 HC 的闭实例。no-same-index 的第二个参数是被否定的对象，不声称能实填。

```agda
Rows.raw-form : proj₁ raw ≡ proj₁ (O.limc⁺ row)
```

```agda
actual-form : proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)) ≡ proj₁ Actual.raw
```

```agda
row₀-strict : (A : F.Base (B.tw 2)) (β : O.Tr⁺ B.zero) →
  L.suc (K.readRW (proj₁ β)) ≼ K.readRW (proj₁ (Rows.row A β 0))
```

```agda
beta3-ref2-lower : (h : E.HC (E.EBOψ 2)) → R.Rt h ≼ K.readRW (proj₁ (GI.betaᴱ 3))
```

```agda
ref-start : E.fsn R.t₊ 0 ≡ E.EBOψ 2
```

```agda
start-lower : (h : E.HC R.t₊) → R.Rt (R.hω-inv h refl 0) ≼ K.readRW (proj₁ (GI.betaᴱ 3))
```

```agda
no-same-index : (h : E.HC R.t₊) →
  (∀ n → K.readRW (O.cum (λ j → proj₁ (Actual.row j)) n)
      ≼ R.Rt (R.hω-inv h refl n)) → ⊥
```

```agda
reference-inhabited : E.HC R.t₊
```

白话对应顺序：raw-form 展开直接 TBRow 内链；actual-form 将该调用逐字接回原 q0；row₀-strict 表示任意非零起点在该首行中至少严格升一步；beta3-ref2-lower 复用已有第 2 站下界；ref-start 核出参照第 0 基本列项；start-lower 将该项放在原 β3 以下；no-same-index 由首项矛盾否定整族同编号配对；reference-inhabited 显示否定的证书前提有闭实例。

所有值桥仅使用稳定的第 0 层两读回转换、树序严格性与第 2 站已知下界。没有搬运旧整折叠，也没有导入 YiXV 或 YiCW 文件。

YiUDQ0Update 的三条编译等式逐字如下；Twice 的两个参数已用规范闭实例 GI.baseᴱ2、GI.betaᴱ2 实填：

```agda
beta3-form : proj₁ (GI.betaᴱ 3) ≡ proj₁
  (TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (GI.baseᴱ 2)
    B.zero (P.z≤ (B.tw 2)) (GI.betaᴱ 2) (proj₁ (O.Ωt (B.tw 2))))
```

```agda
base-zero-form : ∀ i (u : i P.≤ B.tw 2) →
  proj₁ (GI.baseᴱ 3 i (P.inc B.zero u)) ≡ proj₁
  (TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (GI.baseᴱ 2)
    i u (GI.baseᴱ 2 i u) (proj₁ (O.Ωt (B.tw 2))))
```

```agda
q0-twice : proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)) ≡
  proj₁ (Twice.second (GI.baseᴱ 2) (GI.betaᴱ 2))
```

其中 Twice.upd i u 是在 tw2 上以原底分量 A i u 作起点折 Ωt(tw2)；first 是同一次折叠的零层输出；second 使用 upd 和 first 再折一次 Ωt(tw2)。q0-twice 本身逐字实例化两次原调用，不靠函数外延或旧块搬运。

4. 第一个精确未填命题与已尝试接线

原任务的第一个未填命题逐字为（独立参照 h₊ 不是原输出或其别名）：

```agda
upper₀ :
  K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)))
    ≼ R.Rt R.h₊
```

YiUDMin 中把原输出与该参照封为 opaque；只核了 out₀-form 与合法性，没有给 upper₀ 的项。

尝试 A（具体行与同编号参照）：YiUDDirectFrame.agda 直接用 l≼ (λ n → ≼l n …) 对原输出作上界接线。第一稿把实际 feed 路径 self ∙ lift 写成 lift，退出 42；修正该字面路径后，构造和等式可核，但具体上界接线的框架在 8G 下退出 251。该日志没有完成的 definitions profile，不能伪造其热定义统计。

定位 A：删去 upper₀ 声明与证明，保持原 Rows、A₀、Actual、actual-form 和 opaque 参照，得到 YiUDShapeFloor；退出 0。profile 为 Rows.raw-form 52ms、actual-form 192ms，总计约17秒，最大驻留 1,405,194,696 字节。由删除运行定位到具体上界接线，而非基底展开等式。

尝试 B（变量化源与参照、自适应编号）：YiUDAtVariables 将源 A、行族 F、展开等式和参照证书 h 全作为变量，先证明 Prefix.close、Reference.into、Solve.solve，再一次实参化为原 Rows 和 h₊。退出 42 仅因一个明确设计洞，框架17.884秒、最大驻留1,659,658,984字节。余项逐字为：

```agda
-- S = 私有 YiUDShapeFloor；S.Actual 等于仓库模块的 Actual。
-- R.h₊ : E.HC R.t₊ 是既有的独立记号证书。
match₀ : (n : ℕ) → Σ ℕ λ m →
  K.readRW (O.cum (λ j → proj₁ (S.Actual.row j)) n)
    ≼ R.Rt (R.hω-inv R.h₊ refl m)
```

这是所试的充分接线，没有证明它与原 upper₀ 等价，也没有证明它可满足。尤其不能将对未知 Match 的条件定理当成第 0 步通过。同编号 m=n 已被仓库 no-same-index 精确否定；没有否定自适应的 m(n)，也没有否定整体 upper₀。变量化后没有再撞堆墙，因此本次停止不援引“改形状后第二次 251”，也不声称“两次实质证明重设计均被类型反例否定”。停止理由是连续具体接线后，第 0 步的独立界仍未填，按原顺序交精确余项；不越过它改题。

尝试 C（实际底的原生更新）：在 YiUDUpdate 临时最小实例中先核 beta3-form 和 base-zero-form，再将两次同层折叠写成 Twice，q0-twice 退出0。此后提取到 YiUDQ0Update 并冷编退出0。它保留全部原底与原起点，给出了原 upper₀ 的另一份逐字源表达，但没有取得它的独立上界。没有由这个展开擅自引入“更新保上界”的全域律；规范实例的第二次折叠值仍未填。停止依据仍是第0步的独立界未填，未把新展开当成上界或按其纸面读法判否。

5. 候选、放下办法、偏离和事故

- 候选 q0=ψ₀(Ω_{Ω+1})：仍未证；同编号配对被否定不关闭它。
- 候选 q1=ψ₀(Ω_{Ω_{Ω+1}})：只冻结了估值，未进行 q1 界证明。
- 具体 l≼/≼l 同编号接线：先触发251，二分与变量化后，首项机制被编译否定。
- 自适应 cofinal Match：未填；记录为候选，不写“只有此法”。
- 原 q0 作为两次同层 Ω 折叠的源表达：已编译展开，第二次折叠的独立值界未填；没有把它改写成新的树或折叠定义。
- 没有开旧整折叠搬运桥，也没有试改主线定义。已有反例的适用范围只按其陈述读，没有将它们外推成所有旧工具均不可用。
- 第一稿的路径省写错误已经修正，原稿与报错保留在 YiUDDirectFrame.v1.agda.txt / YiUDDirectFrame.log。它是本路错误，不是数学障碍。
- 最早 YiUDMin 和 YiUDDirectFrame 的调用未包 timeout 600；这未符合大 refl 的超时包装约定。两次均自行返回，未发生超时杀进程；从后续定位与仓库验证起均使用 timeout 600。所有调用始终带8G上限；没有原样重跑251，没有擅自加堆。
- 读取 ps 被系统拒绝，未绕过；因此没有取得全局 Agda 进程数量的工具证据，不将它写为0。本路调用始终逐一完成后才启动下一次。
- 一次跨线程状态通知被自动审批审查拒绝，理由是目标线程及内部路径内容未获明确授权；没有重试或绕过，改在当前对话交付本回报。这不阻塞文件和数学结果交付。
- 没有派子智能体、装包、pkill、提交或推送；没有浏览外部网页或绕过内容过滤。

直接读取范围：原始简报与补充护栏完整读；AGENTS.md 完整读；EBOHandbook 第4节完整读；Bedrock C-9、C-10、S-1、S-3、H-6、Q-1、Q-23 指定条目读。YiFRStep/YiUPBase/YiMTTab/YiMSShape 的相关定义直接读，TBRow/RWFold/RWOps/RWPath/KVRel/KSDesc/KDStep/FRStations 的所用定义与签名直接核过。YiCeil*、YiXV* 和上批 YiUP 回报只查了所需范围，未把没有冷编复核的转述当本轮新增定理。没有导入运行中的 YiXV 文件，所以不存在其导入时冻结哈希。本轮依赖用现有接口，不声称对全部依赖作了从头冷编独立审核。

工具元数据：当前为 Codex；接口未提供精确模型型号、推理档和本轮 token 用量，不写0。

6. 冻结与交付

仓库源码快照：YiUDQ0Align.lagda.md.snapshot 与 YiUDQ0Update.lagda.md.snapshot。完整源码/日志/原简报/护栏/估值/回报/审计资源表的 SHA256 与字节数见 SHA256-freeze.tsv（清单自身不自哈希）。最终仓库源码与快照哈希一致。

由主审核陈述、禁项并删自身接口冷编后才认可；本路不自行更新 README/LOG/台账或采用任何候选。最终禁项与本机路径扫描均为0，对本路两件仓库新文件逐件检查；两件冷编均退出0、日志均仅自身Checking。私有一次性试验有设计洞、被否定接线和本机路径，已明确分档，不能当成通过的成品。

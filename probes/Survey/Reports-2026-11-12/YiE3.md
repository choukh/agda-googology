# YiE3 声明定位与对象封装：变量框架8G停报：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | 0数学模块；临时成功/失败/未编源及数据/日志附件留档 |
| 文件前缀 | `YiE3` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiE3 工程定位、封装与未完成变量框架复核” 一节 |
| 主审复核后的一句结论 | 主审三件成功源5G冷编0，原inner-two声明触发8G已定位；Base/Objects封装可编，Frame改形状后8G251；完整接线/同义对照未完成，按简报停报、非数学否定。 |

## 简报原文

### 任务简报：第 3 站的工程层：按性能手册定位、封装、变量化（工程）（前缀 YiE3）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十六批（选项原文 "现在派 (Recommended)"）。作者原话："内存等性能问题参考手册，我记得我们之前专门整理过手册的"。第 3 站的具体对象上已两次 8G 堆耗尽（YiMS 沿分支展开；YiCK 只写出具体的内层链结构）。本路只做工程：按手册把这一站的对象与那一条不等式的框架做到能在 8G 内编译，**不要求证出不等式本身**。与在跑的 YiUP、YiXV 在数学上互不依赖。
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
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（另见上面的共同陈述）
- **两次撞墙的材料**（先读，不原样重跑）：`probes/Survey/Reports-2026-11-12/attachments/Experiment-YiCKStep0-Codex.agda.txt`（65 行，写出实际的 c₁、h₁、`baseᴱ 3` 的路径限制、`betaᴱ 3`、结构化的内层 `feed`/`chain`/`out`、第一行与见证 1 的接线；整件 8G 耗尽，日志定位不到是哪条声明）；`Experiment-YiCKStep1-Codex.agda.txt`（未编译的草稿）；`Experiment-YiMSBranchS-Codex.agda.txt`（沿分支展开到 ψ₀(Ω_Ω+2)，8G 耗尽）。回报 `YiCK.md`、`YiMS.md`。
- **手册**（务必读这些具体条目，不要只看标题）：
  - `probes/Survey/EBOHandbook.md` 4.2 节 "实测有效的手段" 第 1 至 8 条（陈述逐字写；大参照树放 `opaque` 导出接口；隐式参数写出来；行与链写成顶层名字；不对大项 `with`；不用直接计算证明大的不等式，改分步；按功能拆文件；一次有意的加堆）与 4.6 节（"未测，值得先试" 一表）。
  - Bedrock 的性能手册（本仓库外，作者定不进仓库）：`<主目录>/Agentic/Bedrock/dev/cubical-agda-performance.md`。先读开头的分诊步骤与症状表（第 80 至 120 行），再读：**C-9**（在变量上陈述引理，定义等式作假设，在唯一的调用点用 `refl` 实例化）、**C-10**（具体的站作 opaque 原子或模块参数）、**S-1**、**S-3**（重的构造在出生处封进 `opaque`，连同规格）、**Q-1**（`agda --profile=definitions` 定位热定义）、**Q-23**（草稿里用一个洞量框架的底价）、**Q-7**、**Q-25**（跑不完时二分）、**H-5**、**H-6**（不原样重跑；加堆很少救得了爆炸）、**T-15**（在对策处写 `-- perf:` 注释）。它的实测来自 `--cubical` 加 HIT 的开发，手册 4.6 节已标出哪些适用、哪些不适用。
- 已有的封装先例：`YiS2Low` 第 31 行把 `hc-row`（沿良基证明算出的参照树）放进 `opaque`；`EndLowAccept.treeE`（手册 4.2 第 2 条）。

#### 要做的（按序）
0. **定位**（在临时目录，不进仓库）：把 `Experiment-YiCKStep0` 按声明二分（每次只保留前 k 条，或把后面的换成洞），每段记秒数与 `+RTS -s` 的 maximum residency，找出是哪一条声明把框架推过 8G；能跑完的段用 `--profile=definitions` 看热定义（Q-1）。交一张表：声明、秒数、峰值、是否撞墙。
1. **封装**：新建一个对象模块，把第 3 站要用的具体对象（`Step.chain 2 1` 即 c₁、孩子层号 h₁、限制后的底 `λ i u → baseᴱ 3 i (inc c₁ u)`、`betaᴱ 3`、内层链、目标项的参照树与 HC 证书）在出生处放进 `opaque`，每个都导出它的定义等式（在 `opaque` 块里证）以及后面要用的少数形状引理（如 `YiLBActual.out-child` 那种接线）。
2. **变量化**：把 `missing-child-low₁` 改写成在变量上的陈述（C-9）：例如一个参数化模块，参数是 c、h、底、起点以及它们各自 "等于实际对象" 的等式；不等式里只出现这些变量与 `opaque` 的原子。再在唯一的调用点用第 1 步的定义等式实例化，接回原来的 `FirstMissing`。证明的困难部分留作模块参数（仓库文件不许有洞），只要求框架编译通过。
3. **对照**：对同一个小引理，分别用 "具体对象直接写" 与 "变量化加封装" 两种写法各编一次，报秒数与峰值（同一会话、同一上限），说明效果。
4. **回报**：框架模块编译通过（8G 以内）；按 T-15 在每处对策旁写 `-- perf:` 注释；交第 0 步的定位表和第 3 步的对照数据，格式能直接补进手册 4.6 节的 "未测" 一表（由主审补）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiE3`（模块名 `OCF.Lean.YiE3…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiUP`）。验收文件，文首标明。
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
- **停下的条件（本路特别规定，覆盖上面的通用写法）**：退出 251 时**不原样重跑**（Bedrock H-6），先按下面第 1 至 3 步改形状并定位；改过形状后在同一上限（8G）下仍撞墙，才停下回报，并附上二分或 profile 的数据。需要加堆时不要擅自加，在回报里写明要多少、为什么（Bedrock H-5，手册 4.2 第 8 条：一次有意的加堆只在别的路不编译时由主审安排）。
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

本路按原8G停止条件交部分工程回报：定位与对象封装成立，变量出口框架/FirstMissing接线与同义对照未完成，未否定数学目标。原失败整件和耗尽Frame没有原样重跑。主审全文查源与报告，三组独立只读审查；复制成功Base/Objects及Cut18Profile到主审私有目录，自身无接口、依赖热，以5G独立冷编三件全0，Checking仅自身。Base/Objects墙钟18.020/17.920秒、maximum residency 1619206704/1597051904B；Profile段24.530秒、2597634840B，逐定义Total 24346ms、Miscellaneous17589ms、inner-one6757ms。原8G实验与主审5G复编上限/并行条件不同，不作提速对照或比值。

Objects.output-actual等的是整个Tr⁺输出，确接原q1；限制底/β/孩子内κ未替换。内链按形状输运构造，但未证原输出的该内链分解等式。Frame仍把原具体out(chain1)写在后段类型中，不能称完全变量化；low参数仍是固定q1、全部HC的原困难比较，未实填。Use/TwoSealed都是未编草稿；TwoSealed保持原小引理目标，尚无资源结果。实验中的c₁-shape可与既有MS同域形状结果复用，具体别名调用仍须将来编译核实，不因该判断改动已测冻结源码。

仓库0新数学模块；通过的临时构造与失败/未编草稿均以下列附件留档，不并入产品成本。原冻结表所有项目及原依赖源SHA核对一致，禁用构造/洞/源码本机路径0；路径指针越界等事故保留原回报。原报告SHA256为0bbf3eff7dc1d64ef83a99937fbb80ed9ae6ba5375e919483d5f1f10cebff5df。

[YiE3Base](attachments/Experiment-YiE3Base-Codex.agda.txt)、[YiE3Cut12](attachments/Experiment-YiE3Cut12-Codex.agda.txt)、[YiE3Cut18](attachments/Experiment-YiE3Cut18-Codex.agda.txt)、[YiE3Cut18Profile](attachments/Experiment-YiE3Cut18Profile-Codex.agda.txt)、[YiE3Cut19](attachments/Experiment-YiE3Cut19-Codex.agda.txt)、[YiE3Cut20](attachments/Experiment-YiE3Cut20-Codex.agda.txt)、[YiE3Frame](attachments/Experiment-YiE3Frame-Codex.agda.txt)、[YiE3Objects](attachments/Experiment-YiE3Objects-Codex.agda.txt)、[YiE3TwoSealed](attachments/Experiment-YiE3TwoSealed-Codex.agda.txt)、[YiE3Use](attachments/Experiment-YiE3Use-Codex.agda.txt)。

资源表见[测量数据](attachments/YiE3-Measurements-Codex.json)；脚本见[测量脚本](attachments/YiE3-Measure-Codex.py.txt)；成功profile与两份失败日志见[成功段](attachments/YiE3-Cut18Profile-Codex.log.txt)、[Cut19](attachments/YiE3-Cut19-Codex.log.txt)、[Frame](attachments/YiE3-Frame-Codex.log.txt)。这些报告/日志附件仅替换本机路径，原始字节与哈希保留在私有冻结材料；Agda源码附件逐字保留。

### 执行方完整原回报

### YiE3 工程路完整回报（第五十六批，2026-11-15）

#### 1. 判决、范围与逐步状态

对纲领与目标：没有改树、折叠、合法性或实际继承底与起点，没有新增第 3 站或 EBO 的值下界，没有否定 FirstMissing。原 CK 整件失败源码没有重跑；先按声明截断定位，随后完成一版出生处 opaque 的实际对象封装。变量化框架在相同 8G 上限下仍耗尽，触发原简报停止条件；本路已停止所有 Agda、后续实验和仓库正式化，只整理材料与冻结。

本轮工程目标未全部完成。**第 0 步定位完成；第 1 步有临时编译通过的对象封装；第 2 步变量框架 251，唯一调用点草稿未编；第 3 步两写法完整实测未完成。没有仓库新增文件，全部结果留在本私有目录，交主审独立冷编。** Base/Objects 的“编译定理”仅指本路 Agda 初次冷编 0；主审核准前不作为已复核结果。

停止依据是原简报的原文：“改过形状后在同一上限（8G）下仍撞墙，才停下回报，并附上二分或 profile 的数据。”本次第二种形状已同时采用出生处 opaque、变量环境、定义等式、变量迭代引理；YiE3Frame 随后 251。没有加堆，也没有在这次 251 后再编译、再二分或改题。

| 问题 | 位置 | 档与判决 |
|---|---|---|
| 原失败整件的首个超预算声明 | 原 YiCKStep0 第 54–55 行 `inner-two` | 有限性能测试：前缀到 53 行通过，加入这条声明则 251；未区分签名与证明体成本 |
| 原 `first-row` 自身是否超预算 | 原第 56–58 行 | 未判定；含它的前缀已经先遇到 inner-two，不能归因给 first-row |
| 实际 c₁、h₁、限制底、起点及形状 | YiE3Objects | 编译定义/等式；8G 内初编 0 |
| 原 q=1 输出与封装输出的接线 | `YiE3Objects.output-actual` | 编译等式，不是值下界 |
| HC 闭项与封装参照族/闭参照树 | `hc`、`reference`、`target-tree` | 编译构造与定义等式，不是支配结论 |
| 带形状输运的内层回灌、链、前两点 | `inner-g/feed/chain`、`inner-zero/step/two` | 编译构造与等式；未声称已证它与整个 Ω 折叠的 first-row 分解等式 |
| 变量框架接回原 FirstMissing | YiE3Frame | 未验收；251；不计框架通过 |
| 唯一调用点（两项等式以 refl 实填） | YiE3Use | 已写草稿，未编译 |
| 同一小引理两写法对照 | YiE3Cut19 与 YiE3TwoSealed | 直接写法已测 251；封装变量写法只写草稿、未编译，不作已完成对照 |

原有与本路新建的源依赖没有变化；依赖哈希核对全为 true。没有导入 YiUP/YiXV，未以它们的未证上界实填任何前提。

#### 2. 第 0 步：声明二分、profile 与资源表

每次命令都是独立进程，堆上限 `+RTS -M8G -s -RTS`，`timeout 600`；Agda stdout/stderr 均落独立文件。measure.py 直接读取 subprocess 返回码，未经过管道。各轮自己的源文件此前均无接口；依赖使用已有接口。成功日志只有各自一条 Checking，没有共享依赖重编。

表中秒数为 Python monotonic 量得的整进程墙钟；另列 RTS Total elapsed，避免混用。maximum residency 是 GHC RTS 的整进程驻留峰值，不是 OS RSS；8G 是堆上限，不是整个进程的 RSS 上限。

| 临时文件 | 原文件截断点 / 内容 | 退出码 | 墙钟秒 | RTS elapsed 秒 | maximum residency bytes | RTS total memory MiB | 撞墙 |
|---|---|---:|---:|---:|---:|---:|---|
| YiE3Cut12.agda | 原 1–38 行，止于 h₁-shape | 0 | 16.536 | 16.441 | 1,531,392,840 | 2663 | 否 |
| YiE3Cut18.agda | 原 1–53 行，止于 inner-one | 0 | 19.667 | 19.566 | 2,361,492,232 | 4208 | 否 |
| YiE3Cut20.agda | 原 1–58 行，止于 first-row | 251 | 146.564 | 146.440 | 8,432,359,800 | 8298 | 是 |
| YiE3Cut19.agda | 原 1–55 行，止于 inner-two；带 definitions profile | 251 | 150.462 | 150.316 | 8,431,527,920 | 8298 | 是 |
| YiE3Cut18Profile.agda | 原 1–53 行，成功侧 profile | 0 | 20.952 | 20.844 | 2,332,758,176 | 4109 | 否 |
| YiE3Base.agda | 变量环境与变量迭代引理 | 0 | 17.209 | 17.114 | 1,613,455,216 | 2791 | 否 |
| YiE3Objects.agda | 分块 opaque 实际对象与等式 | 0 | 16.546 | 16.454 | 1,548,552,064 | 2645 | 否 |
| YiE3Frame.agda | 变量环境 + 两项定义等式 + 困难值参数 + 接线 | 251 | 122.465 | 122.333 | 8,431,834,168 | 8297 | 是，触发停止 |

Cut 名字只是运行标识，并非声明数量。二分顺序为 38→53→58→55 行；由 53 行成功、55 行失败确定加入的唯一声明是：

```agda
inner-two : inner-chain 2 ≡ inner-feed (inner-feed B.zero)
inner-two = refl
```

该定位只说明**这一原上下文里加入该声明使预算超限**。它不是等式为假的证明，也未排除上下文交互；没有把第一行折叠或整个内层回灌数学归类为已否定。

本机 `agda --help` 确认支持 `--profile=definitions`，帮助原文保存在 agda-help.txt。成功侧 profile 原样为：

```
Total                      20,786ms
Miscellaneous              17,632ms
YiE3Cut18Profile.inner-one  3,153ms
```

`inner-one` 占定义名下约 3.153 秒，Miscellaneous 占约 17.632 秒。没有进一步的 internal profile，不能把 Miscellaneous 全说成加载。两个 251 没有产生 definitions profile；不将缺数据当成已测。

进程起止估计记录在 measurements.json（以结果文件 mtime 减 monotonic 时长）。八次 Agda 运行互不重叠，本路同时只有一个 Agda。期间 root/XV 可能有并行编译，故墙钟仅作本会话量级，没有宣称单进程机器基准。一次只读 ps 检查被 sandbox 拒绝，未改用其他渠道绕过，也未声称已测全局进程数。

首个临时文件于 07:31:01 UTC 开始，07:31:17 结束，退出 0；符合首文件 30 分钟内写出并编译要求。

#### 3. 文件、定义与已编译定理

仓库新增、改动 YiE3 文件为 0，没有 .lagda.md 成品交付。依据停止条件，未在 251 后搬入仓库并重编。这里保留纯 .agda 临时实验，中文说明与 `-- perf:` 均在实验的对策旁。初次编译时各自接口不存在，所以 Base/Objects 是“自身无接口、依赖热”的初次冷编；没有在停止后再删接口重复自冷编。主审可独立删除本私有目录中自身接口再检查。

| 文件 | 源码行（含空白） | 状态 |
|---|---:|---|
| YiE3Base.agda | 37 | 初次冷编 0 |
| YiE3Objects.agda | 139 | 初次冷编 0 |
| YiE3Frame.agda | 30 | 251，未验收 |
| YiE3Use.agda | 23 | 未编译草稿 |
| YiE3TwoSealed.agda | 65 | 未编译草稿 |

完整定义与定理的名字、逐字声明、白话、文件、档位见 [declarations-and-theorems.md](attachments/YiE3-Declarations-Codex.md)，其中 Frame/Use/TwoSealed 单列未验收。原文源码全部原样保留，可核对提取表。主结果摘录如下（Q=YiE3Base，FR=YiFRStep）：

```agda
-- YiE3Base：变量上的出口接线与迭代等式。
raw-wire : ∀ q → collapse (make (FR.Step.chain 2 q)) (GI.betaᴱ 3)
  ≡ FR.Step.out 2 (FR.Step.chain 2 q)
iter-two : {A : Set} (f : A → A) (z : A) → O.iter f z 2 ≡ f (f z)

-- YiE3Objects：实际对象与实际继承底、起点。
c₁-def : c₁ ≡ FR.Step.chain 2 1
h₁-def : h₁ ≡ FR.Step.child 2 c₁
base₁-def : subst F.Base h₁-def base₁ ≡ (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
β-def : β ≡ GI.betaᴱ 3
output-actual : output ≡ FR.Step.out 2 (FR.Step.chain 2 1)
reference-def : ∀ h → reference h ≡ SI.E.tree h
inner-chain-def : inner-chain ≡ O.iter inner-feed B.zero
inner-two : inner-chain 2 ≡ inner-feed (inner-feed B.zero)
```

这些是编译等式/构造，不是原值不等式。r₁ 保留 MT.rbᶻ；实际底没有换成 B₀。对象上下文把层号、Ok、表和底一起携带，ctx-def 实填 `ctx ≡ Q.make c₁`，β-def 实填实际起点；c₁-def 与 output-actual 则将输出接回原 q=1。参照的 HC 沿 target-def 输运，且 reference-def 对每个 HC 证书成立，未添加 Funext。

内层分支与槽位路径借 h₁-shape 作命题输运，再在 h₁、base₁、β 上建立回灌；这些输运的定义式均已导出。没有证明这条输运后的链与整个 output 的 limc⁺ 分解，因此不把 inner-two 说成已经处理完原 first-row。封装版的 inner-two 与原直接版含有不同的透明边界和显式形状输运；未完成等义小引理对照前，不能据它给出提速倍数。

各 opaque 块都在出生处与规格一起写，参照、证书、环境、链分块；Base.iter-two 在函数变量上检查。Base.raw-wire 复用 YiLBActual.out-child，未重证出口。原 h₁/c₁ 形状证明来自 CKStep0 的前缀；目标 HC 复用 YiLBStart.hc-target；树输运拟复用 FR.tree-transport，最后者所在框架未验收。

#### 4. 第一个障碍、原目标与条件框架

原源码首个已定位的工程障碍是 `inner-two`；重写后的新障碍是 YiE3Frame 整模块 251。新日志只有自身 Checking 和 Heap exhausted，没有声明位置。**不能从现有数据精确判定新墙发生在 sealed-low、raw-low、actual-low、connect 或 first-at-one 的哪一条。** 因停止条件未再二分；不能把任何一条记为编译定理。

第 2 步草稿把环境（层号、Ok、表、底）d、起点 β 以及它们等于封装实际对象的等式作参数。困难值命题也是显式模块参数：

```agda
module Frame (d : Q.Ctx) (d-eq : d ≡ A.ctx)
  (β : O.Tr⁺ B.zero) (β-eq : β ≡ A.β)
  (low : (h : SI.E.HC A.target) → A.reference h ≼ K.readRW (proj₁ (Q.collapse d β))) where
```

d-eq/β-eq 的可满足实例已经由 Objects 的具体上下文与起点提供，唯一调用点草稿用 A.ctx/refl/A.β/refl。low 是原困难比较的改写，未实填，也未声称其可满足性已经另证；这是作者允许保留的模块参数。该框架后半仍在 actual-low/connect 的结论里写出原具体 FR 输出，不能宣称已达到“不等式里只出现变量与 opaque 原子”的全部工程要求；这是一处纸面复核发现的未完成点，不是对新墙机制的编译定位。

第一条数学余项仍是：

```agda
(h : SI.E.HC (E.fsn (Keel⁻.row GI.keelᴱ 3) 1)) →
SI.E.tree h ≼ K.readRW (proj₁
  (TB.ψ h₁ (proj₂ (P.Ok-tw 3) c₁) (MT.rbᶻ h₁)
    (λ i u → GI.baseᴱ 3 i (P.inc c₁ u))
    B.zero (P.z≤ h₁) (GI.betaᴱ 3)
    (proj₁ (O.Ωt h₁))))
-- c₁ = FR.Step.chain 2 1；h₁ = FR.Step.child 2 c₁。
```

output-actual 证明封装输出确实来自这个原输出；没有值支配、FirstMissing 见证、Tail 2 或 Kᴱ 3。本轮不需要证明该不等式，也没有以未证明它为停止理由；停止理由是形状重写后的框架再次耗尽。

#### 5. 第 3 步对照、可供手册使用的数据与未执行建议

完整的“同一个小引理直接写 vs 变量化加封装”对照**未执行完成**。直接侧是 Cut19 的 inner-two（带 profile 标志，251，150.462 秒到失败，驻留 8,431,527,920 bytes）；YiE3TwoSealed 保留同一字面的最终签名，并拟通过封装 feed、变量 iter-two 和定义等式输运得到，但没有启动编译。不得报告它通过，不得把 Objects 的不同上下文数字当作同引理对照，更不计算加速比。

可直接交主审挑选补入手册 4.6 的表项如下；“局部”与“未完成”须保留：

| 规则 | 本路实测 | 判决/限度 |
|---|---|---|
| Q-7/Q-25，声明二分 | 53 行成功 19.667 秒/2,361,492,232 bytes；55 行 251/8,431,527,920 bytes | 定位到原 inner-two 声明；未区分签名与证明体 |
| Q-1，definitions profile | 成功侧 total 20,786ms；Miscellaneous 17,632ms；inner-one 3,153ms | 标志本机支持；失败侧没有 profile；未作 internal profile |
| S-1/C-10，出生处 opaque | 实际对象封装 139 行，16.546 秒，1,548,552,064 bytes，0 | 封装可编；不是同义对照，不主张因果提速或值下界 |
| C-9/S-1，变量环境+封装 | Base 0；Objects 0；Frame 251/122.465 秒/8,431,834,168 bytes | 框架工程目标未完成；不能标作此组合已救活整件 |
| C-9，同义小引理对照 | 直接侧 251；变量+封装侧未编 | 仍未完成；无比例 |
| T-15 | 新临时源在每个 opaque/变量化对策旁写 perf 注释 | 已执行代码纪律，没有独立性能因果结论 |

如作者另行授权继续，建议先对 Frame 按声明二分，并把后半的具体目标也移到变量出口引理/封装接口，再测同一上限；这是未执行建议，不是要求改树定义，也不是路线否定。

#### 6. 偏离、事故、读取范围与冻结

- 停止后没有再跑 Agda、删接口、改源码、搬仓库或编译未验收草稿。只写报告、提取声明、做静态检查、拷原实验留档、核哈希。没有提交、推送、装包、pkill 或派子路。
- 仓库源码、README/LOG/台账/既有留档、src/archive 未修改；没有新增仓库数学文件。git 的 YiE3 前缀检查为空。其他并行变化没有触碰或回退。
- 范围事故：启动脚本额外在私有目录外写了 `<本路私有目录外的路径指针>` 一个本路路径指针，第一次调用 measure 用过它；随后一律使用本私有目录字面路径。该指针不在仓库，违反“仅自己的私有目录”范围，明确留档；未在停止后删除或移动它。
- 一次只读 ps 被 sandbox 拒绝，未请求提权或绕过。一次 git status 的未引号 glob 因无匹配而由 zsh 返回 1，随后改用带引号的 pathspec，确认 YiE3 前缀为空；这不是 Agda 失败。
- 禁用构造、洞与本机路径检查在 10 份新临时 .agda 中全为 0（audit.json）。选项均为 safe/without-K/lossy-unification，补足 cubical-compatible/guardedness/hidden-argument-puns；没有 cubical、K、postulate、Funext 或不相关投影开关。未产出 html 或切片，没有失败轮切片结论。
- 已完整读 AGENTS、原简报和 batch56 护栏。已直接读手册 4.1–4.6，含 4.2 实测八条和 4.6 未测表；已直接读 Bedrock 分诊/症状表及 C-9/C-10、S-1/S-3、Q-1/Q-7/Q-23/Q-25、H-5/H-6、T-15 的正文。Bedrock 未复制进仓库。Q-23 的洞测法没有执行；本路改用作者允许的困难模块参数，但框架没有通过，因此不报告 Q-23 实测成功。
- 已读 CKStep0/Step1、MSBranchS 原实验；CK 与 MS 回报的相关实际结果、失败点、事故和资源段落已读（原始内容另存）。源文件只读所用定义/证明段：FRStep、LBActual、LBStart、S2Low、MSShape、RWBlock/Ops/Path/Fold、TBRow、AbsSim/Inst、RefTw2、ExInst、FNTarget 等；不声称通读整个导入闭包。UPBase 曾只读作为背景，没有导入或引用其结论；XV 没有使用。外部数学文献没有重新检索；简报中的强度数值只作背景，未独立验收。
- 哈希 `starting-hashes.json` 是早期读取后、封装前的技能/简报快照；`dependency-initial-hashes.json` 是封装前的所用本地数学源快照，二者不是本对话开始前的全仓库冻结。结束核对均未变化。原实验副本与简报原文单独列在 ORIGINAL-SHA256SUMS.txt；全部原实验、草稿、最终通过的临时源、日志、测量表、声明表、本报告列在 frozen-hashes.json 与 SHA256SUMS.txt。源码没有在编译0后修改。

完整交付目录即本报告所在目录。主审应独立冷编 Base/Objects 并核陈述；Frame 是已耗尽形状，不宜原样重跑。原目标仍未判定，本回报没有关闭这条路线。

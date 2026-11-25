# YiE4 全封装、变量出口与整表参数化工程交付：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiE4Base、Cut19、Cut20、Objects、Frame、Use、Param、ParamFrame、Default、Inner、Instances、ParamInner；主审只整理新Cut20证明复用 |
| 文件前缀 | `YiE4` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiE4 完整工程出口及受控同义对照复核” 一节 |
| 主审复核后的一句结论 | 12件主审8G冷编0；复用nodeZ后594行。固定q1全HC难值界仍为参数，整表参数化/原表接线/内层整行通过；A/B单次直接251封装0，早期重叠排除；无无条件FirstMissing。 |

## 简报原文

### 任务简报：第 3 站的工程层（续）：按 SC7 的封法全封装、变量化、对表参数化（工程）（前缀 YiE4）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十八批（选项原文 "现在派 (Recommended)"），接续 YiE3（回报 `probes/Survey/Reports-2026-11-12/YiE3.md`）。本路只做工程，**不要求证出不等式本身**。与在跑的 YiCW（按龙骨的比较表）、YiUD（上界续）、YiXV（收尾中）在数学上互不依赖。
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
- **YiE3 交了什么、停在哪里**（附件 `probes/Survey/Reports-2026-11-12/attachments/Experiment-YiE3*-Codex.agda.txt`、`YiE3-Measurements-Codex.json`；手册 `probes/Survey/EBOHandbook.md` 4.6 节末的 YiE3 表）：
  - 二分把墙定位到 `inner-two : inner-chain 2 ≡ inner-feed (inner-feed B.zero)`（证明 `refl`）；前 53 行能编过，加上它就 8G 耗尽。
  - `Experiment-YiE3Base`、`Experiment-YiE3Objects`（出生处 `opaque` 封装 q1、`Ok`、表、限制底、起点、HC 与参照族）编过。
  - 变量框架 `Experiment-YiE3Frame` 改过形状后仍 8G 耗尽，后段还残留具体的 `out (chain 1)`；同义对照未完成。
- **主审的对症实测 SC7**（附件 `SelfCheck-SC7Seal.agda.txt`，手册 4.6 节末 "C-24 与 S-1 的一次对症实测"）：
  - 只把 `inner-feed` 放进 `opaque`，在块里导出定义等式 `inner-feed-eq`（`refl`）；`inner-one` 改由 `inner-feed-eq zero` 给出，`inner-two` 仍是 `refl`。
  - 原来 8G 耗尽的那一段，在 6G 上限下 17.9 秒通过，maximum residency 约 1.6G。
  - 机制：Bedrock C-24（用 `refl` 比较递推）加上重的函数没有在出生处封装（S-1）。
- **表的依赖**：`YiGIInst` 第 79–87 行的 `baseᴱ`、`betaᴱ`、`keelᴱ` 都固定用 `MT.rbᶻ Λ`；`YiFRStep.Step` 也固定用 `MT.rbᶻ`。在跑的 YiCW 在检验一张按龙骨的比较表 `rbᵗ`、`rbΛ`（附件 `SelfCheck-SC6Table.agda.txt`），若采用，第 3 站的对象会换成它下的版本。

#### 要做的（按序）
0. **全封装**（照 SC7）：把第 3 站上一切作函数用的折叠在出生处放进 `opaque`，各自导出定义等式：外层的 `Step.feed 2`、`Step.out 2`、`Step.g 2`，内层的 `inner-feed`、`inner-out`、`inner-g`，以及限制底 `base₁`、`base₀` 一类。然后把 YiE3 的 `Cut19`、`Cut20` 与 `Frame` 依次改成这种写法编译，每件记秒数与 maximum residency。
1. **完成变量框架**（C-9）：`missing-child-low₁` 写成对变量的陈述（链点、孩子层号、底、起点都是变量，各带 "等于实际对象" 的等式），证明里难的部分作模块参数；在唯一的调用点实例化，接回 `YiFRStep.FirstMissing`（见证 1）。要求整件在 8G 内编过，后段不再出现具体的链点输出。
2. **对表参数化**：把框架与对象层写成以表 `r : Rb Λ` 为参数（`pre`、`baseᴱ`、`betaᴱ`、`Step` 需要以 r 为参数的副本，写在新文件里，不改旧文件）；在 `MT.rbᶻ Λ` 处接回原定义（接线等式只在封装之后、唯一的调用点写，注意 C-24）。若参数化代价太大，先对 `rbᶻ` 完成，并逐条列出参数化要动的定义与代价。
3. **同义对照**（YiE3 未完成的那一项）：同一个小引理，"具体对象直接写" 与 "封装加变量化" 各编一次，同一上限、同一会话，报秒数与峰值。
4. **回报**：框架编译通过的模块表；每处对策旁写 `-- perf:` 注释；第 0、3 步的数据格式能直接补进手册 4.6 节（由主审补）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiE4`（模块名 `OCF.Lean.YiE4…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiCW`、`YiUD`）。验收文件，文首标明。
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

### 主审复核说明与当前入口

本路工程目标通过：12件正式源已全文读核，三组独立只读审查，主审逐件删自身接口以8G冷编全0，Checking仅自身。计入主审整理后594非空非整行注释代码行、638物理代码行；202.31秒、RTS maximum residency峰1728991120B。它们均为第4层验收工程，未增加前三层证书字段或产品成本，没有无条件FirstMissing或新增序数值界。

默认入口是[YiE4Default.FromOriginal.first-at-one](../../OCF/Lean/YiE4Default.lagda.md)，参数化内层整行是[YiE4ParamInner.At.first-row](../../OCF/Lean/YiE4ParamInner.lagda.md)。OriginalAtOne仍是原固定q1、全部HC的困难值界；与封装Missing只给双向蕴含，不是互逆函数/类型等式。其余环境/等式/HC前提有规范实例，原表与空表均列出。对r:RbΛ的孩子表确取r分量，未残留固定rbᶻ；原表处接回原GI/FR对象。

主审仅整理了一处新文件的证明复用：Cut20.row0签名不变，改为调用已有YiLTLim.nodeZ，并标明来源。执行方[原Cut20](attachments/YiE4-Cut20-Original-Codex.lagda.md.txt)与[原冻结表](attachments/YiE4-Producer-Freeze-Codex.json)逐字保留；原170项均可核，当前正式源仅该处与原稿不同。[主审接受的源码哈希/计数/冷编表](attachments/YiE4-Root-Accepted-Codex.json)对应修订后12件，已全部重编。原报告的“row0两个构造子消去”属修订前实现；当前复用旧消去接口。所谓全封装限任务列出的折叠/限制底函数，不包括投影、make、a或chain等普通函数。报告“未采用fallback”只指未采用工程备选方案，不表示删除TBRow的缺表回退行。

A/B源的函数体、最终目标、导入/选项/heap一致：[直接源](attachments/Experiment-YiE4ABDirect-Codex.agda.txt)、[封装源](attachments/Experiment-YiE4ABSealed-Codex.agda.txt)、[差异](attachments/YiE4-AB-Diff-Codex.patch.txt)。同8G、同会话的单次组合改写（opaque+定义等式+变量迭代引理），直接251：146.753秒/8431556536B；封装0：16.415秒/1494526184B。外部墙钟与RTS elapsed分开，不能叫OS RSS、不能算成功编译提速比或单独归因opaque。见[直接测量](attachments/YiE4-AB-Direct-Codex.json)、[封装测量](attachments/YiE4-AB-Sealed-Codex.json)及[直接日志](attachments/YiE4-AB-Direct-Codex.log.txt)、[封装日志](attachments/YiE4-AB-Sealed-Codex.log.txt)。原失败源未由主审原样重跑。

[完整测量汇总](attachments/YiE4-Measurements-Codex.json)仍含premises/cut20-v3等早期重叠轮，不能整张表当有效基准集；必须携带[事故时间戳](attachments/YiE4-Incident-Times-Codex.json)与[中断轮说明](attachments/YiE4-Interrupted-Run-Codex.json)。Cut20 v2仅runner130，Agda原退出码未知，不能补记251。默认出口墙只定位到新增声明整体，v2源未单独即时快照，不当严格单变量A/B。重建早期失败源不是原时点冻结。原自冷编资源是修订前[执行方12件表](attachments/YiE4-Producer-Modules-Codex.json)，声明[检索索引](attachments/YiE4-Declarations-Codex.md)须连模块参数与正式源阅读。

### 执行方完整原回报

### YiE4 完整回报：工程出口完成，值界参数保留

本轮对纲领与目标的意义：已经把第3站固定链点1的工程框架接回原 `YiFRStep.FirstMissing`，并完成 `r : Rb Λ` 参数化与原表实例接线。树、折叠、合法性与旧源码均未修改。结果是条件定理，不是新的无条件序数值下界；原固定链点1、全 HC 的困难值界没有实填。本文不宣称树已自足，不否定任何数学路线。

正式源码只新增 `probes/OCF/Lean/YiE4*.lagda.md`。入口是 `YiE4Default.FromOriginal.first-at-one`；参数化内层整行在 `YiE4ParamInner.At.first-row`。全部最终源码副本在本目录 `final-source/`，逐字声明索引在 `declarations.md`，全部编译原始输出是本目录各 `.log`，每次调用与测量在对应 `.json` 和合并表 `measurements.json`，冻结见 `SHA256SUMS.txt`、`frozen-hashes.json`。主审仍须独立从头编译、检查陈述与禁用构造。

#### 1. 按原顺序的交付

| 步骤 | 本轮结果 | 档 |
|---|---|---|
| 0 全封装与 Cut19/Cut20/Frame | 外层 g/feed/out、限制底、内层 g/feed/out 均在本路的出生处 opaque；导出定义等式；改写的 Cut19、Cut20 和完整变量 Frame 都通过8G | 编译定理；资源数据为有限工程测试 |
| 1 完整变量框架 | 链点 c、层号 h、合法性 o、表 r、底 bs、起点 β 全作变量；等式限定实际对象；出口只用变量和 opaque 原子；唯一调用点给出条件 `FirstMissing`、见证1 | 编译定理，困难值界作显式模块参数 |
| 2 整张表参数化 | `pre`、`baseᴱ`、`betaᴱ`、`Step`、实际 q1、限制底、变量框架及实际内层整行均以 `r : Rb Λ` 参数化；在 `MT.rbᶻ Λ` 处通过变量等式接回原定义 | 编译定理；未采用 fallback |
| 3 同义 A/B | 原直接 `inner-two` 一次251；同函数体、同目标的出生处封装加变量迭代引理一次0；相同8G、相同会话、无 profile 标志、各自没有自身接口 | 有限工程测试；失败与成功并列，不计算提速比 |
| 4 自查与冻结 | 每个正式文件删除自己的字面接口后冷编0，依赖保持热；每份冷编日志只一条本模块 Checking；禁用构造、洞、Funext、本机路径检查0 | 编译与静态工程检查 |

问题表：

| 问题 | 位置 | 档与当前范围 |
|---|---|---|
| 固定q1的原值界仍未实填 | YiE4Default.OriginalAtOne | 编译定理仅给出它与封装参数的双向转换及条件FirstMissing；不宣称无条件值界 |
| 直接写法在8G失败 | 私有YiE4ABDirect.inner-two | 有限工程测试：251，不是等式为假的证明 |
| 早期本路编译有重叠 | Cut20 v2/premises/v3 | 工程事故，区间见时间戳；初测排除出受控性能证据 |
| 全机是否独占未观测 | ps观测被sandbox拒绝 | 判断的证据范围受限；本轮不声称全机独占 |

`Cut19` 的形状呈现有一处明确改写：用带封装 branch 的显式 Ω 节点给出 c₁，而非让下游反复计算旧 feed zero；`c₁-actual` 证明它等于原 `FR.Step.chain 2 1`，`h₁-actual` 证明对应孩子层号。它们是对旧对象的外部等式，不改旧树定义。`Cut20.first-row` 还证明整行分解，没有把二次迭代等式当成整行分解。

#### 2. 最终文件与冷编

以下都使用 `timeout 600`、`+RTS -M8G -s -RTS`。外部墙钟由 Python monotonic 单独计时；RTS elapsed 与 maximum residency 是 Agda/GHC 自报的整进程数据。maximum residency 不是 OS RSS，8G 是堆上限；代码段行包含空白与注释，不作成品成本比较。

| 文件 | Agda行/物理行 | 冷编退出 | 外部墙钟秒 | RTS elapsed秒 | RTS maximum residency字节 |
|---|---:|---:|---:|---:|---:|
| YiE4Base | 37/42 | 0 | 16.571 | 16.479 | 1,594,250,456 |
| YiE4Cut19 | 93/98 | 0 | 15.762 | 15.671 | 1,594,641,000 |
| YiE4Cut20 | 30/35 | 0 | 15.656 | 15.566 | 1,482,308,360 |
| YiE4Default | 72/77 | 0 | 16.551 | 16.460 | 1,494,593,528 |
| YiE4Frame | 37/42 | 0 | 16.594 | 16.503 | 1,594,315,376 |
| YiE4Inner | 45/50 | 0 | 16.544 | 16.452 | 1,762,457,584 |
| YiE4Instances | 26/31 | 0 | 16.506 | 16.415 | 1,539,702,800 |
| YiE4Objects | 48/53 | 0 | 16.704 | 16.612 | 1,646,038,664 |
| YiE4Param | 95/100 | 0 | 16.667 | 16.576 | 1,707,244,888 |
| YiE4ParamFrame | 56/61 | 0 | 16.547 | 16.455 | 1,491,994,992 |
| YiE4ParamInner | 57/62 | 0 | 16.617 | 16.525 | 1,663,499,760 |
| YiE4Use | 41/46 | 0 | 16.608 | 16.516 | 1,531,549,608 |

冷编依赖保留接口，每次只删除本文件自己的 `probes/_build/2.8.0.2/agda/OCF/Lean/YiE4….agdai`。路径逐项写在 `final_check.py`，没有通配删除。初次正式依赖构建的四份 `build-*.log` 也完整保留，不把含依赖 Checking 的构建轮当作最后自冷编。

#### 3. 关键定理与参数的逐字陈述

下列均为编译定理；凡处在参数模块内，其模块前提一并保留。完整源码和 `declarations.md` 列出其余规格与计算律。

##### 原值界未被换成存在性结论

`YiE4Default`：

```agda
Bound : E.T → O.Tr⁺ B.zero → Set
Bound t x = (h : SI.E.HC t) → SI.E.tree h ≼ K.readRW (proj₁ x)
OriginalAtOne : Set
OriginalAtOne = Bound LS.target (FR.Step.out 2 (FR.Step.chain 2 1))
from-original : OriginalAtOne → U.Missing
to-original : U.Missing → OriginalAtOne
module FromOriginal (low : OriginalAtOne) where
  first-at-one : FR.FirstMissing
```

白话：困难参数固定在旧链点1，对目标的每一个 HC 证书取值界；不是 Σ 链点，不是单个 HC。封装后的参数 `U.Missing` 与它有双向蕴含。原简报中把右侧写成孩子层折叠的版本，由现有 `YiLBActual.out-child` 逐字接线；本轮固定表的 `YiE4Use.collapse-wire` 及默认表的 `output-old` 保留该接线。`low` 是作者允许保留的未证前提，未声称它已可满足或已实填。

##### 完整变量环境

`YiE4Frame`：

```agda
module Frame (c : B.Tr (B.tw 2)) (c-eq : c ≡ C.c₁)
  (h : B.L) (o : P.Ok h) (r : TB.Rb h) (bs : F.Base h)
  (env-eq : (h , o , r , bs) ≡ Q.make c)
  (β : O.Tr⁺ B.zero) (β-eq : β ≡ A.β)
  (low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse (h , o , r , bs) β))) where
  context-eq : (h , o , r , bs) ≡ A.ctx
  sealed-low : (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ A.output)
  raw-low : (e : SI.E.HC A.target) → SI.E.tree e ≼ K.readRW (proj₁ A.output)
```

白话：层号与底的等式一起装在依赖环境等式 `env-eq` 中，链点与起点另有明确等式；没有把底换成标准底。后段没有具体 `out (chain 1)`。`YiE4Use.Use` 是固定表的唯一规范调用点，具体输出接线只放在该调用文件；参数表版的对应内容在 `YiE4ParamFrame.For`。

##### 参数表的分量与旧定义接线

`YiE4Param.At (r : TB.Rb B.Λ)`：

```agda
table : ∀ n → TB.Rb (B.tw n)
table n = proj₂ r n
module Step (n : ℕ) where
  child-table : ∀ c → TB.Rb (child c)
  child-table c = proj₂ (table (suc n)) c
```

白话：塔表、孩子表均来自 r 对应的分量；内层 branch 用的是 `D.Step.child-table 2 B.zero`，没有把这个孩子0的表偷偷换成独立的 `table 2`，更没有残留固定 `rbᶻ` 作为一般参数实例的孩子表。

`YiE4Default` 中 `D = R.At (MT.rbᶻ B.Λ)`：

```agda
pre-eq : ∀ n → D.pre n ≡ GI.pre n
base-eq : ∀ n → D.baseᴱ n ≡ GI.baseᴱ n
beta-eq : ∀ n → D.betaᴱ n ≡ GI.betaᴱ n
g-eq : ∀ n → D.Step.g n ≡ FR.Step.g n
feed-eq : ∀ n → D.Step.feed n ≡ FR.Step.feed n
out-eq : ∀ n → D.Step.out n ≡ FR.Step.out n
chain-eq : ∀ n q → D.Step.chain n q ≡ FR.Step.chain n q
output-old : D.output ≡ FR.Step.out 2 (FR.Step.chain 2 1)
```

白话：表取回原表时，参数化副本连同实际继承底与起点接回旧定义。没有使用函数外延；上述函数等式在变量处随规格证明，链等式只复合函数等式，不用 refl 对比两条具体递推。

##### 内层整行确实来自实际输出

`YiE4Cut20`：

```agda
first-row : TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁) (GI.betaᴱ 3) (proj₁ (O.Ωt h₁))
  ≡ O.limc⁺ (λ n → inner-out (inner-chain n))
```

`YiE4ParamInner.At (r : TB.Rb B.Λ)`：

```agda
first-row : D.output ≡ O.limc⁺ (λ n → Inner.out (Inner.chain n))
```

白话：后一条从实际 q1 对应环境，经已证明的形状等式输运到内层，整个输出等于内层各链点输出的部分和极限。输运后的合法性、表、底都带规范构造，r 的孩子分量也随环境输运；不声称内层链已经满足困难值界。

##### 其它前提确有规范实例

先于一般固定表框架编译了私有 `YiE4Premises.agda`，先于参数表框架编译了私有 `YiE4ParamPremises.agda`，都为0；不是有洞草稿。最终 `YiE4Instances.Canonical (r : Rb Λ)` 实填环境等式、链点等式、起点等式与 `A.target` 的 HC，并证明孩子表正是 r 的分量。又列原表和空表两个规范实例。`YiE4Use.Use.Inst`、`YiE4ParamFrame.For.Use.Inst` 是各自唯一的实际应用，全部非困难参数均给出具体项，未将半变量化文件算作交付。

#### 4. 障碍的精确定位及改写

1. 首次 Cut19 是 opaque/unfolding 布局的 ParseError，退出42，随后改为正确换行；首个有效临时文件于08:51:20 UTC开始、约15.58秒后通过，距首次时钟记录08:48:56约3分钟，满足30分钟要求。
2. Cut20 v1 退出42 `UnequalTerms`：封装 branch 后，`kp` 的零层不保留不再字面归约。v2 改用现成 `YiRWCheck.kp-z` 的 rewrite，后来日志达到 Heap exhausted；运行脚本被中断，Agda原始退出码未收回，不能记成已读到251。它不是通过。
3. 对该形状改用变量 `Keep zero` 的节点消去 `row0`，不让具体路径进入 rewrite；Cut20 v3 同8G通过，最终正式冷编再次通过。`row0` 的两个构造子分支对应 `YiKSDesc.rowN` 的零层消去方式；没有重证 `kp-z`。检索过 `YiRWCheck.node⊥`，它是旧 `YiRWFold.ψ` 的计算律，不直接是本路 `YiTBRow.ψ` 的规格。
4. 默认表接线 v1 原始退出251、47.134秒、RTS maximum residency 4,232,354,800B，日志明确 Heap exhausted/8G。保留完整失败源 `YiE4Default-v1-source.txt`，没有原样重跑。前缀 Cut1（到 out-eq）、Cut2（到 output-old）、Cut3（到 Use.Inst）均0，后者精确把加入的困难声明定位为 `Use.first-at-one`。三份源码和 definitions profile 日志保留；profile 时间均归 Miscellaneous，没有把它说成已定位某个内部归约热点。
5. 将该声明的直接闭输出 `subst` 改成已编译的变量 `at-one` 应用，v2 同8G通过：16.390秒/1,482,274,496B。后来增加原值界双向转换仍0，最终正式冷编亦0。没有因251加堆。

第一个尚未证明的数学余项仍是 `OriginalAtOne`，等价于原简报的 `missing-child-low₁`，固定原 q1、全部 HC。它不是工程停止障碍；本任务允许它保留为模块参数。没有关闭或否定该数学路线。

#### 5. A/B 与可直接补进手册4.6的材料

A/B 原始源是 `YiE4ABDirect.agda`、`YiE4ABSealed.agda`，逐字差异 `ab-controlled-diff.patch`。两侧都基于原 YiE3Cut19 的同一完整上下文、同一 inner-feed 函数体、同一最终签名 `inner-chain 2 ≡ inner-feed (inner-feed B.zero)`；封装侧把 inner-feed 在出生处 opaque，导出定义等式供 inner-one 使用，再以变量函数上的 iter-two 证明最终目标。没有换目标、heap、profile标志或导入上下文来凑成功。

| 写法 | 原始退出码 | 外部墙钟秒 | RTS elapsed秒 | RTS maximum residency字节 | 开始UTC |
|---|---:|---:|---:|---:|---|
| ab-direct | 251 | 146.753 | 146.634 | 8,431,556,536 | 2026-11-15T09:04:29Z |
| ab-sealed | 0 | 16.415 | 16.324 | 1,494,526,184 | 2026-11-15T09:07:35Z |

这是一次受控 A/B，未扩成重复尝试。直接侧按原退出码251保留，封装侧0；不报告比例，也不把别处等式的成功混入对照。两侧本路编译互不重叠。只读 `ps` 被 sandbox 拒绝，未提权、未绕过；故未观测外部进程，不能声称全机独占。

手册可用条目（由主审复核后更新，本路未改手册）：

| 规则 | 本次有限工程测试 | 边界 |
|---|---|---|
| S-1/C-24，全封装 | 正式 Cut19、Cut20 自冷编的秒数与RTS驻留见文件表 | 与SC7的6G运行不混算比例；Cut20包含整行等式 |
| C-9，变量出口 | 固定表Frame/Use、参数表ParamFrame/Default均自冷编0 | 困难值界保留；不是新增值下界 |
| C-24，实例化边界定位 | Default v1为251；前缀Cut1/2/3为0；改变量at-one后0 | 定位声明，不宣称已做内部归约profile |
| C-9/S-1，同义A/B | 直接251；封装加变量0，数据见上表 | 同8G、同会话、单次，不算加速比 |
| T-15 | 每处封装、输运、改形状旁有perf注释 | 代码纪律，无单独因果性能结论 |

#### 6. 偏离、事故、读取范围与冻结

- **确有单路纪律事故。** Cut20 v2 未结束时启动了 premises；运行脚本中断后 Agda 子进程仍继续到日志 Heap exhausted，又与 Cut20 v3 的初测重叠。日志时间戳证据在 `incident-log-timestamps.json`。第一段重叠为08:53:26.821–08:53:44.461 UTC，第二段为08:54:56.958–08:55:13.470 UTC；v2日志最后写入08:55:14.857。它们是日志创建/最后写入所示区间，不冒充精确进程存活观测。没有把这些初测称作单进程基准；正式冷编及A/B在其后由顺序runner逐个等待，未再出现本路重叠。v2的runner返回130，Agda退出码没被runner读回；`cut20-v2-interruption.json` 将该轮从有效测量中排除。其源留在 `YiE4Cut20-v2-source.txt`。
- 另有早期 opaque 布局42、Cut20类型不匹配42、参数 betaᴱ 的 n 未显式标 ℕ 引起的 unresolved metas42，均修正后重新编译。它们未当作通过，也未作为数学否定。汇总声明脚本另有一次 Python SyntaxError，修正后完成，未改数学源码或编译状态。每次有效测量都读 subprocess 原始返回码，不经管道；`diff` 的退出1仅表示两侧源有差异。
- 后续编译顺序由 `final_check.py` 串行管理，一次一个 Agda，全部-M8G。没有 --ignore-interfaces、--interaction、HTML或切片；没有加堆、装包、pkill、提交、推送或再派子路。只在本私有目录和新YiE4前缀源码写入；编译器生成相应自身接口。旧src/archive、其它前缀、README/LOG、台账、手册与既有留档没有被本路改写。
- 完整读原简报、补充guardrails与AGENTS。直接读工程手册4.1–4.6全部（含YiE3/SC7记录）及SC7完整源码。直接读Bedrock C-9、C-10、C-24、S-1、S-12、S-13、H-5、H-6、Q-1、Q-7、Q-23、Q-25、T-15；未把标题检索冒充正文阅读，未复制该手册入仓库。Q-23的洞测法未执行，本轮使用作者允许的困难模块参数。
- 直接读取所用 YiE3Cut19/Cut20/Base/Objects/Frame 源与YiE3回报相关段；读取 YiGIInst、YiFRStep、YiLBActual、YiLBStart 的所用定义，检索读 YiTBRow、YiMTTab、YiRWBlock/Ops/Path/Fold、YiRWCheck、YiKSDesc 的对应签名/实现。YiCWActual只作为“孩子表分量”的本地对照读取，没有导入YiCW，也没有重启CW/XV/UD。没有重新调研文献或外部代码。原简报中的序数强度背景未独立重验，本轮结论不用那些数值作前提。
- 静态审计 `audit.json` 逐文件列出禁用构造、洞、Funext、本机路径检查，均为空；没有公设、停机/正性指示、K、函数外延或无关投影选项。所有正式文件都有safe/without-K/lossy-unification，仓库库选项继承；私有实验显式补齐infective选项。
- 冻结表列最终正式源码、私有实验源码与失败源、日志、测量、简报、报告与脚本的SHA256。接口、PID文件和冻结表自身不纳入递归哈希；它们不是源码交付依据。`read-sources-final-hashes.json` 是结束时的读取来源哈希，不伪称会话开始前的全仓库快照。后续主审应以冻结源码独立复核。

早期版本留存说明：第一次Cut19布局42、第一次Cut20的42与第一次参数betaᴱ未标ℕ的42，其源码当时原位改正，没有逐轮即时快照；现在按确定的一处修改分别重建到 `reconstructed-early-failures/`，明确标为重建，不伪称当时冻结。其原始Agda日志和测量JSON均保留。Cut20 v2和Default v1的失败源码是在改写前直接留存，不属于这三份重建。

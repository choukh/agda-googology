# YiAT 新表接线与源关系：首个逐项值界未证：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiATStart、YiATWire；私有YiATSource另附，不计仓库模块 |
| 文件前缀 | `YiAT` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: 第六十批YiAT/YiAZ部分回报复核” 一节 |
| 主审复核后的一句结论 | 2件正式源主审8G冷编0；新表实际q1/整行接线及T0/T1展开已核；非零层源关系不是值界，prior未用于增长；T0逐项支配未证，无目标否定。 |

主审补注：两件正式源8G独立冷编0，另将私有YiATSource逐字复制到新的主审目录冷编0；源码、实际表/底/链与条件量化已另行审查。固定新q1的Missing与原实际值界互推；Missing本身没有实填。源关系仅在非零层成立，两次ψ-⊵只取Ω地板，尚未使用prior的额外信息，也没有T[0]零层值界。候选M=1的单支值界未证，不否定其他M。

本次是数学未完成的部分回报，无251、超时或两次实质重设计失败；未触发工程强制停止条件，不把路线关闭。两个正式源104非空代码行；执行方26项冻结哈希及公共依赖均核同。[源关系探针](attachments/Experiment-YiATSource.agda.txt)、[原冻结](attachments/YiAT-Producer-SHA256SUMS-Codex.txt)、[执行方冷编](attachments/YiAT-cold-measurements-Codex.json)、[主审四件正式源及两件私有源接受表](attachments/Yi60-Root-Accepted-Codex.json)。

## 简报原文

### 任务简报：第 3 站那一条值不等式：在按龙骨比较表的新闭项上（数学，构造）（前缀 YiAT）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第六十批两路之一（选项原文 "两张表各派一路 (Recommended)"；主线 "暂不替换，两条并列 (Recommended)"）。两路用同一个框架、同一种办法，攻同一条不等式在两张比较表下的版本：本路在按龙骨比较表的新闭项上（`YiCWTable.rbΛ`）。两路在数学上互不依赖，可以对照。
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
- **第 3 站的工程层已完成**（YiE4，主审复核过，回报 `probes/Survey/Reports-2026-11-12/YiE4.md`）：`YiE4Base`、`YiE4Objects`（第 3 站一切作函数用的折叠在出生处封进 `opaque` 并导出定义等式）、`YiE4Inner`/`YiE4ParamInner`（内层链与整行的部分和极限等式，`YiE4Cut20.first-row`）、`YiE4Frame.at-one`、`YiE4ParamFrame.Missing`（对表 `r : Rb Λ` 参数化的那一条值不等式：`Missing = (e : SI.E.HC A.target) → A.reference e ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β))`）、`YiE4Instances`（最小比较表与空表的实例）、`YiE4Default`（`OriginalAtOne = Bound LS.target (FR.Step.out 2 (FR.Step.chain 2 1))`，`from-original`/`to-original` 与封装的 `Missing` 互推，`first-at-one` 以它为参数给出 `FirstMissing`）。**在这个框架里做**，不要重写具体对象；同义对照：直接写 8G 耗尽，封装加变量化 16 秒约 1.5G（手册 `probes/Survey/EBOHandbook.md` 4.6 节末）。
- **目标项与它的基本列**：`LS.target`（`YiLBStart`）即 ψ₀(Ω_{Ω_A})，A = ψ₀(Ω_Ω)；标准形与 G 集成员已实填。纸面审计（YiPA，回报 `YiPA.md` 第 3.3、5 节，判断档）：记 ρ₀ = 1，ρₙ₊₁ = ψ₀(Ω_{ρₙ})，则 A[n] = ρₙ₊₁，目标的基本列 T[n] = ψ₀(Ω_{Ω_{ρₙ₊₁}})；建议的骨架：把输出写成内层序列的累计极限 P_M = G(0) + G(s 0) + … + G(sᴹ 0)，对每个 n 找 M(n) 使 T[n] 不高于 P_M(n) 的读回，再经累计极限出口得到不等式；不要假设同一下标 n 对应同一内链点。
- **可用的关系与值工具**：`YiLBInv`（文献式不变量 `Inv`、`inv0`、`step→first`）、`YiLBActual.child-gamma`/`g-gamma`（孩子在非零层上的关系，对一切链点）、`YiS2Chain.actual-chain`（第 2 站的链在塔第 1 项那一层上的关系）、`YiS2Low.station→certificate` 与 `YiKCSem.sem→M⁰`（值不等式与关系推导互推）、`YiMSValue`/`YiMSValueRef`（沿分支的值界，只作局部工具）、`YiNDAccept`（新终点上经 F2 对照关系的做法）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（另见上面的共同陈述）
- **本路的表**：`YiCWTable.rbΛ`（按龙骨的比较表），新闭项 `twᵗ`、`EBOᵗ`；`YiCWActual.hit₁`（第 3 站那一格给出路径）、`base-form`（第 3 站孩子拿到的底由继承来的 `prior` 折出，不再重置为标准底）、`YiCWStations.k0`/`k1`/`k2`/`floor`；`YiNDAccept.tω≼EBOᵗ`（新终点不倒退）。
- 判断：新表下孩子的底带着继承来的信息，内层序列的增长可能比旧表下大；这是本路相对旧表那一路的优势，请在回报里说明它在证明里是否真的用上了。

#### 要做的（按序）
0. **最小检查**，在临时目录：在本路的那张表下实例化 `YiE4ParamFrame.Missing`（或对应的 `OriginalAtOne`），确认类型与已有的接线；写出目标基本列的前两项 T[0]、T[1] 在仓库记号里的项，以及内层序列的前两项在框架里的名字。不成立就停下回报。
1. **逐项支配**：照纸面审计的骨架，先对 n = 0、1 证 T[n] 不高于某个内层部分和的读回（M(n) 由你选），用关系族与已有的出口（`station→certificate`、`sem→M⁰` 一类），只对实际对象陈述，不写全域律。
2. **对一切 n**：把第 1 步写成对 n 的归纳（或找到第一个挡住的 n 并交它的展开形式），经累计极限出口得到 `Missing`，再经 `first-at-one` 得到 `FirstMissing`。
3. **往 `Tail 2` 推**：试第 3 站其余的基本列项，从而得到第 3 站的值下界；做不到就交第一个挡住的项。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiAT`（模块名 `OCF.Lean.YiAT…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiAZ`）。验收文件，文首标明。
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

### 第六十批 YiAT 完整回报

#### 1. 判决与进度

没有新增第3站值下界，也没有得到否定。第0步完成；第1步的 n=0 逐项值支配未证，n=1 也未证。由此没有进入全 n 归纳、累计极限的无条件值出口或第3站其余基本列项。树、折叠、合法性与主线均未改变。这次产出属于验收接线与一个非零层源关系，不能计作目标强度的推进，也不能据此关闭新表路线。

**本次没有完成作者原数学目标。** 没有把命题类型、条件接线、源层关系、前三站 floor 或既知终点界报成逐项值支配。没有构造出新的合法定义，所用闭项全是 YiE4 在 YiCWTable.rbΛ 处的原实例。

##### 第0步

最小临时文件 YiATMinimal.agda 已在接手后30分钟内写出并编译，退出0，RTS elapsed 17.098秒，maximum residency 1573895592字节。日志与原源保留。没有失败重跑。

- `module D = YiE4Param.At YiCWTable.rbΛ`。
- `module U = YiE4ParamFrame.For YiCWTable.rbΛ`。
- `module I = YiE4ParamInner.At YiCWTable.rbΛ`。
- Missing-check 确认实例的全 HC 量化以及右侧环境、底、β 全来自 D。
- `first-row` 逐字复用 I.first-row，保留**完整 Tr⁺ 等式**，不是 iter-two，也不是只取树分量。
- 新表的实际接线在 YiATWire 中独立编译。D 的 pre/base/beta/g/feed/out/chain 分别接到 YiCWActual；输出接到新表实际外链 q=1。
- 只从 YiE4Default 借用了与旧表无关的 Bound 与 move-bound 两个通用定义；没有调用它的 output-old、原表 out-eq、FirstMissing 或其他旧链等式。

记 `ρ(x) = E.ψ [] (E.Ωt x) ∷ []`，`ρ₁ = ρ(E.natT 1)`，`ρ₂ = ρ(ρ(E.natT 1))`。编译确认的两项为：

```agda
T₀ : E.fsn LS.target 0 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (E.natT 1)))) ∷ []
T₁ : E.fsn LS.target 1 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (ρ (E.natT 1))))) ∷ []
```

所以 T[0]=ψ₀(Ω_{Ω_{ρ₁}})，T[1]=ψ₀(Ω_{Ω_{ρ₂}})。这里只确认这两个固定项，不把它扩充成所有 n 的公式定理。两个项的 HC 由原目标的 HC 经 hω-inv 实填，定义都在 opaque 内。

内层前两项的框架名字是 `I.Inner.out (I.Inner.chain 0)`、`I.Inner.out (I.Inner.chain 1)`；其中 `chain 0 ≡ B.zero`、`chain 1 ≡ I.Inner.feed B.zero` 均已编译。部分和必须另取 `O.cum (λ k → proj₁ (I.Inner.out (I.Inner.chain k))) M`，不能将前两项误当部分和。

##### 问题表

| 问题 | 位置 | 状态与档 |
|---|---|---|
| 本路表、完整内行与 Missing 的实例 | YiATStart | 编译定理 |
| 接回 YiCWActual 实际外链与输出 | YiATWire.output-new | 编译定理 |
| T[0]/T[1] 展开与非空 HC 域 | YiATStart.T₀/T₁/hc₀/hc₁ | 编译定理，仅两个固定项 |
| T[0] 参数在实际内分支上的非零层关系 | 私有 YiATSource.source-at-one | 编译定理；不是零层值界 |
| T[0] 被某个内层部分和支配 | 本回报 §4 的 n0-partial | 未证；没有否定 |
| T[1] 逐项值支配 | 同上 n=1 版本 | 未证；只有展开与 HC |
| 全 n、Missing 的无条件实填 | U.Missing | 未进行；依原顺序停在 n=0 |
| 新 FirstAt | YiATWire.Use.first-at-one | 条件接线，前提 Missing 未实填 |
| 新 Tail 2 与第3站其余项 | — | 未进行，不冒用旧 FR.Step/Tail |

##### 继承 prior 的信息是否实际用于增长证明

**没有。** 私有源关系证明里实际使用的两个 ψ-⊵ 调用，只提取“Ω 树不高于折叠底、底不高于折叠输出”的关系；它们没有调用 YiCWActual.hit₁ 或 base-form，也没有提取 prior 中超过 Ω 树的值信息。`branch-above` 继而给 `branch-ρ₁`，再经 raiseR 给 `child-ρ₁` 与 `source-at-one`。这些调用确实针对新表的实际对象，但证法只需要 Ω 地板。因而新表继承 prior 的优势尚未在本路的任何困难值界中用上。

#### 2. 文件与编译

只新建两个正式源：

- `probes/OCF/Lean/YiATStart.lagda.md`
- `probes/OCF/Lean/YiATWire.lagda.md`

私有 YiATSource.agda 是源关系的实际构造探针，不是完成逐项支配的交付；它没有洞或假设。

统一计数列依次为：非空非整行注释代码行 / 代码物理行 / 文件物理行。内存是 GHC RTS maximum residency，**不是 OS RSS**。外部墙钟使用 time.monotonic 测量；RTS elapsed 来自各日志；没有声称全机独占。

| 文件 | 三项行数 | 冷编退出码 | 外部墙钟秒 | RTS elapsed秒 | RTS maximum residency字节 |
|---|---:|---:|---:|---:|---:|
| YiATStart | 44 / 45 / 51 | 0 | 16.405 | 16.315 | 1574069768 |
| YiATWire | 60 / 60 / 66 | 0 | 17.436 | 17.345 | 1721793544 |
| YiATSource | 49 / 49 / 49 | 0 | 16.407 | 16.318 | 1471735568 |

冷编逐件只删除自己的接口；依赖接口保持热，单路顺序运行，没有 ignore-interfaces。三个日志的 Checking 行分别只有自身模块；详见 cold-measurements.json。两个正式源共104行（统一计数）。禁项与正式源本机路径检查均为0，详细正则和结果见 counts-and-scan.json。所有 Agda 运行均用 -M8G，一次最多一个本路 Agda。

初编记录：YiATMinimal、YiATWire（临时）、YiATStart（正式）、YiATSource、YiATWire（正式）都退出0。没有42/251/124/154；没有堆墙或重设计失败日志。未实施 profile 或二分，因为没有资源失败需要定位。该事实不能替代 n=0 的数学证明。

#### 3. 定理与前提

以下 `D/U/I` 都是同一张 rbΛ 表的实例。完整逐字陈述及证明见随冻结包保存的源。两个正式源的完整内容附在本文后面，避免省掉隐式量化范围。

| 名字 | 白话 | 档与范围 |
|---|---|---|
| Start.Missing-check | 实例的 Missing 正是所需固定全HC值界类型 | 编译等式；不是 Missing 的元素 |
| Start.output-wire | 封装输出是该表实际 q1 输出 | 编译定理 |
| Start.first-row | 该输出是完整 Tr⁺ 内层累计极限 | 编译定理 |
| Start.T₀、T₁ | 目标基本列头两项展开正确 | 编译定理，固定0/1 |
| Start.hc₀、hc₁ | 前两项各有闭 HC，量化域非空 | 编译闭项 |
| Start.inner0、inner1 | 内层链前两点的框架名字正确 | 编译定理 |
| Wire.pre-eq/base-eq/beta-eq/g-eq/feed-eq/out-eq/chain-eq | 封装对象与 YiCWActual 同表实际对象一致 | 编译定理，变量n/q |
| Wire.output-new | 固定封装输出接回新实际外链q1 | 编译定理 |
| Wire.from-original/to-original | 全HC的实际新q1值界与 Missing 互相转换 | 编译接线；两种值界均未实填 |
| Wire.Use.first-at-one | Missing 若实填，则固定新q1给存在链点结论 | 编译条件接线；不是无条件 FirstAtNew |
| Source.rd-ρ₁ | ρ₁ 是 tw2 的带证据读法 | 编译闭项 |
| Source.leaf-ρ₁ | tw2 的 Ω 树承载 Ω_{ρ₁} 的关系 | 编译定理 |
| Source.branch-above/branch-ρ₁ | 实际 branch 每一项保有该 Ω 地板/关系 | 编译定理，只量化此实际函数的d |
| Source.child-ρ₁ | 实际 a d 的 Ω 树承载 Ω_{Ω_{ρ₁}} | 编译定理 |
| Source.source-ρ₁/source-at-one | 实际内层 g 在指定内链点上承载 T[0] 参数 | 编译定理；没有折到零层后的保持 |

源关系的逐字关键陈述是：

```agda
source-at-one : GR.R I.h (E.Ωt (E.Ωt ρ₁))
  (I.Inner.g (I.Inner.chain 1))
```

它是非零层 GR.R，不是 `K.M⁰`，也不是所求的值不等式。用 source-at-one 直接交给 lower⁰ 是类型不符的；本次没有将这种不符编造为路线否定或障碍定理。

前提实例：

- 对 rbΛ 实例，所有环境等式在 Frame 规范调用点由 YiE4 的导出规格/reflexivity 实填；新实际接线另行证明，没有替换孩子0的表。
- T[0]/T[1] 的 HC 实填为 Start.hc₀/hc₁。
- Source 的 rd-ρ₁ 实填为 `GR.cc (inj₁ (E.hd< (E.lv< E.[]<))) (GR.rd-child (B.sΩ (B.tw 1)) (D.Step.child 1) B.zero LL.rdΩ)`；不是假设。
- Wire.Use 的唯一困难前提 `U.Missing` 未有实例；其可满足性仍是数学目标，不能借条件接线的编译通过声称已满足。此接线是作者第0步要求的对应实例，不是另造一个假定终点的路线。

来源复用：目标 HC 用 YiLBStart、YiExInst.back、YiRefTw2.hω-inv；接线证法来自 YiE4Default；实际源关系骨架来自 YiLBActual 的 slot/chain/child/gamma 构造，但对象逐项换为同一 r 的 YiE4ParamInner 实例；关系与底的工具直接调用 YiTBFam.ψ-⊵、YiHCRel.Gen.m⊴、YiNLTop2.leaf-tw2、YiNLRaise.raiseR，没有复制这些工具证明。

#### 4. 第一个未证引理

设 `T n = E.fsn LS.target n`，

```agda
P M = O.cum (λ k → proj₁ (I.Inner.out (I.Inner.chain k))) M
```

作者要求中首先未证的是：

```agda
n0-partial : Σ ℕ λ M → (e : SI.E.HC (E.fsn LS.target 0))
  → SI.E.tree e ≼ K.readRW (P M)
```

本次构造 source-at-one 后，想取 M=1，先处理更强的指定分支值界：

```agda
n0-branch-one : (e : SI.E.HC (E.fsn LS.target 0))
  → SI.E.tree e ≼ K.readRW
      (proj₁ (I.Inner.out (I.Inner.chain 1)))
```

**n0-branch-one 没有证明，也没有否定。** M=1 是尝试选取的候选，没有定理证明它足够；其未证不说明别的 M 不行。已构造的 source-at-one 只给折叠前的关系。现有 lower⁰ 要求折叠后的 K.M⁰；sem→M⁰ 要求先给出零层值界。station→certificate 的前提也是相应站值界；不能用这些出口循环生产缺失的值界。

审阅过的普遍保持办法会引入整个 ChildU、SlotU 或 LayerIndex/PrefixU；这些量化超出本次实际对象，而且简报明确不许改成全域保持。本路没有声明这些全域律，也没有以它们为未实填前提交一个貌似完成的 n0。

##### 停留位置说明

本次在构造实际源关系后，未找到可提交检查器的 n0 零层值界证明项。这是数学未完成，**不是**8G工程停止条件，不是编译否定，不是两次失败重设计后的资源结论。没有用未知当否定；按原顺序，没有转去证明其他终点界、旧表结论或新定义。作者若继续此路，起点是上述 n0-partial；source-at-one 只是一项已检查的准备。

#### 5. 偏离、事故与阅读范围

- 没有改树、折叠、合法性、旧文件、公共导航/台账、另一前缀、src 或 archive；没有提交、推送、装包、pkill、子派或原样重跑耗尽源。
- 本路只新建 YiATStart/YiATWire 与自身私有目录内容。没有写公共完成状态或替换主线。
- 有一次批量 rg 的通配路径 `YiPA*` 在 zsh 下无匹配，有两次检索包含不存在的候选文件名；它们不是 Agda 运行，没有被用作数学结论。
- 已完整读原简报、batch60护栏、AGENTS、EBOHandbook第4节；Bedrock手册读了C-9/C-10/S-1/S-3/Q-1/Q-23/H-6对应条目。数学源按签名与所需局部读取；不声称逐字审读所有传递依赖。
- 没有直接读 YiPA 全回报或外部文献；关于原表 prior/base 的历史判断只来自简报，本次没有把它当作证明。T[0]/T[1] 的公式另由检查器确认。
- 未重启 YiXV，未导入 YiAZ 活动文件。没有外部模型复核或独立路线否定。
- 没有跑记号无关性切片：本次文件明确是读记号的验收文件，没有提出新的成品定义。

#### 6. 冻结包

本回报、原简报/护栏副本、所有本路源、初编与冷编日志、计数与实测JSON、冷编脚本均留在本私有目录。`SHA256SUMS` 给完整冻结文件清单；`frozen/` 是源快照，便于主审从头复核。本回报在任务线程仅报路径，不写公共留档。

#### 附：YiATStart.lagda.md 完整源

### 新表固定 q1 的最小检查
验收文件；表取 YiCWTable.rbΛ，复用 YiE4 整表参数框架。
编译目标前两项展开、闭 HC 与完整内层整行接线；没有逐项值支配。
来源：YiE4ParamFrame、YiE4ParamInner；HC 复用 YiRefTw2.hω-inv。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiATStart where
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiE4Param as R
import OCF.Lean.YiE4ParamFrame as V
import OCF.Lean.YiE4ParamInner as J
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_)
module D = R.At CW.rbΛ
module U = V.For CW.rbΛ
module I = J.At CW.rbΛ
Missing-check : U.Missing ≡ ((h : SI.E.HC A.target) → A.reference h ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β)))
Missing-check = refl
output-wire : D.output ≡ D.Step.out 2 (D.Step.chain 2 1)
output-wire = U.output-chain
first-row : D.output ≡ O.limc⁺ (λ n → I.Inner.out (I.Inner.chain n))
first-row = I.first-row
ρ : E.T → E.T
ρ x = E.ψ [] (E.Ωt x) ∷ []
T₀ : E.fsn LS.target 0 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (E.natT 1)))) ∷ []
T₀ = refl
T₁ : E.fsn LS.target 1 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (ρ (E.natT 1))))) ∷ []
T₁ = refl
inner0 : I.Inner.chain 0 ≡ B.zero
inner0 = refl
inner1 : I.Inner.chain 1 ≡ I.Inner.feed B.zero
inner1 = refl

import OCF.Lean.YiExInst as XI
import OCF.Lean.YiRefTw2 as RT
opaque
  hc₀ : SI.E.HC (E.fsn LS.target 0)
  hc₀ = SI.conv (RT.hω-inv (XI.back LS.hc-target) refl 0)
  hc₁ : SI.E.HC (E.fsn LS.target 1)
  hc₁ = SI.conv (RT.hω-inv (XI.back LS.hc-target) refl 1)
```

#### 附：YiATWire.lagda.md 完整源

### 新表的实际闭项接线
验收文件；Missing 与新表实际 q1 的全 HC 值界互推；值界未填。
来源：YiE4Default 的变量接线证明，改为 YiCWActual；仅复用其 Bound/move-bound 通用输运。
FirstAtNew 的链与输出均为 YiCWActual，不接旧 FR.Step。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiATWire where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Lean.YiCWTable as CW
import OCF.Lean.YiCWActual as C
import OCF.Lean.YiE4Param as R
import OCF.Lean.YiE4ParamFrame as V
import OCF.Lean.YiE4Objects as A
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Frame as W
import OCF.Lean.YiE4Default as DF
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiLBStart as LS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiKVRel as K
open import OCF.Align.Value using (_≼_)
module D = R.At CW.rbΛ
module U = V.For CW.rbΛ
opaque
  unfolding D.FΛ D.pre D.baseᴱ D.betaᴱ D.Step.g D.Step.feed D.Step.out
  pre-eq : ∀ n → D.pre n ≡ C.pre n
  pre-eq zero = refl
  pre-eq (suc n) = refl
  base-eq : ∀ n → D.baseᴱ n ≡ C.baseᴱ n
  base-eq n = cong (λ x → λ i u → TB.ψ B.Λ P.Ok-Λ CW.rbΛ (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) x) (pre-eq n)
  beta-eq : ∀ n → D.betaᴱ n ≡ C.betaᴱ n
  beta-eq n = cong (λ x → TB.ψ B.Λ P.Ok-Λ CW.rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) x) (pre-eq n)
  g-eq : ∀ n → D.Step.g n ≡ C.Step.g n
  g-eq n = refl
  feed-eq : ∀ n → D.Step.feed n ≡ C.Step.feed n
  feed-eq n = refl
  out-eq : ∀ n → D.Step.out n ≡ C.Step.out n
  out-eq n = refl
chain-eq : ∀ n q → D.Step.chain n q ≡ C.Step.chain n q
chain-eq n q = cong (λ f → O.iter f B.zero q) (feed-eq n)
opaque
  output-new : D.output ≡ C.Step.out 2 (C.Step.chain 2 1)
  output-new = trans U.output-chain (trans (cong (λ f → f (D.Step.chain 2 1)) (out-eq 2))
    (cong (C.Step.out 2) (chain-eq 2 1)))
OriginalAtOne : Set
OriginalAtOne = DF.Bound LS.target (C.Step.out 2 (C.Step.chain 2 1))
from-original : OriginalAtOne → U.Missing
from-original low h = subst (λ x → x ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β)))
  (sym (A.reference-eq h))
  (DF.move-bound (sym A.target-eq) (trans (sym output-new) D.output-eq) low h)
to-original : U.Missing → OriginalAtOne
to-original low = DF.move-bound A.target-eq (trans (sym D.output-eq) output-new)
  (λ h → subst (λ x → x ≼ K.readRW (proj₁ (Q.collapse D.ctx D.β))) (A.reference-eq h) (low h))
FirstAtNew : Set
FirstAtNew = Data.Product.Σ ℕ λ q → (h : SI.E.HC LS.target) → SI.E.tree h ≼ K.readRW (proj₁ (C.Step.out 2 (C.Step.chain 2 q)))
module Use (low : U.Missing) where
  module I = U.Use low
  first-at-one : FirstAtNew
  first-at-one = W.at-one LS.target (λ q → C.Step.out 2 (C.Step.chain 2 q)) D.output output-new I.target-low
```

#### 附：YiATSource.agda 完整源

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module YiATSource where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
import OCF.Lean.YiATStart as S
open S using (module D; module I; ρ)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiNLTop2 as N
import OCF.Lean.YiNLRaise as NR
import OCF.Lean.YiNLCtx as NC
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiCWTable as CW
open import OCF.Lean.YiKCStep using (⊴-trans)
ρ₁ = ρ (E.natT 1)
rd-ρ₁ : GR.Rd (B.tw 2) ρ₁
rd-ρ₁ = GR.cc (inj₁ (E.hd< (E.lv< E.[]<)))
  (GR.rd-child (B.sΩ (B.tw 1)) (D.Step.child 1) B.zero LL.rdΩ)
leaf-ρ₁ : GR.R (B.tw 2) (E.Ωt ρ₁) (proj₁ (O.Ωt (B.tw 2)))
leaf-ρ₁ = N.leaf-tw2 rd-ρ₁
opaque
  unfolding D.baseᴱ D.restricted I.base₀ I.branch
  branch-above : ∀ d → proj₁ (O.Ωt (B.tw 2)) K.⊴ I.branch d
  branch-above d = ⊴-trans
    (TF.ψ-⊵ B.Λ P.Ok-Λ CW.rbΛ (F.B₀ B.Λ) (B.tw 2) (P.inc 3 (P.inc B.zero P.self)) (O.Ωt (B.tw 2)) (D.pre 3))
    (TF.ψ-⊵ (B.tw 2) (P.Ok-tw 2) (D.Step.child-table 2 B.zero) (D.restricted B.zero) (B.tw 2) P.self
      (D.baseᴱ 3 (B.tw 2) (P.ink P.self)) (D.Step.g 1 d))
branch-ρ₁ : ∀ d → GR.R (B.tw 2) (E.Ωt ρ₁) (I.branch d)
branch-ρ₁ d = H.Gen.m⊴ leaf-ρ₁ (branch-above d)
child-ρ₁ : ∀ d → GR.R (I.a d) (E.Ωt (E.Ωt ρ₁)) (proj₁ (O.Ωt (I.a d)))
child-ρ₁ d = NR.raiseR (B.tw 2) (NC.prefix (B.tw 2)) [] (GR.c0 refl)
  (N.leaf-tw2 (GR.c0 refl)) (branch-ρ₁ d)
opaque
  unfolding I.Inner.g
  source-ρ₁ : ∀ d → GR.R I.h (E.Ωt (E.Ωt ρ₁)) (I.Inner.g d)
  source-ρ₁ d = H.mU H.mz (child-ρ₁ d)
source-at-one : GR.R I.h (E.Ωt (E.Ωt ρ₁)) (I.Inner.g (I.Inner.chain 1))
source-at-one = source-ρ₁ (I.Inner.chain 1)
```

# YiAZ 基本列全n公式与必要子列：原值界未证：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiAZStart、YiAZLocal；私有YiAZQuant量词诊断另附，不计仓库模块 |
| 文件前缀 | `YiAZ` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: 第六十批YiAT/YiAZ部分回报复核” 一节 |
| 主审复核后的一句结论 | 2件正式源主审8G冷编0；全n基本列公式、全HC的S0/S1到实际P0值界已核，S2及T0/T1未证；无目标或后支否定。 |

主审补注：两件正式源8G独立冷编0，另将私有YiAZQuant逐字复制到新的主审目录冷编0；源码/实际原表实例及量词范围已独立审查。全n基本列公式、全HC的必要子列S(0)/S(1)到实际P₀的值界成立；S(2)=ψ₀(Ω_{Ω₂})及T[0]/T[1]仍未证。表中“Missing实例”指Missing类型的原表实例，不是困难值界已有居民。没有FirstMissing、目标否定或后支否定。

量词探针否定的左端是实际完整累计极限自身，不是作者目标T[n]。它说明一般的有限部分和失败不能直接当作完整极限不支配；没有证明本目标的有限见证不存在。本次未触发工程强制停止条件，两个42为已修复的作用域/等式形状错误，无251；只交数学未完成的部分回报，不关闭路线。两源128非空代码行，43项原冻结核同。原回报扫描规则里的路径前缀也机械换成占位，私有原报告保持原SHA。

[量词探针](attachments/Experiment-YiAZQuant.agda.txt)、[原冻结](attachments/YiAZ-Producer-SHA256SUMS-Codex.txt)、[执行方编译表](attachments/YiAZ-measurements-Codex.json)、[主审四件正式源及两件私有源接受表](attachments/Yi60-Root-Accepted-Codex.json)。

## 简报原文

### 任务简报：第 3 站那一条值不等式：在现在的主线上（数学，构造与丢值的配对）（前缀 YiAZ）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第六十批两路之一（选项原文 "两张表各派一路 (Recommended)"；主线 "暂不替换，两条并列 (Recommended)"）。两路用同一个框架、同一种办法，攻同一条不等式在两张比较表下的版本：本路在现在的主线上（最小比较表 `MT.rbᶻ Λ`）。两路在数学上互不依赖，可以对照。
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
- **本路的表**：现在的主线（最小比较表 `MT.rbᶻ`），闭项 `twᶻ`、`EBOᶻ`；`YiUPBase.base-form`（第 3 站孩子拿到的底只是 Ω 树加三段固定的可数尾项，不随实际回灌链增长，因为比较表在那一格返回 "无法比较"、退路行重置了底）；`YiFRStations.k0`/`k1`/`k2`。
- **本路兼做配对否定**：若在证明中发现重置后的底让某个 T[n] 无法被任何内层部分和支配，把它写成编译的否定（对本路的实际对象），并检查错位配对（目标能否被后面某一支支配）；若都被否定，这是 "旧表在第 3 站丢值" 的编译证据，按 AGENTS 交作者定（不改定义）。

#### 要做的（按序）
0. **最小检查**，在临时目录：在本路的那张表下实例化 `YiE4ParamFrame.Missing`（或对应的 `OriginalAtOne`），确认类型与已有的接线；写出目标基本列的前两项 T[0]、T[1] 在仓库记号里的项，以及内层序列的前两项在框架里的名字。不成立就停下回报。
1. **逐项支配**：照纸面审计的骨架，先对 n = 0、1 证 T[n] 不高于某个内层部分和的读回（M(n) 由你选），用关系族与已有的出口（`station→certificate`、`sem→M⁰` 一类），只对实际对象陈述，不写全域律。
2. **对一切 n**：把第 1 步写成对 n 的归纳（或找到第一个挡住的 n 并交它的展开形式），经累计极限出口得到 `Missing`，再经 `first-at-one` 得到 `FirstMissing`。
3. **往 `Tail 2` 推**：试第 3 站其余的基本列项，从而得到第 3 站的值下界；做不到就交第一个挡住的项。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiAZ`（模块名 `OCF.Lean.YiAZ…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiAT`）。验收文件，文首标明。
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

### 第六十批 YiAZ 回报（旧表独立路）

#### 1. 判决与执行范围

**未走通原简报第1步。没有新增第3站、FirstMissing或终点的值下界，也没有得到旧表丢值的编译否定。** 两件正式模块只做记号侧验收；树、折叠、比较表、合法性和具体YiE4对象均未改。基本列公式与局部子列值界是编译定理，不读作树自足的进展，也不读作本批要求的T[0]/T[1]逐项支配。

完整读取原简报、batch60-guardrails、仓库AGENTS.md及EBOHandbook第4节；另读Bedrock性能手册C-9、C-10、S-1、S-3。使用整张旧表`MT.rbᶻ B.Λ`的`YiE4Param`、`YiE4ParamInner`、`YiE4ParamFrame`实例。所有孩子表、底、β、内链均取同一实例的分量，未以独立table2替换table3的孩子0。

| 原任务 | 实际结果 | 档 |
|---|---|---|
| 第0步：Missing实例、旧表双向接线、T[0]/T[1]及内层前两项 | `YiAZMin.agda`退出0；正式`YiAZStart`冷编0 | 编译定理/最小检查 |
| 第1步：T[0]对某个实际P_M的全HC支配 | 未证，尚未给出M(0) | 未完成；不作否定 |
| 第1步：T[1]逐项支配 | 未证；未越过T[0]而另外宣称该步成立 | 未完成 |
| 子问题：S(m)=T[0][0][m] | 全m项公式及HC实例已证；S(0)、S(1)对实际P_0的全HC支配已证 | 编译定理；不是原第1步 |
| 第2步：全n归纳、Missing、FirstMissing | 未证 | 未完成 |
| 第3步：其余第3站项、Tail 2、Kᴱ 3 | 未推进 | 未完成 |
| 配对否定：某个实际T[n]对所有M不支配 | 未证 | 未完成 |
| 后支错位：固定q1、所有q、终点 | 未得到任何目标值的后支否定；没有用固定q1失败关闭FirstMissing或终点 | 未完成 |
| 有限部分和到累计极限的量词审计 | 对本路实际P_M与D.output编译了下述全M否定，但其左端是D.output自身，不是T[n] | 编译定理，仅限所写命题 |

##### 固定的记号与对象

`ρ 0 = E.natT 1`，`ρ (suc n) = E.ψ [] (E.Ωt (ρ n)) ∷ []`。

已编译：

```agda
γ-ρ : ∀ n → E.γT (E.ΩTower 2) [] n ≡ ρ n
A-fsn : ∀ n → E.fsn (E.EBOψ 2) n ≡ ρ (suc n)
T-form : ∀ n → T n ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (suc n)))) ∷ []
```

其中`T n = E.fsn LS.target n`。故前两项逐字为：

```agda
T0 : T 0 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ 1))) ∷ []
T1 : T 1 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ 2))) ∷ []
```

白话是T[0]=ψ₀(Ω_{Ω_{ρ₁}})、T[1]=ψ₀(Ω_{Ω_{ρ₂}})。这次没有把纸面ρ递推当作现成定理，已对全n编译了它与实际fsn的等式。

实际内链及部分和未重写：

```agda
module D = R.At (MT.rbᶻ B.Λ)
module U = V.For (MT.rbᶻ B.Λ)
module N = I.At (MT.rbᶻ B.Λ)
G n = N.Inner.out (N.Inner.chain n)
P = O.cum (λ n → proj₁ (G n))
```

前两项为`G 0`、`G 1`；`N.Inner.chain 0 ≡ B.zero`、`N.Inner.chain 1 ≡ N.Inner.feed B.zero`；`P 0 ≡ proj₁ (G 0)`、`P 1 ≡ proj₁ (G 0) O.+ proj₁ (G 1)`。`whole-row : D.output ≡ O.limc⁺ G`直接用`N.first-row`，是完整Tr⁺等式，没有以树投影或iter-two代替。

#### 2. 文件、冷编与资源

正式源文件均只新建于`probes/OCF/Lean/YiAZ*`。计数口径：代码块中非空且非整行`--`注释的行，包含模块头、选项及导入；另列代码物理行和文件物理行。

| 文件 | 非空非整行注释代码 | 代码物理行 | 文件物理行 | 自身接口冷编退出码 | 外部墙钟秒 | RTS elapsed秒 | RTS maximum residency字节 |
|---|---:|---:|---:|---:|---:|---:|---:|
| YiAZStart.lagda.md | 71 | 72 | 78 | 0 | 16.392 | 16.276 | 1778421128 |
| YiAZLocal.lagda.md | 57 | 58 | 64 | 0 | 16.468 | 16.363 | 1698420808 |

每次Agda均`+RTS -M8G -s -RTS`，本路同时只有一个Agda。没有观测全机独占，不称上述数为OS RSS。依赖接口保持热；未使用`--ignore-interfaces`。两次正式冷编日志均只有自身的Checking行及RTS统计，无错误、洞或警告。

`min01`退出0，17.278秒，RTS elapsed 17.179秒，maximum residency 1515245152字节；首文件在创建本路私有目录后数分钟内完成，满足30分钟要求。完整运行表在`measurements.json`，原日志及每轮源快照均保留。

禁项及本机路径检查：两件正式源均为0。检查包括postulate、洞标记、终止/正性绕过、trustMe、allow-unsolved-metas、irrelevant-projections、`--cubical`（区别于允许的cubical-compatible）、`<user-directory-prefix>`、`<private-directory-prefix>`、`<temporary-directory-prefix>`、`<library-directory-prefix>`。

#### 3. 定理与规范前提

所有下表“编译定理”均为本路源经检查器通过的陈述；不是主审已独立复核的宣告。完整逐字源及全部公开签名列于冻结源与文末附件。

| 名字 | 一句白话 | 文件/档 |
|---|---|---|
| `from-original`、`to-original` | 旧表`OriginalAtOne`与本实例`Missing`双向转换，复用YiE4Default | Start，编译定理 |
| `γ-ρ`、`A-fsn`、`T-form` | ρ递推与实际γT/fsn对全部n一致 | Start，编译定理 |
| `nf-T`、`hc-T`、`hc-T-form` | 全部目标基本列项有标准形及闭HC证书，纸面式也有输运后的HC | Start，编译定理 |
| `inner0`、`inner1`、`P0`、`P1`、`whole-row` | 前两链点、部分和与完整累计极限接线 | Start，编译定理 |
| `β-prior` | 本实例实际β的树分量是原终点第2支 | Local，编译定理 |
| `out-base` | 对本实例的每个实际内层输入d，输出值不低于原β | Local，编译定理 |
| `S-form`、`S0`、`S1`、`S2` | 必要子列S(m)=ψ₀(Ω_{Ω_m})；0、1项接已证站，2项为ψ₀(Ω_{Ω₂}) | Local，编译定理 |
| `S0-low`、`S1-low` | 这两个子列项对实际P₀的全HC值界 | Local，编译定理 |
| `hc-S` | 必要子列每个m均有闭HC证书，特别是未证子项m=2的前提非空 | Local，编译定理 |
| `S-below-T0` | 每个S(m)的任意HC值不高于T[0]的任意HC值；因此S(2)是T[0]的必要子问题 | Local，编译定理 |

“前提可满足”的精确范围：`C.Original.environment`给规范环境等式，`C.Original.hc`给封装目标HC；`hc-T n`、`hc-S m`给全部相应HC域的实例；底、β、表与chain均为YiE4现成闭项。没有将困难的Missing作为已经实填、已经可满足或已经矛盾的前提。以上结果不含Funext或其它额外假设。

##### 私有量词审计（不是目标否定）

`YiAZQuant.agda`退出0，外部墙钟16.557秒，RTS elapsed 16.437秒，maximum residency 1717503512字节。来源：严格第一位置界复用YiKDStep.◃s≼，读回桥复用YiKQSuff.read≤/YiKCSem.rr≼，反自后继复用YiNFO.s≼-irrefl。

逐字命题：

```agda
finite-strict : ∀ m → L.suc (K.readRW (P m)) ≼ K.readRW (proj₁ D.output)
no-finite-upper : ∀ m → K.readRW (proj₁ D.output) ≼ K.readRW (P m) → ⊥
whole-self : K.readRW (proj₁ D.output) ≼ K.readRW (proj₁ D.output)
```

它展示同一实际累计极限不被任何有限部分和支配，同时被自身支配。**被否定的左端是本路实际累计极限自身，绝非作者要求的T[n]。** 因而这不是“旧表在固定q1不达目标”的证据，不计作本路所要求的目标配对否定。

量词审计的结论：即便以后证出某个T[n]对所有有限M均不支配，也不能仅凭此否定它对完整累计极限的支配。固定q1的完整目标否定也不能否定`Σ q → At q`；所有q的有限见证失败还不能自动改写成终点完整极限的值否定。本路没有编译这些目标否定中的任何一条。

#### 4. 第一个障碍与后支范围

原第1步仍未实填的第一个完整命题是：

```agda
Σ ℕ λ M → (h : SI.E.HC (T 0)) → SI.E.tree h ≼ K.readRW (P M)
```

在复用现有站值界、先证明必要子列的尝试中，已经实填m=0、1及M=0；下一个未证的具体引理是：

```agda
Σ ℕ λ M → (h : SI.E.HC (S 2)) → SI.E.tree h ≼ K.readRW (P M)
-- S 2 ≡ E.ψ [] (E.Ωt (E.Ωt (E.natT 2))) ∷ []
```

`S-below-T0 2`已编译，故它确是T[0]的必要子值，未把另一个较低目标当成原任务。`hc-S 2`已实填，不能以HC域空解释未证。这里没有M(0)，没有声称M=0不可能，也没有声称任意M不可能。

核对现成工具后的界限（判断）：`YiLBActual.child-gamma/g-gamma`给的是非零层R；`sem→M⁰`的调用本身先要零层值不等式；`station→certificate`把已有站值反射成证书。它们均没有直接填上这条实际零层支配。本路没有为此新写全对象保持律，也没有把已知退化全域反例外推到当前实际对象。

后支错位检查的实际范围：旧表D.output已用YiE4Default接回原`FR.Step.out 2 (FR.Step.chain 2 1)`；未发现目标项的独立记号上界，也没有得到q=0、q=2或所有后支对目标的否定。YiFNUpper的相对站上界和YiMSValueRef的q=2已知下界均不足以判定这条S(2)或完整目标。后两项背景仅按原简报及其源签名核对，未作为本路新值证明的前提。**后支目标比较仍未完成，不能据此宣告终点丢值。**

#### 5. 偏离、事故与停止依据

- 未重写对象，未更换表，未改旧文件、src、archive、另一活动前缀或公共导航台账；未提交、推送、装包、pkill或另派子路。
- 本路把T[0]展开到其必要子列并交了两个局部值定理。它们仍服务同一T[0]义务，但原第1步没有完成；没有据此跳到全n、Missing或Tail 2。
- `local01`退出42：[NotInScope]，临时源把未显式导入的YiLBStart.hc-target写成全限定名字。改用已经导出的`hc-T 0`后，`local02`退出0。未将此作用域错误当作数学反例。
- `local03`退出42：[UnequalTerms]，全m子列式的`refl`遇到`replicate m 𝟏`与递归`natT m`的非字面相同。检索并复用YiCLPhi.rep1，经cong输运，`local04`退出0。没有重证rep1。
- 所有Agda运行均无251、124或154。没有发生堆墙，未加堆；两个42是已修复的作用域/等式形状问题，不是原值界的两次实质重设计失败。未运行原YiCK耗尽源。
- 一次宽glob检索因不存在YiPA源模式而返回1，随后改用已有文件；一次`ps`只读进程查看被环境拒绝，未绕过或据此声称全机独占。
- 本轮没有触发简报的工程强制停止条件。主数学义务未能实填，现交回第一个精确未证引理，不另换问题、不改定义，也不把“未走通”写成路线已否定。
- 用到的YiE4接口、被调用的小引理及k1/k2均已读源码或其精确声明/证明段；没有重编依赖的整个闭包。YiE4Cut19/Cut20等下层工程的复核状态取原简报，没有重新独立审计整套工程证明。没有调用并行YiAT的活动源；YiCW/YiND未导入。
- YiPA的审计及相关段落已读，但仅用来确定待验证公式与原骨架；本路公式已经另编译确认。原简报给出的既有强度、历史否定及“已复核”状态没有冒充本路从头复核的结果。

冻结目录含原简报、补充约束、所有轮次源/日志/命令/遥测、正式最终源、本回报及SHA256清单。没有把任何失败轮切片或HTML作为有效成果。

#### 附：正式源公开签名（逐字摘录）
冻结源保留完整定义和证明体；以下只摘声明，不把其中的Set命题当作其值界已证。

##### YiAZLocal.lagda.md

```agda
  β-prior : proj₁ D.β ≡ Keel⁻.twc GI.keelᴱ 2
out-base : ∀ d → K.readRW (proj₁ D.β) ≼ K.readRW (proj₁ (N.Inner.out d))
S : ℕ → E.T
S-form : ∀ m → S m ≡ E.ψ [] (E.Ωt (E.Ωt (E.natT m))) ∷ []
S0 : S 0 ≡ Keel⁻.row GI.keelᴱ 1
S1 : S 1 ≡ Keel⁻.row GI.keelᴱ 2
S2 : S 2 ≡ E.ψ [] (E.Ωt (E.Ωt (E.natT 2))) ∷ []
S0-low : (h : SI.E.HC (S 0)) → SI.E.tree h ≼ K.readRW (P 0)
S1-low : (h : SI.E.HC (S 1)) → SI.E.tree h ≼ K.readRW (P 0)
  hc-S : ∀ m → SI.E.HC (S m)
S-below-T0 : ∀ m (h : SI.E.HC (S m)) (h₀ : SI.E.HC (T 0)) → SI.E.tree h ≼ SI.E.tree h₀
```

##### YiAZStart.lagda.md

```agda
Missing : Set
from-original : Df.OriginalAtOne → Missing
to-original : Missing → Df.OriginalAtOne
canonical-hc : SI.E.HC A.target
ρ : ℕ → E.T
γ-ρ : ∀ n → E.γT (E.ΩTower 2) [] n ≡ ρ n
A-fsn : ∀ n → E.fsn (E.EBOψ 2) n ≡ ρ (suc n)
T : ℕ → E.T
T-form : ∀ n → T n ≡ E.ψ [] (E.Ωt (E.Ωt (ρ (suc n)))) ∷ []
T0 : T 0 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ 1))) ∷ []
T1 : T 1 ≡ E.ψ [] (E.Ωt (E.Ωt (ρ 2))) ∷ []
nf-T : ∀ n → EB.NF (T n)
  hc-T : ∀ n → SI.E.HC (T n)
  hc-T-form : ∀ n → SI.E.HC (E.ψ [] (E.Ωt (E.Ωt (ρ (suc n)))) ∷ [])
inner0 : N.Inner.chain 0 ≡ B.zero
inner1 : N.Inner.chain 1 ≡ N.Inner.feed B.zero
G : ℕ → O.Tr⁺ B.zero
P : ℕ → B.Tr B.zero
P0 : P 0 ≡ proj₁ (G 0)
P1 : P 1 ≡ (proj₁ (G 0) O.+ proj₁ (G 1))
whole-row : D.output ≡ O.limc⁺ G
```

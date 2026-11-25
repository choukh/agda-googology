# YiUP 实际限制底、旧上界桥反例与未证独立上界：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiUPBase；七件临时源码以附件留档，不重复计模块 |
| 文件前缀 | `YiUP` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiUP 续做实际接线、窄桥否定与最终回报复核” 一节 |
| 主审复核后的一句结论 | 首稿两件、续稿六件主审5G逐件冷编0；新增Base等式18行，临时桥反例范围已核；q0/q1独立上界和FirstMissing未判定，不改定义、不关闭原路线。 |

## 简报原文

### 任务简报：上界判定：第 3 站实际链点的输出能不能达到目标（数学，否定方向）（前缀 YiUP）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十五批四路之一（选项原文 "上界判定：实际链点输出能不能达到目标 (Recommended)"）。四路都冲着第 3 站的那一条不等式：一路判定上界、一路构造、一路摆脱侧、一路纸面审计，在数学上互不依赖。
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
- 本路先于构造方向的意义：新旧两条主线都卡在第 3 站同一处，配对否定一路（YiFN）未判定，原因是缺独立的记号上界。若实际链点的输出全都低于目标项，构造方向就是在一个假命题上用力。
- AGENTS："否定路线要有依据"（要编译过的否定定理）；"第 4 层不反过来改前 3 层"（若发现非改定义不可，停下交作者）；"构造与否定配对"。
- 上界工具（先检索，能复用就复用）：`YiCeilRead`（第 0 层读回的上界、部分和吸收 `plus≼`、`next≼`、`limc≼`，第 0 层折叠不高于参照的幂 `fold₀≼`，`ε₀-upper`、`chain≼`）、`YiCeilWit`、`YiCeilSmall`、`YiUB*`；在跑的 YiXV（主线之外的精确值一路）已编译了大量上界框架，例如 `YiXVReadCapBound`、`YiXVReadCapValue`、`YiXVCountableFoldBound`、`YiXVFiniteUp`、`YiXVSourceWorldUp`、`YiXVSourcePrefixes.allpre`。**YiXV 仍在执行，它的文件可能还会变**：只读；若要导入，记下导入时那几个文件的 SHA256，回报里列出，不改它们。

#### 要做的（按序）
0. **纸面估值与最小检查**，在临时目录：先在回报里写出你对 `Step.out 2 (Step.chain 2 q)`（q = 0、1、2）的值的纸面估计（判断档），再为 q = 0、1 编译独立的记号上界（形如 `readRW (proj₁ (Step.out 2 (Step.chain 2 q))) ≼ 某个参照树`）。
1. **对一切 q 的统一上界**：编译一个参照 U 与 `∀ q → readRW (out (chain q)) ≼ U`，并比较 U 与目标项。
   - 若 U 低于目标项：编译 `¬FirstMissing`；再检查错位配对（第 3 站的参照能否被后面某一支 `twc m` 支配）：先陈述，再证或否定。若错位也被否定，是定义层面的问题：写成编译定理后停下，交作者，不改定义。
   - 若 U 不低于目标项：交 U 与它到目标项的比较，说明上界方法到这里判定不了。
2. 回报里把纸面估计与编译结论分开写，纸面部分标 "判断"。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiUP`（模块名 `OCF.Lean.YiUP…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiCK`、`YiTC`、`YiPA`）。验收文件，文首标明。
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

### 主审复核与两次完整回报

两次原回报按顺序保留，首稿是检查点；续做回报结束本次研究交付，原独立上界任务未达成、未否定。主审全文查源码及陈述，首稿两件与续做六件均删除各自接口后5G冷编退出0；续做95.44秒、峰1656055376B，Checking均仅自身。禁用构造、洞与源码本机路径检索0，原始冻结表首尾一致。另有三组独立只读审查，未将其算新路线。

仓库仅新建18行验收模块YiUPBase；其base-form对全部i/u证明proj₁树等式，不是整个带证明对象或底函数的等式。三个δ来自标准B₀闭项，原β3与c₁内κ未删除。β1的ω上界和最小搬运桥反例留在临时实验附件；β2仅接原Fn1 Bᶻᶠ，不套标准底上界。β=1探针只否定字面/逐支桥；β=实际betaᴱ1探针证明严格值反例，仍使用B₀且不是原第3站链点比较。原q0/q1独立记号上界、统一U、FirstMissing及后支错位均未判定。原数学路线未关闭，未改变前三层或新增无条件强度。

续稿原文SHA256 ec42c90145172860f46f83710f5111616e270c3b7bddae71e6fc1f8ab8e22bcf；续稿冻结表SHA256 6fe3b37976e7494af10d595561ccd9f11189c6228662549c540e69e0a4b51692。以下附件是已编译临时源码，Q1Base是正式Base的原型，不重复计数学模块：

[YiUPCheck](attachments/YiUPCheck-Codex.agda.txt)、[YiUPPartial](attachments/YiUPPartial-Codex.agda.txt)、[YiUPActualAttempt](attachments/YiUPActualAttempt-Codex.agda.txt)、[YiUPBridgeProbe](attachments/YiUPBridgeProbe-Codex.agda.txt)、[YiUPBridgeValue](attachments/YiUPBridgeValue-Codex.agda.txt)、[YiUPQ1Base](attachments/YiUPQ1Base-Codex.agda.txt)、[YiUPTools](attachments/YiUPTools-Codex.agda.txt)。


### 首次完整回报（冻结检查点）

### YiUP 完整回报

#### 1. 判决、范围与各步状态

对纲领与目标的含义：没有改树、折叠、合法性、实际继承底或起点；本路没有新增站值下界，也没有得到实际链点的独立记号上界。FirstMissing 仍未判定，不能据本次未完成关闭构造路线。

本路停在第 0 步，未进入第 1 步。纸面 q=0、1、2 估值先写入 `paper-before-check.md`，之后才启动第一个 Agda；它们均为判断。最小检查得到原 q=0 的内层实际链展开，并把 q=0 上界等价展开为该内层链全部部分和的上界，但没有实填候选记号界。q=1 的独立记号界也没有实填。

停止读法：第 0 步的上界检查未通过，交精确余项；这是“未走通/暂停”，不是第 0 步的数学命题被否定。没有发生 8G 堆耗尽，没有两次实质重设计被检查器拒绝，不以这些情况作停止理由。后续统一上界、U 与目标比较、¬FirstMissing 和错位配对均未开展；按序不越过第 0 步。

| 问题 | 精确位置 | 档与状态 |
|---|---|---|
| 原 q=0 展开是否确为 tw 2 上的继承底折叠 | YiUPCheck.actual0 | 编译定理，成立；复用 YiFNUpper.out0 |
| 原 q=0 的内部实际回灌链和部分和极限 | YiUPPartial.g₀/f₀/c₀/r₀/p₀/out0-form | 编译定义和等式，成立 |
| q=0 输出是否不高于 ψ₀(Ω_{Ω+1}) | YiUPPartial.Upper0 | 仅待证命题的类型；未有证明 |
| q=1 输出是否不高于 ψ₀(Ω_{Ω_Ω}) | YiUPPartial.Upper1 | 仅待证命题的类型；未有证明 |
| 以第 2 站参照 ψ₀(Ω_Ω) 为 q=0 上界 | YiUPPartial.not-ref2-upper | 编译否定定理；只否定这个更低候选，不否定 Upper0/Upper1 |
| 对一切 q 的独立统一上界 U | 原简报第 1 步 | 未开展，无定理 |
| FirstMissing 或 ¬FirstMissing | 原命题 | 未判定 |

没有有限数值测试；两个临时文件都是类型检查，不能把它们的退出码当成 Upper0/Upper1 的证明。

##### 检查前纸面估值（判断）

固定原 Step 2、baseᴱ 3、betaᴱ 3。以下三个独立记号界都是候选估计，不能由旧下界推得；尤其不把 ψ₀(Ω_Ω+1) 当实际值。

- q=0：输出是在 tw 2 = Ω 形状的层号上，对 Ω 树再作一次零层折叠，起点和全部低层底继承自终点 pre 3。估计它仍在 ψ₀(Ω_{Ω+1}) 以下；估计理由是新增的是同一 tw 2 层的一次折叠，且不新增外侧 tw 3 的回灌。此理由尚无上界保持定理，可信度有限；若成立，它高于实际第 2 支但低于目标。
- q=1：孩子层号已从 tw 2 变成 tw 2 ⊕ ↑(tw 2)(chain 1)，而 chain 1 有根 Ω 结点；不能用“只多一次迭代”的可数读法估值。宽松候选界取 ψ₀(Ω_{Ω_Ω})（第 3 站整棵参照）。这个候选界高于目标，单凭它不能判定 FirstMissing。没有 q=1 低于目标的纸面结论。
- q=2：再次回灌可能增加孩子层号的嵌套。估计用更宽的 ψ₀(Ω_{Ω_{Ω_Ω}})（第 4 站整棵参照）作候选界。这个估计没有链单调或闭包证明，不声称 q=1 到 q=2 的值单调。

这不是对候选界的穷尽判断。第 0 步必须分别编译 q=0 和 q=1 的独立记号上界才能继续一般形式。

#### 2. 文件、冷编与资源

仓库新增文件：0。仓库已有源码、导航、台账、报告目录、src/archive 均未改。本路只写私有实验目录；暂存结果未提升为仓库研究模块，因为原第 0 步的独立上界没有得到证明。

实际命令均在仓库根目录运行，每次带 `+RTS -M8G -s -RTS`、私有 libraries、`-l standard-library -i src -i probes -i <实验目录>`；一次只跑一个 Agda。未用 --ignore-interfaces，也未删除共享接口。自冷编只删除本目录 YiUPCheck.agdai / YiUPPartial.agdai。

| 文件 | 物理行 / 非空非注释代码行 | 冷编退出码 | 最大驻留 | RTS 总用内存 | 墙钟 | 日志 |
|---|---:|---:|---:|---:|---:|---|
| `YiUPCheck.agda` | 33 / 28 | 0 | 1,594,195,448 bytes | 2613 MiB | 15.461 s | `check-final-cold.log` |
| `YiUPPartial.agda` | 78 / 67 | 0 | 1,595,125,560 bytes | 3109 MiB | 43.104 s | `partial-final-cold.log` |

`YiUPCheck` 第一次编译在开始工作后 30 分钟内完成。最终冷编的 Checking 行只含各自的临时模块；依赖使用共享现成接口。这不是对导入依赖全部删接口重编。

#### 3. 编译定理与证书（逐字陈述）

这些是临时检查产物，不是原任务的独立记号上界。`FR` = YiFRStep，`GI` = YiGIInst，`FU` = YiFNUpper，`FS` = YiFRStations；`K.readRW` 是实际零层树的读回；`SI.E.tree` 是记号参照证书的树值。

##### YiUPCheck.agda

```agda
actual0 : FR.Step.out 2 (FR.Step.chain 2 0) ≡
  TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) FU.childBase B.zero
    (P.z≤ (B.tw 2)) (GI.betaᴱ 3) (proj₁ (O.Ωt (B.tw 2)))
```

白话：原第 0 链点的输出是 tw 2 上 Ω 树的折叠，仍使用实际继承底。来源 `FU.out0`，没有重证。

```agda
reference3 : SI.E.HC (E.EBOψ 3)
```

白话：第 3 站参照的证书是闭项，来自 `SI.conv (ET.hc-tower 3)`。`Upper1 : Set` 只是命题类型，没有 Upper1 的项。

##### YiUPPartial.agda

```agda
out0-form : proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)) ≡ proj₁ (O.limc⁺ r₀)
```

白话：原 q=0 输出逐字是内层实际行 r₀ 的部分和极限。f₀ 使用 FU.childBase，起点是相应底分量；r₀ 使用 GI.betaᴱ 3，没有换成标准底。

```agda
partial→upper0 : (U : L.Ordᶜ L.zero) → ((m : ℕ) → K.readRW (p₀ m) ≼ U)
  → K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 0))) ≼ U
upper0→partial : (U : L.Ordᶜ L.zero) → K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 0))) ≼ U
  → (m : ℕ) → K.readRW (p₀ m) ≼ U
partial-instance : (m : ℕ) → K.readRW (p₀ m)
  ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)))
```

白话：对同一个原 q=0 输出，极限上界等价于所有部分和上界。条件的非空检查取 U 为原输出的读回，并以 refl 填输出上界，得到 partial-instance；这个 U 依赖原输出，所以明确不算独立记号界。对独立 U₀ 的前提仍未填，不声称其可满足。

```agda
ref2-strict : (h : SI.E.HC (Keel⁻.row GI.keelᴱ 2))
  → L.suc (SI.E.tree h) ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 0)))
not-ref2-upper : (h : SI.E.HC (Keel⁻.row GI.keelᴱ 2))
  → K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 0))) ≼ SI.E.tree h → ⊥
```

白话：q=0 严格高于第 2 站参照，因此该参照不能作上界。来源为 `FS.k2`、`FU.prior-strict`、`NF.s≼-irrefl` 的组合。前提实例是闭项 h₂，不是空前提。

证书均在 opaque 中：

```agda
u₀-hc : SI.E.HC R.t₊
u₁-hc : SI.E.HC (E.EBOψ 3)
h₂ : SI.E.HC (Keel⁻.row GI.keelᴱ 2)
```

分别由 `SI.conv R.h₊`、`SI.conv (ET.hc-tower 3)`、`SI.conv (ET.hc-tower 2)` 填出。R.t₊ 是 ψ₀(Ω_{Ω+1})，U₀ = SI.E.tree u₀-hc，U₁ = SI.E.tree u₁-hc。上述证书不包含任何实际输出的上界证明。

#### 4. 第一个障碍（精确余项）

原第 0 步第一个未填的是：

```agda
Upper0 = K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 0))) ≼ U₀
```

其中 U₀ 是独立记号 ψ₀(Ω_{Ω+1}) 的参照。直接按实际根的极限行证明时，需要：

```agda
(m : ℕ) → K.readRW (p₀ m) ≼ U₀
```

连 m=0 的实例 `K.readRW (p₀ 0) ≼ U₀` 都未填。`out0-form` 及双向逻辑展开只暴露这个义务，没有解决它。实际 betaᴱ 3 也没有在本路获得独立记号上界；不能用它的低下界填上界。

第 0 步第二个未填的是：

```agda
Upper1 = K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 1))) ≼ U₁
```

不把这些未填命题当否定。即使 Upper1 成立，U₁ 是整第 3 站参照，高于目标第 1 项的记号位置；本路没有编译它们的比较，不能据纸面位置作原第 1 步的判决。未构造对所有 q 的 U。

#### 5. 搜索范围、偏离与事故

- 已完整读 AGENTS.md、原简报、共同护栏、EBOHandbook 第 4 节；读 README 当前状态，其他大文件按定义/签名定位读取。
- 直接查看了 YiFRStep、YiGIInst、YiFNUpper、YiLBActual、YiFRStations、YiMSShape/ValueRef、YiTBRow、YiMTTab、YiBRValue/Rel/Fold 等相关源码；部分文件只读相关片段。以上既有结果通过导入使用缓存，未声称对所有依赖从头冷编独立复核。
- 上界工具的核对范围：YiCeilRead、YiCeilWit、YiCeilSmall、YiUB*；它们使用 YiLegBlock，当前目标使用 YiRWBlock+YiTBRow。YiBRFold 现成桥针对 YiRWFold；YiMTValue 中表折叠到旧块的已用实例在 tw1 等限定范围。没有找到能直接给当前原 q=0/q=1 上界的现成实例。这里是检索结论，不是不存在这类桥的否定定理。
- YiXV 只读了 ReadCapBound/Value、CountableFoldBound、ThirdZero、Start、SourcePrefixes 相关代码/签名。尤其其 Start.pre 是旧块 tw1 运行内部有限源的前缀，不是 GI.pre 3；没有把它的 allpre 当成本路实际输出的界。没有导入任何 YiXV 文件，所以不存在导入时冻结哈希清单；也没有将运行中源码改动静默作为编译依赖。
- 无外部文献/代码调研，无子智能体，无安装、提交、推送；ps 盘点曾受沙箱拒绝，随后未提权或绕开，也未据此宣称已盘点全局进程。本路自身始终顺序编译，服从所分配的单 Agda 槽位。
- 数学偏离：没有改派发或规则；没有另开候选路线；未把纸面估计升级为值或上界。较宽的第 3 站参照曾在最初临时文件里作候选类型，后续 q=0 的精确待证类型回到纸面 U₀，q=1 仍取 U₁；没有为这些候选写出证明。
- 没有编译失败或堆耗尽；没有任何编译过的 ¬FirstMissing。没有把未走通归到壁垒、W/V/C 或定义错误。

禁项与本机路径检查见 audit.json；本路没有仓库文件可作本机路径检查。冻结文件及 SHA256 见 FREEZE.sha256，回报本身也在清单内。


### 续做完整回报（本次交付）

### YiUP 续做完整回报

#### 1. 判决、原第 0 步及工作范围

**对纲领与目标：没有改树、折叠、合法性、原 Step 2、实际底或起点。固定 q=1 的限制底展开已成为编译等式；原 q=0/q=1 的独立记号上界仍未证，也没有 ¬FirstMissing 或新增站值强度。**

首稿把“独立上界未填”作为第 0 步未通过而停报，依据不充分；未证明不等于第 0 步对象不成立。本次完整保留首稿及其冻结文件，续做了具体上界工具接线与最小反例，首稿仅算阶段检查点。原 paper-before-check 的 q=0/1/2 判断不改，未从后来诊断倒改最初估计。

本次交精确余项的依据是连续尝试的具体上界接线受阻，**不是第 0 步命题为假的结论**。三种已核查的办法分别是：直接使用 MTRel.A/topΩ 的 NoΩ 桥；删去 NoΩ 后改以新输出不高于旧输出搬运旧上界；把整个原调用的层重索引为 ReadCap 的可数源层。前一种在原调用处的前提不可填；第二种在使用实际 betaᴱ1 的最小探针上被编译值反例否定；第三种精确的 RelL 桥也被编译反例否定。这些结论不排除带更大参照的弱上界桥，也不关闭原上界路线。

本轮同时取得两处实际正接线：betaᴱ1 ≼ ω；betaᴱ2 与旧块中精确的 Fn 1 Bᶻᶠ 相关。原 betaᴱ3 及 q=0 的 m=0 部分和的实际调用均已编译展开，再尝试上述桥，未以类型别名或检索结果代替尝试。

| 原任务问题 | 本轮位置 | 档及状态 |
|---|---|---|
| q=0、1、2 检查前估计 | 首稿 paper-before-check.md；文末逐字保留 | 判断，未升级为值/上界 |
| 实际继承起点 betaᴱ1 的独立界 | YiUPTools.beta1-upper | 编译定理：不高于 ω |
| 实际继承起点 betaᴱ2 到旧工具的桥 | YiUPActualAttempt.beta2-R | 编译定理；精确到旧 Fn 1 Bᶻᶠ，无其记号上界 |
| 原 betaᴱ3 的实际控制入口 | YiUPActualAttempt.beta3-form | 编译等式；下一步是 tw 2、原 baseᴱ2/β2 下的值上界，未填 |
| 原 q=0 第 0 部分和 | YiUPActualAttempt.m0-form | 编译等式；保留两次零孩子限制底和原 β3，未填上界 |
| 固定 q=1 的实际限制底 | OCF.Lean.YiUPBase.base-form | 编译等式，三个 δ 是标准闭项，不是独立记号参照 |
| 直接旧桥的可用性 | YiUPTools / YiUPBridgeValue | 编译否定，只针对下文逐字类型 |
| q=0/q=1 的独立记号上界 | 原第 0 步 | 未证；没有用原输出充当 U |
| 统一 U、U 与目标比较、¬FirstMissing、错位配对 | 原第 1 步 | 未进入，按序不越过第 0 步 |

没有有限数值测试。refl 展开是全参数类型检查的等式证明，不是增长率估计；各退出码也不意味着原独立上界已证。

#### 2. 文件、冷编与资源

仓库仅新增 `probes/OCF/Lean/YiUPBase.lagda.md`；未改任何旧文件、src/archive、其他前缀、导航或台账。其余是一过性接线试验，留在本私有实验目录。没有子路、安装、提交或推送。

全部 Agda 各 ≤8G、一路同一时刻只跑一个，日志落文件，读取 subprocess.returncode 或直接 shell 退出码，不经过管道。最终自冷编只删列出的本路接口，依赖保持缓存。没有 --ignore-interfaces 或共享接口删除。

| 模块 | 代码行 | 冷编退出码 | 最大驻留 | RTS 总内存 | 墙钟 | 日志 |
|---|---:|---:|---:|---:|---:|---|
| `YiUPTools` | 38 | 0 | 1,572,827,024 bytes | 2643 MiB | 15.811 s | `YiUPTools.cold.log` |
| `YiUPActualAttempt` | 35 | 0 | 1,443,002,592 bytes | 2686 MiB | 16.443 s | `YiUPActualAttempt.cold.log` |
| `YiUPQ1Base` | 18 | 0 | 1,572,735,304 bytes | 2643 MiB | 15.845 s | `YiUPQ1Base.cold.log` |
| `YiUPBridgeProbe` | 41 | 0 | 1,411,734,744 bytes | 2395 MiB | 15.965 s | `YiUPBridgeProbe.cold.log` |
| `YiUPBridgeValue` | 64 | 0 | 1,384,334,936 bytes | 2560 MiB | 15.726 s | `YiUPBridgeValue.cold.log` |
| `YiUPBase` | 18 | 0 | 1,406,420,416 bytes | 2491 MiB | 15.67 s | `YiUPBase.cold.log` |

代码行的计数是非空、非整行注释的 Agda 行；数学仓库文件只计算 agda fence 内。最终每份日志的 Checking 行均只含该模块。`cold-status.json`、`audit-v2.json` 保存机器可读记录。编译失败的一次试验记录见第 5 节。

#### 3. 定理表：逐字陈述与前提实例

别名：B/O/P 分别是 YiRWBlock/YiRWOps/YiRWPath；GI 是 YiGIInst；FR 是 YiFRStep；R 是 YiBRRel；S/SO 是 YiLegBlock/YiLegOps；RV 是 YiBRValue；K 是 YiKVRel。RV.readRW 与 K.readRW 是各模块的两种同文读回。下列否定不含值时绝不当作值否定。

##### 3.1 新的仓库定理：固定 q=1 限制底

文件 `probes/OCF/Lean/YiUPBase.lagda.md`（验收文件）：

```agda
δ : ℕ → B.Tr B.zero
δ n = MT.twᶻ n
c₁ = FR.Step.chain 2 1
base-form : ∀ i (u : i P.≤ FR.Step.child 2 c₁) →
  proj₁ (GI.baseᴱ 3 i (P.inc c₁ u)) ≡
  (((proj₁ (O.Ωt i) O.+ O.ι i (δ 0)) O.+ O.ι i (δ 1)) O.+ O.ι i (δ 2))
```

白话：原第 1 链点孩子上，实际继承底是 Ωt i 后加三个标准零层闭项的嵌入。PA 后到诊断给了这个纸面式；本路没有把诊断当前提，而是独立以 refl 编译。原外侧 β3 仍传给 out，c₁ 的内部 κ 仍存在；δ1/δ2 没有独立记号上界，因此这不是封顶。

##### 3.2 已实填的实际起点工具接线

文件 `YiUPTools.agda`：

```agda
beta1-R : R.RelT B.zero S.zero (proj₁ (GI.betaᴱ 1))
  (SO.next (S.suc S.zero) S.◃s)
beta1-upper : K.readRW (proj₁ (GI.betaᴱ 1)) ≼ C.ωx C.𝟏
```

白话：第一个实际继承起点对应旧块的 next 1，读回不高于 ω。来源为 YiBROps.next-R、YiBRValue.rel≅、YiKQSuff.read≤、YiCeilRead.next≼。这里实际实例本身即证明前提可满足，没有换底。

文件 `YiUPActualAttempt.agda`：

```agda
beta2-R : R.RelT B.zero S.zero (proj₁ (GI.betaᴱ 2)) (EB.Fn 1 MV.Bᶻᶠ)
```

白话：下一实际继承起点恰接到旧块的 Fn 1 Bᶻᶠ，而不是旧 B₀ 上的 Fn 1。直接复用 YiMTValue.br1-Rᶻ，检查器确认原对象定义性接上。主审已明确：目前已验收的旧工具中没有这个精确旧对象的独立上界，不能按名字替换成已证 Allpre。

##### 3.3 原 β3 与 q=0 的 m=0：实际调用已接出

文件 `YiUPActualAttempt.agda`：

```agda
beta3-form : GI.betaᴱ 3 ≡ TB.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2))
  (GI.baseᴱ 2) B.zero (P.z≤ (B.tw 2)) (GI.betaᴱ 2) (proj₁ (O.Ωt (B.tw 2)))

m0-base : F.Base (B.tw 1)
m0-base i u = GI.baseᴱ 3 i (P.inc B.zero (P.inc B.zero u))
m0-form : p₀ 0 ≡ proj₁ (TB.ψ (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1)) m0-base
  B.zero (P.z≤ (B.tw 1)) (GI.betaᴱ 3) (proj₁ (O.Ωt (B.tw 1))))
```

白话：原 β3 本身是 tw 2 上带原继承底的 Ω 折叠；原第 0 部分和是 tw 1 上带两次零孩子限制底、仍以 β3 为起点的 Ω 折叠。不能把 m0-base 换成 B₀，也不能把 PA 固定 q=1 的公式套到这个两次零孩子路径。

p₀ 是冻结首稿 YiUPPartial 中原 q=0 内层回灌行的部分和，不是重新选择的链。该文件只导入首稿用于精确同一对象，不改它。

##### 3.4 第一种接线：NoΩ 的原调用处前提不成立

文件 `YiUPTools.agda`：

```agda
no-A-on-prefix : NoΩ B.Λ → ⊥
no-topΩ-on-out0 : ((c : B.Tr (B.tw 1)) → NoΩ (FR.Step.child 1 c)) → ⊥
```

白话：MTRel.A 若直接从原 Λ 前缀搬运，需要 NoΩ Λ，取第 1 孩子就矛盾；MTRel.topΩ 用于原 tw 2 调用，需要所有孩子无 Ω 形状，零孩子恰是 tw 1，因此矛盾。只否定所需结构前提，没有比较折叠值。

##### 3.5 第三种接线：直接读回整个原层号的 RelL 桥不成立

文件 `YiUPTools.agda` 与 `YiUPActualAttempt.agda`：

```agda
no-read-source-layer : (x : S.Tr S.zero) → R.RelL (B.tw 2) (T1.h₁ x) → ⊥
no-m0-read-source-layer : (x : S.Tr S.zero) → R.RelL (B.tw 1) (T1.h₁ x) → ⊥
```

白话：ReadCap/Countable 工具的源层 h₁ x 来自零层树，根只能为零、后继或自然极限；原 tw 1/tw 2 根为 Ω 形状，现成逐层关系不能把整个原调用重索引到这种源层。x 的域非空（zero 就是闭项），原层号也有闭项与 Ok；没有外加假设。它们不否定逐个源孩子使用这些工具，再另证外层回灌链上界的办法。

##### 3.6 第二种接线：去掉 NoΩ 后的直接逐支桥与值上界桥

文件 `YiUPBridgeProbe.agda`：最小输入为

```agda
x : B.Tr (B.tw 1)
x = B.up B.zero B.zero (B.suc B.zero) B.◃s
```

目标路径是 `P.inc B.zero P.self`，初始 β=Ωt zero；new 为 TB.ψ、表取 MT.rbᶻ，old 为 RW.ψ，其他参数相同且 B₀ 相同。编译结果：

```agda
new-first : branch0 new ≡ one
old-first : branch0 old ≡ two
one≠two : one ≡ two → ⊥
not-literal-bridge : new ≡ old → ⊥
not-rel-bridge : R.RelT B.zero S.zero new old′ → ⊥
```

one=suc zero，two=suc(suc zero)；old′ 是旧块对应的 `1 + ι zero (next 1)`。这只否定逐字/逐支桥。初始 β=1 探针的两个输出在纸面上都读作 ω；本节未编译其同值，亦不从逐支不同推出值不同。

文件 `YiUPBridgeValue.agda`：把同一最小输入的 β 改为**实际 GI.betaᴱ1**（原 q=0/q=1 的定义均未改，此处是诊断桥的探针），得到无外加前提的值反例：

```agda
strict : L.suc (RV.readRW old) ≼ RV.readRW new
not-upper-bridge : RV.readRW new ≼ RV.readRW old → ⊥
```

白话：旧回退是 β+ω，表行是 next β；其纸面读法分别为 ω·2 与 ω²。本节的编译结论是逐字 strict，而非以该纸面读法为前提：具体 new/old 通过 YiBROps 的 next/+ /ι 关系搬到旧块，旧读回加法与 ι 的 ≅、YiCeilRead.assoc≼、加法单调与第 2 分支给出逐字 strict，最后用 YiNFO.s≼-irrefl。β1、输入 x、非零证据与旧对应树都是闭项，所以没有空前提。这个反例否定“新输出不高于旧输出”的这条搬运方式，不否定带更高参照的值上界桥。

#### 4. 第一个精确余项及后续未进入范围

原第 0 步仍需要原 β3 及 m=0 的独立记号控制。若以独立记号参照 Uβ 作起点，首先未填的是：

```agda
beta3-upper : K.readRW (proj₁ (GI.betaᴱ 3)) ≼ Uβ
```

其中 Uβ 必须是独立记号参照，不能定义成 β3 的读回或其他原输出。经 beta3-form，它是 tw 2、GI.baseᴱ2、GI.betaᴱ2 下的那次具体折叠上界。beta2-R 给出一个可用的精确旧对象，但缺其上界，不是把源改成 B₀ 的许可。

其次，对 q=0 的实际第 0 部分和，需要独立记号 U₀ 满足：

```agda
m0-upper : K.readRW (p₀ 0) ≼ U₀
```

经 m0-form，要处理 tw 1 上的具体 m0-base 和原 β3；上述两条旧桥不能直接交出它。即使该项填出，仍需控制所有原内层部分和，再得到 q=0 上界；本路没有把一个部分和上界说成整个输出上界。

q=1 的 base-form 已实填，但 δ1、δ2、β3 与 c₁ 内部回灌依赖都未获独立记号上界，仍没有原 q=1 上界；不固守首稿 U₀ 猜测，也没有宣称某个放宽后的 U 已成立。

**判断，供继续时参考：** 与现有反例不冲突的尝试是允许上界参照在表行发生额外增长，或者在实际链上逐点构造较弱的值上界关系。此处没有完成这类关系或穷尽所有办法；未改树定义。第 1 步的一切 q 统一 U、与目标比较、否定 FirstMissing、错位配对均未作数学结论。

#### 5. 偏离、事故、来源与冻结

- 所有原关键对象、动词与范围保持；没有用“同名”替换实际 Fn1 Bᶻᶠ，没用较低下界当值或上界，也没把后到 PA 诊断当公理。
- 现有旧模块只按签名/相关定义阅读及导入现成接口。本路冷编的是自己的模块，未声称冷编所有旧依赖。新增定理所有参数与分支均经检查器；最终日志只含各自 Checking 行。
- 本轮没有导入任何 YiXV 模块，因此没有运行中 XV 导入冻结清单。对它的现有结构只作工具适用范围的判断；编译反例本身只依赖稳定的 NoΩ、RelL 及原层号定义，未依赖转述的 XV 新结论。Root 告知其已验收219件中没有上述精确旧对象上界，消息原文保存在 continuation-instructions.md。
- YiUPBridgeProbe 第一次编译退出42，错误是 one≠two 中泛型 T S 的隐式 S 未解；显式给 one/two 类型 B.Tr B.zero 后通过。它不是实质重设计受阻，未计作停止依据。没有 LibraryError、堆耗尽或超时；没有擅自加堆。
- 没有把桥反例归入 LPO 壁垒、W/V/C；这些否定仅对逐字陈述负责。尤其无 ¬FirstMissing、无“定义必须改”的结论。
- 首稿保持原样，第二份报告另存；初始估计与后到诊断分别留档。禁项、本机路径扫描与冷编统计见 audit-v2.json；冻结清单列出本报告、所有本轮源码、日志与唯一仓库新文件的 SHA256。

#### 附：首稿检查前纸面判断（原文，不改）

### YiUP：检查前纸面估值（判断，不是定理）

固定原 Step 2、baseᴱ 3、betaᴱ 3。以下三个独立记号界都是候选估计，不能由旧下界推得；尤其不把 ψ₀(Ω_Ω+1) 当实际值。

- q=0：输出是在 tw 2 = Ω 形状的层号上，对 Ω 树再作一次零层折叠，起点和全部低层底继承自终点 pre 3。估计它仍在 ψ₀(Ω_{Ω+1}) 以下；估计理由是新增的是同一 tw 2 层的一次折叠，且不新增外侧 tw 3 的回灌。此理由尚无上界保持定理，可信度有限；若成立，它高于实际第 2 支但低于目标。
- q=1：孩子层号已从 tw 2 变成 tw 2 ⊕ ↑(tw 2)(chain 1)，而 chain 1 有根 Ω 结点；不能用“只多一次迭代”的可数读法估值。宽松候选界取 ψ₀(Ω_{Ω_Ω})（第 3 站整棵参照）。这个候选界高于目标，单凭它不能判定 FirstMissing。没有 q=1 低于目标的纸面结论。
- q=2：再次回灌可能增加孩子层号的嵌套。估计用更宽的 ψ₀(Ω_{Ω_{Ω_Ω}})（第 4 站整棵参照）作候选界。这个估计没有链单调或闭包证明，不声称 q=1 到 q=2 的值单调。

这不是对候选界的穷尽判断。第 0 步必须分别编译 q=0 和 q=1 的独立记号上界才能继续一般形式。

首稿冻结清单 SHA256：`d9f27817650b4fdfc045dd372fe7725074dc0cad24243c3c6381dcfabd5e7c1f`；本次逐项核对仍一致。

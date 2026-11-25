# YiCK 实际内层链结构检查：8G停报：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；原始编译记录见回报与LOG |
| 新建仓库文件（主审核实） | 无数学模块；主审只保留未通过实验/未编译草稿附件 |
| 文件前缀 | `YiCK` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiCK 第0步8G停报复核” 一节 |
| 主审复核后的一句结论 | 第0步一次8G堆耗尽，251；无新增编译定理，不重编失败实验、不改定义；目标未否定。 |

## 简报原文

### 任务简报：攻那一条具体的不等式（数学，构造）（前缀 YiCK）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十五批四路之一（选项原文 "攻那一条具体的不等式 (Recommended)"）。四路都冲着第 3 站的那一条不等式：一路判定上界、一路构造、一路摆脱侧、一路纸面审计，在数学上互不依赖。
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
- **目标**：上面的 `missing-child-low₁`，只对这一个对象。
- **结构**（判断，供参考）：孩子层号 h₁ = tw 2 ⊕ ↑ (tw 2) c₁。它左边的 `tw 2` 部分在槽位层 `tw 1` 上有 Ω 结点，Ω 树折叠时会在 `tw 1` 上走一条内层回灌链，底是继承来的（`baseᴱ 3` 沿 `inc c₁` 限制）。第 2 站的链在 `tw 1` 上的关系已证（`YiS2Chain.actual-chain`，底是 `baseᴱ 2`），本路的内层链与它同形、底不同。
- **方法要求**：结构化地做，不要沿具体分支一层层展开（YiMS 用这种办法推到 ψ₀(Ω_Ω+2) 就 8G 耗尽，离目标太远）。具体参照树放 `opaque`，经非单射的头求解的隐式参数显式写出（`probes/Survey/EBOHandbook.md` 第 4 节）。不写全域律，只对实际出现的对象陈述。

#### 要做的（按序）
0. **最小检查**，在临时目录：展开 h₁ 的结构与 `Ωt h₁` 折叠的第一行，写出内层回灌链（槽位层 `tw 1` 上，继承的底）的前两个链点；确认 `missing-child-low₁` 的类型与 `YiLBActual.out-child 1` 接得上。不成立就停下回报。
1. **内层链的关系**：照 `YiS2Chain.actual-chain` 的证法，对这条内层链证在 `tw 1` 上的关系（对一切内层链点）；`YiS2Chain` 的证明若依赖 `baseᴱ 2` 的具体形状，说出依赖在哪里、换成继承的底后哪一步要改。
2. **折到第 0 层与值**：由内层链的关系与已有的出口和反射（`station→certificate`、`HC.of⁰`、`ex-of⁰`，以及 `YiLBActual.child-gamma`），得到 `missing-child-low₁` 的值不等式。
3. 得到后编译 `FirstMissing`（见证 1）；再试 `Tail 2`。做不到就交第一个挡住的引理，精确到项。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiCK`（模块名 `OCF.Lean.YiCK…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiUP`、`YiTC`、`YiPA`）。验收文件，文首标明。
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

### YiCK 完整回报（第五十五批，2026-11-15）

#### 1. 判决与问题表

本路没有新增编译定理、闭项或值下界；没有修改树、折叠、合法性，也没有据此否定目标不等式。第 0 步的临时结构检查在 8G 堆上限下耗尽，触发原简报“8G 仍耗尽（先在回报里说明）”的停止条件，已停止后续证明和编译，不加堆、不改题。

第一个临时文件已经写出并完成一次编译尝试，编译耗时 145.575 秒，满足 30 分钟内写出并编译的过程要求。退出码为 251，日志包含 `Heap exhausted`。本次失败不作“第 0 步陈述为假”的结论。

| 问题 | 位置 | 档与结果 |
|---|---|---|
| 实际外层链点 c₁ 的 Ω 形状，以及 h₁ 在 tw 1 上分支 | YiCKStep0.agda:35–38 | 未编译通过；无定理 |
| 实际继承底上的内层回灌链，前两点及第二次回灌 | YiCKStep0.agda:39–55 | 已写出候选定义与等式；未编译通过 |
| Ωt h₁ 零层折叠的第一行 | YiCKStep0.agda:56–58 | 未编译通过 |
| missing-child-low₁ 经 out-child 1 接回原 FirstMissing | YiCKStep0.agda:59–65 | 已写出条件接线；未编译通过 |
| 第 1 步：内层链在 tw 1 上的关系 | YiCKStep1.agda | 仅编译前准备的草稿，未启动编译；不计结果 |
| 第 2 步：折到第 0 层的目标值比较 | 原 missing-child-low₁ | 未进入 |
| 第 3 步：FirstMissing 见证 1，再试 Tail 2 | 原 YiFRStep | 未进入 |

#### 2. 文件与编译

仓库新建/修改文件为 0。没有需要交付冷编的 YiCK 仓库模块，没有删除共享接口。全部临时产物在本回报同目录。

| 文件 | 代码行 | 编译状态 | RTS 数字 |
|---|---:|---|---|
| YiCKStep0.agda | 65 | 一次初编，251；无已生成接口可交付冷编 | 最大驻留 8,431,982,096 bytes；total memory in use 8298 MiB；分配 105,571,205,128 bytes；elapsed 145.575s |
| YiCKStep1.agda | 34 | 未编译草稿 | 无 |

命令（原样结构；本机路径以占位符表示）：

```sh
timeout 600 agda +RTS -M8G -s -RTS --library-file=<实验目录>/libraries -i src -i probes -i <实验目录> -l standard-library <实验目录>/YiCKStep0.agda > <实验目录>/step0.log 2>&1
```

Agda 退出码由紧接编译的 `printf` 直接取得，为 251，未经过管道。日志只有 YiCKStep0 自身的 Checking 行，随后是堆耗尽与 RTS 统计，没有依赖重编行。

静态检索见 `static-check.json`：两份临时源码的禁用构造、洞及本机路径命中均为 0。未使用 XV 文件；无需冻结或比较运行中的 XV 源码。

#### 3. 定理表与未验收陈述

编译定理表为空。以下逐字列候选陈述，均不是编译定理。

```agda
c₁-shape : c₁ ≡ B.Ω (inj₁ (inj₁ tt)) branch
h₁-shape : h₁ ≡ B.nd (B.sΩ (B.tw 1)) a

first-row : TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁)
  (GI.betaᴱ 3) (proj₁ (O.Ωt h₁))
  ≡ O.limc⁺ (λ n → inner-out (inner-chain n))

Missing = (h : SI.E.HC LS.target) → SI.E.tree h ≼ K.readRW (proj₁
  (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ B.zero (P.z≤ h₁)
    (GI.betaᴱ 3) (proj₁ (O.Ωt h₁))))

connect : Missing → (h : SI.E.HC LS.target) →
  SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 c₁))
first-at-one : Missing → FR.FirstMissing
```

其中对象、底和起点均保留实际定义：

```agda
k = B.tw 2
c₁ = FR.Step.chain 2 1
h₁ = FR.Step.child 2 c₁
o₁ = proj₂ (P.Ok-tw 3) c₁
base₁ : F.Base h₁
base₁ i u = GI.baseᴱ 3 i (P.inc c₁ u)
base₀ : F.Base k
base₀ i u = GI.baseᴱ 3 i (P.inc B.zero u)
branch : B.Tr (B.tw 1) → B.Tr k
branch d = proj₁ (TB.ψ k (P.Ok-tw 2) (MT.rbᶻ k) base₀ k P.self
  (GI.baseᴱ 3 k (P.ink P.self)) (FR.Step.g 1 d))
a : B.Tr (B.tw 1) → B.L
a d = k B.⊕ B.↑ k (branch d)
inner-g : B.Tr (B.tw 1) → B.Tr h₁
inner-g d = proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = a} d (O.Ωt (a d)))
inner-feed : B.Tr (B.tw 1) → B.Tr (B.tw 1)
inner-feed d = proj₁ (TB.ψ h₁ o₁ (MT.rbᶻ h₁) base₁ (B.tw 1) (P.ink P.self)
  (base₁ (B.tw 1) (P.ink P.self)) (inner-g d))
inner-chain : ℕ → B.Tr (B.tw 1)
inner-chain = O.iter inner-feed B.zero
```

`inner-chain` 是原折叠公式在孩子 h₁ 处得到的内层链候选名；`Missing` 是原目标不等式的同对象别名。接线的候选证明逐字使用 `sym (LA.out-child 1)`，未以已知第 2 站值充作第 3 站值，也未使用 station→certificate 循环填 K3。

#### 4. 第一个障碍与精确余项

第一个实际障碍是 YiCKStep0 整文件在 8G 内未通过第 0 步结构检查。日志只报文件级 Checking，没有定位分配发生在哪条声明，因此不能声称已经定位到某一个等式；尤其不能把 `first-row` 认作已确定的耗尽点。

第 0 步还需编译确认上述 `c₁-shape`、`h₁-shape`、`first-row`、实际继承底下的前两链点及 `connect`。这些确认之前，本路不能进入第 1 步。

以下是从已读取源码得到的纸面分析，不是本路编译定理：YiS2Chain 中 `slot-above` 是唯一直接写出 `baseᴱ 2`/`pre 2` 来建立底下界的位置；`feed-above` 也代入了该底，但所用 `ψ-⊵` 定理本身允许任意底。`actual-above`、`chain-top`、`actual-chain` 则用传递、已有 leafΩ 与 gamma-bound，不再展开该底。对本路继承底，候选替换为：

```agda
slot-above : proj₁ (O.Ωt (B.tw 1)) K.⊴
  proj₁ (base₁ (B.tw 1) (P.ink P.self))
slot-above = ψ-⊵ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) (B.tw 1)
  (P.inc 3 (P.inc c₁ (P.ink P.self))) (O.Ωt (B.tw 1)) (GI.pre 3)
```

该替换及关系链仅留在未编译的 YiCKStep1 草稿；不能据此报告“第 1 步已完成”。草稿中的列表空项作用域等也未经检查。第 2 步尚未构造任何从高层关系到零层值比较的推导。

#### 5. 偏离、事故与读取范围

- 事故：第 0 步一次编译在 8G 堆上限耗尽，未重新设计、未重跑、未加堆。堆耗尽后只做读日志、静态检索、回报和哈希冻结；没有再运行 Agda。
- 第一个临时文件含结构化的一行展开与链公式，没有沿具体分支逐层求值；没有把一般全域保持律换作目标。
- 没有仓库代码、导航、台账或留档改动；没有提交、推送、安装、子路、删除或移动共享文件。
- AGENTS.md、YiCK 原简报、batch55-guardrails.md、EBOHandbook 第 4 节均已完整读。YiS2Chain 的证明正文、YiLBActual 的 out-child、YiFRStep 的 Step/FirstMissing、YiGIInst 的实际底定义、YiTBRow 的折叠首行已直接读取。
- YiS2Low 的 station→certificate、YiHCCheck 的 of⁰/ex-of⁰、YiKCSem 的 sem→M⁰ 等已读相关签名/定义。本路没有应用这些来建立值。
- 原简报中的外部文献与 YiMS 回报未重新读或独立复核；本回报未把它们列成本路结果。
- `source-hashes.json` 是本路结束时相关源码与简报的哈希快照，不冒称开工前冻结；没有导入 XV。

冻结清单见 `frozen-hashes.json`，包含本回报、临时源码、完整编译日志、静态检查和源码快照的 SHA-256。

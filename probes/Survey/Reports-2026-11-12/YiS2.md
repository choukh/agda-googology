# YiS2 第2站实际关系连出口：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiS2Shape、Chain、Low、Accept |
| 文件前缀 | `YiS2` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiS2 实际LowAt2与第3站起条件出口复核” 一节 |
| 主审复核后的一句结论 | 4件独立冷编0；LowAt2以既有值下界经语义反射构造实际R+同推导Ex；终点剩Low>=3全族，未新增强度。 |

## 简报原文

### 任务简报：第 2 站的保持连出口：在 Ω 槽位上直接构造（数学）（前缀 YiS2）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十四批（选项原文 "派 (Recommended)"，问题是 "照 YiS1 的办法直接构造第 2 站的保持连出口（第一次在 Ω 槽位上用这种做法；第 2 站的值已知）"），与在跑的 YiXV、YiMS、YiFN、YiSL、YiLB 在数学上互不依赖。
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
- **龙骨上的 Leaf 与 Lift 已全部实填**（YiNL，主审复核过）：`YiNLRead.readR : ∀ ℓ {ν c} → GR.R ℓ ν c → GR.Rd (↑ ℓ c) ν`，`YiNLKeel.leaf-keel`、`lift-keel`，`YiNLTop2.leaf-tw2`（塔第 2 项对一切读法的 Leaf），`YiCNTw1.leaf-tw1`；`YiNLKeel.ebo-from-low : CA.LowRest → …`。主审在临时文件里把它与第 1 站拼起来（留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC5Low.agda.txt`）：
  ```agda
  ebo-from-low2 : (∀ n → C.LowAt (suc (suc n))) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  ebo-from-low2 lo = ebo-from-low λ { zero → low1 ; (suc n) → lo n }
  ```
  即关系路线只差从第 2 站起每站的保持连出口。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（另见上面的共同陈述）
- **目标**（`YiCNKeel` 第 36 行，逐字）：
  ```agda
  LowAt n = GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n))) → Σ (GR.R B.zero (row n) (twc n)) H.Exᴴ
  ```
  本路要 `LowAt 2`。第 2 站的参照是 ψ₀(Ω_Ω)，它的值下界已由已有的 BTBO 下界得到（`YiFRStations.k2`），但关系推导连同出口证据还没有；`LowAt 2` 是关系路线在 Ω 槽位上的第一站。
- **第 1 站的做法**（照着做，回报 `probes/Survey/Reports-2026-11-12/YiS1.md`）：`YiS1Shape` 展开第 1 行（实际底 `baseᴱ 1`、起点 `betaᴱ 1`、路径、实际的第 1 支与标准底 `twᶻ 1` 字面不同）；`YiS1Low.folded¹` 直接为实际输出构造关系推导与出口证据（根链两次 `next⁺`，两次取第 0 支到有限层 `fn 1`，复用不带 `mc` 的保持，再经 `HC.of⁰`/`ex-of⁰` 与两次上折传回，最后取部分和）；不先证全域保持，忽略 `LowAt` 的输入。
- **第 2 站的新难处**：回灌链住在槽位层 `tw 1` 上（`YiFRStep` 的 `Step 1`：`ℓ = tw 2`，`k = tw 1`，`feed`、`chain`、`out`），`tw 1` 是 Ω 形状层号。链点的关系要在 `tw 1` 那一层上表述（`YiGIRel` 的 `GR.R (tw 1)`），再折到第 0 层。可用：塔第 1 项那一层的已有结果（`YiKPRel`、`YiLTKid`、`YiPCKeel.k1ᴾ`、`YiPJQ.qω+1`、`YiPJLimStep`）、`leaf-tw1`、`readR`；出口条件 `Exᴴ` 只在 `mc` 结点上要求标准形（`¬Mono`、`¬Exit′` 说明去不掉）。

#### 要做的（按序）
0. **最小检查**，在临时目录：展开 `keelᴱ` 的第 2 行（`row 2`、`twc 2`、`baseᴱ 2`、`betaᴱ 2`、路径），以及 `Step.chain 1 0`、`Step.chain 1 1`；确认 `LowAt 2` 的类型与要构造的推导的形状。不成立就停下回报。
1. **直接构造**：为实际的 `twc 2` 构造 `GR.R B.zero (row 2) (twc 2)` 的推导，每个 `mc` 结点满足标准形条件；链点在槽位层 `tw 1` 上的关系，只对实际出现的链点构造，不写全域律。
2. 得到 `LowAt 2` 后，经 `ebo-from-low2` 写出 "从第 3 站起的保持连出口 ⇒ 终点"，并说明第 2 站的构造里哪些部分对一般的 n 可以照搬（为第 3 站做准备）。做不到就交第一个挡住的地方：哪个链点在 `tw 1` 上的关系造不出来，或哪个 `mc` 结点不是标准形，精确到项。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiS2`（模块名 `OCF.Lean.YiS2…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiMS`、`YiFN`、`YiSL`、`YiLB`）。验收文件，文首标明。
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
  - **堆上限 8G**：同时最多六路在编译，机器共 64G。若某个文件确实要超过 8G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
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

### YiS2 完整回报（待根审）

#### 1. 判决与范围

实际站上的条件反射 station→certificate 已对全部 n 编译，前提为所写的 Kᴱ n；LowAt 2 用 k2 实例化后已实填；交付为实际 twc 2 上的关系推导以及同一推导的 Exᴴ，并给出“从第 3 站起 LowAt 全族 ⇒ 实际终点的 EBO 序数值下界”的条件定理。树、折叠、表、合法性、实际底、实际起点与链没有改动。四件新增文件都是验收文件。

本批没有新增序数强度：ψ₀(Ω_Ω) 的下界复用 YiFRStations.k2。新增的是可供关系路线消费的 Σ 证书。最终证明经现成的语义反射函数构造，不是 YiS1 那种逐层保持的证明。实际槽位链的关系已独立编译保留；最终 LowAt 2 构造不使用这份链关系，不据此声称一般 Low 或第 3 站的逐链保持已经完成。

主审已在本线程明确说明：护栏禁止以值公式冒充 Σ，而不禁止现成函数真正反射出相同目标的证书。原文保存在 YiS2-root-clarification.txt；本批按此澄清执行，目标类型没有放宽。

一般反射只统一第四层的验收接线，不提供树侧自足判据。

第 0 步完成：YiS2Shape 核对 row 2、twc 2、baseᴱ 2、betaᴱ 2、路径、chain 1 0 与 chain 1 1；后者进一步展开为 tw 1 上沿 self 折 Ω 树。输入实例 input2 = leaf-keel 2 rd2，故 LowAt 2 不是靠空域。第 0 步 refl 仅核对指定闭项，不据此声称一般展开或保持。

| 问题 | 位置 | 结果与档 |
|---|---|---|
| 实际参数与前两个链点 | YiS2Shape | 指定闭项展开测试通过；input2 是已编译实例 |
| 实际正编号链点的所需 γ 关系 | YiS2Chain.actual-chain | 编译定理，量化全部 n |
| 实际孩子的 Ω 树关系 | YiS2Chain.child-leaf / actual-g | 编译定理，量化全部 n |
| 实际 twc 2 的 R 与同一推导 Exᴴ | YiS2Low.folded² | 无附加前提的编译定理 |
| LowAt 2 | YiS2Low.low2 | 无附加前提的编译定理 |
| 从第 3 站起的 LowAt 全族到终点 | YiS2Accept.ebo-from-low3 | 编译条件定理，剩余全族未实填 |
| 用同一证书走出口 | YiS2Accept.k2-from-certificate | 编译定理，值下界仍为已知第 2 站 |

#### 2. 证明接线与前提可满足性

完整核读 YiKCSem 的 inv-suc / sem→M⁰：它们对第 0 层的实际 Tr zero 工作，不要求标准底，不读取当前折叠的表，也不将值不等式直接当成关系。inv-suc 从构造性的值序证明中选出实际后继子树；sem→M⁰ 对 HC 证明递归，返回不带 mc 的 YiKVRel.M⁰。

hc-row n 用 YiGIEnd.row-eq n 把 EboLeanTree.hc-tower n 运输到实际 Keel⁻.row keelᴱ n，h2 = hc-row 2。hc-tower 的源码是 hc (nf-tower k) (c∷ c[])；hc 经可数标准形良基证明构造 HC，不是公设。hc-row 放在 opaque 中，避免转换展开良基证明。

value-from-station n kn 先用 YiAbsSimInst.toL-tree (hc-row n)，把具体参照接到抽象 SI.E.tree，再调用给定 kn；不要求全族 Kᴱ 成立。sem→M⁰ 需要的 HC 与同一个参照的值不等式全部提供，实际站的证书统一在一处构造：

    raw-from-station n kn = KS.sem→M⁰ (hc-row n) (Keel⁻.twc keelᴱ n) (value-from-station n kn)
    station→certificate n kn = HC.of⁰ (raw-from-station n kn) , HC.ex-of⁰ (raw-from-station n kn)
    raw2 = raw-from-station 2 k2
    folded = HC.of⁰ raw2
    ex-folded = HC.ex-of⁰ raw2
    folded² = station→certificate 2 k2
    low2 _ = folded²

of⁰ 与 ex-of⁰ 的源码已核读：转换只产生 mz、m1、mL、mw；在零层不可能出现 mΩ/mU；没有 mc。因此本输出推导的每个 mc 标准形条件为空，Exᴴ 由同一 raw2 的 ex-of⁰ 编译证明。YiS2Chain.actual-chain 里使用的高层 mc 属于另一份对照推导，不能拿它的标准形性质替代本输出的 Exᴴ；本批没有这样做。

终点接线先在 ebo-from-low2 中用已有 low1 填第 1 站，再在 ebo-from-low3 中用本次 low2 填第 2 站。第 0 站仍由既有 YiCNAccept / YiCNKeel 组装提供。未加入隐藏前提、函数外延或新的定义参数。

#### 3. 文件表与冷编

四件均先初编 0，再逐件删除字面路径下自身接口后冷编；依赖接口保留。收到主审后续一般 n 的建议后，先在 YiS2UniformReflect.agda 编译一般条件反射 0，再仅重整 YiS2Low；Low 与其依赖者 Accept 再次删除自身接口冷编 0。Shape/Chain 源字节未变。每次 timeout 600 与 +RTS -M8G -s -RTS，同时只跑一个 Agda。冷编日志断言仅有对应自己模块的 Checking 行。

| 文件 | 代码行 | 非空代码行 | 物理行 | 冷编退出码 | 最大驻留 B | RTS 总内存 MiB |
|---|---:|---:|---:|---:|---:|---:|
| YiS2Shape | 45 | 45 | 52 | 0 | 1,577,472,856 | 2633 |
| YiS2Chain | 53 | 48 | 60 | 0 | 1,654,177,880 | 2760 |
| YiS2Low | 49 | 46 | 56 | 0 | 1,605,112,824 | 2645 |
| YiS2Accept | 26 | 23 | 33 | 0 | 1,639,749,448 | 2720 |

行数口径：代码行是唯一 Agda fenced block 中全部行（含空行）；另列非空代码行和物理行，不与其他口径比较。内存是 +RTS -s 的 maximum residency，不是系统 RSS；8G 是每次堆上限。

当前逐件日志：YiS2Shape-cold.log、YiS2Chain-cold.log、YiS2Low-uniform-cold.log、YiS2Accept-uniform-cold.log；对应 .exit 是实际 Agda/timeout 退出码，没有经管道。机器路径只出现在私有回报与日志，不出现在四件仓库文件中。

#### 4. 定理表（逐字签名）

下面附录从冻结前源文件提取逐字签名；没有改写签名或省去前提。除标注的形状测试外，均为编译定理；value-from-station / raw-from-station / station→certificate / ebo-from-low2 / ebo-from-low3 都是带其所写前提的条件定理。station→certificate 的前提在 n = 2 上由 k2 实例化；未声称全族 Kᴱ 已实填。表中解释与代码签名一一对应。

| 名字 | 白话 | 文件 | 档 |
|---|---|---|---|
| `YiS2Shape.row2` | 核对实际第 2 行的记号项；指定闭项展开测试。 | `YiS2Shape.lagda.md:30` | 有限展开测试 |
| `YiS2Shape.base2` | 核对实际第 2 行继承底的逐分量展开。 | `YiS2Shape.lagda.md:32` | 有限展开测试 |
| `YiS2Shape.beta2` | 核对实际起点由终点前缀 cum FΛ 1 产生；指定展开测试。 | `YiS2Shape.lagda.md:34` | 有限展开测试 |
| `YiS2Shape.path2` | 核对实际零层路径；指定展开测试。 | `YiS2Shape.lagda.md:36` | 有限展开测试 |
| `YiS2Shape.closed2` | 核对实际闭树等于终点实际第 2 支；指定展开测试。 | `YiS2Shape.lagda.md:38` | 有限展开测试 |
| `YiS2Shape.actual2` | 核对闭树确为实际参数的一次折叠；指定展开测试。 | `YiS2Shape.lagda.md:40` | 有限展开测试 |
| `YiS2Shape.low2-type` | 核对原目标的输入、实际输出与同一推导出口类型；指定展开测试。 | `YiS2Shape.lagda.md:42` | 有限展开测试 |
| `YiS2Shape.input2` | 原 LowAt 2 输入的闭实例。 | `YiS2Shape.lagda.md:44` | 编译定理 |
| `YiS2Shape.chain0` | 核对实际链起点是零；指定展开测试。 | `YiS2Shape.lagda.md:46` | 有限展开测试 |
| `YiS2Shape.chain1` | 核对实际第 1 链点的一次实际 feed；指定展开测试。 | `YiS2Shape.lagda.md:48` | 有限展开测试 |
| `YiS2Shape.chain1-child` | 进一步核对第 1 链点为 tw 1 上沿 self 的折叠；指定展开测试。 | `YiS2Shape.lagda.md:50` | 有限展开测试 |
| `YiS2Chain.slot-above` | 实际槽位底不低于 tw 1 的 Ω 树。 | `YiS2Chain.lagda.md:38` | 编译定理 |
| `YiS2Chain.feed-above` | 每次实际 feed 输出不低于同一个实际槽位底。 | `YiS2Chain.lagda.md:40` | 编译定理 |
| `YiS2Chain.actual-above` | 每个正编号实际链点具有同一 Ω 树结构下界。 | `YiS2Chain.lagda.md:42` | 编译定理 |
| `YiS2Chain.chain-top` | 全部正编号实际链点具有 tw 1 上的基准关系。 | `YiS2Chain.lagda.md:45` | 编译定理 |
| `YiS2Chain.gamma-bound` | 所需 γ 项的项序界；不是新值上界。 | `YiS2Chain.lagda.md:48` | 编译定理 |
| `YiS2Chain.actual-chain` | 全部实际正编号链点对着所需 γ 项。 | `YiS2Chain.lagda.md:51` | 编译定理 |
| `YiS2Chain.child-leaf` | 实际孩子 Ω 树对着相应 Ω 项。 | `YiS2Chain.lagda.md:54` | 编译定理 |
| `YiS2Chain.actual-g` | 实际 tw 2 上的 g 分支对着所需 Ω 项。 | `YiS2Chain.lagda.md:58` | 编译定理 |
| `YiS2Low.hc-row` | 所有实际行的封装 HC 证书。 | `YiS2Low.lagda.md:32` | 编译定理 |
| `YiS2Low.value-from-station` | 给定实际站的 Kᴱ，接成具体参照的值界。 | `YiS2Low.lagda.md:35` | 编译条件定理 |
| `YiS2Low.raw-from-station` | 给定实际站的 Kᴱ，构造不带 mc 的关系。 | `YiS2Low.lagda.md:37` | 编译条件定理 |
| `YiS2Low.station→certificate` | 给定实际站的 Kᴱ，统一构造原实际 Σ 证书。 | `YiS2Low.lagda.md:39` | 编译条件定理 |
| `YiS2Low.h2` | 第 2 行的封装 HC 闭证书，防止展开良基递归。 | `YiS2Low.lagda.md:42` | 编译定理 |
| `YiS2Low.value2` | 把既有 k2 接成现成反射函数所需的具体参照值界。 | `YiS2Low.lagda.md:44` | 编译定理 |
| `YiS2Low.raw2` | 实际闭树上的不带 mc 的关系推导。 | `YiS2Low.lagda.md:46` | 编译定理 |
| `YiS2Low.folded` | 转换成原 GR.R 关系。 | `YiS2Low.lagda.md:48` | 编译定理 |
| `YiS2Low.ex-folded` | 同一转换后推导的出口证据。 | `YiS2Low.lagda.md:50` | 编译定理 |
| `YiS2Low.folded²` | 原目标的实际 Σ 闭证书。 | `YiS2Low.lagda.md:52` | 编译定理 |
| `YiS2Low.low2` | 实填第 2 站 LowAt。 | `YiS2Low.lagda.md:54` | 编译定理 |
| `YiS2Accept.k2-from-certificate` | 本次同一 Σ 走原出口后的实际第 2 站值下界。 | `YiS2Accept.lagda.md:25` | 编译定理 |
| `YiS2Accept.ebo-from-low2` | 用既有第 1 站，将条件写成从第 2 站起。 | `YiS2Accept.lagda.md:28` | 编译条件定理 |
| `YiS2Accept.ebo-from-low3` | 用本次第 2 站，将终点条件写成从第 3 站起。 | `YiS2Accept.lagda.md:31` | 编译条件定理 |



##### YiS2Shape.row2

```agda
row2 : Keel⁻.row keelᴱ 2 ≡ (E.ψ [] (E.Ωt (E.Ωt (E.natT 1))) ∷ [])
```

##### YiS2Shape.base2

```agda
base2 : ∀ i u → baseᴱ 2 i u ≡ T.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) i (P.inc 2 u) (O.Ωt i) (O.cum FΛ 1)
```

##### YiS2Shape.beta2

```agda
beta2 : betaᴱ 2 ≡ T.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (O.cum FΛ 1)
```

##### YiS2Shape.path2

```agda
path2 : Keel⁻.w₀ keelᴱ 2 ≡ P.z≤ (B.tw 2)
```

##### YiS2Shape.closed2

```agda
closed2 : Keel⁻.twc keelᴱ 2 ≡ MV.brᶻ 2
```

##### YiS2Shape.actual2

```agda
actual2 : Keel⁻.twc keelᴱ 2 ≡ proj₁ (T.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (baseᴱ 2) B.zero (P.z≤ (B.tw 2)) (betaᴱ 2) (proj₁ (O.Ωt (B.tw 2))))
```

##### YiS2Shape.low2-type

```agda
low2-type : CN.LowAt 2 ≡ (GR.R (B.tw 2) (E.Ωt (E.Ωt (E.natT 1))) (proj₁ (O.Ωt (B.tw 2))) → Σ (H.M⁰ (E.ψ [] (E.Ωt (E.Ωt (E.natT 1))) ∷ []) (Keel⁻.twc keelᴱ 2)) H.Exᴴ)
```

##### YiS2Shape.input2

```agda
input2 : GR.R (B.tw 2) (E.Ωt (E.Ωt (E.natT 1))) (proj₁ (O.Ωt (B.tw 2)))
```

##### YiS2Shape.chain0

```agda
chain0 : FR.Step.chain 1 0 ≡ B.zero
```

##### YiS2Shape.chain1

```agda
chain1 : FR.Step.chain 1 1 ≡ proj₁ (T.ψ (B.tw 2) (P.Ok-tw 2) (MT.rbᶻ (B.tw 2)) (baseᴱ 2) (B.tw 1) (P.ink P.self) (baseᴱ 2 (B.tw 1) (P.ink P.self)) (proj₁ (O.upz {s = B.sΩ (B.tw 1)} {h = FR.Step.child 1} B.zero (O.Ωt (FR.Step.child 1 B.zero)))))
```

##### YiS2Shape.chain1-child

```agda
chain1-child : FR.Step.chain 1 1 ≡ proj₁ (T.ψ (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1)) (λ i u → baseᴱ 2 i (P.inc B.zero u)) (B.tw 1) P.self (baseᴱ 2 (B.tw 1) (P.ink P.self)) (proj₁ (O.Ωt (B.tw 1))))
```

##### YiS2Chain.slot-above

```agda
slot-above : proj₁ (O.Ωt (tw 1)) K.⊴ proj₁ βslot
```

##### YiS2Chain.feed-above

```agda
feed-above : ∀ c → proj₁ βslot K.⊴ FR.Step.feed 1 c
```

##### YiS2Chain.actual-above

```agda
actual-above : ∀ n → proj₁ (O.Ωt (tw 1)) K.⊴ FR.Step.chain 1 (suc n)
```

##### YiS2Chain.chain-top

```agda
chain-top : ∀ n → GR.R (tw 1) ΩΩ (FR.Step.chain 1 (suc n))
```

##### YiS2Chain.gamma-bound

```agda
gamma-bound : ∀ n → E.γT ΩΩ [] n ≤ᵀ ΩΩ
```

##### YiS2Chain.actual-chain

```agda
actual-chain : ∀ n → GR.R (tw 1) (E.γT ΩΩ [] n) (FR.Step.chain 1 (suc n))
```

##### YiS2Chain.child-leaf

```agda
child-leaf : ∀ n → GR.R (FR.Step.child 1 (FR.Step.chain 1 (suc n))) (E.Ωt (E.γT ΩΩ [] n))
  (proj₁ (O.Ωt (FR.Step.child 1 (FR.Step.chain 1 (suc n)))))
```

##### YiS2Chain.actual-g

```agda
actual-g : ∀ n → GR.R (tw 2) (E.Ωt (E.γT ΩΩ [] n)) (FR.Step.g 1 (FR.Step.chain 1 (suc n)))
```

##### YiS2Low.hc-row

```agda
  hc-row : ∀ n → E.HC (Keel⁻.row keelᴱ n)
```

##### YiS2Low.value-from-station

```agda
value-from-station : ∀ n → SA.Kᴱ n → Rt (hc-row n) ≼ K.readRW (Keel⁻.twc keelᴱ n)
```

##### YiS2Low.raw-from-station

```agda
raw-from-station : ∀ n → SA.Kᴱ n → K.M⁰ (Keel⁻.row keelᴱ n) (Keel⁻.twc keelᴱ n)
```

##### YiS2Low.station→certificate

```agda
station→certificate : ∀ n → SA.Kᴱ n → Σ (GR.R B.zero (Keel⁻.row keelᴱ n) (Keel⁻.twc keelᴱ n)) H.Exᴴ
```

##### YiS2Low.h2

```agda
h2 : E.HC (Keel⁻.row keelᴱ 2)
```

##### YiS2Low.value2

```agda
value2 : Rt h2 ≼ K.readRW (Keel⁻.twc keelᴱ 2)
```

##### YiS2Low.raw2

```agda
raw2 : K.M⁰ (Keel⁻.row keelᴱ 2) (Keel⁻.twc keelᴱ 2)
```

##### YiS2Low.folded

```agda
folded : GR.R B.zero (Keel⁻.row keelᴱ 2) (Keel⁻.twc keelᴱ 2)
```

##### YiS2Low.ex-folded

```agda
ex-folded : H.Exᴴ folded
```

##### YiS2Low.folded²

```agda
folded² : Σ (GR.R B.zero (Keel⁻.row keelᴱ 2) (Keel⁻.twc keelᴱ 2)) H.Exᴴ
```

##### YiS2Low.low2

```agda
low2 : CN.LowAt 2
```

##### YiS2Accept.k2-from-certificate

```agda
k2-from-certificate : SA.Kᴱ 2
```

##### YiS2Accept.ebo-from-low2

```agda
ebo-from-low2 : (∀ n → C.LowAt (suc (suc n))) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
```

##### YiS2Accept.ebo-from-low3

```agda
ebo-from-low3 : (∀ n → C.LowAt (suc (suc (suc n)))) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
```


#### 5. 第一个障碍与方法对照

原任务的目标已完成，没有剩余的 LowAt 2 障碍。逐链低层保持方法未完成，也没有被否定。

切到现成反射函数前，私有 YiS2Out.agda 已编译 branch0、ex-branch0 与根部分和组装 from-branches；它只作诊断，不进入仓库。第 1 个未填诊断类型是该文件的 FirstOut（只是 Set，不是已经存在的证书）：

    FirstOut = Σ (GR.R zero (E.ψ [] (E.Ωt S1.row1) ∷ [])
      (proj₁ (FR.Step.out 1 (FR.Step.chain 1 2)))) H.Exᴴ

S1.row1 是 ψ₀(Ω₁) 的项；此输出目标是 ψ₀(Ω_{ψ₀(Ω₁)})。实际 chain 1 2 上的 γ 项关系已由 YiS2Chain.actual-chain 1 给出；尚未构造由这份关系沿实际 child/out 折到零层的保持推导。不能把这件未完成的接线写成链关系不存在，也不能说某个 mc 非标准形；本批未找到此类否定。

本批最终低层证书复用语义反射，从已知第 2 站值定理得到原目标的实际构造，故无需以 FirstOut 作为完成原目标的前提。没有把标准 B₀ 链、新链或任意其他对象代入实际 Step.chain/feed/out。

#### 6. 已编译的复用部分与第 3 站的未填目标

station→certificate 已对一般实际站 n 编译：

    station→certificate : ∀ n → SA.Kᴱ n → Σ (GR.R B.zero (Keel⁻.row keelᴱ n) (Keel⁻.twc keelᴱ n)) H.Exᴴ

这条条件定理的量化域是每个实际 row n / twc n，不是任意树、任意底或任意输入关系的保持。HC 的来源也统一为 hc-row n。第 2 站的 folded² 明确等于 station→certificate 2 k2，避免未来复制反射证明。

未知仍是实际第 3 站的值下界 Kᴱ 3；本批未实填它，也未实填从第 3 站起的 LowAt 全族。一般语义反射已经编译，不等于一般 Ω 槽位保持已经证明。

其余方法解释（未新增其一般 n 定理）：slot-above / feed-above 只调用既有 ψ-⊵，actual-above 合成实际底与实际输出的结构下界；复用于更高槽位时，须提供对应基准关系和 γ 的项序证明。raiseR 的现成一般定理给实际孩子 Ω 树的关系，但不提供把这份关系折到第 0 层的保持。本批的实际槽位链结果仍只在第 2 站实填。

没有新增“剩下只有这些方法”的穷尽判断。

#### 7. 偏离、事故与阅读范围

1. 最初第 0 步临时编译退出 42：给 input2 错传了 YiLLCheck.rdΩ（它在 tw 1 上），而实际需要 tw 2 的读法。前面所有参数等式已经检查通过；把实例改为既有 YiCNAccept.rd2 后整个第 0 步编译 0。是调用处域错，不是第 0 步的形状不成立。失败日志之后被同名修正版日志覆盖；失败首错在本线程工具输出可核，最终日志记录修正版 0。
2. 首次文件在启动后数分钟即写出并运行 Agda，满足 30 分钟内首次编译；没有反复两次重新设计同一失败数学步骤，没有 251、124、154，没有加堆。
3. 为遵守全局槽位尝试只读 ps 检查进程，沙箱拒绝；未提权或绕过。全局最多六路由主审协调，本路始终单个 Agda。
4. 初读手册输出发生截断；§4.1–4.5 随后单独读完，§4.6 在冻结前补读至第 394 行。未查 Bedrock 仓库原文，报告也不把该原文当独立证据。
5. 最初按护栏暂不采用已有值界反射；检索发现现成 sem→M⁰ 后立即报告主审；主审澄清并明确要求核验现成桥。保留澄清原文，最终证明如实标记复用 k2 和反射，没有伪装成逐链保持。
6. 首轮冻结后收到主审后续建议，明确授权把现成语义反射组织成实际站条件引理。经临时编译 0，改动仅本批新文件 YiS2Low，重冷编 Low/Accept 并更新冻结；上一版冻结副本与回报另存 frozen-v1/、YiS2-report-v1.txt、SHA256SUMS-v1。未改任何既有仓库文件、其他前缀、src、archive、README、LOG、台账或历史留档；未派子路，未安装包、提交、推送，未用 ignore-interfaces。仅新增四件 YiS2 数学文件和自己的私有材料。
7. 四件文件的禁用构造与本机路径检索命中为 0，文首均不超过 5 行，选项均为规定的 safe/without-K/lossy-unification。审计结果见 source-audit.json。没有对它们宣称记号无关性；它们明确是验收文件，因此未做定义切片或产品导入闭包审计。

已直接核读的数学入口包括：YiS1Shape、YiS1Low、YiS1Exit、YiS1Accept、YiCNKeel、YiCNAccept、YiFRStep、YiFRStations、YiGIRel、YiHCRel、YiHCCheck、YiNLKeel、YiNLRead、YiNLCtx、YiNLRaise、YiNLTop2、YiKCSem、YiGIInst 的实际参数段、YiGIEnd 的行等式段、EboLeanTree 的 HC 与塔标准形段、YiAbsSimInst 的 conv / toL-tree 段。还按签名检索 YiLTKid/YiLTLift/YiPJQ/YiPJLimStep 等供方法判断；没有把其未读依赖当作已独立复核成果。

没有外部文献或外部代码引用。本批不把未走完的逐链方法归到某堵已知墙，不新增路线否定。根审仍须独立冷编、检查陈述与禁用构造后才算主审验收。

#### 8. 冻结

本次版本为一般实际站反射版；仅 YiS2Low 源码相对上一版变更。四件当前源码 SHA256：

7ef846debcbadc54fdfb44b192c2d8cec6cd11738f2186b5a1cb2209efd559f9  probes/OCF/Lean/YiS2Shape.lagda.md
7e352f0188dc7381d0c52e0561811edba827eb452767396aa15f93ccd64904aa  probes/OCF/Lean/YiS2Chain.lagda.md
426dc246377664e1966dcfc3b21f75208a15f0da18689a569b8e1c54ceabf568  probes/OCF/Lean/YiS2Low.lagda.md
0a79d81f3d93dfd24b78b967ee05e2a0c9c7f03d205b6ecec7055f09abe45dca  probes/OCF/Lean/YiS2Accept.lagda.md

SHA256SUMS 文件哈希：1e1e0956590c2fe92e619f0701fa38681e50abc93da40394ddb59608cea66008

冻结副本在 frozen/；源文件与冻结副本字节一致。冷编矩阵见 cold-summary.json；审计见 source-audit.json。前版在 frozen-v1/，旧回报与清单保留。至此再次冻结，停止本路编辑与编译，等待根审。

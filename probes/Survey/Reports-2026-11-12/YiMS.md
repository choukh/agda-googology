# YiMS 实际q2值界与8G停止回报：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiMSShape、Seed、Value、ValueRef |
| 文件前缀 | `YiMS` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiMS 实际q2值界、8G停止与最终复核” 一节 |
| 主审复核后的一句结论 | 4件独立冷编0；实际q2有ψ₀(Ω_Ω+1)下界；后续分支8G退出251按简报停研究，FirstMissing未证，非数学否定。 |

## 简报原文

### 任务简报：攻第 3 站的缺口 FirstMissing（数学，构造）（前缀 YiMS）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十二批三路之一（选项原文 "攻 FirstMissing (Recommended)"），三路都冲着第 3 站的缺口，一路构造、一路否定、一路摆脱侧，在数学上互不依赖。
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
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（另见上面的共同陈述）
- 可用的已有结果（先检索，能复用就复用）：塔第 2 项起的无条件下界 `YiVTTw2Hi.tω≼twᶻ`（≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))）；旧的 K(2) 归约 `YiMTValue.K2-redᶻ`、`YiKQRel`/`YiKQFold`/`YiKQSuff`（`feedΩ`、`Fold.LF²`、`chain`）；读回的下界引理 `YiLSRead`；第 1 站的直接构造 `YiS1Low.folded¹`（做法可照搬）；记号一侧的基本列与共尾 `OCF/Align/EboLeanDef`（`fsT`、`γT`）、`YiCFCofin`。

#### 要做的（按序）
0. **最小检查**，在临时目录：展开 `Step.chain 2 0`、`Step.chain 2 1` 与 `Step.out 2 (Step.chain 2 q)`（q = 0、1）的形状；写出你要比较的那一对（目标项与某个 q 的链点输出），确认 `HC` 证书存在、类型正确。不成立就停下回报。
1. **选 q 并证支配**：对你选的 q，证 `FirstMissing`。可以直接算实际链点的值下界，也可以对这个具体的链点构造关系推导再经出口（照 `YiS1Low` 的做法）；不写全域律。
2. **往 `Tail 2` 推**：`FirstMissing` 成立后，尝试对一切 m 给出 `Tail 2`（下一行第 m+1 项被某个链点支配），从而得到第 3 站的值下界 `Kᴱ 3`；做不到就交第一个挡住的 m 与那一项的展开形式。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiMS`（模块名 `OCF.Lean.YiMS…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiNL`、`YiXV`、`YiFN`、`YiSL`）。验收文件，文首标明。
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

### YiMS 最终回报：8G 停止，原 FirstMissing 未完成

#### 1. 判决与步骤

本路只新增第4层验收文件；树、折叠、合法性和最小比较表均未改变，不报告树自足或终点新增强度。**已触发原停止条件：具体分支重写 YiMSBranchS.agda 在 -M8G 下 Heap exhausted，退出251。按主审确认停止该研究尝试，不加堆、不重跑失败分支；停止后只整理已通过结果、复用同域函数并冷编交付。**

第0步成立，首个临时文件在开始后30分钟内写出并编译。第1步选原实际 q=2，已取得源侧关系证书，以及实际零目标值比较：原 q=2 输出连续取第0分支22次，字面得到 next⁺(betaᴱ3)。故该闭树读回不高于原 q=2 输出；再由第2站实际值下界与零层关系出口，给出固定 q=2 的 **ψ₀(Ω_Ω+1)** 参照下界，闭 HC 实填。这里加1在 Ω_Ω 外面，与 ψ₀(Ω_{Ω+1}) 不是同一项。

**原 YiFRStep.FirstMissing 仍未实填，Tail 2、Kᴱ3 未进入。ψ₀(Ω_Ω+1) 是本具体链点的局部界，不作为终点新增强度。源侧 R 证书与零层值结论分开报告。8G 耗尽不是数学否定，本路没有 ¬FirstMissing 或对所有 q 的上界。**

具体尝试按原顺序如下：

1. YiMS0.agda 编译0：实际 chain 2 的第0、1点、out的q=0/1形状、原目标HC与原比较类型成立；Shape 为正式保留版。目标展开是 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})。
2. 对原 q=2 实填 seed/Ωseed/source；它们只是源关系，未冒充值。随后按主审要求继续具体值，未转一般保持接口。
3. YiMSValue0、YiMSNextRef 临时文件均编译0：选定字面的22次第0分支，并经实际 betaᴱ3 的第2站界得到 ψ₀(Ω_Ω+1) 参照；正式为 Value/ValueRef。
4. 再试将第21次第0分支处的源 Ω 结点改选分支1。首次把该源层猜为 tw1，YiMSBranch1.last-level 编译报 sS != sΩ(tw0)，这是具体形状错误。随即按检查器显示的实际后继层重写 YiMSBranchS，试 ψ₀(Ω_Ω+2) 的局部值链；整件耗尽8G，未计为结果，触发停止。

| 问题 | 位置 | 档 |
|---|---|---|
| 原目标HC、q=1/2比较类型、实际链/输出展开 | YiMSShape | 编译定理；Pair/Pair2仅类型、未实填 |
| 原q=2链点上的γ₁及Ω_{γ₁}关系，实际孩子Ω树的源关系 | YiMSSeed | 编译证书，未自行提供零层值出口 |
| 原q=2输出的22次第0分支恰为next⁺ betaᴱ3 | YiMSValue.point-form | 编译等式，具体点 |
| next⁺ betaᴱ3读回不高于原q=2输出 | YiMSValue.value-next | 编译值定理 |
| ψ₀(Ω_Ω+1)参照不高于原q=2输出，HC闭项存在 | YiMSValueRef.bound/hNext | 编译值定理 |
| 修改为实际后继层后，所选分支1是否给ψ₀(Ω_Ω+2) | 临时YiMSBranchS | 未完成；251堆耗尽，不是类型或数学否定 |
| 原FirstMissing的q=2具体分量 | YiFRStep/Shape.Pair2 | 未走通；没有否定 |
| Tail2及Kᴱ3 | 原Step2 | 未开始，未越过原顺序 |

#### 2. 文件、冷编与资源

代码行口径为agda代码块全部行（包括空行）；另列非空。只删自己的字面接口，未ignore-interfaces，未删依赖接口。均从仓库根用 +RTS -M8G -s -RTS 顺序编译。每份冷编日志仅有自己模块的一条Checking。

| 文件 | 代码行/非空 | 全文行 | 冷编码 | max residency(bytes) | total memory(MiB) | elapsed(s) |
|---|---:|---:|---:|---:|---:|---:|
| probes/OCF/Lean/YiMSShape.lagda.md | 69/66 | 75 | 0 | 5,395,216,176 | 8298 | 127.495 |
| probes/OCF/Lean/YiMSSeed.lagda.md | 45/44 | 51 | 0 | 3,225,061,792 | 5638 | 43.362 |
| probes/OCF/Lean/YiMSValue.lagda.md | 33/32 | 39 | 0 | 1,565,558,408 | 2696 | 17.587 |
| probes/OCF/Lean/YiMSValueRef.lagda.md | 41/41 | 47 | 0 | 1,590,128,384 | 2658 | 16.268 |

合计188代码行、183非空代码行；全部为验收，不纳入成品树定义。源头的Shape/Seed在阶段冻结后没有修改，原哈希保持。

冷编日志分别为 YiMSShape-cold.log、YiMSSeed-cold.log、YiMSValue-cold.log、YiMSValueRef-cold.log，退出码见同名.exit；RTS全量保存在各log。审计细项在audit.json。

失败重写：YiMSBranchS.agda，退出251；RTS堆上限8,589,934,592 bytes，max residency 8,434,050,400 bytes，elapsed 139.563s。完整源码、YiMSBranchS.log、YiMSBranchS.exit、failure.json原样保存。没有调大堆或重跑它。

#### 3. 定理表与逐字陈述

Shape里 k=B.tw2、ell=B.tw3，CF c为原实际child c上的Ω树折叠，底是baseᴱ3沿inc c的限制。Seed里γ=E.EBOψ2=ψ₀(Ω_Ω)，base=baseᴱ3(tw2)(ink self)。Value里c₂=原Step.chain2 2，β=betaᴱ3，out=proj₁(原Step.out2 c₂)；tNext=ψ₀(Ω_Ω+1)。这些都是原闭项的简写。

| 定理或类型 | 白话 | 文件 | 档 |
|---|---|---|---|
| chain0/chain1/chain1-root/chain2-form | 原实际链前3点及Ω/Up形状 | Shape | 编译等式 |
| feed-form/out-form/out0/out1 | 不换底、不换起点地展开原Step2 | Shape | 编译等式 |
| target-hc/target-form | 原待比较项有闭HC，并精确展开参数 | Shape | 编译定理 |
| Pair/Pair2 | 原FirstMissing在q1/q2的比较类型 | Shape | 类型已检查、未实填 |
| base-above/chain-above、seed/Ωseed/source | 实际q2的源关系证书 | Seed | 编译证书，不等于值定理 |
| γ-bound/Ωγ-bound/γ-ref | 源证书的记号比较与原γ₁接线 | Seed | 编译定理 |
| first≤/follow≤ | 读取有限个第0分支不会升高零层值 | Value | 编译值定理 |
| point-form/value-next | 实际22次路径取得next⁺β，并给原输出下界 | Value | 编译等式/值定理 |
| β-lower/mβ/mNext | 由实际第2站值经sem→M⁰和next进入已知零层出口 | ValueRef | 编译定理 |
| bound/nfNext/hNext | 固定原q2的ψ₀(Ω_Ω+1)下界，NF与闭HC均实填 | ValueRef | 编译定理 |

first是现有YiS1Shape.branch0的重命名，不再另定义；follow用现有YiRWOps.iter，不另写迭代。其余值读取引理未发现同域现成版本；YiIntoTw3.desc≼处理旧St/Ψ类型，不用于本处。

##### YiMSShape.chain0

```agda
chain0 : S.Step.chain 2 0 ≡ B.zero
```

##### YiMSShape.chain1

```agda
chain1 : S.Step.chain 2 1 ≡ proj₁ (CF B.zero k P.self (baseᴱ 3 k (P.ink P.self)))
```

##### YiMSShape.feed-form

```agda
feed-form : ∀ c → S.Step.feed 2 c ≡ proj₁ (CF c k (P.self P.∙ P.lift k (B.↑ k c)) (baseᴱ 3 k (P.ink P.self)))
```

##### YiMSShape.out-form

```agda
out-form : ∀ c → S.Step.out 2 c ≡ CF c B.zero (P.z≤ (child c)) (betaᴱ 3)
```

##### YiMSShape.out0

```agda
out0 : S.Step.out 2 (S.Step.chain 2 0) ≡ CF B.zero B.zero (P.z≤ k) (betaᴱ 3)
```

##### YiMSShape.out1

```agda
out1 : S.Step.out 2 (S.Step.chain 2 1) ≡ CF (proj₁ (CF B.zero k P.self (baseᴱ 3 k (P.ink P.self)))) B.zero (P.z≤ (child (S.Step.chain 2 1))) (betaᴱ 3)
```

##### YiMSShape.target-hc

```agda
target-hc : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1)
```

##### YiMSShape.target-form

```agda
target-form : E.fsn (Keel⁻.row keelᴱ 3) 1 ≡ E.ψ [] (E.Ωt (E.Ωt (E.EBOψ 2))) ∷ []
```

##### YiMSShape.chain1-root

```agda
chain1-root : S.Step.chain 2 1 ≡ B.Ω (inj₁ (inj₁ tt))
(λ c → proj₁ (O.Up (S.Step.child 1 c) (O.down O.stop c)
(baseᴱ 3 k (P.ink P.self)) (proj₁ (O.Ωt (S.Step.child 1 c)))))
```

##### YiMSShape.chain2-form

```agda
chain2-form : S.Step.chain 2 2 ≡ proj₁ (CF (S.Step.chain 2 1) k
(P.self P.∙ P.lift k (B.↑ k (S.Step.chain 2 1))) (baseᴱ 3 k (P.ink P.self)))
```

##### YiMSShape.Pair

```agda
Pair : Set
```

##### YiMSShape.Pair2

```agda
Pair2 : Set
```

##### YiMSSeed.base-above

```agda
base-above : proj₁ (O.Ωt k) ⊴ proj₁ base
```

##### YiMSSeed.chain-above

```agda
chain-above : proj₁ base ⊴ S.Step.chain 2 2
```

##### YiMSSeed.γ-bound

```agda
γ-bound : γ E.<ᵀ E.Ωt (NL.κ 2)
```

##### YiMSSeed.seed

```agda
seed : GR.R k γ (S.Step.chain 2 2)
```

##### YiMSSeed.Ωγ-bound

```agda
Ωγ-bound : E.Ωt γ E.<ᵀ E.Ωt (NL.κ 2)
```

##### YiMSSeed.Ωseed

```agda
Ωseed : GR.R k (E.Ωt γ) (S.Step.chain 2 2)
```

##### YiMSSeed.source

```agda
source : GR.R (S.Step.child 2 (S.Step.chain 2 2)) (E.Ωt (E.Ωt γ)) (proj₁ (O.Ωt (S.Step.child 2 (S.Step.chain 2 2))))
```

##### YiMSSeed.γ-ref

```agda
γ-ref : E.γT (E.ΩTower 3) [] 1 ≡ γ
```

##### YiMSValue.first≤

```agda
first≤ : ∀ x → K.readRW (first x) ≼ K.readRW x
```

##### YiMSValue.follow

```agda
follow : ℕ → B.Tr B.zero → B.Tr B.zero
```

##### YiMSValue.follow≤

```agda
follow≤ : ∀ n x → K.readRW (follow n x) ≼ K.readRW x
```

##### YiMSValue.point-form

```agda
point-form : follow 22 out ≡ proj₁ (O.next⁺ β)
```

##### YiMSValue.value-next

```agda
value-next : K.readRW (proj₁ (O.next⁺ β)) ≼ K.readRW out
```

##### YiMSValueRef.β-lower

```agda
β-lower : (h : E.HC (E.EBOψ 2)) → R2.Rt h ≼ K.readRW (proj₁ β)
```

##### YiMSValueRef.mβ

```agda
mβ : K.M⁰ (E.EBOψ 2) (proj₁ β)
```

##### YiMSValueRef.mNext

```agda
mNext : K.M⁰ tNext (proj₁ (O.next⁺ β))
```

##### YiMSValueRef.bound

```agda
bound : (h : SI.E.HC tNext) → SI.E.tree h ≼ K.readRW out
```

##### YiMSValueRef.GNext

```agda
GNext : GB [] (E.sucT (E.ΩTower 2)) (E.sucT (E.ΩTower 2))
```

##### YiMSValueRef.nfNext

```agda
nfNext : NF tNext
```

##### YiMSValueRef.hNext

```agda
hNext : SI.E.HC tNext
```

#### 4. 首个余项及停止点

原目标仍是下面这个同一实际q=2分量：

```agda
(h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
→ SI.E.tree h ≼ K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 2)))
```

它的左项是ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})。本次通过的局部参照仅为ψ₀(Ω_Ω+1)；没有把其下界当实际输出的上界，也没有由这点比较否定目标。

后续具体方法的余项在私有YiMSBranchS：把原输出连续取第0分支21次到实际后继层world，选该Ω结点的回灌分支1；该分支应为next⁺ Z，其中Z是该实际孩子W上、原betaᴱ3起点、继承限制底下对实际第1内链点的零目标折叠。候选值链定位在child-point、Z-value、mrow1及bound（拟达ψ₀(Ω_Ω+2)）。整件251，**这些声明均未被本回报计作编译定理**。堆耗尽日志没有声明位置，无法从现有日志断言耗尽发生在其中哪一条；未再运行定位或重写。最早有明确位置的类型错误是上一设计YiMSBranch1.last-level第28行的源层形状错误，该假设已放下。

即使该较小参照界日后通过，也不等于原FirstMissing。此处只交精确余项和已通过值结论；未进入Tail2，不提出“只剩这些方法”的穷尽判断，未关闭路线。

#### 5. 纪律、事故及引用范围

- 只新建YiMSShape/Seed/Value/ValueRef及私有临时文件。没有改既有数学、src、archive、其他前缀、README/LOG/台账，没有提交/推送/安装/派子路。
- Shape/Seed阶段冻结后保持源码和哈希；新值两件已依主审要求复用branch0与iter，并各自冷编0。四件禁用构造与本机路径检索均0。没有Funext前提。
- 最早YiMS0临时文件有作用域与限定mixfix括号错误，修正后0；前两次同名日志曾被覆盖，已存的最早失败为YiMS0-r3.log。此类错误不是数学否定。
- YiMSDepth是故意失败的归约诊断，显示depth ℓ=22（42）；随后正式文件以字面22编译0。它不作为否定定理。
- YiMSBranch1在猜测源层tw1处42，日志显示实际sS。按实际sS重写的BranchS在8G下251，触发停止。这不是“证明ψ₀(Ω_Ω+2)失败”的数学结论，更不是原FirstMissing的否定。
- 停止后未再研究、加堆或重跑BranchS；后续只是按主审授权将已经通过的Value0/NextRef正式化、合并现有同域分支函数、冷编与审计。
- 已完整读原简报、护栏、AGENTS和手册§4。数学源文件按相关签名、定义及所用证明段落读取，不声称通读整个导入闭包。新增定义只在验收侧，未作记号无关性声称。
- 证明引用源码：YiFRStep/FRStations/GIInst、YiExInst、YiRefTw2、YiAbsSimInst、YiTBFam、YiKCStep、YiLLCheck、YiNLCanonical、YiNLRaise、YiS1Shape、YiKVRel、YiKCSem、EboLeanBase/Tree/3Base相关定义；相关段落已读。mβ使用现有k2、sem→M⁰，mNext使用现有m-next与lower⁰，没有重写这类出口。
- 收到YiFN已编译目标路径/目标下界等信息，未根审，本路没有导入或用其作证明前提。SL仅n1/q1的out11范围已由主审明确，未用于n2/q2。主审最终通讯确认：四件正式源码已全文读取、独立只读核查并逐件冷编0；Shape/Seed为8G，Value/ValueRef为5G，总200.90秒，峰值5,395,216,480 bytes，同口径183非空代码行，四哈希一致。该段为主审通讯留档；本路自冷编日志与统计仍独立列于第2节。此后本路未再编任何文件。
- 新候选供台账：实际22次分支路径的值模拟（已编）；实际后继层分支1的下一参照界（8G未完成，暂停，不否定）。不要求改树、折叠或合法性。

#### 6. 冻结与材料

四件正式文件哈希在SHA256SUMS.txt；冷编0后未再更改，主审已确认独立复核与哈希一致。所有私有源码、诊断、通过/失败日志、退出码、RTS、原简报与护栏副本的哈希在PRIVATE-SHA256SUMS.txt。旧阶段回报在YiMS-report-phase1.md；以本回报为本轮最终状态。

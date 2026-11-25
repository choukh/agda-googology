# YiTC 槽位值计数化候选与旧Can字段否定：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiTCValue、YiTCControlNeg |
| 文件前缀 | `YiTC` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiTC 合法候选、旧Can字段否定与未证值桥复核” 一节 |
| 主审复核后的一句结论 | 两件独立冷编0、完整闭包与编译器图吻合；候选合法，旧Can在实际对照对象上否定；ChildLow₁未证，第3站/Nchild未开，未否定路线。 |

## 简报原文

### 任务简报：摆脱侧：同一步的树侧对应（前缀 YiTC）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十五批四路之一（选项原文 "摆脱侧：同一步的树侧对应 (Recommended)"）。四路都冲着第 3 站的那一条不等式：一路判定上界、一路构造、一路摆脱侧、一路纸面审计，在数学上互不依赖。
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
- AGENTS 目标 "让树自足"、"攀爬与摆脱翻译要平衡"（1:1）。本路是本批的摆脱侧。
- **上一路（YiSL）**：`YiSLStart`（不读记号地重建实际的底、起点与槽位链，`growth0`：全部站上链的第 0 到第 1 点的第一位置步进，`point-base`、`out-base`）、`YiSLOut.out11`（第 1 个链点的第 0 层输出不高于该链点在槽位层上的树侧值）、`YiSLCheck`（与原定义逐字相等）；第 1 到第 2 个链点的一步与末端记号引理 `Nslot` 未做（回报 `probes/Survey/Reports-2026-11-12/YiSL.md`）。
- 新块上的树侧值：`YiVWVal.val`（各层的值，不读记号）、`V.≼`、`V.◁`。

#### 要做的（按序）
0. **最小检查**，在临时目录：在第 2 站（n = 1，值已知）上写出一条不读记号的陈述，把 "Ω 形状孩子层号上的 Ω 树折到第 0 层的树侧值" 与 "该孩子（槽位层上的链点）的树侧值" 联系起来（形如 `val zero (折叠输出) ` 不低于某个由 `val (tw n) c` 构造的树侧值）；编译它。不成立就停下回报。
1. **第 3 站**（n = 2，c₁ = `Step.chain 2 1`）：只在树侧证同一条陈述。
2. **末端的一条记号引理** `Nchild`：精确写出把树侧值对到参照所需的那一条，编译 "`Nchild` 加树侧陈述 ⇒ `missing-child-low₁`"；在第 2 站上检查 `Nchild` 的实例，作为对照。
3. 交翻译账：树侧陈述用到树的哪些构造与字段，`Nchild` 读了记号的哪些东西。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiTC`（模块名 `OCF.Lean.YiTC…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiUP`、`YiCK`、`YiPA`）。树侧的文件若不读记号，文首标明 "不读记号"，用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包；读记号的文件标明 "验收文件"。
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

### YiTC 回报：第 0 步未走通

#### 1. 判决与范围

对纲领与目标：本轮给出一个不读记号的合法计数化候选，以及关于原第 2 站实际对象的一个旧接口字段否定。没有改树、折叠、比较表、合法性、实际终点继承底或起点。没有新增序数值下界，没有证明树自足。

**原第 0 步未完成。** 候选和前提的实际实例能通过检查器，候选值与原实际输出之间的 `ChildLow₁` 未证、也未否定。没有把合法闭项当成值比较，没有把已有 `out11` 反向界、继承底界或展开等式当作原第 0 步。

第 1 步（第 3 站、原 `Step.chain 2 1`）与第 2 步（`Nchild` 的条件、目标接线、第 2 站实例）均未开。没有改写 `missing-child-low₁` 或 `FirstMissing`。

本回报按 AGENTS“连续受阻时停下来报告是允许的，那不等于否定路线”的范围交精确余项；**不声称触发“第 0 步整体不成立”，不声称已有两次不同数学设计均被否定，也不声称发生了退出码 251 的堆耗尽。** 本轮未走通，YiTC 原路线没有被否定。

| 问题 | 位置 | 档与状态 |
|---|---|---|
| 从合法槽位值构造一个合法零层候选 | `YiTCValue.collapseᵛ`、`candidate₁` | 编译构造；前提实际实例已填 |
| 第 2 站候选值不高于原实际输出 | `YiTCValue.ChildLow₁` | 未证、未否定；第 0 步未通过 |
| 原实际孩子上的 Ω 树满足旧 `Can` | `YiTCControlNeg.no-sourceCan` | 编译否定，仅限这个字段 |
| 候选层号与原孩子层号可用 `refl` 接上 | 临时 `YiTCLiteral.literal` | 检查器报 42；诊断，不是值否定 |
| 第 3 站与末端 `Nchild` | 原简报第 1、2 步 | 未开，不以条件接口冒充已填实例 |

本轮没有有限序数值测试结果。临时文件成功检查的“前提有实例”属于合法构造检查，不是序数强度比较。

#### 2. 文件、冷编与审计

代码行口径：代码围栏内含空行；另列非空代码行。冷编删除各自的字面接口路径，依赖保持已有接口；每次同时仅一个 Agda，均 `-M8G -s`。

| 文件（均位于 `probes/OCF/Lean/`） | 代码行 / 非空 | 冷编退出码 | RTS 最大驻留 bytes | RTS 总内存 MiB |
|---|---:|---:|---:|---:|
| `YiTCValue.lagda.md` | 53 / 43 | 0 | 154700048 | 266 |
| `YiTCControlNeg.lagda.md` | 29 / 25 | 0 | 169786944 | 282 |

两份冷编日志均只有本模块的一行 `Checking`，没有依赖模块的 `Checking`。未使用 `--ignore-interfaces`。

完整导入闭包（没有 `--only` 过滤）：

- `YiTCValue`：脚本闭包 17 模块，本地 9；禁用表命中 0。
- `YiTCControlNeg`：脚本闭包 18 模块，本地 10；禁用表命中 0。
- Agda `--dependency-graph` 的本地模块集合分别为 9、10，与脚本逐项相同；本地模块全部是 `OCF.Lean.YiRW*`、`YiTBRow`、`YiMTTab`、`YiVWVal`、`YiSLStart`、本路模块，否定件另含 `YiVRRel`。
- 两份仓库文件禁项检查 0、本机路径检查 0。没有公设、洞、停机/正性跳过、K、函数外延前提、`--irrelevant-projections` 或 `--cubical`。
- 没有生成 HTML 或定义级切片；不把导入闭包检查写成定义级切片结果。

冻结源码 SHA256：

```
350907e0a951b499017c442dedbf6da7d67b66e0f8451cc42605b5e7e2ec4407  probes/OCF/Lean/YiTCValue.lagda.md
2b18088c41c586d9992a994d17f64a912e50bb0cdc908f93729d65c7faf6dfbd  probes/OCF/Lean/YiTCControlNeg.lagda.md
```

#### 3. 公开构造与定理的逐字陈述

以下代码均在源文件所示导入上下文中。`V` 是 `YiVWVal`，即各层的树侧值；`S` 是不读记号地重建原实际对象的 `YiSLStart`。

##### YiTCValue

`↑ᵛ` 只读值的四种构造；`childᵛ k v = k ⊕ ↑ᵛ k v`。它们是候选定义，不附带序数值保持结论。

```agda
↑ᵛ : (k : L) → V.V k → L

◁→⊑ᵛ : (k : L) {x y : V.V k} → x V.◁ y → ↑ᵛ k x ⊑ ↑ᵛ k y

OkOᵛ : (a k : L) → Ok k → k ≤ a → (v : V.V k) → V.LegV k v → OkO a (↑ᵛ k v)

childᵛ : (k : L) → V.V k → L

ok-childᵛ : (k : L) → Ok k → (v : V.V k) → V.LegV k v → Ok (childᵛ k v)

collapseᵛ : (k : L) → Ok k → (v : V.V k) → V.LegV k v → Tr⁺ zero

v₁ : V.V (tw 1)
v₁ = V.val (tw 1) (S.Step.chain 1 1)

hv₁ : V.LegV (tw 1) v₁

candidate₁ : Tr⁺ zero
candidate₁ = collapseᵛ (tw 1) (Ok-tw 1) v₁ hv₁
```

白话与档：`◁→⊑ᵛ` 把值的第一位置步进转成读回层号上的路径；`OkOᵛ`、`ok-childᵛ` 证明读值构造的层号合法；`collapseᵛ` 使用该合法性、默认底、原 `YiTBRow.ψ` 与原 `rbᶻ` 构造零层非零树；`hv₁` 实填原第 2 站槽位点的前提，`candidate₁` 是合法闭项。这些全部已编译；**没有给出 `candidate₁` 的序数值下界或上界。**

实际使用的折叠定义逐字为：

```agda
collapseᵛ k o v hv = ψ (childᵛ k v) (ok-childᵛ k o v hv) (rbᶻ (childᵛ k v))
  (B₀ (childᵛ k v)) zero (z≤ (childᵛ k v)) (Ωt zero) (proj₁ (Ωt (childᵛ k v)))
```

这里默认底只用于新候选；比较右端始终是原实际继承底与起点上的 `S.Step.out 1 (S.Step.chain 1 1)`，没有用默认底替换右端。

##### YiTCControlNeg

`R` 是旧树侧关系 `YiVRRel`。公开定理逐字为：

```agda
no-sourceCan : R.Can (S.Step.child 1 (S.Step.chain 1 1))
  (proj₁ (Ωt (S.Step.child 1 (S.Step.chain 1 1)))) → ⊥
```

白话与档：原第 2 站实际孩子上的 Ω 树不满足旧关系的自相关字段 `Can`；编译定理。原对象本身合法，因为 `Ωt` 给出 `Tr⁺`。否定的是这个额外谓词，不是对象合法性，更不是它折到零层的值。

证明来源是 `YiVRRel.β-not` 的两个不同孩子机制。原 `β-not` 只对 `tw 1`、孩子函数 `zero ⊕ ↑ zero c` 陈述；此处层号是 `S.Step.child 1 (S.Step.chain 1 1)`，孩子函数来自原实际 `Up` 与 `S.baseᴱ 2`，二者不是相同对象。私有小辅助把孩子函数当参数，最后只实填原实际对象；没有修改旧接口。

陈述内没有折叠、没有 `V.val`、没有零层值比较，因此不把它归成折叠值障碍或已知某堵墙。旧 `YiVRFold` 的折叠还是 `YiRWFold`，不能把这个前提检查写成主线 `YiTBRow` 的完整保持或否定。

#### 4. 第一个障碍与尝试范围

首个未证引理精确为 `YiTCValue.ChildLow₁`：

```agda
ChildLow₁ : Set
ChildLow₁ = V.val zero (proj₁ candidate₁) V.≼ V.val zero (proj₁ (S.Step.out 1 (S.Step.chain 1 1)))
```

它的左端确由原 `val (tw 1) c₁` 经 `↑ᵛ`、合法性证书和原折叠构造。右端确为原实际输出。没有填这个类型的项，也没有填其否定。

- 直接传输尝试：检查 `childᵛ (tw 1) v₁ ≡ S.Step.child 1 (S.Step.chain 1 1)` 能否 `refl`。临时 `YiTCLiteral` 退出 42，首个差异是 `↑ᵛ (tw 1) (V.val (tw 1) (proj₁ (Up …)))` 对原 `↑ (tw 1) (proj₁ (Up …))`。这只否定本次逐字接线，不否定层号的序数值相等或目标值比较。
- 旧关系保持尝试：先查 `Can` 在原实际源 Ω 树上的实例，得到上述编译否定。没有从“关系不容纳该对象”推出实际值比较不成立，也没有重写成对一切合法树的保持律。
- 没有把这些诊断强算成“原第 0 步整体不成立”或“两次不同数学候选已否定”。没有穷尽路线的判断。

#### 5. 翻译账、候选想法与事故

翻译账：

1. `↑ᵛ` 的零、后继、ℕ 极限、Ω 四行取自树侧值的构造，形式参照原树读回 `↑`；Ω 用树自己的 `at`、`fromBr` 和原低层树坐标。
2. 合法性用值的第一位置步进、字面路径、原 `Ok`/`OkO`/`Ok⊕`；没有比较裸层号，没有加入派发证据、记号标签或专属合法性字段。
3. 计数化候选仍调用原折叠与最小比较表，并非本轮建立了折叠的值理论。它是新候选闭项，没有与原实际输出的已证比较，不能写成树自足或站值推进。
4. `Nchild` 尚未定义，因而本轮没有可列的 `Nchild` 条件、实例、接线或记号依赖账。没有读任何新记号结构来调整前三层；没有“第 4 层逼出”的定义改动。

供主审记台账的候选与纸面想法（除已明确编译部分外均为判断，未否定路线）：

- 恒等/扩张的槽位值下界：在临时文件确认不适用于这个原第 2 站点；`no-direct` 只留作私有诊断，不进仓库、不计正式成果。其证明复制了 `YiSLOut` 私有的 `under-c1` 并注明来源，主审指出可见性后没有正式保留重复证明。
- 从 `LegV` 把裸值重建成原 `Tr` 再回灌：纸面检查发现需要处理限值步进证书与对象第一位置的接线；本轮未实现，不声称重建不可能。
- 从值直接读出层号再默认折叠：已交 `YiTCValue`；合法构造通过，实际比较未走通。
- 以逐点关系代替读值层号与原层号的字面等式，证明原实际对象的跨层模拟：纸面候选，未实现；没有扩成全域保持律。
- 值上直接定义计数化回灌，把零层输出送回低层坐标：纸面候选，未实现；涉及原 `Tr` 坐标的合法重建及证明参数接线，没有把该工程缺口说成否定。
- 取第一分支或自然数坐标形成计数化投影：纸面候选，未实现；没有实例或值比较，不能凭读法关闭。
- 直接以继承底作为下界，或由已知站值抽取某个链点：未采用为第 0 步。它们没有交出指定槽位值构造与指定实际点的所求比较；不能用改变见证对象来完成原题。

编译/工程记录（全部日志在本实验目录）：

| 文件/运行 | 退出码 | 说明 |
|---|---:|---|
| `YiTCPre.agda` | 0 | 首文件；实际值合法与已有反向界，约开始后十余分钟内完成检查，不算第 0 步 |
| `YiTCZero.agda` | 0 | 私有 `no-direct` 诊断；不作正式交付定理 |
| `YiTCValue.agda` | 0 | 候选合法性与实际前提实例 |
| `YiTCLiteral.agda` | 42 | 逐字传输失败；非值否定 |
| `YiTCPrivate.agda` | 42 | `YiSLOut.under-c1` 的限定名不可见；主审也确认其位于 private |
| `YiTCCan.agda` | 130 | 在巨项上 with；本路自行中断，约 291 秒，最大驻留 8012851688 bytes，日志无 Heap exhausted |
| `YiTCCan2-scope.log` | 42 | 首次辅助版把投影的限定名写错；改为 `proj₂`，属作用域修正 |
| `YiTCCan2.agda` 修正后 | 0 | 抽出孩子函数及小辅助，不在巨项上 with；最大驻留 150106008 bytes |
| 两份仓库文件首次编译、各自删接口冷编 | 全部 0 | 见第 2 节与冷编日志 |

第一版 Can 的中断：`lsof` 仅查持有本路私有日志的 Agda PID；普通沙盒的 `kill -INT` 被拒，随后仅对同一本路 PID 的提权 SIGINT 获准并成功。没有 `pkill`，没有停止他路。该运行是 130，不是 251 或 124；没有擅自加大堆。

没有修改旧文件、导航、台账、他路前缀、src 或 archive；没有安装、提交、推送、开子路，也没有导入并行 YiXV 的任何文件。只删除了本路两份字面接口。两份新数学文件均文首不超过五行，没有本机路径。

阅读范围：完整读了 AGENTS、原简报、batch55 护栏、手册第 4 节，以及 `YiSLStart`、`YiSLOut`、`YiSLCheck`、`YiVWVal`、`YiFRStep`、`YiRWBlock`、`YiRWOps`、`YiMTTab`、`YiTBRow` 等直接使用的定义；其他旧接口按签名与相关证明段检索。没有独立冷编全部旧模块。原简报关于 YiLB/YiMS 的既有值界与各否定只作背景，没有独立验收后再当本轮证明使用；没有引用或复核并行他路的新结果，没有外部文献或浏览资料。

# YiFN FirstMissing配对否定：未判定：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiFNTarget、YiFNUpper |
| 文件前缀 | `YiFN` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiFN 目标下界与实际链点相对值界复核” 一节 |
| 主审复核后的一句结论 | 两件独立冷编0；目标下界和实际输出相对严格界已证，FirstMissing未判定，后支错位步骤未进入。 |

## 简报原文

### 任务简报：配对否定：检查 FirstMissing 会不会为假（数学，否定）（前缀 YiFN）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十二批三路之一（选项原文 "配对否定：检查 FirstMissing 会不会为假 (Recommended)"），三路都冲着第 3 站的缺口，一路构造、一路否定、一路摆脱侧，在数学上互不依赖。
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
- AGENTS："律带公共上界, 构造与否定配对"；"否定路线要有依据"（判定走不通必须有编译过的否定定理）；"第 4 层不反过来改前 3 层"（若发现非改定义不可，停下交作者）。并行的 YiMS 在构造方向攻同一条。
- 上界工具（先检索，能复用就复用）：`YiCeilRead`（第 0 层读回的上界、部分和吸收）、`YiCeilWit`、`YiCeilSmall`、`YiUB*`；在跑的 YiXV 有大量上界框架（`YiXV*`，主线之外，可只读其已编译的结论，不改它的文件）。

#### 要做的（按序）
0. **最小检查**，在临时目录：对 q = 0、1、2 给出 `readRW (proj₁ (Step.out 2 (Step.chain 2 q)))` 的上界（编译），并写出目标项 `E.fsn (row 3) 1` 的参照值的下界；看两者的大小关系是否已能判定。
1. **对一切 q 的上界**：若小 q 上链点输出都低于目标项，证对一切 q 的统一上界，编译 `¬FirstMissing`（`FirstMissing → ⊥`）。若某个 q 已经高于目标项，交那个 q 的编译事实（这是给 YiMS 的正面信息），停下。
2. **若得到否定**：再检查错位的配对是否还成立：第 3 站的参照是否被后面某一支（第 m 支，m > 3）支配。终点只要 "每个参照都被某一支支配"，不必逐站对齐；把这条较弱的形式写成陈述，检查它在第 3 站上会不会也被否定。若错位也被否定，说明主线闭项在这一站弱于参照，是定义层面的问题：写成编译定理后停下，交作者，不改定义。
3. 判定不了时只写 "未判定"，交两侧的界各到哪里。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiFN`（模块名 `OCF.Lean.YiFN…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiNL`、`YiXV`、`YiMS`、`YiSL`）。验收文件，文首标明。
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

### YiFN 完整回报：原 FirstMissing 未判定

执行范围：原简报 YiFN 与 batch52-guardrails，按第 0 → 1 → 条件第 2 → 第 3 步的顺序；只新建 YiFN 两个验收模块与本私有目录文件。未修改原 FirstMissing、Step 2 的实际 baseᴱ/betaᴱ/chain/out、树、折叠、表或合法性。

#### 1. 判决与问题表

对纲领与目标的意义：本路没有证明主线掉值，也没有证明 FirstMissing。没有触发改定义或后支错位的条件。新增结果只约束原目标与实际输出：目标的参照值不低于 ψ₀(Ω_{Ω_ω})，也不低于 ψ₀(Ω_{Ω+1})；实际第 0 个输出严格高于实际第 2 支，全部实际输出严格低于实际第 3 支。这里关于输出的上界是实际树的相对界，不是独立的记号强度上界。

第 0 步：`YiFNCheck0.agda` 在 03:16:56 UTC 首次整体退出 0；开工读取完整简报与约束后约 6 分钟，满足首次 30 分钟内编译。它给 q = 0、1、2 的实际输出各一个上界（实际 twc 3），以及目标到 ψ₀(Ω_Ω) 的下界。之后正式模块把目标下界提高到 ψ₀(Ω_{Ω_ω})，并把各输出的相对上界提高为带一个后继的界。

第 1 步：没有证明小 q 的输出低于原目标，也没有找到某个 q 支配原目标；因此没有把有限小例推广为 `¬FirstMissing`。独立的记号上界仍未填。

第 2 步：没有得到 `¬FirstMissing`，按原简报条件没有进入错位覆盖检查；未对后支覆盖作正面或负面判断。

第 3 步：交付“未判定”，两侧的界见以下表与逐字陈述。未宣布任何数学路线关闭。

| 问题 | 位置 | 档与状态 |
|---|---|---|
| 原 `YiFRStep.FirstMissing` | 原文件末尾，未改 | 未判定 |
| q = 0、1、2 的上界 | `YiFNUpper.upper0/1/2` | 编译定理；只到实际 twc 3 |
| 所有实际链点的相对上界 | `YiFNUpper.strict-upper` | 编译定理；suc(out q) ≼ twc 3 |
| 目标的两侧中下界一侧 | `YiFNTarget.lower`、`lower-plus` | 编译定理；ψ₀(Ω_{Ω_ω}) 与 ψ₀(Ω_{Ω+1}) 的参照不高于目标 |
| 实际 q = 0 能否由实际 twc 2 给上界 | `YiFNUpper.not-prior-upper` | 编译否定；不能。不是 FirstMissing 的否定 |
| 旧块桥能否直接用于实际 out0 的输入层 | 临时 `YiFNBridgeCheck.no-NoΩ-tw2`；所读桥为 `YiMTRel.A/S` | 编译否定该桥的 NoΩ 前提；不否定上界策略 |
| 可分离的独立记号上界 | `YiFNUpper.out0` 右侧的实际第 2 层折叠起 | 未得到；不能用当前已知低下界充当它 |
| 后支错位覆盖 | 未进入第 2 步 | 未检查、未否定 |

#### 2. 文件与冷编

代码行口径：Agda 代码块里的非空、非整行注释行，含选项、模块头与导入。只删自己模块接口，依赖保持热；两次冷编日志的 Checking 都只有自己模块一行。每次 Agda 都单进程且带 -M8G；没有提高堆上限，没有 ignore-interfaces。

| 文件 | 代码行 | 物理行 | 冷编退出 | 最大驻留 bytes | RTS total memory MiB | RTS elapsed |
|---|---:|---:|---:|---:|---:|---:|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 69 | 90 | 0 | 1,309,253,912 | 2217 | 14.721s  ( 14.714s elapsed) |
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 59 | 74 | 0 | 1,487,273,368 | 2548 | 16.447s  ( 16.443s elapsed) |

当前冷编日志与退出码文件：`YiFNTarget-alias-cold.log/.exit`、`YiFNUpper-cold.log/.exit`；原 Target 冷编 `YiFNTarget-cold.log/.exit` 留作初版记录；解析数据 `cold-summary.json`。禁用构造、洞、主机路径、--cubical 选项的本次新文件文本扫描均为 0，详情 `audit.json`。选项实际含 --safe --without-K --lossy-unification，库配置的 infective 选项沿仓库生效；scratch 各自显式写全。

#### 3. 逐字陈述与白话

本段逐字摘录正式源文件的签名；相应模块的别名与导入以源文件为准。`Keel⁻.twc keelᴱ n` 是终点实际继承底上的第 n 支，不是标准底上的 `twᶻ n`。`S` 是原 `YiFRStep`，`K` 是 `YiKVRel`，`SI` 是 `YiAbsSimInst`，`R` 是 `YiRefTw2`。

`low` 的逐字定义为 `E.ψ [] (E.Ωt (E.Ωt (E.EBOψ 0))) ∷ []`；其中 EBOψ 0 是 ω，所以这是 ψ₀(Ω_{Ω_ω})。这里是参照树的值下界，不声称 FGH 比较。

##### `YiFNTarget.lower`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 编译定理 | 目标不低于 ψ₀(Ω_{Ω_ω}) 的任意 HC 参照；该前提由 low-hc 实填。 |

```agda
lower : (hl : E.HC low) (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → R.Rt hl ≼ SI.E.tree h
```

##### `YiFNTarget.lower-btbo`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 编译定理 | 目标不低于 ψ₀(Ω_Ω) 的标准参照。 |

```agda
lower-btbo : (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → R.Rt (ET.hc-tower 2) ≼ SI.E.tree h
```

##### `YiFNTarget.lower-plus`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 编译定理 | 目标不低于 ψ₀(Ω_{Ω+1}) 的标准参照。 |

```agda
lower-plus : (h : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1))
  → R.Rt R.h₊ ≼ SI.E.tree h
```

##### `YiFNTarget.target-hc`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 编译构造 | 原目标项有封在 opaque 内的 HC 闭项。 |

```agda
  target-hc : SI.E.HC (E.fsn (Keel⁻.row keelᴱ 3) 1)
```

##### `YiFNTarget.low-hc`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 编译构造 | ψ₀(Ω_{Ω_ω}) 有封在 opaque 内的 HC 闭项，所以下界没有空前提。 |

```agda
  low-hc : E.HC low
```

##### `YiFNTarget.back-lower`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 编译定理 | 原 HC 与抽象 HC 的反向读回桥；只用于把实际 h 的下界写成原参照树值。 |

```agda
back-lower : ∀ {t} (h : SI.E.HC t) → ME.toL (ET.tree (XI.back h)) ≼ SI.E.tree h
```

##### `YiFNTarget.walk-lower`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 编译定理 | 沿每步 cofinality = ω 的给定有限基本列路径，终点参照不高于起点参照；每步复用原 fs≼。 |

```agda
walk-lower : ∀ t ns (ok : PathOK t ns) {u} → walk t ns ≡ u
  → (hu : E.HC u) (h : SI.E.HC t) → R.Rt hu ≼ SI.E.tree h
```

##### `YiFNTarget.shape00`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 有限测试：固定路径的 refl 等式 | 原目标的 [0,0] 后代就是 low。 |

```agda
shape00 : walk target p00 ≡ low
```

##### `YiFNTarget.shape001`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 有限测试：固定路径的 refl 等式 | 原目标的 [0,0,1] 后代就是 EBOψ 2。 |

```agda
shape001 : walk target p001 ≡ E.EBOψ 2
```

##### `YiFNTarget.shape-plus`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNTarget.lagda.md` | 有限测试：固定路径的 refl 等式 | 原目标的 [0,0,2,1,0,0,2,0] 后代就是 t₊。 |

```agda
shape-plus : walk target pplus ≡ R.t₊
```

##### `YiFNUpper.upper0`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 编译定理 | 实际第 0 个输出不高于实际第 3 支；复用已有 branch-upper。 |

```agda
upper0 : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 0))) ≼ K.readRW (Keel⁻.twc keelᴱ 3)
```

##### `YiFNUpper.upper1`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 编译定理 | 实际第 1 个输出不高于实际第 3 支；复用已有 branch-upper。 |

```agda
upper1 : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 1))) ≼ K.readRW (Keel⁻.twc keelᴱ 3)
```

##### `YiFNUpper.upper2`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 编译定理 | 实际第 2 个输出不高于实际第 3 支；复用已有 branch-upper。 |

```agda
upper2 : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 2))) ≼ K.readRW (Keel⁻.twc keelᴱ 3)
```

##### `YiFNUpper.prior-strict`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 编译定理 | 实际第 2 支的后继不高于实际第 0 个输出。 |

```agda
prior-strict : L.suc (K.readRW (Keel⁻.twc keelᴱ 2))
  ≼ K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 0)))
```

##### `YiFNUpper.not-prior-upper`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 编译否定 | 实际第 2 支不能作为实际第 0 个输出的上界；只否定这一候选上界。 |

```agda
not-prior-upper : K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 0)))
  ≼ K.readRW (Keel⁻.twc keelᴱ 2) → ⊥
```

##### `YiFNUpper.strict-upper`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 编译定理 | 每个实际输出的后继都不高于实际第 3 支。 |

```agda
strict-upper : ∀ q → L.suc (K.readRW (proj₁ (S.Step.out 2 (S.Step.chain 2 q))))
  ≼ K.readRW (Keel⁻.twc keelᴱ 3)
```

##### `YiFNUpper.beta3`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 有限测试：固定闭项的 refl 等式 | 实际 betaᴱ 3 的树分量就是实际第 2 支，保留原证明分量。 |

```agda
beta3 : betaᴱ 3 ≡ (Keel⁻.twc keelᴱ 2 , proj₂ (betaᴱ 3))
```

##### `YiFNUpper.out0`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 有限测试：固定闭项的 refl 等式 | 实际第 0 个输出展开为 tw 2 上的 Ω 折叠；底是 baseᴱ 3 的实际 inc zero 限制，起点仍为 betaᴱ 3。 |

```agda
out0 : S.Step.out 2 (S.Step.chain 2 0) ≡
  T.ψ (B.tw 2) (P.Ok-tw 2) (M.rbᶻ (B.tw 2)) childBase B.zero
    (P.z≤ (B.tw 2)) (betaᴱ 3) (proj₁ (O.Ωt (B.tw 2)))
```

##### `YiFNUpper.branch-form`

| 文件 | 档 | 白话 |
|---|---|---|
| `probes/OCF/Lean/YiFNUpper.lagda.md` | 有限测试：固定闭项的 refl 等式 | 实际第 3 支展开为原实际 out/chain 的 limc⁺，没有换链。 |

```agda
branch-form : Keel⁻.twc keelᴱ 3 ≡
  proj₁ (O.limc⁺ (λ q → S.Step.out 2 (S.Step.chain 2 q)))
```

#### 4. 第一个障碍（精确到比较）

实际第 0 点的独立记号上界未得到。它不能替换成标准底或前一站：

```agda
childBase i u = baseᴱ 3 i (P.inc B.zero u)
```

而 `out0` 的右侧仍是

```agda
T.ψ (B.tw 2) (P.Ok-tw 2) (M.rbᶻ (B.tw 2)) childBase B.zero
  (P.z≤ (B.tw 2)) (betaᴱ 3) (proj₁ (O.Ωt (B.tw 2)))
```

尚缺关于这一实际折叠的比较：给独立参照 U 的 HC，证明该输出的读回不高于 U 的参照值，并将 U 与原目标作可分离的值比较。此处未构造该证明。新 `not-prior-upper` 只说明 U 不能直接取实际 twc 2；它没有枚举或排除别的候选上界。

查到的旧块工具：`YiCeilRead.fold₀≼/folds₀≼` 是零层折叠，`YiCeilWit/Small` 是旧合法块的受限类；`YiXVStart/ThirdZero/World3` 中所读上界也作用在旧块。实际第 0 点当前需要的是 tw 2 输入层。检查了 `YiMTRel.A/S` 的逐字签名，二者要求 `NoΩ ℓ`，但临时编译定理 `no-NoΩ-tw2 : NoΩ (B.tw 2) → ⊥` 说明不能以该桥直接搬来结论。这个诊断只否定该桥的这一前提，不是否定另外构造桥的可能。

没有得到小 q 都低于原目标这一条件，故没有在缺少实例时转去证一般独立上界，也没有创建替代 FirstMissing 的弱接口。原 `YiFRStep.FirstMissing` 始终只读。两份正式文件都是验收文件，不主张记号无关性，也没有运行/声称依赖切片或导入闭包审计。

#### 5. 偏离、事故、读源与并行交流

- 先读了完整原简报、batch52-guardrails、AGENTS 与 EBOHandbook §4；未改题与定义，未进入条件未满足的错位步骤。
- 最初两个临时形状猜测错误：先猜目标的第 0 基本列项是 EBOψ 2（`YiFNCheck0.log`，退出 42）；第一次改写猜连续三个 0 后代是 ψ₀(Ω_ω)（`YiFNCheck0-2.log`，退出 42）。第二次改写按真实展开改为路径 [0,0,1] 后代是 EBOψ 2，`YiFNCheck0-3.log` 整体退出 0。没有把前两次猜测当数学结论；同一处两次重新设计后仍不通过的停止条件未发生。
- `YiFNUpperCheck.log` 的退出 42 是临时文件漏导入 `_,_`；补导入后 `YiFNUpperCheck-2.log` 退出 0，新增严格界后 `YiFNUpperCheck-3.log` 退出 0。无堆耗尽、超时、Agda 内部错误。未加堆、未另派子路。
- 初版完成了正式两件的逐件冷编。根审随后要求按 AGENTS 合并重复证明：已完整读 YiMXSamples，将 Target.walk/PathOK/get/get≤ 分别改为 trace/Allω/walk/walk≼ 的参数顺序适配别名，四个外部签名及其余所有签名逐字不变；back-lower 保留。修改后仅重冷编 Target，退出 0，日志只检查 Target；Upper 源码、冻结副本和其冷编日志未改。全文新文件扫描见 audit.json，未修改 README、LOG、台账、其他前缀、src 或 archive，未提交、推送或装包。
- 已在实现前查过并读到实际使用的定义/陈述：YiFRStep、FRStations、GIInst、GIEnd、ExSuff 的相关段；YiTBRow、MTTab、RWFold、RWOps 与 RWPath 的相关定义；YiKVRel.readRW、KQSuff.read≤、KCSem.rr≼、KSDesc.cumᴿ、KDStep.◃s≼、NFO.s≼-irrefl；目标侧的 AbsSim/AbsSimInst、ExInst、RefTw2 与 EboLeanTree.hc-tower。只按签名/局部查阅的大模块不声称整篇读过。
- 没有依靠未读代码的他人结论作为新增定理。原简报关于主线已有强度/其它各路的事实只作背景，未用来推上界。YiMS 回传第 0 步、q1 尝试及实际 chain 2 上 GR.R 种子/source 的正面方向状态（YiMSSeed），未独立复核，未导入或用于本路证明；它也未声称已给零层折叠值下界。
- 已向主审和已核 ID 的 YiMS 内部传递具体编译结果，均注明执行方已编、尚未独立复核。没有改动对方文件，没有向外部人员发消息。

#### 6. 冻结与复核入口

- 正式源文件的当前相同副本在 `frozen/`；Target 的合并前初版在 `history/YiFNTarget-before-alias.lagda.md`，Upper 未改；对应源文件和冷编日志的 SHA256 见 `SHA256SUMS.txt`。
- 本回报、audit.json、cold-summary.json、初次与冷编日志、临时已通过的源文件也入冻结清单。
- 独立复核先读两份正式模块的陈述，再分别只删该模块接口冷编。`NoΩ` 的桥诊断只有私有 scratch 文件，不作为新仓库数学模块；需要时按 libraries 加标准库与私有 include 路径重编。
- 主审独立复核之前，本回报的“编译”均指本路自身编译，不记为根审通过。

#### 7. 根审要求的复用修订（本次增补）

数学判决不变。重复递归已删除，当前定义如下；旧公开定义与本路同域同陈述，证书未发生阻止适配的差异。

```agda
walk t ns = MX.trace ns t
PathOK t ns = MX.Allω ns t
get t ns = MX.walk ns {t = t}
get≤ t ns = MX.walk≼ ns {t = t}
```

当前 Target 冷编与源码统计已替换上表；Upper 的源码 SHA256 仍为 `e8f516594b19becd493de72fc67aacc4381993723ac2a82f7a7d968e4a503600`。本次没有重编 Upper。

# YiNL Cn上Leaf的第三种构造：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | Codex，接口未提供精确标识 |
| effort (转录里请求的字段) | 未记录 |
| 起止 (转录的时间戳，UTC) |  至  |
| 封装记录中的回报调用 | 1；不代表执行过程工具或Agda次数 |
| token / 编译遥测 | 未提供；原始简报与完整回报封装留档，0计数不表示实测为0；冷编实测见回报与LOG |
| 新建仓库文件（主审核实） | YiNLCtx、Read、Raise、Ceiling、Bound2、Top2、Canonical、Keel |
| 文件前缀 | `YiNL` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-15: YiNL 第二塔项、龙骨Leaf/Lift与单顶接口否定复核” 一节 |
| 主审复核后的一句结论 | 8件独立复核：tw2完整Leaf、龙骨全部Leaf/Lift；Λ无单个E.T顶界但有Leaf；一般Leafᶜ未证，终点保留LowRest。 |

## 简报原文

### 任务简报：Cn 上一般的 Leaf：第三种构造（数学）（前缀 YiNL）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-15，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第五十一批四路之一（选项原文 "Cn 上一般的 Leaf（第三种构造）"），与本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **旧的组装**（主审复核过；它的全域 Leaf 前提已被 `YiLLLeafNeg.noLeaf` 否定，所以它本身什么也没说）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- **当前的组装**（主审复核过）：`YiCNAccept.ebo-rest : LeafRest → LiftRest → LowRest → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，三族前提是沿龙骨的具体陈述（`YiCNKeel` 的 `LeafAt`、`LiftAt`、`LowAt`，分别从第 3、2、1 站起未证）。
- **共同的目标陈述**（主审 2026-11-15 在临时文件里编译通过，源码留档 `probes/Survey/Reports-2026-11-12/attachments/SelfCheck-SC3Ends.agda.txt`；正式文件里请自己重写一遍并编译）：
  ```agda
  open ExSuff gradedᵍ domsᵍ using (Keel⁻)        -- YiExSuff, YiGIInst
  Kᴱ : ℕ → Set
  Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
  ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  ebo-from-stations k = ≼-trans reference (l≼ (λ n → ≼-trans (k n (hs n)) (upperᴱ n)))   -- reference, hs, upperᴱ 取自 YiGIEnd
  ```
  即终点等于 "对一切 n，第 n 站（`Keel⁻.row keelᴱ n` 即 `EBOψ n`，`Keel⁻.twc keelᴱ n` 是 `EBOᶻ` 的第 n 支）的值下界"。Leaf、Lift、保持这几族律只是证它的一种办法。已知的值：`YiMTValue.k1ᶻ : Kᶻ 1`（对 `twᶻ 1`），`YiMTValue.Kᶻ n = (h : HC (E.ψ [] (E.Ωt (ΩTower n)) ∷ [])) → Rt h ≼ readRW (twᶻ n)`；`YiVTTw2Hi.tω≼twᶻ`（塔第 2 项起 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))）。`Keel⁻.twc keelᴱ n` 与 `twᶻ n` 的关系请自己核对（`keelᴱ` 的底取 `EBOᶻ` 各支实际继承的折叠）。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **目标**（`YiCNAccept` 第 42–43 行，逐字）：
  ```agda
  Leafᶜ = ∀ {ℓ} → Cn ℓ → ∀ {ν} → GR.Rd ℓ ν → GR.R ℓ (E.Ωt ν) (proj₁ (O.Ωt ℓ))
  ```
  `cn→keel : Leafᶜ → C.Leafᵏ`。规范层号域 `YiCNDomain.Cn`（不读记号；构造：零、后继、带相邻路径的 ℕ 极限、Ω 函数字面为 `k ⊕ ↑ k c` 的 Ω 形状），`cn-tw`、`cn-ok`、`cn-mono`。
- **已证**：`YiCNAccept.leaf-tw0`、`YiCNTw1.leaf-tw1`（塔第 1 项，对一切读法）。`leaf-tw1` 的证法：先证全部读法都不高于 Ω₁，再用已有的 `leafΩ` 沿关系的向下封闭得到。
- **两次未走通的构造**（YiCN 回报 `probes/Survey/Reports-2026-11-12/YiCN.md`）：继承式（首错 zero 与 c 不一致）与直接式（首错孩子层号与 k 不一致），卡在 Ω 继承分支：假设孩子的 Leaf 仍不能把任意孩子 c 沿只接第一孩子 0 的边嵌入；`YiCNDirectNeg.no-NuFromChild` 否定了 "从孩子的后继读法提取 k 上相同前驱读法" 这个字段。
- 全域 Leaf 被否定（`YiLLLeafNeg.noLeaf`），反例不在 `Cn` 里。

#### 要做的（按序）
0. **最小检查**，在临时目录：在塔第 2 项上（第一个还没证的）写出 "全部读法不高于某个规范读法 κ"，以及 κ 上的 Leaf；确认类型正确、前提可满足。不成立就停下回报。
1. **第三种构造**（主审的建议，判断）：推广 `leaf-tw1` 的证法：对 `Cn` 里的每个层号 ℓ 给出树侧的规范顶读法 κ ℓ，证 (a) ℓ 的一切读法都在项序上不高于 κ ℓ，(b) κ ℓ 上的 Leaf，再用关系的向下封闭（`mc`）得到一切读法上的 Leaf。对 `Cn` 归纳。你也可以换别的办法（例如对读法 `Rd` 的推导归纳），说明理由。
2. 做成就交 `Leafᶜ`；做不到就交第一个挡住的引理；若在 `Cn` 里找到 Leaf 的反例，写成编译否定并停下（这是 "规范域上的 Leaf 被否定"）。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiNL`（模块名 `OCF.Lean.YiNL…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiXV`、`YiFR`、`YiS1`、`YiSX`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <标准库的 .agda-lib 路径>
  <cubical 的 .agda-lib 路径>
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

### YiNL 完整回报（待根审独立复核）

#### 1. 判决与原目标

对纲领与目标：本路没有修改树、折叠、合法性或 Cn。新内容全是验收侧关系、证书与定理，不进入前三层，也不声称树已自足。第 0 步完整通过；tw 2 对任意 Rd 读法的完整 Leaf 已证。原目标 Leafᶜ 整体仍未证。

一般化的首个障碍是“对每个 Cn 层号选择一个 E.T 顶读法”的接口本身：Λ 属于 Cn，但其读法在 E.T 项序上无界。该否定只针对单个有限记号顶读法，不是否定 Leafᶜ，也不排除以树或共尾族代替顶读法的办法。同一 Λ 的 Leaf 对任意记号项反而有正面定理。按原简报第 2 项及根审续派“前者可作为第三种构造首个障碍交付”的范围，本次在此交付；不把未证的 Leafᶜ 判作路线已否定。

原目标与终点的实际接通：另从同一搬运引理得到全部龙骨站的 Leafᵏ 与 Liftᵏ，且原全域 Lift 实填。旧的 LeafRest、LiftRest 不再作为新组装的前提；ebo-from-low 仅以原 LowRest 为前提。LowRest 从第 1 站起量化，包含低层关系推导及 Exᴴ 出口证据，整族可满足性仍未知。因此没有新增无条件 EBO 序数值验收；没有新的 FGH 比较结论。

这里“完整 Leaf”指对指定层号的全部 GR.Rd 推导成立；“全部龙骨 Leaf”指 C.Leafᵏ 的逐站固定读法，不代表整个 Cn 的 Leaf。

##### 第 0 步

候选 κ₂ = E.Ωs (E.Ωt (E.natT 1))，即 Ω_{Ω+1}。三件均有无额外前提的实例：rd-top₂ 给出 Rd (tw 2) κ₂；upper₂ 给出全部读法 ν ≤ᵀ κ₂；leaf-top₂ 给出顶读法上的 Leaf。top-check₂ 拼成完整实例，leaf-tw2 经 Ωt-mono 与 mc 得到任意读法的 Leaf。cn₂ 实填规范域证据。不是只把前提写成参数。

首次临时编译 min-01.log 为退出 42（up 与构造子撞名），修正后 min-02.log 退出 0。首次编译发生在本路开始约 10 分钟内，满足 30 分钟要求。先完成 top2-03.log 的第 0 步无条件实例，再写 Canonical 一般化文件；没有以一般 Cn 结果作第 0 步假设。

##### 问题表

| 问题 | 位置 | 档与结果 |
|---|---|---|
| tw 2 全部读法封顶 | YiNLBound2.upper₂ | 编译定理：不高于 Ω_{Ω+1} |
| 顶读法可满足及其 Leaf | YiNLTop2.rd-top₂ / leaf-top₂ | 编译定理：均实填 |
| tw 2 完整 Leaf | YiNLTop2.leaf-tw2 | 编译定理：任意 Rd 读法 |
| 任意 R 推导读回上抬层号 | YiNLRead.readR | 编译定理：全部层号、无额外前提 |
| 一般 Cn 的单个 E.T 顶界 | YiNLCanonical.no-finite-tops | 编译否定；反例层号 Λ 在 Cn 内 |
| 该否定是否为 Cn Leaf 反例 | YiNLCanonical.leaf-Λ | 编译正例：Λ 上任意记号项都有 Leaf |
| 整个 Leafᶜ | 原 YiCNAccept.Leafᶜ | 仍未证；未否定 |
| 全部龙骨 Leaf / Lift | YiNLKeel.leaf-keel / lift-keel | 编译定理：整个全称族实填 |
| 原全域 Lift | YiNLKeel.full-lift | 编译定理：忽略 Gl 前提即可由 readR 得到 |
| 终点 EBO | YiNLKeel.ebo-from-low | 编译条件定理：只剩 LowRest；整族可满足性未知 |
| 第四层是否迫使前三层改定义 | 全部文件 | 没有；只新建 YiNL 前缀验收模块 |

#### 2. 文件、冷编、内存与冻结

| 文件 | 代码行 | 物理行 | 冷编退出码 | 最大 residency（字节） | RTS total memory（MiB） | 秒 |
|---|---:|---:|---:|---:|---:|---:|
| YiNLCtx.lagda.md | 64 | 83 | 0 | 994,633,168 | 1865 | 11.352 |
| YiNLRead.lagda.md | 51 | 64 | 0 | 1,524,978,240 | 2498 | 15.106 |
| YiNLRaise.lagda.md | 87 | 103 | 0 | 1,375,660,184 | 2484 | 15.201 |
| YiNLCeiling.lagda.md | 126 | 154 | 0 | 1,375,134,840 | 2354 | 15.189 |
| YiNLBound2.lagda.md | 65 | 79 | 0 | 1,360,011,072 | 2485 | 15.731 |
| YiNLTop2.lagda.md | 58 | 80 | 0 | 1,524,968,216 | 2498 | 15.236 |
| YiNLCanonical.lagda.md | 64 | 86 | 0 | 1,525,009,528 | 2498 | 15.179 |
| YiNLKeel.lagda.md | 43 | 57 | 0 | 1,343,194,384 | 2576 | 15.196 |

总计有效代码行 558；物理行 706。

代码行口径：Agda 代码块内非空、非整行注释的行，包含选项与导入。另列物理行数，二者不混用。这些均为第四层验收文件，不与前三层 1513 行预算相加比较。

每件均只删除字面列出的自身 .agdai，然后在仓库根目录以 -M8G 和 -s 编译，依赖保持缓存。未使用 ignore-interfaces。每份冷编日志只出现自身模块的一条 Checking；源码编译前后 SHA256 相同。RTS 最大 residency 不是操作系统 RSS；total memory 也是 RTS 的另一口径。

冻结 SHA256 全表另见 YiNL-freeze.tsv / YiNL-freeze.sha256；逐件结果为 cold-results.json。禁用构造、本机路径扫描为 0，见 static-scan.json。未用公设、洞、停机/正性绕过、K、函数外延、irrelevant-projections 或 cubical。

#### 3. 主要定理（逐字陈述）

所有下述项目均为编译定理；含参数者明确保留参数。不列任何有限样本为证明。完整签名索引见 YiNL-signatures.md。

Ctx 的 run 是层号变换，row 是它逐字保留结点形状的律。Top a ν 是 GR.R a (E.Ωt ν) (proj₁ (O.Ωt a)) 的缩写。Ctx 由 identity、prefix a、compose 实填；row 的复合用等式合成，不用函数外延。

##### 读回与搬运

```agda
readR : ∀ ℓ {ν c} → GR.R ℓ ν c → GR.Rd (↑ ℓ c) ν

RaiseAt : L → Set
RaiseAt ℓ = ∀ F t → GR.Rd (run F zero) t → Top (run F zero) t →
  ∀ {ν y} → GR.R ℓ ν y → Top (run F (↑ ℓ y)) (t ++ ν)

raiseR : ∀ ℓ → RaiseAt ℓ
```

readR：任意 R 推导读回它的上抬层号，文件 YiNLRead。raiseR：底上已有读法与 Leaf 时，R 推导在相容上下文中产生 Leaf，文件 YiNLRaise。两者不把任意 Rd 推导直接变成 Leaf。

rd-ctx 是统一的拼接接口：

```agda
rd-ctx : ∀ F b {t ν} → GR.Rd (run F zero) t → GR.Rd b ν → GR.Rd (run F b) (t ++ ν)
```

原临时 rd-sum 已在正式文件中并入这一个接口，readR 与 raiseR 共用。

##### 第 0 步

```agda
κ₂ : E.T
κ₂ = E.Ωs T1.Ω₁

Upper₂ : Set
Upper₂ = ∀ {ν} → GR.Rd (tw 2) ν → ν ≤ᵀ κ₂

upper₂ : Upper₂

rd-top₂ : GR.Rd (tw 2) κ₂

LeafTop₂ : Set
LeafTop₂ = GR.R (tw 2) (E.Ωt κ₂) (proj₁ (O.Ωt (tw 2)))

leaf-top₂ : LeafTop₂

top-check₂ : TopCheck₂

leaf-tw2 : ∀ {ν} → GR.Rd (tw 2) ν → GR.R (tw 2) (E.Ωt ν) (proj₁ (O.Ωt (tw 2)))
```

upper₂ 在 YiNLBound2；其余在 YiNLTop2，TopCheck₂ = Upper₂ × LeafTop₂。Light 的 Ω 下标层都没有 Ω 形状，children 递归满足 Light；它给出严格上界，并覆盖第二塔项的全部孩子：

```agda
child-bound₂ : ∀ c {ν} → GR.Rd (tw 1 ⊕ ↑ (tw 1) c) ν → ν E.<ᵀ κ₂
```

文件 YiNLCeiling；这不是改变原合法性的新限制，仅是验收证明中的辅助谓词。light₁、light-up、light-sum 实填实际实例。

##### Ω 规范族与第一障碍

```agda
reg-read : ∀ k {μ} → GR.Rd k μ → GR.Rd (Ωc k) (E.Ωs μ)

reg-top : ∀ k {μ} → GR.Rd k μ → Top (Ωc k) (E.Ωs μ)

κ : ℕ → E.T
κ zero = []
κ (suc n) = E.Ωs (κ n)

canon-read : ∀ n → GR.Rd (tw n) (κ n)

canon-top : ∀ n → Top (tw n) (κ n)

cn-Λ : Cn Λ

unbounded-Λ : ∀ t → Σ E.T (λ ν → GR.Rd Λ ν × (t E.<ᵀ ν))

no-top-Λ : ∀ t → (∀ {ν} → GR.Rd Λ ν → ν ≤ᵀ t) → ⊥

FiniteTops : Set
FiniteTops = ∀ {ℓ} → Cn ℓ → Σ E.T (λ t → ∀ {ν} → GR.Rd ℓ ν → ν ≤ᵀ t)

no-finite-tops : FiniteTops → ⊥

leaf-Λ : ∀ ν → Top Λ ν
```

文件 YiNLCanonical。reg-read / reg-top 的输入有 canon-read 各项作实例。unbounded-Λ 对每个 t 构造具体更大的读法，不是依赖已矛盾的额外前提。其见证是 κ (suc (depth t))，depth 只沿项首的层号递归。这里比较的是有限记号的项序，不报告 κ 族的序数值验收或 FGH 强度。

##### 龙骨与终点

```agda
full-lift : Lift

kt-upper : ∀ n → Keel⁻.kt keelᴱ n ≤ᵀ κ n

leaf-keel : C.Leafᵏ

lift-keel : C.Liftᵏ

ebo-from-low : CA.LowRest → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ

Kᴱ : ℕ → Set
Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)

ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
```

文件 YiNLKeel。leaf-keel 用 kt-upper 将同站的 canon-top 向下封闭；lift-keel 用 readR。两个全族均有函数定义，未留参数。ebo-from-low 调原 CA.ebo-rest，只替换 LeafRest 与 LiftRest 的实填；没有引用全域 Leaf 的否定作消去。逐站 Kᴱ 到 EBO 的共同目标已按简报重写并编译，来自 GE 的仅 reference、hs、upperᴱ。

LowRest 不是闭项合法性；它含折叠保持与出口。它的整个全称族仍未实填、也未否定。故 ebo-from-low 只能读成条件定理。没有把 twᶻ n 的旧下界冒充实际继承底的 Keel⁻.twc keelᴱ n 的下界；这一步不是本路证明所需，未作该对应的额外结论。

#### 4. 第一个障碍与停止范围

第一障碍精确为 YiNLCanonical.FiniteTops，否定为 no-finite-tops；它比“κ 自身还有 Rd 证据和 Leaf”的原候选接口还少要求，只要求单个 E.T 上界，已在 Λ 失败。cn-Λ 给出域内实例，unbounded-Λ 给出逐个反例见证；leaf-Λ 同时防止把它误归类为规范域 Leaf 反例。

原目标没有改写：Leafᶜ 仍是 YiCNAccept 的原逐字陈述。未把 Cn 缩小为有限塔，也未新增构造子、改变派发、折叠或合法性。没有编译的 Leafᶜ 否定，故不写“Cn Leaf 已否定”。采用共尾族或按 Rd 推导的另一种一般构造仍属未完成建议；本路不将建议算作定理。

停止的实际依据是原简报允许交首个挡住的引理，及根审明确确认单顶接口不存在可以作为此构造的首个障碍交付。未触发 8G 耗尽或同点两次实质重设计失败。首个 readR 写法被停机检查拒绝，改为固定节点的 Node.readN 后通过；没有继续第二次失败重设计。

#### 5. 偏离、事故与引用范围

- 未改已有文件、README、LOG、台账、留档、src、archive；只新建八件 YiNL 文件及自身实验目录文件。未提交或推送。未引用本批 YiXV/YiFR/YiS1/YiSX 前缀。根审后续整合 YiS1.low1 不在本路范围。
- 为完成第 0 步，先证明了通用的 R 读回和相容上下文搬运；它们作为实际 top-check₂ 的依赖使用，不以条件接口替代实例。第 0 步通过后才写一般单顶接口的反例。
- 临时 read-02 为停机检查失败；read-03 将层号递归与固定节点上的 R 推导递归分开后通过。其他失败为作用域、等式方向、模块 telescope 不能 with、隐式参数推断和一次括号错误；没有删减定理前提、使用禁用编译指示或增加堆。正式提取时修正过 Ctx 字段导出与显式导入；全部文件随后重新编译并冷编。
- 临时早期版本没有逐版冻结源码。错误日志保留作工程轨迹，不把当前临时源码冒充每次失败时的原样源码。正式交付源及其逐件冷编、哈希一一对应。
- 曾尝试向主审线程发进度，被自动审批拒绝，理由是未核验收件线程及该内容的发送授权；该发送没有成功。随后只读核验来源线程。根审明确改为从本线程 final 读取报告，不再发送消息或申请提权；本路遵照执行，此事不影响本地数学与编译。
- 已读 AGENTS、手册 §4、当前 README、YiGIRel、YiHCRel 相关定义、YiLLCheck、YiCNTw1、YiCNDomain/CNAccept、YiLLLeafNeg 的句法引理与反例证明，以及本路用到的 EBO、EboLeanView/Base/3Base、MENote、MWPre、KVInst、GIInst/GIEnd、CNKeel、ExSuff 的相关片段。
- YiGT 只检索相关签名，未据其数学判断写证明。一次范围较宽的本地签名检索输出含 YiXV 的若干签名行，未打开其正文、未导入、未用于本路构造；不声称完全未看见其他路的文件名。
- 旧 Barrier、YiMX 否定以及旧报告的总体判断仅按简报作背景，未重新独立冷编所有旧依赖，未用这些判断作新否定的依据。对 N 的使用限于正面句法引理，不调用 noLeaf/noLeafOk；原终点 GE 只引用 reference/hs/upperᴱ。

##### 日志索引

- min-01 / min-02：42（撞名）/ 0（最小接口）。
- read-01 / read-02 / read-03：42（投影导入）/ 42（停机检查）/ 0。
- raise-01 / raise-02：42（括号）/ 0。
- ceiling-01 至 ceiling-04：42 / 42 / 42 / 0。
- bound2-01 至 bound2-03：42 / 42 / 0。
- top2-01：0（候选 Rd 与条件接线）；top2-02：42（导入）；top2-03：0（完整第 0 步、完整 tw 2 Leaf）。
- canonical-01、keel-01：均 0。
- YiNLRaise-initial-01：42（Ctx 字段导出）；随后八件 initial 均 0。
- 八件 cold：全部退出 0，各仅自身 Checking，源码哈希均不变。

完整原始简报另存 brief-original.md；所有日志、JSON、签名索引、冻结表和本报告均在同一实验目录。

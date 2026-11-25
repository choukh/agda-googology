# 摆脱侧：回灌链的前驱闭包域 (YiPC)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十七批；外部模型，作者转发 |
| 前缀 | `YiPC` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：摆脱侧：回灌链的前驱闭包域（前缀 YiPC）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十七批五路之一（选项原文 "摆脱侧：回灌链的前驱闭包域 (Recommended)"），与在跑的 YiPJ、YiNX、YiXV 以及本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- 作者 2026-11-14："“记作以后 \"摆脱翻译\" 那一侧的候选” 这个务必落实"。AGENTS "量化域先取带证据的读回域"，"攀爬与摆脱翻译要平衡"（1:1）。本路是本批的摆脱侧。
- **上一批的摆脱侧（YiCD）**，回报 `probes/Survey/Reports-2026-11-12/YiCD.md`：
  - `YiCDCanon.Canon`（不读记号：零、后继、各支都是有限树的极限）；`YiCDLift`：`StepSᶜ`、`liftQᶜ`、`lift-redᶜ : StepSᶜ → Lift₁ᶜ`。
  - `YiCDKeel`：`actual-chain : ∀ k → idx k ≡ iter (F.feed G) zero k`（塔第 1 项那一层的实际回灌链），`not-idx2 : Canon (idx 2) → ⊥`，`not-feed-closed`，`not-keel-domain`；`idx2-related`、`idx2-gamma`（`idx 2` 在记号关系的定义域里）。
  - 原因：`idx 2` 是极限，首支本身又是极限。
- 要求的量化域："一切满足 `M⁰ η c` 的第 0 层树"（`YiLTLift`）被几路判断为太宽；有限支的 `Canon` 被编译证明太窄。
- **主审建议的域**（判断，未编译）：实际回灌链各项的结构前驱闭包，`Pre x = Σ ℕ λ k → x ⊴ idx k`，`⊴` 是第 0 层结构前驱 `Lt`（`◃s`、`◃l n`）的自反传递闭包（检索现成的，例如 `YiKVRel` 的 `_⊴_`）。它只用树、折叠与回灌链，不读记号。你可以选别的不读记号的定义，说明理由。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：不读记号地写出 `Pre`；确认 `idx 0`、`idx 1`、`idx 2` 在内；确认 `lift-redᶜ` 一类的归纳要用到的前驱（`YiCDLift` 里的 `suc-inv`、`below` 一类）留在 `Pre` 里（向下封闭）。不成立就停下回报。
1. **域上的归约**：`StepS` 限到 `Pre` ⇒ `Lift₁` 限到 `Pre`（照 `YiCDLift.lift-redᶜ`，能复用就复用）。
2. **够不够接龙骨**：检查塔第 1 项那一层的保持（`YiKPRel.Top.Fold.LF¹`、`chain`，主线折叠上的 `YiLTKid`）用在实际塔第 1 项上时，只对 `Pre` 里的孩子调用 `Lift₁`；交 "塔第 1 项的值下界只需要 `Pre` 上的 `Lift₁`" 的编译定理，或第一个用到 `Pre` 之外孩子的反例。
3. **翻译账的信息**：这个域用到树的哪些构造与字段；若有更宽或更窄的域被编译否定，写成否定定理。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiPC`（模块名 `OCF.Lean.YiPC…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiNX`、`YiXV`、`YiLK`、`YiFM`、`YiLL`、`YiVW`）。定义量化域的文件文首标明 "不读记号"，用 `probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包没有记号模块；其余文件标明 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有八路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；5G 仍耗尽（先在回报里说明）；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。



## 本会话主审复核（2026-11-14）

3 件、140 同口径代码行（排除全行注释）；主审逐件删自身接口、5G 独立冷编全 0，各仅自身 Checking，源码哈希与定稿相同；禁用构造、洞、本机路径、Funext 0。Dom 全域 importclosure 本地 8 件、禁用 0，编译器依赖图恰为同 8 件、无记号模块。已读全部源码与回报。idx-in/below/least、Pre 上 StepSᴾ→Lift₁ᴾ、真实使用 Pre 内孩子证据的 chain/k1ᴾ 通过；新 M⁰ 推导 Exᴴ 未填、完整 StepSᴾ 未填。k1-value 独立复用已有值界，不用忽略参数的蕴涵冒充量化域证明。

## 回报原文（本会话执行）

### YiPC 完整回报（定稿，2026-11-14）

#### 1. 判决与范围

本路交付一个不读记号的量化域，以及该域足够用于实际塔第 1 项保持证明的编译定理。它满足“量化域先取带证据的读回域”：不改变树、折叠、比较表或合法性；不要求下标判等、三歧或全域派发。对“让树自足”的进展是量化域由树的实际回灌链及结构前驱确定，并有最小闭包定理。域目前专属于塔第 1 项的实际链，未证明阶段无关的域族。

**源码已经冻结；本回报定稿。** 三个仓库源码均在冻结后逐件删自身接口冷编，退出 0，各日志只有自己模块的 Checking。主审可独立冷编。

- 第 0 步：临时 `YiPCPrem.agda` 已先写出并编译，退出 0；此时尚未写一般保持证明。初始检查完成于本轮开始后 30 分钟内。`idx-in` 对所有 k 给见证，因此 `idx 0、1、2` 的成员证据不是由有限样本外推。`below`、`suc-inv`、`lim-inv` 覆盖所需的前驱递归。
- 第 1 步：`Restricted.lift-redᴾ : StepSᴾ → Lift₁ᴾ` 已编译。完整 `StepSᴾ` 和完整 `Lift₁ᴾ` 未实填；`step-zero` 及其全部前提有编译实例，`step-finite` 直接复用已有有限后继族。局部实例不被当作完整前提已成立的证据。
- 第 2 步：`chain` 与 `k1ᴾ` 保留实际折叠的保持推导，`k1ᴾ : Lift₁ᴾ → M⁰ (E.EBOψ 2) (twᶻ 1)` 已编译。它不调用原来的全域 `leaf¹` 或 `k1ˢ`。每次需要 lf 的实际调用都有 `idx-in (suc k)`；没有使用 Pre 外的孩子。此处没有反例，也没有未通过的编译。
- 闭项与值分开：树闭项仍为已有的 `idx k` 与 `twᶻ 1`；新增的是成员证据与条件保持推导。`k1-value` 直接复用 `YiMTValue.k1ᶻ`，交付已有的 ψ₀(Ω_Ω) 序数值下界，不提高无条件强度。不把这个旧值界包装成忽略 `Lift₁ᴾ` 的蕴涵，也不据它声称新 `M⁰` 推导已满足 `Exᴴ`。
- 第 3 步：`least` 给出 Pre 的生成最小性。`not-Canon-cover` 编译证明“Pre 不能全落在旧 Canon 内”，用实际 `idx 2` 和原 `YiCDKeel.not-idx2`。这不是 Canon 与 Pre 的双向包含/不包含分类，也不否定更宽的候选域。

| 问题 | 位置 | 档 / 结论 |
|---|---|---|
| 域是否有实际实例，是否包含第 2 个链项 | YiPCDom.idx-in / idx2 | 编译定理：包含全部链项 |
| 关系归纳的前驱是否留在域内 | YiPCDom.below / suc-inv / lim-inv | 编译定理：向下封闭 |
| 受限后继律能否推出受限孩子保持 | YiPCLift.Restricted.lift-redᴾ | 编译条件定理：能；完整前提未实填 |
| 实际根 Ω 保持是否调用域外孩子 | YiPCKeel.chain / k1ᴾ | 编译条件定理：只需要 Pre 内的调用 |
| 旧 Canon 能否覆盖该域 | YiPCKeel.not-Canon-cover | 编译否定：不能，反例是 idx 2 |
| 新保持推导本身的值出口条件 | YiPCKeel.k1ᴾ | 未实填 Exᴴ；不从 M⁰ 自动推值 |
| 塔第 1 项是否仍有值下界 | YiPCKeel.k1-value | 已有编译定理的直接复用，ψ₀(Ω_Ω) 下界 |
| 是否已经得到阶段无关的规范域 | 本路范围外 | 未证明；候选判断，不作路线否定 |

本路没有以有限测试替代证明，也没有宣布任何未编译否定的路线失败。

#### 2. 文件、冷编与审计

代码行口径：只数 Agda 代码围栏里的行；“总 / 非空”同时列出，包含选项和导入。内存为 GHC `+RTS -s` 的 maximum residency 与 total memory in use，不是操作系统 RSS。全部使用单个 Agda、`-M5G`，从未提高堆上限。

| 文件（均在 probes/OCF/Lean/） | 代码行 总 / 非空 | 冷编退出码 | maximum residency（bytes） | total memory（MiB） | elapsed（s，存在并行） |
|---|---:|---:|---:|---:|---:|
| `YiPCDom.lagda.md` | 40 / 32 | 0 | 158,893,240 | 271 | 1.795 |
| `YiPCLift.lagda.md` | 67 / 56 | 0 | 1,389,844,960 | 2344 | 17.106 |
| `YiPCKeel.lagda.md` | 60 / 53 | 0 | 1,678,730,632 | 2719 | 18.711 |

所有冷编日志的 Checking 行均严格只有本文件；不使用 `--ignore-interfaces`。删接口使用三个字面路径，每次只删对应 YiPC 模块。源码冻结校验见 `source-freeze.sha256`。

- `importclosure.py OCF.Lean.YiPCDom`：退出 0；脚本闭包 16 模块，本地 8、库直接可见 8；禁用表命中 0；没有传入 `--only` 缩窄审计范围。
- Agda `--dependency-graph`：143 节点，本地恰为同样 8 个模块，集合差 0；`OCF.Align.*`、`OCF.Notation.*`、`OCF.Free.Lab.*` 命中 0。编译器图含标准库的传递闭包，节点总数与脚本的库计数口径不同。
- Dom 的本地完整导入闭包：`YiPCDom`、`YiCDCanon`、`YiMTTab`、`YiRWBlock`、`YiRWFold`、`YiRWOps`、`YiRWPath`、`YiTBRow`，均在 `OCF.Lean`。
- 新增三个源码：公设、洞、停机/正性绕过、trustMe、禁用选项、函数外延、本机路径的检索命中均为 0。选项逐件为 `--safe --without-K --lossy-unification`；库选项沿用仓库。
- 上述审计只对新增源码和 Dom 的导入闭包作所列保证，不把旧依赖的所有结论计作本路独立复核。没有用切片计数替代编译器闭包。

#### 3. 定义与定理表

名称所在作用域照源码。`Restricted` 对任意比较表 `r : Rb ℓ¹` 参数化；接实际塔时取 `rbᶻ ℓ¹`。

```agda
Pre : Tr zero → Set
Pre x = Σ ℕ λ k → x ⊴ idx k

StepSᴾ : Set
StepSᴾ = ∀ {η x} → Pre x → cof η ≡ c1 → M⁰ (pred η) x
       → Q (ψᴺ 0 (E.Ωt (pred η))) (h₁ x)
       → Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc x))

  Lift₁ᴾ : Set
  Lift₁ᴾ = ∀ {η c} → Pre c → M⁰ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₁ c)))
```

这里的 `_⊴_` 是 `Lt` 的自反闭包；`Lt` 自身已含传递构造子 `◃t`，所以等于所要求的自反传递闭包。该两构造子编码来自 `YiKVRel._⊴_`，为保持 Dom 的干净闭包，在 Dom 内按第 0 层复置。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `idx-in` | <code>idx-in : ∀ k → Pre (idx k)</code> | 每个实际链项都带域证据。 | `YiPCDom.lagda.md` | 编译定理 |
| `idx0` | <code>idx0 : Pre (idx 0)</code> | 初始链项在域内。 | `YiPCDom.lagda.md` | 编译定理 |
| `idx1` | <code>idx1 : Pre (idx 1)</code> | 第一链项在域内。 | `YiPCDom.lagda.md` | 编译定理 |
| `idx2` | <code>idx2 : Pre (idx 2)</code> | 第二链项在域内。 | `YiPCDom.lagda.md` | 编译定理 |
| `below` | <code>below : ∀ {x y} → Pre y → zero ⊢ x ◃ y → Pre x</code> | 第一位置前驱留在域内。 | `YiPCDom.lagda.md` | 编译定理 |
| `suc-inv` | <code>suc-inv : ∀ {x} → Pre (suc x) → Pre x</code> | 后继的直接前驱留在域内。 | `YiPCDom.lagda.md` | 编译定理 |
| `lim-inv` | <code>lim-inv : ∀ {f a} → Pre (lim f a) → ∀ n → Pre (f n)</code> | 极限的每个分支留在域内。 | `YiPCDom.lagda.md` | 编译定理 |
| `least` | <code>least : (D : Tr zero → Set) → (∀ k → D (idx k))<br>      → (∀ {x y} → D y → zero ⊢ x ◃ y → D x)<br>      → ∀ {x} → Pre x → D x</code> | 任何包含全部链项且向下封闭的域都包含 Pre。 | `YiPCDom.lagda.md` | 编译定理 |

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `restriction` | <code>restriction : StepS → StepSᴾ</code> | 全域后继律可以限制到 Pre。 | `YiPCLift.lagda.md` | 编译定理 |
| `liftQᴾ` | <code>liftQᴾ : StepSᴾ → ∀ {η c} → Pre c → M⁰ η c → Q (ψᴺ 0 (E.Ωt η)) (h₁ c)</code> | 在 Pre 内对关系推导归纳，后继情形归到 StepSᴾ。 | `YiPCLift.lagda.md` | 编译定理 |
| `lift-redᴾ` | <code>lift-redᴾ : StepSᴾ → Lift₁ᴾ</code> | 把受限 Q 归约复用原 Q→Kd，得到受限孩子保持。 | `YiPCLift.lagda.md` | 编译定理 |
| `step-finite` | <code>step-finite : ∀ n → Q (ψᴺ 0 (E.Ωt (natT (suc n)))) (h₁ (suc (CF.nat n)))</code> | 直接复用已有的任意字面有限后继结论。 | `YiPCLift.lagda.md` | 编译定理 |
| `step-zero` | <code>step-zero : Pre zero → cof (natT 1) ≡ c1 → M⁰ (pred (natT 1)) zero<br>          → Q (ψᴺ 0 (E.Ωt (pred (natT 1)))) (h₁ zero)<br>          → Q (ψᴺ 0 (E.Ωt (natT 1))) (h₁ (suc zero))</code> | 受限 StepS 在 η=1、x=0 处有局部实例。 | `YiPCLift.lagda.md` | 编译定理 |
| `step-zero-domain` | <code>step-zero-domain : Pre zero</code> | 局部实例的树侧域前提有见证。 | `YiPCLift.lagda.md` | 编译定理 |
| `step-zero-rel` | <code>step-zero-rel : M⁰ (pred (natT 1)) zero</code> | 局部实例的关系前提有见证。 | `YiPCLift.lagda.md` | 编译定理 |
| `step-zero-ih` | <code>step-zero-ih : Q (ψᴺ 0 (E.Ωt (pred (natT 1)))) (h₁ zero)</code> | 局部实例的 Q 归纳前提有见证。 | `YiPCLift.lagda.md` | 编译定理 |

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `branch` | <code>branch : (lf : Lift₁ᴾ) → ∀ {η c} → Pre c → M⁰ η c → M.M¹ (E.fsT ΩΩ η) (G c)</code> | 带 Pre 证据的孩子保持给实际 G 分支的关系。 | `YiPCKeel.lagda.md` | 编译定理 |
| `chain` | <code>chain : Lift₁ᴾ → ∀ k → M⁰ (E.γT ΩΩ [] k) (idx (suc k))</code> | 仅用 Pre 内孩子保持得到全部实际 γ 回灌链关系。 | `YiPCKeel.lagda.md` | 编译定理 |
| `k1ᴾ` | <code>k1ᴾ : Lift₁ᴾ → M⁰ (E.EBOψ 2) (twᶻ 1)</code> | 仅用 Pre 内孩子保持得到实际塔第 1 项的 M⁰ 下界。 | `YiPCKeel.lagda.md` | 编译定理 |
| `k1-redᴾ` | <code>k1-redᴾ : StepSᴾ → M⁰ (E.EBOψ 2) (twᶻ 1)</code> | 受限 StepS 可代入上一条实际塔保持。 | `YiPCKeel.lagda.md` | 编译定理 |
| `not-Canon-cover` | <code>not-Canon-cover : (∀ {c} → Pre c → C.Canon c) → ⊥</code> | 旧 Canon 不能覆盖 Pre；见证是 idx 2，不断言两域包含关系。 | `YiPCKeel.lagda.md` | 编译定理 |
| `k1-value` | <code>k1-value : (h : E.HC (E.EBOψ 2)) → Rt h ≼ readRW (twᶻ 1)</code> | 直接复用已有的无条件序数值下界，没有 Lift 参数。 | `YiPCKeel.lagda.md` | 编译定理 |

`actual-chain` 不重证；`YiPCKeel` 用 public import 直接再导出原 `YiCDKeel.actual-chain`：

```agda
actual-chain : ∀ k → idx k ≡ iter (F.feed G) zero k
```

原文件与本路的 `M`、`F` 实例均为 `Sem (rbᶻ ℓ¹)` 及 `M.Fold (B₀ ℓ¹) M.gb₀ˢ`。该复用导入在本路冷编中通过；本路没有删除或冷编旧依赖接口。

##### 实际保持调用的证据

`chain` 的零行从实际折叠输出的非零证明用 `pos⁰` 构造关系，不需要 lf。后继行把 `chain lf k` 交给实际分支 `G (idx (suc k))`，通过 `branch lf (idx-in (suc k)) ...` 得到嵌入结点的关系，再直接用原 `F.LF¹ M.wi`；这个推导只有 `mU mz`，不会递归进入新的 Ω 结点。根 `k1ᴾ` 逐项用同一个 `branch lf (idx-in (suc k)) ...`，路径改成 `M.wu`，再沿原 `G⁰.m-cum` 和 `nodeZ` 汇成实际根。

因此不是从一个对所有 η、c 的 leaf 关系开始再口头声称只用了链；受限证据在每个实际调用位置存在，并由检查器验证。新源码中的 lf 只有 `branch` 真正调用，`branch` 的类型强制接收 `Pre c`。`F.LF¹` 的其余输入和 `gb₀ˢ` 不含全域 Lift 假设。

#### 4. 第一个障碍与翻译账

本任务的最小实例、受限归约和实际塔保持没有遇到类型错误或堆墙。继续构造无条件的受限 Lift 时，第一个未填陈述精确为 `YiPCLift.StepSᴾ`，对应 `liftQᴾ` 的 `m1` 行（源码第 40 行）；该行把 `Pre (suc x)` 向下反演为 `Pre x` 后调用 st。它是当前未填假设，不是编译过的路线否定。本路没有证明完整 `StepSᴾ` 的可满足性；只能交付全部已列局部实例与所要求的条件归约，不能把这些局部实例读作一般前提成立。

若后续要让这条新保持推导自身导出序数值，仍须处理 `Exᴴ (k1ᴾ lf)`，或者提供相应推导的其他出口。`k1-value` 使用已存在的无条件值定理，未解决这个推导级问题，也未把它隐藏进新的“域足够”蕴涵。

翻译账：

1. Pre 新使用的字段只有实际链号 k 和第一位置前驱证据；结构闭包用后继 `◃s`、极限分支 `◃l n`、传递 `◃t`。Dom 直接复用既有树侧 `G/feed/idx`；链本身照旧使用主线 `ψ`、`rbᶻ`、`B₀` 和孩子层 `h₁`。
2. 没有增加树构造子、结点字段、合法性条件或专用比较表前提；没有“第 4 层逼出”的定义改动。新增脚手架是规范读回域证据与保持关系的外部证明。
3. `least` 说明域不是逐个加特例生成：凡包含全部链项且向下封闭的谓词都包含它。这个结论不说明 Pre 具有全域 feed 闭包；本路没有声称 `Pre c → Pre (feed c)`。
4. 记号只出现在 Lift 与 Keel 两个验收文件，用来陈述 Q、M⁰ 与值下界；Dom 的编译导入闭包无记号模块。这个审计只保证“不引用”，不声称历史上的 h₁/ψ 定义未受记号启发。
5. 旧 Canon 被否定的是“覆盖全部 Pre/实际链”这一写明要求。没有证明 Canon 与 Pre 的严格包含，也没有否定其他更宽域。Pre 作为未来摆脱翻译侧的候选应登记；是否能推广到后续塔项，仍是待做问题。

#### 5. 偏离、事故与读源范围

- 没有修改已有文件、共享接口、导航、LOG、台账、src 或 archive；没有派子路，没有提交或推送。三个新源码全部为 YiPC 前缀。
- 没有编译失败、堆耗尽、超时或 Agda 内部错误；没有触发停止条件。仅逐件删除自身 `.agdai`。
- 证明来源均在文首注明。早期临时 `YiPCChainCheck` 对 `actual-chain` 用了一条 refl；定稿时已改为直接复用原 theorem，没有保留重复证明。保留临时源以便核查。
- 本路未读外部文献或外部代码，不需要重新调研。`YiNXFull/Low/Exit` 源码曾只读检查出口范围，确认其专用结果不能当作任意 Mᴴ 的无条件出口，没有导入本路；YiPJLimStep 只做签名检索，未用其结论；YiXV 未读取或引用。
- 简报提到的 `YiGIEnd.eboᵍ` 源码读过签名与定义作范围核对，没有作为新证明的依据，也未独立冷编。`YiKPRel` 只检索 LF¹/chain 并读模块来源，实际复用的是已读的主线 `YiLTKid`。没有把这些旧结果说成本路重新证明的定理。
- AGENTS、简报已完整读取；EBOHandbook §4 的一次组合工具输出被总输出截断，遗漏的 §4 末尾已另行补读。该末尾是性能经验对照，没有据截断内容作数学结论。
- 完整 StepSᴾ 无实例的事实已在模块头与本回报明确；没有以一个可能空真的完整前提宣称无条件强度进展。有限后继和零点前提的具体见证只按其原陈述使用。

#### 6. 全部路径与日志清单（供主审）

仓库源码：

- `<仓库>/probes/OCF/Lean/YiPCDom.lagda.md`
- `<仓库>/probes/OCF/Lean/YiPCLift.lagda.md`
- `<仓库>/probes/OCF/Lean/YiPCKeel.lagda.md`

唯一私有实验目录：`<实验目录>`。本回报：`<回报原文>`。本机路径只出现在临时回报/日志，仓库源码中为 0。

临时源码与生成脚本：

- `<实验目录>/YiPCPrem.agda`：第 0 步，先编译通过。
- `<实验目录>/YiPCLiftCheck.agda`：受限归约实验，编译通过。
- `<实验目录>/YiPCChainCheck.agda`：实际链和根 Ω 保持实验，编译通过。
- `<实验目录>/write_report.py`：本回报与验证摘要生成脚本，不是数学文件。

编译日志全部列出（每次使用 `-M5G -s`，均 exit 0）：

- `<实验目录>/YiPCPrem.log`
- `<实验目录>/YiPCDom-first.log`
- `<实验目录>/YiPCLiftCheck.log`
- `<实验目录>/YiPCLift-first.log`
- `<实验目录>/YiPCChainCheck.log`
- `<实验目录>/YiPCKeel-first.log`
- `<实验目录>/YiPCDom-cold.log`
- `<实验目录>/YiPCLift-cold.log`
- `<实验目录>/YiPCKeel-cold.log`

审计与构建辅助：

- `<实验目录>/libraries`
- `<实验目录>/YiPCDom-cold.exit`
- `<实验目录>/YiPCLift-cold.exit`
- `<实验目录>/YiPCKeel-cold.exit`
- `<实验目录>/YiPCDom-importclosure.log`
- `<实验目录>/YiPCDom.dot`
- `<实验目录>/dependency-graph-audit.log`
- `<实验目录>/source-audit.log`
- `<实验目录>/source-freeze.sha256`
- `<实验目录>/verification-summary.json`
- 临时编译接口：同一实验目录下 `YiPCPrem.agdai`、`YiPCLiftCheck.agdai`、`YiPCChainCheck.agdai`。
- 仓库编译接口：`probes/_build/2.8.0.2/agda/OCF/Lean/YiPCDom.agdai`、`YiPCLift.agdai`、`YiPCKeel.agdai`。

冷编配方：从仓库根目录，每件先删自己对应的上述接口，再运行（Dom 那件额外加依赖图参数）：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiPCDom.lagda.md > <实验目录>/YiPCDom-cold.log 2>&1
agda_result=$?
printf 'exit %s\n' "$agda_result"
```

冻结摘要：

```text
fbbeee780d33c62f5be75668f53fe348a0a7d7793642ecbeb5f79f6fbc110e55  probes/OCF/Lean/YiPCDom.lagda.md
cbf950cbd8697da83d5aa747ec19e3f6bd124844136717e2c62889994ff98be6  probes/OCF/Lean/YiPCLift.lagda.md
5df1a60c04914f4194accd365b06a301eba23892cded6f50a01221ec5ac52349  probes/OCF/Lean/YiPCKeel.lagda.md
```

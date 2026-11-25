# 塔第 1 项那层的量化域扩到塔实际用到的树（数学） (YiSP)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十六批（“外部模型额度很充足，我们可以多线并行”）；外部模型，作者转发 |
| 前缀 | `YiSP` |
| 回报 | 尚未返回；作者转回后附在下面 |

## 简报原文（本机路径换成占位）

### 任务简报：塔第 1 项那层的量化域扩到塔实际用到的树（数学）（前缀 YiSP）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十六批六路之一（选项原文 "塔第 1 项那层的量化域扩到塔实际用到的树 (Recommended)"），与并行的其他各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。原主线 `YiRWFold` 的值定理保留作参照。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **塔第 1 项那一层的保持**：`YiKPRel.Top.Fold.LF¹`（新主线折叠上的版本在 `YiLTKid`）对孩子层接口 `Kid` 成立，**量化域 `Sp`** 有两条限制（YiKP 回报 `probes/Survey/Reports-2026-11-12/YiKP.md` §1 问题表）：
  - 嵌入结点 `up x c y` 的左项推导是 `mz`（树 x 任意，参照取空）；
  - 推导里没有孩子层槽位上的 Ω 结点。
  - 塔第 1 项的 Ω 树在这个域里（`leafSp`）。
- **为什么要扩**：塔第 2 项的回灌链，下标是折到塔第 1 项那一层的输出；这些输出里有上折产生的孩子层槽位结点，也有左项非零的嵌入（YiKP 回报 §1 "离塔第 2 项回灌链里的折叠还差什么"）。所以 K(2) 要的保持超出 `Sp`。
- 关系：遗传封闭的族 `YiHCRel.Mᴴ`（构造子 `mc`）；有限读回层号上的保持 `YiHCFold`、新折叠上 `YiLTFold`。
- 底的闭包：嵌入行的底是 "x 朝各层的折叠"（`YiRWFold` 第 82–93 行）。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：各写一个最小的例子：(a) 左项非零的嵌入 `up x c y`（x 是塔第 1 项那一层的非零树）；(b) 带孩子层槽位 Ω 结点的树（例如上折 `Up` 产生的）。写出 `LF¹` 在它们上的陈述，确认类型正确、前提可满足。不成立就停下回报。
1. **去掉第一条限制**：左项推导任意时的保持。要用到底的闭包（"x 朝各层的折叠"）对关系的保持；若要额外的接口项，写清楚。
2. **去掉第二条限制**：孩子层槽位 Ω 结点的保持（这些槽位的层号是读回层号，没有 Ω 形状，可用 `YiLTFold` 一类）。
3. **检验**：塔第 2 项回灌链的前两个下标（折到塔第 1 项那一层的输出）落在扩大后的量化域里（构造或 `refl`）。做不到就交第一个挡住的引理。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiSP`（模块名 `OCF.Lean.YiSP…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiCD`、`YiDD`、`YiKQ`、`YiNX`、`YiXV`、`YiGI`、`YiVF`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有九路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
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

2 件，按主审统一口径计 225 代码行（执行方 264 行口径含空行与注释，不并列为同一成本）。主审逐件删自身接口、5G 冷编均 0，各仅自身 Checking；禁用构造、洞、本机路径与 Funext 命中 0。已读 Kid⁺、Shift、LF¹ 与 Zero/Fin 实例，孩子槽位仍为空。非零左项实例是编译定理；完整域扩张未完成。第 0 步与三次保持复用失败另行独立复跑；结果记录于 LOG，不把 42 当数学否定。

## 回报原文（本会话执行）

### YiSP 完整回报

定稿日期：2026-11-14。执行方自编译结果；主审仍须按简报独立冷编、查陈述后采信。

#### 1. 判决

**对纲领与目标的意义**：全部新增内容都在验收侧，不改树、折叠、合法性、闭项与证书。得到一条带额外底更新律的保持定理，以及一个非零左项的无额外前提实例；没有完成塔实际量化域的扩张，没有新增塔的序数值下界，不声称推进到新的 ψ₀(Ω_x) 强度，也不声称树已自足。

**停止位置**：第 1 步在有限孩子的指定路径保持 `Fin.Keep` 未走通。同一处初始复用方案和两次改写分别被检查器拒绝（实验 A、B、C，均退出 42）；依简报停止一般证明，没有继续第 2 步孩子槽位的一般保持，也没有开展第 3 步塔第 2 项回灌链前两个下标的入域证明。失败日志不是否定定理，没有关闭这条路线。

##### 第 0 步

临时文件 `YiSPStep0.agda` 通过（修正后退出 0）。

- (a) `nonzeroUp = up (suc zero) zero (suc zero) ◃s`，输入推导是 `mU (m1 refl mz) child1`。左项的树非零，左项参照也非零，推导确实不是 `mz`。
- (b) `childSlot = Ω (inj₂ (zero , inj₁ tt)) (λ c → suc (ι ℓ¹ c))`，槽位是孩子 `zero` 的第 0 层，输入推导 `childSlot-m` 已构造。其参照是 `E.Ωt (E.natT 1)`，不是 `E.Ωt []`。
- `LF¹-at` 逐字写出两者朝第 0 层折叠应满足的 `M⁰ (ψᴺ 0 ([] ++ a))` 结论，类型正确。`premises` 给出标准底、`z≤ ℓ¹` 路径与起点的实例。
- 档：两个输入与前提是编译构造；两条保持陈述的型检查是有限实例检查。该临时文件没有证明槽位例子的保持结论；没有把第 0 步当成第 2 步的证明。
- 首个临时编译已在任务开始后 30 分钟内执行；第一次约 15.5 秒退出 42，修正参照项后约 15.2 秒退出 0。

##### 各步交付范围

| 问题 | 位置 | 档与结论 |
|---|---|---|
| 非零左项及孩子槽位两个最小探针 | 临时 `YiSPStep0.agda` | 编译构造 + 有限型检查，通过 |
| 嵌入左项推导任意时的保持 | `YiSPRel.Top.Fold.LF¹` | 编译定理，条件是新接口 `Kid⁺` 和全称底更新律 `Shift`；没有 `Sp` 参数 |
| 这些额外前提是否有实例 | `YiSPInst.Zero` | 编译实例：孩子限字面 `zero`，`Shift` 由 `tt` 填入；非零左项的折叠结论已证 |
| 有限孩子上的前缀不变底闭包 | `Fin.gbx-same` | 编译定理，仅同一个前缀 |
| 有限孩子上的前缀更新 | `Fin.shift-from-keep` | 编译的逐推导归约；`Keep` 在 `mz` 上有实例 `keep-mz`；没有对任意推导的实例 |
| 孩子槽位结点的一般保持 | 第 2 步 | 未开展，按第 1 步停止条件收尾 |
| 塔第 2 项前两个下标入域 | 第 3 步 | 未开展，没有给出构造或 `refl` |

新增接口的实质区别：原 `Kid` 的前缀固定为 `t₀`；`Kid⁺.foldᶜ` 对前缀 `t` 量化，`GBc` 也显式带 `t`。在嵌入 `mU m ch` 中，左项 `m : M¹ a x` 先给出起点对着 `ψ₀(t ++ a)`，孩子折叠要在同一新前缀下使用底。额外律 `Shift B t` 正是要求孩子底 `cb B x c` 满足该新前缀的条件。它是充分接口，本路没有证明任意有效保持方案都必须具备这么强的全称律。

#### 2. 文件、编译与内存

只新增两份仓库源码；没有修改旧文件、文档、台账或其他前缀。代码行只计 Agda 围栏内。

| 文件 | 总行 / 代码行 | 删本文件接口后冷编退出码 | `+RTS -s` maximum residency | RTS total memory in use |
|---|---:|---:|---:|---:|
| `probes/OCF/Lean/YiSPRel.lagda.md` | 142 / 134 | 0 | 1,487,911,160 bytes | 2439 MiB |
| `probes/OCF/Lean/YiSPInst.lagda.md` | 138 / 130 | 0 | 1,337,543,752 bytes | 2319 MiB |

全程一次只跑一个 Agda，全部用 `-M5G -s`，没有加堆。冷编只删各自的接口，依赖接口保持热；不是整个导入闭包的从零构建。两份冷编日志分别只有一行 `Checking`，且为各自模块，无警告。禁用构造、洞和本机路径检索各为 0；明细与 SHA256 在 `YiSP-audit.log`。两个模块都明确标为读记号的验收文件，没有做“记号无关”的宣称，也没有运行定义依赖切片。

仓库源码（全部）：

- `<仓库>/probes/OCF/Lean/YiSPRel.lagda.md`
- `<仓库>/probes/OCF/Lean/YiSPInst.lagda.md`

实验目录：`<实验目录>`。库文件：`<实验目录>/libraries`。

临时 Agda 源码（全部保留）：

- `<实验目录>/YiSPStep0.agda`（通过）
- `<实验目录>/YiSPTryShiftA.agda`（失败尝试，退出 42）
- `<实验目录>/YiSPTryShiftB.agda`（失败尝试，退出 42）
- `<实验目录>/YiSPTryShiftC.agda`（失败尝试，退出 42）

主审编译命令（分别替换模块名）：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiSPRel.lagda.md
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiSPInst.lagda.md
```

#### 3. 定理表与逐字陈述

| 名字 | 一句白话 | 文件 | 档 |
|---|---|---|---|
| `Top.Fold.LF¹` | 给出前缀更新底律后，嵌入左项推导不限 `mz` | YiSPRel | 条件编译定理 |
| `Top.Fold.LFU` | 将任意左项的归纳结论交给孩子折叠 | YiSPRel | 条件编译定理，同一模块前提 |
| `Top.Fold.chain` | 下标层槽位的回灌链仍满足 `M⁰` | YiSPRel | 条件编译定理，同一模块前提 |
| `Zero.shift` | 孩子为字面零时底更新律可填入 | YiSPInst | 编译定理 |
| `Zero.lf¹` | 字面零孩子的全部 `M¹` 推导可保持，嵌入左项任意 | YiSPInst | 编译定理，无额外接口假设 |
| `Zero.nonzeroUp-m` | 给一个左项树与参照都非零的合法嵌入推导 | YiSPInst | 编译构造 |
| `Zero.nonzeroUp-fold` | 该嵌入的折叠对着 ψ₀(2) | YiSPInst | 编译定理，停在 `M⁰`，未过值出口 |
| `Fin.gbx-same` | 任意左项的底在原前缀下保持 | YiSPInst | 编译定理 |
| `Fin.keep-mz` | `Keep` 的逐推导前提有 `mz` 实例 | YiSPInst | 编译定理 |
| `Fin.shift-from-keep` | 指定孩子各有限地板的保持足以更新该推导的孩子底 | YiSPInst | 条件编译定理，前提实例为 `keep-mz` |

以下陈述直接从定稿源码抽取。`ℓ¹ = tw 1`。`M¹` 是 `Mᴴ (Sig ℓ¹) Low¹ Kd Nu¹`；本次一般定理的 `Low¹`、`Nu¹` 在孩子槽位仍取空。

##### 新接口与底更新律
```agda
record Kid⁺ (o : Ok ℓ¹) (r : Rb ℓ¹) : Set₁ where
  field
    Kd : (c : Tr zero) → E.T → Tr (h₁ c) → Set
    GBc : (c : Tr zero) → E.T → Base (h₁ c) → Set
    Pc : (c : Tr zero) → zero ≤ h₁ c → Set
    pz : ∀ c → Pc c (z≤ (h₁ c))
    pk : ∀ c → Pc c (self ∙ proj₂ (proj₁ o) c)
    foldᶜ : ∀ c (v : zero ≤ h₁ c) → Pc c v → (t : E.T)
          → (B : Base (h₁ c)) → GBc c t B
          → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
          → ∀ {s y} → Kd c s y
          → M⁰ (ψᴺ 0 (t ++ s)) (proj₁ (ψ (h₁ c) (proj₂ o c) (proj₂ r c) B zero v β y))
```

```agda
Shift : Base ℓ¹ → E.T → Set
Shift B t = ∀ {a x} → M¹ a x → ∀ c → GBc c (t ++ a) (cb B x c)
```

##### 保持定理的全部外部参数

```agda
module Top (o : Ok ℓ¹) (r : Rb ℓ¹) (K : Kid⁺ o r) where
  module Fold (B : Base ℓ¹) (t : E.T) (gb : GB¹ B t) (shift : Shift B t) where
```

`Pw` 的构造子只有 `wu`（一致路径）和 `wi`（`ink self`）；`F w β x = ψ ℓ¹ o r B zero w β x`。

###### `Top.Fold.LF¹`

```agda
LF¹ : ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ {a x} → M¹ a x → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (F w β x))
```

###### `Top.Fold.LFU`

```agda
LFU : ∀ {w a s x c y ey} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → M¹ a x → Kd c s y
    → M⁰ (ψᴺ 0 ((t ++ a) ++ s)) (proj₁ (F w β (up x c y ey)))
```

###### `Top.Fold.chain`

```agda
chain : ∀ {a} {g : Tr zero → Tr ℓ¹} → cof a ≡ cΩ []
      → (h : ∀ η c → M⁰ η c → M¹ (fsT a η) (g c))
      → ∀ k → M⁰ (γT (t ++ a) [] k) (iter (feed g) zero (suc k))
```

##### 实例及有限孩子的归约

`Zero`、`Fin` 均以 `(r : Rb ℓ¹)` 为模块参数，因而也可取主线的 `rbᶻ ℓ¹`。

###### `Zero.shift`

```agda
shift : ∀ B t → Shift B t
```

###### `Zero.lf¹`

```agda
lf¹ : (B : Base ℓ¹) (t : E.T) → M⁰ (ψᴺ 0 t) (proj₁ (B zero (ink self)))
    → ∀ {w} → Pw w → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ {a x} → M¹ a x → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (ψ ℓ¹ o¹ r B zero w β x))
```

###### `Zero.nonzeroUp-m`

```agda
nonzeroUp-m : M¹ (E.natT 1 ++ E.natT 1) nonzeroUp
```

###### `Zero.nonzeroUp-fold`

```agda
nonzeroUp-fold : M⁰ (ψᴺ 0 (E.natT 1 ++ E.natT 1))
  (proj₁ (ψ ℓ¹ o¹ r (B₀ ℓ¹) zero (z≤ ℓ¹) (Ωt zero) nonzeroUp))
```

###### `Fin.gbx-same`

```agda
gbx-same : ∀ B t → GB¹ B t → ∀ x c → GBcᶠ c t (cb B x c)
```

###### `Fin.Keep`

```agda
Keep : (B : Base ℓ¹) (t : E.T) → ∀ {a x} → M¹ a x → Set
Keep B t {a} {x} m = (n : ℕ) → ∀ {i} (si : Sb n i)
         → M i (ψᴺ i (t ++ a))
            (proj₁ (ψ ℓ¹ o¹ r B (fn i) (inc (nat (suc n)) (inc tt (pth si)))
              (B (fn i) (inc (nat (suc n)) (inc tt (pth si)))) x))
```

###### `Fin.keep-mz`

```agda
keep-mz : ∀ B t → GB¹ B t → ∀ x → Keep B t (mz {x = x})
```

###### `Fin.shift-from-keep`

```agda
shift-from-keep : ∀ B t → GB¹ B t → ∀ {a x} (m : M¹ a x) → Keep B t m
                → ∀ c → GBcᶠ c (t ++ a) (cb B x c)
```


`Kid⁺`、`GB¹`、`Shift` 的可满足实例是 `Zero.kid`、标准底下的 `mkGB¹ (m1 refl mz) (λ _ → tt)`、`Zero.shift`；`Zero.nonzeroUp-fold` 实际把这些实例送入了 `LF¹`。`Fin.shift-from-keep` 的前提是逐个推导的 `Keep B t m`，不是未经实例化的全称假设；`keep-mz` 给出其可满足实例。任意推导上的 `Keep` 没有被填入。

#### 4. 第一个障碍：有限孩子底的指定路径保持

待证目标精确为以下签名（只在回报列出，源码没有洞或假设该项）：

```agda
-- 在 YiSPInst.Fin r 内
all-keep : (B : Base ℓ¹) (t : E.T) → GB¹ B t
         → ∀ {a x} (m : M¹ a x) → Keep B t m
```

若有它，可对每个 `m` 调 `shift-from-keep` 得到 `Shift`；本路没有证明 `all-keep`，也没有否定它。`Keep` 的第一个分量（`n = 0`，`i = 0`，`si = s0`）就要求路径

```agda
inc (nat 1) (inc tt self)
```

上的折叠保持，而已有 `LF¹` 的路径只是一致路径和 `ink self`。

| 尝试 | 检查器首个错误 | 解释与档 |
|---|---|---|
| A：用 `gb⊴`/`ψ-⊵` 的同前缀底闭包填 `Shift` | `t != t ++ a` | 有限失败尝试；`gbx-same` 没有改变参照前缀 |
| 改写一 B：以 `LF¹` 填入首个地板分量 | `inu (…) != inc (suc zero) (inc tt self)` | 有限失败尝试；所需指定孩子路径不在现有 `Pw` 中 |
| 改写二 C：以孩子层已有的 `YiLTFold.LF` 接收源推导 | `m` 不能检查为 `M 1 …`，源签名的槽位类型不同 | 有限失败尝试；有限层的定理不能直接接收 `tw 1` 的 `M¹` 推导 |

这些错误只说明上述三个复用项没有满足所写类型，不证明目标为假，不证明 `Keep` 是保持不可避免的前提。没有把它们归到壁垒或已知墙。

#### 5. 偏离、事故、候选与阅读边界

##### 范围与停止

- 严格只写 YiSP 前缀的新仓库模块；实验和库文件都在自己的实验目录。
- 没有改树、折叠、合法性的定义，没有提出第 4 层改前 3 层的请求。
- 没有新增子路，没有提交或推送，没有修改 README、LOG、台账或留档。
- 在第 1 步同一底更新缺口的两次改写仍失败后停止；因此第 2、3 步没有完成，最终不报告为成功扩域。
- 把原固定前缀 `Kid` 改成验收侧新接口 `Kid⁺`，属于简报允许的“额外接口项”，不是已有树侧定义的改动。原 `Kid` 没有被改写。

##### 编译与工程事故

- 第 0 步最初把孩子第 0 层槽位的参照写作 `E.Ωt []`；检查器指出其余尾为后继，改为 `E.Ωt (E.natT 1)` 后通过。只是修正探针参照，不是改题。
- `YiSPRel-v1` 误把嵌在 `Top` 中的 `nodeZ` 当顶层导出导入，退出 42；随后通过 `Sem (rb-no ℓ¹)` 的既有导出复用，未重证该引理。
- `YiSPInst-v1` 的依赖相等匹配写在内联 lambda 中，无法完成替换；改为与既有文件相同的顶层路径引理后通过。
- 生成审计文本的 Python 命令曾因旧版 Python 不接受 f-string 表达式内的反斜线而失败；把行数计算移出 f-string 后完成。没有影响 Agda 源码或编译结论。
- 无堆耗尽、超时、内部错误或 LibraryError；没有使用 `--ignore-interfaces`，没有删除别人的接口。

##### 给主审入台账的候选与放下的尝试

- 新候选：任意前缀的孩子接口 `Kid⁺`，配显式底更新律 `Shift`，可导出不带 `Sp` 的 `LF¹`。状态：条件编译定理；字面零孩子有完整实例；有限孩子的全称实例未走通。
- 新归约：有限孩子的每个底分量要求 `Keep`，即 `tw 1` 沿字面指定孩子路径折向该孩子各有限地板的保持。状态：逐推导充分条件编译，`mz` 有实例，全称版本未证。
- 放下的直接复用办法：同前缀广义单调、现有两路径的 `LF¹`、孩子源层的有限 `LF`；对应 A/B/C 日志，均不是否定结果。
- 判断/建议（未实施，不算证明）：下一轮若继续，可先检验指定孩子路径的保持目标；也可检查本路的全称底条件是否超过孩子推导实际读取的槽位范围。这两项均未被本路否定，也没有改派。

##### 实际阅读与转述边界

完整读取了简报、AGENTS.md、EBOHandbook.md 第 4 节。导航读取 README 入口片段；按签名与相关代码段读取 YiLTKid、YiKPRel、YiKPInst、YiHCRel、YiHCFam、YiLTFold、YiHCFold 的底记录、YiRWBlock、YiRWOps、YiRWPath、YiTBRow、YiMTTab、YiKVRel、YiRBCrit 的相关定义；YiKP 留档只读了开头与简报/回报起始段，未冒充通读。另查看 YiT2Frame、YiPMT2Frame、YiPMT2Desc、YiTBTail、YiTSOrbit 的相关片段用于定位背景，没有将它们未经复核的新结论算作本路结果。

EboLeanDef、EboLeanBase 等记号模块未逐篇读正文；使用的记号计算、`cof`、`fsT` 等经实际读取的已有接口定理和检查器核型。没有外部检索或独立模型审核，没有把任何未通读的报告判断当作本路的否定定理。

#### 6. 全部日志路径与退出码

| 日志绝对路径 | Agda 退出码 |
|---|---:|
| `<实验目录>/YiSPStep0.log` | 42 |
| `<实验目录>/YiSPStep0-v2.log` | 0 |
| `<实验目录>/YiSPRel-v1.log` | 42 |
| `<实验目录>/YiSPRel-v2.log` | 0 |
| `<实验目录>/YiSPInst-v1.log` | 42 |
| `<实验目录>/YiSPInst-v2.log` | 0 |
| `<实验目录>/YiSPInst-v3.log` | 0 |
| `<实验目录>/YiSPInst-v4.log` | 0 |
| `<实验目录>/YiSPTryShiftA.log` | 42 |
| `<实验目录>/YiSPTryShiftB.log` | 42 |
| `<实验目录>/YiSPTryShiftC.log` | 42 |
| `<实验目录>/YiSPRel-cold.log` | 0 |
| `<实验目录>/YiSPInst-cold.log` | 0 |

审计日志：`<实验目录>/YiSP-audit.log`（生成命令退出 0）。

回报：`<回报原文>`。定稿后未再更改数学文件。

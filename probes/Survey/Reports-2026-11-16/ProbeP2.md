# 探针 P2：树侧自举，终点写成树侧算子的闭包点（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 10:52 至 11:21 |
| 工具调用 / agda 编译 (粗数) | 63 / 6 |
| token (usage 字段，按消息去重) | 输出 171820；新写入缓存的输入 320964；读缓存的输入 10709137；其余输入 102 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `ProbeP2` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 卡住，卡点与 MathO2 相同：结构半边已编译（主线、原块、候选 A 已有龙骨下降，本轮补上换基候选 keelᴮ，主审 6G 冷编 P2Keel、P2Shape 都退出 0）；'每多一项塔多一层 Ω 下标' 写成单命题有三种形：结构形真但不约束值，无滞后值形第一个实例就是第 3 站（主线偏向不成立，判断），带滞后值形与目标等价（编译 lag→all、all→lag）；下一个必经缺口仍是 YiFRStep.FirstMissing；换基候选只剩 k6 一种亏损（形状编译）；文件附 attachments/ProbeP2-*.txt |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b87/P2.md`。先用 Read 工具完整读它，再逐条照做（含 "规则" 与 "回报" 各节）。只在简报指定的工作目录里写，不改仓库里任何文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

### 探针 P2 回报：树侧自举（终点写成树侧算子的闭包点，逐层闭合）

主文件 `report.md` 没有写成：Write 工具拒绝子智能体写报告文件，所以全文放在本回报里，请主审另存。两个试验文件和它们的日志都在工作目录 `<实验目录>/probe/P2/`：`P2Keel.agda`、`P2Shape.agda`、`P2Keel.log`、`P2Shape.log`。没有改仓库里的任何文件。

档位：【编】编译定理；【纸】纸面证明；【测】有限测试；【判】判断。

站号：第 n 站是 ψ₀(Ω_{ΩTower(n−1)})。第 2 站是 ψ₀(Ω_Ω)，第 3 站是 ψ₀(Ω_{Ω_Ω})。
- `Kᶻ n`（在 `YiMTValue` 里）说：独立塔 `twᶻ n` 不低于第 n+1 站。
- `Kᴱ n`（在 `YiFRStations` 里）说：终点第 n 支 `twc n` 不低于第 n 站。它比 `Kᶻ` 多滞后一步。

#### 0. 一句话结论

**卡住，卡点与 MathO2 相同。** 这条办法没有给出越过已知缺口的新手段。

- **结构半边已经编译。** 这一半在树侧，不读记号。龙骨层号 `kl n = tw n ⊕ ↑ (tw n) (Ωt (tw n))` 是塔第 n 项后面接 "Ω_{tw n}"。它上面的标准折叠不高于塔第 n+1 项。
  - 主线 `keelᶻ`、原块 `keel`、候选 A `keelᴬ` 已有。
  - 换基候选的 `keelᴮ` 本轮补上【编】。
  - 读法半边也已编译：`tw-step`、`leaf-keel`、`lift-keel`。
- **剩下的值半边，就是现成条件定理的前提。**
  - 主线：`LowRest`（`YiNLKeel.ebo-from-low`）。
  - 换基候选：`LowSlot`（`YiWREnd.ebo-endˢ`）。
  - 逐站写法：`YiFRStep.Tail`。
  - 值半边的每一步，都要证折叠保持某个参照的分级关系或值语义。这正是第 3 路（公理化）与第 4 路（模拟）的对象。
- **"每多一项塔，精确的外层至少多一层 Ω 下标" 写成单个命题，有三种形，都不能把缺口归结过去。**
  - 结构形是真的【编】，但它不约束值。
  - 无滞后的值形 `GrowV`，第一个实例就是 `Kᶻ 2`（第 3 站）。在主线上偏向不成立【判，依据 MathO2】。
  - 带滞后的值形 `GrowLag`，与 "一切站都被某项塔支配" 等价【编：`lag→all`、`all→lag`】，等于目标本身，不算归约。
- **下一个必经缺口：`YiFRStep.FirstMissing`。**
  - 它要证：第 3 站基本列的第 1 项 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}}) 不高于终点第 3 支某个链点的输出。
  - 这一项高于 ψ₀(Ω_{Ω₂})，证明要经过 MathO2 定位的亏损格（下标 Ω+1 那一层，记作 `k6`）。
  - 剩余距离：从第 3 站到 EBO 的全部站，而且需要一条对一切站都成立的保持定理。

#### 1. 要证的精确陈述（逐级）

##### 1a. 第 0 层的闭合：x ↦ ψ₀(Ω_x)，x 可数

不动点就是第 2 站，已编译【编】：
- `YiKSRead.k1 : K 1`
- `YiMTValue.k1ᶻ : Kᶻ 1`
- `YiFRStations.k2 : Kᴱ 2`

##### 1b. 第 tw n 层的闭合：朝 tw n 折，以输出作下标

树侧算子取自 `YiFRStep.Step n`，是主线终点第 n+1 支实际用的回灌链：

```agda
feed : Tr (tw n) → Tr (tw n)      -- 以 c 为下标的 Ω 树, 朝 tw n 折
feed c = proj₁ (TB.ψ (tw (suc n)) (Ok-tw (suc n)) (rbᶻ _) (baseᴱ (suc n)) (tw n) (ink self)
                     (baseᴱ (suc n) (tw n) (ink self)) (g c))
chain = iter feed zero             -- 逼近这一层的闭包点
out c = TB.ψ (tw (suc n)) … zero (z≤ _) (betaᴱ (suc n)) (g c)   -- 同一棵树折到第 0 层
```

| 形 | 陈述（Agda 类型） | 状态 |
|---|---|---|
| 结构：上界 | `branch-upper : ∀ m → readRW (proj₁ (out (chain m))) ≼ readRW (twc (suc n))` | 【编】`YiFRStep` |
| 结构：多一层 Ω | `σ¹ n : ↑ (tw n) (Ωt (tw n)) ⊑¹ ↑ (tw n) (σ n)`：第 1 个链点读成层号后，第一孩子路上有 Ω 树 | 【编】`YiKSDesc`（独立塔，标准底） |
| 结构：龙骨 | `GrowS n = readRW (F₀ᶻ (kl n) (okl n)) ≼ readRW (twᶻ (suc n))` | 【编】主线 `keelᶻ`；换基 `keelᴮ`（本轮） |
| 读法 | `tw-step : Rd (↑ (tw n) (Ωt (tw n))) ν → Rd (tw (suc n)) ν`；`LeafAt n`、`LiftAt n` | 【编】`GR.tw-step`；`YiNLKeel.leaf-keel`、`lift-keel` |
| 值：起点 | `start-match : Kᴱ n → (h : HC (fsn (row (suc n)) 0)) → tree h ≼ readRW (proj₁ (out (chain 0)))` | 【编】`YiFRStep` |
| 值：余项 | `Tail n = ∀ m → Σ ℕ λ q → (h : HC (fsn (row (suc n)) (suc m))) → tree h ≼ readRW (proj₁ (out (chain q)))`；`step : Kᴱ n → Tail n → Kᴱ (suc n)` | `step`【编】；`Tail` 缺，第一个缺口是 `FirstMissing`（n = 2，第 1 项） |
| 值：分级（主线） | `LowAt n = R (tw n) (Ω_{kt n}) (Ωt (tw n)) → Σ (R zero (row n) (twc n)) Exᴴ`；`LowRest = ∀ n → LowAt (suc n)` | 缺；`ebo-from-low : LowRest → toL EBO-tree′ ≼ readRW EBOᶻ`【编】 |
| 值：分级（换基） | `LowSlot = ∀ s K → Inv s K → ∀ p → Nu a p κ → R a η y → R (at a p) (ψ_κ(K ++ η)) (slotFold s p y)` | 缺；`ebo-endˢ`【编】；`YiWREnd` 文首判断 `Inv₀`、`Inv₁` 下量化域太宽 |
| 值：龙骨 | `KLᶻ n = (c : HC (EBOψ (suc (suc n)))) → Rt c ≼ readRW (F₀ᶻ (kl n) (okl n))`；`Stepᶻ n = Kᶻ n → KLᶻ n` | n ≥ 1 时缺；`kl→Kᶻ`【编】；`K2-redᶻ` 把 `KLᶻ 1` 归到 `Row₂ᶻ`，第 0 行【编】，第 1 行起缺 |

##### 1c. 单命题的三种值形（本轮的 `P2Shape.agda`，全部【编】为类型或定理）

```agda
Ht n h  = (c : HC (EBOψ (suc h))) → Rt c ≼ readRW (twᶻ n)   -- 塔第 n 项不低于 ψ₀(Ω_{ΩTower h})
GrowV   = ∀ n h → Ht n h → Ht (suc n) (suc h)
GrowLag = ∀ n h → Ht n h → Σ ℕ λ d → Ht (suc (d + n)) (suc h)
```

已编译的组装：
- `grow→K : GrowV → ∀ m → Kᶻ (suc m)`
- `grow→K2 : GrowV → Kᶻ 2`
- `step→K : (∀ n → Stepᶻ (suc n)) → ∀ m → Kᶻ (suc m)`
- `lag→all`，以及反方向的 `all→lag`（用到 `tw≼ᶻ` 与 `m≤′m+n`）
- `all→ebo`、`lag→ebo`、`grow→ebo`

##### 1d. 最后一步需要什么

```agda
all→ebo : (Y : T₀) → (∀ n → readRW (twᶻ n) ≼ Y) → (∀ m → Σ ℕ λ n → Ht n (suc m)) → toL EBO-tree′ ≼ Y   -- 【编】
```

唯一的一次比较是 `YiRefTw2.endpoint`：EBO 参照树的值不高于任何支配它各行的 Y。这一条已编译。它要两样输入：

- **(i) 每项塔都不高于 Y。**
  - 取 Y = `EBOᶻ` 时，要 `YiSYFrame.Bridge n = twᶻ n ≼ twc n`。这条既没有编译证明，也没有否定。
  - 改用终点各支 `twc`，则已有 `YiNLKeel.ebo-from-stations`。
- **(ii) 一切站的下界**，即 1b 的值形全体。

所以 "最后只比一次" 的写法不存在。能做成一次性的，最多是一条对一切层号都成立的保持定理（分级关系 R 加 `LowKeep`），而那是第 3、4 路的对象。

#### 2. 已有的可复用结果

- **结构（树侧）：**
  - `YiKSDesc`：`desc`、`σ¹`、`rowsΩ`、`keel`、`row1`、`rowN`
  - `YiMTKeel`：`keelᶻ`、`rowsΩᶻ`、`tw≼ᶻ`、`row0ᶻ`
  - `YiKSDescA`：`keelᴬ`
  - `YiFRStep`：`branch-upper`、`prior-upper`
  - `YiFRStations`：`station-step`、`branch-form`
- **读法：**
  - `YiKSRead`：`Read.Rd`、`rd-kl→tw`
  - `YiExSuff`：`Keel⁻.tw-step`、`TowerE.keel`
  - `YiNLKeel`：`leaf-keel`、`lift-keel`、`full-lift`
- **值（条件定理）：**
  - `YiKSRead`：`kl→K`、`K2-red`、`row0₂`
  - `YiMTValue`：`K2-redᶻ`、`row0₂ᶻ`
  - `YiFRStep`：`step`、`start-match`
  - `YiNLKeel`：`ebo-from-low`、`ebo-from-stations`
  - `YiCNAccept`：`LowRest`、`ebo-rest`
  - `YiWREnd`：`Wire.LowSlot`、`chain←slot`、`ebo-endˢ`、`ebo-end₀`、`ebo-end₁`
  - `YiKDStep`：`Fam`、`FamStep`、`Chain.fam→Kκ`、`Blk`（这是 YiKD 原型块，不是主线）
- **抽象理论：** `YiAbsGIface` 与 `YiAbsGSuff`（分级模拟的接口与充分性），`YiExSuff`（带条件的出口）。
- **最后一步：** `YiRefTw2.endpoint`；`YiEXRow.down₀`、`down₁`。

#### 3. 第一步：本轮已做与下一级台阶

##### 本轮已做

两个文件都用 6G 堆编译，退出码 0。

**`P2Keel.agda`【编】**

- **换基候选的龙骨下降：**
  - `keelᴮ : readRW (F₀ᴮ (kl n) (okl n) (rbkl n)) ≼ readRW (twᴮ (suc n))`，对一切 n 成立。
  - `twᴮ n` 是 `YiBSFold.closed n`，即换基候选的独立塔，用标准底。
  - 证明照 `keelᶻ` 写。证据沿第一孩子路继承（`rb¹`）。第一个链点在三个折叠里是同一棵树（`σ-sameᴮ`，refl）。下降路径不经过换基那一行。
- **`k6-tw1`、`keep-one`：两个候选共用的保留缺陷，最小实例。**
  - 在 tw 1 上取一个槽位：它在孩子 nat 1（也就是层 1）里，位于第 0 层。目标是层 1，路径经过同一个孩子 nat 1。结果是 `nothing`，即不保留。
  - 同一个槽位放到层 1 自己上、路径取 `self`，就保留。
- **`k6ᴮ`：** 在一般的 Ω 形状层号上，换基候选的结点行逐字走链（refl），条件是孩子侧槽位配经指定孩子的路径。原因是 `YiBSFold` 照用 `YiRWFold.kp`。
- **`seen-row`、`fallback-row`：回灌底所在的那一格（tw 1 上，目标第 1 层，经孩子 nat 2）。**
  - 换基候选：重建层 1 ⊕ ↑c 的 Ω 树朝层 1 折（`seen`），再加上孩子树折到第 0 层。
  - 主线：嵌入在后继孩子时表里没有条目，逐字回退成 "左项的折叠 ⊞ 孩子树折到第 0 层"。
  - 所以 MathO2 的两种亏损里，换基候选只剩 `k6` 一种。形状是【编】，对值的影响是【判】。

**`P2Shape.agda`【编】：** 1c、1d 里列出的全部定义与定理。

##### 若继续这一路，下一级台阶

- **台阶 A（树侧，结构）：把结构形接到真正的终点上。**
  - 交付：终点各支（用继承的底）上的龙骨下降，或者 `Bridge n`。
  - 做法：先证 "折叠的输出读成层号后，第一孩子路上含底值"；再证底在 Ω 树之上（`ψ-⊵` 的 ◃ 形）时 `step¹` 照旧成立。
  - 止损：如果需要折叠对底的值单调（不只是第一位置序），就停。
  - 这一步不提高强度。
- **台阶 B（值）：证 `FirstMissing`，或它的带滞后形 "∃ n，`Ht n 2`"。**
  - 需要 MathO2 的 (C1) 和 (C2)。(C1) 是对非正规树也有定义、对各行单调的值语义；(C2) 是补回引理。
  - 止损：一轮写不出 (C1) 就停。MathO2 已经一轮没写出来。

#### 4. 到终点的台阶清单（代价与可行性都是判断）

| 台阶 | 内容 | 代价 | 可行性 |
|---|---|---|---|
| 0 | 结构形，全塔，独立塔 | 已编译（主线、原块、候选 A、换基候选） | — |
| A | 终点各支上的结构形，或 `Bridge` | 200 到 500 行 | 偏向可行 |
| B | 第 3 站：`Kᴱ 3`，即从 `FirstMissing` 开始的 `Tail 2` | (C1) 800 到 1500 行；(C2) 不估 | 未知 |
| C | 一切站：对一切 n 成立的分级保持（`LowRest`，或带合适 `Inv` 的 `LowSlot`） | 3000 行以上 | 未知 |
| D | 最后一步的比较 | 已编译（`endpoint`、`all→ebo`） | — |

单命题对两个候选分别真不真：

| 写法 | 主线 | 换基候选 |
|---|---|---|
| 结构形 `GrowS` | 真【编 `keelᶻ`】 | 真【编 `keelᴮ`】 |
| 无滞后值形 `GrowV`，第一个实例是第 3 站 | 偏向不成立【判：MathO2 偏向 "塔第 2 项不低于 ψ₀(Ω_{Ω+1})" 不成立，把握不高】 | 未知：只剩 `k6` 一种亏损，是否仍能到第 3 站没有算 |
| 带滞后值形 `GrowLag` | 与目标等价【编】，真假未知 | 同左 |

#### 5. 风险与可能撞上的已编译否定

- **`YiAbsGNeg.unkept→¬low`【编（抽象形）】。** 前提是关系由六条规则生成、参照一侧保持余尾 Ω、折叠输出不含结点；在这三条下 `LowKeep` 不成立。
  - 槽位层严格低于目标时，`k6` 格符合这个模式【判：没有核对 `GR.R` 是否满足 `Inv` 模块的生成前提】。
  - 所以在包含 `k6` 格的量化域上，无滞后的逐层保持走不通，值半边只能带滞后或带补回 (C2)。
- **`YiAbsFrame.branch→wdec`、`hand→wdec`，以及 `YiAbsObs` 的 `obs→dec` 一族。** 修 `k6` 最直接的办法是 "槽位孩子等于路径孩子时保留"，这要求对孩子判等，正好落在这一族的前提里【判：只读了文首】。
- **`YiAbsGNeg.cap→¬low`。** 只要某一格的折叠值有一个低于参照的上界，`LowKeep` 就不成立。
- **层号序上的单调。**
  - 沿任意孩子的层号路径，F₀ 不单调；即使在理想读法里也不单调，因为坍缩函数在闭包外不单调【纸】。
  - 跨层单调接口另有编译否定 `YiCompatDlNeg`、`YiCompatDlLPO`（只读了文首）。
  - 所以树侧自举能用的 "层号序"，只能由第一孩子路与链点孩子这两种边生成。
- **结构形不约束值【纸】。**
  - `GrowS` 把 K(n+1) 换成 `KLᶻ n`，而 kl n 的读法恰好是 ΩTower(n+1)，高度没有降下来。
  - 沿链再展开一层，链点孩子 tw n ⊕ Ω_{tw(n−1) ⊕ d₁} 的理想读法仍是 Ω_{ν_n}，高度还是一样。
  - 要落地，只能落到记号基本列的可数种子上（`YiKDStep.Fam n`），而 `FamStep` 需要分级关系（`Blk`）。

#### 6. 没有读、只凭转述引用的

- **MathO2：** 序数模型里的值，以及 "塔第 2 项与理想值一致的部分大约止于 ψ₀(Ω_Ω·ψ₁(Ω₂))"、"三族层号都避不开 `k6`" 这些判断，都取自留档 `MathO2.md` 的回报原文。没有打开 `MathO2Check.agda.txt`。
- **只读了文首或签名的：**
  - `YiKSDescA`、`YiAbsGIface`、`YiAbsGSuff`、`YiAbsObs`、`YiAbsFrame`
  - `YiCompatDlNeg`、`YiCompatDlLPO`、`YiSYFrame`
  - `YiBSAccept`、`YiBSRead`、`YiWRZero` 等 `YiBS*`
  - `YiBCCover`（只 grep 过）
  - `YiGIRel`：`GR.R`、`GR.Rd` 的定义没有读
  - `YiHCRel`、`YiLLCheck`
- **没有读：**
  - `probes/OCF/Barrier.lagda.md`
  - MathA、MathR、MathE、MathK、MathV 各留档
  - `YiAbsGNeg` 中 `Inv` 模块的正文
  - 文献与 `research_notes/`
- **读了全文的：**
  - 块与折叠：`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`、`YiTBRow`、`YiMTTab`
  - 龙骨与站：`YiKSDesc`、`YiKSRead`、`YiKDStep`、`YiMTKeel`、`YiFRStations`、`YiFRStep`
  - 分级组装：`YiExSuff`、`YiGIInst`、`YiNLKeel`、`YiCNKeel`、`YiCNAccept`
  - 换基候选：`YiBSBase`、`YiBSFold`
- **部分读：** `YiWREnd`（120 到 245 行），`YiMTValue`（导入与 (d) 节）。

文件（本机路径）：
- `<实验目录>/probe/P2/P2Keel.agda`
- `<实验目录>/probe/P2/P2Shape.agda`
- `<实验目录>/probe/P2/P2Keel.log`
- `<实验目录>/probe/P2/P2Shape.log`

## 简报正文（子智能体读的文件，本机路径换成占位）

### 探针 P2：树侧自举：终点写成树侧算子的闭包点，逐层闭合

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。工作目录 `<实验目录>/probe/P2/`，主文件写进 `<实验目录>/probe/P2/report.md`。

#### 这一路探什么
已编译的 "塔第 n+1 项不低于龙骨层号上 Ω 树的标准折叠"（`probes/RESULTS.md` "龙骨的树侧一半" 一行，`YiKSDesc`、`YiKSDescA`；另看 `YiKDStep`、`YiFRStations`、`YiFRStep`）。要回答：
- 把终点写成树侧算子 F（我们自己的折叠作用在 "以 x 为层号的 Ω 树" 上）的闭包点，需要哪些陈述；注意 x ↦ ψ₀(Ω_x) 在可数 x 上的不动点只是 ψ₀(Ω_Ω)（第 2 站），所以闭合要逐层：在龙骨的每一层 ℓ 上，朝 ℓ 的折叠对 "以输出作下标" 闭合。写出这组逐层闭合陈述的精确形状（Agda 类型），核对哪些已编译、哪些缺。
- 剩下的缺口能否归结为 "每多一项塔，精确的外层是否至少多出一层 Ω 下标" 这一个树侧命题；它对主线与换基候选分别真不真（纸面或小实例编译）。
- 最后一步才需要一次比较（与任何参照）；说清那一步要什么。

#### 作者的话（原文，2026-11-17）
- 作者问："除了与记号EBO对比外, 你认为还有什么办法能说明其值不小于EBO?" 主审答了五种：1 经典集合论里直接算值（比较对象换成 Buchholz 的集合论定义）；2 树侧自举（终点写成树侧算子的闭包点，逐层闭合）；3 公理化（律加一次性的充分性定理）；4 模拟（先证现折叠带滞后地支配一个修正过的参照折叠，再比一次参照）；5 证明论强度（若理论 T 的证明论序数是 EBO，证 "沿这棵树的超限归纳推出 T 的一致性" 一类陈述，就给出不低于 |T|）。
- 作者随后原话："并行派出多路探针子代理给你的5种办法先行探路. 我特别看中第五种, 与你的评估相反. 形式化代价高, 但可能一步一个脚印能到终点, 而不会像现在一样完全看不出出路, 感觉是无底洞"。你是其中一路探针：先行探路，不是做完。

#### 背景（只给指针，自己读定义核实）
- 先读 `AGENTS.md`（纲领、结论的写法、Agda 一节）与 `probes/README.md` 的 "当前阶段"。现状：作者裁决纲领第 4 条不改（成品与记号无关），终点暂定在已证的第 2 站；读法到 EBO = ψ₀(Λ) 的树闭项有两个：主线 `EBOᶻ`（`probes/OCF/Lean/YiMTTab`，折叠 `YiTBRow.ψ`，块与路径 `YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`；已证 `YiFYRef.target-low`：不低于 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω) 的参照树；成品入口 `YiSHEntry`）与换基候选 `EBOᴮ`（`YiBSBase`、`YiBSFold`、`YiWREnd`）。
- 已知障碍（留档 `probes/Survey/Reports-2026-11-16/` 的 `MathA`、`MathR`、`MathE`、`MathK`、`MathV`、`MathO2` 及 `attachments/Math*`）：保留判定 `kp` 在 "Ω 形状层号上、目标经指定孩子、槽位层低于目标层" 时走链（`kp (nd (sΩ k) h) _ (inj₂ _) (inc _ _) = nothing`），下标 Ω+1 一层就被问到，与塔无关；主线另有表缺项的回退；树侧没有对非正规树有定义、对折叠单调的 "该有的值"；逐项对应的参照关系已被反例否定。已编译的否定：`obs→dec` 一族（`YiAbsObs`）、`YiAbsFrame.hand→wdec`、壁垒 `probes/OCF/Barrier.lagda.md`、跨层单调接口 `YiCompatDlLPO`/`YiCompatDlNeg`。
- 主审的先验判断（不是定理）：换基候选终点不低于 EBO 约 45%，主线约 20%；关键问题是 "每多一项塔，精确的外层是否至少多出一层 Ω 下标"。
- 记号一侧：`probes/OCF/Align/EBO.lagda.md`，标准形良基 `EboLean3Omega.wf`，抽出的参照树 `EboLean3Tree.EBO-tree″`（验收文件可以用，成品不能用）。文献：`probes/Survey/reports/布劳威尔树折叠难点文献调查.md` 与 `research_notes/` 下的笔记，查文献先看 `probes/Survey/OrdinalNotationsGuide.md`、`CodeGuide.md`。

#### 规则
- 只在你的工作目录写；不改仓库里任何文件，不删 `.agdai`（自己工作目录的除外），不 `rm`/`pkill`，不写 `/tmp`，不装包，不提交。网络检索只用通用数学术语，不带项目名、作者名或个人信息。
- 可写小的纯 `.agda` 检查（选项行 `{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}`），在仓库根目录编译 `agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes -i <你的工作目录> <文件>`；同时还有五路探针，一次只跑一个 agda；报退出码不经过管道。无公设、无洞、无停机或正性编译指示；`Funext` 只能作前提。
- 区分四档：编译定理、纸面证明、有限测试、判断。不用比喻和方向性形容，不用 "决定性" 的说法；报 "下一个必经缺口"、它所在的位置与剩余距离。强度写 ψ₀(Ω_x)。否定只有编译过的定理才算，否则写 "未走通"。
- 一轮内交回。止损：一轮内看不出第一步怎么落地，就如实报卡在哪里。

#### 回报（最后一条消息就是回报，主审会原样留档；工作目录里的主文件也会附进留档）
0. 一句话结论：这条办法看起来 可行 / 不清楚 / 卡住，依据。1. 这条办法要证的精确陈述（分到每一步或每一级台阶）。2. 已有的可复用结果（仓库模块与定理名，或文献）。3. 第一步（或第一级台阶）的具体做法、交付与止损点；若做了小实验，给编译结果。4. 到终点的台阶清单与每级的代价估计（判断）。5. 风险与可能撞上的已编译否定。6. 没有读、只凭转述引用的东西。


# 摆脱侧：字面路径单调的一般形式（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 12:30 至 13:04 |
| 工具调用 / agda 编译 (粗数) | 72 / 15 |
| token (usage 字段，按消息去重) | 输出 184566；新写入缓存的输入 501107；读缓存的输入 11672410；其余输入 106 |
| 写过的仓库文件 | `YiLXClimb.lagda.md`, `YiLXFold.lagda.md`, `YiLXOne.lagda.md` |
| 文件前缀 | `YiLX` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 3 件全部退出 0，禁用构造 0，导入闭包干净；climb（字面路径上源折叠不高于目标折叠，一般形式）成立；前缀 0、1 由它得出；前缀 2 的底前提被否定（Le 太窄） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b70/YiLX.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiLX 回报（摆脱侧：折叠对字面路径与底的单调，一般形式，不读记号）

#### 1. 判决

**这对纲领与目标意味着什么。** 三个新文件都不读记号（导入闭包审计禁用表命中 0），选项是 `--safe --without-K --lossy-unification`，没有公设。"源 Ω 树的折叠不高于目标 Ω 树的折叠"这一步现在是一条树侧编译定理 `climb`。它在字面路径 ℓ ⊑ ℓ′ 上陈述，层号、路径、两侧的底、两侧的表、目标层都是变量，也不按阶段加专属前提。

不过，要把它用到两条实际链上（得到 ActualMissing），必须比较源与目标的底，而现在的模拟关系 `Le` 装不下这种比较：
- 源前缀 2 的底在第 2 层（`C.g 1`）有一个分量，含一个分支取值在第 0 层的 Ω 结点。
- 对应的目标分量没有这种结点。
- `Le` 不能把这样一个 Ω 结点放到极限链下面。

按 AGENTS 的读法，这是"关系太窄"，不是值比较本身的数学障碍（此读法是判断）。

**各步进度：**
- 第 0 步：做完。在 `YiOGFirst` 的对象上，前提可满足（编译）。
- 第 1 步：做完。量化域是"源层不含 Ω 形状"；路径经过 Ω 形状的结点时只经孩子 `zero`，这部分已纳入。
- 第 2 步：前缀 0、1 已得到；前缀 2 起未走通。
- 第 3 步：见本节末尾的翻译账。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 一般形式（任意 ℓ ⊑ ℓ′、底、表、目标层） | `YiLXClimb.climb`、`climbₒ` | 编译定理 |
| 前缀 0、1 由一般形式得出，与 `YiOFLocal.At.first`、`YiOGFirst.prefix-one` 陈述相同 | `YiLXOne.prefix-zero`、`prefix-one` | 编译定理 |
| 前缀 2 对齐到目标前缀 0 或 1 时，`climb` 的底前提不成立 | `YiLXOne.no-base-two-at0`、`no-base-two-at1` | 编译定理（否定） |
| 前缀 2 对齐到目标前缀 2 时，底前提不成立 | `YiLXOne.no-base-two` | 编译条件定理；条件是 `Dry target-next`，未证，它成立是判断 |
| 对齐到目标前缀 m ≥ 3 时也不成立 | — | 判断（理由：目标链的层号都 ≥ 3，第 2 层的分量不会出现分支在第 0 层的 Ω 结点） |
| 源层本身含 Ω 形状 | 基情形需要 `Can (Ωt ℓ)`，`YiVRRel.β-not`（已有）对 `tw 1` 否定了它 | 编译否定（已有），只否定这一步 |
| Ω 形状结点经孩子 c ≠ zero | — | 判断：需要兄弟孩子层号之间的路径，`Ok` 与 `rbᶻ` 一般不给 |
| 目标路径取 `inc` 形（ℕ 极限结点按 `way` 比较） | — | 未做；目标第 0 层的一致路径 `z≤` 是 `inu` 形 |
| ActualMissing 的全部前缀、Offset、Cover；"末端读记号只一次" | — | 未走通，末端未到达 |

**翻译账**
- 用到的树侧构造：
  - 路径 `self`、`inc`、`inu`；拉回 `pull-base`、`pull-ok`；
  - `Ok`、`Base`、`Pr`、`⊴`；
  - `Le` 的规则，第一位置序 `◃`（`◃t`、`◃l`、`◃s`），以及 `mono`；
  - `next⁺`；ℕ 极限层 Ω 树的部分和 `cum`、`limc⁺`；
  - `kp`、`node⁺`（经 `node≼ʳ`）；
  - 表 `Rb` 只作变量：不含 Ω 形状的层号上不被查询，Ω 形状一行只在 `inflA` 里按三种条目处理。
- 新增脚手架两件：
  - `Fit`：目标路径沿 v 的每个结点取 `inu`；
  - `Dom`：目标底的每个非 `self` 分量与标准 Ω 树相等，或在它第一位置之后。
  - 两件都没有从记号读入，也不给树加构造子或字段。
- 这条定理在整体引理里是哪一块（判断）：它是"跨层一步"，把前缀比较化成最底层上同一层号的底比较（B ⊴ 拉回的 B′）。整体引理缺的那一块，是一条比 `Le` 宽的底关系，能把分支取值在更低层的 Ω 结点与极限链相比。

#### 2. 文件表

| 文件 | 代码行 | 删接口后冷编 | 用时 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiLXFold.lagda.md` | 133 | 0 | 2.6 s |
| `<仓库>/probes/OCF/Lean/YiLXClimb.lagda.md` | 119 | 0 | 3.0 s |
| `<仓库>/probes/OCF/Lean/YiLXOne.lagda.md` | 74 | 0 | 2.4 s |

- 冷编日志里各只有自己模块的一行 `Checking`。
- 检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、洞、`--cubical`、`irrelevant-projections`、本机路径：结果为 0。
- `importclosure.py` 对三个模块：禁用表命中 0，退出码 0。
- 临时目录 `<实验目录>/work/YiLX/` 里有 `YiLX0.agda`（第 0 步，撞 251 后弃用）、`YiLXok.agda`、`YiLX1.agda`，以及各次日志。

#### 3. 定理表

全部是编译定理。

- **`climb`**（YiLXClimb）
  ```
  climb : ∀ {j ℓ ℓ′} (v : ℓ ⊑ ℓ′) {w : j ≤ ℓ} {w′ : j ≤ ℓ′} → Fit v w w′ → NoΩ ℓ
    → (o′ : Ok ℓ′) (r : Rb ℓ) (r′ : Rb ℓ′) (B : Base ℓ) (B′ : Base ℓ′)
    → B ⊴ pull-base v B′ → Dom B′ → (β β′ : Tr⁺ j) → Le j (proj₁ β) (proj₁ β′)
    → Le j (proj₁ (ψ ℓ (pull-ok v o′) r B j w β (proj₁ (Ωt ℓ))))
           (proj₁ (ψ ℓ′ o′ r′ B′ j w′ β′ (proj₁ (Ωt ℓ′))))
  ```
  白话：沿字面路径往上，若源底不高于拉回的目标底、目标底不低于标准底、起点不高，则源层 Ω 树的折叠不高于目标层 Ω 树的折叠（按 `Le`）。`ψ` 是 `YiTBRow.ψ`，主线所用的那个折叠。

- **`climbₒ`**（YiLXClimb）
  同上，只是源层的合法性证据取变量 `(o : Ok ℓ) → o ≡ pull-ok v o′`，结论里的源折叠是 `ψ ℓ o r B j w β (proj₁ (Ωt ℓ))`。
  白话：实例用的形状，等式在实例里由 `refl` 给出。

- **`peelS`**（YiLXClimb）
  ```
  peelS : (a : L) (o : Ok (nd sS (λ _ → a))) (r : Rb (nd sS (λ _ → a))) (bs : Base (nd sS (λ _ → a))) (j : L) (w : j ≤ a) (β : Tr⁺ j) {x : Tr j}
    → Le j x (proj₁ (ψ a (proj₂ o tt) (proj₂ r tt) (λ i u → bs i (inc tt u)) j w β (proj₁ (Ωt a))))
    → a ⊢ proj₁ (Ωt a) ◃ suc (proj₁ (next⁺ (bs a (inc tt self))))
    → Le j x (proj₁ (ψ (nd sS (λ _ → a)) o r bs j (inu (λ _ → w)) β (proj₁ (Ωt (nd sS (λ _ → a))))))
  ```
  白话：后继层的一步，是 `YiOGRelPeel.peel-from` 的表变量版。

- **`tower-low`**（YiLXClimb）
  ```
  tower-low : (n : ℕ) → Le zero (proj₁ (ψ zero tt tt (B₀ zero) zero self (Ωt zero) (proj₁ (Ωt zero))))
    (proj₁ (ψ (tw n) (Ok-tw n) (rbᶻ (tw n)) (B₀ (tw n)) zero (z≤ (tw n)) (Ωt zero) (proj₁ (Ωt (tw n)))))
  ```
  白话：路径的每一步都经过 Ω 形状结点（孩子 `zero`）时也成立。这是"含 Ω 形状层号"能纳入的部分的实例。

- **`fl`**（YiLXFold）
  ```
  fl : (ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (r r′ : Rb ℓ) (B B′ : Base ℓ) → B ⊴ B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j)
      → Le j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′
      → Le j (proj₁ (ψ ℓ o r B j w β x)) (proj₁ (ψ ℓ o r′ B′ j w β′ x′))
  ```
  白话：同层的底、起点、输入单调，两侧的表可以不同。从 `YiOGFold.fl` 搬来。

- **`inflA`**（YiLXFold）
  ```
  inflA : (ℓ : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ) {a : Tr j}
        → Le j a (proj₁ β) → Le j a (proj₁ (ψ ℓ o r B j w β x))
  ```
  白话：对一切层号（含 Ω 形状）、一切表，折叠不低于起点。

- **`prefix-zero`**（YiLXOne）
  `V.val zero (proj₁ (St.G.piece 0)) V.≼ V.val zero (proj₁ (St.T.piece 0))`
  白话：ActualMissing 的前缀 0，由 `climbₒ` 得到。

- **`prefix-one`**（YiLXOne）
  `V.val zero (proj₁ (St.G.piece 1)) V.≼ V.val zero (proj₁ (St.T.piece 1))`
  白话：前缀 1，底前提来自 `YiOGBaseAll.base-transfer-one`。

- **`source-wet`**（YiLXOne）
  `Self.Dry (C.g 1) (proj₁ Self.source-next) → ⊥`
  白话：源前缀 2 的那个底分量不满足 `Dry`。

- **`no-base-dry`**（YiLXOne）
  ```
  no-base-dry : ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′)
    → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self)))
    → St.G.base-at 2 ⊴ OP.pull-base v B′ → ⊥
  ```
  白话：任意对齐下，只要拉回的那个分量满足 `Dry`，源前缀 2 就不满足底前提。

- **`no-base-two-at0`、`no-base-two-at1`**（YiLXOne）
  ```
  St.G.base-at 2 ⊴ OP.pull-base {b = C.h 0} self (St.T.base-at 0) → ⊥
  St.G.base-at 2 ⊴ OP.pull-base {b = C.h 1} (inc tt self) (St.T.base-at 1) → ⊥
  ```
  白话：对齐到目标前缀 0、1，无条件否定。

- **`no-base-two`**（YiLXOne）
  `Self.Dry (C.g 1) (proj₁ Self.target-next) → St.G.base-at 2 ⊴ OP.pull-base v2 (St.T.base-at 2) → ⊥`
  白话：对齐到目标前缀 2 的条件否定。条件未证，它是否成立是判断。

**与已有结果的特例关系：**
- `v = self` 时就是 `YiOGFold.fl` 取 `x = x′ = Ωt ℓ`。
- 后继层一步即 `YiOGRelPeel.peel-from`。
- 前缀 1 的底前提正是 `YiOGTransfer.BaseTransferOne`，起点前提是 `YiOGActual.beta-one`。
- 前缀 2 在槽位 `inc tt self` 上的分量正是 `YiOGSelf` 的 `source-next` 与 `target-next`。
- `climb` 只在"标准 Ω 树 ◃ suc (next⁺ b)"这种锚点上用第一位置序，不走 `YiTYNoDirect.no-direct` 否定的那种直接比较。

#### 4. 第一个障碍

障碍在 `YiLXOne.no-base-dry`，具体是源前缀 2 的底分量 `St.G.base-at 2 (C.g 1) (inc tt self)`：
- 这个分量等于 `YiOGSelf.source-next`，它的第一分支含 `source-carry`，即嵌进第 2 层、分支取值在第 0 层的 Ω 结点。所以它不满足 `Dry`（`source-wet`）。
- `Dry` 沿 `Le` 向下封闭（`YiOGSelf.down`）。
- 源折叠 `Ωt (C.g 2)` 一定读这个分量。

这是数学上（`Le` 这个关系本身）挡住的，不是工程上。判断：它挡住的是所有经同层 `fl` 的 `Le` 证法，不只 `climb`。

#### 5. 偏离与事故

- **第 0 步的时限与 251。** 第 0 步的临时文件约第 35 分钟才第一次编译（超出 30 分钟），先退出 42（`Set₁` 应为 `Set`），改后在 8G 撞 251（约 10 分钟）。没有原样重跑，按 C-9 改了形状：源层合法性证据改作变量加等式（`climbₒ`），实例里用 `subst₂` 代替 `rewrite`。实测：等式单独 1.8 s，实例 2.2 s。把 251 归因于"检查器比较写法不同的 `Ok` 证据下的两个 `ψ` 项"是判断，没有做 profile。
- **顺序偏离。** `YiLXFold` 与 `YiLXClimb` 是在第 0 步编译期间写的，`YiLXClimb` 先于"n = 1 前提可满足"的检查编译通过。
- **陈述比第 0 步草案更一般。** `NoΩ` 从目标层移到源层，并加了 Ω 形状结点的一步（`fΩ`、`fΩu`）。
- **重复代码。** `YiLXFold` 逐行搬了 `YiOGFold.infl/fl`（约 70 行），只把表换成变量，文首注明了来源。
- **没有读、只凭转述的东西：**
  - A 路的纸面反例与 Fable 对陈述草案的审核，只凭简报；
  - `YiTNLocal`、`YiTQChain`、`YiTNShift`、`YiTMInner`、`YiVRRead` 没读；`YiTZLocal`、`YiTNShape` 只检索了定义；`YiKAMono` 只用了 `le◃`；
  - `YiMXNote`、`YiKWObjects` 没用到。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：摆脱侧，折叠对字面路径与底的单调（一般形式，不读记号）（前缀 YiLX，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。作者 2026-11-16 定：主线停止逐项攻法，改攻一条整体引理；本路是同批四路之一，选项原文 "摆脱侧：字面路径单调的一般形式 (Recommended)"。AGENTS 目标 "让树自足"、"攀爬与摆脱翻译要平衡"（1:1）：本路是这一批的摆脱侧，要交**主线会引用的**树侧编译事实，不读记号。另三路与你互不导入。

#### 背景
- 主线块与折叠：`YiRWBlock`、`YiRWOps`、`YiRWPath`（路径 `_≤_`、`inc`/`inu`/`ink`、`Ok`）、`YiRWFold`（`Base`、`B₀`）、`YiTBRow.ψ`（`mono` 只管 `◃`）、`YiMTTab.rbᶻ`；树侧的值 `YiVWVal`；树侧的模拟关系 `YiVRRel`（`Le ℓ = LeS (Sig ℓ) (LB ℓ) (LC ℓ)`）、`YiVRFold`、`YiVRRead`、`YiKAMono`。
- 这条线已有的件（都不读记号，导入闭包干净）：`YiTYPath`（沿字面路径嵌入再折到第 0 层，等于在源层直接折叠）、`YiOFPath`（带上下文：保留沿路径拉回的 `Base` 与原 β）、`YiOGFold`（`NoΩ` 层号上最小表折叠保持 `YiVRRel.Le` 的底、起点与输入关系）、`YiOGState`、`YiOGPeel`、`YiOGRelPeel`、`YiOGFirst.prefix-one`（两条具体链的第 1 个前缀）、`YiOGSelf`（编译否定：一条加强的分量保持律不成立）、`YiTYNoDirect.no-direct`（不能直接用第一位置证据调 `mono`）。
- 另一路正在把 "以树侧值序为前提的下标单调" 编成否定（A 路的纸面反例）；所以本路的前提**必须是字面路径**（`◃→⊑` 生成的 `⊑`、`P._≤_`）或模拟关系 `Le`，不是值序。
- Fable 审核 A 路的陈述草案（判断）：对字面路径 ℓ ⊑ ℓ′ 与逐点不低（按 `Le`）的底，`val zero (折 (Ωt ℓ)) ≼ val zero (折 (Ωt ℓ′))`；难点：对底的单调需要内链上 G 的单调，是互递归。

#### 要做的（按序）
0. **最小检查**：写出一般陈述（层号、路径、两份底、表、目标层都是变量），列出它对 `YiOG*` 已有结果的特例关系；在 `YiOGFirst` 的对象上确认可满足。不读记号。不成立就停下回报。
1. **证一般形式**：对路径（或层号的形状）归纳，与内链 G 的单调互递归；量化域先取 `NoΩ` 层号，再看含 `sΩ zero` 结点的层号能否纳入。
2. **实例化**：得到 `YiOFLocal.ActualMissing` 的一切前缀（从而 `Offset`、`Cover`），说明末端读记号只一次。
3. 交翻译账：用到树的哪些构造；这条定理在整体引理里是哪一块（判断即可）。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 8G（另有三路与主审在编）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
- **停下的条件**：退出 251 时不原样重跑，先按 C-9、C-10、S-1 改形状并定位（附 profile 或二分数据）；改过形状后同一上限仍撞墙才停。同一处两次重新设计仍过不了检查器也停。若某一步要改树、折叠或合法性的定义，停下回报。没有编译的否定时只写 "未走通"。
- **过程**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。动手证一般形式之前先用临时文件检查前提可满足；已有引理先检索（`grep`）再写，不重证，搬来的证明在文首写明来源。查签名用检索，不整篇读大文件。
- 不在你的临时目录与你前缀的新文件之外写、删、移任何东西；不 `pkill`，不写 `/tmp`，不装包，不提交，不改 `probes/README.md`、`probes/LOG.md`、台账与留档。
- **两条已更正的事实**（不要再照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧非标准形项的项序单调，**不是**树侧折叠的跨层单调（树侧跨层单调目前没有编译的否定）；`YiKWObjects.kept` 是新封装的对象，与 `YiC1Slot` 不透明块里的 `kept` 不是同一个。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0；文首标 "不读记号" 的文件用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包。

#### 回报（最后一条消息就是回报，主审会原样留档）
1. 判决：先说对纲领与目标意味着什么；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理；是数学上挡住还是工程上挡住。
5. 偏离与事故；没有读、只凭转述引用的东西。
不用 "只差"、"自然" 一类形容；判断与定理分开写。


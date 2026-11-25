# 换基的定义侧小检验 (YiRD)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-14 06:52 至 07:12 |
| 工具调用 / agda 编译 (粗数) | 47 / 13 |
| token (usage 字段，按消息去重) | 输出 127720；新写入缓存的输入 235905；读缓存的输入 4756155；其余输入 64 |
| 写过的仓库文件 | `YiRDFold.lagda.md`, `YiRDLvl.lagda.md` |
| 文件前缀 | `YiRD` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第三十九批 YiRD 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 目标层 ⊕ c 写成折叠的一行 (YiRDFold), 不改块不加证据字段, 调用已定义的 YiRWFold.ψ; k ≤ j 由 YiAltCmp.cmp 部分读出: 塔第 1 项一切目标路径 (cmp-z, row-1), 塔第 2 项起路径停在偏移部分时 (cmp-up, row-up), 进下标层时读不出, 退回原行 (in-2, row-in), 目标第 0 层时不存在 (no-kj); 层号偏移对一切参数 (off-all, same, differ): 兄弟孩子比目标层 ⊕ c 高 d 层 (c′ = d + m); 停机: 调用自身不过 (有限测试), 加 ℕ 分层参数可过; 两件 6G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定与原则（2026-11-14，选项原文或原话）
- 换基："先不定，两种都推到塔第 2 项再比"。
- 本批："先 (1)，并行一路定义侧小检验 (Recommended)"。本路就是那一路定义侧小检验，选项说明原文："另一路只查目标层 ⊕ c 在塔第 2 项能否带证据写出、或改块后能否写成一行，并把两者在已知形状不同处的层号偏移编译出来（不涉及值）"。
- 原则："折叠是FGH在更高层次的推广……顺着原来的脉络看, 看是否自然……如果实在分不出, 就交给我来决定"。选哪种由作者定，本路只交事实。
- 原则："不能以'追求同步'为名反过来指导树的定义形状"。
- 本路**不涉及值**；值的判据另有一路（前缀 YiRL）在做，不要碰它的文件和题目。

###### 已有的东西（主审复核过）
- 主线精简块 `probes/OCF/Lean/YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`。要换的是 `YiRWFold` 第 94–95 行附近 "Ω 形状层号、目标经指定孩子 c′、嵌入在孩子 c" 那一行。
- **兄弟孩子 c′ + c**：`YiRBSib`（定义候选，能写成折叠的一行；证据 `Rb`，塔上是闭项 `rb-tw`；`row-tw`、`row-no`）。
- **目标层 ⊕ c**：
  - 第十八次审查的临时试验：`probes/Survey/Reports-2026-11-12/attachments/Review18-R18Rebase.agda.txt`；台账 `probes/Survey/IdeaLedger.md` V149，推论是要改块，把嵌入字段改成一族 `(d : Tr k) → Tr (h (d + c))`，或带证据。
  - YiRB 的停机试验 `attachments/YiRB-RBTerm.agda.txt`：把调用换成 `ψ (j ⊕ ↑ k c) …` 后 `TerminationIssue`，只试了这一种写法。
  - YiRB 的原型 `YiRBCrit.seenʳ : (j : L) → Ok j → Tr⁺ j → Tr zero → Tr⁺ j`：调用现成折叠，要 `Ok j` 与 `k ≤ j`；下标层是第 0 层时后者是 `z≤ j`。回报 `Reports-2026-11-12/YiRB.md` 原文："塔第 2 项起 `k ≤ j` 没有来源（判断），要么带证据，要么改块"。
- **已知形状不同的一处**：`YiRBCrit.lvlˢ : h₁ (nat 3 + nat 1) ≡ fn 4`，`lvlᵗ : two ⊕ ↑ zero (nat 1) ≡ fn 3`。配置是目标在孩子 3 里的第 2 层、嵌入在孩子 1。

###### 要做的（按序）
1. **目标层 ⊕ c 能否写成折叠里的一行。**
   - (a) 先试别的写法能否过停机检查：换递归的度量；把对 `ψ (j ⊕ ↑ k c)` 的调用改成对已定义函数的调用；或把这一行拆成辅助函数。每种写法放临时文件，记退出码与首个错误。
   - (b) 在塔第 2 项上，写出它需要的证据（`k ≤ j`、`Ok j` 等）的精确类型，查现有的块与证据能不能给出（例如塔上的闭项证据 `Ok-tw`、`rb-tw` 的同类构造）。能给出就写出闭项；不能就说清缺哪一项。
   - (c) 只在 (a)(b) 都不行时：在临时目录写改块的最小原型（嵌入字段改成一族），只查类型与停机，不往下做。标明是改块。
2. **层号偏移的形状定理**（`refl` 级别，不涉及值）：在已知形状不同的那类配置上，即目标在孩子 c′ 里的第 j 层、嵌入在孩子 c，对一小族参数（c′、c 取几个自然数），编译出两种写法各在哪一层上折，与 "孩子 c 自己的层" 和 "目标层" 各差几层。说明这些差在基本列上意味着什么（一句话，标判断）。
3. 交一张事实表：两种写法在塔第 1、2 项上 "能否写成一行""需要的证据""是否改块""层号偏移"，各格标档（编译定理 / 有限测试 / 判断）。

**纪律**（作者同意的，必须照做）：
- 先查已有的东西，不重做 YiRB 已做的事。
- 不改任何已有文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiRD`（模块名 `OCF.Lean.YiRD…`）。不碰 `src/`、`archive/`。定义候选文件文首标明 "定义候选（换基），未经作者采纳"，形状定理文件标明是验收文件。只交编译过的；停机失败的试验留在临时目录，在回报里列出路径。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。另一路执行方也在编译，不用 `--ignore-interfaces`，只删自己模块的 `.agdai`。不用 `--interaction`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量，执行前核对路径。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时。
- 临时目录：`<实验目录>/agents/rd`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：每种写法最多两次重新设计；6G 仍耗尽就停。没有编译的否定时只写 "未走通"。停机检查失败只是有限测试，不是否定。
- **过程要求**：第一个临时文件 20 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：目标层 ⊕ c 能否写成一行（试过的写法与结果）；塔第 2 项上的证据；层号偏移；事实表；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**这对纲领与目标意味着什么。** "目标层 ⊕ c" 这种换基写法可以写成折叠里的一行，不用改块，也不加证据字段（编译定理）。前提是这一行调用已经定义好的主线折叠 `YiRWFold.ψ`，不调用正在定义的 ψ 自己。它需要的 `k ≤ j`（下标层在目标层之下，这里指一条路径）由现成的 `YiAltCmp.cmp` 读出：`cmp` 比较两条已给出的路径，一条是 `Ok` 里自带的 `k ≤ h c′`，一条是目标路径；遇到 Ω 形状上两条都经指定孩子时交 `nothing`，不比较孩子下标。
- 塔第 1 项上，一切目标路径都能读出。
- 塔第 2 项起，目标路径停在偏移部分时能读出；目标路径进了下标层时读不出，这一行退回原来那一行。

YiRB 回报说 "塔第 2 项起 `k ≤ j` 没有来源（判断）"，台账 V149 推论 "要改块"（判断）。对塔各项，这两条现在被编译的构造取代：上面所说的部分来源。V149 的推论对非塔的一般块是否仍成立，没有检验。

**(a) 能否过停机检查。** 都是临时文件，结果是有限测试。
| 写法 | 文件 | 退出码 | 首个错误 / 内存 |
|---|---|---|---|
| T1：拆成互递归里的辅助函数 `reb`，仍调用同一个 ψ | `<实验目录>/agents/rd/RDT1.agda` | 42 | `TerminationIssue`：`ψ, reb`；问题调用含 `ψ (j ⊕ ↑ k c) … (proj₁ (Ωt (j ⊕ ↑ k c)))` |
| T2：换度量，加 ℕ 分层参数 κ；换基一行在第 suc κ 层调用第 κ 层，第 0 层回退 | `<实验目录>/agents/rd/RDT2.agda` | 0 | 188MB |
| T3：调用已定义的 `YiRWFold.ψ`（就是仓库里的 `YiRDFold`） | `<实验目录>/agents/rd/RDT3.agda` | 0 | 152MB |

日志在同目录的 `*.log`。T2 要在闭项处给定 κ，取哪个 κ 没有答案（判断）。T3 在换基后的层里再遇到同一配置时走主线回退（由定义），相当于 T2 取 κ = 1（判断）。YiRB 的 `RBTerm` 没有重跑，结果引自其回报。

**(b) 塔第 2 项上的证据。** k = `tw 1`，`h c = tw 1 ⊕ ↑ (tw 1) c`。
- `Ok j`：`Ok-≤ (h c′) (proj₂ o c′) v`，对一切 c′ 与 v 都给得出（`YiAltCmp` 现成）。
- `Ok k`：`Ok-tw 1`。
- `Ok (j ⊕ ↑ k c)`：`Ok⊕ j (↑ k c) (Ok j) (OkO↑ j k (Ok k) u c)`。
- `k ≤ j`：`cmp (h c′) (proj₂ o c′) (lift (tw 1) (↑ (tw 1) c′)) v : Maybe (tw 1 ≤ j)`，部分地给出：
  - 路径形如 `wk (⊕⊑ (tw n) u)` 时交 `just`（`cmp-up`，`row-up`，对一切 n）；
  - 路径进了 `tw 1` 时交 `nothing`（实例 `in-2`）；
  - 目标是第 0 层时，`tw 1 ≤ zero` 根本不存在（`no-kj`）。
  - "停在偏移部分的路径都是 `wk (⊕⊑ …)` 形" 是判断，没有编译。

**(c)** (a)(b) 都已走通，没有写改块原型。

**层号偏移。** 配置：塔第 n+1 项，孩子都是自然数，c′ = d + m，目标是孩子 m 的层，嵌入在孩子 c = b。对一切 n、d、m、b 都是编译定理：
| 写法 | 比孩子 c 的层 | 比目标层 |
|---|---|---|
| 兄弟孩子 | 高 c′ 层 | 高 d + b 层 |
| 目标层 ⊕ c | 高 m 层 | 高 b 层 |
- 兄弟孩子比目标层 ⊕ c 高 d 层；d = 0 时两层相同（`same`），d ≥ 1 时不同（`differ`）。
- 已知的一处 (c′, m, c) = (3, 2, 1)：兄弟孩子在 `st 4 (tw n)` 上折，目标层 ⊕ c 在 `st 3 (tw n)` 上折，塔第 1、2 项都是这样。

**基本列上的意思（判断）：** 嵌入块那一项用到的层号，在兄弟孩子写法里随目标路径所经的孩子 c′ 变；同一目标层 m 经更深的孩子到达时高 d 层。目标层 ⊕ c 写法只随 m 与 c 变。

**事实表**
| | 兄弟孩子 c′ + c（`YiRBSib`） | 目标层 ⊕ c（`YiRDFold`） |
|---|---|---|
| 塔第 1 项：能否写成一行 | 能（`YiRBSib.ψ`；编译，前序主审已复核） | 能，调用 `YiRWFold.ψ`（编译）；调用自身不过停机（有限测试） |
| 塔第 1 项：证据 | `Rb`，`rb-tw 1` 是闭项（编译） | 无新字段；一切目标路径都读出 `k ≤ j`（`cmp-z`，`row-1`，编译） |
| 塔第 2 项：能否写成一行 | 能（`row-tw`，`rowˢ-321`，编译） | 能（`row-up`，`rowᵗ-321`，编译） |
| 塔第 2 项：证据 | `rb-tw 2` 是闭项（编译） | 停在偏移部分读出（`cmp-up`，编译）；进下标层读不出、回退（`in-2`，`row-in`，编译）；目标第 0 层时 `k ≤ j` 不存在（`no-kj`，编译）；"偏移部分的路径都是此形"（判断） |
| 是否改块 | 否（编译：导入闭包里只有原块） | 否（编译：导入闭包里只有原块） |
| 层号偏移 | 比孩子 c 层高 c′，比目标高 d + c（`off-all`，编译） | 比孩子 c 层高 m，比目标高 c（`off-all`，编译） |
| 两者之差 | 兄弟孩子高 d 层；d = 0 相同，d ≥ 1 不同（`same`，`differ`，编译） | 同左 |

**列问题**
| 问题 | 位置 | 档 |
|---|---|---|
| 换基层里的嵌套配置走主线回退；T2 能嵌套 κ 层，但闭项取哪个 κ 未定 | `YiRDFold` 那一行；T2 临时文件 | 定义事实 / 判断 |
| `YiRBCrit.tgt-crit` 证的是原型 `gᵗ`（`seenʳ`），不是 `YiRDFold` 的行。两者差在：`R.ψ` 对 `YiRBSib.ψ` 带 `rb-no`；`Ok` 的项不同。认为相等要函数外延，没有编译。值那一路（YiRL）不能直接引用 | `YiRBCrit` 对 `YiRDFold` | 判断 |
| `cmp` 派发是否对上 `obs→dec` 一族的前提：它只比较两条给定路径，Ω 形状 inc/inc 处交 `nothing`，不判等孩子，也不要求 "能保留处都保留" | `YiAltCmp.cmp` | 判断，未对照编译 |
| 塔上 `cmp` 读不出时 `k ≤ j` 是否一概不存在：只对目标第 0 层编译了 | `no-kj` | 编译（部分），其余判断 |
| ℕ 极限或 Ω 形状的孩子的层号偏移 | `YiRDLvl` 未覆盖 | 未做 |
| 非塔的块上 `Ok` 的 `k ≤ h c` 不是 `lift` 形时读出多少，没查；V149 "要改块" 对这类块是否仍成立未定 | — | 判断 |

#### 2. 文件表
| 文件 | 代码行（非空） / 总行 | 冷编退出码 | 最大驻留 |
|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiRDFold.lagda.md`（定义候选（换基），未经作者采纳） | 131 / 183 | 0 | 261MB |
| `<仓库>/probes/OCF/Lean/YiRDLvl.lagda.md`（验收文件：形状，不读记号，不涉及值） | 133 / 199 | 0 | 166MB |

- 冷编前只删了这两件自己的 `.agdai`（`probes/_build/2.8.0.2/agda/OCF/Lean/` 下），两件依次编译，堆上限 6G；每个日志里只有自己模块的 `Checking` 行。
- 禁用构造检索为 0；仓库文件里没有本机路径。
- `importclosure.py` 对两件都是 OK，禁用表命中 0；闭包里只有 `YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`、`YiAltCmp`，`YiRDLvl` 另有 `YiRBSib`、`YiRDFold`。

#### 3. 定理表
| 名字 | 逐字的陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `ψ` 那一行 | `ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) = cM (cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v) (λ u → R.ψ (j ⊕ ↑ k c) (Ok⊕ j (↑ k c) (Ok-≤ (h c′) (proj₂ o c′) v) (OkO↑ j k (proj₁ (proj₁ o)) u c)) (B₀ (j ⊕ ↑ k c)) j (lift j (↑ k c)) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x) (proj₁ (Ωt (j ⊕ ↑ k c))) ⊞ ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y) (ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ (h c) (proj₂ o c) (B₀ (h c)) zero (z≤ (h c)) (Ωt zero) y)` | 目标层 ⊕ c 写成一行（定义，`mono` 同时过） | YiRDFold | 编译 |
| `twᵈ`, `EBOᵈ` | `twᵈ : ℕ → Tr zero`；`EBOᵈ : Tr zero` | 闭项，无前提 | YiRDFold | 编译 |
| `cmp-up` | `(a : L) {b′ b : L} (o : Ok (a ⊕ b)) (u : b′ ⊑ b) → cmp (a ⊕ b) o (lift a b) (wk (⊕⊑ a u)) ≡ just (lift a b′)` | 停在偏移部分的路径读出 `a ≤ j` | YiRDFold | 编译 |
| `no-kj` | `(n : ℕ) → tw (suc n) ≤ zero → ⊥` | 塔第 2 项起，目标第 0 层时没有 `k ≤ j` | YiRDFold | 编译 |
| `cmp-z` | `(b : L) (o : Ok (zero ⊕ b)) {j : L} (v : j ≤ zero ⊕ b) → Σ (zero ≤ j) λ u → cmp (zero ⊕ b) o (lift zero b) v ≡ just u` | 下标层是第 0 层时一切路径都读出 | YiRDFold | 编译 |
| `cM-just` | `∀ {A X : Set} {m : Maybe A} {a : A} (F : A → X) (d : X) → m ≡ just a → cM m F d ≡ F a` | 小工具 | YiRDFold | 编译 |
| `row-up` | `∀ n (B : Base (tw (suc n))) c′ {b′ : L} (u : b′ ⊑ ↑ (tw n) c′) β x c y e → ψ (tw (suc n)) (Ok-tw (suc n)) B (tw n ⊕ b′) (inc c′ (wk (⊕⊑ (tw n) u))) β (up x c y e) ≡ R.ψ ((tw n ⊕ b′) ⊕ ↑ (tw n) c) (Ok⊕ (tw n ⊕ b′) (↑ (tw n) c) (Ok-≤ (tw n ⊕ ↑ (tw n) c′) (proj₂ (Ok-tw (suc n)) c′) (wk (⊕⊑ (tw n) u))) (OkO↑ (tw n ⊕ b′) (tw n) (Ok-tw n) (lift (tw n) b′) c)) (B₀ ((tw n ⊕ b′) ⊕ ↑ (tw n) c)) (tw n ⊕ b′) (lift (tw n ⊕ b′) (↑ (tw n) c)) (ψ (tw (suc n)) (Ok-tw (suc n)) B (tw n ⊕ b′) (inc c′ (wk (⊕⊑ (tw n) u))) β x) (proj₁ (Ωt ((tw n ⊕ b′) ⊕ ↑ (tw n) c))) ⊞ ψ₀ᵈ (tw n ⊕ ↑ (tw n) c) (proj₂ (Ok-tw (suc n)) c) y` | 塔各项上，路径停在偏移部分时那一行是换基的折叠 | YiRDFold | 编译 |
| `row-1` | `∀ (B : Base (tw 1)) j c′ (v : j ≤ zero ⊕ ↑ zero c′) β x c y e → ψ (tw 1) (Ok-tw 1) B j (inc c′ v) β (up x c y e) ≡ R.ψ (j ⊕ ↑ zero c) (Ok⊕ j (↑ zero c) (Ok-≤ (zero ⊕ ↑ zero c′) (proj₂ (Ok-tw 1) c′) v) (OkO↑ j zero tt (proj₁ (cmp-z (↑ zero c′) (proj₂ (Ok-tw 1) c′) v)) c)) (B₀ (j ⊕ ↑ zero c)) j (lift j (↑ zero c)) (ψ (tw 1) (Ok-tw 1) B j (inc c′ v) β x) (proj₁ (Ωt (j ⊕ ↑ zero c))) ⊞ ψ₀ᵈ (zero ⊕ ↑ zero c) (proj₂ (Ok-tw 1) c) y` | 塔第 1 项上那一行总是换基 | YiRDFold | 编译 |
| `row-in` | `∀ k h (o : Ok (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) j c′ (v : j ≤ h c′) β x c y e → cmp (h c′) (proj₂ o c′) (proj₂ (proj₁ o) c′) v ≡ nothing → ψ (nd (sΩ k) h) o B j (inc c′ v) β (up x c y e) ≡ ψ (nd (sΩ k) h) o B j (inc c′ v) β x ⊞ ψ₀ᵈ (h c) (proj₂ o c) y` | 读不出时是原来那一行的形状 | YiRDFold | 编译 |
| `in-2` | `cmp (tw 1 ⊕ ↑ (tw 1) (n̂ 3)) (proj₂ (Ok-tw 2) (n̂ 3)) (lift (tw 1) (↑ (tw 1) (n̂ 3))) (z≤ (tw 1 ⊕ ↑ (tw 1) (n̂ 3))) ≡ nothing` | 塔第 2 项上路径进下标层的一例，读不出 | YiRDFold | 编译（refl） |
| `off-all` | `∀ n d m b → Off n d m b`，其中 `Off n d m b = (sibL n (nk (tw n) (d +ℕ m)) (nk (tw n) b) ≡ st (d +ℕ m) (hk n (nk (tw n) b))) × (sibL n (nk (tw n) (d +ℕ m)) (nk (tw n) b) ≡ st (d +ℕ b) (hk n (nk (tw n) m))) × (tgtL n (hk n (nk (tw n) m)) (nk (tw n) b) ≡ st m (hk n (nk (tw n) b))) × (tgtL n (hk n (nk (tw n) m)) (nk (tw n) b) ≡ st b (hk n (nk (tw n) m))) × (sibL n (nk (tw n) (d +ℕ m)) (nk (tw n) b) ≡ st d (tgtL n (hk n (nk (tw n) m)) (nk (tw n) b)))`；`sibL n c′ c = hk n (c′ + c)`，`tgtL n j c = j ⊕ ↑ (tw n) c`，`hk n c = tw n ⊕ ↑ (tw n) c`，`st n a` 是 a 上叠 n 层后继形状 | 五个偏移，对一切参数成立 | YiRDLvl | 编译 |
| `same` | `∀ n m b → sibL n (nk (tw n) m) (nk (tw n) b) ≡ tgtL n (hk n (nk (tw n) m)) (nk (tw n) b)` | d = 0 时两层相同 | YiRDLvl | 编译 |
| `differ` | `∀ n d m b → sibL n (nk (tw n) (suc d +ℕ m)) (nk (tw n) b) ≡ tgtL n (hk n (nk (tw n) m)) (nk (tw n) b) → ⊥` | d ≥ 1 时两层不同 | YiRDLvl | 编译 |
| `i₁`…`i₇`, `j₁`…`j₇` | `Off 0 d m b` 与 `Off 1 d m b`，(d, m, b) ∈ {(1,2,1), (0,2,1), (1,2,0), (1,2,2), (2,2,1), (3,1,2), (2,3,3)} | 塔第 1、2 项各七组 | YiRDLvl | 编译（refl） |
| `lvl₁`, `lvl₂` | `sibL 0 (nk zero 3) (nk zero 1) ≡ st 4 zero × tgtL 0 (hk 0 (nk zero 2)) (nk zero 1) ≡ st 3 zero`；`sibL 1 (nk (tw 1) 3) (nk (tw 1) 1) ≡ st 4 (tw 1) × tgtL 1 (hk 1 (nk (tw 1) 2)) (nk (tw 1) 1) ≡ st 3 (tw 1)` | 已知一处的两个层号 | YiRDLvl | 编译（refl） |
| `rowˢ-321`, `rowᵗ-321` | 塔第 2 项，目标 `hk 1 (nk (tw 1) 2)`，路径 `inc (nk (tw 1) 3) (inc tt self)`，嵌入 `nk (tw 1) 1`：兄弟孩子那一行 ≡ `S.ψ (st 4 (tw 1)) …`，目标层 ⊕ c 那一行 ≡ `R.ψ (st 3 (tw 1)) …`（全文见文件末节） | 两行各在哪一层上折 | YiRDLvl | 编译 |

#### 4. 偏离与事故；只凭转述引用的东西
- 第一次编译 T3 时套了 `/usr/bin/time`，它在沙箱里失败（`sysctl`），退出码 1 掩盖了 agda 的退出码；改用 `+RTS -s` 重跑。临时编译起初漏了 `-W noUnsupportedIndexedMatch`，那次只多出警告。
- `YiRDFold` 中途两次编译退出码 42（`cong (λ m → cM m _ _)` 的元变量解不出），改用 `rewrite` 与 `cM-just` 后通过。
- 没有改任何已有文件；只新建了两件仓库文件和临时目录里的文件。git 里已修改的 `AGENTS.md` 等是本路开始前就有的改动。
- 没有读全文、只凭检索片段或转述引用的：
  - `Review18.md`、`Review19.md` 两份回报；
  - `YiRB.md` 只读了检索到的行；
  - 台账 V146、V149、V153、V154 是检索出的行；
  - `branch→wdec`、`hand→wdec`、`viaE→dec`、`full→dec` 的陈述没读，只读了 `YiAbsObs` 文首与 `obs→dec`；
  - `YiCLFam` 只查了 `nat`、`fn`；`YiAltFold` 只读了文首与那一行；
  - `RBTerm` 的退出码引自 YiRB 回报。

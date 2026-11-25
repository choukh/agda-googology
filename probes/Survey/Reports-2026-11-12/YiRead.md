# 第 1 层定义的人类可读性重构 (YiRead)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 03:09 至 03:22 |
| 工具调用 / agda 编译 (粗数) | 25 / 6 |
| token (usage 字段，按消息去重) | 输出 84957；新写入缓存的输入 155193；读缓存的输入 2014198；其余输入 38 |
| 写过的仓库文件 | `YiReadCheck.lagda.md`, `YiReadCore.lagda.md` |
| 文件前缀 | `YiRead` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 第 1 层定义的可读重写返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 英文全词命名的可读重写，与原定义一一对应，切片 147 行；新旧结构对应（塔与 Λ），不是翻译函数；两件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的原话: **"对ψ₀(Λ) 新树的第 1 层定义代码做人类可读性重构, 要求每一个命名都能读出意义, 而不要全是读不出的缩写"**. 主审会从头冷编译复核你交的文件. 全程用中文写文件与回报.

#### 0 对象

ψ₀(Λ) 新树的第 1 层 (类型与基本运算的定义) 就是 `probes/OCF/Lean/YiNextCore.lagda.md` 的全部定义 (约 114 行代码): 通用的树 `G.R` (zero / suc / lim / lc / em / top), 层号 `LF` 与一组归纳递归的函数 (`Lay`, `Pre`, `Lo`, `Kid`, `KS`, `Raw`, `layer`, `Dn`, `DnI`, `Lgl`, `up`, `upN`, `upT`), 第一位置序 `Le`, `Cp`, 读回与塔 `up`, `upN`, `upT`, `tw`, `Λ`, 加法 `acc`, `Bld`, `add`, `plus`. 先全读这个文件 (连讲解). 想知道这些东西在折叠里怎么用, 可以检索 `YiNextBase.lagda.md`, `YiLamFold.lagda.md`, 但不要整篇读.

另读 `AGENTS.md` 的 Agda 一节与 "研发阶段的文字预算".

#### 1 要交的

1. **新文件** `probes/OCF/Lean/YiReadCore.lagda.md` (模块 `OCF.Lean.YiReadCore`): 与 `YiNextCore` 定义上一一对应的重写. 要求:
   - **每一个命名都能读出意义**: 类型, 构造子, 函数, 记录字段, 模块, 模块参数, 以及模式里的约束变量 (至少是跨越多行的那些) 都改成能读出意义的名字, 不用读不出的缩写. 一致地用一种语言 (英文全词或中文词都可以, 选一种并在回报里说理由). 数学上的惯用符号 (例如 Ω, Λ, ψ 一类) 若保留, 只在它就是通行写法时保留, 并在回报的命名表里说明它读作什么.
   - **数学内容不变**: 同样的构造子, 同样的子句, 同样的归纳递归结构, 同样的选项 (`--safe --without-K --lossy-unification`). 可以重排声明顺序, 可以把长类型拆成有名字的辅助定义, 但不加新的数学内容, 不删任何定义.
   - 只导入标准库. 非验收文件, 文首写 "非验收文件".
   - 中文 literate Agda. **文字预算**: 文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由, 不复述代码. 命名的意义要靠名字本身读出来, 不靠注释.
2. **对应的检查** (新文件 `probes/OCF/Lean/YiReadCheck.lagda.md`, 可导入 `YiNextCore` 与 `YiReadCore`): 尽量给出编译过的对应, 证明重写没有改内容. 至少做到: 一个把新层号翻成旧层号的函数 (连同树的翻译, 归纳递归要一起翻), 以及 "新的塔与 Λ 翻过去就是旧的塔与 Λ" (能 `refl` 最好). 做不到完整的对应时, 说清做到哪里、卡在哪里; 这一步不要为了凑而写复杂的证明, 超过约 150 行就停下报告.
3. **命名表**: 只在回报里交一张表 (旧名, 新名, 一句读法), 不写报告文件.

#### 2 规则

- **只新建文件**, 前缀 `YiRead`. 不改任何已有文件 (包括 `YiNextCore`), 不碰 `src/`, `archive/`.
- 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`, 函数外延.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/read`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送, 不要把仓库整个拷到临时目录.
- 过程要求: 读完对象后尽快动手, 第一版在 25 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0; 跑 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.YiReadCore --only OCF.Lean.` 查导入闭包.

#### 3 回报格式 (只在回报里交一次)

1. 判决: 做到哪一步; 一段话说重写后的可读性 (选了什么语言, 保留了哪些符号, 为什么).
2. 文件表: 文件, 代码行数 (与旧文件的 114 行对比), 冷编译退出码, 是否验收文件, 导入闭包结果.
3. 命名表: 旧名, 新名, 一句读法. 全部列出.
4. 对应检查: 定理名, 逐字的陈述, 档 (编译定理 / 有限测试 / 判断).
5. 偏离与事故.

## 回报原文

#### 1 判决

全部做到了，只有一处没有照原样：要的那个“翻译函数”没有做，换成了编译过的结构对应。

- **`YiReadCore`**：与 `YiNextCore` 定义上一一对应的可读重写，冷编译退出码 0。构造子、子句与归纳递归结构都没变。只多了两个定义性缩写 `PositionTree`、`ChildTree`，它们就是旧的 `Lay.A (Lo x r)` 与 `Lay.A (KS x i)`。
- **`YiReadCheck`**：给出编译定理 `towerCorresponds`、`ΛCorresponds`，都无前提，档位是编译定理。它们说新塔与新 `Λ` 跟旧的 `tw`、`Λ` 处在结构对应关系 `Corresponds` 里。这不是相等，也不是翻译函数（原因见第 4 节）。

可读性：命名一律用英文全词。理由是标准库与 Agda 的现成名字都是英文（`ℕ`、`zero`、`suc`、`inj₁`、`Σ`），旧块的代码名也是英文缩写，改成中文标识符会和导入的名字混用，两种语言并存。
- 保留的符号只有 `Λ`：它就是 ψ₀(Λ) 的通行写法，读作“塔的上确界 Λ”。
- 标准库的 `ℕ`、`zero`、`suc` 不能改，照旧。
- ℕ 下标变量 `n` 保留，这是惯例。
- 树与层号的构造子用全词 `successor` / `limit` / `layerLimit`，读的时候能把 ℕ 上的 `suc` 与它们分开。
- 文中只在第一次出现时说明 `layerLimit` 是 Ω 结点、`top` 是一层的 Ω、`readBackTop` 是 Ω̂；其余意义都靠名字本身读出。

#### 2 文件表

代码行数按 agda 块里的非空行算。用同一口径，旧 `YiNextCore` 是 122 行（简报说约 114，可能口径不同）。

| 文件 | 代码行 | 冷编译 | 验收文件 | 导入闭包 (`--only OCF.Lean.`) |
|---|---|---|---|---|
| `probes/OCF/Lean/YiReadCore.lagda.md` | 155（旧 122） | 0 | 否（文首写明“非验收文件”） | 本地 1 个（只有自己）+ 标准库 6 个；禁用表命中 0，范围外 0，OK |
| `probes/OCF/Lean/YiReadCheck.lagda.md` | 156 | 0 | 否 | 本地 3 个（`YiNextCore`、`YiReadCore`、自己）+ 标准库 6 个；命中 0，OK |

- **行数增加的来源**：长行拆开；`Legal` 的 Ω 结点子句由 2 行拆成 7 行；两个缩写各占签名与定义。
- **冷编译做法**：删掉自己两个模块的 `.agdai`（字面路径）后，从 `YiReadCheck` 编译。最终日志只有两行 `Checking`：`OCF.Lean.YiReadCheck` 与 `OCF.Lean.YiReadCore`。
- **自查**：两个文件里 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`、函数外延、本机路径的检索命中都是 0。选项是 `--safe --without-K --lossy-unification`，与旧文件相同。

#### 3 命名表

模块、类型、构造子、字段：

| 旧名 | 新名 | 读法 |
|---|---|---|
| `G`（模块） | `Raw` | 一层的树的通用形状 |
| `G` 的参数 `P` / `L` / `K` / `B` | `Position` / `PositionTree` / `Child` / `ChildTree` | 位置集，位置上那一层的树，孩子集，孩子层的树 |
| `G.R` | `Raw.Tree` | 一层的树 |
| `G.zero` / `G.suc` / `G.lim` | `Raw.zero` / `Raw.successor` / `Raw.limit` | 零，后继，ℕ-极限 |
| `G.lc` | `Raw.layerLimit` | Ω 结点：在某位置那一层的每棵树上各有一支 |
| `G.em` | `Raw.embed` | 嵌入孩子层的树 |
| `G.top` | `Raw.top` | 这一层的 Ω |
| `LF` | `Level` | 层号 |
| `LF` 的 `zero` / `suc` / `lim` / `lc` | `zero` / `successor` / `limit` / `layerLimit` | 层号的零，后继，ℕ-极限，Ω 结点 |
| `Lay` / `lay` | `Layer` / `makeLayer` | 打包的一层 / 打包 |
| 字段 `A` | `Carrier` | 这一层的树 |
| 字段 `dn` | `strictlyBelow` | 严格第一位置序 |
| 字段 `lg` | `legal` | 合法 |
| 字段 `tp` | `top` | 顶，即 Ω |
| 字段 `rd` | `readBack` | 读回成层号 |

函数：

| 旧名 | 新名 | 读法 |
|---|---|---|
| `Pre` | `Position` | 层号的位置 |
| `Lo` | `positionLayer` | 位置上的那一层 |
| `Kid` | `Child` | 层号的孩子 |
| `KS` | `childLayer` | 孩子那一层 |
| `Raw` | `RawTree` | 层号上的树（未查合法性） |
| `layer` | `layerOf` | 层号自己那一层的打包 |
| `Dn` | `StrictlyBelow` | 严格第一位置 |
| `DnI` | `StrictlyBelowWithinChild` | 同一孩子里的严格第一位置 |
| `Lgl` | `Legal` | 合法 |
| `Le` | `AtOrBelowIn` | 打包层里的第一位置（相等或严格） |
| `Cp` | `AtOrBelow` | 层号上的第一位置（相等或严格） |
| `up` | `readBack` | 读回 |
| `upN` | `readBackLayerLimit` | 在位置上读回成 Ω 结点 |
| `upT` | `readBackTop` | 顶的读回，即 Ω̂ |
| `tw` | `tower` | 塔 |
| `Λ` | `Λ`（保留） | 塔的上确界 |
| `acc` | `accumulate` | 逐项累加 |
| `Bld` | `NodeBuilder` | 造结点的办法 |
| `add` | `addWithBuilder` | 带造结点办法的加法 |
| `plus` | `plus`（不变） | 加法 |
| （新增缩写） | `PositionTree`、`ChildTree` | 位置上 / 孩子上那一层的树 |

模式与约束变量：

| 旧名 | 新名 | 读法 |
|---|---|---|
| `k`（在 `suc k` 里） | `predecessor` | 前驱层号 |
| `k` / `g`（在层号 `lc k g` 里） | `indexLevel` / `branchLevel` | 下标所在层号 / 分支层号 |
| `f` | `sequence` | 序列 |
| `r` | `position` | 位置 |
| `g`（在树 `lc r g` 里）、`upN` 的 `h` | `branch` | 分支 |
| `η` / `η′` | `index` / `index′` | 分支下标 |
| `i` / `j` | `child` / `child′` | 孩子 |
| `Dn` 里的 `a` / `d` | `lower` / `upper` | 下面的 / 上面的 |
| 其余的 `a` | `tree` | 树 |
| `q` | `same` | 两个孩子相等的证明 |
| `x` / `y`（层号） | `level` | 层号 |
| `X` | `layer` | 一层 |
| `T` | `Value` | 累加的值的类型 |
| `acc` 的 `s` / `x` | `step` / `start` | 每一步 / 起点 |
| `add` 的 `M` / `k` / `B` | `target` / `source` / `build` | 目标层号 / 来源层号 / 造结点 |
| `add` 的 `x` / `a` | `left` / `right` | 左、右加数 |
| `l` | `legal` | 合法证明 |
| 累加里的 `λ i y` | `λ stage partial` | 第几步，部分和 |
| `n` | `n`（保留） | ℕ 下标 |

#### 4 对应检查（`YiReadCheck`）

**档位：编译定理，无前提。**

**定义。** `data Corresponds : New.Level → Old.LF → Set`：两边层号逐构造子对应。Ω 结点要求 `∀ index oldIndex → TreeCorresponds sameIndexLevel index oldIndex → Corresponds (branchLevel index) (oldBranchLevel oldIndex)`，即在对应的分支下标上分支对应。
- 与 `Corresponds` 一起递归定义的还有 `TreeCorresponds`、`PositionCorresponds`、`PositionTreeCorresponds`、`ChildCorresponds`、`ChildTreeCorresponds`。
- 旧侧的形状用等式 `old ≡ 构造子 …` 给出，证明里匹配 `refl`。
- 位置与孩子里的合法性证明不参与对应。

**陈述（逐字）：**
- `towerCorresponds : ∀ n → Corresponds (New.tower n) (Old.tw n)`
- `ΛCorresponds : Corresponds New.Λ Old.Λ`
- `readBackTopCorresponds : ∀ {level oldLevel} → Corresponds level oldLevel → Corresponds (New.readBackTop level) (Old.upT oldLevel)`
- `readBackCorresponds : ∀ {level oldLevel} (same : Corresponds level oldLevel) tree oldTree → TreeCorresponds same tree oldTree → Corresponds (New.readBack level tree) (Old.up oldLevel oldTree)`
- `readBackLayerLimitCorresponds`（`readBackLayerLimit` 对 `upN`）与 `childReadBackCorresponds`（孩子层的 `readBack` 对 `rd`），同一组互递归定理
- 对照：`zeroNotSuccessor : Corresponds New.zero (Old.suc Old.zero) → ⊥`，说明关系不是处处成立

**卡在哪里（判断，未形式化）。** 简报要的“新层号翻成旧层号的函数（连同树的翻译）”没有做：
1. 新层号 `layerLimit k g` 翻过去，要先把旧树翻回新树（`from`）。
2. 但 Ω 结点层号上 `embed` 的孩子 `(η , l)` 翻过去，落在旧层号 `g (from (to η))` 上，而手里的树在 `g η` 上。
3. 所以要来回复原 `from (to η) ≡ η`。树里有 ℕ-极限，这要 `limit (λ n → from (to (f n))) ≡ limit f`，不用函数外延证不出来，`refl` 更不可能。

因此改用结构对应，`refl` 只出现在匹配里。

**没覆盖的。** `Legal`、`StrictlyBelow`、`AtOrBelow` 与加法（`addWithBuilder`、`plus`、`accumulate`）的对应没做：检查文件已到约 150 行的上限，按简报停下。

#### 5 偏离与事故

- **偏离**：交的是对应关系，不是翻译函数（原因见第 4 节）。另外加了两个定义性缩写 `PositionTree`、`ChildTree`，文首已写明。
- **事故 1 次**：仓库库文件带 `--hidden-argument-puns`，`{n}` 被读成具名参数 `{n = n}`，退出码 42（`WrongHidingInLHS`）。改成 `{child = n}` 后通过。
- 没改任何已有文件，没碰 `src/`、`archive/`，没提交。临时日志都在 `<实验目录>/agents/read/`。

文件：
- <仓库>/probes/OCF/Lean/YiReadCore.lagda.md
- <仓库>/probes/OCF/Lean/YiReadCheck.lagda.md

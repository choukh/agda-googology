# 乙线折叠，否定路 (YiIrrNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-10 13:02 至 13:36 |
| 工具调用 / agda 编译 (粗数) | 40 / 11 |
| token (usage 字段，按消息去重) | 输出 215798；新写入缓存的输入 675311；读缓存的输入 4328464；其余输入 48 |
| 写过的仓库文件 | `YiIrrNeg.lagda.md`, `YiIrrNegDispatch.lagda.md`, `YiIrrNegForced.lagda.md`, `YiIrrNegLegal.lagda.md`, `YiIrrNegModel.lagda.md`, `YiIrrNegWide.lagda.md`, `YiIrrNegWideDecide.lagda.md` |
| 文件前缀 | `YiIrrNeg` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-10 晚: 否定路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 接口未被否定且有模型；定义域取整个 Only0 × Legal 时推出凭无关证据取数据的原则 (谓词太宽)；新块上合法性到 Λ；七件冷编退出码全 0 |

## 简报原文

你是 Agda 形式化研究的一路执行者 (否定路, 与另一条构造路配对, 共用同一个接口文件). 仓库: <仓库> (作者 choukh 的大数数学形式化). 请全程用中文思考与写作.

### 先读 (按顺序)
1. `AGENTS.md` (纲领与全部约定, 必须遵守; 特别是 "量化域先取带证据的读回域", "否定路线要有依据", "前提要可满足").
2. `probes/Survey/EBOHandbook.md` 的 §3.1, §4, §5.
3. `probes/Survey/RR5-SoftStops.md` 的 §1, §2, 与 `probes/Survey/Retro-2026-11-10.md` 的 §3 (此前十条 "否定" 都落在退化结点上的教训).
4. 三个已定稿、只增不改的文件: `probes/OCF/Align/RR5IrrCore.lagda.md` (块: 结点里的证据与分支守卫是无关参数), `probes/OCF/Align/RR5IrrCheck.lagda.md` (读回 `up`, `Ω̂`, `tw`, `Λ`, 以及已有的核对定理), `probes/OCF/Align/YiIrrIf.lagda.md` (**共用接口, 记录 `FoldRows`**).
5. 旧块上的先例: `YiK2bBase.lagda.md` (`certificate-coherence-required`), `YiK2cIrr.lagda.md`, `YiWallConditional.lagda.md` (`funext-fold-tree→wlpo` 及其探针), `YiCarryNeg.lagda.md` (`no-K2′`: 一条成功的接口否定), `YiK2Stop.lagda.md` (`no-start-all`).

### 背景
乙线 = "层号是树". 旧块上目标层 0 的折叠卡在 "证明被当成数据". 新块把证据标成 Agda 的无关参数, 主审的最小实验说明这一障碍在骨架一级不出现; 作者定无关参数可进成品候选. 构造路正在实填 `YiIrrIf.FoldRows` (目标层 0 的完整递归 ψ: 零给 1; 后继给 `successor`; ℕ 极限逐项; 层号 0 的 Ω 结点走加法链, 从下界自身起步; 证书参数无关; 定义域 `Dom` 是记录字段, 必须对分支遗传并含规范 Ω₁ 即 `tw 2`).

### 你的目标: 对同一接口写否定, 或给出它经得住哪些攻击的编译证据
按下面的次序做, 每一项都要么得到编译过的定理, 要么如实写 "未找到".

1. **接口本身.** 试证 `FoldRows → ⊥`, 或 `FoldRows → WLPO` (不带 Funext; 带 Funext 的版本必须标 "条件" 并单独成文件). 注意 `Dom` 被遗传性强迫包含的对象: `tw 2` 的每个分支, 即一切合法正坐标的读回, 其中有退化坐标 (常值极限等). 对这些被强迫进入定义域的对象, 逐个字段检查: `fold-legal`, `fold-positive`, `next-grow`, `gt-row`, `position` 之间有没有矛盾.
2. **"证明当数据".** 主审的判断是: 这个折叠处处只需要在无关位置使用证明. 找反面: 有没有哪个字段, 在任何实例里都迫使输出依赖守卫证明或证书的内容 (在新块里这将与类型矛盾, 于是得到 `FoldRows → ⊥`)? 或者反过来证明这种依赖不可能出现的精确陈述.
3. **大定义域.** 构造路会先试 `Dom x = Only0 x × Legal x` (整个合法片段). 找一棵满足 `Only0` 与 `Legal` 的树, 使四行加 `fold-legal` 或 `position` 不能同时成立. 这样的结果要如实标注: 反例对象是否在规范构造的读回域内; 不在的, 读作 "这个定义域太宽", 不读作乙线的障碍. **同形的退化反例最多写两条**, 之后改查量化域.
4. **块本身.** 旧块有 `Legal x → Legal (Ω̂ x)` 对一切 x (`LevelFixVal.Legal-Ω̂`). 在新块上 (用 YiIrrIf 的 `Legal`) 找 `Legal x` 而 `Ω̂ x` 不 `Legal` 的反例, 或证明封闭 (证明封闭也是有用的交付, 它是构造路与下一步都要的引理; 若你证了, 明确写出以免重复劳动).
5. **目标层不为 0 的预告 (可选, 时间允许再做).** 目标层 1、层号 1 的 gt 行需要三路派发. 写出最小的陈述: 派发所需的位置证据是否必须作为数据 (而不是无关的证明) 给 ψ; 能写成编译定理就写, 不能就留判断并说明测到哪里.

### 纪律
- 否定要是编译过的定理, 每个前提给实例或说明为何可满足; 前提矛盾的定理什么也没说. 只否定写明的形状.
- 没有找到反例, 不等于证明了成立: 写 "在以下明确列出的搜索范围内未找到".
- 不要为了交出否定而改弱接口的字段再否定改弱后的版本; 若你认为某字段写错了, 单独指出.
- 你与构造路互不通信; 不读也不改 `YiIrrFold*` 文件 (即使它们出现在盘上).

### 止损
同形退化反例两条即停该方向; 整体上第 1 至 4 项各自给出结论 (定理或 "未找到") 后交回, 不必等第 5 项.

### 硬性约束
- 选项 `--safe --without-K` (可加 `--lossy-unification`). 无公设, 无洞, 无停机或正性编译指示, 无 trustMe. 不开 K. Funext 只准作前提出现在标明 "条件" 的文件里.
- **只新建文件**, 前缀 `YiIrrNeg`, 放 `probes/OCF/Align/`, 中文 literate `.lagda.md`. 不改任何已有文件 (包括 README, LOG, RESULTS, 三个定稿文件); 不动 `src/`, `archive/`.
- 编译: 从仓库根目录 `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>`. 堆上限 6G. **同一时刻只跑一个 agda** (另有四路在并行编译). 退出码不经管道: 0 通过, 42 类型错误 (先看日志首行是不是 LibraryError), 251 堆耗尽, 124 超时.
- 只删你自己模块的 `.agdai` (在 `probes/_build/2.8.0.2/agda/OCF/Align/`), 不用 `--ignore-interfaces`.
- 临时文件与日志只写到 `<实验目录>/agents/neg/`. 不写 `/tmp` 的其它地方, 不装包, 不 `rm` 自己文件之外的东西, 不 `pkill`, 不提交, 不推送, 不再派子智能体.
- 仓库文件里不写本机路径 (包括临时日志路径).
- 导入闭包: `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 输出 OK.
- 结论分三档: 编译过的定理 / 有限测试 / 判断. "穷尽" 一律标判断.

### 交回时的报告 (中文, 简明)
1. 先一段: 对纲领与目标意味着什么.
2. 文件清单; 每个模块删自身接口后冷编的退出码.
3. 第 1 至 5 项逐项的结论: 定理名与一句白话陈述, 或 "未找到" 加搜索范围; 每条否定注明反例对象是否在读回域内.
4. 你认为接口里写错或过强、过弱的字段 (若有).
5. 新增代码行数.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-10 13:29 (UTC)：

作者刚定了研发阶段的文字预算, 从现在起适用; 已写好的文件不必返工, 也不用回复这条消息, 继续你的任务.
1. 每个模块文首不超过 5 行: 判决与档位, 做了什么, 不否定什么, 入口指向. 代码之间的文字只写范围与不显然的定义理由, 不复述代码.
2. 不写只有导入语句的报告文件. 入口文件只放导入与不超过 10 行的判决. 报告只在最后交回时写一次 (写在回报里); 冷编表, 切片表, 成本表, 生成脚本不进仓库文件.
3. 一次性的试验放你的临时目录, 用纯 .agda; 要留下的结果才进仓库写成 literate.
4. 编译日志落文件, 只看首个错误附近; 查签名用检索, 不整篇读.

## 回报原文

### YiIrrNeg 否定路回报（对 `YiIrrIf.FoldRows`）

#### 1 对纲领与目标意味着什么

- **接口本身没有被否定，反而有实例。** 我在新块上写出了 `model : FoldRows`，定义域是整个零层合法片段另带相关的下界证据（`Only0 × Legal × Low0`）。所以 `FoldRows → ⊥` 不可证。
- **主审的判断在目标层 0 上对这个实例成立。** 折叠 `ψ⁺` 只在无关位置用证明，各行都是 `refl`。要相关证据的只有 `fold-legal` 与 `position` 这两个本身是证明的字段。
- **唯一被编译结果指到的是一种定义域取法。** `Dom x = Only0 x × Legal x`（不带相关的下界证据）推出两条 "凭无关证据取数据" 的原则。这读作 `Legal` 缺一个字段，不是乙线的数学障碍；反例对象不在规范塔的读回域内。
- 强度没有变化，没有序数值，没有 Funext，没有记号。`Low0` 是树侧的合法性字段。

#### 2 文件与冷编

全部在 `<仓库>/probes/OCF/Align/`。逐个删自身 `.agdai`（字面路径）后 6G 冷编，依赖用缓存：

| 模块 | 退出码 | Checking 行 | 代码行 |
|---|---|---|---|
| `YiIrrNegLegal.lagda.md` | 0 | 有 | 137 |
| `YiIrrNegWide.lagda.md` | 0 | 有 | 275 |
| `YiIrrNegForced.lagda.md` | 0 | 有 | 168 |
| `YiIrrNegWideDecide.lagda.md` | 0 | 有 | 335 |
| `YiIrrNegModel.lagda.md` | 0 | 有 | 170 |
| `YiIrrNegDispatch.lagda.md` | 0 | 有 | 65 |
| `YiIrrNeg.lagda.md`（入口） | 0 | 有 | 8 |

- 选项都是 `--safe --without-K --lossy-unification`。
- 检索 `postulate`、停机或正性指示、`trustMe`、洞、`Extensionality`、本机路径：0 命中。
- `importclosure.py` 对七个模块都 OK（未加 `--only`；入口闭包本地 10 个模块）。
- 没有改任何已有文件，没有读 `YiIrrFold*`。

#### 3 逐项结论

**第 1 项（接口本身）：未找到否定，并有实例。**
- 编译构造 `YiIrrNegModel.model : FoldRows`，`not-refutable : (FoldRows → A) → A`。`FoldRows → WLPO` 因此等于直接证明 WLPO。带 Funext 的版本没有写。
- 实例只是可满足性的见证：没有值定理，没有 Ω₁ 同值或下界，这些仍是构造路的交付。
- `YiIrrNegForced` 记录了被迫进定义域的对象与被迫的值（`forced`、`ψ-cst`、`ψ-coord`、`second-coordinate`）。在常值极限、它的后继、链的头一步上，接口索要的类型有闭居民；这是有限检查。搜索范围六条列在该文件末尾。

**第 2 项（证明当数据）：没有字段迫使输出依赖证明；反向陈述是定理**（`YiIrrNegForced.Consequences`，对任何实例）。
- `ψ-certificate-irr`、`out-evidence-irr`：换证书、结点证据、守卫，输出定义性相等。
- `next-irr`、`chain-irr`、`gt-pointwise-irr`：`next` 与整条链逐点不依赖 `w`、`b`、定义域证据。
- `gt-function-required`：gt 行推出两份证明下的极限体作为函数相等。这是必要条件，`next` 不看证明时为 `refl`；它是 `lim-function-equality-required` 在新块上的对应。

**第 3 项（大定义域）：两条编译定理，读法是判断。** 前提都是 `∀ x → Only0 x → Legal x → Dom x`。
- `YiIrrNegWide.wide→irr-search`：推出 `IrrSearch`，即由无关的 `Σ n. α n ≡ true` 算出见证。`wide→irr-search′` 不用 `position`，改用 `fold-legal` 加极限行。
- `YiIrrNegWideDecide.wide→irr-decide`：推出 `IrrDecide`，即对单调布尔列，凭无关的 "字面全假或有真值" 判定是哪一种。
- 机制：结点里的 `w` 是无关的，`Legal` 又没有 `Lgl k c` 字段；而 `position` 在 Ω 结点处要交出输出极限里的下标，那是数据。
- 反例对象 `node α s`、`node₂ γ mono s` **不在读回域内**（下界是为编码而造的坐标）。两种证据各有闭的合法实例（`closed-node-legal`、`quiet-node-legal`、`loud-node-legal`）。同形反例恰好两条，已停。
- 判断：`IrrDecide` 在 Agda 里没有闭证明（纸面的连续性论证，未形式化）。`IrrSearch` 更软，只是语言没有这种递归；四种直接写法在临时目录里被 `SplitOnIrrelevant` 拒绝，属有限测试。
- 按 "否定路线要有依据"，对 `Dom = Only0 × Legal` 这一取法只能写 **未走通**，待独立审核。
- 没有找到使各行互相矛盾的 `Only0 × Legal` 树；带 `Low0` 时各行同时成立（即上面的实例）。`low0-node→found`、`low0-node₂→decide` 说明补上字段后这两条攻击只取回成员自带的证据。

**第 4 项（块本身）：封闭，已证，不必重复。**
- `YiIrrNegLegal.Legal-Ω̂ : ∀ x → Legal x → Legal (Ω̂ x)`，用的是 `YiIrrIf` 的 `Legal`。
- 同时有 `lgl→Legal`（读回合法，对一切层号）、`Ω̂-CP`、`cp→CP`、`Legal-tw`、`Legal-Λ`、`Legal-ΩΛ`。
- 是旧块 `LevelFixVal` §4、§5 的逐行搬运，没有一处把无关证据当数据。

**第 5 项（预告）：两条编译定理加一条判断**（`YiIrrNegDispatch`）。
- 目标层 1：三路由层号的构造子形状判定（`way₁`、`way₁-retain`、`way₁-collapse`），保留结点的位置唯一（`Pre₁-unique`），保留结点对无关守卫类型正确（`retain₁`、`retain₁-read`）。所以目标层 1 上位置证据不必作为数据给折叠。
- 一般目标层：`locate→irr-search` 说明保留结点的位置 `r : Pre y` 不能由无关证据恢复。对象 `high α` 不在读回域内。
- 判断，未测：塔上的目标层 `tw n`（n ≥ 2）同样要位置数据。目标层 1 的折叠没有写。

#### 4 对接口字段的意见

- **`Legal` 偏弱（缺字段）。** 它没有相关的 `Lgl k c × Nested k c`。定义域要放宽到整个合法片段，须另带 `YiIrrNegWide.Low0` 这样的证据；规范 Ω₁ 满足它（`Ω₁-low`）。
- **`next` 的 `w`、`b` 可标成无关。** `next-irr` 说明这份相关性没有内容，改后强弱不变，`gt-function-required` 直接成为 `refl`。各行里的 `w`、`b` 保持相关是合适的。这不是错误。
- 没有发现写错或过强的字段。`Dom` 不要求对第一支 `t` 遗传，实例里也不需要：`position` 的 `fst` 情形走起点分支。

#### 5 行数与其它

- 新增代码 1158 行（代码块内非空行），七个文件。
- 文字预算：消息到达前写好的四件（`Legal`、`Wide`、`Forced`、`WideDecide`）文首较长，按指示未返工；之后的 `Model`、`Dispatch`、入口按新预算写。
- 事故：一次用变量拼路径的循环 `rm` 被安全检查拦下，没有执行；改用字面路径，只删了自己七个模块的 `.agdai`。
- 临时文件在 `<实验目录>/agents/neg/`，其中 `t/T1.agda` 至 `t/T4.agda` 是那四个被拒绝的写法。
- 重复劳动提示：`model` 与构造路的目标重叠（目标层 0 的完整递归 ψ，170 行）；两边可对照定义域的取法。

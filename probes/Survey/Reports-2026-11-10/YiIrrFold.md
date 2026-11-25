# 乙线折叠，构造路 (YiIrrFold)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-10 13:02 至 13:30 |
| 工具调用 / agda 编译 (粗数) | 55 / 14 |
| token (usage 字段，按消息去重) | 输出 178788；新写入缓存的输入 483529；读缓存的输入 8525502；其余输入 70 |
| 写过的仓库文件 | `YiIrrFold.lagda.md`, `YiIrrFoldBase.lagda.md`, `YiIrrFoldInst.lagda.md`, `YiIrrFoldSeed.lagda.md`, `YiIrrFoldValue.lagda.md` |
| 文件前缀 | `YiIrrFold` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-10 晚: 构造路与 K3 返回并复核; 派出第一次回灌 (主审)” 一节 |
| 主审复核后的一句结论 | 接口 FoldRows 已实填，目标层 0 的完整递归折叠；五件冷编退出码全 0；值在 ψ₀(Ω₁·ω) 以内互相 ≼，前沿不变 |

## 简报原文

你是 Agda 形式化研究的一路执行者 (构造路). 仓库: <仓库> (作者 choukh 的大数数学形式化). 请全程用中文思考与写作.

### 先读 (按顺序)
1. `AGENTS.md` (纲领与全部约定, 必须遵守).
2. `probes/Survey/EBOHandbook.md` 的 §3.1, §4, §5 (工程坑与复核清单).
3. `probes/Survey/RR5-SoftStops.md` 的 §1, §2 (本任务的来由).
4. 三个已定稿、只增不改的文件: `probes/OCF/Align/RR5IrrCore.lagda.md` (块), `probes/OCF/Align/RR5IrrCheck.lagda.md` (读回 `up`, `Ω̂`, `tw`, `Λ`), `probes/OCF/Align/YiIrrIf.lagda.md` (**共用接口, 记录 `FoldRows`**).
5. 旧块上的对应物 (可搬的证明来源): `probes/OCF/Align/YiK2Base.lagda.md` (第 0 层算术与 `Chain`), `YiK2bBase.lagda.md` (旧接口 `FoldRows0` 与 `AddChain`), `YiK2cFamily.lagda.md`, `YiK2cValue.lagda.md`, `YiK2Value.lagda.md` (族与值), `LevelFixCore.lagda.md` §3 (`Cp-tr`, `Dn-tr`, `cmpC` 等), `LevelFixVal.lagda.md` (`_+ᴸ_`, `Legal-Ω̂` 等). `YiIntrRaw.lagda.md` 与 `YiIntr.lagda.md` 文末的脚本, 演示了怎样把 LevelFixCore §3 机械搬到一个平行块.

### 背景 (已编译的事实)
乙线 = "层号是树". 旧块 (LevelFixCore) 上, 目标层 0 的完整递归折叠 ψ 三轮都没有交出, 卡在 "证明被当成数据": 读证书的 ψ 要求换证书后输出字面相等直到函数相等 (`YiK2cIrr.lim-function-equality-required`); 证据作普通参数进树时同一坐标两份守卫证明给出两棵树 (`YiIntrCheck.tw₃-not-root-irr`). 新块 RR5IrrCore 把结点里的证据 (`w : Lgl k c`, `b : Nested k c`) 与分支的守卫参数标成 Agda 的无关参数 `.( … )`: 换证明不换树、分支不依赖守卫证明都是 `refl`, `Ω̂ : LF → LF` 是全函数, 只读树的起点 `g c (inj₁ refl , w , b)` 对一切层号有定义. 作者 2026-11-10 定: 无关参数可以进成品候选 (不开 `--irrelevant-projections`).

### 你的目标
**实填 `YiIrrIf.FoldRows`**: 在新块上写出目标层 0 的完整递归折叠 ψ (四行: 零给 1; 后继给 `successor`; ℕ 极限逐项; 层号 0 的 Ω 结点走加法链 ηₙ₊₁ = ηₙ + ψ(g ηₙ), 从下界自身起步), 证书参数无关, 并交值.

交付分三段, 按顺序:
- **(a) 构造.** 一个 `FoldRows` 的记录值. `Dom` 由你选; 先试 `Dom x = Only0 x × Legal x`; 不行再收窄, 但必须含 `tw 2` (规范 Ω₁) 并对分支遗传. 需要的第 0 层引理 (`add-cp`, `add-legal`, `copies-step`, `positive` 等) 从 YiK2Base 搬; `Cp-tr` 等从 LevelFixCore §3 搬 (新块的 `lc` 模式多两个无关参数, `Lgl.lc` 的五元组形状与旧块相同).
- **(b) 规范实例.** 除 Ω₁ 外, 至少把 Ω₁+Ω₁, Ω₁·n 的族及其极限放进 `Dom` 并算出 ψ 在其上满足四行 (需要时把 `_+ᴸ_` 搬到新块).
- **(c) 值 (第 4 层, 单独的验收文件, 可导入验收侧模块).** 至少: ψ 在规范 Ω₁ 上的输出读回后与 `Value.ψ⁰ Ω₁` 互相 ≼ (对应旧的 `YiK2Value.same-on-Ω₁`); 争取 Ω₁+Ω₁ 与 lim Ω₁·n 的下界 (对应 `nested-lower`, `omega-lower`). 新块的 `Raw zero` 与旧块的同构 (只有 zero, suc, lim, top), 可以写一个到旧 `Raw zero` 的翻译后复用旧的读法. 强度一律写 ψ₀(Ω_x), 不用 ψ₁.

### 主审的分析 (判断, 供参考, 不是结论; 你应当检验它)
- ψ 可以写成 `ψ : (x : LF) → .(Dom x) → R`, 对树结构递归. gt 行里链点的守卫 `Gd zero c ηₙ` 要用 "ψ 在分支上的输出合法" 这条引理, 所以 ψ 与它的引理 (输出为正, 输出合法, 位置保持) 大概要写成互递归; 引理只在 ψ 的无关位置被调用. 链点用带无关分量的记录 `Point` (接口里已给); 无关字段不能投影, 只能对构造子 `point η e` 匹配.
- 位置保持 (`position`) 的自反情形现在是 `inj₁ refl`. 严格情形对被比较的大树递归: 落在 Ω 结点上时用 `Legal` 的 `tg` 字段 (第一支 ≤ 每个分支) 接到链的第 0 项.
- 无关变量只能出现在无关位置; 在无关参数的位置里可以对它们调用普通函数 (包括 `proj₁`), 但不能在子句左边对无关参数做模式匹配 (空模式与记录构造子除外).

### 止损
- 若某一行确实需要把证明当数据用 (类型检查器因无关性拒绝, 且换写法两次仍如此): 把 "哪一行, 哪个字段, 报错原文" 写进文件, 尽量把它写成一条编译过的陈述, 然后停.
- 若接口本身对规范实例不可满足: 写编译过的否定 (前提可满足), 指出字段, 并在你自己的文件里给出增补接口, 不改 YiIrrIf.
- 一个表述失败时, 先换表述或做最小实验, 再考虑停. 不要用 "具体的族加一份障碍分析" 代替完整的递归定义: 上一个执行方三轮都是这样交的, 这正是本任务要纠正的.
- 没有编译过的否定定理, 只能写 "未走通", 不能写路线已否定.

### 硬性约束
- 选项 `--safe --without-K` (可加 `--lossy-unification`). 无公设, 无洞, 无停机或正性编译指示, 无 trustMe. 不开 K. Funext 只准作前提出现在标明 "条件" 的验收文件里, 不进定义与证书.
- **只新建文件**, 前缀 `YiIrrFold`, 放 `probes/OCF/Align/`, 中文 literate `.lagda.md` (代码、讲解、结论交织). 不改任何已有文件 (包括 README, LOG, RESULTS, 上述三个定稿文件); 不动 `src/`, `archive/`. 记录由主审补.
- 编译: 从仓库根目录 `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>`. 堆上限 6G. **同一时刻只跑一个 agda** (另有四路在并行编译). 报退出码不要经过管道: 0 通过, 42 类型错误 (先看日志首行是不是 LibraryError), 251 堆耗尽, 124 超时.
- 只删你自己模块的 `.agdai` (在 `probes/_build/2.8.0.2/agda/OCF/Align/`), 不用 `--ignore-interfaces`.
- 临时文件与日志只写到 `<实验目录>/agents/fold/`. 不写 `/tmp` 的其它地方, 不装包, 不 `rm` 自己文件之外的东西, 不 `pkill`, 不提交, 不推送, 不再派子智能体.
- 仓库文件里不写本机路径 (包括临时日志路径); 需要时写 `<实验目录>`, `<仓库>`.
- 定义模块的导入闭包要干净: `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 输出 OK (验收文件除外, 注明).
- 结论分三档: 编译过的定理 / 有限测试 / 判断. 条件定理的前提给实例. "穷尽" 一律标判断. 不用 "自然", "只差" 一类形容.

### 交回时的报告 (中文, 简明)
1. 先一段: 对纲领与目标意味着什么 (证书、闭项、值三件事分开说).
2. 文件清单; 每个模块删自身接口后冷编的退出码.
3. 定理名与一句白话陈述, 标档; `FoldRows` 是否实填, `Dom` 取的是什么.
4. 未完成项与原因; 止损是否触发; 主审的哪条分析被证实或被推翻.
5. 新增代码行数 (代码块里的非空行).

## 中途消息（主审发给这一路）

转录时间戳 2026-11-10 13:29 (UTC)：

作者刚定了研发阶段的文字预算, 从现在起适用; 已写好的文件不必返工, 也不用回复这条消息, 继续你的任务.
1. 每个模块文首不超过 5 行: 判决与档位, 做了什么, 不否定什么, 入口指向. 代码之间的文字只写范围与不显然的定义理由, 不复述代码.
2. 不写只有导入语句的报告文件. 入口文件只放导入与不超过 10 行的判决. 报告只在最后交回时写一次 (写在回报里); 冷编表, 切片表, 成本表, 生成脚本不进仓库文件.
3. 一次性的试验放你的临时目录, 用纯 .agda; 要留下的结果才进仓库写成 literate.
4. 编译日志落文件, 只看首个错误附近; 查签名用检索, 不整篇读.

## 回报原文

### 构造路回报: YiIrrFold (无关证据块上, 目标层 0 的完整递归折叠)

#### 1 对纲领与目标意味着什么

- **证书.** 折叠写成 `ψ : (x : LF) → .(Dom x) → R`, 证书参数无关; 换证书输出定义性相等 (`certificate-free`, `refl`). 证书是树外谓词, 不引用记号. K2′ 三轮卡的 "证明被当成数据" 在这种写法下没有出现: `ψ` 只把证明转交给无关位置 (分支守卫, 链点守卫).
- **构造 (不是单个闭项).** 接口 `YiIrrIf.FoldRows` 已实填 (`YiIrrFold.fold-rows`). `ψ` 对树结构递归, 四行与 `next-additive` 都是 `refl`. 它是片段上一个全定义的折叠, 不是为某个族单写的. 闭项: 规范 Ω₁, Ω₁·(n+1), 它们的极限, 另加 Ω₁² (分支 η ↦ Ω₁·η).
- **值.** 第 4 层单独成篇: Ω₁, 一切 Ω₁·(n+1), lim Ω₁·(n+1) 三族上, 输出读回后与 `Level.ψ⁰` 的参照**互相 ≼** (旧 `YiK2cValue` 对后两族只有下界). 强度没有变化: 这些值都在 ψ₀(Ω₁·ω) 以内, 值前沿仍是 ψ₀(Ω_{Ω·ω²}).
- **一处与预想不同.** 定义域不是先试的 `Only0 × Legal`, 而是 `Dom x = Only0 x × Legal x × Seed x`. `Seed` = 沿后继, 极限, 分支走到的每个 Ω 结点, 下界合法 (`Lgl k c × Nested k c`) 有一份**相关的**证明 (树外). 它只进引理的证明, 不进 `ψ` 的输出. 对应旧 `YiCarry.Carry` 里 `Lgl k c` 一项 (不带 `Reg`, 不带第一支).

#### 2 文件与冷编

全部在 `<仓库>/probes/OCF/Align/`, `--safe --without-K --lossy-unification`, 6G:

| 文件 | 内容 | 退出码 |
|---|---|---|
| `YiIrrFoldBase.lagda.md` | 第 0 层算术 (`Cp-tr₀`, `lgl-cp₀`, `add-cp`, `add-legal`, `copies-*`), `Seed`, `Dom`, 加法链 `Chain`/`ChainLegal` | 0 |
| `YiIrrFold.lagda.md` | 互递归块 `ψ`, `ψ-positive`, `ψ-legal`, `ψ-position`; `fold-rows : FoldRows` | 0 |
| `YiIrrFoldInst.lagda.md` | `_+ᴸ_`, `add-dom`, `sum`, `limit`, 实例上的行, `Ω₁²` | 0 |
| `YiIrrFoldSeed.lagda.md` | 定义域分析: 五个写法的报错原文, `Unsquash` 等价, 条件实填, `Seedᶠ` 在塔与 Λ 上 | 0 |
| `YiIrrFoldValue.lagda.md` | 验收 (第 4 层) | 0 |

- 冷编口径: 五个 `.agdai` 一齐删掉后按依赖顺序逐个编, 各有 `Checking` 行, 全 0. 之后只改了 `YiIrrFold` 的说明文字 (代码未动): 删它自己的接口重编 0, 下游三件随之重查 (各有 `Checking` 行) 0. 首次编译五件都一次通过, 没有 42/251/124.
- `importclosure.py` 对前四件输出 OK (本地模块只有 `RR5IrrCore`, `RR5IrrCheck`, `YiIrrIf` 与自己). `YiIrrFoldValue` 是验收文件, 导入 `Value`, `RR4ChainAdd`, `RR4MonoFragment`, `YiK2cValue` (只取参照树一侧), 闭包审计按设计 FAIL.
- 禁用构造 0 (无公设, 洞, 编译指示, trustMe, Funext, `--irrelevant-projections`); 无本机路径; 无尾随空白. 没有改任何已有文件, 没有提交.
- 临时文件与日志在 `<实验目录>/agents/fold/` (实验在其下 `exp/`, 纯 `.agda`).

#### 3 定理 (都是编译过的, 除非另标)

**实填 (`YiIrrFold`)**
- `fold-rows : FoldRows`, `Dom = Only0 × Legal × Seed`; `dom-Ω₁ : Dom (tw 2)`; 对后继, 极限, 分支遗传.
- `ψ-positive : ∀ x .(d : Dom x) → Dn zero G.zero (ψ x d)`: 输出为正, **不读证书**.
- `ψ-legal : ∀ x (d : Dom x) → Lgl zero (ψ x d)`: 输出合法.
- `ψ-position : ∀ x y dx dy → CP x y → Cp zero (ψ x dx) (ψ y dy)`: 字面第一位置被保持, 对 `Dom` 里任意两棵树.
- `certificate-free`, `gt-first` (gt 行第 0 项是下界自身那一支): `refl`.

**实例 (`YiIrrFoldInst`)**
- `add-dom : Dom a → Dom x → Dom (a +ᴸ x)`: `Dom` 对层号加法封闭.
- `sum-dom`, `limit-dom`, `dom-Ω₁²`; `append-row`, `tail-zero/suc/lim/top`, `Ω₁-row`, `sum-row`, `limit-row` (由 `fold-rows` 的字段或 `refl`); `sum-position`, `limit-legal`, `Ω₁²-legal` 等.

**值 (`YiIrrFoldValue`, 序数值验收, 无 Funext)**
- `same-on-Ω₁ : read (ψ (tw 2) dom-Ω₁) ≈ᵛ L.ψ⁰ V.Ω₁`.
- `Lower.append-lower` / `Upper.append-upper`: 一步定理. 对 `Dom` 里任何前缀 `x` 与带自模拟的参照 `X`, `ψ⁰ X ≼ read (ψ x)` 推出 `ψ⁰ (X + Ω₁) ≼ read (ψ (x +ᴸ Ω₁))`, 反向同理. 没有按阶段加前提.
- `finite-same : ∀ n → read (ψ (sum n) _) ≈ᵛ L.ψ⁰ (K.reference n)`; `nested-same` (Ω₁+Ω₁); `omega-same : read (ψ limit _) ≈ᵛ L.ψ⁰ K.omega-reference`.
- 范围: 输入一侧的对应是按构造平行的, 没有层号树到 `Level` 第 1 层的一般解释; 不外推到 `Dom` 里别的树. 基本列不一致 (加法链第 n 项对参照链第 2n 项). Ω₁² 没有值定理.

**定义域分析 (`YiIrrFoldSeed`)**
- `guard→low`, `low→guard` (在 Base): 有任何一份相关守卫 ⟺ 有相关的 `Lgl 0 c`.
- `seed-all→unsquash`, `unsquash→seed-all`: "一切 `Only0 × Legal` 的树都有 `Seed`" ⟺ `Unsquash = ∀ c → .(Lgl zero c) → Lgl zero c`. 探针是退化结点 (常值分支), 读作谓词太宽, 不读作数学障碍.
- `Wide.wide-rows` (**条件定理**): 有 `Unsquash` 时接口在 `Only0 × Legal` 上实填, 同一个 `ψ`. 前提在 Agda 里没有实例也没有反驳 (判断: 擦掉无关标注的解释下是恒等, 相容但拿不出).
- `seed-Ω̂`, `seed-up`, `seed-tw`, `seed-Λ`: 遗传版 `Seedᶠ` 对 Ω 与读回封闭, 一切层号, 一步; 塔与 Λ 满足. 所以 `Seed` 在规范塔上不是空的要求. (这不是说 `tw 3` 以上在 `Dom` 里: `Only0` 不成立.)
- `start-from-certificate` (`refl`): 起点守卫取结点里那份或证书里那份, 是同一个链点.

#### 4 未完成, 止损, 对主审分析的检验

**未完成 / 未走通**
- `Dom = Only0 × Legal` 上实填: **未走通, 没有否定定理**. 卡在 gt 行: 下一个链点的守卫要 "子树的输出合法", 这条引理对未知的树递归, 要调用 `Legal` 的分支字段, 字段的守卫参数是相关的, 而结点里的 `w` 是无关的.
- 五个具体写法的检查器事实 (报错原文已写进 `YiIrrFoldSeed` §0):
  1. 相关引理里直接用 `w`;
  2. 名字前加点的无关定义 `.tree-seed`;
  3. 在无关位置里用 `LF` 的消去子现场读 `w`;
  以上三个都是 `[VariableIsIrrelevant] Variable w is declared irrelevant, so it cannot be used here`.
  4. 把结论压扁成带无关字段的记录, 用投影合并可数个证明: `[ProjectionIsIrrelevant] … Turn on option --irrelevant-projections to use it (unsafe)`;
  5. 同上改用模式匹配: `[VariableIsIrrelevant]` (变量 `p`).
- `LevelFixCore` §3 的一般层版本 (含 `cmpC`) 没有搬: 目标层 0 用不到, 只写了层号 0 的几行.
- 目标层不为 0 (三路派发, 回灌) 没有碰.

**止损.** 没有触发 "停": 收窄 `Dom` 是任务书允许的, 接口实填了. 但 "哪一行, 哪个字段, 报错原文" 已按止损条款的要求写进文件 (gt 行; 结点的 `w`; 上述原文), 并配了编译过的等价陈述.

**主审分析的检验**
- 证实: `ψ` 写成 `.(Dom x)` 参数, 结构递归, 与引理互递归 (检查器直接接受停机, 无度量).
- 证实: 位置保持自反情形 `inj₁ refl`; 严格情形对大树 `y` 递归, 在 Ω 结点上用 `Legal.tg` 接到链的第 0 项.
- 修正: "引理只在 `ψ` 的无关位置被调用" 对 `ψ-legal` 成立; `ψ-positive` 是例外, 接口的 `next-grow` 对守卫无关的任意链点要一份相关的增长, 所以它必须写成不读证书的.
- 推翻: "先试 `Only0 × Legal`" 不够, 要加 `Seed`.
- 补充 (实测): 无关位置只放开**已在上下文里**的无关变量; 位置里面新绑定的 (λ 或模式匹配) 仍不能相关地用, 无关定义的定义体也一样. 所以结点里存的无关证明只能原样转交, 不能被递归引理收集.

**对后续的含义 (判断).** 在 `Dom` 上, 这个折叠真正用到新块的是 "分支守卫参数无关" 与 "证书参数无关" 两件; "证据存在结点里" 折叠可以不用 (`start-from-certificate`). 第一次回灌若也要 "输出合法" 作守卫, 大概同样要树外的相关证书, 这一条未验证.

**翻译账.** 四行的形状来自接口 (承自旧 `FoldRows0`, 再往上是记号的折叠规则), 本轮没有新增这一类. 树逼出的: 加法链, 链点的无关守卫, `Seed`, 位置保持经 `tg` 接到链的第 0 项. 新增脚手架 `Seed`, `Chain`/`ChainLegal` 都不读记号. 验收用序数值, 没有用标签. 第 4 层逼出: 无.

#### 5 行数 (代码块里的非空行)

| 文件 | 行 |
|---|---|
| YiIrrFoldBase | 137 |
| YiIrrFold | 119 |
| YiIrrFoldInst | 177 |
| YiIrrFoldSeed | 136 |
| YiIrrFoldValue | 244 |
| 合计 | 813 |

前三层 (Base + Fold + Inst) 433 行; 定义域分析 136; 第 4 层 244.

**关于文字预算.** 协调者的预算消息在五个文件写完之后到达; 按消息所说没有返工, 所以现有文件的文首都超过 5 行. 冷编表, 切片表, 生成脚本都没有进仓库文件. 记录 (README, LOG, RESULTS) 没有动, 由主审补.

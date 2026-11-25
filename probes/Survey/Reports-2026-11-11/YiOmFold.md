# 第 4 步第一站，构造路 (YiOmFold)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 05:21 至 06:18 |
| 工具调用 / agda 编译 (粗数) | 71 / 24 |
| token (usage 字段，按消息去重) | 输出 339559；新写入缓存的输入 649747；读缓存的输入 17385365；其余输入 102 |
| 写过的仓库文件 | `YiOmFold.lagda.md`, `YiOmFoldBase.lagda.md`, `YiOmFoldChain.lagda.md`, `YiOmFoldGap.lagda.md`, `YiOmFoldNorm.lagda.md`, `YiOmFoldRel.lagda.md`, `YiOmFoldTop.lagda.md` |
| 文件前缀 | `YiOmFold` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 第 4 步第一站的构造路返回并复核; 五路结清 (主审)” 一节 |
| 主审复核后的一句结论 | 没有过去；闭项 T⁺ 合法无前提但用了替代行，读法未定；三处障碍的约化与闭实例；两条绕过障碍的行没有接进闭项；七件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "乙线第 4 步第一站 (公共上界含 Ω 结点), 构造路". 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条 (第 3 条壁垒); "交替路线" (全分支的高层比较被禁止); "量化域先取带证据的读回域"; "律带公共上界, 构造与否定配对"; Agda 一节 (选项, 无关参数, 文字预算, 退出码, 堆); "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §3.1, §4.1 到 §4.5, §5.4. `probes/Survey/Reports-2026-11-11/README.md` 的 §2 (上一轮三路做成了什么, 没做成什么); 要细节再读同目录的 `YiRawFold.md`, `YiRawNeg.md` (回报原文).
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - 块: `RR5IrrCore` (注意 `Pre`, `Low`, `Kid`, `KidR` 在 `lc` 层号上的子句: 分支里的位置与孩子带**相关的**守卫 `Gd k c η`; 而 `G.lc` 与 `LF` 的 `lc` 的分支函数只带**无关的**守卫), `RR5IrrCheck` (`up`, `upT`, `Ω̂`, `tw`), `YiIrrIf`.
   - **本轮的共用接口 `YiOmIf`**: `Slot`, `slot-rel`, `kid-rel`, `SlotIrr`, `KidIrr` (两条陈述, 没有证也没有否定), `Ω₁⁺`, `Ω₁⁺-form`, `Ω₁⁺-is-top`, `start₂`, `start-branch`. 上两步的接口 `YiRawIf` (`Tgt`, `dispatch`, `RawFold`), `YiLvIf`.
   - 上一轮构造路, 你要接着它做: `YiRawFoldBase` (`Ext`, `psum`, `CohP`), `YiRawFold` (`Ψ`: 写在 `Raw K` 上的折叠, K 是 `Plain` 的; `own`, `ownT`; `rawFold`; `complete-*`), `YiRawFoldInst`, `YiRawFoldUp` (`Φ-below`), `YiRawFoldTw3` (`T₃ᵐ`: `tw 3` 的闭项, 根上的链点带相关的 `Lgl zero η`).
   - 上一轮否定路: `YiRawNegOmega` (`K₂ω = tw 2`, `br`, `Link`, `compare-link`, `compare-same-branch`, `no-compare-tw2`, `dec-at→lpo`, `keep-fold→wlpo`), `YiRawNegChain` (`Root`, `Bridge.cross`), `YiRawNegLift` (`wrap`, `toRaw`, `fromRaw`), `YiRawNegModel` (`plain-fix`).
   - 更早的可复用部件: `YiLvNegCanon` (`ccompare`), `YiLvNegCompare` (`At`, `coordᴺ`, `witness-guard`, `guard→found`), `YiLvNegKeep` (`level-legal→found`, `LPO`), `YiIrrNegWide` (`IrrSearch`), `YiLvFoldAdd`, `YiLvFoldBase`.
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么, 对纲领与目标意味着什么

乙线: 层号是树 (`LF`), 第 k 层的树是 `Raw k`; 终点是 ψ₀(Λ) 的闭项加值, Λ = lim tw. 上一轮做成: 折叠写在 `Raw K` 上 (K 没有 Ω 结点), 派发读树里的位置, 处处完全; `tw 3` 的闭项 `T₃ᵐ` 合法, 没有前提 (读法 ψ₀(Ω_Ω), 与已封存的 BTBO 持平; 没有值定理).

本步是**层号不可数的第一站**: 公共上界取 `tw 2` (读法 Ω₁, 它自己是一个 Ω 结点). 目标闭项是 `Ω₁⁺ = Ω̂ (suc (tw 2))` 的目标层 0 折叠, 读法 ψ₀(Ω_{Ω₁+1}), 是第一个越过 BTBO 的规范结点. 历史上没有一条线过得去这里; 纲领第 3 条 (壁垒) 管的就是这一带. 所以这一站最有价值的产出是**编译过的事实**: 哪一行能写, 哪一行不能写, 不能写的是块的写法造成的还是壁垒.

`Ω₁⁺` 是层号 `tw 2` 的结点, 下界 `top`, 第一支 `tw 3`, 分支是 `Raw (tw 2)` 的读回 (`YiOmIf.Ω₁⁺-form`). 目标层 0 的折叠是一条 `Raw (tw 2)` 里的链: 起点 `top`, 下一点是这一点加上**目标是 `tw 2` 自己的折叠**在这一点上的输出, 观察取目标层 0 的折叠.

### 2 主审的纸面分析 (判断, 没有验证; 请先挑战它)

1. **目标层 0, 起点.** `top : Raw (tw 2)` 的读回是 `tw 3`; 它的目标层 0 折叠就是上一轮 `T₃ᵐ` 那条链 (根是层号 0 的结点, 链点带相关的合法性, 各支经孩子进到 `Raw (read0 η)`). 这一处应当能接上.
2. **保留模式下的 `top` (目标是 `tw 2` 自己).** 根是层号 0 的结点, 层号 0 在 `tw 2` 的主干位置上, 所以要保留: 输出是 `Raw (tw 2)` 里主干槽位上的结点, 它的第 η 支应当是 "第 η 支的 `top`" 的保留模式折叠, 其中的保留结点要落在第 η 支的槽位 `br η e r` 上, 或者整个经 `em (η , e)` 嵌进来. 这两样都要**相关的**守卫 `e`, 而结点的分支函数只拿到**无关的**守卫. 这就是接口里的 `SlotIrr`, `KidIrr`. 我预计它们推出凭无关证据取数据 (例如坐标 `coordᴺ α` 的守卫与 `Found α` 等价), 也就是这一行在这个块里写不出. **这是我预计的第一个障碍, 而且它来自块的写法 (位置与孩子带相关守卫, 分支带无关守卫), 不是壁垒.**
3. **跨支比较.** 结点在第 η 支的槽位上, 它自己那一层的折叠遇到别的支 η′ 上的结点时要比较两个位置; 只有路径相连的位置对可比 (`Link`). 规范的链 (从 `top` 出发, 加法, 折叠的输出) 走到的位置对是不是都相连, 没有判定.
4. **真正的壁垒大概在这里:** 目标在某一支里层号 ≥ 1 的位置上, 而树里有 `top`. 那时 `top` 的根 (层号 0) 在目标之下要保留, 它的第 η″ 支对一切 η″ 都要折到那个目标层, 要把任意的 η″ 与目标所在的 η 比较. 规范的链需不需要这一种, 没有判定.

### 3 目标, 分四站, 每站先交再往下

每站交 (a) 构造或闭项, (b) 强度的证据 (派发完全性落实到折叠上的定理; 值的下界或写明没做), 或者 (c) 编译过的约化. 部分进展也算.

**第 A 站, 目标层 0.** 把上一轮的 `Ψ` 推广到公共上界 `tw 2`, 只做目标层 0: `top` 的行 (就是 `T₃ᵐ` 那条链), 主干槽位上的结点 (层号 0, 加法链), 分支槽位上的结点, `em` 的三种孩子. 说清楚哪些树在定义域里 (定义域先取规范的链走到的树, 不取一切合法的树).

**第 B 站, 决定性的一问: 保留模式下的 `top`.** 给出 "目标是 `tw 2` 自己" 时 `top` 的行并证它合法; 或者把缺的东西写成带确切类型的前提 (`SlotIrr`, `KidIrr`, 或你找到的更弱的陈述), 在这个前提下条件地做出来. 若做不出, 再给一个不需要这些前提的合法替代行 (例如只用 `top` 与主干槽位能表达的树), 写明它与本该有的那一行差在哪里, 不对读法作任何声称.

**第 C 站, 链上的位置对.** 给一个对规范的链封闭的谓词 (对起点, 加法, 第 A, B 站的折叠输出封闭), 在它之内派发所需的比较都由 `compare-link` 给出; 或者指出链上第一个不相连的位置对 (编译的实例).

**第 D 站, 闭项.** `Ω₁⁺` 的目标层 0 折叠: 闭项, 合法性, 根上的行, 链行. 用了替代行就明说, 并且不写读法 ψ₀(Ω_{Ω₁+1}).

**停下的条件.** 遇到下面任一种就停在那一站, 交已有的文件与约化, 不硬攻:
- 同一处连续三次重新设计仍过不了检查器;
- 需要 Funext 或 K;
- 你判断必须改块.
约化: 把缺的东西写成带确切 Agda 类型的陈述, 其余条件地证出来并编译; 说明前提在规范实例上是否可满足.

**若判定必须改块:** 不在仓库里建新块 (这要作者定). 可以在你的临时目录里做最小的可行性试验, 用纯 `.agda`: 块的某个变体 (例如位置与孩子的守卫改成无关; 或 ℕ 极限自带相邻第一位置的路径, 使比较要的数据在树里) 能否过正性与停机检查, `up`, `Ω̂`, `tw` 能否照搬, 第 B 站的那一行在变体里是否写得出. 把编译事实写进回报, 单列为 "临时目录里的试验", 不算成果.

### 4 规则

- **只新建文件**, 前缀 `YiOmFold`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiOmIf`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另四路用前缀 `YiOmNeg` (否定路), `YiPsum`, `YiRawVal`, `YiLvAll`, 不要动它们的文件, 也不要依赖它们. 对共用接口的增补写在你自己的文件里, 并在回报里说.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提出现在标明 "条件" 的文件里, 不进折叠的定义与闭项.
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件; 编译表不进文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径).
- 你的临时目录: `<实验目录>/agents/omfold`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 通过; 检索禁用构造为 0.

### 5 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几站 (HOLDS / PARTIAL / BLOCKED), 一段话说对纲领与目标意味着什么; 障碍是块的写法造成的, 还是壁垒, 还是没有判定.
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表: 名字, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型, 并说前提是否可满足.
4. 强度的证据单列; 用了替代行的地方单列.
5. 第一个障碍: 精确到字段或子句, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 临时目录里的试验 (若做了): 变体是什么, 编译事实, 哪些已有定理在变体里会不成立.
7. 偏离与事故.
闭项, 证书, 值分开说; 强度写 ψ₀(Ω_x), 标明是读法还是定理; 不用 "只差", "自然" 一类形容.

## 回报原文

### 回报：乙线第 4 步第一站 (公共上界 `tw 2`)，构造路 `YiOmFold*`

#### 1 判决

- 第 A 站 PARTIAL，第 B 站 PARTIAL (本该有的行 BLOCKED，另给两条无前提的合法行)，第 C 站只对替代行的链 HOLDS，第 D 站 HOLDS 但用了替代行。
- 闭项 `T⁺ : R` 与 `Lgl zero T⁺` 没有前提。它不带读法 ψ₀(Ω_{Ω₁+1})，没有值定理。

**对纲领与目标意味着什么。** 层号不可数的第一站上，折叠的大部分行在现有的块里写得出：
- 目标层 0 的 `top` 行，就是上一轮的 `T₃ᵐ`。
- 主干槽位结点的加法链，三种孩子在目标层 0 的行。
- 目标为 `tw 2` 自己时一切结点的保留行 (`Φˢ⁺`)。
- 对一切 `Raw (tw 2)` 的加法。

写不出、或只能写成替代行的有三处，性质不同：

| 障碍 | 内容 | 归类 | 依据 |
|---|---|---|---|
| O1 | 保留模式下 `top` 的分支族只拿到无关守卫，而槽位与孩子要相关守卫 | 块的写法，不是壁垒 | 编译约化：分支族满足保留律就推出 `IrrSearch` (`keep→irr-search`)，不是 LPO/WLPO |
| O2 | 各支逐槽位搬进来后互不为第一位置，也不在第一支之上 (纸面分析里没有这一条) | 块的写法 (`DnK` 跨孩子种类为 ⊥) | 两个编译的闭实例；即使守卫相关也如此 |
| O3 | 目标层 0 的折叠在分支槽位结点上的行，缺目标在一支里的折叠 `own` | 没有判定 | 对一切位置对要求保留律是壁垒 (上一轮 `keep-fold→wlpo`, `dec-at→lpo`)；链实际要的对能否带路径，未定 |

对纸面分析的挑战，有两条编译结果：
- **O1 与 O2 可以无前提地绕过。** 槽位取在归一坐标 `suc (nrm a)` 的那一支，守卫由树算出；各支沿坐标的路径累加。得到的行 `topᴺ` 合法，分支里是真的分支槽位结点。保留律在归一坐标上成立，坐标不含极限时原样成立。
- **纸面分析第 4 条单独不是壁垒。** 目标在一支里而树里有 `top` 时，分支取相对坐标 `η + nrm δ` 就有字面路径，所问的比较正是 `compare-link` 的值 (`rel-compare`)。

所以真正停下的位置比纸面分析更靠后：已经放在别的支槽位上的结点，在分支目标下的派发。

#### 2 文件表

都在 `<仓库>/probes/OCF/Align/`。删自己的接口后冷编译，每个约 2 秒，常驻内存不超过约 0.5G。`importclosure.py` 七个模块全过，禁用表命中 0；禁用构造检索 0；无本机路径。

| 文件 | 代码行 (非空) | 冷编译退出码 |
|---|---|---|
| `YiOmFoldBase.lagda.md` | 166 | 0 |
| `YiOmFold.lagda.md` | 366 | 0 |
| `YiOmFoldGap.lagda.md` | 225 | 0 |
| `YiOmFoldNorm.lagda.md` | 258 | 0 |
| `YiOmFoldRel.lagda.md` | 156 | 0 |
| `YiOmFoldChain.lagda.md` | 102 | 0 |
| `YiOmFoldTop.lagda.md` | 106 | 0 |

依赖序：Base，Fold，Gap，Norm，Rel，Chain；Top 只依赖 Base 与 Fold。日志在 `<实验目录>/agents/omfold/` 下的 `<模块>.cold.log`。

#### 3 定理表

除标明的以外都是编译定理，无前提。

**`YiOmFoldBase`：加法与主干片段**
- `plusΩ`：对一切 `Raw (tw 2)` 的加法。三种孩子逐槽位搬进来，分支的孩子用树里自带的相关守卫，这三行不改。`x + top` 是替代行 `topᴬ`。
- `plus-weak`, `plus-cp`, `plus-dn`, `plus-grow`, `plus-lgl`, `plus-ns`：弱增长，保持第一位置，严格增长，合法，嵌套。
- `Tr`：主干片段，结点只在主干两个槽位上，没有分支的孩子。`plus-tr`, `copiesΩ-tr`：对加法与 ω 倍封闭。

**`YiOmFold`：第 A、B 站的两个折叠**
- `Φ⁰`：目标层 0 的折叠，定义域 `Dom⁰` 是一切不含分支槽位结点的树，含三种孩子与 `top`。`Φ⁰-legal`, `Φ⁰-cp`, `Φ⁰-dn`, `Φ⁰-pos`。
- 行都是 `refl`：`Φ⁰-top` (`top` 给 `T₃ᵐ`)；`Φ⁰-kid` (分支的孩子用上一轮的 `Φᵐ`，读孩子自带的守卫)；`NodeRow.chain-row`, `next-row`, `body-row` (主干结点的链由 `Φ⁰` 自己推进)。
- `Φˢ`：目标为 `tw 2` 自己，定义域 `Tr`。`Φˢ-legal`, `Φˢ-nested`, `Φˢ-cp`, `Φˢ-tr` (对 `Tr` 封闭)。`top` 的行是替代行 `topˢ`。
- 派发：`Φ⁰-fold-root`, `Φ⁰-fold-first` (输出是 ℕ 极限)；`Φˢ-keep-root`, `Φˢ-keep-first`, `Φˢ-keep-top` (保留在原槽位)。

**`YiOmFoldGap`：缺的行**
- `Branches`, `RowLegal`, `KeepLaw`：前提的类型，见第 5 节。`row-legal`, `row-nested`。
- `βˢ-legal`, `βˢ-not-keep`：替代行合法，但不满足保留律。
- `keep-not-tr`：满足保留律的分支族的输出不在 `Tr` 里。
- **`keep→irr-search : ∀ β → KeepLaw β → IrrSearch`**：约化。
- `keep-rel`, `move-legal`：守卫相关时某一支写得出并合法。
- `keep-from-data : GdData → Σ Branches KeepLaw`：前提不空 (条件定理)。`GdData = ∀ η → .(Gd zero raw1 η) → Gd zero raw1 η`。
- `kid-same-branch`, `kid-not-above-first`：嵌入的孩子跨支不可比，不在第一支的孩子之上。
- `moved-undirected`, `moved-not-first`：闭实例，第 2、3 支与第一支。
- `BranchRow.branch-row-legal`：条件定理，见第 5 节 (3)。

**`YiOmFoldNorm`：归一坐标上的保留行**
- `nrm`, `nrm-legal`, `γ : ∀ a → Gd zero raw1 (G.suc (nrm a))`：归一坐标的相关守卫由树算出。
- `keepAll`, `KA-legal`, `KA-cp`, `KA-nested`, `KA-pos`：一支里一律保留的折叠，不读 `Legal`。
- `topᴺ`, `topᴺ-legal`, `topᴺ-nested`, `topᴺ-kept`。
- **`norm-keep : ∀ a e → Kept K₂ω (read0 (nrm a)) (βᴺ (G.suc a) e)`**；`norm-keep-fin` (`a` 不含极限时层号就是 `read0 a`)。
- `norm-not-dom`, `norm-not-tr`, `point₁ᴺ-guard`, `point₁ᴺ-not-dom`。

**`YiOmFoldRel`：目标在一支里时 `top` 的行**
- `Rel.eᵟ`, `linkᵟ`：坐标 `η + nrm δ` 的相关守卫，与目标之间的字面路径。
- **`rel-compare`**：那一支里问的比较等于 `compare-link` 在这条路径上的值 (`refl`)。
- `Row.rowᴿ-legal`, `rowᴿ-nested`, `rowᴿ-kept` (根保留在目标层的层号 0 槽位)。
- `row₃-legal`, `row₃-kept`：规范实例，目标在第 3 支的根上。

**`YiOmFoldChain`：对一切树的自目标折叠与链点**
- `Φˢ⁺ : RΩ → RΩ`：对一切树；`Φˢ⁺-legal`, `Φˢ⁺-nested`, `Φˢ⁺-cp`, `Φˢ⁺-pos`。
- `Φˢ⁺-keep : ∀ r c t g → Kept K₂ω (lev K₂ω r) (Φˢ⁺ (G.lc r c t g))`：一切位置。
- `pointsᴺ-legal`, `pointsᴺ-nested`, `pointsᴺ-grow`, `pointsᴺ-guard`：链点对一切 n；`pointsᴺ-one`。

**`YiOmFoldTop`：第 C、D 站**
- `tr-node`, `trunk-link`, `tr-compare`：`Tr` 里的位置对由 `compare-link` 给三路。
- **`T⁺`, `T⁺-legal`**；行 (`refl`)：`T⁺-start`, `T⁺-feedback`, `T⁺-body`, `T⁺-term`, `T⁺-term₀` (第 0 项是 `T₃ᵐ`), `T⁺-branch`, `Ω₁⁺-node`, `T⁺-point₁`。
- `T⁺-grow`, `guards⁺`：链点严格增长，是 `Ω₁⁺` 的带守卫坐标。`T₃ᵐ-first : Dn zero T₃ᵐ T⁺`。

#### 4 强度的证据，与替代行

**强度的证据，都是派发层面的。**
- 目标层 0：主干结点的输出是 ℕ 极限。
- 目标为 `tw 2` 自己：一切结点保留在原位 (`Φˢ⁺-keep`)。
- `top` 的分支在归一坐标上满足保留律 (`norm-keep`, `norm-keep-fin`)。
- 分支目标下 `top` 的根保留 (`rowᴿ-kept`)，其中每一支用接口实例 `Φᵐ`，带它的保留律与折叠律。
- **值：没做。** 只有 `T₃ᵐ-first` (上一轮的闭项是 `T⁺` 的第 0 项)，这是第一位置关系，不是值定理。

**替代行。**
1. `topᴬ` (`x + top`)：根槽位结点，第一支 `x + top₁`，第 η 支是第一支加上坐标 η 自己。本该是 `x + em (η , e) top`。两条链都用到它。
2. `topˢ` (`Φˢ top`)：第 η 支是 `t₀ + F₀ η`，只用主干。**闭项 `T⁺` 用的是这一条**，所以 `T⁺` 的链点全在主干片段里，没有任何分支上的层号。
3. `topᴺ` (`Φˢ⁺ top`)：槽位在归一坐标那一支，并沿路径累加。`pointsᴺ` 用它；这条链没有观察，所以没有闭项。
4. `rowᴿ`：分支取相对归一坐标，并沿 δ 累加。它是独立的一行，没有接进任何链。
5. 沿用上一轮的：`T₃ᵐ` 里极限层号的 `top` 取部分和；`keepAll` 在极限层号的 `top` 上同样取部分和。

**累加的两边账** (手册 §3.8)：
- 省下的：`dir` 项不再要跨支的第一位置；守卫不再要从无关变回相关。
- 改了的：第 η 支含它路径上此前各支的全部；含极限的坐标被 `nrm` 换成部分和；基本列与值都可能与本该有的行不同。
- `nrm` 与原坐标的值关系没有定理。

#### 5 第一个障碍

**(1) 本该有的保留行。** 子句是 `Φˢ G.top` 的分支函数，类型 `(η : R) → .(Gd zero raw1 η) → Raw K₂ω`；本该取 `move η e G.top`。检查器报错原文 (临时目录里的测试)：

```
[VariableIsIrrelevant] Variable e is declared irrelevant, so it cannot be used here
when checking that the expression e has type Gd zero raw1 η
```

- 来源：`RR5IrrCore` 里 `Pre` 与 `Kid` 在 `lc` 上的子句带相关的 `Gd k c η`，而 `G.lc` 的 `g` 带无关的。
- 缺的引理：`Σ Branches λ β → KeepLaw β × RowLegal β`，其中
  - `Branches = (η : R) → .(Gd zero raw1 η) → Raw K₂ω`
  - `KeepLaw β = ∀ a (e : Gd zero raw1 (G.suc a)) → Kept K₂ω (read0 a) (β (G.suc a) e)`
- 可满足性：`KeepLaw` 一项已推出 `IrrSearch`；在 `GdData` 下有居留 (`keep-from-data`)，所以不可反驳。连同 `RowLegal` 是否可满足，没有判定。

**(2) 跨支的第一位置。** `DnK` 在 `lc` 层号上：第一支的孩子对分支的孩子是 ⊥，两个分支的孩子要 `x ≡ x′`。搬进来的结点落在 `br η e r`，不同的 η 是不同的位置。闭实例 `moved-undirected`, `moved-not-first`。这只否定 "各支用各自的槽位排成结点" 这一种放法；各支共用一套沿路径一致的槽位是否可行，没有试。

**(3) 目标层 0 在分支槽位结点上的行。** `Dom⁰ (G.lc (inj₂ (inj₂ _)) c t g) = ⊥`。缺的是：

```
own : (ζ : Low (read0 η) r) → .(GdL (read0 η) r c ζ) → Raw (lev (read0 η) r)
```

- 它应当是目标 `at (br η e r)` 的派发完全的折叠在 `g ζ` 上的值。
- 给了 `own` 与它的合法、嵌套、头为正，这一行合法 (`BranchRow.branch-row-legal`)。前提可满足 (常值，`OwnConst`)，但常值不带强度。
- 首次出现：用归一行推进时，第 1 个链点就出了 `Dom⁰`，位置是链的起点坐标 1 上的那一支 (`point₁ᴺ-not-dom`)。

**判断 (纸面，未编译)：**
- 起点那一支的结点层号是 0，它的 `own` 就是 `Φ⁰`，这一项应当可以经 `BranchRow` 做出。
- 之后的项层号 ≥ 1，`own` 会遇到同一条路径上别的支的结点；`nrm` 过极限不保持第一位置 (上一轮 `cum-not-monotone` 的机制，没有在 `nrm` 上重证)。
- 从第 2 个链点起，会遇到另一个根槽位结点的全部分支，两边的坐标是互相独立的约束变量。
- 折叠拿到的树里看不出一个结点与目标是不是同一支，所以连同支的结点也无法在一般的树上诚实派发。
- 链点坐标上有没有不相连的位置对，没有编译的实例，属于没有判定。

**下一步的方向 (判断，未验证)：** 把折叠写在生成数据上 (`top`、加法、`Gκ`、`keepAll` 的调用结构)，而不是写在已经搬好槽位的树上，并配合相对坐标。这样同支与路径是结构给出的。

#### 6 临时目录里的试验 (不算成果)

目录 `<实验目录>/agents/omfold/v1/`，纯 `.agda`，`--safe --without-K`。

**变体一：位置与孩子的守卫改成无关。**
- `V1Core.agda` 退出码 0，过正性与停机。
- `V1Check.agda` 退出码 0：
  - `up`, `upT`, `Ω̂`, `tw`, `Λ` 只改模式就照搬。
  - 从无关守卫直接得到槽位 `br η .e r` 与孩子 `kid η .e T`，层号与读回的等式是 `refl`，即 `SlotIrr`, `KidIrr` 的同形命题平凡成立。
  - O2 仍在 (`kid-not-above-first`)。
- `V1Fail.agda` 退出码 42，是预期的：从位置读 `Lgl zero η` 报 `VariableIsIrrelevant`。
- 所以下列在变体里不能照写：`YiRawNegOmega` 的 `compare-up`, `compare-zero`, `compare-link`；本轮 `Φ⁰` 的分支孩子行；`YiOmFoldRel`。这是一次尝试，不是不可能性的证明。
- 判断：变体一把 O1 换成 "同支比较拿不到 `Legal` 数据"，没有减少障碍。

**变体二 (只做了第 0 层)：ℕ 极限自带相邻项的路径。**
- `V2Zero.agda` 退出码 0：归纳-递归的树类型通过；加法与 "保持第一位置" 互递归通过；坐标 `1 + η` 的路径与沿路径的相连由树算出，不要守卫，也不要归一。
- 没有做整个块。
- 代价：极限的步证明成了树的数据，同项不同证明的两个极限是不同的树。哪些已有定理会不成立，没有评估。

#### 7 偏离与事故

- 交了七个文件，比四站多出 `Norm`, `Rel`, `Chain` 三个。它们是对纸面分析第 2、4 条的挑战，没有接进闭项。
- 对共用接口的增补都写在自己的文件里：`Branches`, `RowLegal`, `KeepLaw`, `GdData` (`YiOmFoldGap`)；`Tr` (`YiOmFoldBase`)；`Dom⁰` (`YiOmFold`)。没有用 `YiOmIf` 的 `SlotIrr`, `KidIrr` 作前提，换成了行层面的 `KeepLaw`；两者之间的蕴涵没有证。
- `Φˢ` (定义域 `Tr`) 与 `Φˢ⁺` (一切树) 并存，只在 `top` 的行上不同；这一点没有写成定理。
- `rplain` 在 `YiOmFoldBase` 里重定义了一份，与 `YiRawFoldTw3.rplain` 同文，为的是底座不导入 Tw3。
- 导入了上一轮否定路已定稿的 `YiRawNegOmega`, `YiLvNegCompare`, `YiLvNegKeep`, `YiLvNegCum`, `YiIrrNegWide`。没有依赖同时在跑的四路的任何文件。
- 临时目录里有两次预期失败的测试 (`t/Sanity.agda`, `t/IdealRow.agda`)。`v1` 里一次因缺库文件得 42 (日志首行 `FileNotFound`)，加了本地 `v1.agda-lib` 后重跑。
- 全程同时只跑一个 agda，没有用 `--ignore-interfaces`，只按字面路径删过自己七个模块的接口。没有改任何已有文件，没有提交。

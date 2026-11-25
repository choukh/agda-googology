# K3：现成闭项的封顶 (K3Cap)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-10 13:02 至 13:31 |
| 工具调用 / agda 编译 (粗数) | 87 / 16 |
| token (usage 字段，按消息去重) | 输出 167112；新写入缓存的输入 433966；读缓存的输入 19468185；其余输入 138 |
| 写过的仓库文件 | `K3Cap.lagda.md`, `K3CapHtFeed.lagda.md`, `K3CapOutputDriven.lagda.md`, `K3CapRadical.lagda.md`, `K3CapRecB.lagda.md`, `K3CapSan.lagda.md`, `K3CapThird.lagda.md` |
| 文件前缀 | `K3Cap` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-10 晚: 构造路与 K3 返回并复核; 派出第一次回灌 (主审)” 一节 |
| 主审复核后的一句结论 | 五个现成闭项都只得到封顶的编译事实，没有条件覆盖的实填，没有一条是值上界；七件冷编退出码全 0 |

## 简报原文

你是 Agda 形式化研究的一路执行者 (判定题: 把 "读法封顶" 从判断变成编译事实). 仓库: <仓库> (作者 choukh 的大数数学形式化). 请全程用中文思考与写作.

### 先读 (按顺序)
1. `AGENTS.md` (纲领与全部约定, 必须遵守).
2. `probes/Survey/EBOHandbook.md` 的 §3.1, §4, §5.
3. `probes/Survey/RR5-SoftStops.md` 的 §3.2 与 §5.2 (R4); `probes/Survey/RouteReview3.md` 的 §1.2 (障碍 C), §1.4, §2 的 O1, 以及 §5.5 (乙线五轮: O1 只对一个候选做过, 结果是 `no-ω-target`); `probes/Survey/RR4-Fable52.md` 里 K3 的部分; `probes/Survey/SkeletonAudit.md` (各闭项经固定类型因子化的 refl 级事实 `fac-*`).
4. 已有的工具与先例: `probes/OCF/Align/TreeLevels.lagda.md` 与 `TreeLevelsRound2.lagda.md` (`Cover.terminal`, `ChainDom`, `GeneratedCover`; 对候选 `LevelNoKFold` 的诊断 `no-ω-target`), `probes/OCF/Align/TerminalFoldAccept.lagda.md` (终点参照 `reference` 与值序), `probes/Survey/EBOEndgame.lagda.md` (各候选的端到端评估, 多为判断).
5. 五个候选闭项: `probes/OCF/Lean/ThirdTm.lagda.md` (`TΛ`), `probes/OCF/Lean/OutputDriven.lagda.md` (`closed`, `closedGrid`), `probes/OCF/Align/RadicalValueNativeFinal.lagda.md` (`closed`), `probes/OCF/Align/HtFeedClosed.lagda.md` (`TΛ`), `probes/OCF/Lean/RecB.lagda.md` (`Tω`).

### 背景
这些闭项都是合法的、有 FGH 的布劳威尔树闭项, 但 "它的序数值到哪里" 只有读法 (判断) 或很低的下界, "它的类型装不下更高的站" (障碍 C: 坍缩到固定类型, 有损读回) 也只是判断加一些 refl 级的因子化事实. 第三次审查的三路都把 "对每个候选写一条条件覆盖定理, 写不出时失败点就是它的类型封顶" 列为第一件该做的事 (O1); 实际只对一个候选做了. 这使得 "现成闭项里有没有值得继续的候选" 至今靠判断.

### 你的目标
对上面五个候选 (六个闭项名) 逐个给出**编译事实**, 二选一:
- **(甲) 条件覆盖定理:** 照 `Cover.terminal` 的模板, 写出记号项到该候选对象类型的解释 ι 所需的接口 (后继一步, ω-共尾一步, 以及对一切 k 的 `ι (EBOψ k) ≤ᵛ T`), 并把 ι 实际定义到**第一个需要 Ω-共尾派发的站** (即第一个要求折叠在某个 Ω 结点处按 "目标层对结点层" 分情况的站; 各候选这一站在哪里由你定并说明). 说明到这一站为止接口的每个字段是否实填.
- **(乙) 封顶的编译事实:** 一条定理, 说明 ι 的像类型装不下某个具体的站 (形如 `no-ω-target`: 某个必须的折叠目标、层号或坐标在该候选的类型里没有对应的项; 或该候选的运行在某一步之后与一个更小的固定对象定义性相等). 前提可满足; 只否定写明的形状, 不把它说成 "这个候选的值不超过某某" (那是值上界, 需要另外的证明; 能证就证, 不能就明说没有).

每个候选设一个时间盒: 读懂它的对象类型与折叠的数据流 → 定位第一个 Ω-共尾站 → 写 (甲) 或 (乙). 时间盒内两者都写不出的, 交 "未走通" 加精确的卡点 (哪个定义, 哪个类型报错), 然后做下一个. **不要在一个候选上耗尽.** 建议次序: `HtFeedClosed.TΛ`, `RecB.Tω`, `ThirdTm.TΛ`, `OutputDriven.closedGrid`, `RadicalValueNativeFinal.closed`.

### 纪律
- 这是第 4 层 (验收侧), 可以导入记号模块; 文件头注明. 不改任何候选的定义.
- 这些候选的模块有的很重. **不要删别人的 `.agdai`, 不要用 `--ignore-interfaces`.** 若导入某个候选导致重新检查大量模块或退出 251, 记下事实, 换一个更小的导入点 (只导入定义对象类型与折叠的子模块), 或把该候选标 "编译受限, 未做".
- "读法" 与 "值" 分开: 没有值定理的地方不写值的结论. 有限测试明确标为测试.
- 你的结论会被用来决定哪些候选值得继续投入, 所以宁可少而硬.

### 止损
五个候选各自给出 (甲), (乙) 或 "未走通" 之一后交回. 整体上若前两个候选都在同一处卡住 (例如值序的搬运), 先把那个共同的卡点写成一条编译陈述再继续.

### 硬性约束
- 选项 `--safe --without-K` (可加 `--lossy-unification`). 无公设, 无洞, 无停机或正性编译指示, 无 trustMe. 不开 K. Funext 只准作前提出现在标明 "条件" 的文件里.
- **只新建文件**, 前缀 `K3Cap`, 放 `probes/OCF/Align/`, 中文 literate `.lagda.md`. 不改任何已有文件 (包括 README, LOG, RESULTS); 不动 `src/`, `archive/`.
- 编译: 从仓库根目录 `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>`. 堆上限 6G. **同一时刻只跑一个 agda** (另有四路在并行编译). 退出码不经管道: 0 通过, 42 类型错误 (先看日志首行是不是 LibraryError), 251 堆耗尽 (不是类型错误也不是通过), 124 超时.
- 只删你自己模块的 `.agdai` (在 `probes/_build/2.8.0.2/agda/OCF/Align/`).
- 临时文件与日志只写到 `<实验目录>/agents/k3/`. 不写 `/tmp` 的其它地方, 不装包, 不 `rm` 自己文件之外的东西, 不 `pkill`, 不提交, 不推送, 不再派子智能体.
- 仓库文件里不写本机路径 (包括临时日志路径).
- 结论分三档: 编译过的定理 / 有限测试 / 判断. "穷尽" 一律标判断. 强度写 ψ₀(Ω_x), 不用 ψ₁. 不用 "自然", "只差" 一类形容.

### 交回时的报告 (中文, 简明)
1. 先一段: 对纲领与目标意味着什么 (五个候选里有没有不封顶的; 封顶的各封在哪).
2. 一张表: 候选 | 第一个 Ω-共尾站在哪 | 结果 (甲/乙/未走通) | 定理名 | 档.
3. 文件清单; 每个模块删自身接口后冷编的退出码; 哪些候选因编译受限没做.
4. 未完成项与卡点.
5. 新增代码行数.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-10 13:30 (UTC)：

作者刚定了研发阶段的文字预算, 从现在起适用; 已写好的文件不必返工, 也不用回复这条消息, 继续你的任务.
1. 每个模块文首不超过 5 行: 判决与档位, 做了什么, 不否定什么, 入口指向. 代码之间的文字只写范围与不显然的定义理由, 不复述代码.
2. 不写只有导入语句的报告文件. 入口文件只放导入与不超过 10 行的判决. 报告只在最后交回时写一次 (写在回报里); 冷编表, 切片表, 成本表, 生成脚本不进仓库文件.
3. 一次性的试验放你的临时目录, 用纯 .agda; 要留下的结果才进仓库写成 literate.
4. 编译日志落文件, 只看首个错误附近; 查签名用检索, 不整篇读.

## 回报原文

### K3 (R4) 交回: 五个现成闭项的封顶位置

#### 1 对纲领与目标意味着什么

五个候选全部交 (乙) 封顶的编译事实, 没有一个交 (甲). (甲) 的三个前提 (后继一步, ω-共尾一步, 全塔上界) 是各候选至今没有的值定理, 我没有去填. **没有一条是值上界**: 没有证明任何闭项的序数值不超过某个具名序数, 也没有证明运行上的损失使值下降; 各入口原有的读法既没被证实也没被推翻.

候选分两类:

- **类型封顶的三个** (`HtFeedClosed.TΛ`, `RecB.Tω`, `RadicalValueNativeFinal.closed`): 层号的下标类型里缺一种极限. 它们的第一个 Ω-共尾派发的站在类型之内, 封顶在更高处 (分别是层号 Ω₂, 第 ω 个底, Ω-共尾的高度).
- **类型不封顶的两个** (`Third.TΛ`, `OutputDriven.closed`/`closedGrid`): 层号类型一路到底的并 `SΛ`. 但从第 1 站起, 每一站下降的第一次回灌读到的源就是 Ω-共尾下标对应的结点, 跨底折叠在那里不按 "目标层对结点层" 分情况, 定义性地只走代表坐标一支. 这一条连 "闭项的实际运行里到达" 也是编译事实.

所以 "有没有不封顶的": 按类型, Third 与 OutputDriven 不封顶; 按运行, 它们在第一个 Ω-共尾站就不派发. 五个里没有一个是 "类型够, 且在 Ω-共尾站按规则派发, 只缺第 4 层" 的.

#### 2 结果表

括号里的 ψ₀(Ω_x) 是按各入口约定的读法, 属判断. "第一个 Ω-共尾派发的站" 一列除 Third/OutputDriven 外都是读代码得到的判断.

| 候选 | 第一个 Ω-共尾派发的站 | 结果 | 定理 (文件) | 档 |
|---|---|---|---|---|
| `HtFeedClosed.TΛ` | 最高层 `hs Ωᴴ` (ψ₀(Ω_{Ω+1})); 在类型之内, 派发是公共世界里的 `cmpH` | (乙) 类型, 封在层号 Ω₂ | `no-Ω₂-top` (记录 `Top H LgH Below` 无实例: 没有高度在 H 的一份保序合法拷贝之上), `no-retract-H`; 对照 `Ω₁-instance` (同一记录以 `A` 为指标有实例) — K3CapHtFeed | 定理 |
| `RecB.Tω` | 第 1 个底的边界 (层号 Ω); 在类型之内, 派发是 ℕ 上分情况加可数界下 `cmpB` | (乙) 类型, **签名一级**, 封在第 ω 个底 (层号 Ω·ω) | `no-ω-bottom`, `cd-Ωfree`, `dcI-suc` (refl), `Tω-shape` 等 (refl) — K3CapRecB | 定理是关于 ℕ 与 Cd 的; "底只按 ℕ 编号" 是读签名, 不是定理 |
| `Third.TΛ` | 第 1 站 (第 2 个底向第 1 个底下降) 的第一次回灌 | (乙) 运行, 就在这一站 | 一般: `ΦX-rep`, `ΦX-const`, `ΦX-old`, `ΦX-chain`, `chain-first` (refl), `san-Ωfree`, `san-kept`, `keep-washed` (refl), `tp-bot` (refl) — K3CapSan. 实例: `TN-first` (refl), `first-step-chain`, `first-src-old`, `first-item-rep`, `third-rep`; 独有 `comp-bound-zero`, `comp-pos`, `comp-Pos` (世界固定, 分量种类的界是 0) — K3CapThird | 定理 (多为 refl) |
| `OutputDriven.closed`, `closedGrid` | 同上 | (乙) 运行, 同上; 比 Third 少一处 (世界不冻结) | `TN-first`, `first-step-chain`, `first-src-old`, `first-item-rep`, `driven-rep`, `driven-san-Ωfree`; `rep-is-bound` (refl: 代表坐标是世界里的实际界) — K3CapOutputDriven | 定理 (多为 refl) |
| `RadicalValueNativeFinal.closed` | 高度从 `h₀` 升一级 (层号 Ω); 在类型之内, 派发是段内三歧 `HtB.tri` | (乙) 类型, 源族封在 Ω-共尾的高度 (层号 Ω²); 闭项另固定在码 `ω²ᶜ` | `no-Ω-height` (任一 `S : HtB` 里没有高度在 `Ordᴵ` 的严格保序拷贝之上, 只用字段 `rk`, `rk<`), `no-copy`; 对照 `nat-copy` (同一记录以 ℕ 为指标有实例) — K3CapRadical | 定理 |

Third/OutputDriven 的编译链 (每环都是定理): `TN (suc n) = desc n first-step _` → `first-step` 是一条链 → 链第 0 项回灌种子 `fl (suc n)` → 回灌出的坐标是 Ω-结点 → 读到的源是指标分量旧种类的结点 → `ΦX` 在其上等于代表坐标一支上的折叠 (`first-item-rep`). 把分支族换成那一支的常值族, 折叠值不变 (`ΦX-const`).

#### 3 文件, 冷编, 编译受限

都在 `<仓库>/probes/OCF/Align/`:

- `K3Cap.lagda.md` (入口, 只有导入与判决)
- `K3CapHtFeed.lagda.md`
- `K3CapRecB.lagda.md`
- `K3CapSan.lagda.md` (Third 一族共用的一般陈述, 对任一底与世界)
- `K3CapThird.lagda.md`
- `K3CapOutputDriven.lagda.md`
- `K3CapRadical.lagda.md`

七个模块各自删自身接口后冷编 (6G, 单路依次): **退出码全 0**, 每个日志只有 1 行 `Checking` (没有重新检查任何候选模块), 峰值 0.36G 到 0.78G. 选项 `--safe --without-K --lossy-unification`; 代码块里公设, 洞, 停机/正性指示, `trustMe`, Funext 均为 0; 无本机路径. `importclosure.py OCF.Align.K3Cap`: 禁用表命中 0 (这一组实际没有导入记号模块, 仍按任务标第 4 层). **没有候选因编译受限而未做.**

#### 4 未完成项与卡点

- **(甲) 一个也没有.** 共同卡点不是接线: ι 的两条一步律是跨站 (HtFeed 是跨 `Λ` 实例) 的值比较, 各候选都没有这类值定理. 我没有把它写成编译陈述 (写出来只是 `Cover.terminal` 的平凡实例化).
- **RecB 的结果弱.** 入口自己已写明底的下标是 ℕ; 我能加的定理只到 `ℕ`/`Cd` 一级, 没有 "不存在别的折叠" 的定理.
- **Third/OutputDriven 的另两处损失未验证到达.** "Ω-共尾的层上留下的结点坐标被洗成无 Ω-结点的树" 与 "Ω-共尾层的地板取底分量" 是对一切底成立的定义性事实, 但在闭项实际运行里是否到达, 没有验证.
- **HtFeed 与 Radical 在类型之内各站** 没有任何新的值结论.
- 引用的已有定理 (`GridCheckCountableSan`, `GridBaseTowerAccept`, `TotalValue` 的下界) 本次没有重编.
- 各条否定只否定写明的形状 (下标类型里 "某指标类型的严格保序拷贝加一个顶"), 不否定换下标类型或换派发规则后的同族候选.

偏离与事故: (1) 中途收到文字预算的通知后, 入口已削到只有导入与判决; 其余六个文件的文首在通知前写成, 超过 5 行, 按通知未返工. (2) 一次 `rm` 用了变量拼路径, 被安全检查拦下未执行; 改用字面绝对路径, 只删过上述七个模块自己的 `.agdai`.

#### 5 新增代码行数

agda 代码块里非空非注释行共 **458**: K3CapSan 127, K3CapThird 86, K3CapOutputDriven 81, K3CapRadical 61, K3CapHtFeed 55, K3CapRecB 40, K3Cap 8.

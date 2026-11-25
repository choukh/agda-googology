# 写在第 K 层的树上，否定路 (YiRawNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-10 23:59 至 00:40 |
| 工具调用 / agda 编译 (粗数) | 59 / 14 |
| token (usage 字段，按消息去重) | 输出 256769；新写入缓存的输入 805631；读缓存的输入 9963234；其余输入 86 |
| 写过的仓库文件 | `YiRawNegChain.lagda.md`, `YiRawNegLift.lagda.md`, `YiRawNegModel.lagda.md`, `YiRawNegNorm.lagda.md`, `YiRawNegOmega.lagda.md` |
| 文件前缀 | `YiRawNeg` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: "写在第 K 层的树上" 的构造路与否定路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 接口记录偏弱（有便宜的模型）；根链的判据与限制形式；部分和与归一值不降、可升高；公共上界含 Ω 结点时只有路径相连的位置对可比；五件冷编退出码全 0；没有值 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "乙线: 把折叠写在第 K 层的树上, 否定路": 对同一个共用接口写编译过的否定定理与边界定理, 并给构造路探路. 另一路 (构造路, 前缀 `YiRawFold`) 同时在做构造. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条 (尤其第 3 条壁垒, 以及 "交替路线" 一条: 全分支的高层比较被禁止); "量化域先取带证据的读回域" (反例对象不在读回域内的否定读作 "谓词太宽"); "律带公共上界, 构造与否定配对"; Agda 一节; "结论的写法" (否定要编译定理且否定的确实是那条路线; 前提要可满足; 穷尽是判断; 归到已知的墙要逐条核机制).
2. `probes/Survey/EBOHandbook.md` 只读 §3.1, §3.13, §4.1 到 §4.5, §5.4. `probes/Survey/Reports-2026-11-10/README.md` 只读 §2 里 "乙线第 3 步, 构造" 与 "乙线第 3 步, 否定" 两段; 要细节再读同目录的 `YiLvFold.md`, `YiLvNeg.md` (上一轮两路的回报原文).
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - 块: `RR5IrrCore`, `RR5IrrCheck` (`up`, `upT`, `Ω̂`, `tw`), `YiIrrIf` (`CP`, `Legal`, `R`, `read0`).
   - **本轮的共用接口 `YiRawIf`**: `Tgt`, `tlev`, `dispatch`, `dispatch-complete`, `dispatch-sound`, `test-keep-ω`, `test-cross`, `tw₃-is-top`, `branch-is-top`, `IsLim`, 记录 `RawFold`. 上一步的接口 `YiLvIf` (`Plain`, `lev`, `shift`, `Tri`, `Compare`, `compare`, `Kept`).
   - 上一轮否定路 (写法与可复用的定义): `YiLvNegCompare` (`At`, `PosIrr`, `prefix→tri`, `no-both`, `lev-legal`), `YiLvNegKeep` (`KeepRows`, `bare-way→lpo`, `LPO`, `Locate`, `oracle-model`), `YiLvNegCert` (`CertRows`, `Forced.coherence`, `antisym`), `YiLvNegCanon` (`ccompare`, `ccompare-slot`, `ccompare-levels`, `ccompare-shift`), `YiLvNegRestrict` (`restrict`, `Coh`, `CohDom`, `ψ-legal-coh`, `independent-differ`), `YiLvNegCum` (`cum`, `norm-guard`). 更早的: `YiIrrNegWide` (`IrrSearch`), `YiIrrNegWideDecide` (`IrrDecide`), `YiIrrNegModel`.
   - 上一轮构造路: `YiLvFold` (以派发为参数的折叠, 对任意派发合法), `YiLvFoldBase` (`Way`, `nodeAt`), `YiLvFoldAdd` (`plus`), `YiLvFoldLim`, `YiLvFoldTw3`.
   - 参照: `probes/OCF/Barrier.lagda.md` (壁垒定理), 以及仓库里已有的 `dec→WLPO`, `Trich₂→WLPO`, `noBT` 一类结果 (用检索找到它们所在的文件).
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么

乙线: 层号是树 (`LF`), 第 k 层的树是 `Raw k`. 上一轮 (层号任意可数, 目标是塔的第 3 项 `tw 3`) 的结果: 写在 `LF` 上, 以派发为参数的折叠做成了, 但 **输出合法对任意派发都成立, 闭项合法不携带强度信息**; 只读裸层号而处处完全的派发推出 LPO; 证书不作数据的写法在宽定义域上被排除.

作者 2026-11-11 定: 主攻 **把折叠写在第 K 层的树上**. `Raw K` 的结点 `G.lc r c t g` 自带位置 `r : Pre K`, 公共上界是字面的 K, 同一个 K 里两个位置用规范比较 `ccompare` 分路 (读相关的 `Legal K`). 接口 `YiRawIf` 已把派发 `dispatch` 及其完全性, 不多保留写成定理, 并给了记录 `RawFold` (`Φ`, `keep-law`, `fold-law`, `position`, `legal`). `tw 3` 的折叠在这种写法下是 `top : Raw (tw 2)` 处的值; 第 η 支是 `top : Raw (read0 η)` 处的值, 它读 `Legal (read0 η)`, 所以根上的链点要带相关的合法性.

### 2 任务, 按次序; 每条交编译过的定理, 或写明 "没写成"

主审的看法都是判断, 没有验证; 你的任务是把能定的定成编译定理, 并挑战其余.

**R1 记录 `RawFold` 本身.** 它可满足吗? (i) 找一个便宜的模型 (不必是真的折叠), 说明各律同时可满足, 或指出哪个字段不可满足, 哪两个字段互相矛盾. (ii) `keep-law` 只说 "输出是某个层号对的槽位上的保留结点", 没有说是哪个槽位: 由 `position` (两份无关证书, 字面第一位置) 加 `keep-law` 能不能推出槽位与 `L` 无关? 给出依赖 `L` 选槽位的实例, 或证明不能有. (iii) `legal` 不带 "`L` 一致" 的前提: 找一个 `Plain` 的 K 与两份 (或一份不一致的) `Legal K`, 检验任何满足 `keep-law`, `fold-law`, `position` 的 `Φ` 在极限层号处是否被迫违反 `legal`; 或说明为什么不被迫. 这一条决定构造路要不要带一致性.

**R2 `Raw K` 之内的搬运.** `G.em i T` 把低一层的树嵌进来; 极限层号 `lim f` 里, 目标在第 m 支, 树在第 n 支 (m ≠ n) 时, 折叠要把一边搬到另一边. 检验: (i) 沿 `L` 的路径把 `Raw (f n)` 的树提升到 `Raw (f m)` (n < m) 的函数能不能写出, 它保不保持第一位置与合法性; 写出来, 或给出过不去的子句与报错原文. (ii) 这个提升依赖路径的选择吗 (同一个 K 的两份证书给出不同的提升)? 若依赖, 对折叠的 `position` 意味着什么. 这一条是探路, 正面结果同样交.

**R3 根上的链.** 链点带相关的 `Lgl zero η` 时: (i) 上一轮 `fold-legal-reads-certificate` 说旧折叠的输出证书随输入证书变. 对 "链点的证书由输出的合法性引理生产" 这种链, 写一个最小记录 (分支值 `E : (η : R) → Lgl zero η → R`, `E-legal`, 链的下一点是这一点加 `E`), 检验根的极限合法需要什么: 给出它等价于或蕴含的一条关于 `E` 的陈述 (例如 `E` 沿限制单调, 或 `E` 不依赖证书), 并说明哪一种在不用函数外延时可证. (ii) 只在链上归一 (`YiLvNegCum.norm-guard`): `cum` 之后的链点还压得住原来的累计吗? 检验 `Cp zero v (cum v)` 或它的值版本是否成立; 归一后的链与不归一的链的第 n 点是什么关系. 成立就证, 不成立给编译的反例.

**R4 下一步的预告: 公共上界含 Ω 结点.** `tw 3 = up (tw 2) top`, 公共上界 `tw 2` 不是 `Plain` 的: 它的位置里有 `(η , e , r)`, 即第 η 支 (带相关守卫 `e`) 里的位置. (i) 对 `K = tw 2` 陈述 `Compare` 的同形命题 (同一个 `tw 2` 里任意两个位置的三路), 检验它是否推出某条全知原理 (不同的 η, η′ 上的两个位置要比较两个第 0 层的坐标); 这是 "两个下标有字面的公共上界" 在上界含 Ω 分支时够不够的问题. 归到壁垒或 W 墙之前逐条核机制. (ii) `tw 3` 的折叠实际需要这种跨支比较吗? 按 `top : Raw (tw 2)` 的展开走一遍: 根上是层号 0 的结点, 各支经 `em` 进到 `Raw (read0 η)`; 说明哪些比较留在同一支里. 能写成定理就写 (例如: 只在同一支里比较的 `Compare` 变体对 `tw 2` 成立), 否则交判断并标明. 这一条不影响本轮构造, 是给第 4 步 (层号不可数) 划界.

**R5 挑战.** 主审认为 `Raw K` 上的折叠可以避开上一轮的三个障碍 (裸层号, 无关证书的宽定义域, 两份独立证书). 找一个它避不开的地方, 或指出主审的哪条分析已被你的定理支持或排除. 允许只交判断, 但要标明.

做不完不要紧: R1, R3 是主要的, R2, R4 是探路. 每条定理写清它否定的是哪一种写法, 不否定什么; 反例对象是否在 `tw 3` 的读回域内; 前提的实例. 不把 `IrrSearch`, `IrrDecide` 说成矛盾.

### 3 规则

- **只新建文件**, 前缀 `YiRawNeg` (如 `YiRawNegModel`, `YiRawNegLift`, `YiRawNegChain`, `YiRawNegOmega`), 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiRawIf`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiRawFold` (构造路) 与 `YiLvVal` (值定理), 不要动它们的文件, 也不要依赖它们 (它们在变). 对共用接口的增补写在你自己的文件里, 并在回报里说.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 所在文件文首标 "条件".
- 否定结果写成编译过的定理; 有限样本的测试标为测试. 没有编译定理的地方只写 "未走通" 或 "没写成". 每个否定定理与条件定理的前提给一个实例或说明为何可满足.
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件; 编译表不进文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写精确名字, 不用通配: 构造路的前缀与你的前缀开头相同).
- 你的临时目录: `<实验目录>/agents/rawneg`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 通过 (读记号的验收文件除外, 文首标明); 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 一段话, 先说对纲领与目标意味着什么 (哪些写法被编译定理排除, 哪些被支持, 构造路该注意什么, 第 4 步的界在哪).
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表, 按 R1 到 R5: 名字, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 每条否定写: 否定的是哪一种写法; 反例对象是否在读回域内; 前提的实例.
4. 正面结果单列.
5. 没写成的条目与第一个障碍 (检查器报错原文, 缺的引理的 Agda 类型).
6. 偏离与事故.
证书, 闭项, 值分开说; 不用 "只差", "自然" 一类形容.

## 回报原文

### 乙线 "把折叠写在第 K 层的树上" 否定路回报 (前缀 YiRawNeg)

#### 1 判决

**对纲领与目标。** 没有触到纲领四条，没有读记号，没有折叠，没有值，强度不变。交出的是关于接口 `YiRawIf.RawFold` 的树侧判据，都是编译定理或带实例的条件定理，不用函数外延。

**被编译定理排除或收窄的写法：**
- `legal` 不带一致性前提，同时 `top` 在极限层号处逐项 (`TopLim`)，同时 `Φ` 在 (`base`, `top`) 处读 `L` 或 `Plain` 的证明：`Forced.forced-coherence` 逼出这一处换证书字面相等，`function-equality-required` 逼出极限处两个函数字面相等。是 "要求"，没有证它不可得。
- "换 `L` 输出相等或可比"：带 `CrossRow` (沿 `L` 的路径提升) 与 `BranchRow` 两行的任何 `RawFold`，在 `Kᶜ` 的两份闭证书下输出互不为第一位置 (`Rows.reads-L`)。
- 根链的单调写成两份独立证书 (`FreeMono`)：逼出分支值与证书无关 (`free→const`)，在极限行上要函数相等 (`free-needs-function-equality`)。
- 公共上界取 `tw 2`：`Compare` 的同形命题不可满足 (`no-compare-tw2`)；放宽成判定 `At` 推出 LPO (`dec-at→lpo`)；`keep-law` 与 `fold-law` 原样搬过去推出 WLPO (`keep-fold→wlpo`)。

**被支持的：** `RawFold` 四条律同时可满足，不要任何原则 (`canonical`, `moved`)；`Raw K` 内的提升 `wrap` 写成，保持第一位置、合法性、嵌套证据、读回；跨公共上界的一条 `cross` (限制形式) 由 `position` 加两行得到；根的极限合法等价于 `StepMono`，限制形式推出它并且穿过极限行不要函数相等；带一致性时极限层号处 `top` 的合法性由各支得到 (`top-legal`)；`tw 2` 上有路径相连的位置对可比 (`compare-link`)。

**构造路该注意 (前五条有定理，第六条是模型上的观察)：**
1. `legal` 要带一致性前提 (`CohLg` 一类)，或者 (`base`, `top`) 那部分的定义不接触 `L` 与 `Plain` 的证明，或者极限处 `top` 不取逐项。取部分和时值不降，但在常值列上严格升高 (`lim≼psum`, `psum-inflates`)。
2. `Plain K` 的证明在接口里也是相关参数，两份证明不用函数外延证不出相等；跨 `K` 的陈述里它也要取限制 (`restrictP`)，或先过 `plain-fix`。
3. `RawFold.position` 只在同一个 `K` 里；根上相邻链点的公共上界不同，要 `cross`。极限层号里 `top` 没有前驱 (`DnT (lim f) a = ⊥`)，这一处只能靠极限行。
4. 不归一的根链在 "带一致性的 `legal`" 下还要 "输出证书一致" (`CohBranch.E-coh`)；归一的链不要 (`NormRoot.root-legalᶜ`, `cum-coh`)，但它改了链的行，值可以严格变高 (`inflate`, `const-strict`)。
5. 输出对 `L` 的字面依赖来自提升路径，规范槽位救不了；一切跨证书的陈述用限制形式。
6. `keep-law` 不约束保留结点的下界与分支 (`canonical` 的保留结点下界取零，各支取常值)，也不约束槽位与 `L` 无关 (`by-compare`)。建议接口增补 `SlotFree`，`canonical` 满足它。

**第 4 步的界。** 律的定义域不能取成含 Ω 结点的公共上界的一切位置对；可以取成 `Link`：有一个位置在主干上，或两支的坐标有字面的第一位置路径 (含同一支)。第 3 步不受影响。

#### 2 文件表

都在 `<仓库>/probes/OCF/Align/`。代码行 = agda 块内非空非注释行。冷编译 = 删这五个模块自己的 `.agdai` (逐个写精确名字) 后按依赖序各编一次，`-M6G`，每个约 2 秒。

| 文件 | 代码行 | 冷编译 |
|---|---|---|
| `YiRawNegModel.lagda.md` | 245 | 0 |
| `YiRawNegChain.lagda.md` | 258 | 0 |
| `YiRawNegLift.lagda.md` | 291 | 0 |
| `YiRawNegNorm.lagda.md` | 284 | 0 |
| `YiRawNegOmega.lagda.md` | 185 | 0 |

- 依赖：Model ← {Chain, Lift, Norm}；Omega 只依赖接口与上一轮文件。没有导入 `YiRawFold*`、`YiLvVal*`。
- `importclosure.py OCF.Align.<模块>` (无 `--only`) 五个都 OK，禁用表命中 0。
- 禁用构造检索为 0；文件里不出现 `Funext` 一词，没有本机路径。
- 日志在 `<实验目录>/agents/rawneg/` (`cold-*.log`, `closure-*.log`)。

#### 3 定理表

除标明者外都是编译定理。

##### R1 记录 `RawFold` 本身 (`YiRawNegModel`)

| 名字 | 白话 | 档 |
|---|---|---|
| `Cheap.model`, `canonical` | (i) 以派发为参数的便宜模型；用接口的 `dispatch` 时是 `RawFold` 的实例，四条律同时成立，对任何 `L` | 编译 |
| `by-compare`, `by-compare-slot₀/₁`, `by-compare-reads-L` | (ii) 把 `ccompare` 换成 `compare` 仍是实例；`Kᶜ` 的两份证书下保留槽位是 0 与 1 | 编译 |
| `SlotFree`, `canonical-slot-free` | (ii) "槽位换 `L` 不变" 写成陈述，`canonical` 满足 | 编译 |
| `Forced.forced-coherence` | (iii) `RawFold` 加 `TopLim` ⟹ `Φ K pl L base top ≡ Φ K pl′ L′ base top`，对任意两份 `Plain` 证明与两份 `Legal` | 条件 |
| `Forced.function-equality-required` | (iii) 同前提 ⟹ 极限层号处两族任意证书给出的输出函数字面相等 | 条件 |
| `CohLg`, `mixed-coherent→same` | 一致性前提之下，上面用的混合证书只在 `L′ ≡ L` 时合格 | 编译 |
| `plain-fix`, `plain-fix-free` | `Plain` 的证明可由无关的证明按层号重算，结果与输入定义性无关 | 编译 |

- (ii) 的结论：`position` 加 `keep-law` 推不出槽位与 `L` 无关。反例对象 `Kᶜ = read0 κ` 与两份证书都是闭的；`Kᶜ` 是不是 `tw 3` 的折叠走到的链点没有判定。
- (iii) 的结论：四条律本身不逼出对 `legal` 的违反 (`canonical` 对一切 `L` 成立，含不一致的闭实例 `mixedᶜ`)。加 `TopLim` 后被逼的是字面无关。
- `Forced` 否定的是 "无前提 `legal` + 极限逐项 + 这一处读证书" 的组合；不否定 `RawFold`，不否定带一致性的 `legal`。前提的实例：`canonical-top-lim`, `by-compare-top-lim` (便宜的模型在这一处不接触两个参数)。
- 判断：把 `L` 逐支传过极限的折叠，不用函数外延证不出那条函数相等。

##### R2 `Raw K` 之内的搬运 (`YiRawNegLift`)

| 名字 | 白话 | 档 |
|---|---|---|
| `wrap`, `wrap-cp`, `wrap-dn`, `wrap-lgl`, `wrap-nested` | (i) 沿 `CP a b` 逐步包 `em` 的提升；保持第一位置、合法性、嵌套证据；对一切层号 | 编译 |
| `wrap-read`, `wrap-read-free` | 提升后读回不变，读回与路径无关 | 编译 |
| `moved` | (i) 做了跨支搬运的 `RawFold` 实例：n < m 提升树，m < n 搬目标位置并沿层号相等搬回输出；四条律都过 | 编译 |
| `lift-form`, `lift-apart` | (ii) `Kᶜ` 的两份证书给出的提升是 `em tt (em j T)`，j = 0, 1，互不为第一位置 | 编译 |
| `Rows.out-j`, `Rows.reads-L` | (ii) 带 `CrossRow` 与 `BranchRow` 的任何 `RawFold`：树 `em 0 zero`，目标在第 1 支的根，两份证书下的输出互不为第一位置 | 条件 |
| `moved-cross`, `moved-branch`, `moved-reads-L` | 上一条前提的实例与结论的实例 | 编译 |
| `toRaw`, `fromRaw`, `from-to`, `to-from`, `gd-to`, `gd-from` | `Low K r` 与 `Raw (lev K r)` 之间逐子句恒等的往返，守卫随之往返 | 编译 |

- `Rows.reads-L` 否定的是 "换 `L` 输出相等或可比"；不否定同一个 `L` 之内的 `position` (`moved` 满足它)。两份证书闭且各自一致 (`YiLvNegRestrict.κ-coh`)；是不是链点没有判定。
- `moved` 的结点处理仍是便宜的 (各支取常值)，不是折叠。

##### R3 根上的链 (`YiRawNegChain`, `YiRawNegNorm`)

(i) 不归一的链，证书由输出的合法性引理生产：

| 名字 | 白话 | 档 |
|---|---|---|
| `Branch`, `Root.step→root`, `Root.root→step` | 根对一切起点合法，当且仅当 `StepMono` (分支值沿链的一步单调) | 编译 |
| `Root.restr→step` | 限制形式 `RestrMono` 推出 `StepMono`；用到 `restrict-add-weak` | 编译 |
| `Root.restr-lim` | 限制形式在极限行上由各项得到，不要函数相等 | 编译 |
| `Root.free→const`, `Root.free-needs-function-equality` | 独立证书形式逼出分支值与证书无关；在极限行上要函数字面相等 | 编译 |
| `reading`, `reading-root-legal`, `reading-not-free`, `reading-not-restr` | 一个读证书的分支值：根对一切起点合法，但两种较强形式都不满足 | 编译 |
| `CohBranch`, `CohRoot.restr→step`, `CohRoot.step→root` | 合法性引理只对一致证书给出时，链点带一致性，要 `E-coh` | 编译 |
| `Bridge.cross` | `K` 是 `K′` 的字面第一位置时 `Φ K … base top ⊲ Φ K′ … base top`，小的一边取限制；前提是 `EmSucTop` 与 `TopLim`，不用 `legal` | 条件 |
| `Bridge.restr-mono`, `Bridge.root-legal` | 第 η 支的 `top` 折到第 0 层作分支值时满足限制形式；加无前提的 `legal` 则根合法 | 条件 |
| `Bridge.top-legal` | 极限层号处 `top` 的合法性，由各支的合法性加相邻两支 (`Plain` 证明与 `Legal`) 沿路径一致得到 | 条件 |

- 回答 "哪一种不用函数外延可证"：限制形式。独立证书形式对读证书的分支值是一条函数相等的要求，没有证它不可得。
- 前提的实例：`plain`, `plain-free`, `plain-lim`, `plain-coh`, `plain-coh-root`；`canonical-em-suc`, `canonical-root-legal`, `canonical-top-legal`。`canonical` 不是折叠，所以 `Bridge` 三条对真的折叠是条件定理。
- `root-legal` 用的无前提 `legal`，按 `Forced` 只有在这一处与 `L` 字面无关的 `F` 才有。

(ii) 只在链上归一：

| 名字 | 白话 | 档 |
|---|---|---|
| `cum-not-first`, `point-not-first` | 字面上不成立：`ω` 不是 `cum ω` 的第一位置；`1 + ω` 不是 `1 + cum ω` 的第一位置。`ω` 合法 | 编译 |
| `_≼_`, `_≺_` 及 `≼-refl`, `≼-trans`, `≺-irrefl`, 加法五条 | 第 0 层的树上值的序，本文件自己定义，没有对参照验收 | 编译 |
| `cum-above`, `point-above`, `cum-add` | 值上成立：`v ≼ cum v`；`c + v ≼ c + cum v`；`cum v + y ≼ cum (v + y)` | 编译 |
| `Compare.raw≼pt` | 分支值只读坐标且按值单调时，不归一的链第 n 点 `≼` 归一的链第 n 点 | 条件 |
| `inflate`, `cum-not-below`, `const-strict`, `const-not-back` | 反向不成立：`cum (ω+ω)` 严格高于 `ω+ω`；分支值取常值 ω 时两条链在第 2 点严格分开 | 编译 |
| `lim≼psum`, `psum-inflates` | 只在一个极限处取部分和：值不降；常值列上严格升高 | 编译 |
| `cum-coh`, `cum-restrict`, `NormRoot.cert-restrict` | 归一的链点的证书由树算出，一致，沿链的一步限制回来是前一点的证书 | 编译 |
| `NormRoot.root-legal`, `NormRoot.root-legalᶜ` | 归一的链：根合法只要分支值沿限制单调与各自合法；链的定义不调用合法性引理，不要 `E-coh` | 条件 |

- `raw≼pt` 的前提实例是常值 (`Const`)；真的折叠的分支值读证书，按值单调没有证。`NormRoot` 的前提实例：`plain-norm-legal`, `plain-norm-legalᶜ`。
- 折叠的输出是不是总落在归一不改值的那一类树上，没有判定。

##### R4 公共上界含 Ω 结点 (`YiRawNegOmega`)

| 名字 | 白话 | 档 |
|---|---|---|
| `no-compare-tw2` | (i) `Legal (tw 2) → ∀ q q′ → Tri …` 不可满足：两支上的层号 `lim (λ _ → 1)` 与 `1` 三路都无居留 | 编译 |
| `dec-at→lpo` | (i) 放宽成判定 "结点层在目标层的位置上"，对 `tw 2` 的一切位置对 ⟹ LPO | 编译 |
| `KeepFold₂`, `keep-fold→wlpo` | (i) `keep-law` 与 `fold-law` 原样搬到 `tw 2` ⟹ WLPO | 编译 |
| `locate→dec-at`, `oracle-model₂` | 后两条的前提在排中律的实例 `Locate` 下有模型，所以说的是 "拿不到数据"，不是矛盾 | 编译 |
| `compare-link`, `compare-up`, `compare-zero`, `compare-same-branch`, `unlinked` | (ii) 正面：`Link` 的位置对三路成立；反例对不满足 `Link` | 编译 |

- 归类，逐条核过：`no-compare-tw2` 的机制与旧块上的 `InaccTree.noBT` 相同，这里在当前块与 `Tri` 上重证；陈述里没有折叠，没有值，失败的是 `Tri` 的三个构造子。它不是 `Barrier.barrier` 的实例，那里的前提这里没有检查。
- 后两条的机制是 `YiLvNegKeep.bare-way→lpo`，对象沿用它的 `coordᴸ α` (守卫对一切 α 有闭形式)。
- 反例与探针的位置都带闭的相关守卫，探针树合法并带嵌套证据；它们是不是第 4 步的规范构造走到的 (目标，结点) 对，没有判定。可能读作 "律的定义域太宽"。
- (ii) 的走查是判断：`tw 3` 在目标 `base` 处，根结点层号 0，派发直接折叠，不比较；各支经 `em` 进到 `Raw (read0 η)`，其后的比较都在同一支里。支持它的定理是 `compare-same-branch` 与 `Bridge` (分支值只用 `Plain` 的公共上界上的 `Φ`)。

##### R5 挑战

- 裸层号：在 `Plain` 的 `K` 内避开了。依据是接口的 `dispatch-complete`, `dispatch-sound`，加上 `canonical` 说明两条律不要原则。到 `tw 2` 这个障碍以 `dec-at→lpo` 的形式回来。
- 无关证书的宽定义域：避开了。`canonical` 与 `moved` 对一切合法的 `ξ` 满足四条律，树的证书全程无关。
- 两份独立证书：只在 "同一个 `K`，同一个 `L`" 之内避开。三处回来，各有定理：极限层号的 `top` 经 `legal` (`Forced`)；根链跨 `K` (`cross` 是需要的增补，`free-needs-function-equality` 是独立证书形式的代价)；提升路径 (`Rows.reads-L`)。
- 判断，没有合成定理：做了搬运的折叠与无前提的 `legal` 不能同时有极限逐项的 `top` 行。

#### 4 正面结果单列

- 模型：`canonical`, `by-compare`, `moved`。
- 搬运：`wrap` 一组；`toRaw`/`fromRaw` 一组；`subst-cp`, `subst-lgl`。
- 跨公共上界：`restrictP`, `restrictP-read0`, `Bridge.cross`, `Bridge.restr-mono`, `Bridge.top-legal`。
- 根链：`Root` 的等价与两条推出；`CohRoot`；`NormRoot`；`cum-coh`, `cum-restrict`。
- 值的序：`_≼_` 一套，`cum-above`, `cum-add`, `raw≼pt`, `lim≼psum`。
- 比较：`compare-link` 一组；`canonical-slot-free`；`plain-fix`。

#### 5 没写成的条目

没有被检查器拒绝后放弃的条目，所以没有报错原文；下面都是没有去编码或缺引理。

| 条目 | 第一个障碍 |
|---|---|
| "读 `L` 的折叠在不一致的 `L` 上违反 `legal`" 的具体实例 | 只有蕴含式 `forced-coherence`；要一个真的读 `L` 的折叠，本路没有 |
| 那条函数相等不可得 | 没有证，只是判断 |
| 与 `L` 无关的规范提升路径 | 没写。缺 `cp-compare : ∀ x → Plain x → Legal x → ∀ {u v} → CP u x → CP v x → CP u v ⊎ CP v u`，以及极限处最小可行分支的唯一性 (`YiLvNegCanon.canon-const` 的路径版本) |
| 限制形式、`E-coh`、按值单调，对真的折叠 | 没有可检验的折叠；`Bridge` 只到条件定理 |
| 目标不是 `base` 时的 `cross` | 没写；要 `at` 目标上 `em` 与 `top` 的行，那是构造路的定义 |
| "无前提 `legal` + 搬运 ⟹ 矛盾" 合成一条 | 没写；要 `at` 目标上 `top` 的极限行，我只能猜它的形状 |
| 一般的含 Ω 结点的公共上界上的 `Link` | 只对 `tw 2` 写了 |
| 第 4 步的规范构造是否走到非 `Link` 的位置对；`Kᶜ`、`κ` 是不是链点 | 没有判定 |

#### 6 偏离与事故

- **对共用接口的增补都写在自己的文件里**，`YiRawIf` 等已有文件没有改：
  - Model：`Dispatch`, `Complete`, `SlotFree`, `Forced.TopLim`, `mixed`, `CohLg`, `plain-fix`。
  - Chain：`Branch`, `CohBranch`, `StepMono`/`RestrMono`/`FreeMono`/`LimRow`, `restrictP`, `Bridge.EmSucTop`。
  - Lift：`wrap`, `Rows.CrossRow`, `Rows.BranchRow`, `toRaw`/`fromRaw`。
  - Norm：`_≼_`, `_≺_`, `Compare`, `NormRoot`。
  - Omega：`KeepFold₂`, `DecAt₂`, `Link`, 本地的 `WLPO`。
- **中途改过一次陈述。** Lift §4 起初写的是 "目标在根上时 `em` 下的子树原样交出"。折叠在目标 `self` 上不是恒等 (零行、后继行照样作用)，所以换成更弱的 `BranchRow` (输出仍是第 j 支里的 `em`，支里不限定)。`moved` 仍用原样交出，文件里注明是便宜的取法。
- **任务外加做的：** `toRaw`/`fromRaw`，`plain-fix`，`CohRoot`，`NormRoot`，`lim≼psum`/`psum-inflates`，`compare-link`，`Bridge.top-legal`。
- **末尾只读地看过构造路五个文件的文首各 8 行**，没有导入，没有编辑，文件在变，下面未复核。文首写的是：
  - 无前提的实例 `Φᵐ` 在极限层号的 `top` 上取部分和 (对应 `Forced`：不带一致性就不能逐项)；
  - 逐项的 `Φ` 的合法性要 `CohP` (对应 `top-legal`)；
  - `Φ-below` (对应 `cross`)；
  - `T₃ᴿ` 条件于 `OutCoh`，没有证 (对应 `E-coh`)；
  - `T₃ᶜ` 把部分和放到根的坐标上 (对应 `NormRoot`)。
  - 判断：`psum-inflates` 提示取部分和的放法在相邻项相等的极限层号上值可能与逐项的放法不同。我的定理只关于 `psum`，不关于那些文件。
- 只删过自己五个模块的 `.agdai`，两次；没有 `--ignore-interfaces`，没有提交。无堆耗尽，无超时，无类型错误的运行。
- 翻译账：新定义都由树的要求给出，没有读记号；`_≼_` 是布劳威尔树通常的序；`cum`, `psum` 沿用上一轮。第 4 层逼出：无。

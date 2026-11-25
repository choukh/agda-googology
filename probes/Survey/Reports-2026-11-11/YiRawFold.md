# 写在第 K 层的树上，构造路 (YiRawFold)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-10 23:59 至 00:40 |
| 工具调用 / agda 编译 (粗数) | 56 / 19 |
| token (usage 字段，按消息去重) | 输出 244876；新写入缓存的输入 398384；读缓存的输入 11468918；其余输入 88 |
| 写过的仓库文件 | `YiRawFold.lagda.md`, `YiRawFoldBase.lagda.md`, `YiRawFoldInst.lagda.md`, `YiRawFoldNoLim.lagda.md`, `YiRawFoldTw3.lagda.md`, `YiRawFoldUp.lagda.md` |
| 文件前缀 | `YiRawFold` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: "写在第 K 层的树上" 的构造路与否定路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 接口记录有实例，派发处处完全；塔的第 3 项的闭项合法、无前提；极限层号上的 top 在保留模式下取部分和；没有值定理；六件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "乙线: 把折叠写在第 K 层的树上, 构造路". 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条; "量化域先取带证据的读回域"; "律带公共上界, 构造与否定配对"; Agda 一节 (选项, 无关参数, 研发阶段的文字预算, 退出码, 堆); "结论的写法" (三档; 交付拆成闭项与值; 前提要可满足; 证书, 闭项, 值分开说).
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4. `probes/Survey/Reports-2026-11-10/README.md` 只读 §2 里 "乙线第 3 步, 构造" 与 "乙线第 3 步, 否定" 两段 (上一轮两路做成了什么, 没做成什么); 要细节再读同目录的 `YiLvFold.md`, `YiLvNeg.md` (上一轮两路的回报原文).
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 下面这些都已定稿, 可以导入, 不许编辑):
   - 块: `RR5IrrCore` (`LF`, `Raw`, `Pre`, `Low`, `Kid`, `KidR`, `Gd`, `GdL`, `Lgl`, `LglLow`, `Nested`, `NestedLow`, `Cp`, `Dn`, `DnK`, `DnT`), `RR5IrrCheck` (`up`, `upN`, `upK`, `upT`, `Ω̂`, `cO`, `tw`), `YiIrrIf` (`CP`, `Legal`, `R`).
   - **本轮的共用接口 `YiRawIf`**: `Tgt`, `tlev`, `dispatch`, `dispatch-complete`, `dispatch-sound`, `test-keep-ω`, `test-cross`, `tw₃-is-top`, `branch-is-top`, `IsLim`, 记录 `RawFold`. 上一步的接口 `YiLvIf` (`Plain`, `lev`, `Low-lev`, `shift`, `Tri`, `compare`, `Kept`).
   - 上一轮构造路, 你要复用它的部件: `YiLvFoldAdd` (对层号一般的加法 `plus`, 值域接口 `Alg`), `YiLvFoldBase` (`Way`, `nodeAt`, `Chain`, `ChainLegal`, `Dom`), `YiLvFold` (模块 `Fold`: 以派发为参数的折叠, 十个互递归函数; 结点处的 `ψn` 把结点层号当变量, 所以 `keep s refl` 不用搬运), `YiLvFoldFin`, `YiLvFoldLim` (`bare-incomplete`, `branch-complete→lpo`), `YiLvFoldTw3` (`T₃`).
   - 上一轮否定路: `YiLvNegCanon` (`ccompare`, `ccompare-slot`, `ccompare-levels`, `ccompare-shift`: 规范比较, 槽位只由两个层号决定), `YiLvNegCompare` (`At`, `no-both`, `no-same`, `lev-legal`, `ext`, `lev-ext`, `prefix→tri`), `YiLvNegRestrict` (`restrict`, `Coh`, `restrict-add-weak`, `add-coh`, `ψ-legal-restrict`, `ψ-legal-coh`), `YiLvNegCum` (`cum`, `cum-legal`, `norm-guard`, `norm-directed`, `norm-level-legal`), `YiLvNegKeep`, `YiLvNegCert` (被排除的写法).
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么, 对纲领与目标意味着什么

乙线: 层号是树 (`LF`), 第 k 层的树是 `Raw k`; 终点是 ψ₀(Λ) 的闭项加值. 上一轮 (层号任意可数, 目标是塔的第 3 项 `tw 3`, 读法 ψ₀(Ω_Ω), 与已封存的 BTBO 持平) 的结果:

- 做成了一套对目标层参数化的折叠, 写在 `LF` 上, 派发 (折叠遇到一个 Ω 结点时, 决定保留它还是折掉) 是参数. 有限层号与 ω 上派发完全.
- **编译事实: 输出合法, 带嵌套证据, 保持第一位置, 对任意派发都成立. 所以闭项合法不携带强度信息; 强度在派发是否完全 (该保留的都保留), 要由完全性定理或值定理验收.**
- 障碍是每个结点的派发数据从哪里来: 只读两个裸层号而处处完全则 LPO (`bare-way→lpo`, `branch-complete→lpo`); 证书不作数据并且定义域对一切带守卫的分支遗传, 推出凭无关证据取数据 (`keep→irr-search`). `LF` 的结点不存它在目标层里的位置.

作者 2026-11-11 定: **主攻 "写在第 K 层的树上"**. `Raw K` 的结点 `G.lc r c t g` 自带位置 `r : Pre K`, 它是树里的数据; 公共上界就是字面的 K; 同一个 K 里两个位置的比较可判定 (`ccompare`, 读相关的 `Legal K`). 这条路没有人试过, 也没有被否定. 上一轮构造路没有走它, 理由是 "槽位若取自输入的位置或证书, 同一棵子树的两处出现会得到不同槽位, 位置保持的自反子句不再是 refl"; 这个理由对 `Raw K` 上的折叠是否成立没有检验 (在 `Raw K` 里位置是子树自己的一部分, `Cp K ξ ξ′` 比的是带位置的树).

`tw 3` 与它的各支都是 `top` 的读回 (`YiRawIf.tw₃-is-top`, `branch-is-top`), 所以它们的折叠可以陈述成 `Raw` 上的折叠在 `top` 处的值.

### 2 主审的纸面分析 (判断, 没有验证; 请先挑战它)

1. 折叠 `Φ K pl L τ ξ` 对 `ξ : Raw K` 递归, K 的合法性 `L` 是相关参数, 目标 `τ : Tgt K` 是第 0 层, K 自己, 或 K 里的一个位置. 结点 `G.lc r c t g` 处用 `YiRawIf.dispatch K pl L τ r : Way (tlev K τ) (lev K r)`. 目标是 K 自己时槽位就是 `r`, `Low K r` 原样, 不用任何转换.
2. 目标在位置 `q` 而保留时, 结点的下界与分支域在 `Low K r`, 要放到目标层 `lev K q` 的槽位 `s` 上. 上一轮的办法是把结点层号当变量 (`ψn m k (y : Way m k) (c : Raw k) …`), `keep s refl` 就不用搬运. 这里结点的类型是 `Low K r` 而不是变量 k 的 `Raw k`; 我预计要一对结构转换 `Low K r ↔ Raw (lev K r)` (对 (K, r) 递归, `Plain` 时三个子句, 每个子句是恒等), 守卫的转换只在无关位置用. 不要用 `subst` 搬树: 那样行与合法性都会卡在搬运上.
3. `G.em i T` (低一层的树的嵌入): 进到孩子的层号里递归. 目标要相对孩子重新表达: 目标在孩子里则是孩子里的位置; 目标在孩子之外 (之上) 则 T 里一切结点都在目标之下, 一律保留, 用上一轮加法里 "把造结点的办法当参数传下去" 的写法 (`Alg`). 极限层号处目标与树在不同分支时, 用 `YiLvIf.shift` 沿 `L` 里的路径搬位置.
4. `G.top`: 按 K 的形状展开成它读回的那个结点 (与 `upT` 一致): 后继处是根位置的结点, 下界 `cO`, 分支是 `em`; 极限处是各支 `top` 的极限.
5. 在固定的 K 与固定的 `L` 之内, 位置保持与合法性大概不需要证书的一致. 可能出问题的地方: 同一个层号经两条路到达 (先进孩子再比, 或在父层直接比) 时两边的槽位要相同, 这要 `ccompare-levels`, `ccompare-shift`, 它们只是命题相等.
6. `tw 3` 的根: 第 η 支的折叠是 `Φ (read0 η) … base top`, 它读 `Legal (read0 η)`, 即链点 η 的合法性要相关. 链是你自己定义的, 可以让链点带相关的 `Lgl zero η` (由输出的合法性引理生产, 这里源树是 `top`, 证书平凡). 极限层号处的合法性大概要 `L` 的一致 (`YiLvNegRestrict.Coh`), 于是链还要带一致性, 需要 "输出的合法性证书是一致的" 这一类引理 (上一轮否定路对旧的目标层 0 折叠做过 `ψ-legal-coh`). 另一个办法是只在链上归一 (`YiLvNegCum.norm-guard` 等): 链点取下界加归一后的累计, 合法性由树算出; 它改了链的行, 作者对累加有保留 (手册 §3.8). 先试前者; 用后者要在回报里明说链的行改成了什么.

### 3 目标, 分三站, 每站先交再往下

每站交 (a) 构造与闭项, (b) 强度的证据: 派发完全性落实到折叠上的定理 (接口的 `keep-law`, `fold-law`), 以及值的下界定理或写明没做. 部分进展也算.

**第 A 站, `Plain` 的公共上界 K.** 交:
- 折叠 `Φ`, 满足接口记录 `YiRawIf.RawFold` (或带你写明的额外前提的版本, 并说明前提为什么需要, 在规范实例上为什么可满足).
- 各行: 零, 后继, 极限, `em`, `top`, 保留行, 链行. 链行写明: 下一点是这一点加上**结点自己那一层的折叠**在这一点的分支上的输出, 观察取目标层的折叠.
- 闭项 `Φ K … base top` (读法 ψ₀(Ω_K)) 的合法性, 对一切合法 (必要时一致) 的 `Plain` K.
- 规范实例: K = ω+1; K = ω+2 (上一轮只读裸层号的派发在这里出错: 目标层 ω+1 上层号 ω 的结点应保留. 交一条定理, 指到链上一个具体的点, 那里新折叠保留而 `wayᵇ` 折掉); K = ω·2+1.
- 与上一轮的关系: 有限层号上新折叠与 `YiLvFoldFin.foldᶠ` 的关系 (相等, 第一位置, 或写明没比).

**第 B 站, 公共上界之间.** K 是 K′ 的字面第一位置时, `Φ K … base top` 是 `Φ K′ … base top` 的第一位置 (`L` 取 `L′` 沿路径的限制); 极限层号 `lim f` 处 `Φ (lim f) … base top` 是各 `Φ (f n) … base top` 的极限并且合法.

**第 C 站, `tw 3`.** 闭项 `T₃ᴿ : R` 与 `Lgl zero T₃ᴿ`, 没有前提; 根上的行 (加法链, 起点是下界 1, 链点处的值是第 η 支的折叠 `Φ (read0 η) … base top`); 写明链点带什么数据. 与上一轮的 `YiLvFoldTw3.T₃` 的关系能说多少说多少.

**停下的条件.** 遇到下面任一种就停在那一站, 交已有的文件与约化, 不硬攻:
- 同一处连续三次重新设计仍过不了检查器;
- 需要 Funext 或 K;
- 只有用 `subst` 搬树才能写出折叠, 而行或合法性因此证不出;
- 你判断必须改块.
约化的意思: 把缺的东西写成带确切 Agda 类型的陈述 (模块参数或记录字段), 其余在这个前提下条件地证出来并编译; 说明前提在规范实例上是否可满足. 判定一条路走不通必须有编译过的否定定理, 否则只写 "未走通".

### 4 规则

- **只新建文件**, 前缀 `YiRawFold` (如 `YiRawFoldBase`, `YiRawFold`, `YiRawFoldInst`, `YiRawFoldTw3`), 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiRawIf`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiRawNeg` (否定路) 与 `YiLvVal` (给上一轮有限层号的闭项补值定理), 不要动它们的文件, 也不要依赖它们. 对共用接口的增补写在你自己的文件里, 并在回报里说.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提出现在标明 "验收" 或 "条件" 的文件里, 不进折叠的定义与闭项.
- 新的树侧定义不从导入闭包含记号的模块导入. 值的验收文件单独成文件, 文首标 "验收".
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件; 编译表, 成本表不进文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写精确名字, 不用通配: 否定路的前缀与你的前缀开头相同).
- 你的临时目录: `<实验目录>/agents/rawfold`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 对非验收文件通过; 检索禁用构造为 0.

### 5 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几站 (HOLDS / PARTIAL / BLOCKED), 一段话说对纲领与目标意味着什么.
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表: 名字, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型, 并说前提是否可满足.
4. 强度的证据单列: 派发完全性落实到折叠上的定理; 新折叠与只读裸层号的折叠第一次出现差别的具体位置; 值定理或 "没做".
5. 设计上的关键选择: 转换怎么写的; `em`, `top` 怎么处理; 哪些行是 `refl`; 证书哪些相关哪些无关; 与 §2 的分析哪里一致, 哪里不同.
6. 第一个障碍: 精确到字段或子句, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
7. 偏离与事故: 没按简报做的地方及原因.
闭项, 证书, 值分开说; 强度写 ψ₀(Ω_x), 标明是读法还是定理; 不用 "只差", "自然" 一类形容.

## 回报原文

### 乙线 "写在第 K 层的树上" 构造路回报 (前缀 YiRawFold)

#### 1 判决

- **第 A 站 HOLDS.** 接口记录有实例 `rawFold : YiRawIf.RawFold`, 没有前提.
- **第 B 站 HOLDS (目标第 0 层), 对接口实例只到一半.** `Φ` 对一切字面第一位置路径成立, 极限层号上的合法性要前提 `CohP`; 接口实例 `Φᵐ` 只证了 "极限处取第 0 支" 的路径.
- **第 C 站 HOLDS, 带一处要明说的行.** 闭项 `T₃ᵐ : R` 与 `Lgl zero T₃ᵐ` 没有前提, 根上的行不改; 但各支的折叠用的是 `Φᵐ`, 它在极限层号的 `top` 上取部分和.
- **三站都没有值定理.** 读法 ψ₀(Ω_{ω+1}), ψ₀(Ω_{ω+2}), ψ₀(Ω_{ω·2+1}), ψ₀(Ω_Ω) 都是读法, 不是定理.

对纲领与目标: 折叠写在 `Raw K` 上可行, 块没有改, 没有 Funext, K, 公设, 没有读记号. 派发读树里的位置和相关的 `Legal K`; 折叠问到的每一处派发都完全 (编译定理), 上一轮 "派发在极限层号上未到位" 这一条在完全性的意义上补上了. 代价是一条树侧逼出的行: 目标保留结点时, 极限层号上的 `top` 取各支折叠的部分和 (累加). 这条有一个编译过的否定实例作依据, 见 §6.

翻译账: 本轮新增的脚手架是 `Ext`, `CohP`, 部分和行, 链点带相关的 `Lgl`. 四样都由块的第一位置与合法性逼出, 没有哪个字段的形状读自记号. 零, 后继, 链这些行沿用上一轮.

#### 2 文件表

都在 `<仓库>/probes/OCF/Align/`. 删自己的接口后按依赖序冷编译, 每个约 2 秒, 常驻内存 0.5G 以下.

| 文件 | 代码行 | 冷编译 |
|---|---|---|
| `YiRawFoldBase.lagda.md` | 194 | 0 |
| `YiRawFold.lagda.md` | 382 | 0 |
| `YiRawFoldInst.lagda.md` | 126 | 0 |
| `YiRawFoldUp.lagda.md` | 81 | 0 |
| `YiRawFoldNoLim.lagda.md` | 89 | 0 |
| `YiRawFoldTw3.lagda.md` | 233 | 0 |

`importclosure.py` 六个模块都是 "禁用表命中 0, OK". 检索 `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `--cubical`, `irrelevant-projections`, `Funext` 均为 0. 没有改任何已有文件.

#### 3 定理表

除标明的以外都是编译定理.

**折叠 (`YiRawFold`)**

| 名字 | 白话 |
|---|---|
| `Ψ` | 折叠, 对 (公共上界 k, `Raw k` 的树) 按字典序递归, 证书无关; 外部派发 `Ext m k` 是参数 |
| `Ψ-legal`, `Ψ-nested`, `Ψ-cp` | 输出合法, 带嵌套证据, 保持第一位置; 对任意 `mix w` 成立, `low` 下合法性要 `CohP` |
| `rawFold : RawFold` | 接口实例 `Φᵐ`, 四条律, 无前提 |
| `Φ`, `Φ-keep`, `Φ-fold`, `Φ-position`, `Φ-nested` | 目标第 0 层改用 `low` 的那一版, 这几条无前提 |
| `Φ-legal` | 条件定理, 前提 `GoodT K pl L τ`: 目标 `base` 时是 `CohP K pl L`, `self` 与 `at q` 时是 `⊤` |
| `keepᴳ`, `foldᴳ` | 一般外部派发上: 派发说保留则输出是结点 (`Kept`), 否则是 ℕ 极限 |
| `complete-S`, `-L`, `-own`, `-ownT`, `-mix`, `-ext` | 折叠问到的五种来源的派发都完全 |
| 各行 | `zero-row`, `suc-row`, `lim-row`, `node-row`, `em-rowˢ`, `em-rowˡ`, `top-row⁰`, `top-rowˢ`, `top-rowˡ`, `top-rowᶜ`, `keep-row`, `fold-row`, `next-additive`, `ΨN-rowʳ/ˢ/ˡ`, 全是 `refl` |
| `top-as-node` | 后继层号上 `top` 与字面写出的根位置结点折叠相同, `refl` |
| `self-keep₀`, `self-keep₁` | 目标是 K 自己时, 根位置与根下一格的结点原样保留, 槽位就是位置, `refl` |
| `certificate-free` | 换证书输出不变, `refl` |

**实例 (`YiRawFoldInst`)**

| 名字 | 白话 |
|---|---|
| `closed-legal` | 条件定理, 前提 `CohP K pl L`: `Φ K … base top` 合法 |
| `closedᵐ-legal` | `Φᵐ K … base top` 合法, 对一切 `Plain` 且 `Legal` 的 K, 无前提 |
| `ω-coh`, `ω+-coh`, `ω2-coh` | 三个规范实例的 `CohP`, 方程两边定义性相等 |
| `Ωω+1-legal`, `Ωω+2-legal`, `Ωω2+1-legal` | 三个闭项合法 |
| `closed-row`, `closed-body`, `closed-obs`, `closed-feedback` | 后继层号上闭项的链行, `refl` |
| `new-keeps`, `new-kept`, `old-way`, `old-folds` | ω+2 上新旧折叠不同的那一点, 见 §4 |
| `test-slot-ω`, `ω+1-body₀` | ω+1 上派发的槽位与上一轮相同 (有限测试); 推进用的输出是部分和 |
| `fin-zero`, `fin-one-term₀` | 与 `foldᶠ`: n = 0 字面相等; n = 1 只核对第 0 项 (有限测试) |

**公共上界之间 (`YiRawFoldUp`, `YiRawFoldNoLim`)**

| 名字 | 白话 |
|---|---|
| `Φ-below` | K 是 K′ 的字面第一位置, 则 `Φ K … base top` 是 `Φ K′ … base top` 的第一位置; K 的 (`Plain`, `Legal`) 取 K′ 的沿路径的限制 |
| `Φ-below-coh` | K 自带的那一对等于限制时换成它 |
| `Φ-lim-row`, `Φ-lim-at` | 极限层号上是各支闭项的极限 (`refl`); 每支是它的第一位置 |
| `Φ-lim-legal`, `Φ-lim-step` | 条件定理, 前提 `CohP (lim f) pl L` |
| `Φᵐ-below` | 接口实例的同一结论, 只对 `Zp p` (极限处只取第 0 支) 的路径 |
| `Φᵐ-lim-row`, `Φᵐ-lim-legal` | 极限层号上是各支的部分和 (`refl`), 合法无前提 |
| `side-lim-illegal` | 否定: 公共上界与目标都取 ω, `self` 派发下, `top` 在各支上的折叠排成的极限不合法 |

**`tw 3` (`YiRawFoldTw3`)**

| 名字 | 白话 |
|---|---|
| `T₃ᵐ`, `T₃ᵐ-legal` | 闭项与合法性, 无前提 |
| `T₃ᵐ-start`, `T₃ᵐ-term`, `T₃ᵐ-feedback` | 根上的行, `refl`: 起点下界 1, 第 n 项是第 ηₙ 支的 `Φᵐ (read0 ηₙ) … base top`, 下一点是 ηₙ 加上它 |
| `guardsᵐ`, `T₃ᵐ-branch` | 链点是 `tw 3` 的带守卫坐标; 第 n 项折的是 `tw 3` 在那一支的原像 `top` |
| `read0-cohP`, `plainR-read0`, `pair-read0` | 一致的坐标证书读成 `CohP`; 读回与限制可交换 |
| `cum-coh`, `cum-restrict`, `restrict-weak` | 累加归一的证书一致, 沿链的一步是限制 |
| `T₃ᶜ`, `T₃ᶜ-legal` | 另一种放法, 无前提: 各支用 `Φ`, 链点只带累计 v, 访问第 `1 + cum v` 支. **这改了根上的行** |
| `Plain3.T₃ᴿ`, `Plain3.T₃ᴿ-legal` | 条件定理: 各支用 `Φ`, 根不改. 前提见下 |

`Plain3` 的前提:
```agda
OutCoh = ∀ η (l : Lgl zero η) (ch : Coh η l) → Coh (fold₃ η l) (fold₃-legal η l ch)
```
没有证, 也没有否定, 连一个实例都没验. 所以 `Plain3` 目前不能当结果用.

`CohP` 在三个规范实例上由 `refl` 满足, 在 `read0 η` 上由一致的证书满足 (`read0-cohP`).

#### 4 强度的证据

- **派发完全性落实到折叠上.** `rawFold` 的 `keep-law` 与 `fold-law` 管入口的结点. 嵌套在孩子里和链里的结点由 `keepᴳ`, `foldᴳ` 加六条 `complete-*` 管: 互递归块里出现的外部派发只有五种来源, 五种都完全. 输出合法对任意派发成立, 仍然不携带强度.
- **与只读裸层号的折叠不同的两处.**
  - ω+2, 派发不同. `Ωω+2` 的链在 `Raw (ω+1)` 里, 第 0 点是 `top`. 推进用的输出在新折叠里是根槽位的结点 (`new-keeps`, `refl`; `new-kept`). 上一轮同一处 `wayᵇ (ω+1) ω = fold` (`old-way`), 输出是 ℕ 极限 (`old-folds`).
  - ω+1, 派发相同, 行不同. 第 0 点 `top_ω` 处推进用的输出, 新折叠是各支的部分和 (`ω+1-body₀`), 上一轮是各项的极限. 这一处新折叠带累加, 上一轮不带.
- **值定理: 没做.**
- **与 `foldᶠ`:** n = 0 字面相等. n ≥ 1 没比: 两边的分支函数是两个不同的递归定义, 极限之下的逐字相等要函数外延.
- **与上一轮 `T₃`:** 没比. `fin-below-T₃` 的对应没有做成, 那条路径在极限处取第 n 支, 部分和行不保持它.

#### 5 设计上的关键选择

- **没有转换, 没有 `subst` 搬树.** 记录 `Nd m k A Gd′ Lg′ Ns′` 收结点折叠要用的数据. `ΨN` 对 (K, r) 递归三个子句; 在根位置, `Low` 形式与 `Raw` 形式的两个记录类型定义性相等, 记录原样交给 `Ψn`. `Ψn` 里层号是变量, `keep s refl` 直接匹配, 复用上一轮的 `nodeAt`, `Chain`, `ChainLegal`.
- **目标不相对孩子重新表达.** 折叠带一个外部派发 `Ext m k`: `low` (一律折叠) 或 `mix w` (`w` 是位置上的函数). 进孩子时用复合限制 (`inS`, `inL`), 层号定义性不变. 所以没用到 `shift`, `ccompare-levels`, `ccompare-shift`.
- **结点自己那一层的派发.** `own k pl L r = mix (dispatch k pl L (at r))`, 读当前这一层的 `Legal`; 进孩子后换成孩子的那一份. 这使小公共上界上的折叠字面地出现在大的里面, `Φ-below` 因此对路径归纳几行就完.
- **`top`.** 层号 0 上是 1 的像. 后继层号上是根位置的结点, 下界 `cO k`, 分支是孩子里的树. 极限层号上, `low` 之下取各支的极限, `mix` 之下取各支的部分和.
- **证书.** `Ψ` 的 `Lgl`, `Nested` 无关. `Plain K` 与 `Legal K` 相关. `tw 3` 根上的链点带相关的 `Lgl zero η`.
- **与简报 §2 的分析对照.**
  - 2.1, 2.4 (后继处), 2.5 一致: 固定的 K 之内不需要证书一致, 位置保持的自反子句是 `refl`.
  - 2.2, 2.3 不同: 不需要转换对, 也不需要重新表达目标.
  - 2.4 极限处不同: 保留模式下各支的极限不可用.
  - 2.6: 链点带相关 `Lgl` 一致. "输出证书一致" 只在各支用 `Φ` 的版本里需要, 用 `Φᵐ` 时不需要. 链上归一的办法也交了 (`T₃ᶜ`).
- **上一轮不走这条路的理由** (同一子树两处出现得到不同槽位) 在固定的 K 内不成立. 但它以另一种形式出现: 极限层号里同一个层号在不同分支是不同的位置.

#### 6 第一个障碍

**(a) 保留模式下极限层号上 `top` 的行.** 子句是 `Ψ m (lim f) pl L (mix w) G.top`. 要取各支的极限, 缺的是
```agda
∀ n → Cp m (Ψ m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt)
           (Ψ m (f (suc n)) (pl (suc n)) (proj₂ L (suc n)) (mix (λ r → w (suc n , r))) G.top tt tt)
```
- 对接口的 `self` 派发, 它在 ω 上为假 (`side-lim-illegal`). 第 1 支输出的槽位是 (1, 根), 第 2 支输出的第一支的槽位是 (2, 根下一格); 两个位置层号相同, 是不同的位置.
- 对规范槽位的派发 (`at q`, `ownT`) 没有证, 也没有否定.
- 判断: 那里要 "派发沿路径限制后作为函数相等", 即函数外延加上层号相等证明的唯一性; 或者改块. 两样我都没有碰.
- 所以取了部分和, 与上一轮 `YiLvFoldAdd.add` 在 `x + top` 处同一个写法. 没有检查器报错, 这是定义时的选择.

**(b) `OutCoh`** (类型见 §3). 只影响 "各支用 `Φ` 而根不改" 的版本. 判断: 证它要对新折叠在一切目标层上重做 "每条合法性引理配一条与限制交换", 包括经 `Alg` 的一般层加法, 规模估计上千行. 而且证出来也去不掉 (a) 的部分和, 链的推进仍在保留模式下. 所以没有攻.

**(c) `Φᵐ-below` 对取第 n ≥ 1 支的路径:** 没有证, 也没有否定.

#### 7 偏离与事故

- **接口的增补都在我自己的文件里:** `Ext`, `Nd`, `CohP`, `plainR`, `Good`, `GoodT`, `Φ`, `Zp`. `YiRawIf` 没动.
- **`CohP` 里含 `Plain` 的一致.** 比较把 `Plain` 当数据传, 含极限的层号上两份 `Plain` 的相等不用函数外延证不出.
- **`top` 展开后, 结点自己那一层的派发没有用接口的 `self`.** 用的是根位置的 `own` 限制到孩子 (`ownT`, 规范槽位), 这样 `top-as-node` 才是 `refl`. 接口的 `self` 只在入口用.
- **第 C 站的闭项不是某个定义在 `LF` 上的折叠在 `tw 3` 处的值.** 根的链是直接写出来的. 整个 `tw 3` 的公共上界 `tw 2` 不是 `Plain` 的, 不在本轮片段里.
- **我是构造路, 但多交了一个否定文件 `YiRawFoldNoLim`**, 作部分和行的依据. 它在我的前缀下, 没有依赖否定路的文件.
- **没做的:** 任意位置上链行的统一陈述 (只给了根位置的行加 `ΨN` 的三条归约); 任意位置上 `self` 保留行的一般陈述 (只有两条 `refl` 加存在形式的 `Kept`).
- **事故一件.** 第一次删接口的命令用了 shell 变量拼路径, 被安全检查拦下, 没有执行. 改成逐个写出字面的绝对路径后删除; 只删了我自己六个模块的 `.agdai`.
- 没有提交, 没有推送. 另两路的文件 (`YiRawNeg*`, `YiLvVal*`) 没有碰, 也没有依赖.

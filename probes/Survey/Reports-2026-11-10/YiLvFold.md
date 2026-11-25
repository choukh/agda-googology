# 乙线第 3 步，构造路 (YiLvFold)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-10 15:40 至 16:36 |
| 工具调用 / agda 编译 (粗数) | 51 / 14 |
| token (usage 字段，按消息去重) | 输出 326027；新写入缓存的输入 620961；读缓存的输入 7084454；其余输入 64 |
| 写过的仓库文件 | `YiLvFold.lagda.md`, `YiLvFoldAdd.lagda.md`, `YiLvFoldBase.lagda.md`, `YiLvFoldFin.lagda.md`, `YiLvFoldLim.lagda.md`, `YiLvFoldTw3.lagda.md` |
| 文件前缀 | `YiLvFold` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 乙线第 3 步构造路返回并复核; 两路结清 (主审)” 一节 |
| 主审复核后的一句结论 | 对目标层参数化的折叠做成，有限层号与 ω 上派发完全；塔的第 3 项只有合法闭项，派发不完全，读法未定；合法性对任意派发成立；六件冷编退出码全 0；没有值 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "乙线第 3 步, 构造路". 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条; "量化域先取带证据的读回域"; "律带公共上界, 构造与否定配对"; Agda 一节 (选项, 无关参数可以用, 研发阶段的文字预算, 退出码, 堆); "结论的写法" (三档; 否定要编译定理; 交付拆成闭项与值; 前提要可满足; 证书, 闭项, 值分开说).
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 (编译与内存) 与 §5.4 (复核清单). `probes/Survey/RR5-SoftStops.md` 只读 §2 (无关证据的块为什么这样设计). 别的审查报告不必读.
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`):
   - 块与接口, 定稿, 只增不改, 不许编辑: `RR5IrrCore` (块: `LF`, `Raw`, `Pre`, `Low`, `Kid`, `Gd`, `Lgl`, `Nested`, 证据是无关参数), `RR5IrrCheck` (`up`, `upN`, `upK`, `upT`, `Ω̂`, `cO`, `tw`, `Λ`), `YiIrrIf` (`CP`, `Legal`, 第 0 层算术, `FoldRows`), `YiLvIf` (**本步的共用接口**: `Plain`, `OnlyP`, `lev`, `Low-lev`, `shift`, `Tri`, `Compare`, `CompareIrr`, `compare`, `Kept`, `tw3-onlyP`).
   - 上一步 (第一次回灌, 层号字面为 0 或 1) 的写法, 你要推广的就是它: `YiIrrFbIf` (接口 `FbRows`, 第 1 层算术 `_+¹_`, `Pt`), `YiIrrFbBase` (定义域, `Chain₁`, `ChainLegal₁`), `YiIrrFb` (九个互递归函数, 行都是 `refl`), `YiIrrFbInst` (闭项 Ω₂), `YiIrrFbValue` (值下界的办法).
   - 可用的已有定理: `YiIrrFoldBase` (`Chain`, `ChainLegal`), `YiIrrFoldSeed` (`Seedᶠ`, `seed-Ω̂`, `seed-up`, `seed-tw`), `YiIrrNegLegal` (`Legal-Ω̂`, `lgl→Legal`, `Ω̂-CP`, `cp→CP`, `Legal-tw`), `YiIrrNegDispatch` (`locate→irr-search`), `YiIrrNegWide` (`IrrSearch`).
   - 参照 (只读, 不导入): `src/OCF/BTBO.lagda.md` 第 640 到 710 行 (`Ordᴰ`, 有界三歧 `<-dec`) 与第 838 到 1038 行 (`Ord<`, `coe`, `↑`, `Ω`, `ψ<` 的三路派发, `ordᴰ` 与 `cumsum`). BTBO 在自己的族里做到了本步要做的事.
   查签名用检索 (grep), 大文件不要整篇读.

### 1 这一步是什么, 对纲领与目标意味着什么

乙线: 层号本身是树 (`LF`), 第 k 层的树是 `Raw k`, Ω 结点 `lc k c w b t g` 以 `Raw k` 里不低于下界 `c` 的坐标为分支. 塔 `tw 0 = 0`, `tw (n+1) = Ω̂ (tw n)`, `Λ = lim tw`; 终点是 ψ₀(Λ) 的合法闭项加值 (EBO). 已做成: 目标层 0 的完整折叠 (`YiIrrFold.fold-rows`); 第一次回灌, 即层号字面为 0 或 1 的片段上互递归的 `ψ₀`, `ψ₁`, 闭项 ψ₀(Ω̂ 2) 合法, 值下界 ψ₀(Ω₂) (`YiIrrFb.fb-rows`, `YiIrrFbValue.Ω₂-lower`). 那一步的派发是按层号的字面形状逐个写的, 没有比较层号.

本步: **层号任意可数**. 目标是塔的第 3 项 `tw 3` 的折叠闭项. `tw 3 = lc zero raw1 _ _ (tw 2) (λ η e → Ω̂ (up zero η _))` (`RR5IrrCheck.tw₃-form`), 第 η 支是 Ω̂ (read0 η), 读法 Ω_η; 所以结点的层号是任意的可数树 (`YiLvIf.Plain`, 只由零, 后继, ℕ 极限组成), `tw 3` 在片段 `OnlyP` 里 (`tw3-onlyP`). ψ₀(tw 3) 的读法是 ψ₀(Ω_Ω), 与已封存的 BTBO 持平; 它也是乙线第一次真正需要比较层号的地方. 做成的方式 (是不是一套对层号参数化的定义) 比做到哪一个序数更重要: 后面的层号不可数, 逐层手写帮不上.

### 2 主审的纸面分析 (判断, 没有验证; 请先挑战它, 不要当成前提)

1. 目标层 m 的折叠遇到层号 k 的结点, 要分路 (对照 BTBO 的 `ψ<`): k 严格在 m 之下则保留, 输出是 `Raw m` 的结点 `G.lc s …`, 要 k 在 m 里的槽位 `s : Pre m` 这份数据, 还要把结点的下界与分支域 `Raw k` 搬到 `Low m s` (`YiLvIf.Low-lev` 给类型相等; 字面层号时是 `refl`, 一般要搬运); 否则折叠, 链在 `Raw k` 里, 由目标层 k 的折叠推进, 观察取目标层 m. "相等" 一路看来可以并入 "之上" 的写法 (链的输出只差一项), 那样不需要搬运.
2. `LF` 的结点只存层号 k, 不存 k 与目标层的关系. 位置只在 `Raw K` 的结点 `G.lc r c t g` (`r : Pre K`) 里是数据, 读回 `up` 把它丢掉 (`upN`). 所以一般目标层的折叠大概要写在 `Raw K` 上 (输入是带位置的树, K 是两个层号字面的公共上界, 像 BTBO 的 `Ord ℓ`), 而不是写在裸的 `LF` 上; `LF` 上只有目标层 0 的派发不用比较 (看层号的头). `YiIrrNegDispatch.locate→irr-search` 是这一点在 `LF` 一侧已有的编译事实.
3. 有限层号 (字面的 sucⁿ zero) 没有极限: 两个裸层号可以按形状递归直接比较, 槽位可以算出, 不触壁垒, 也不需要证书. 这一段, `LF` 上证书无关的写法应当能原样推广.
4. 层号含 ℕ 极限 `lim f` 时, 两个位置落在不同分支 (n ≠ m) 就要把一个沿 `CP (f n) (f m)` 搬到另一支里再比 (`YiLvIf.compare`, 已编译). 这读了 `Legal K` 里的路径数据. 而这个块里合法性在树外, 折叠的证书是无关的; `tw 3` 根上的链点 η 只带无关的 `Lgl zero η`, 第 η 支的层号 `read0 η` 的比较却要它的数据. **我预计这是第一个真正的障碍.** 我看到的出路, 都没有验证:
   (a) 层号的合法性作相关参数, 沿根的链传 (链点带相关的 `Lgl`, 由折叠的合法性引理生产). 这时折叠的输出依赖证书里的路径 (槽位随路径变), 极限行的合法性要证书的一致: `Legal (lim f)` 的各分量 `lf n` 彼此独立, 要 `lf n` 等于 `lf (n+1)` 沿 `st n` 的限制; 位置保持要改写成限制形式 (小树的证书是大树证书沿路径的限制), 一致性要对规范证书 (加法, 链, 折叠的合法性引理) 逐个证. 我手推加法一例不需要 Funext (限制只取分量), 其余没推.
   (b) BTBO 的办法: 把折叠输出变成层号前先累加归一 (`ordᴰ`, `cumsum`), 路径由树算出, 不要证书. 但它改了被折叠的树 (分支成了 Ω̂ (read0 (归一 η))), 累加后的分支对第一位置不单调 (`Legal` 的 dir 项过不去), 作者对累加也有保留 (手册 §3.8). 用它得到的不是 `tw 3` 的折叠, 要如实说.
   (c) 路径数据进树 (ℕ 极限自带相邻第一位置的路径, 像 BTBO 的 `lim f mono`). 这是改块, **不在本任务范围**, 要作者定; 你若认为非此不可, 交编译证据说明为什么, 不要自己做新块.

### 3 目标, 分三站, 每站先交再往下

每站交 (a) 合法的闭项或构造, (b) 关于它的值的定理 (下界即可, 办法见 `YiIrrFbValue`) 或写明没做. 没有 (b) 不因读法低而不交 (a). 部分进展也算: 一站做完, 文件编译通过, 就已经是可以汇报的结果.

**第 1 站, 有限层号, 对层号参数化.** 片段: Ω 结点的层号是字面的 sucⁿ zero. 用一套定义 (对层号递归或参数化, 不是把 `ψ₀`, `ψ₁`, `ψ₂` … 逐个写出) 给出一切有限目标层的折叠, 证书无关. 交:
- 各目标层的行: 零, 后继, 极限, 保留行 (层号在目标层之下的结点), 链行与回灌行 (其余结点; 链在结点自己的层里, 由那一层的折叠推进). 行尽量是 `refl`.
- 合法性, 嵌套证据, 位置保持 (照 `YiIrrFb` 的九个函数的分工).
- 闭项: 对一切 n : ℕ, ψ₀(Ω̂ (sucⁿ zero)) 合法 (一条对 n 的定理, 不是逐个实例); ψ₀(Ω̂ ω) 合法, 其中 ω = lim (λ n → sucⁿ zero), `Ω̂ ω = lim (λ n → Ω̂ (sucⁿ zero))`, 里面没有层号 ω 的结点. 读法 ψ₀(Ω_ω).
- 限制到层号 0 或 1 时, 与 `YiIrrFb` 的行一致 (能证多少证多少; 字面相等若要 Funext 就只交行的一致).
你会需要对层号一般的加法与 `top` 的展开 (推广 `YiIrrFbIf._+¹_`: `x + em a` 对 `a` 递归, `x + top` 写成展开后的结点), 以及 `zero-not-below-top` 那类头的处理. 这些自己设计, 写进你的文件.

**第 2 站, 层号含 ℕ 极限的结点.** 最小实例是 Ω̂ (suc ω), 即层号 ω 的结点, 读法 ψ₀(Ω_{ω+1}). 先做最便宜的决定性实验: `Raw ω` 里两个不同分支上的位置的三路 (`compare` 的实例), 以及保留行里沿 `Low-lev` 的搬运能不能让各行与合法性证明通过. 交: 对带合法性的 `Plain` 层号 K (合法性相关还是无关, 由你定并说明理由), Ω̂ (suc K) 的目标层 0 折叠; 至少 K = ω 的闭项与它的合法性. 比较层号一律走 `YiLvIf.Compare` 的形状 (同一个字面的 K 里的两个位置), 不比较裸的含极限的层号.

**第 3 站, `tw 3` 的根.** 层号是链点的读回. 交: 闭项 `T₃ : R` 与 `Lgl zero T₃`, 没有前提; 根上的行 (T₃ 是加法链 ηₙ₊₁ = ηₙ + (第 ηₙ 支的折叠) 的观察的极限, 起点是下界 1); 第 η 支的折叠与第 2 站的定义是同一个. 值的下界若做, 先对每个有限 n 证不低于 ψ₀(Ω_n) 的参照.

**停下的条件.** 遇到下面任一种就停在那一站, 交已有的文件与一份约化, 不硬攻:
- 同一处连续三次重新设计仍过不了检查器 (正性, 停机, 无关参数的限制);
- 需要 Funext 或 K 才能证的行或合法性;
- 你判断必须改块 (上面的 (c)) 或必须改被折叠的树 (上面的 (b)).
约化的意思: 把缺的东西写成带确切 Agda 类型的陈述 (模块参数或记录字段), 其余在这个前提下条件地证出来并编译; 说明这个前提在规范实例上为什么可满足或为什么不知道. 判定一条路走不通必须有编译过的否定定理, 否则只写 "未走通".

### 4 规则

- **只新建文件**, 前缀 `YiLvFold` (如 `YiLvFoldFin`, `YiLvFoldLim`, `YiLvFoldTw3`), 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiLvIf`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 另一路 (否定路) 在用前缀 `YiLvNeg`, 不要动它的文件. 需要对共用接口增补就写在你自己的文件里, 并在回报里说.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提出现在标明 "验收" 或 "条件" 的文件里, 不进折叠的定义与闭项.
- 新的树侧定义不从导入闭包含记号的模块导入. 值的验收文件 (读 `OCF.Free.Level` 的参照树) 单独成文件, 文首标 "验收".
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件; 编译表, 成本表不进文件. 一次性的试验放你的临时目录, 用纯 `.agda` (选项见 AGENTS: 仓库外的文件要自己写上仓库的全部选项).
- 仓库文件里不写本机路径 (含临时目录路径).
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写精确名字, 不用通配).
- 你的临时目录: `<实验目录>/agents/lvfold`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 对非验收文件通过; 检索禁用构造为 0.

### 5 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几站 (HOLDS / PARTIAL / BLOCKED), 一段话说对纲领与目标意味着什么.
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表: 名字, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型, 并说前提是否可满足.
4. 设计上的关键选择: 折叠写在 `LF` 上还是 `Raw K` 上; 证书哪些相关哪些无关, 为什么; 哪些行是 `refl`; 与 §2 的分析哪里一致, 哪里不同.
5. 第一个障碍: 精确到字段或子句, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 值: 定理或 "没做".
7. 偏离与事故: 没按简报做的地方及原因.
闭项, 证书, 值分开说; 强度写 ψ₀(Ω_x), 标明是读法还是定理; 不用 "只差", "自然" 一类形容.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-10 16:33 (UTC)：

否定路 (YiLvNeg*) 已返回, 主审已冷编复核六件 (退出码全 0). 下面是信息, 不改你的任务与停下的条件; 不必回复, 不要为它阻塞. 这六个文件已定稿, 可以导入, 不要编辑.

与你的设计直接相关的编译定理:
1. `YiLvNegKeep.bare-way→lpo : (way : BareWay) → Correct way → LPO`. 派发 `way m k` 只读两个裸层号, 并且在 `tw 3` 的带相关守卫的坐标读回里 "k 在 m 的位置上就保留" 处处成立, 则 LPO. 所以含极限的层号上, 只读裸层号的正确派发没有构造性的实例; 有限层号 (第 1 站) 不受影响. 否定路末尾只读地看过你当时的 `ψ : (m x : LF) → .(Dom x) → Raw m` 与 `way m k`, 它指的就是这个参数; 我没有复核这一条观察, 你自己对照.
2. `YiLvNegKeep.keep→irr-search : KeepRows → IrrSearch`. 证书无关, 定义域对一切带守卫的分支遗传并含 `tw 3`, 保留律交出槽位, 推出 IrrSearch. 读作这个定义域太宽或证书必须相关; 不否定定义域只沿链点遗传的折叠. `lv-irr→irr-search`: 把相关的 `Legal k` 放进证书但经无关守卫遗传, 同样.
3. `YiLvNegCompare.compare-irr→irr-search`, `compare-read→irr-decide`: 合法性只无关地给比较, 不行. `prefix→tri`: 两个位置相同或互为延伸时三路直接写出, 不要合法性.
4. `YiLvNegCert.compare-reads-certificate`: `YiLvIf.compare` 的槽位随证书变 (同一层号两份证书给槽位 0 与 1). `Forced.coherence`, `no-by-compare`: 位置保持若写成两份独立证书的形式, 就要求换证书输出相等, 槽位取自 `compare` 时不可满足.
5. 正面, `YiLvNegCanon.ccompare : Compare`, `ccompare-slot`, `ccompare-levels`, `ccompare-shift`: 规范比较. 极限处取最小的可行分支 (有界搜索, 读合法性的数据来判定), 交出的三路形状与槽位只由两个层号决定, 换证书, 换公共上界, 沿路径搬位置都不变 (命题相等). 方程分量 `lev i s ≡ j` 的证明是否与证书无关没有证.
6. 正面, `YiLvNegRestrict`: 目标层 0 上限制形式成立, 不用函数外延. `restrict`, `restrictDom`, `Coh`, `CohDom`; `restrict-add-weak`, `add-coh`, `successor-coh`; `ψ-legal-restrict` (无前提: 限制形式的位置保持与 `YiIrrFold.ψ-legal` 的输出证书相容); `ψ-legal-coh` (一致的定义域证书上输出证书一致); `read0-legal-coh`. 反面 `fold-legal-reads-certificate`: `ψ-legal` 对两份定义域证书给出不相等的输出证书 (ψ 的输出相同).
7. `YiLvNegCum`: 把 `tw 3` 的分支换成 `Ω̂ (read0 (cum η))` 的树不过 `Legal` 的 dir (`cum-tower-not-legal`). 正面: 树不改, 链点取 `c + cum v` (v 是累计), 则守卫, 相邻两支的第一位置路径, 层号的合法性都由树与下界的合法性算出, 是相关的, 不调用折叠的输出合法 (`norm-guard`, `norm-directed`, `norm-level-legal`, `tw3-chain-step`). 这条改了链的行 (下一点不再是这一点加输出), 折叠与值都没有写; 若你走它, 在回报里明说链的行改成了什么.

用哪条由你定. 若走相关证书: 位置保持写成限制形式, 槽位用 `ccompare` 的规范位置. 交回时照原简报的格式.

## 回报原文

### 乙线第 3 步构造路回报 (前缀 YiLvFold)

#### 1 判决

- **第 1 站 HOLDS.** 一套对目标层参数化的折叠 `ψ : (m x : LF) → .(Dom x) → Raw m`, 证书无关, 行都是 `refl`; 对一切 n, ψ₀(Ω̂ (sucⁿ 0)) 合法; ψ₀(Ω̂ ω) 合法.
- **第 2 站 PARTIAL.** K = ω 做成: ψ₀(Ω̂ (suc ω)) 合法, 派发在目标层 ω 及其下完全. 一般的 K: 闭项对任意派发合法, 但派发的完全性没有, 而且在我的写法里拿不到 (见 §5).
- **第 3 站 PARTIAL.** 闭项 `T₃ : R` 与 `Lgl zero T₃` 无前提, 根上的行是 `refl`, 第 η 支的折叠就是同一个 `ψ zero`. 但 `T₃` 的读法**不能写成 ψ₀(Ω_Ω)**: 派发在链点的层号上是否完全没有证. 只有块内的第一位置下界.

对纲领与目标意味着什么: "对层号参数化" 这件事做成了, 没有逐层手写, 没有记号, 没有 Funext. 但做成的方式暴露了一件要紧的事: **输出合法、带嵌套证据、保持第一位置, 对任意派发都成立, 包括恒折叠的派发.** 所以乙线上 "闭项合法" 不携带强度信息; 强度全在派发是否正确, 而这要值定理来验收, 本轮没有值定理. 与已封存的 BTBO 持平这一目标没有达到.

#### 2 文件表 (都在 `<仓库>/probes/OCF/Align/`)

| 文件 | 代码行 | 冷编退出码 |
|---|---|---|
| `YiLvFoldAdd.lagda.md` | 213 | 0 |
| `YiLvFoldBase.lagda.md` | 140 | 0 |
| `YiLvFold.lagda.md` | 186 | 0 |
| `YiLvFoldFin.lagda.md` | 188 | 0 |
| `YiLvFoldLim.lagda.md` | 126 | 0 |
| `YiLvFoldTw3.lagda.md` | 91 | 0 |

口径: 代码块内非空行. 冷编: 删这六个模块自己的 `.agdai` 后按依赖顺序各编一次, `-M6G`, 每个约 2 秒. `importclosure.py` 六个都 OK (禁用表命中 0). 禁用构造检索 0. 没有验收文件.

#### 3 定理表 (全部是编译定理, 除标明者)

| 名字 | 白话 | 文件 |
|---|---|---|
| `add`, `plus`, `add-cp`, `add-weak`, `grow`, `add-lgl`, `add-ns` | 对层号一般的加法及其五条引理, 一切 `Plain` 层号 | Add |
| `nodeAt`, `node-dn`, `node-lgl`, `node-ns` | 按槽位造保留结点, 不搬运下界与分支域 | Base |
| `Fold.ψ`, `ψ-legal`, `ψ-nested`, `ψ-pos`, `ψ-position` | 折叠; 对**任意** `way` 输出合法, 带嵌套证据, 头为正, 保持第一位置 | Fold |
| `zero-row`, `suc-row`, `lim-row`, `node-row`, `keep-row`, `fold-row`, `next-additive`, `certificate-free` | 各行, 都是 `refl` | Fold |
| `complete-fin`, `sound-fin`, `keep-fin` | 有限层号上, 保留当且仅当目标层 = suc (e + 结点层号) | Fin |
| `foldᶠ-legal`, `foldᶠ-row` | 对一切 n, ψ₀(Ω̂ (sucⁿ 0)) 合法; 链行对 n 一致 | Fin |
| `fold-Ωω-legal`, `fold-Ωω-row` | ψ₀(Ω̂ ω) 合法, 等于各项折叠的极限 | Fin |
| `keep-row₁`, `gt-row₀`, `feedback-row₁`, `gt-row₁`, `plus-top₁` | 层号 0, 1 上与 `FbRows` 同形的行 | Fin |
| `way-ω`, `complete-ω`, `complete-sub`, `keep-ω-row` | 目标层 ω 上层号 sucʲ 0 保留在槽位 (j+1, inj₁); ω 及其下完全 | Lim |
| `fold-Ωω1-legal`, `fold-Ωω1-row`, `fold-Ωω1-feedback` | ψ₀(Ω̂ (suc ω)) 合法, 链在 `Raw ω` 里由 `ψ ω` 推进 | Lim |
| `General.fold-K-legal`, `fold-K-free` | 任意派发, 任意合法 `Plain` 的 K, ψ₀(Ω̂ (suc K)) 合法; 输出不读 `Legal K` | Lim |
| `bare-incomplete` | `wayᵇ` 在目标层 `suc ω` 上漏掉层号 ω | Lim |
| `branch-complete→lpo` | 派发参数在 `tw 3` 带守卫分支的层号上处处完全, 则 LPO | Lim |
| `T-legal`, `T₃-legal`, `T₃-row`, `T₃-term`, `T₃-feedback` | `tw 3` 的折叠对任意派发合法; 根上的行 | Tw3 |
| `fin-below-T₃` | 每个 `foldᶠ n` 是 `T₃` 的字面第一位置 | Tw3 |
| `test-same`, `test-above`, `test-below`, `test-keep`, `test-compare` | **有限测试** | Fin, Lim |

条件定理一条: `branch-complete→lpo : ∀ way → BranchComplete way → N.LPO`, 其中 `BranchComplete way = ∀ (η : R) (e : Gd zero raw1 η) (q : Pre (read0 η)) → Complete way (lev (read0 η) q)`. 它是把否定路的 `YiLvNegKeep.bare-way→lpo` 接到我的 `Fold` 参数上, 编译通过, 所以否定路那条观察确实指的是这个参数. 前提的可满足性沿用否定路: 在排中律实例 `Locate` 下有模型, 构造性的实例没有.

#### 4 设计上的关键选择

- **折叠写在 `LF` 上**, 不在 `Raw K` 上. 派发是模块参数 `way : ∀ m k → Way m k`, 只读两个裸层号.
- **证书全部无关.** `ψ` 只把 `Dom` 的分量交到无关位置. 相关地用证书的只有合法性, 嵌套, 位置保持这几条证明, 与 `YiIrrFb` 相同.
- **保留行没有搬运.** `Way` 的 `keep s (e : lev m s ≡ k)` 匹配成 `refl` (k 是变量), 之后 `nodeAt` 对 (m, s) 递归到 `suc k′` 的 `inj₁`, 那里 `Low` 字面就是 `Raw k′`. 简报担心的沿 `Low-lev` 搬运没有出现.
- **"相等" 并入 "之上"**, 与你的 §2.1 一致: 一个 `fold` 子句, 链在 `Raw k` 里, 观察取目标层 m.
- **加法用值域接口 `Alg k`**: 递归到低层时把 "在槽位 r 上造结点" 作参数传下去, 所以也不搬运.
- 与 §2 不同的三处:
  1. §2.2 预计一般目标层要写在 `Raw K` 上. 我没有这样写. 理由: 位置保持的自反子句是 `inj₁ refl`, 靠的是输出只是树的函数; 槽位若取自输入的位置或证书, 同一棵子树的两处出现会得到不同槽位.
  2. §2.4 预计第一个障碍是链点的 `Lgl` 无关. 在我的写法里障碍更早: 不在链点, 在每个结点的派发数据从哪里来 (§5).
  3. 极限层号上 `x + top` 我取了逐项累加 `x + top_{f 0} + … + top_{f n}`. 原因是块本身: `DnT (lim f) a = ⊥`, 且 `DnK (lim f) n m` 要 n ≡ m, 所以 `λ n → x + top_{f n}` 不是合法的 ℕ 极限. 这是加法的定义, 没有改被折叠的树.

#### 5 第一个障碍

位置: `YiLvFold.lagda.md` 里 `ψ m (lc k c w b t g) d = ψn m k (way m k) c w b t g d` 这一句的 `way m k`.

保留需要 `keep s e` 这份数据. 它的三个可能来源:
- **裸层号**: m 含 ℕ 极限时不行. `bare-incomplete` 是具体一例 (两个极限层号字面相等不能由形状判定); `branch-complete→lpo` 是一般的.
- **无关的证书 `d`**: 否定路 `keep→irr-search` 已覆盖.
- **相关的证书**: 这时 `ψ-position` 的自反子句不再是 `inj₁ refl`. 这一变体我**没有写代码**, 所以没有检查器报错原文; 以下是判断.

缺的东西 (判断, 未编译): 位置保持要改成限制形式, 类型大致是 `∀ m x y (dy : Domᶜ y) (p : CP x y) → Cp m (ψ m x (restrictDom p dy)) (ψ m y dy)`, 定义域要带一致性 (`CohDom`), 并且每条合法性引理 (各层的加法, 各层的链, 保留结点) 都要配一条 "与限制交换". 否定路只在目标层 0 做了这些. 链点还要带相关的守卫, 这会让 `ψ` 的输出依赖 `ψ-legal`.

没有判定的: 只在链点上 (而不是一切带守卫的分支上) 完全的裸派发是否存在. 没有实例, 也没有否定; "在链点上完全" 我也没有写成类型, 因为它要对内层链点遗传.

判断: `wayᵇ` 在 `T₃` 的计算里实际会漏保留 (例如目标层 suc K, 结点层号是极限 K). 这一条没有编译见证.

#### 6 值

参照族的值定理: **没做**, 三站都没有.

有的只是块内关系: `fin-below-T₃ : ∀ n → Cp zero (foldᶠ n) T₃`. 读法: T₃ 不低于每个 ψ₀(Ω_n). 这是读法, 因为 `foldᶠ n` 自己也没有对参照验收; 有限层号上派发正确是编译定理 (`sound-fin`, `keep-fin`).

各站读法: ψ₀(Ω_n) 对一切 n, ψ₀(Ω_ω), ψ₀(Ω_{ω+1}). 都是读法.

#### 7 偏离与事故

- **没有按 "比较层号一律走 `YiLvIf.Compare`" 做.** `wayᵇ` 在目标层 `lim f` 上只看第 j+1 支 (j 是结点层号头上的后继个数), 那一支字面是 `suc k` 才保留. 它不判定两个极限层号相等, 但确实读了裸的极限目标层. 这是只为 ω 写的一种形状, 不是一般办法. `compare` 只做了一个实例测试 (`test-compare`).
- **第 0 层的 ω 倍第 0 项取一份** (`copies m y 0 = y`), 对一切层号同一写法; `YiIrrFb` 在第 0 层取零份. 正性相应地只看头 (`Pos`), 没有 `Dn 0 zero y` 那一条.
- **与 `YiIrrFb` 的字面一致没有证.** 加法是 `plus`, 不是 `_+ʳ_`, `_+¹_`; 只交了同形的行.
- `YiLvFoldLim` 导入了否定路定稿的 `YiLvNegCompare.At` 与 `YiLvNegKeep`. 我原先自己写的一条较弱的 LPO 探针 (用 `high α`) 换成了这座桥.
- 对共用接口的增补都在自己文件里: `Way`, `nodeAt`, `Alg`, `Complete`, `BranchComplete`.
- 没有改任何已有文件, 没有碰 `src/`, `archive/`, 没有提交. 只删过自己六个模块的 `.agdai`. 无堆耗尽, 无超时.
- 你来信第 7 条 (链点取 `c + cum v`) 与 "相关证书加 `ccompare`" 两条路都没有走.

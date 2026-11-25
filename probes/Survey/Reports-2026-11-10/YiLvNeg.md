# 乙线第 3 步，否定路 (YiLvNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-10 15:40 至 16:30 |
| 工具调用 / agda 编译 (粗数) | 64 / 22 |
| token (usage 字段，按消息去重) | 输出 301295；新写入缓存的输入 848445；读缓存的输入 13830142；其余输入 100 |
| 写过的仓库文件 | `YiLvNegCanon.lagda.md`, `YiLvNegCert.lagda.md`, `YiLvNegCompare.lagda.md`, `YiLvNegCum.lagda.md`, `YiLvNegKeep.lagda.md`, `YiLvNegRestrict.lagda.md` |
| 文件前缀 | `YiLvNeg` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 乙线第 3 步否定路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 层号的合法性必须作为相关数据到达比较处；五类写法被编译定理排除，规范槽位与目标层 0 上的限制形式是正面结果；六件冷编退出码全 0；没有值 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "乙线第 3 步, 否定路": 对同一个共用接口写编译过的否定定理与边界定理. 另一路 (构造路, 前缀 `YiLvFold`) 同时在做构造. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条 (尤其第 3 条壁垒); "量化域先取带证据的读回域" (反例对象不在读回域内的否定, 读作 "谓词太宽", 不读作数学障碍); "律带公共上界, 构造与否定配对"; Agda 一节 (选项, 无关参数, 文字预算, 退出码, 堆); "结论的写法" (否定要编译定理且否定的确实是那条路线; 前提要可满足; 穷尽是判断; 归到已知的墙要逐条核机制).
2. `probes/Survey/EBOHandbook.md` 只读 §3.13 (空真), §4.1 到 §4.5, §5.4. `probes/Survey/RR5-SoftStops.md` 只读 §2.
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`):
   - 块与接口, 定稿, 只增不改, 不许编辑: `RR5IrrCore` (块), `RR5IrrCheck` (`up`, `upN`, `upT`, `Ω̂`, `tw`, `Λ`), `YiIrrIf` (`CP`, `Legal`, `FoldRows`, `read0`), `YiLvIf` (**本步的共用接口**: `Plain`, `OnlyP`, `lev`, `Low-lev`, `shift`, `Tri`, `Compare`, `CompareIrr`, `compare`, `Kept`, `tw3-onlyP`).
   - 上一轮否定路的写法与可复用的定义: `YiIrrNegWide` (`Found`, `IrrSearch`, `seen`, `mark`, `high`, `high-legal`, `wide→irr-search`), `YiIrrNegWideDecide` (`IrrDecide`), `YiIrrNegDispatch` (`locate→irr-search`), `YiIrrNegModel` (不可反驳的模型怎么写), `YiIrrNegLegal` (`Legal-Ω̂`, `lgl→Legal`, `Legal-tw`).
   - 上一步的折叠, 供你了解行的形状: `YiIrrFbIf` (`FbRows`), `YiIrrFb`.
   - 旧块上的同类结果, 只作参照: `YiK2cIrr` (`lim-function-equality-required`), `YiLevelCompare`.
   - 参照 (只读): `src/OCF/BTBO.lagda.md` 第 640 到 710 行 (`Ordᴰ` 的极限自带单调证明, `<-dec`) 与第 838 到 1038 行 (`ψ<`, `ordᴰ`, `cumsum`).
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么

乙线: 层号是树 (`LF`), 第 k 层的树是 `Raw k`. 已做成目标层 0 的完整折叠与第一次回灌 (层号字面为 0 或 1, 派发按字面形状). 本步是 **层号任意可数**: 目标是塔的第 3 项 `tw 3` (第 η 支是 Ω̂ (read0 η), 层号是任意的 `Plain` 树; 读法 ψ₀(tw 3) = ψ₀(Ω_Ω), 与 BTBO 持平) 的折叠闭项. 这是乙线第一次要比较层号. 共用接口 `YiLvIf` 把律的定义域钉成: 被比较的两个层号是同一个字面层号 K 里的两个位置 (`Compare`); `compare` 已证明合法性作数据 (相关参数) 时有界比较成立.

折叠到目标层 m 遇到层号 k 的结点: k 严格在 m 之下则保留, 输出 `Raw m` 的结点 `G.lc s …`, 槽位 `s : Pre m` 是数据 (`YiLvIf.Kept` 就是 "输出是层号 k 的保留结点" 的陈述); 否则折叠, 链在 `Raw k` 里.

### 2 主审的纸面分析 (判断, 没有验证). 你的任务是把其中能定的定成编译定理, 并挑战其余

主审预计的障碍: 层号含 ℕ 极限 `lim f` 时, 比较不同分支上的两个位置要 `CP (f n) (f m)` 的路径数据, 它在 `Legal K` 里; 这个块的合法性在树外, 折叠的证书是无关参数; `tw 3` 根上的链点只带无关的 `Lgl zero η`. 主审列的出路有三种, 并且认为 "只有这三种" (这是判断, 请先挑战): (a) 合法性作相关参数沿链传, 配证书的一致 (极限行各分量 `lf n` 与 `lf (n+1)` 沿 `st n` 的限制相等) 与限制形式的位置保持; (b) 像 BTBO 那样把输出累加归一后再作层号, 路径由树算出; (c) 路径数据进树 (改块, 不在本轮范围).

请按下面的次序做. 每条交编译过的定理, 或写明 "没写成"; 前面的便宜, 先做.

**N1 无关合法性下的有界比较.** `CompareIrr → IrrSearch` (或更强的结论). 主审手推的见证: K = lim f, f 0 = suc zero, f (n+1) = suc (high α); `Legal K` 当且仅当 α 有见证; 位置 (1, inj₁ tt) 的层号是 `high α`, 位置 (0, inj₁ tt) 的层号是 zero; `Tri (high α) zero` 只能是 `below`, 它的槽位给出见证. 请核对并写成定理. 再回答三个问题, 各写成定理或说明: (i) 反方向 `IrrSearch → CompareIrr` 成立吗 (两者等价的话, `CompareIrr` 的强度就定了); (ii) 这个见证层号是不是某个带守卫的坐标 η 的读回 `read0 η`, 即它在不在 `tw 3` 的分支域里 (守卫只需无关地成立); 它在不在 `tw 3` 的折叠实际走到的链点里, 是另一个问题, 写明你没有或有判定; (iii) 结论对 "两个位置字面上互为延伸" 的情形 (一个位置是另一个的前缀延伸) 是否仍然需要数据, 即哪一类位置对的比较不读合法性.

**N2 `LF` 上证书无关的一般目标层折叠.** 把 `locate→irr-search` 推到本步的片段上: 设折叠 `ψ : (m x : LF) → .(证书) → Raw m` 在 `OnlyP` 的某个对分支遗传, 含 `tw 3` 的定义域上有保留律 (层号 k 在目标层 m 之下的结点, 输出满足 `Kept m k`), 则得到 `IrrSearch` 或类似结论. 把保留律写成最弱的, 构造路无论怎么设计都得满足的形状; 写明你的律的每个前提在规范实例上可满足.

**N3 证书作数据时, 输出依赖证书.** (1) 给出一个 `Plain` 的层号 K 与它的两份合法性证书 L, L′, 使 `compare K pl L q q′` 与 `compare K pl L′ q q′` 给出不同的槽位 (编译的不等式). (2) 更一般: 存在不依赖合法性证书的 `Compare` 实现吗 (对一切 L, L′ 输出相等)? 主审猜它蕴含某种全知原理 (要在极限里找最小的可行分支), 请定成定理或给出实现. (3) 由此: 若折叠取相关的层号合法性, 且位置保持按 "两份独立证书" 的形式陈述 (像 `FoldRows.position` 那样 `dx`, `dy` 各自任意), 这个陈述是否不可满足或要求函数相等 (对照 `YiK2cIrr.lim-function-equality-required`)? 写成对一个最小记录的定理.

**N4 证书的一致能不能证.** 定义沿第 0 层第一位置路径的限制 `restrict : Cp zero a b → Lgl zero b → Lgl zero a` (以及 `Legal` 沿 `CP` 的限制), 检验规范证书是否一致, 不用 Funext: 加法 (`restrict (add-weak …) (add-legal …) ≡ lx` 一类), `copies`/`successor`, 以及目标层 0 折叠的合法性引理 (`YiIrrFold` 的 `ψ-legal`, `ChainLegal.collapse-legal`) 的输出. 交: 成立的写成定理; 不成立的给出编译的反例; 需要 Funext 才成立的写成 "条件" 并指出是哪一处的函数相等. 这一条是给出路 (a) 探路, 正面结果同样要交.

**N5 累加归一.** 定义第 0 层的累加归一 `cum : R → R` (极限处取部分和) 与它不要证书的合法性; 检验 "对第一位置单调" (`Cp zero a b → Cp zero (cum a) (cum b)`) 是否成立: 成立就证, 不成立给编译的反例 (主审手推: y 不是 x + y 的第一位置). 由此说明把 `tw 3` 的分支换成 Ω̂ (read0 (cum η)) 之后的树过不过 `Legal` 的 dir 项. 只否定写明的这一种归一, 不否定 "存在某种归一".

**N6 挑战穷尽.** 主审说出路只有 (a)(b)(c). 找一个不在其中的办法, 或指出其中哪一条其实已被上面的定理排除或支持. 这一条允许只交判断, 但要标明.

做不完不要紧: N1 到 N3 是主要的, N4, N5 是探路. 每条定理写清它否定的是哪一种写法, 不否定什么; 反例对象是否在读回域内.

### 3 规则

- **只新建文件**, 前缀 `YiLvNeg` (如 `YiLvNegCompare`, `YiLvNegKeep`, `YiLvNegCert`, `YiLvNegRestrict`, `YiLvNegCum`), 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiLvIf`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 构造路在用前缀 `YiLvFold`, 不要动它的文件, 也不要依赖它 (它在变). 需要对共用接口增补就写在你自己的文件里, 并在回报里说.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 所在文件文首标 "条件".
- 否定结果写成编译过的定理; 有限样本的测试标为测试. 没有编译定理的地方只写 "未走通" 或 "没写成", 不写成路线已否定. 每个否定定理与条件定理的前提给一个实例或说明为何可满足.
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件; 编译表不进文件. 一次性的试验放你的临时目录, 用纯 `.agda` (仓库外的文件要自己写上仓库的全部选项, 见 AGENTS).
- 仓库文件里不写本机路径 (含临时目录路径).
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写精确名字, 不用通配: 构造路的前缀与你的前缀开头相同).
- 你的临时目录: `<实验目录>/agents/lvneg`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 通过; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 一段话, 先说对纲领与目标意味着什么 (哪些写法被编译定理排除, 哪些没有, 构造路该避开什么).
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表, 按 N1 到 N6: 名字, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 每条否定写: 否定的是哪一种写法; 反例对象是否在 `tw 3` 的读回域内; 前提的实例.
4. 正面结果 (N4 的一致性引理等) 单列.
5. 没写成的条目与第一个障碍 (检查器报错原文, 缺的引理的 Agda 类型).
6. 偏离与事故.
证书, 闭项, 值分开说; 不用 "只差", "自然" 一类形容; 不把 `IrrSearch` 说成矛盾 (它在通常语义下为真, 只是这里推不出).

## 回报原文

### 乙线第 3 步 否定路 (YiLvNeg) 回报

#### 1 判决

**对纲领与目标。** 没有触到纲领四条, 没有新的壁垒实例, 没有记号; 没有值, 强度不变。对 "树自足" 的含义是一条树侧判据: **层号的合法性必须作为相关数据到达比较处**, 并且分三档, 每档都有编译定理:

- 派发只读两个裸层号而又正确 ⟹ LPO (`bare-way→lpo`; 对象在带相关守卫的读回域内)。
- 合法性或证书只无关地给 ⟹ `IrrDecide`/`IrrSearch` (`compare-read→irr-decide`, `keep→irr-search`, `lv-irr→irr-search`)。`IrrSearch`, `IrrDecide` 在通常语义下为真, 这里只是推不出; 三条的前提在排中律的一个实例 `Locate` 下都有模型, 所以都不可反驳, 不读作数学障碍。
- 合法性作数据 ⟹ 比较成立 (`YiLvIf.compare`), 而且槽位可以取成只由两个层号决定的规范位置, 不要全知原理 (`ccompare`, `ccompare-levels`)。

**被编译定理排除的写法:** (1) 无关合法性下的有界比较; (2) 证书无关 + 定义域对一切带守卫的分支遗传 + 保留律; (3) 把层号合法性放进证书但经无关守卫遗传; (4) 只读裸层号的正确派发; (5) 位置保持带两份独立证书且槽位取自 `compare` (不可满足), 一般情形它要求极限行的函数相等; (6) 把 `tw 3` 的分支换成 `Ω̂ (read0 (cum η))` (不过 `Legal` 的 `dir`)。

**没有被排除的:** 出路 (a) 按限制形式陈述位置保持 (目标层 0 上限制形式与证书一致都证了, 不用函数外延); 出路 (b) 只在链上归一、不改树 (守卫与路径由树算出, 折叠没写); 证书相关的折叠; 定义域只沿链点遗传的折叠。

**构造路该避开:** 上面 (1) 到 (6); 位置保持写成限制形式 (小树的证书取大树证书沿路径的限制), 证书里带一致性; 保留槽位用规范位置而不是 `compare` 的原始输出。

#### 2 文件表

代码行数 = agda 代码块内非空非注释行。全部 `--safe --without-K --lossy-unification`; 删各自接口后按依赖序冷编译, 6G, 每个约 2 秒。`importclosure.py OCF.Align.<模块>` (无 `--only`) 六个都 OK; 禁用构造检索为 0 (文件里不出现 Funext 一词)。

| 文件 | 代码行 | 冷编译 |
|---|---|---|
| <仓库>/probes/OCF/Align/YiLvNegCompare.lagda.md | 279 | 0 |
| <仓库>/probes/OCF/Align/YiLvNegKeep.lagda.md | 268 | 0 |
| <仓库>/probes/OCF/Align/YiLvNegCert.lagda.md | 136 | 0 |
| <仓库>/probes/OCF/Align/YiLvNegCanon.lagda.md | 156 | 0 |
| <仓库>/probes/OCF/Align/YiLvNegRestrict.lagda.md | 269 | 0 |
| <仓库>/probes/OCF/Align/YiLvNegCum.lagda.md | 188 | 0 |

依赖: Compare ← {Canon, Keep, Cum}; Cert ← {Canon, Restrict}。导入的旧模块: `YiIrrNegWide`, `YiIrrNegWideDecide`, `YiIrrNegLegal`, `YiIrrFoldBase`, `YiIrrFold`; 没有导入 `YiLvFold*`。日志在 <实验目录>/agents/lvneg/ (`cold-YiLvNeg*.log`)。

#### 3 定理表

内部名字: `At i j` = j 是 i 的某个位置上的层号 (`Σ s. lev i s ≡ j`); `PosIrr` = 凭无关的 `At i j` 交出相关的; `EqIrr` = 凭无关的 `a ≡ b` 交出相关的 (Plain 层号); `IrrDecide` = 对单调布尔列, 凭无关的 "字面全假或有真值" 判定是哪一种 (取自 `YiIrrNegWideDecide`); `Locate` = 判定 `At m k` 的神谕 (排中律的实例)。

##### N1 (YiLvNegCompare) 全部编译定理

| 名字 | 白话 |
|---|---|
| `compare-irr→irr-search` | `CompareIrr → IrrSearch`。主审的手推核对成立 |
| `compare-read→irr-search`, `compare-read→irr-decide`, `compare-irr→irr-decide` | 只对坐标的读回陈述 (`CompareRead`: η 的 `Lgl` 无关) 也推出 `IrrSearch` 与更强的 `IrrDecide` |
| `compare-irr→pos-irr`, `pos-irr→compare-irr` | (i) `CompareIrr ⟺ PosIrr`, 强度定在这里 |
| `pos-irr→eq-irr`, `compare-irr→eq-irr` | 还推出 `EqIrr` |
| `witness-branch`, `witness-guard`, `guard→found`, `tw₃-branches` | (ii) 见证层号是 `read0 (coordᴺ α)`, 它是 `tw 3` 的第 `coordᴺ α` 支的层号; 守卫与 `Found α` 等价 |
| `prefix→tri` | (iii) 两个位置相同或互为延伸时三路直接写出, 对一切层号, 不要 Plain 与合法性 |
| `compare-bare→⊥` | 合法性前提整个去掉则不可满足 (不合法层号上三路都不成立) |
| `wf-all`, `no-loop` | 位置关系良基, 三路互斥 |

- 否定的写法: 合法性只作无关参数交给比较。不否定 `Compare`。
- 反例对象: 在 `tw 3` 的分支域内 (守卫无关地成立时); 守卫相关时见证在守卫里。是不是折叠走到的链点: **没有判定** (纸面: 链点除起点外是第 0 项非 1 的极限, 不是)。
- 前提实例: `closed-legal`, `closed-is-below` (α 恒真, 计算检查); `IrrDecide` 的 `Mono`/`Evidence` 用旧文件的 `quiet`, `loud`; `CompareIrr`, `PosIrr` 在 `Locate` 下有实例 (`locate→compare-irr`, 在 Keep 文件)。
- 与主审手推的差别: 见证没有用字面的 `high α`, 改用读回 `read0 (dense α)`, 这样它字面上在分支域里 (两者只逐点相等)。

##### N2 (YiLvNegKeep) 全部编译定理

| 名字 | 白话 |
|---|---|
| `keep→locate`, `keep→irr-search` | 记录 `KeepRows` (证书无关的 `ψ : (m x) → .(Dom m x) → Raw m`; 目标层 0 的三条遗传 `dom-branch`/`dom-step`/`dom-out`, 形状取自 `FoldRows`/`FbRows`; 保留律前提是相关槽位) ⟹ `IrrSearch` |
| `bare-way→lpo` | 派发 `way m k` 只读两个层号, 律只要求 "k 在 m 的位置上则保留", 定义域只取 `tw 3` 带相关守卫的坐标读回里的层号 ⟹ LPO |
| `lv-irr→irr-search` | 证书里放相关的 `Legal k` 但对分支遗传时守卫无关 (`LvIrr`) ⟹ `IrrSearch` |
| `oracle-model`, `oracle-way`, `locate→pos-irr` | `Locate` 下 `KeepRows`、正确的裸派发、`PosIrr` 都有实例 |
| `probe-onlyP₁..₃`, `probe-legal₁`, `closed-root-guard`, `start-guard₃`, `slot₁` | 探针在 `OnlyP` 里, 给相关证据时合法; 各前提的规范实例 |

- 保留律的形状: 前提取相关槽位 `(s : Pre m) → lev m s ≡ k`, 结论 `Kept m k`; 遗传前提取 "0 在 k 的位置上" 的相关证据 (比 "k 非零" 强, 所以律更弱)。
- `keep→irr-search` 否定的: 证书无关且定义域对**一切带守卫的分支**遗传。探针坐标在分支域内 (守卫无关成立), 不是链点 (纸面, 没有判定) ⟹ 读作这个定义域太宽 / 证书必须相关。
- `bare-way→lpo` 否定的: 派发不读位置不读证书而处处正确。对象 `suc (1 + dense α)` 对一切 α 有闭形式的相关守卫, **在带相关证据的读回域内**; 不否定读公共上界里的位置与合法性的派发。同 AGENTS "裸下标上的律重证判等" 形状相近, 我没有逐条核机制, 不归类。
- `lv-irr→irr-search` 的前提 `LvIrr (tw 3)` 没有 Agda 实例 (纸面: 在 `.(Legal K) → Legal K` 这类原则下沿 `up-onlyP` 的递归可得, 未编译); 守卫相关的同形谓词由 `Legal-tw 3` 满足。

##### N3 (YiLvNegCert, YiLvNegCanon) 全部编译定理

| 名字 | 白话 |
|---|---|
| `compare₀`, `compare₁`, `compare-reads-certificate` | (1) 层号 `Kᶜ = read0 κ` 的两份证书让 `compare` 交出槽位 0 与 1, 不等 |
| `ccompare`, `ccompare-slot`, `ccompare-levels`, `ccompare-shift`, `canon-const`, `canon₀/₁` | (2) **正面**: 规范比较; 形状与槽位与证书无关, 且只由两个层号决定 (换公共上界、沿路径搬位置都不变)。极限处取最小可行分支, 是有界搜索 |
| `Forced.coherence`, `Forced.slot-coherence` | (3) 位置保持带两份独立证书 (`CertRows.position`) ⟹ 换证书输出相等, 保留槽位与证书无关 |
| `Forced.LimRow.lim-function-equality-required` | 加上极限逐项 ⟹ 两族任意证书给出的输出函数字面相等 |
| `no-by-compare` | 槽位取自 `compare` 的写法 (`ByCompare`, 只对 `Kᶜ` 一个实例要求) 不可满足 |
| `antisym`, `dn-acc` | Plain 层号的 `Raw m` 上第一位置无环、反对称 (一般层, 含 `em`/`top`) |

- 主审猜 "证书无关的 Compare 蕴含全知原理": 对形状与槽位**不成立**, 实现是 `ccompare`。对完整的 `Tri` 相等 (含方程分量) 没写成, 见第 5 节。
- 反例对象 `κ` 是闭的, 两份守卫都是闭的相关证明, 在 `tw 3` 的分支域内; 是不是链点没有判定。前提实例: `CertRows` 有 `trivial`; `ByCompare.keep` 的前提由 `compare₀/₁` 满足。
- 函数相等一条: 是 "要求", 没有证明它不可得 (与 `YiK2cIrr` 同档)。

##### N4 (YiLvNegRestrict) 见第 4 节; 反面两条

| 名字 | 白话 |
|---|---|
| `independent-differ` (配 `κ-coh`) | 同一个值的两份证书各自一致却不相等: 一致不给出证书唯一 |
| `fold-legal-reads-certificate` (配 `same-output`) | `YiIrrFold.ψ-legal` 对两份定义域证书给出不相等的输出证书 (ψ 的输出相同, `refl`) |

##### N5 (YiLvNegCum) 全部编译定理

| 名字 | 白话 |
|---|---|
| `cum-legal`, `cum-level-legal` | 正面: 归一后的值不要证书就合法, 层号 `read0 (cum η)` 的 `Legal` 由树算出 |
| `cum-not-monotone`, `cum-mono-fails` | `ω ⊲ lim (1, ω, ω, …)` 但归一后不是第一位置 (两个对象都合法)。主审的手推成立 |
| `dir-fails`, `cum-tower-not-legal` | 分支换成 `Ω̂ (read0 (cum η))` 的 `tw 3` 不过 `Legal` 的 `dir`; ω 与 b 是带闭守卫的坐标, 在分支域内 |
| `cum-add-weak`, `chain-dir` | 正面: 沿链的一步 `η ⊲ η + y` 归一保持第一位置 |
| `norm-guard`, `norm-directed`, `norm-level-legal`, `tw3-chain-step` | 正面: 树不改, 链点取 `c + cum v`, 则守卫、相邻两支的路径、层号的合法性都由树与下界的合法性算出, 不调用折叠的输出合法 |

只否定 "把树的分支换成归一后的读回" 这一种; 不否定别的归一, 不否定只在链上归一。

##### N6 挑战穷尽 (判断, 除注明外没有定理)

- 没有找到 (a)(b)(c) 之外的办法。试过并落空的: 只比较互为延伸的位置 (纸面: 目标层取极限层号第 n 支里的位置时, 要派发 `Ω̂ k` 其余各支的结点, 两个位置在极限处分叉); 只读裸层号 (定理 `bare-way→lpo`); 证书经无关守卫遗传 (定理)。
- (a) 被支持并被收窄: 目标层 0 上限制形式与一致性成立 (第 4 节定理); 槽位可规范 (定理); 但位置保持不能写成两份独立证书 (定理)。一般目标层没有折叠可检验。
- (b) 分成两种: 改树的被 `cum-tower-not-legal` 排除; 链上归一的有 `norm-guard` 等支持, 但它改了链的行 (`next-additive` 不再逐字成立), 下界的合法性仍要一份相关证明, 折叠与值都没有。
- (c) 没有碰。

#### 4 正面结果 (N4, 全部编译定理, 不用函数外延)

- 限制 `restrict` = `lgl-cp₀` (取路径所指的子证书); `restrictDom` (定义域证书沿 `CP`), `restrictL` (`Legal` 沿 `CP`)。
- 加法: `restrict-add-weak` (`restrict (add-weak x y) (add-legal x y lx ly) ≡ lx`), `restrict-add` (加法对第二个加数的路径)。
- 一致 `Coh` (极限处第 n+1 项证书沿第 n 步限制等于第 n 项, 逐项): `add-coh`, `copies-restrict`, `copies-coh`, `successor-coh`。
- 折叠: `ψ-legal-restrict` (限制形式的位置保持与输出证书相容, **无前提**); `ChainCoh.collapse-coherent`, `ChainCoh.collapse-coh` (`ChainLegal.collapse-legal` 的输出, 前提是分支引理沿守卫的限制); `ψ-legal-coh` (在一致的定义域证书 `CohDom` 上输出证书一致); `Ω₁-cohdom`, `Ω₁-legal-coh` (规范 Ω₁ 满足前提)。
- 读回与限制可交换: `restrictDom-read0`, `read0-cohdom`, `restrictL-read0`, `read0-legal-coh` (一致的坐标证书读成一致的层号证书)。
- 需要函数外延才成立的一致性陈述: 这条线上没有遇到; 遇到的只有 N3 的两份独立证书形式。
- 另: `compare-read` (坐标合法性作数据时比较成立), N3 的 `ccompare` 一组, N5 的正面各条。

#### 5 没写成的条目

没有被检查器拒绝后放弃的条目 (只有两处笔误: `zero` 歧义, 变量名撞构造子 `lc`, 已改); 下面都是没有去编码或缺引理。

| 条目 | 第一个障碍 |
|---|---|
| `IrrSearch → CompareIrr` | 没写成。它要 `EqIrr`, 缺的是 `∀ (f g : ℕ → LF) → .(lim f ≡ lim g) → f ≡ g`; 层号相等不可判定, 不是可判定谓词上的搜索。纸面: `EqIrr` 在函数外延下可逐点归纳证出, 未编译 |
| `ccompare` 的方程分量与证书无关 | 缺 `∀ i s j (e e′ : lev i s ≡ j) → e ≡ e′` (层号相等证明唯一); 判断: 本仓库选项下对含极限的层号证不出。折叠沿 `e` 搬运下界, 所以 "换证书输出相等" 除槽位外还要这一项与函数相等一项 |
| 见证/探针是不是 `tw 3` 折叠的链点 | 没有判定; `tw 3` 的折叠还没有 |
| 一般目标层上的 N4 | 没有可检验的折叠 |
| `KeepRows → IrrDecide`; 原始 `compare` 对限制的交换性 | 没有尝试 (后者的规范版本是 `ccompare-shift`) |

#### 6 偏离与事故

- 对共用接口的增补都写在自己的文件里: `At`, `lev-legal`, `ext`/`lev-ext`/`Prefix`, `CompareRead`, `PosIrr`, `EqIrr` (Compare); `KeepRows`, `Locate`, `LvIrr`, `BareWay` (Keep); `CertRows`, `ByCompare` (Cert); `Shape`, `ccompare` (Canon); `restrict`, `Coh`, `CohDom` (Restrict); `cum` (Cum)。`YiLvIf` 等已有文件没有改。
- 任务外加做的: `bare-way→lpo`, `lv-irr→irr-search`, `compare-read→irr-decide`, `ccompare-levels`, `norm-guard` 一组。
- 末尾只读地看过构造路三个文件 (`YiLvFold`, `YiLvFoldBase`, `YiLvFoldAdd`) 的文首与 `ψ` 的签名, 没有导入, 没有编辑。当时 `ψ : (m x : LF) → .(Dom x) → Raw m`, 派发 `way m k` 只读裸层号, 文首写明值依赖派发是否正确。`bare-way→lpo` 与 `keep→irr-search` 说的正是: 这个参数在 `tw 3` 的分支域上没有构造性的正确实例, 正确的派发要读位置与相关的合法性。那些文件在变, 这一条未复核。
- 只删过自己六个模块的 `.agdai` (逐个写精确名字); 没有 `--ignore-interfaces`, 没有提交; 临时目录里建了一个未使用的 `exp/exp.agda-lib`。无堆耗尽, 无超时。
- 翻译账: 新定义都由树的要求给出, 没有读记号; `cum` 照 `src/OCF/BTBO` 的 `cumsum`。第 4 层逼出: 无。

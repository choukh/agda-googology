# 第 4 步第一站，否定路 (YiOmNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 05:21 至 05:55 |
| 工具调用 / agda 编译 (粗数) | 65 / 17 |
| token (usage 字段，按消息去重) | 输出 207730；新写入缓存的输入 593354；读缓存的输入 10931523；其余输入 90 |
| 写过的仓库文件 | `YiOmNegBranch.lagda.md`, `YiOmNegBranchFixed.lagda.md`, `YiOmNegSlot.lagda.md`, `YiOmNegTop.lagda.md`, `YiOmNegTrunk.lagda.md` |
| 文件前缀 | `YiOmNeg` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 第 4 步第一站的否定路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 保留行的障碍来自块的写法（推出凭无关证据取数据）；目标在某一支里而树是 top 时保留律推出 LPO；替代行够不到保留行的像；两种块变体的试验见附件；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "乙线第 4 步第一站 (公共上界含 Ω 结点), 否定路": 对同一个共用接口写编译过的否定定理与边界定理, 并给构造路与作者的裁决探路. 另一路 (构造路, 前缀 `YiOmFold`) 同时在做构造. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条 (第 3 条壁垒); "交替路线" (全分支的高层比较被禁止: `dec→WLPO`, `Trich₂→WLPO`, `noBT`); "量化域先取带证据的读回域" (反例对象不在读回域内的否定读作 "谓词太宽"); Agda 一节; "结论的写法" (否定要编译定理且否定的确实是那条路线; 前提要可满足; 归到已知的墙要逐条核机制).
2. `probes/Survey/EBOHandbook.md` 只读 §3.1, §3.13, §4.1 到 §4.5, §5.4. `probes/Survey/Reports-2026-11-11/README.md` 的 §2; 要细节再读同目录的 `YiRawFold.md`, `YiRawNeg.md` (上一轮两路的回报原文).
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - 块: `RR5IrrCore` (注意 `Pre`, `Low`, `Kid`, `KidR` 在 `lc` 层号上的子句: 分支里的位置与孩子带**相关的**守卫 `Gd k c η`; 而 `G.lc` 与 `LF` 的 `lc` 的分支函数只带**无关的**守卫), `RR5IrrCheck` (`up`, `upT`, `Ω̂`, `tw`), `YiIrrIf`.
   - **本轮的共用接口 `YiOmIf`**: `Slot`, `slot-rel`, `kid-rel`, `kid-rel-read`, `SlotIrr`, `KidIrr`, `Ω₁⁺`, `Ω₁⁺-form`, `start₂`, `start-branch`. 上两步的接口 `YiRawIf`, `YiLvIf`.
   - 上一轮否定路 (写法与可复用的定义): `YiRawNegOmega` (`K₂ω = tw 2`, `br`, `Link`, `compare-link`, `no-compare-tw2`, `dec-at→lpo`, `keep-fold→wlpo`, `oracle-model₂`), `YiRawNegModel`, `YiRawNegChain`, `YiRawNegLift`, `YiRawNegNorm`.
   - 更早的: `YiLvNegCompare` (`At`, `coordᴺ`, `levelᴺ`, `witness-guard`, `guard→found`, `found→lgl`), `YiLvNegKeep` (`level-legal→found`, `LPO`, `Locate`, `coordᴸ`), `YiIrrNegWide` (`IrrSearch`, `Found`), `YiIrrNegWideDecide` (`IrrDecide`), `YiIrrFoldSeed` (`Unsquash`).
   - 上一轮构造路 (了解折叠的行): `YiRawFold` (`Ψ`, `own`, `ownT`), `YiRawFoldTw3` (`T₃ᵐ`).
   - 参照: `probes/OCF/Barrier.lagda.md`; 仓库里已有的 `dec→WLPO`, `Trich₂→WLPO`, `noBT` (用检索找到所在文件).
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么

乙线: 层号是树 (`LF`), 第 k 层的树是 `Raw k`. 上一轮: 折叠写在 `Raw K` 上 (K 没有 Ω 结点), 派发处处完全; `tw 3` 的闭项合法 (读法与 BTBO 持平). 本步是层号不可数的第一站: 公共上界取 `tw 2` (读法 Ω₁, 它自己是 Ω 结点), 目标闭项是 `Ω₁⁺ = Ω̂ (suc (tw 2))` 的目标层 0 折叠 (读法 ψ₀(Ω_{Ω₁+1}), 第一个越过 BTBO 的规范结点). 它的链在 `Raw (tw 2)` 里, 起点 `top`, 由 "目标是 `tw 2` 自己" 的折叠推进.

历史上没有一条线过得去这里. 这一站最有价值的产出是编译过的事实: 哪一行不能写, 不能写是块的写法造成的 (可以改块解决), 还是壁垒 (改块也不行).

### 2 任务, 按次序; 每条交编译过的定理, 或写明 "没写成"

主审的看法都是判断, 没有验证.

**O1 `SlotIrr`, `KidIrr`.** 主审预计: 保留模式下折叠 `top : Raw (tw 2)` 时, 根是层号 0 的结点要保留, 它的第 η 支里的保留结点要落在第 η 支的槽位上 (或整支经 `em (η , e)` 嵌进来), 这要相关的守卫, 而分支函数只有无关的守卫. 请定: `SlotIrr` 与 `KidIrr` 各推出什么 (主审猜 `IrrSearch`: 取坐标 `coordᴺ α`, 它的守卫与 `Found α` 等价; 槽位若落在别的支里, 用 "那一支的合法性加层号相等推出 `Found α`" 一类的引理, 见 `level-legal→found`); 两者谁强; 它们在排中律的实例下有没有模型; 反例对象是否在规范的链走到的坐标里 (没有判定就写没有判定).

**O2 保留模式下 `top` 的行.** 写一个最小记录: `Raw (tw 2)` 上目标是 `tw 2` 自己的折叠, 在 `top` 处输出主干槽位上的保留结点, 它的各支与 "第 η 支的 `top` 的折叠" 有你写明的最弱的联系 (例如读回后相等, 或其中某个保留结点的层号在第 η 支里). 证明它推出 `SlotIrr` 一类的陈述, 或给出模型. 这一条回答 "那一行在这个块里写不写得出" 是不是定理.

**O3 替代行丢了什么.** 若那一行写不出, 构造路只能用不引用各支内部的替代 (只用 `top`, 主干槽位, 第 0 层的值能表达的树). 给出 `Raw (tw 2)` 里 "不引用任何一支的内部" 的树的刻画 (一个谓词), 证明它对加法封闭; 说明规范的 `top` 的保留像若存在则不在其中 (定理或判断, 标明). 这一条给 "替代行之后闭项的读法还剩多少" 提供依据; 不要求给出序数.

**O4 壁垒在哪.** 目标在某一支 η 里层号 ≥ 1 的位置上, 树是 `top`. 这时 `top` 的根在目标之下, 要保留, 它的第 η″ 支对一切 η″ 都要折到那个目标层. 写成最小记录, 检验它推出哪条全知原理 (LPO, WLPO 或别的). 逐条核机制: 陈述里有没有折叠, 失败的是哪个字段; 它与 `no-compare-tw2`, `dec-at→lpo` 是不是同一机制; 是不是壁垒定理的实例 (核对 `Barrier` 的前提). 再回答: `Ω₁⁺` 的规范的链需要这一种吗 (走一遍: 起点 `top`, 推进用目标 `tw 2` 自己; 哪些结点的自己那一层在某一支里)? 没有判定就写没有判定.

**O5 块的变体 (给作者的裁决探路, 不是成果).** 若 O1, O2 说明障碍来自 "位置与孩子带相关守卫, 分支带无关守卫" 这一写法: 在你的临时目录里用纯 `.agda` 试最小的变体, 交编译事实, 不进仓库:
- 变体甲: 位置与孩子的守卫改成无关 (`Pre`, `Kid` 的 `lc` 子句). 能否过检查器; `up`, `Ω̂`, `tw` 能否照搬; 这时 `SlotIrr`, `KidIrr` 是否平凡成立; 但比较要的 `Legal (read0 η)` 从哪里来 (上一步的 `compare` 读相关的合法性), 是否因此又推出搜索.
- 变体乙: ℕ 极限自带相邻第一位置的路径 (像 `src/OCF/BTBO.lagda.md` 的 `lim f mono`), 使比较要的数据在树里, 守卫可以处处无关. 归纳—递归的定义能否过正性与停机检查 (最小骨架即可); 上一轮被否定的 "把合法性的证明当普通参数放进结点" (`YiIntrCheck.tw₃-not-root-irr`) 在这个变体里是否重现.
把 "哪些已有定理在变体里会不成立" 列出来 (判断即可, 标明). 这一条只做到能给出编译事实为止, 不要展开成新块.

**O6 挑战.** 主审认为第一个障碍来自块的写法, 壁垒在 O4. 找反例或支持.

做不完不要紧: O1, O2, O4 是主要的. 每条定理写清它否定的是哪一种写法, 不否定什么; 反例对象是否在读回域内; 前提的实例. 不把 `IrrSearch`, `IrrDecide`, LPO, WLPO 说成矛盾.

### 3 规则

- **只新建文件**, 前缀 `YiOmNeg`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 `YiOmIf`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另四路用前缀 `YiOmFold` (构造路), `YiPsum`, `YiRawVal`, `YiLvAll`, 不要动它们的文件, 也不要依赖它们. 对共用接口的增补写在你自己的文件里, 并在回报里说.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 所在文件文首标 "条件".
- 否定结果写成编译过的定理; 有限样本的测试标为测试. 没有编译定理的地方只写 "未走通" 或 "没写成". 每个否定定理与条件定理的前提给一个实例或说明为何可满足.
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件; 编译表不进文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径).
- 你的临时目录: `<实验目录>/agents/omneg`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 通过; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 一段话, 先说对纲领与目标意味着什么: 第一个障碍是块的写法造成的还是壁垒; 壁垒在哪; 规范的链是否碰到它 (定理, 判断或没有判定, 分开说).
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表, 按 O1 到 O6: 名字, 一句白话, 文件, 档. 每条否定写: 否定的是哪一种写法; 反例对象是否在读回域内; 前提的实例.
4. 正面结果单列.
5. 临时目录里的试验 (O5): 变体, 编译事实, 会不成立的已有定理. 单列, 标明不是成果.
6. 没写成的条目与第一个障碍 (检查器报错原文, 缺的引理的 Agda 类型).
7. 偏离与事故.

## 回报原文

### 乙线第 4 步第一站, 否定路 (`YiOmNeg*`) 回报

#### 1 判决

**对纲领与目标.** 第一个障碍 (保留模式下 `top : Raw (tw 2)` 的那一行) 是块的写法造成的, 不是壁垒; 壁垒型的障碍在 "目标落在某一支里, 树是 `top`" 这一行, 与守卫相关还是无关没有关系. 规范的链是否碰到后者没有判定. 分三档说:

- **定理.** `SlotIrr`, `KidIrr` 与最小记录 `TopKeep` 各自推出同一条 `LegalCopy`, 因而推出 `IrrSearch` 与 `IrrDecide`. 这些不是矛盾: 在排中律的实例 `GdDec` 下三者都有模型, 守卫相关时都直接成立.
- **定理.** 最小记录 `TopBranch` 推出 LPO. 它只用保留律, 不用折叠律; 律只对 `Link` 相连的位置对要求时结论不变. 探针的守卫全是闭的相关证明. 所以上一轮定的 "律的定义域取 `Link`" 对这一行不够.
- **条件定理.** 单个闭目标上 (`FixedBranch`), 在第 0 层序列的函数外延 `FunextR` 下得 WLPO. 去掉这个前提后推出什么, 没有判定.
- **编译事实 (临时目录, 不是成果).** 变体甲与变体乙都过检查器, 两条接口陈述在其中按定义成立. 甲把同一原则挪到同支比较上: 那条比较陈述在当前的块上写出后推出 `IrrDecide` (定理 `branch-compare→irr-decide`). 乙的骨架里同支比较无条件成立. 所以 "改块能解决" 只对乙成立, 而且只到骨架级.
- **判断 (走查, 无定理).** 若 `Φ(top)` 取保留的写法, 第二个链点 `ξ₁ = top + Φ(top)` 折到第 0 层时就会问到 "目标在一支里, 被折的树里有叶 `top`". 取替代行 (链留在主干片段里) 时不会问到, 代价见 O3.

#### 2 文件表

都在 `<仓库>/probes/OCF/Align/`. 五个文件删自己的接口后冷编译 (6G 上限) 退出码都是 0; `importclosure.py OCF.Align.<模块>` 五个都是 "禁用表命中 0, OK"; 禁用构造检索为 0. 行数是代码块内非空行 / 文件总行.

| 文件 | 代码行 / 总行 | 冷编译 |
|---|---|---|
| `YiOmNegSlot.lagda.md` | 247 / 350 | 0 |
| `YiOmNegTop.lagda.md` | 59 / 104 | 0 |
| `YiOmNegTrunk.lagda.md` | 111 / 162 | 0 |
| `YiOmNegBranch.lagda.md` | 79 / 152 | 0 |
| `YiOmNegBranchFixed.lagda.md` (条件, 前提 `FunextR`) | 100 / 151 | 0 |

依赖序: `Slot`, `Top`, 然后 `Trunk` 与 `Branch`; `BranchFixed` 独立.

#### 3 定理表

##### O1 (`YiOmNegSlot`)

| 名字 | 白话 | 档 |
|---|---|---|
| `lev-legal₂` | `tw 2` 每个位置上的层号都相关地合法 (支里的位置带相关守卫) | 定理 |
| `slot→copy`, `kid→copy` | `SlotIrr`, `KidIrr` 各推出 `LegalCopy` | 定理 |
| `node₂-copy`, `plain-copy` | `Raw (tw 2)` 的树无关地读回成层号 L 的结点, 就相关地交出 L 的合法拷贝 | 定理 |
| `copy→irr-search`, `slot-irr→irr-search`, `kid-irr→irr-search` | 推出 `IrrSearch` | 定理 |
| `copy→irr-decide`, `slot-irr→irr-decide`, `kid-irr→irr-decide` | 推出 `IrrDecide` | 定理 |
| `dec→data`, `data→slot-irr`, `data→kid-irr` | `GdDec` 给出 `GdData`, 再给出两条陈述 | 定理 (模型) |
| `branch-compare→irr-search`, `branch-compare→irr-decide` | 位置守卫无关时的同支比较 `BranchCompareIrr` 推出同样的原则 | 定理 |

`LegalCopy` 是: 坐标 `suc s` 的守卫只无关地成立时, 交出一棵相关合法的层号树, 它无关地等于 `read0 s`.

- **否定的写法.** 在当前的块里无条件地从无关的守卫交出槽位或嵌入. 不否定守卫相关时的 `slot-rel`, `kid-rel`.
- **谁强.** 没有判定. `SlotIrr` 交出相关的层号方程, `KidIrr` 只交出无关的; 公共下界 `LegalCopy`, 公共上界 `GdData`.
- **读回域.** 探针是 `suc (coordᴺ α)` 与 `suc (coordᴰ γ)`, 在 `tw 3` 根上的分支域里, 守卫只无关地成立. 是不是规范的链走到的坐标, 没有判定.
- **前提实例.** `α = always` 时守卫有闭证明, 槽位直接写出 (`closed-slot`).
- 主审猜的引理形状是对的: 证明走 "那一支的合法性加层号相等". 层号相等只无关地知道时, 沿路径的构造子取下标, 再用布尔相等可判定 (`bool-irr`) 变回相关的.

##### O2 (`YiOmNegTop`)

| 名字 | 白话 | 档 |
|---|---|---|
| `TopKeep` | 记录: `Φ top ≡ G.lc root₂ raw1 t g`; `g (suc s) e` 带嵌套证据且读回是层号 `read0 s` 的结点 | 定义 |
| `top-keep→copy`, `top-keep→irr-search`, `top-keep→irr-decide` | 记录推出 `LegalCopy`, `IrrSearch`, `IrrDecide` | 定理 |
| `kept→reads`, `kid→reads` | 这条联系被 "槽位上的保留结点" 与 "整支的嵌入" 两种更强的写法推出 | 定理 |
| `data→top-keep`, `dec→top-keep` | 记录在 `GdData` / `GdDec` 下有模型 | 定理 (模型) |
| `rel-branch-node`, `slot-node₂-reads` | 分支拿相关守卫时联系无条件成立; 坐标 2 处槽位形式的闭实例 | 定理 (前提实例) |

- **否定的写法.** 在这个块里无条件写出保留形式的那一行, 这是定理. 不否定守卫相关的写法与替代行.
- **读回域.** 同 O1; 联系对相关守卫陈述, 在闭坐标上可满足.

##### O3 (`YiOmNegTrunk`)

| 名字 | 白话 | 档 |
|---|---|---|
| `Trunk` | 谓词: 结点只在 `root₂`, `first₂` 上, 嵌入只来自层号 0 与第一支 | 定义 |
| `trunk-plus` | 对已有的 `YiLvFoldAdd.plus (tw 2)` 封闭 | 定理 |
| `trunk-own-zero` | `Trunk` 的结点的槽位层号都是 0 | 定理 |
| `trunk-read` | `Trunk` 的树读回只含层号 0 的结点与原子 `tw 3` (`Sh`) | 定理 |
| `trunk-node-zero`, `no-trunk` | 满足 `TopKeep` 联系的 `top` 的像不在 `Trunk` 里 | 定理 |

- `no-trunk` 的见证是坐标 2, 闭的相关守卫. 它相对于 `TopKeep` 的联系, 不是相对于某个已写出的折叠.
- `trunk-plus` 对的是已有的 `plus`, 它在 Ω 层号的 `em` 与 `top` 上取固定值. 构造路自己的 `plusΩ` 要另证.
- **读法 (判断).** 链留在 `Trunk` 里时, 折到第 0 层除原子 `tw 3` 外只走第 0 层的链, 没有层号 ≥ 1 的结点, 到不了 ψ₀(Ω_{Ω₁+1}). 具体的界没有算.

##### O4 (`YiOmNegBranch`, `YiOmNegBranchFixed`)

| 名字 | 白话 | 档 |
|---|---|---|
| `TopBranch` | 记录: `branch q η .e : Raw (lev K₂ω q)`; `Link` 且 `At` 时 `branch q (suc s) e` 是 `Kept` | 定义 |
| `top-branch→lpo` | 记录推出 LPO | 定理 |
| `found→link`, `root-below` | 探针对在 `At` 成立时总相连; 目标层里总有层号 0 的位置 | 定理 |
| `oracle-branch` | `Locate` 下有模型 | 定理 (模型) |
| `at-one-dec` | 目标层是 1 时 `At` 可判定 | 定理 (正面) |
| `own-in-branch`, `plus-node`, `plus-leaf` | 走查用的编译事实: 层号非零的槽位必在某一支里; 加法把 `x` 放到零叶上 | 定理 |
| `fixed→wlpo` | 单个闭目标 `q_f` (第 `ω′+2` 支的根) 上, 保留律加折叠律 (`Link` 域), 在 `FunextR` 下得 WLPO | 条件定理 |
| `oracle-fixed` | `HitDec` 下 `FixedBranch` 有模型 | 定理 (模型) |

逐条核机制:

- **有没有折叠, 失败的字段.** 陈述里有折叠的一行 (分支的像与保留律), 没有值. 失败的是保留律要交出的槽位.
- **与 `dec-at→lpo`, `bare-way→lpo`.** 同一机制: 判定层号 1 是否在另一支的极限层号 `levelᴸ α` 的位置上. 这里判定由保留结点的头与槽位读出, 探针树是 `top` 自己在坐标 2 的那一支.
- **与 `no-compare-tw2`.** 不是同一机制. 那里位置对不相连, `Tri` 无居留. 这里相连, 比较本身成立; 拿不到的是 "相连与否" 这一位.
- **与 `Barrier.barrier`.** 不是字面实例. 那里的前提是带精确嵌入, 顶元, 有界三歧的下标类型; 这里的前提是保留律, 没有由它构造那样的下标类型.
- **读回域.** `top-branch→lpo` 的目标族 `qα α` 与坐标 2 都带闭的相关守卫, 证明里没有无关参数的消去. 目标族是不是链点, 没有判定.
- **规范的链需要这一种吗.** 没有判定. 走查的判断见第 1 节; `at-one-dec` 说明最早的层号 1 的目标不碰墙. 墙是否只在目标层含极限层号的位置时出现, 没有证.

##### O5

见第 5 节.

##### O6 挑战

- **支持 "第一个障碍来自块的写法", 有一处修正.** 把守卫改成无关 (甲) 不解决, 只把搜索挪到同支比较. 要把合法性的数据放进树 (乙) 才在骨架级同时得到槽位与同支比较.
- **支持 "壁垒在 O4", 并加强.** 只要保留律就得 LPO; 定义域取 `Link` 不够.
- **两处保留.**
  1. 对规范的链的闭目标, 只有条件定理. 无条件的那条没写成.
  2. 墙是对 "派发完全" 说的. 闭项的值是否需要派发完全, 没有判定. 一个未验证的想法: Ω₁ 长的分支族的极限只看尾部.

#### 4 正面结果

- `lev-legal₂`, `node₂-copy`: 可直接导入的部件.
- `data→slot-irr`, `data→kid-irr`, `data→top-keep`: 守卫能变回相关时, 三条都成立.
- `rel-branch-node`, `kid→reads`, `kept→reads`: 保留形式的行在相关守卫下的两种写法都满足联系.
- `trunk-plus`, `trunk-read`, `trunk-own-zero`: 主干片段的封闭与读回刻画.
- `at-one-dec`: 目标层 1 上保留判定无需神谕.

#### 5 临时目录里的试验 (O5; 不是成果, 没进仓库)

目录 `<实验目录>/agents/omneg/`. 纯 `.agda`, 同目录的 `omneg.agda-lib` 带仓库的选项. 在该目录下 `agda +RTS -M6G -RTS --library-file=<libraries> <文件>`, 两个都退出码 0.

**变体甲** `<实验目录>/agents/omneg/VariantA.agda` (326 行, 由同目录 `genA.py` 从 `RR5IrrCore` 与 `RR5IrrCheck` §1 的代码块改写).

- 改动: `Pre` 与 `Kid` 的 `lc` 子句里守卫放进带无关字段的记录; `DnBr` 改成对坐标的相等.
- 编译事实: 归纳—递归块过正性与停机; `up`, `upT`, `Ω̂`, `tw`, `Λ` 照搬; `tw₃-form` 是 `refl`.
- `slot-irr`, `kid-irr`, `kid-irr-read` 按定义成立.
- `top-node-read`: `top` 写成根位置的结点 (分支是整支的嵌入, 守卫无关), 读回是 `tw 3`, `refl`.
- 比较要的 `Legal (read0 η)` 拿不到: 支里的位置只带无关守卫. 同支比较的陈述就是 `BranchCompareIrr`, 它推出 `IrrDecide` (仓库里的定理).
- 会不成立的已有定理 (判断): `YiRawNegOmega` 的 `compare-up`, `compare-zero`, `compare-link` 的分支情形, `compare-same-branch`; 本轮的 `lev-legal₂`; 一切从位置的守卫里取 `Lgl zero η` 或 `1 ⊲ η` 作数据的引理.
- 仍成立 (判断): `no-compare-tw2`, `dec-at→lpo`, `keep-fold→wlpo`, 本轮的 `top-branch→lpo`, 因为它们用闭守卫.

**变体乙** `<实验目录>/agents/omneg/VariantB.agda` (约 380 行, 手写的最小骨架).

- 写法: `G.R` 与 `LF` 的 `lim` 都带相邻项的路径; 守卫只剩路径, 处处无关; 位置与孩子同甲.
- 没放进来: 结点的合法性 (`Lgl` 的 `lc` 子句), `Nested`, 折叠, `Legal` 的闭包.
- 编译事实:
  1. 块过正性与停机. `G` 模块多两个参数, 模块内 `R` 与路径关系归纳—递归.
  2. `up`, `upT`, `tw` 写得出, 但要与读回的单调性 (`up-cp`, `upT-cp` 等) 互递归.
  3. `all-root-irr` 是 `refl`: `YiIntrCheck.tw₃-not-root-irr` 不重现, 分支不依赖守卫证明.
  4. 重现的是另一种: 同一个序列两份路径给出两棵不同的树 (`two-differ`). ℕ 极限上 "换证明不换树" 不再成立.
  5. `slot-irr` 按定义成立.
  6. `compare` 对 `Plain` 层号不要外部合法性; `branch-compare` 对一切第 0 层坐标成立, 不要守卫.
- 没解决的 (判断): 主干位置与支里位置的三路仍要 `1 ⊲ η` 作数据, 目标在支里时它是 O4 的一部分; `top-branch→lpo` 预计原样成立.
- 会不成立或要重写的 (判断):
  - 以 `Lgl`/`Legal` 的极限子句为外部数据的定理 (`read0-legal`, `CohP`, `restrictL` 一类) 改成读树.
  - 行的右边要带路径, 单调性引理 (`add-cp`, `Ψ-cp`, `copies-step`, `psum-step`) 要并进定义.
  - 以 "合法性只无关成立的坐标" 为探针的否定 (`YiIrrNegWide`, `YiLvNegCompare` §1–2, 本轮 O1/O2) 不再能陈述: 探针坐标造不出来.
  - `evidence-irrelevant` 一类对 ℕ 极限不成立.

#### 6 没写成的条目与第一个障碍

1. **`SlotIrr` 与 `KidIrr` 之间的蕴涵.** `KidIrr → SlotIrr` 没写成: 要 `.(lev K₂ω q ≡ lev (read0 η) r) → lev K₂ω q ≡ lev (read0 η) r`, 层号树的相等不可判定 (`EqIrr` 一类). `SlotIrr → KidIrr` 没有尝试; 判断是结点处读回相等是分支函数的相等, 要函数外延.
2. **`LegalCopy` 的逆向** (推回 `SlotIrr`, `KidIrr`, `TopKeep`), 以及 `IrrDecide → LegalCopy`: 没有尝试.
3. **O4 对单个闭目标的无条件定理.** 缺 `(∀ n → α n ≡ false) → betaᴰ (seen α) ≡ onesᴰ`, 不借函数外延得不到.
4. **规范的链是否走到 O4.** 只有走查. 构造路的折叠只在主干片段上, 没有保留形式的 `Φ` 可以代入.
5. **`TopBranch` 没有写 "保留结点怎样装进输出".** 那要沿 `lev L s ≡ zero` 搬运 `Low L s` 与 `GdL`. 记录只含分支与保留律, 定理因此更强.
6. **O3 的读法没有界**; "`Φ` 保持 `Trunk`" 没有证.
7. **由 `TopBranch` 构造 `Barrier.Ω-Extension`:** 没有尝试.

没有检查器拒绝后放弃的写法; 上面都是没有尝试或缺引理.

#### 7 偏离与事故

- **超出简报的增补.** `YiOmNegBranchFixed` (O4 的单个闭目标, 条件定理) 与 `YiOmNegSlot` §7 (变体甲的后果在当前块上的陈述) 是我加的.
- **对共用接口的增补, 都在我自己的文件里.** `Copy`, `LegalCopy`, `NodeAt`, `GdData`, `GdDec`, `BranchCompareIrr` (`YiOmNegSlot`); `ReadsNode`, `TopKeep` (`YiOmNegTop`); `Trunk`, `Sh` (`YiOmNegTrunk`); `TopBranch` (`YiOmNegBranch`); `FunextR`, `Hit`, `FixedBranch`, `HitDec` (`YiOmNegBranchFixed`). `YiOmIf` 没有动.
- **读了构造路的文件.** 结束前只读了 `YiOmFoldBase`, `YiOmFold`, `YiOmFoldTop` 的文首与签名表, 没有导入. 它们用替代行 (`topᴬ`, `topˢ`) 与主干片段 `Tr`, 自己证了 `plus-tr`, `Φˢ-tr`. 我的 `Trunk` 与它们的 `Tr` 是否同一个谓词, 没有核对.
- **Funext.** 只以 `FunextR` (限于 `ℕ → Raw zero`) 作显式前提出现在 `YiOmNegBranchFixed`, 文首标了条件.
- **编译.** 三次类型错误, 都已修: 记录字段名与 `Tri` 的构造子 `same` 撞名; `suc zero ≡ zero` 的 ℕ/LF 歧义; 一次改稿后的模型字段. 没有堆耗尽. 每次只跑一个 agda, 没用 `--ignore-interfaces`. 删接口用字面路径, 只删自己的五个.
- **没有做的.** 没有提交, 推送, `pkill`, 装包; 没有写临时目录之外的 `/tmp`; 没有改任何已有文件. 临时目录里有 agda 生成的 `_build`.
- **文字预算.** 各文件文首 3 行. `YiOmNegBranch` 末尾有约 8 行的 "范围与归类", 是简报要求的逐条核机制.

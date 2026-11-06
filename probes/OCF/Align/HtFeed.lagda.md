# 高度是树: 一个折叠对一切高度, 回灌选出用到的高度

> 主线第 3 步 (摆脱侧). 入口. **判决: PARTIAL.** 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 没有 `cumA`, ⊞, u+. 定义不读记号, 没有验收文件.
>
> 一句话: 层不再是坐标 $(p,a)$, $(r,p,a)$, 而是**一棵高度树** $L:H$ (第二数类的布劳威尔树, $\Omega$-极限的分支存在数据里, 第一位置按世界分开). 节点种类、分支类型、良基都对 $L$ 结构递归, 比较是一次 `cmpH`, 没有字典序, 没有顶层. 一个折叠、一个闭项定义 `TΛ` 对一切合法高度; `SumClimb` 在 $\Omega^\omega$ 的停机障碍不再出现 ($\Omega^\omega$, $\Omega^\Omega$, $\Omega^{\Omega^k}$, $\Omega^{\Omega^\omega}$ 都有闭项). $\Omega$-极限的层 $\mathrm{h\Omega}\,g$ 折叠到第 0 层时, 用到的高度 $g(c)$ 的坐标 $c$ 是折叠的输出经 `sum` 读回 (`feed`). 一条增长定理 (`Sup`) 对一切最高层与一切节点族成立, 不按站写. 三条否定定理划出高度的哪些字段是比较逼出的.
>
> **没有做到的:** 高度树本身不是折叠的输出; 它由三条布劳威尔树的生成规则写出 (`HtFeedHt`), 回灌只选 $\Omega$-分支的坐标. 把第 1 层的输出读成高度要分支对坐标的一切第一位置单调, 差树的读法只给后继步进 (`no-weak`), 这一步未走通. 强度的读法都是判断, 第 4 层没有做.

## 设计

| 件 | 定义 | 文件 |
|---|---|---|
| 高度 | `data H = hz \| hs H \| hl (ℕ → H) \| hΩ (A → H)` | [HtFeedTree](HtFeedTree.lagda.md) |
| 第一位置 | `a ⊲[ W ] b`; 进 `hΩ g` 的分支 $c$ 要 $c\lhd W$ | 同上 |
| 合法 | `LgH`: ℕ-极限相邻项是第一位置 (世界 $0$); `hΩ g`: $c\lhd c'$ 则 $g\,c\lhd_{[c']}g\,c'$; 遗传 | 同上 |
| 比较 | `cmpH`: 同一棵合法高度在同一世界里的两个第一位置可比; $\Omega$-分支处先 `cmpF` 比坐标, 再用单调搬 | 同上 |
| 层的节点 | `StH W k L`: `ss`, `sl`, `sL` 三种, 对应 $L$ 的三个非零构造子 | 同上 |
| 数据树 | `D₊` 与 `SumOne`, `SumHt` 相同; `D L` 的分支类型对 $L$ 结构递归 | 同上 |
| $\Omega_L$ | `Ωd`: 只看 $L$ 的最外构造子; $\Omega_{\mathrm{h\Omega}\,g}=1+\sum_{c\ge W}\sum_{z:g\,c}1$ | 同上 |
| 合法性 | `sum-fst`, `Lg-sum` (第 0 层的和), 无前提, 不提折叠 | 同上 |
| 折叠 | `SumHtFold` 逐个改写; 模块参数 $\Lambda$ (最高的层); 目标 `Tg W t m`: $t\lhd_{[m]}\Lambda$; `rkT` 是一次 `cmpH` | [HtFeedFold](HtFeedFold.lagda.md) |
| 闭项 | `TΛ Λ lΛ`, 一切合法 $\Lambda$; 合法性是 `Lg-sum` 的一次调用 | [HtFeedClosed](HtFeedClosed.lagda.md) |
| 高度的生成 | `Ωit F x = hΩ (c ↦ F^c (F x))`; `Hier T F c`; `ΩD G = x ↦ hΩ (c ↦ G c x)`; `upT T F = ΩD (Hier T (T F))`; ℕ-对角 `Upω`, `Tω` | [HtFeedHt](HtFeedHt.lagda.md) |

**为什么停机直接过.** `SumClimb` 在 $\Omega^\omega$ 卡住, 是因为层是位数可变的坐标列表, 字典序的下降可以落在任何一位, 停机检查看不见. 这里层的节点种类 `StH W k L` 是 $L$ 的一条第一位置路径, 分支类型 `Vs`, `Vc` 与良基 `accL` 都对 $L$ 结构递归, 节点的层总是 $L$ 的结构子项 (`hΩ g` 的子项是一切 $g\,c$). 不用可达性证明作下标.

**与壁垒.** `H` 有一个在一切可数高度之上的元素 `Ωᴴ` (`top-Ω`), 但第一位置按世界分开: 在任何一个世界里, $\Omega$ 之下的可数高度都不超过这个世界 (`world-bound`), 没有一个世界让一切可数高度都在 $\Omega$ 之下 (`no-world-top`). 比较只在一个世界之内 (`cmpH`); 世界各自取就不可比 (`no-glob`). 所以 `Barrier` 的三条假设 (精确初始段, $\Omega$-共尾元, 有界三歧) 在任何一个世界里不同时成立. 这是判断与上面三条定理的合读, 没有一条定理直接说 "这个设计不推出 LPO".

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `cmpH` | HtFeedTree | 合法高度在一个世界里的两个第一位置可比 | 定理 (构造) |
| `accL`, `accᴸ` | HtFeedTree | 层良基, 对一切高度 | 定理 |
| `sum-fst`, `Lg-sum` | HtFeedTree | 第 0 层的和保第一位置, 合法 | 定理, 无前提 |
| `Run` 一族 | HtFeedFold | 折叠, 对一切合法 $\Lambda$ | 定义 |
| `TΛ`, `Lg-TΛ` | HtFeedClosed | $\psi_0(\Omega_\Lambda)$ 的闭项, 一切合法 $\Lambda$ | 定义; 合法性是定理 |
| `T-Ω`, `T-Ω+1`, `T-Ω·2`, `T-Ωk`, `T-Ωω`, `T-ΩΩ`, `T-ΩΩk`, `T-ΩΩω`, `fgh` | HtFeedClosed | 闭项, 无参数 | 定义 |
| `Good-Ωit`, `Good-Hier`, `upT`, `Good-Upω`, `Good-Tω`, `l-…` | HtFeedHt | 生成规则保合法, 往上走; 一切生成的高度合法 | 定理 |
| `feed₀`, `feed` | HtFeedGrow | `nκ` 回灌的第 $n$ 格的世界是 $v_{n+1}=v_n+\Delta_n$ | 定理 (`refl`) |
| `L1`, `L2`, `L3`, `L4` | HtFeedGrow | 前缀是部分和; 节点非零; 回灌第一格非零; 对一切 $\Lambda$ 与节点族 | 定理 |
| `pre<`, `pre≤s`, `s<κ` | HtFeedGrow | 前缀站严格增长; 在 ℕ-极限之下; 闭包站严格在 ℕ-极限之上 | 定理 |
| **`Sup`** | HtFeedGrow | 对一切 $\Lambda$, 一切节点族 $r,\rho$, 一切 $\sigma:\mathbb N\to\mathbb N$: `asuc (sup_k T (Xn (σ k))) ≤ T Xκ` | 定理 |
| **`ΩSup`** | HtFeedGrow | 上式在 $\Lambda=\mathrm{h\Omega}\,g$, $r_j=g(j)$, $\rho_c=g(c)$; 一切 $g$ | 定理 |
| `Sup-Ω`, `Sup-Ω·2`, `Sup-ΩΩk` | HtFeedGrow | `ΩSup` 代入生成的高度 | 定理 |
| `top-Ω`, `world-bound`, **`no-world-top`** | HtFeedNeg | $\Omega$ 在一切可数高度之上, 但没有一个世界里是 | 定理; 否定 |
| `no-common`, **`no-glob`** | HtFeedNeg | 世界各自取的两个第一位置不可比 (前提有见证) | 否定, 定理 |
| **`no-weak`** | HtFeedNeg | $\Omega$-单调只要后继步进时, 有一棵弱合法高度在世界 $\omega$ 里有两个不可比的第一位置 | 否定, 定理 |
| `a6`, `b6`, `c4`, `d3`, `d4`, `e4` | HtFeedTest | 见下 | 有限测试 |

**`Sup` 说什么, 不说什么.** 前缀站都在 ℕ-部分和的极限之下 (字面的部分和), 闭包节点在其后的回灌输出非零. 所以闭包站严格高于前缀站的任意可数子族的上确界. 这与 `SumClimbGrow.SupN`, `SupR`, `Sup3` 同一档, 不说闭包站高于前一族的某个闭包点 (那要折叠对世界单调). 新的是: **一条定理, 对一切最高层、一切节点族、一切 $\Omega$-极限的高度**; `SumClimb` 那里每一级各写一条 (`SupN`, `SupR`, `Sup3`), 每一级的坐标不同.

**`no-glob`, `no-weak` 否定的形状.** `no-glob`: 前提 "两个第一位置, 世界各自取" 有见证 (`emb ω` 在世界 $\omega$ 里, `emb ω′` 在世界 $\omega'$ 里, 都在 `Ωᴴ` 之下, `Ωᴴ` 合法); 否定的是这种比较存在. `no-weak`: 弱合法 `LgW` 有实例 (`lgW-x`), 世界 $\omega$ 合法; 否定的是弱合法的高度上有比较. 两条都只否定写明的形状, 不否定别的高度类型.

## 闭项与读法

| 闭项 | 高度 | 读法 (判断) |
|---|---|---|
| `T-Ω` | `Ωᴴ` | $\psi_0(\Omega_\Omega)$; 与 `SumOne.T₀` 到深度 6 形状相同 (测试) |
| `T-Ω+1` | `hs Ωᴴ` | $\psi_0(\Omega_{\Omega+1})$ |
| `T-Ω·2` | `Ωit hs Ωᴴ` | $\psi_0(\Omega_{\Omega\cdot2})$ |
| `T-Ωk k` | `Up k hz` | $\psi_0(\Omega_{\Omega^k})$ |
| `T-Ωω` | `Upω hz` | $\psi_0(\Omega_{\Omega^\omega})$: `SumClimb` 的第一个障碍那一站 |
| `T-ΩΩ` | `T (Tk 1) hs hz` | $\psi_0(\Omega_{\Omega^\Omega})$ |
| `T-ΩΩk k` | `T (Tk k) hs hz` | $\psi_0(\Omega_{\Omega^{\Omega^k}})$ |
| `T-ΩΩω` | `Tω hs hz` | $\psi_0(\Omega_{\Omega^{\Omega^\omega}})$ |

读法的依据 (纸面): 把 `hΩ g` 读作 $\sup_{c<\Omega}g(c)$, 按布劳威尔树的算术, `Ωit F x` 读 $\sup_c F^c(Fx)$, 所以 `Up k x` 读 $x+\Omega^k$; `Tk 1` 把 $x\mapsto x+\Omega^\alpha$ 变成 $x\mapsto x+\Omega^{\alpha+\Omega}$, 一般 `Tk k` 加 $\Omega^k$. 这一节没有任何一条是定理: 没有树与对照树之间的 $\preccurlyeq$, 也没有闭项之间跨高度的比较 (见第一个障碍). 按读法, `T-ΩΩω` 远高于 `SumClimb` 的 `T³` ($\psi_0(\Omega_{\Omega^3})$); 这也是判断.

**有限测试** ([HtFeedTest](HtFeedTest.lagda.md), `same d w`, 宽 2):

| 比较 | 结果 |
|---|---|
| `T-Ω` 对 `SumOne.T₀` (同读 $\psi_0(\Omega_\Omega)$, 输入同形) | 到深度 6 相同 |
| `ΩSt emb` 的 `Xκ` 对 `SumHt.T 1 0` (积木同形) | 到深度 6 相同 |
| `ΩSt emb` 的 `Xn 2` 对 `SumHt.T 0 2` | 到深度 4 相同 |
| `T-Ω+1` 对 `T-Ω`; `T-Ω·2` 对 `T-Ω+1` (对照) | 深度 3 相同, 深度 4 不同 |

前两行说明改写在共有的那一站上与旧折叠形状一致, 不说明值. 对照行说明深度 3 没有分辨力, 深度 4 有.

## 第一个障碍

1. **跨高度的比较.** 每个 `TΛ` 在自己的折叠实例里 ($\Lambda$ 是模块参数, 目标的上界). 要比 `TΛ h` 与 `TΛ h′` ($h\lhd h'$), 要一条换实例的引理: 在实例 $h'$ 里折叠层 $h$ 的输入, 与在实例 $h$ 里折叠, 输出相同. 两边的比较走的是不同的路径 ($k\lhd h$ 与 $k\lhd h\lhd h'$), `cmpH` 给出的保留节点带着不同的路径证据 (`StH` 是证明相关的), 所以输出最多是 "差一个路径选择" 的相同, 要一个不看路径的等价或值层的 $\approx$. 没有做, 判断它与第 4 层同类. 所以 `Sup` 只在一个实例内的站之间.
2. **高度是折叠的输出.** 要把第 1 层的输出 (`D (hs hz) W`) 读成 `H`: `ni` 的分支只在更大的世界上有, 读成 `hΩ` 要每个坐标 $c$ 选一个含它的世界; 合法性要分支对坐标的一切第一位置单调, 差树的读法只给后继步进 (`LayerTr` 的 `LgB`), 而 `no-weak` 说只有后继步进就不能比较. 判断: 要用 `BrwHigh` 的正规节点 (存增量, 坐标取差树, 沿前缀单调由 `⊞-fst` 白送), 并把 `H` 的 $\Omega$-分支改成差树坐标. 未走通, 没有否定定理.
3. **第 4 层.** 没有任何一站与对照树有 $\preccurlyeq$. 同 `SumHt`, `SumClimb`.

## 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 高度 `H` 的四个构造子 | 第二数类的布劳威尔树 (纲领第 1 条的树, 高一层); 构造子与 `Barrier` 的朴素 `Ord₁` 同类, 差别是单调证据放在 `LgH` 里, 序按世界分开 | 树侧, 不读记号 |
| $\Omega$-分支的坐标要在世界之下 (`hLim`) | 不这样就不可比 | **树逼的** (`no-glob`, 壁垒) |
| `LgH` 的 $\Omega$-单调沿坐标的一切第一位置 | `cmpH` 要把一边搬进另一边的分支 | **树逼的** (`no-weak`) |
| ℕ-极限的步进写在世界 $0$ 上 | 让一切世界都能用; 生成的高度都满足 | 选择 |
| 节点种类 `ss`, `sl`, `sL` | 由 `H` 的三个非零构造子机械给出 | 树侧; 取代 `SumHt` 的 `sm`/`lo`, `SumClimb` 的 `sm`/`lo`/`lr` |
| 比较 `rkT` 是一次 `cmpH` | 一切层都是 $\Lambda$ 的第一位置 | 树侧; **字典序消失** |
| 折叠以 $\Lambda$ 为模块参数, 目标 `Tg W t m` | 比较要字面公共上界 | 树逼的 (高度的上界); 世界 $m$ 沿用 `SumHt` |
| `mk` 要世界包含, 不要坐标的上界 | 节点种类带世界, 嵌进高层要把 $\Omega$-分支的坐标搬到新世界 | 树逼的 (判断; 没有试 `SumHtTree.Int` 的 `HK` 写法) |
| `Ωd` 只看最外构造子, $\Omega$-极限是 $\sum_{c\ge W}\sum_{z:g\,c}1$ | `SumOne` 的 `Ω̂₀`, `SumHt` 的 `stepH` | 形状受旧树影响 (沿用) |
| 折叠本体 (`Run` 一族), `S = ω⋅` | `SumHtFold` 逐个改写 | 形状受旧树影响 (同 README 翻译账 `SumHtTree`, `SumHtFold`) |
| 生成规则 `Ωit`, `Hier`, `ΩD`, `upT`, ℕ-对角 | 布劳威尔树的迭代与对角 | 树侧; 读法 $\Omega^k$, $\Omega^\Omega$ 是算术读法 (判断) |
| `Ωit` 从 $F\,x$ 起, `upT` 从 $T\,F$ 起 | 第 0 支就是上一级, 世界 $0$ 上的第一位置, 让 ℕ-对角合法 | 树逼的 (`LgH` 的 ℕ-步进在世界 $0$) |
| 站的积木 (ℕ-段 + 世界上的闭包) | 同 `SumHtClosed` 的 `B n` | 选择; 与 `Ωd` 同值是判断 |

**按 `AGENTS.md` 归类: 提供信息; 摆脱翻译的一步, 部分.**
- 加深的三个标志: 新构造子或节点字段读自基本列规则: **没有** (`D₊` 不变; `H` 是布劳威尔树; 节点种类由 `H` 机械给出, 每升一级不加种类). 闭包定理新增专属前提: **没有** (`Lg-sum` 无前提; `Sup` 对一切 $\Lambda$ 与节点族). 只能用 `Lab` 验收: **不是** (没有 `Lab`).
- 提供信息的三个标志: 对结构参数的一步定理: **有** (`Sup` 对 $(\Lambda,r,\rho)$, `ΩSup` 对 $g$; 新用到的字段是 `hΩ` 的分支, 经 `sL` 与世界上的 `nκ`). 序数值验收与基本列的差: **没有**. 否定定理划出不能有的字段: **有** (`no-glob`: 世界必须共用; `no-weak`: 单调不能只在后继处; `no-world-top`: 顶只在 Kripke 意义下).
- 摆脱了什么: "每升一级加一维" (README 翻译账 `SumClimbTree` 那一行) 与字典序. `SumHt` 的 $(p,a)$, `SumClimb` 的 $(r,p,a)$ 照 $\Omega\cdot p+a$, $\Omega^2 r+\Omega p+a$ 写; 这里没有坐标, 高度就是树. 没摆脱的: 折叠的形状 (沿用 `SumHtFold`), 和 "高度是给定的数据" 这一点 (见第一个障碍 2).

## 账

**定义级切片** (口径同 `locslice_l12.py`, `sumht/locslice_climb.py`: 计 agda 非空非注释行, 记号模块除外; 脚本在临时目录 `htfeed/locslice_htfeed.py`, 读 `agda --html` 的输出).

| 路线 | 层 1 (类型) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加增长 |
|---|---|---|---|---|
| SumHt, 到 $\Omega^2$ | 75 | 628 (去共用 545) | 645 (去共用 562) | 865 (净增 220) |
| SumClimb, 到 $\Omega^3$ | 84 | 700 (去共用 617) | 721 (去共用 638) | 1005 (净增 284) |
| **HtFeed, 一切高度; 闭项到 $\Omega^{\Omega^\omega}$** | 51 | 661 (去共用 578) | 665 (去共用 582) | 892 (净增 227) |

- 层 2 按模块: HtFeedTree 220, HtFeedFold 167, HtFeedHt 121, Free.Level 56, CumReadCF 36, HtFeedClosed 34, BTBO 27. 其中 `HtFeedHt` 的 121 行是高度的生成规则与合法性: **高度的合法性在层 2**, 因为折叠要它 (`cmpH` 读 `LgH`), 闭项 `TΛ Λ lΛ` 带着它. 这与 `SumOne` 回灌的层要 `Lg-sum` 同理.
- 层 3 只多 4 行 (`Lg-TΛ` 是 `Lg-sum` 的一次调用).
- 增长净增 227 行 (HtFeedGrow 203, TLRuleSpec 24), 对一切高度一次写完; `SumClimb` 到 $\Omega^3$ 净增 284 行, 每级各写.
- 与 `SumClimb` 比: 层 2 少 39 行, 覆盖 $\Omega^\omega$ 以上 (按读法); 每升一级 `SumClimb` 约加 72 行, 这里加一级只加生成规则 (`upT` 一条对一切级).
- 否定 (独立切片) 227 行: HtFeedNeg 139, 其余是借用的序与路径.
- 文件级 (手数, 非空非注释): `HtFeedTree` 238, `HtFeedFold` 184, `HtFeedHt` 133, `HtFeedClosed` 51, `HtFeedGrow` 241, `HtFeedNeg` 174, `HtFeedTest` 23, 入口 5.

## 审计

- **导入闭包** (`importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRuleSum --only OCF.Align.SumOne --only OCF.Align.HtGen --only OCF.Align.HtFeed`): `HtFeed` (26 个模块, 本地 16), `HtFeedTree`, `HtFeedFold`, `HtFeedHt`, `HtFeedClosed`, `HtFeedGrow`, `HtFeedNeg` 都是退出码 0, 禁用表 0, `--only` 之外 0. `SumOne*`, `TLRuleSum` 进闭包是经 `HtGenGen` (`HtFeedNeg` 借 `lt-irr`) 与 `TLRuleSpec`. `HtFeedTest` 退出码 1: 禁用表 0, `--only` 之外 6 个 (`CumReadAccept`, `CumReadBase`, `CumReadTop`, `CumReadW`, `LevelFixCore`, `LevelFixVal`), 都经比较器 `CumUpAcceptF` 进来, 与 `HtGenTest` 同.
- **定义级切片** (`depslice.py`, 到达块 / 记号块 / 词命中): `HtFeedClosed:fgh` 172/0/0, `HtFeedClosed:TΛ` 113/0/0, `HtFeedClosed:Lg-TΛ` 115/0/0, `HtFeedFold:Run` 96/0/0, `HtFeedGrow:Sup-ΩΩk` 207/0/0, `HtFeedGrow:SupStmt` 133/0/0, `HtFeedNeg:no-weak` 36/0/0, `HtFeedNeg:no-glob` 33/0/0, `HtFeedNeg:no-world-top` 27/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发 (见翻译账与时间线).
- **禁用构造**: 八个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`; 都带 `--safe --without-K --lossy-unification`.
- **从头编译** (`--ignore-interfaces`): 入口退出码 0 (27 秒, 1.2G); `HtFeedTest` 退出码 0 (103 秒, 3.0G).

## 时间线

写定义前读过: `HtGen*`, `SumOne`, `SumOneTree`, `SumOneFold`, `SumOneClosed`, `SumHt`, `SumHtTree`, `SumHtFold`, `SumHtClosed`, `SumHtGrow`, `SumClimb`, `SumClimbGrow` 的陈述, `TLEnd`, `TLOpsW` 开头, `BrwHigh`, `BrwMid`, `LayerTr`, `LayerTrBase` 开头, `CumReadCF`, `Barrier` 的陈述. 没有打开 `EBO`, `Correspond`, `Label`, 也没有读任何基本列规则.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtFeed where

open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; LgH; cmpH; StH; D₊; D; accL; sum-fst; Lg-sum; Ωd) public
open import OCF.Align.HtFeedHt using (emb; Ωᴴ; Lg-Ωᴴ; Ωit; Good-Ωit; Hier; Good-Hier; ΩD; upT; Tk; Upω; Tω; Good-Upω; Good-Tω) public
open import OCF.Align.HtFeedClosed using (TΛ; Lg-TΛ; T-Ω; T-Ω+1; T-Ω·2; T-Ωk; T-Ωω; T-ΩΩ; T-ΩΩk; T-ΩΩω; fgh) public
open import OCF.Align.HtFeedGrow using (module G; module ΩSt; SupStmt; Sup-Ω; Sup-Ω·2; Sup-ΩΩk) public
open import OCF.Align.HtFeedNeg using (top-Ω; world-bound; no-world-top; no-common; GlobCmp; no-glob; LgW; WeakCmp; no-weak) public
```

# 和形式, 层取可变位数: 过 $\psi_0(\Omega_{\Omega^j})$ (一切 $j$), 到 $\psi_0(\Omega_{\Omega^\omega})$

> 入口. **判决: HOLDS (到 $\psi_0(\Omega_{\Omega^\omega})$, 读法是判断).** 一个定义, 层是任意位数的列表, 在 `--safe` 下过停机与正性检查; 合法性由形状给出 (`Lg-sum`, 无前提); 定义里没有 `HS`, `Goodᴺ`, `WF`, `ψW`, 没有证书参数; 闭项 `Tω` 无参数. 增长定理**对一切位数一条**: `SupBlk` (一切深度, 一切高位, 一切点) 取代三位时按维写的 `SupN`, `SupR`, `Sup3`; 落到命名的站上是 `SupSt`, `SupD`, `SupTop`, `SuccSt`, `RankUp`, 再加 `Tω` 恰是 `T⁰ j` 的极限 (`Tω≤sup`, `sup≤Tω`). 再往上 ($\Omega^\omega+1$ 起) 未走通, 没有否定定理.
>
> **上一轮的障碍怎么过的.** [SumClimb](SumClimb.lagda.md) 记录: 位数可变时 `D`, `VL` 停机失败; 改用可达性证明作下标, 类型依赖证明, "链的起点与节点分支的类型对不上". 这里两件事一起做 ([SumVarTree](SumVarTree.lagda.md)):
>
> 1. `D′ L ac` 对可达性证明 `ac : AccY (lay L)` 结构递归 (证明对象, 不是编译指示); 规范的 `D L` 的分支取 `accY L` 里的那一份.
> 2. 对不上的地方用**换证明的搬运**: `mapD` (只换分支的定义域, 对树结构递归), `fw`/`bw` (对证明结构递归), `toD`/`ofD`. 它们就是折叠里本来就有的 `outV`, `inV`; 三位时是沿 `◁` 的浅搬运, 这里是对整棵树的深搬运. 折叠 ([SumVarFold](SumVarFold.lagda.md)) 因此与 `SumClimbFold` 逐个对应, 一次编译通过.
>
> `AccY` 的证明 `accY` 对列表与首位结构递归 (`accC`, `accK`, `accS`), 补零相等的层可达性相同 (`accE`).
>
> 全文 `--safe --without-K --lossy-unification` (工程的 `.agda-lib` 另加 `--cubical-compatible`), 无公设, 无洞, 无停机或正性编译指示, 不开 K, 没有 `next`, `cumA`, ⊞, u+. 定义不读记号, 没有验收文件. 不改已有文件 (从 `SumHtTree` 只导入 `NZ`, `NZ◁`, `tailP` 与路径的两条算律).

## 改动

| 改动 | 文件 |
|---|---|
| 层 `Lay = List A`, 低位在前, `a ∷ L` 读 $\Omega\cdot L+a$; 补零相等 `EqP`, 非零 `NZL`, 各位界 `AllB` | [SumVarTree](SumVarTree.lagda.md) |
| 节点种类 `KL W L L′`: 三个构造子 `hd` (这一位严格低, 以上补零相等), `tl` (以上已经低了, 这一位在世界之下), `tz` (节点是空列表). 对一切位数一个定义, 不再每级多一种 | SumVarTree |
| 分支类型 `D′` 对可达性证明递归; `D` 取规范证明; 搬运 `mapD`, `fw`, `bw`, `toD`, `ofD` (= `outV`, `inV`) | SumVarTree |
| 节点种类的算律 `ktr` (= `mkOf`), `kkL` (= `kk`), `KLup`, `congL`, `congR`, `rebound`, `rehd`: 都对列表结构递归 | SumVarTree |
| $\Omega_L$: `Ωd` 对一切位数, 高位的步 `Up` 对列表递归, 节点由 `wk` 一层层包上 `tl _ 0` | SumVarTree |
| 目标 `Tg W L m`; 比较 `cmpL` 对两个列表同时递归 (先比高位, 相等再比这一位, 空列表按零读); 回灌在各位为零的目标上 (`RKz`, `drpZ`) | [SumVarFold](SumVarFold.lagda.md) |
| 积木 `nd`, `κ j ns`, `Blk j ns`, `Rj j`; 站 `X⁰ j`, `Xs j d ds`, `Xω` | [SumVarClosed](SumVarClosed.lagda.md) |
| 点 `Pt`, `adv`; `Inside`, `Close`, `SupBlk` 与命名站上的定理 | [SumVarGrow](SumVarGrow.lagda.md) |

折叠 `SumVarFold` 与 `SumClimbFold` 逐个对应; 差别只在目标的类型, 比较 (`cmpL` 代替 `rkT`/`rkH`/`rkI`), 回灌的判定 (`zdec` 代替按三位的七个子句).

## 站

都是顶层在世界 $\omega$ 上的输入的折叠. 积木 (三位时的 `nd r n m`, `B r n`, `BR r`, `κ3` 是 `Blk 0 [m,n,r]`, `Blk 1 [n,r]`, `Blk 2 [r]`, `κ 2 []`):

    Blk 0 ns     = nd ns                                     Σ_{z:ns} 1
    Blk (j+1) ns = nl (λ n → Blk j (n ∷ ns)) ⨾ κ j ns        κ j ns = Σ_{c≥ω} Σ_{z:(0,…,0,c,ns)} 1
    Rj j         = nl (λ n → Blk j [n+1]) ⨾ κ j []           Ω^j → Ω^{j+1}, 层有 j+1 位

    X⁰ j      = 1 ⨾ nd [] ⨾ Rj 0 ⨾ … ⨾ Rj (j-1)                                 Ω_{Ω^j}
    Xs j d ds = X⁰ j 的前缀 ⨾ Blk j [1] ⨾ … ⨾ Blk j [d] ⨾ Pr [d+1] ds           Ω_{Ω^j·(d+1)+Ω^{j-1}·ds₀+…+ds_{j-1}}
    Xω        = 1 ⨾ nd [] ⨾ nl Rj                                               Ω_{Ω^ω}

低于 $\Omega^j$ 的层用较短的列表 (`Rj j` 从 `[1]` 起), 层的位数在一个输入里混合, 比较按补零读. 另有 `TΩ L`: 一切合法层 (任意位数) 自己的 $\Omega$ 的折叠.

## 定理表

| 定理 | 文件 | 说的是什么 | 档 |
|---|---|---|---|
| `D′`, `D`, `accY`, `fw`, `bw`, `toD`, `ofD`, `mapD` | SumVarTree | 可变位数的层上的树; 停机由可达性证明的结构递归给出 | 定义 (编译过) |
| `Tω`, `T⁰`, `Ts`, `TΩ`, `Lg-Tω`, `Lg-T⁰`, `Lg-Ts`, `Lg-TΩ`, `fgh` | SumVarClosed | 闭项, 无参数; 合法性各是 `Lg-sum` 的一次调用 | 定义; 合法性是定理 |
| `L1`, `L1b`, `ptF≡pt`, `L1′`, `Next`, `InF` | SumVarGrow | 前缀的折叠是 `nl` 的部分和 | 定理 |
| `L2`, `L3`, `Succ` | SumVarGrow | 一个节点在任何点上非零 (对一切位数的节点层) | 定理 |
| `W.L4`, `nz-κ` | SumVarGrow | **任何** `κN G ρ` 闭包 (节点层位数任意) 在满足 `Inv`, `IZ` 的状态上非零 | 定理 |
| **`Inside i`** | SumVarGrow | 对一切深度 $i$, 高位, 点: `Blk i ns` 里的任何站不超过这一段走完 | 定理 |
| **`Close`** | SumVarGrow | 对一切 `F`, `G`, `ρ`, 点: `asuc (Val p (nl F)) ≤ Val p (nl F ⨾ κN G ρ)` | 定理 |
| **`SupBlk i ns p g`** | SumVarGrow | 对一切深度, 高位, 点, $g:\mathbb N\to\mathbb N\times\mathbb N^i$: 闭包站严格高于段内可数族的上确界 | 定理 |
| `SuccSt a d pre e` | SumVarGrow | 一切秩, 一切前缀: 最低位后继严格增长 | 定理 |
| `SupSt a i d pre e g` | SumVarGrow | 一切秩, 一切位置: `sup_k Ts (pre ++ e ∷ g k) < Ts (pre ++ (e+1) ∷ 0…0)` | 定理 |
| `SupD i d g` | SumVarGrow | 一切秩: 首位 $d$ 之下的可数族 `< Ts (i+1) (d+1) 0…0` | 定理 |
| `SupTop j g` | SumVarGrow | 一切秩: 首位在第 $j$ 位的一切站的可数族 `< T⁰ (j+1)` | 定理 |
| `RankUp j`, `T⁰≤Tω`, `T⁰<Tω`, `Ts≤T⁰`, `Ts<Tω` | SumVarGrow | 秩之间, 到 `Tω` | 定理 |
| `Tω≤sup`, `sup≤Tω` | SumVarGrow | `Tω` 与 $\sup_j$ `T⁰ j` 互相 `≤`: $\Omega^\omega$ 站恰是各秩的极限 | 定理 |
| `Ω²≡`, `Ω²<Ω²+1`, `Ω²+1<Ω²·2`, `Ω³<Ω⁴`, `Ω⁴<Ω^ω` | SumVarGrow | 具体的站 (都是上面的实例) | 定理 |
| 读法: `T⁰ j` 读 $\psi_0(\Omega_{\Omega^j})$, `Tω` 读 $\psi_0(\Omega_{\Omega^\omega})$ | — | 序数值没有验收 | 判断 |

**一条对一切位数的定理取代了按维的定理.** 三位时 `SupN`, `SupR`, `Sup3` 各走一层 `P` 模块; 这里 `SupBlk` 对深度 $i$ 归纳 (`Inside`); 三条分别对应 `SupSt 0 0`, `SupD 1`, `SupTop 2` (首位的记法差一: `Ts j d` 的首位读 $d+1$; 首位为 $0$ 的站在更短的层里, 经 `Ts≤T⁰` 传过去). 证法同三位: 段内的站都在 `nl` 段的极限之下 (字面的部分和), 闭包节点在其后的回灌输出非零 (`nz-κ`, 对一切 `G`, `ρ` 一条). **分辨力到此为止** (同 SumClimb): 多出的是 "可数族的上确界之上一段非零", 不是 "高于前一族的某个闭包点".

## 翻译账 (硬交付)

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| 层是 `List A`, `a ∷ L` 读 $\Omega\cdot L+a$ | $\Omega$ 进制的康托尔范式 (系数可数) | **读自记号的算术** (同 SumClimb 的 $(r,p,a)$, 只是位数放开) |
| `hd`: 最高的不同位严格低 | 范式的字典序 | 读自记号的序 |
| `tl` 的 `h ⊲ W`: 更低的位只要在世界之下 | 不这样没有字面公共上界 | 树逼的 (壁垒); 与三位时 `lo`, `lr` 的世界界同 |
| `tz`, `EqP`, `NZL`, `zdec`, `drpZ`, `congL`/`congR`/`accE` | 列表末尾补零不改值, 位数在一个输入里混合 | **翻译带来的脚手架**: 康托尔范式的列表表示不唯一, 树要它们读法一致 |
| `cmpL` (对一切位数一个比较) | 范式的字典序 | 序读自记号; 比较在字面公共上界 $m$ 之下进行是树逼的 |
| `D′`, `fw`, `bw`, `toD`, `ofD`, `mapD`, `accY` | 位数可变时停机检查看不见字典序 | **树逼的 (停机)**; 与记号无关, 任何可变形状的层下标都要 |
| `Up` (高位的步: 下一位是 $d$, 更低为零) | 三位时 `stepH`, `stepR` 的统一写法 | 树侧, 值不变是判断 |
| `Blk`, `κ j`, `Rj` | 三位时 `nd`, `B`, `BR`, `κ3` 的统一写法 | 选站; 从 `[1]` 起是值的选择 |
| `Pt`, `adv`, `Inside`, `Close`, `SupBlk` | 为了不按维写 | 树侧 |

**按 `AGENTS.md` 归类: 仍是加深翻译, 但 "每升一级加一维" 这一模式在 $\Omega^\omega$ 之下被消掉了.**

- 加深的一面: 层的形状就是 $\Omega$ 进制的康托尔范式, 字段读自记号; 补零相等 (`EqP` 一族) 是翻译带来的脚手架, 不是序数值需要的 (值只要层的序, 不要它的表示).
- 提供信息的一面: (1) 节点种类、比较、$\Omega_L$、闭包都**对一切位数一个定义**, 不再每级多一种; (2) 增长写成对结构参数的一步定理: `Inside` 对深度 $i$ 一步归纳, 每一步新用到的字段只有 `Blk (i+1)` 的 `nl` 段与 `κ i ns` 的 `zs i` 补零; `SupBlk` 取代 `SupN`/`SupR`/`Sup3`; (3) 停机的脚手架 (`D′` 与搬运) 是树自己的要求, 与记号无关, 而且通用: 换成任何有良基序、能证 `AccY` 的层下标都照用.
- 新增脚手架: 停机的那一份是层下标可变所必需 (树逼的); 补零的那一份是用列表表示范式带来的 (翻译).
- 没有否定定理.

**交给摆脱侧的问题.** 停机这一关已经和层的具体形状脱钩: 折叠只用到 "节点种类 `K`, 它的可达性 `AccY`, 传递 `mkOf`, 世界界 `kk`, 比较 `rkT`". 如果层下标本身由回灌生成 (`HtGen` 一路), 这里的 `D′`/`fw`/`bw` 可以原样搬过去; 要补的只是那几条接口.

## 账 (层 1–3, `locslice_l12.py` 口径)

实测, 定义级切片, 计 agda 非空非注释行, 记号模块除外 (脚本在临时目录 `sumvar/locslice_var.py`, 改自 `sumht/locslice_climb.py`).

| 路线 | 层 1 (`D₊`, `D`, `D̂`, `Dl`) | 层 2 (+折叠, 闭项, FGH) | 层 3 (+合法性) | 加严格增长 |
|---|---|---|---|---|
| SumClimb, 三位, 到 $\Omega^3$ | 84 | 700 (去共用 617) | 721 (去共用 638) | 1005 (净增 284) |
| SumVar, 一切位数, 到 $\Omega^\omega$ | 132 | 733 (去共用 650) | 757 (去共用 674) | 1054 (净增 297) |

- 从三位到一切位数的代价: 层 1 多 48 行, 层 2 多 33 行, 层 3 多 36 行, 增长多 13 行. 层 2 按模块: SumVarTree 334, SumVarFold 182, SumVarClosed 59, Free.Level 56, CumReadCF 36, TLOpsW 27, BTBO 27, SumHtTree 12.
- SumVarTree 里按用途 (块级, 非空非注释行): **停机的脚手架 43** (`AccY`, `accY` 一族, `subA`, `D′`, `VL`, `mapD`, `fw`, `bw`, `toD`, `ofD`), **补零的脚手架 99** (`Zs`, `EqP`, `NZL` 与它们的算律, `kzs`, `kzz`, `z◁`, `congL`, `congR`, `accE`, `zdec`, `drpZ`), 节点种类与算律 38, $\Omega_L$ 28. 补零的一份比停机的一份大一倍多, 是翻译 (列表表示) 的代价.
- 积木 (SumVarClosed 内): `Blk` 30, `Rj` 32, `κ` 25, `X⁰` 37, `Xs` 40, `Xω` 34 (都含共用的 `nd`, `Pfx` 等). 三位时按站各加几行; 这里一切秩共用这几行.
- 严格增长 (在层 3 之上): `Succ` +90, `Inside` +105, `Close` +153, `SupBlk` +208, `SuccSt` +162, `SupSt` +259, `SupD` +239, `SupTop` +227, `RankUp` +203, `T⁰≤Tω` +106, `Tω≤sup` +93, `Ts<Tω` +233; 合计净增 297 (SumVarGrow 265, TLRuleSpec 24, SumHtTree 8). 三位时只对三位的 `SupN`/`SupR`/`Sup3` 等净增 284.
- 文件代码行 (非空非注释): SumVarTree 357, SumVarFold 201, SumVarClosed 107, SumVarGrow 298, SumVar 5.

## 第一个障碍: $\psi_0(\Omega_{\Omega^\omega+1})$

顶层 `top` 的节点各位都在世界之下, 读作 $\Omega_{\Omega^\omega}$, 但顶层本身不是一个层: 没有 `lay` 能当它作目标. 要 $\Omega^\omega+1$, 层的下标要有 "第 $\omega$ 位", 即位置本身是序数 (指数取自更低的层), 层成为嵌套的范式 (列表的列表, 或者以树为指数). 判断: `D′` 与搬运这一套不依赖层的形状, 只要新的节点种类有 `AccY`, 传递, 世界界, 与字面公共上界之下的比较; 难处在比较 (指数本身要比较, 比较要在字面公共上界之下) 与 `AccY` 的证明 (嵌套的字典序). 没有试, 是未走通, 不是否定. 判断: 用记号的范式往上嵌套是继续加深翻译; 更应由摆脱侧回答 "层下标由树自己生成".

## 有限测试

没有做新的计值 (上一轮 `G 1` 在 `SumHt` 的 $\Omega_\Omega$ 站已超 90 秒; 这里的 `outV`/`inV` 是深搬运, 只会更慢).

## 审计

- `importclosure.py --only OCF.Free.Level --only OCF.BTBO --only OCF.Align.CumReadCF --only OCF.Align.TLRuleSpec --only OCF.Align.TLRule --only OCF.Align.TLOpsW --only OCF.Align.SumHtTree --only OCF.Align.SumVar OCF.Align.SumVar`: 闭包 24 个模块 (本地 12: CumReadCF, SumHtTree, SumVar 五个, TLOpsW, TLRuleSpec, TLRuleSum, BTBO, Free.Level), 禁用表命中 0, `--only` 之外 0, OK. 编译器保证不引用.
- `depslice.py` (到达块 / 记号块 / 词命中): `SumVarClosed:fgh` 187/0/0, `SumVarClosed:Lg-Tω` 171/0/0, `SumVarClosed:TΩ` 150/0/0, `SumVarGrow:SupBlk` 223/0/0, `SumVarGrow:SupSt` 244/0/0, `SumVarGrow:SupTop` 239/0/0, `SumVarGrow:Tω≤sup` 206/0/0, `SumVarGrow:Ts<Tω` 244/0/0. 正对照 `Om1HnAccept:label-term₀` 1188/92/58. 只保证不引用, 不说明没受记号启发 (层的形状就受了, 见翻译账).
- 禁用构造: 五个文件无 `postulate`, 无洞, 无 `TERMINATING`/`NON_TERMINATING`/`NO_POSITIVITY_CHECK`, 无 `trustMe`, 不用 `--cubical`; 选项都是 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumVar where

open import OCF.Align.SumVarTree using (D₊; D′; D; D̂; Dl; KL; AccY; accY; fw; bw; toD; ofD; mapD; Ωd) public
open import OCF.Align.SumVarClosed using (Blk; Rj; κ; nd; X⁰; Xs; Xω; T⁰; Ts; Tω; TΩ; Lg-T⁰; Lg-Ts; Lg-Tω; Lg-TΩ; TΩ²+1; TΩ²·2; TΩ³; TΩ⁴; TΩ^ω; fgh; G) public
open import OCF.Align.SumVarGrow using (nz-κ; Succ; Close; Inside; SupBlk; SuccSt; SupSt; SupD; SupTop; RankUp; T⁰≤Tω; T⁰<Tω; Ts<Tω; Tω≤sup; sup≤Tω; Ω²≡; Ω²<Ω²+1; Ω²+1<Ω²·2; Ω³<Ω⁴; Ω⁴<Ω^ω) public
```

# NegValC (入口): 值关系搬到 CRw, 否定一路

> 不含记号. 与构造一路 ValC 配对, 共用接口 [ValCIf](ValCIf.lagda.md) (接口定稿 2026-11-06 01:41; 本路不改它). 作者本轮选定原话: "值: Fab5 的路线引理搬到 CRw". 第 4 层: 只新增关系与定理, 不改树, 折叠, 合法性. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延 (连前提也没有).
>
> **对纲领与目标.** 纲领 1: 一切比较都在布劳威尔树 (`HB`) 上, 第 0 层落到 `TLRuleSpec._≤_`. 本路的主要结论是: CRw 的折叠**不是输入的值的函数**. 两个互相 $\le$ 的合法输入 ($\lim(1,1,\dots)$ 与 $1$) 折出的值, 前者严格大于后者. 原因是 ℕ-极限子句取部分和 (累加). 纲领 2, 4: 无公理, 不读记号. 纲领 3: 接口的律都带字面公共上界, 本路没有用到壁垒. 目标 "树侧的合法性标准": Fab5 的值合法 `Mo` 在累加的折叠上不够, 原样移植不是接口的实例 (`fab5-port-excluded`). 还需要一条约束 ℕ-极限的值的合法性 (例如相邻项值严格增长), `LgB` 允许相邻项相同 (`hself`), 给不出它. 这条要求由累加的折叠的三个子句逼出, 不是由记号逼出的 (判断: 读代码). 另外, 定稿接口的路线引理 `route` 在 $t=j$ 处与第 0 层的 `z≤` 不相容 (`route-hself`, `no-z≤`), 要追加只对真 $t\lhd j$ 的记录.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegValC where

open import Data.Unit using (tt)
open import Data.Product using (_×_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁; W₀)
open import OCF.Lean.CRwFold I₁ using (Φ; wf; bX; b⊥; cx)
import OCF.Lean.NegValCInst as NI
import OCF.Lean.NegValCBound as NB
import OCF.Lean.NegValCRoute as NR
```

## 在闭项 `TX` 用的那一个折叠上

`TX` 是 $\Omega_1$ 层的地板经跨底折叠 (`cx W₀`) 折到第 0 层. 同一个折叠 (同一个世界 $W_0=1$, 同一个目标) 把 $\lim(1,1,\dots)$ 与 $1$ 折成值反向的两棵树, 对一切界 $b$.

```agda
module TXFold (b : Cd) = NI.G.AccV I₁ bX hz (wf bX hz) tt b⊥ hz (cx W₀ tt (z⊲ᴮ W₀)) b

tx-rev : ∀ b → NI.Rel._≤[_]_ NI.cr⊥ (hs (TXFold.Φ1 b)) tt (TXFold.ΦL b)
tx-rev b = TXFold.rev b NI.cr⊥

tx-not-mono : ∀ b → ¬ NI.Rel._≤[_]_ NI.cr⊥ (TXFold.ΦL b) tt (TXFold.Φ1 b)
tx-not-mono b = TXFold.acc-not-mono≤ b NI.cr⊥

-- 接口的边界定理, 实例 I₁
module Bound₁ = NB I₁
module Route₁ = NR I₁
```

## 地图

| 名字 | 文件 | 陈述 | 档 |
|---|---|---|---|
| **`G.AccV.acc-not-mono≤`**, `G.AccV.rev` | Inst §3 | 对一切 `I`, 层号, 目标 (`sm`/`cx`), 界, `cr`, 世界: $\Phi\,1+1\le\Phi\,\lim(1,1,\dots)$, $\Phi\,\lim(1,1,\dots)\not\le\Phi\,1$; 输入互相 $\le$ (`l11≤one`, `one≤l11`), `LgB`, `Sh` | 定理 |
| `tx-rev`, `tx-not-mono` | 本篇 | 上一条在 `TX` 的折叠 (`cx W₀`, 实例 `I₁`) 上 | 定理 |
| **`G.mo-not-pres`** | Inst §4 | Fab5 的 `Mo` 原样移植: `N = up (top b⊥ 1)` 合法且值合法, 折到第 1 层 (`keep`) 后不值合法, 对一切界与世界 | 定理 |
| `G.N-in-floor`, `G.N-chain0` | Inst §4 | 第 2 层地板折到第 0 层 (`above`), 回灌链第 0 点就是上一条的折叠 | 定理 (`refl`) |
| `leg-not-mono≤`, `sh-not-mono≤` | Inst §5 | 实例 `I₁`: $\lim(1,1,\dots)\le1$, 而 `leg`, $\mathrm{sh}_0\,B$ 把两者送到值反向的两棵树, 对一切 $B$ | 定理 |
| `Rel.¬s≤` | Inst §1 | Fab5 的关系 (移植): $x+1\not\le x$, 对一切种类结构 | 定理 |
| **`pull`** | Bound §2 | 对一切实例: `Le m x y`, $x, y$ 值合法 ⟹ 以界 $0$ 折到第 0 层后 `TL.≤` | 定理 |
| `Mo-one`, **`no-triv`** | Bound §2 | 对一切实例: 合法层号上 $1$ 值合法, `¬ Le m 1 0`; 平凡关系不是实例 | 定理 |
| **`rep-not-mono`**, `no-l11` | Bound §2 | 对一切实例: $x$, $\lim(x,x,\dots)$ 都值合法 ⟹ `¬ Le m (lim (x,x,…)) x` | 定理 |
| **`l≤-excl`** | Bound §2 | `Le m` 对 `l≤` 封闭 ⟹ 对一切值合法的 $x$, $\lim(x,x,\dots)$ 不值合法 | 定理 |
| **`fab5-port-excluded`** | Bound §2 | 不存在实例, 它的 `Le m` 包含 Fab5 关系, `Mo m` 包含 Fab5 的 `Mo` (任一 `cr`, 世界) | 定理 |
| **`route-hself`**, **`no-z≤`** | Route §3 | 对一切实例: `¬ Le hz hz R` ($R$ 是具体的第 0 层树, 值合法), 所以 `Le hz` 不能含 `z≤`: 接口的 `route` 在 `pt = hself` ($t=j$) 处与 `z≤` 不相容 | 定理 |
| `BI`, `infl`, `hsB≤` | Route §2 | 第 0→0 层折叠与界无关; 第 1 层嵌入折回不降值; 地板 $\Omega_1$ 以界 $B$ 折到第 0 层 $\ge B+1$ | 定理 |

## 只否定什么, 不否定什么

- `acc-not-mono≤`: 只否定含 `l≤` 与自反的关系在 CRw 折叠下单调 (对一切值合法的输入, 用 Fab5 的 `Mo`). **不否定**: 对值严格的 ℕ-极限单调; 去掉或限制 `l≤` 的关系; 在闭项实际折到的输入上单调 (地板与折叠的输出的 ℕ-极限都是部分和, 相邻项至少多 $1$; 这一句是读代码的判断).
- `mo-not-pres`: 只否定 Fab5 的 `Mo-Ψ` 的直接移植. 不否定第 0 层坐标的值合法收窄后的版本.
- `sh-not-mono≤`: 只否定 `I₁` 的回灌对一切坐标值单调; 闭项的跨底目标是第 0 层, 那里 $\Omega_1$ 结点走链, 链的坐标是折叠的输出 (判断).
- 对接口: `pull`, `no-triv` 说明接口不是盲的 (平凡关系不是实例), 不说明接口可满足. `rep-not-mono`, `l≤-excl`, `fab5-port-excluded` 只限制 `Le` 与 `Mo` 的选法. `route-hself`, `no-z≤` 只否定 `pt = hself` ($t=j$) 时的 `route` (对第 0 层含 `z≤` 的关系): 这时右边外层的折叠 (第 $t$ 层到第 $t$ 层) 与界无关, 左边的链从界出发. 构造一路事先已判断这里失败, 计划只对真 $t\lhd j$ 证. **没有**否定 `pt` 以 `hsuc`/`hlim` 开头时的 `route`, 也没有否定 `Φ-mono`, `Mo-Φ`. 本路没有找到真 $t\lhd j$ 时 `route` 在强制值合法的输入 ($0$, $1$, 地板, 折叠的输出) 上的反例; 对几个小输入 ($m=2, 3$; $x=0, 1$, 地板) 手算, 两边要么字面相同 (只差界), 要么两步折法更大 (判断, 不是测试).

## 前提实例

- `acc-not-mono≤` 的一切参数都是全称的; 输入 `l11`, `one` 对一切种类结构合法 (`Lg-l11`, `G.Sh-l11`). `cr` 的实例: `cr⊥`, `G.cr₁`, `G.cr₂`. `TX` 的那组参数就是 `CRw.TX` 的定义里的那组.
- `mo-not-pres`: `N` 的 `LgB` 与 `Mo` 是定理 (`G.Lg-N`, `G.Mo-N`), 对一切世界.
- `no-z≤` 的前提 "`Le hz` 含 `z≤`": 第 0 层的标准前序与 `TL.≤` 的拉回都满足; 构造一路的关系 (按它的消息, `ValCRel`) 也有 `z≤`.
- 接口一侧: 定理对一切 `V : ValC⊥`; 实例要构造一路给出 (本路写成时还没有, 那时前三条空真). `fab5-port-excluded` 是 "不存在", 不依赖实例. `l≤-excl` 的前提 `LClosed` 由 Fab5 的 `l≤` 构造子满足; 值合法的 $x$: `Mo-hz`, `Mo-one`, `Mo-top`.

## 对构造一路的意义 (判断)

0. 按定稿的 `ValC⊥` 没有第 0 层含 `z≤` 的实例 (`no-z≤`, 定理). 修补是追加只对真 $t\lhd j$ 陈述 `route` 的记录 (判断).
1. 关系与值合法要二选一地收窄: `Le` 不含无限制的 `l≤`, 或 `Mo` 排除相邻项相同的 ℕ-极限; 第 0 层坐标的 `Moᴱ` 不能取 `⊤` (`mo-not-pres` 的坐标就是 $\lim(1,1,\dots)$). 一个候选是 "值严格": ℕ-极限的相邻项 $f_n+1\le f_{n+1}$; CRw 折叠的输出与地板都满足这一条的形状 (`⊞-fst` 加一个至少为 $1$ 的项; 判断).
2. 构造一路提出的担心 ("`route` 两边留下的结点的种类 `along q` 与 `along q₂` 字面可能不同"): 读代码的判断是两者命题相等 (直接的目标路径字面是 `⊲ᴮ-tr pt (⊏⊑ pj)`, `cmpB` 两边走过的公共前缀相同, `cl` 与 `along` 往返). 没有证, 也没有反例.
3. 累加把严格增长吸收掉 (`NegLeanLvVal.strict-cell` 的推广): 本路没有写到 CRw 的闭项层面 (要先有值单调才能证两个链的上确界互相 $\le$), 未做.

## 文件

| 文件 | 内容 |
|---|---|
| [NegValCInst](NegValCInst.lagda.md) | Fab5 关系的移植, `¬s≤`; `acc-not-mono≤`, `mo-not-pres`, `sh-not-mono≤` (不依赖接口) |
| [NegValCBound](NegValCBound.lagda.md) | 对接口 `ValC⊥`: `pull`, `no-triv`, `rep-not-mono`, `l≤-excl`, `fab5-port-excluded` |
| [NegValCRoute](NegValCRoute.lagda.md) | 对接口 `ValC⊥`: `route-hself`, `no-z≤` |
| 本篇 | 入口; `TX` 的折叠上的实例 |

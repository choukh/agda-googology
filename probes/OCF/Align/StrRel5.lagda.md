# 结构关系, 第五轮: 嵌套族的结构可靠性对一切深度成立: 入口

> **判决: HOLDS (主线的嵌套族, 动作 `Step`).** 不读记号. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 `Funext`. 没有改任何已有文件.
>
> **定理** [StrRel5Nest](StrRel5Nest.lagda.md) **`sem : ∀ k → Sem k`** (无参数): 嵌套族 $\mathrm{nest}_k$ 在两个运行世界 $W\le W'$ 里, 从树世界出发的两条路径 $q,q'$ 对齐 (`Al`), 两边状态结构相关 (`R∀`) 时, 两边输出对一切读数路径对 $\sqsubseteq^{\mathsf P}$ 相关; 值可比是推论 (`sem-val`). 前提可以满足: 下面的 `top` 对一切 $W\le W'$ 与一切 $k$ 给出跨世界的比较 (树世界就是运行世界, 空状态).
>
> 四件缺件都做了:
>
> 1. **`walk` 的结构结论** ([StrRel5Walk](StrRel5Walk.lagda.md) `walkˢ`): `aS`↦`z0`, `aP`↦`sq`, `aR`/`aRL`↦`pr`, `aL`↦`sq`+`lm`. 状态关系与分支前提作参数.
> 2. **结构的分支与状态语义** ([StrRel5Nest](StrRel5Nest.lagda.md) `R∀`, `advA`, `stepR`): 状态关系是 "状态的差对一切读数路径对相关, 第 0 层累计 $z$ 也相关". `n1` 分支 (动作 `Step`) 的输出是 $\omega\cdot(1⨾0⨾\text{读数})$, 由 `R∀` 直接给出.
> 3. **结构的路径一致** ([StrRel5All](StrRel5All.lagda.md) `walkᴬ`, [StrRel5Nest](StrRel5Nest.lagda.md) `cvR`): `cv` 读旧状态的路径由 `cmpF` 算出, 两边字面不同. 办法不是证明 "不同路径读数相同", 而是让关系**对一切读数路径对**成立, `walkᴬ` 逐格保持它. `cvR` 对 `cmpF` 的 2×2 结果逐一给出.
> 4. **剩下的路径也对齐** ([StrRel5Suf](StrRel5Suf.lagda.md) `rfx`, `fcs`, `fcl`, `walkᵠ`): 外层对齐时, 每对位置剩下的两条路径对齐, 所以语义只对**对齐的** $q,q'$ 量化. 内层 `nκ` 第 0 格的路径由 `StrRel4Pr.alZeroᴾ` 接上.
>
> **不要的东西.** 不要 `CellStep`, 不要领先量 `Adm` 作语义前提 (`Al` 里带着, 但语义不用), **不要 "树世界可比"**, 不要 `Good`/`CohY`/规范形, 不要左边极限截断.
>
> **范围.** 只对嵌套族 $\mathrm{nest}_k$ 与动作 `Step`. 一般的分支族 (`KNest2Sound` 的带下标关系 $\kappa$ 规则, 分支随位置变) 没有重述; 判断: `walkᴬ` 的分支前提是任意的, 所以把 `sem` 的归纳换成对结构关系推导的归纳, 每个构造子照 `StrRel3Lo.sndˡ` 改成 "一切读数路径" 版即可, `ni` 一句要重做 `chainᴼ` 的一切路径版. 未做, 不是否定.

## 1 定理表

| 定理 | 文件 | 内容 | 档 |
|---|---|---|---|
| `Env`, `Rd`, `Rn`, `Wlk` | StrRel5Walk | 一边的运行环境 | 定义 |
| **`walkˢ`** | StrRel5Walk | 对齐的两次 `Walk`, 读数 $\sqsubseteq^{\mathsf P}$ 相关 | 条件定理 (参数 `adv`, `br`) |
| `rfx`, **`fcs`**, **`fcl`**, `e-suc`, `e-lim` | StrRel5Suf | 前端加段仍对齐; 长度证据沿剩下的路径取回 | 定理 |
| **`walkᵠ`**, `cellᵠ` | StrRel5Suf | 同 `walkˢ`, 分支多得到剩下的路径的对齐 | 条件定理 (参数 `adv`, `br`) |
| **`walkᴬ`**, `cellᴬ` | StrRel5All | 同 `walkᵠ`, 对一切读数路径对 | 条件定理 (参数 `adv`, `br`) |
| `advA`, **`cvR`**, `stepR`, `drpR` | StrRel5Nest | 状态关系的 `⊕`, 换世界, 动作, `drp` | 定理 |
| **`sem : ∀ k → Sem k`** | StrRel5Nest | 嵌套族对一切深度结构可靠 | **定理** (`Sem k` 里的前提是陈述的一部分) |
| `sem-val` | StrRel5Nest | 值可比 | 定理 |
| **`top`** | 本文 | 前提可满足: 对一切 $W\le W'$, $k$ | 定理 |

**否定.** 本轮没有新的否定定理, 也没有走不通的件. **有限测试.** 无.

## 2 `KStep`/`snd²` 的重述

`KNest2Glue.kstep` 的对应物在 `sem (suc k)` 的 `where` 里: `St n` 是格 $n$ 的状态 (格世界可比, 格路径对齐, 状态 `R∀`), `st0` 是第 0 格 (`alZeroᴾ`), `stS` 是第 $n+1$ 格 (`alSuccᴾ`, `cvR`), `out` 是一格 (`cellᴬ`, 分支前提是归纳假设). 和 `kstep` 比: 状态从值的 `Cxᴵ` 换成结构的 `R∀`; 格路径的对齐从三条值前提换成 `Al` 数据; 第 0 格的 "树世界可比" 换成 $q\sim q'$ 的对齐. `snd²` 对一切深度的那一句就是 `sem` 本身 (对 $k$ 归纳).

## 3 翻译账

| 新增 | 来源 | 读自记号 / 树逼出 |
|---|---|---|
| `walkˢ` 的五句 | `Walk` 的展开 | **树逼的** |
| `pr` 用在 `aR`/`aRL` | 右边多出的位置 | **树逼的** |
| 剩下的路径的对齐 (`fcs`, `fcl`) | 内层第 0 格路径 = 外层剩下的路径 ⨾ `sum-fst` | **树逼的**; 有否定支撑 (`phead→LPO`: 不能由值求) |
| `R∀` 对一切读数路径对 | `cv` 的读数路径由 `cmpF` 算出 | **树逼的** (折叠的字面) |
| 动作 `Step` | 主线折叠的动作 | 树侧 |

**归类: 提供信息.** 没有新构造子或节点字段, 没有改树、折叠, 没有 `Lab`, 没有记号. `sem` 对一切深度只有一个证明, 不按深度加前提. 这一站新用到的字段: `κc` 的 `v`, `lv`, `wv`, `av`, `ap`, `Sv`, `co` (都由字面给出), `cv` 内部的 `cmpF`. 缺陷没有变深: 值语义 (`KNest2`) 里 "两边树世界可比" 与 `CellStep` 两个前提都消失了, 换成从推导携带的结构.

## 4 审计与账

- 编译: 删掉本组 `StrRel5*` 的 `.agdai` 后从头编译入口, 退出码 0. 无禁用构造, 不出现 `Funext`.
- 导入闭包 (`--only` 同 [StrRel4](StrRel4.lagda.md) §4 的扩展表): 闭包 55 个模块 (本地 45, 库 10), 禁用表命中 0, `--only` 之外 0, OK. 只用 StrRel 的表: 禁用表命中 0, `--only` 之外 10, 与 `KNest2`, `StrRel4` 相同 (继承自 `KNestAdm`/`KNestSound`/`KValSound`). 编译器保证不引用记号; 不说明定义没有受记号启发.
- `depslice.py` (语法级近似): `StrRel5Nest:sem` 211 块, `StrRel5:top` 213, `walkᴬ` 134, `walkᵠ` 133, `walkˢ` 123, `cvR` 39; 记号模块块数都是 0, 别处记号词 0. 正对照 `Om1HnAccept:label-term₀`: 1188 块, 记号模块 92, 别处 58.
- 代码行 (代码块内非空): StrRel5Walk 70, StrRel5Suf 104, StrRel5All 76, StrRel5Nest 113, 入口 23, 合计 386.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel5 where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.SumOneTree using (n0)
import OCF.Align.SumOneClosed as F
open import OCF.Align.LayerTrOne using (one)
open import OCF.Align.KNestSound using (nest)
open import OCF.Align.StrRel4Walk using (aS)
open import OCF.Align.StrRel4Pr using (_⊑ᴾ_; z0)
open import OCF.Align.StrRel5Walk using (Env; Rn; module GoS) public
open import OCF.Align.StrRel5Suf using (rfx; fcs; fcl; module GoQ) public
open import OCF.Align.StrRel5All using (OA; module GoA) public
open import OCF.Align.StrRel5Nest using (E; R∀; advA; cvR; stepR; drpR; Sem; sem; sem-val) public
import OCF.Align.StrRel5Nest as N

-- 前提可满足: 树世界就是运行世界 (q = self), 空状态, 两边世界 W ≤ W′
top : ∀ k {W W′} (lW : Lg W) (lW′ : Lg W′) (l₁ : one ⊲ W) (l₁′ : one ⊲ W′) → W ≤ W′ → ∀ w w′ →
      N.OA (Rn (E W lW l₁) (nest k) C.self w (F.st F.zeroD n0)) (Rn (E W′ lW′ l₁′) (nest k) C.self w′ (F.st F.zeroD n0))
top k lW lW′ l₁ l₁′ le w w′ = sem k lW lW′ l₁ l₁′ le C.self C.self (aS C.self lW′) w w′ _ _ ((λ τ τ′ → z0) , z0)
```

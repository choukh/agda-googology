# `T-Ω` 的值 (三): 下界不能逐点比两个动作

> 不含记号, 不是验收文件. 入口 [HtVal](HtVal.lagda.md).
>
> 与关系无关的核 `MonoPort3Gen` (以及 `StrRel`, `DVal`, `KVal` 的 `snd`) 都要求两边的**动作逐点相关**: 相关的输入与状态, 两个动作的输出也相关 (`HA`, `HA0`, `HA₁`, `HAᶜ`, `Ok` 一类前提). 要由它们得出 `T-Ω` 的下界 (参照的计算不高于主线), 就要参照动作 `Act′` 的输出与主线动作 `Act` 的输出相关, 方向是 `Act′ ⊑ Act`.
>
> **定理 (`no-pointwise`).** 在层 $2$ (`emb 2`) 的目标上, 空状态时两个动作的输出 `outA′` (参照, $\omega\cdot(\Omega'_2⨾0)$) 与 `outA` (主线, $\omega\cdot(\Omega_2⨾0)$) 的关系: 只要关系 $R$ 把 "最外层的和里有层 $0$ 的节点" (`Z0`) 从左边带到右边, 就没有 $R$ `outA′ outA`. 原因是字面的: 主线的 $\Omega_2=1⨾N_1$ 的和里只有层 $1$ 的节点, 参照的 $\Omega'_2=1⨾((0⨾N_0)⨾N_1)$ 有层 $0$ 的节点 $N_0$. `outA≡`, `outA′≡` (`refl`) 说明这确实是折叠里两个动作在空状态、目标 `emb 2` 上的输出.
>
> 为什么要在层 2 的目标上比 (判断): 层 2 的节点 $N_2$ 上升时, 链从状态在层 2 上的差起步, 那个差的开头就是动作在空状态的层 2 输出; 只比第 0 层目标的关系管不住这条链.
>
> **另一条 (`T-Ω≇T-Ω′`, §4).** 主线闭项与参照闭项不 $\cong$: 换动作在结构上看得见.
>
> **否定的范围.** 只杀 "节点按层对齐、动作逐点比较" 这一种做法 (`StrRel` 的 `ni⊑`, `DVal` 的 `ni⊑`, `KVal` 的 `ni⊑` 都是同层的节点对同层的节点). 不杀: (i) 链的错位 (参照链的第 $n$ 点比主线链的第 $n+1$ 点; 在回灌的格里, 状态 $d_2$ 里已经有走过的层 $0$ 节点 $N_0$ 的保留, 所以错位后 `Z0` 不再挡路, 判断); (ii) 跨层的节点对齐 (低层的节点对高层节点的一段); (iii) 按值的关系. 上界方向 (`Act ⊑ Act′`) 不受影响: 主线的写法是参照的删除 (`HtValAct.Ωd≡`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用 `Funext`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtValNeg where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; Lg; _⊲_)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedHt using (Ωᴴ; Lg-Ωᴴ)
open import OCF.Align.HtFeedClosed using (ω⋅)
open import OCF.Align.HtValSplit using (module P)
open import OCF.Align.HtValAct using (Ωd′; Act′; T-Ω′)
open import OCF.Align.HtFeedClosed using (ord; T-Ω)
open import OCF.Align.EndLowTShape using (walk-≅; path)
import OCF.Free.Level as FL
```

## §1 最外层的和里有层 0 的节点

```agda
data Z0 {L : H} {W : A} : D L W → Set where
  zi  : ∀ {r : StH W hz L} {u : ∀ {W′} → W ⊲ W′ → Lg W′ → Vs L r W′ → D L W′} → Z0 (ni {k = hz} r u)
  z⨾ˡ : ∀ {x y} → Z0 x → Z0 (x ⨾ y)
  z⨾ʳ : ∀ {x y} → Z0 y → Z0 (x ⨾ y)
  zl  : ∀ {d} n → Z0 (d n) → Z0 (nl d)
  zw  : ∀ {W₀} {p : W₀ ⊲ W} {x} → Z0 {W = W₀} x → Z0 (nw p x)
```

## §2 两个动作在空状态、目标层 2 上的输出

```agda
L2 : H
L2 = hs (hs hz)

outA outA′ : ∀ {W} → D L2 W
outA = ω⋅ (Ωd L2 ⨾ n0)
outA′ = ω⋅ (Ωd′ L2 tt ⨾ n0)

-- 确实是折叠里的两个动作: 一切以层 2 为目标的 T
outA≡ : ∀ {ly W W′ m} (p : W ⊲ W′) (l : Lg W′) (z : D ly W′) (T : P.Tg W′ L2 m) →
        P.yc (P.Act {ly} {W} p l z P.Y₀) T ≡ outA
outA≡ p l z T = refl

outA′≡ : ∀ {ly W W′ m} (p : W ⊲ W′) (l : Lg W′) (z : D ly W′) (T : P.Tg W′ L2 m) →
         P.yc (Act′ {ly} {W} p l z P.Y₀) T ≡ outA′
outA′≡ p l z T = refl
```

## §3 否定

```agda
yes0 : ∀ {W} → Z0 (outA′ {W})
yes0 = zl 0 (z⨾ˡ (z⨾ʳ (z⨾ˡ (z⨾ʳ zi))))

no0 : ∀ {W} → ¬ Z0 (outA {W})
no0 (zl n (z⨾ˡ (z⨾ˡ ())))
no0 (zl n (z⨾ˡ (z⨾ʳ ())))
no0 (zl n (z⨾ʳ ()))

no-pointwise : ∀ {W} (R : D L2 W → D L2 W → Set) → (∀ {x y} → R x y → Z0 x → Z0 y) → ¬ R outA′ outA
no-pointwise R pres r = no0 (pres r yes0)
```

## §4 换动作在结构上看得见

沿 `EndLowTShape.path` 两边的构造子不同 (那里 `T-Ω` 与 `SumOne.T₀` 也不同; `T-Ω′` 在那里与 `T₀` 相同, 是 [HtValTest](HtValTest.lagda.md) 的 `path′`, `refl`). 所以 `T-Ω` 与参照项的比较不能经 $\cong$, 只能在值上.

```agda
T-Ω≇T-Ω′ : ¬ (ord T-Ω FL.≅ ord T-Ω′)
T-Ω≇T-Ω′ e with walk-≅ path e
... | ()
```

# 改 "在上" 的折法, 否定一路 (二): 实例, Fab3Typed 的复合式折叠在 sup 层与 ι 不相容

> 不含记号. 入口 [NegFold1](NegFold1.lagda.md). 不依赖接口. 只导入 [HtTowerTy](../Align/HtTowerTy.lagda.md), [LFReTy](../Align/LFReTy.lagda.md) (`S⊥`), [Fab3Typed](../Align/Fab3Typed.lagda.md) (`T`, `fold`), [Fab5ValRel](../Align/Fab5ValRel.lagda.md) 与 [Fab5Val](../Align/Fab5Val.lagda.md) (值关系 `≤`, `cr⊥`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **这一篇做什么.** [NegFold1Sup](NegFold1Sup.lagda.md) 的 `CompIncoh.no-coh` 写在 `CRwBase` 的类型上; Fab3Typed 写在 `HtTowerTy` 的类型上 (两边是不同的类型), 所以这里对 Fab3Typed 原样重证一次, 用 Fab5 的值关系 (带世界, 第 0 层世界是 `tt`).
>
> **定理 `fab3-no-coh`.** Fab3Typed 的塔 `T n = stepⁿ S⊥` 与 "折到底" `fold n` (每次一层, $n$ 次复合). `fold 1 0 = 1`, `fold 2 0 = ω` (`f1`, `f2`, 都是 `refl`). 对 sup 层 `sup ℕ T` 上的任何函数 $F_\omega$, 不能同时有 $F_\omega(\iota_k x)\le \mathrm{fold}_k\,x$ 与 $\mathrm{fold}_k\,x\le F_\omega(\iota_k x)$ (对一切 $k$, $x$). 字面相等的版本 `fab3-no-coh≡`.
>
> **只否定什么.** 只否定 sup 层的折叠与 Fab3Typed 的分量双向值相容. **不否定**: 单向相容; sup 层的其他定义; Fab3Typed 在后继层的结果 (`Ψ-mono`, `Ψ-lg`, Fab5 的 `Ψ-mono≤` 都不受影响, 它们是 "单调 + 逐点 + 值单调" 在一步上可以同时成立的正面例子).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFold1Fab3 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.Fab3Typed using (T; fold; module Fold)
open import OCF.Align.Fab5ValRel using (module Rel)
open import OCF.Align.Fab5Val using (cr⊥)
open Rel cr⊥
```

```agda
f1 : fold 1 hz ≡ hs hz
f1 = refl

f2 : fold 2 hz ≡ hl (Fold.mul S⊥ (hs hz))
f2 = refl

¬21 : ¬ (fold 2 hz ≤[ tt ] fold 1 hz)
¬21 (l≤ h) with h 1
... | s≤s ()
... | ≤s ()
¬21 (≤s (l≤ h)) with h 1
... | ()

fab3-no-coh : ∀ (Fω : HB (sup ℕ T) → HB S⊥) →
              (∀ k x → Fω (ι k x) ≤[ tt ] fold k x) → (∀ k x → fold k x ≤[ tt ] Fω (ι k x)) → ⊥
fab3-no-coh Fω lo hi = ¬21 (≤-trans (hi 2 hz) (lo 1 hz))

fab3-no-coh≡ : ∀ (Fω : HB (sup ℕ T) → HB S⊥) → ¬ (∀ k x → Fω (ι k x) ≡ fold k x)
fab3-no-coh≡ Fω e = fab3-no-coh Fω
  (λ k x → subst (λ z → Fω (ι k x) ≤[ tt ] z) (e k x) (≤-refl _))
  (λ k x → subst (λ z → z ≤[ tt ] Fω (ι k x)) (e k x) (≤-refl _))
```

## 结论 (按档)

- **[定理]** `f1`, `f2` (`refl`), `¬21`, **`fab3-no-coh`**, `fab3-no-coh≡`.
- **[判断]** 复合式推广到 sup 层要么放弃与分量的 (双向) 相容, 要么在 sup 层另写一条不是复合的规则; 后者就回到 "一步坍缩多层".

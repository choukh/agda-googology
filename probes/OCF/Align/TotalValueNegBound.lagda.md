# 实际闭包行的界是一：正面校准

本篇不是否定定理。原 rowC 的 qcl 地板为 fz，rowB 的 qclo 也只有
零需求。对任意环境，其目标零闭包界逐字等于一；不由此推出一加反馈
被吸收，更不推出新旧高闭项同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegBound where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Floor

one-shape : ∀ {a} → a ≅ᴵ suc zero → a ≡ suc zero
one-shape (s≅ z≅) = refl

bound-one-shape : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (p : zero <ᴵ ℓ) →
  Bd (bound (fz ⊔ fk zero) ev p) ≅ᴵ suc zero
bound-one-shape ev p = bound-≅ (⊔∼ fz∼ (fk∼ z≅)) ev p
  (tt , (λ { zero → zero })) zero z≅

bound-one : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ fk zero)) (p : zero <ᴵ ℓ) →
  Bd (bound (fz ⊔ fk zero) ev p) ≡ suc zero
bound-one ev p = one-shape (bound-one-shape ev p)

-- 非空实例：原默认目标零、世界一。
actual : Bd (bound (fz ⊔ fk zero)
  (tt , (λ { zero → zero })) zero) ≡ suc zero
actual = bound-one (tt , (λ { zero → zero })) zero
```

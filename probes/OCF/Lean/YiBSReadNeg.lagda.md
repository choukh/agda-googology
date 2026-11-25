# Ω 覆写不能代替任意带码换基
编译否定（字面结构）：固定的 seen 项不能实现 Read 的所有码，反例为 next omega，两个源域实例均给出。
不否定序数值互相支配，不否定 V149；只排除以同一个 Ω 树项满足此字面等式接口。
入口：YiBSRead；本例地板与偏移均为零，目标为第 1 层。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSReadNeg where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiBSBase
open import OCF.Lean.YiBSRead
one : L
one = nd sS (λ _ → zero)
o1 : Ok one
o1 = tt , λ _ → tt
S : Schema zero (λ c → zero ⊕ ↑ zero c)
S = schema zero (↑ zero) tt self (OkO↑ zero zero tt self) (λ c → refl)
data Hd : Set where
  hz hs hl hΩ hu : Hd
hd : ∀ {S} → T S → Hd
hd zero = hz
hd (suc _) = hs
hd (lim _ _) = hl
hd (Ω _ _) = hΩ
hd (up _ _ _ _) = hu
omega-head : hd (proj₁ (seen S one o1 (z≤ one) (Ωt one) zero)) ≡ hΩ
omega-head = refl
next-head : hd (proj₁ (fold S zero (next omega) one o1 (z≤ one) (Ωt one))) ≡ hl
next-head = refl
omega-source : Domain S zero (proj₁ (source S zero omega))
omega-source = omega-in S zero
next-source : Domain S zero (proj₁ (source S zero (next omega)))
next-source = next omega , refl
Ω-only-not-next : seen S one o1 (z≤ one) (Ωt one) zero ≡ fold S zero (next omega) one o1 (z≤ one) (Ωt one) → ⊥
Ω-only-not-next eq with cong (λ z → hd (proj₁ z)) eq
... | ()
Ω-only-not-uniform : (∀ d → seen S one o1 (z≤ one) (Ωt one) zero ≡ fold S zero d one o1 (z≤ one) (Ωt one)) → ⊥
Ω-only-not-uniform h = Ω-only-not-next (h (next omega))
```

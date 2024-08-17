```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.CrossTree where

open import WellFormed.Base
open import WellFormed.Properties
open import Relation.Binary.Definitions
```

**定义 2-x-x**

```agda
data _≼_ : Ord → Ord → Type where
  z≼  : 0 ≼ a
  s≼s : a ≼ b → suc a ≼ suc b
  ≼l  : {w : wf f} → a ≼ f n → a ≼ lim f ⦃ w ⦄
  l≼  : {w : wf f} → (∀ n → f n ≼ a) → lim f ⦃ w ⦄ ≼ a
```

**定理 2-x-x**

```agda
≼-refl : Reflexive _≼_
≼-refl {(zero)} = z≼
≼-refl {suc x} = s≼s ≼-refl
≼-refl {lim f} = l≼ λ n → ≼l ≼-refl
```

**推论 2-x-x**

```agda
f≼l : {w : wf f} → f n ≼ lim f ⦃ w ⦄
f≼l = ≼l ≼-refl
```

**定理 2-x-x**

```agda
≼-trans : Transitive _≼_
≼-trans z≼      q       = z≼
≼-trans (s≼s p) (s≼s q) = s≼s (≼-trans p q)
≼-trans p       (≼l q)  = ≼l (≼-trans p q)
≼-trans (l≼ p)  q       = l≼ λ n → ≼-trans (p n) q
≼-trans (≼l p)  (l≼ q)  = ≼-trans p (q _)
```

**引理 2-x-x**

```agda
≼-suc : a ≼ b → a ≼ suc b
≼-suc z≼ = z≼
≼-suc (s≼s p) = s≼s (≼-suc p)
≼-suc (≼l p) = ≼-trans (≼-suc p) (s≼s f≼l)
≼-suc (l≼ p) = l≼ λ n → ≼-suc (p n)

≼-zero : a ≼ suc a
≼-zero = ≼-suc ≼-refl
```

**定理 2-x-x**

```agda
ns→≼ : NSRoad a b → a ≼ b
ns→≼ (inl zero) = ≼-suc ≼-refl
ns→≼ (inl (suc r)) = ≼-suc (ns→≼ (inl r))
ns→≼ (inl (lim r)) = ≼l (ns→≼ (inl r))
ns→≼ (inr refl) = ≼-refl

≤→≼ : a ≤ b → a ≼ b
≤→≼ (inl r) = ns→≼ (inl (set r))
≤→≼ (inr refl) = ≼-refl
```

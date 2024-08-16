```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.CrossTree where

open import WellFormed.Base
open import WellFormed.Properties
open import Relation.Binary.Definitions
```

```agda
data _≼_ : Ord → Ord → Type where
  z≼  : 0 ≼ a
  s≼s : a ≼ b → suc a ≼ suc b
  ≼l  : {w : wf f} → a ≼ f n → a ≼ lim f ⦃ w ⦄
  l≼  : {w : wf f} → (∀ n → f n ≼ a) → lim f ⦃ w ⦄ ≼ a
```

```agda
≼-refl : Reflexive _≼_
≼-refl {(zero)} = z≼
≼-refl {suc x} = s≼s ≼-refl
≼-refl {lim f} = l≼ (λ n → ≼l ≼-refl)
```

```agda
f≼l : {w : wf f} → f n ≼ lim f ⦃ w ⦄
f≼l = ≼l ≼-refl
```

```agda
≼s : a ≼ b → a ≼ suc b
≼s z≼ = {!   !}
≼s (s≼s r) = {!   !}
≼s (≼l r) = {!   !}
≼s (l≼ x) = {!   !}
```

```agda
ns→≼ : NSRoad a b → a ≼ b
ns→≼ (inl zero) = ≼s ≼-refl
ns→≼ (inl (suc r)) = ≼s (ns→≼ (inl r))
ns→≼ (inl (lim r)) = ≼l (ns→≼ (inl r))
ns→≼ (inr refl) = ≼-refl

≤→≼ : a ≤ b → a ≼ b
≤→≼ (inl r) = ns→≼ (inl (set r))
≤→≼ (inr refl) = ≼-refl
```

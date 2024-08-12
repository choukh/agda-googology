```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
open import Lower using (_∘ⁿ_)
itn : Func → Ord → Seq
itn F i n = (F ∘ⁿ n) i
```

```agda
ε₀ : Ord
ε₀ = lim (itn (ω ^_) 0) ⦃ w ⦄ where
  w : wf (itn (ω ^_) 0)
  w {(zero)} = zero₁
  w {suc n} = ^-pres< (w {n})
```

```agda
ε₁ : Ord
ε₁ = lim (itn {!   !} (suc ε₀))
```
ε₀⁺ ω^ε₀⁺ ω^ω^ε₀⁺
ε₀⁺ ω^ε₀*ω
ε₀⁺ ε₀*ω  ω^(ε₀*ω)

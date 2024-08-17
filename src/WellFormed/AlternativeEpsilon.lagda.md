```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module WellFormed.AlternativeEpsilon where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
open import WellFormed.Fixpoints

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
{-# REWRITE *-idˡ #-}
```

```agda
ε : Func
ε-nt : NonTrivial (ε a)
ε-pres-rd : ε preserves Road

ε-pres : ε preserves _<_
ε-pres = map ε-pres-rd

ε zero = itω (ω ^_) 0 w
  module EpsilonZero where
  w : wf (itn (ω ^_) 0)
  w {(zero)} = zero₁
  w {suc n} = ^-pres (w {n})
ε (suc a) = itω (ε a ^_) 0 w
  module EpsilonSuc where
  instance _ = ε-nt
  w : wf (itn (ε a ^_) 0)
  w {(zero)} = zero₁
  w {suc n} = ^-pres (w {n})
ε (lim f) = lim (ε ∘ f) ⦃ ε-pres it ⦄

ε-nt {(zero)} = nt-intro $ <[ 2 ] $ <[ 2 ] zero₁
ε-nt {suc a} = nt-intro $ <[ 2 ] $ nt-elim ⦃ ε-nt ⦄
ε-nt {lim f} = nt-intro $ <[ 0 ] $ nt-elim ⦃ ε-nt ⦄

ε-pres-rd zero = rd[ 3 ] $ set (^-infl ⦃ ε-nt ⦄ ⦃ _ ⦄)
ε-pres-rd (suc r) = rd[ 2 ] (ε-pres-rd r)
ε-pres-rd (lim {n} r) = rd[ n ] (ε-pres-rd r)
```

```agda
ζ₀ : Ord
ζ₀ = itω ε 0 w where
  w : wf (itn ε 0)
  w {(zero)} = z<l
  w {suc n} = ε-pres (w {n})
```

```agda
instance
  ζ₀-nt : NonTrivial ζ₀
  ζ₀-nt = nt-intro (<[ 1 ] (nt-elim ⦃ ε-nt {0} ⦄))
```

```agda
ε-ζ₀⁺ : Ord
ε-ζ₀⁺ = itω (ζ₀ ^_) 0 w where
  w : wf (itn (ζ₀ ^_) 0)
  w {(zero)} = zero₁
  w {suc n} = ^-pres (w {n})
```

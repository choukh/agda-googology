```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
{-# REWRITE *-idˡ #-}
```

```agda
lim#-rd : (n : ℕ) {w : wf f} → Road a (f n) → Road a (lim f ⦃ w ⦄)
lim#-rd n = lim {n = n} ⦃ _ ⦄
```

```agda
lim# : (n : ℕ) {w : wf f} → a < f n → a < lim f ⦃ w ⦄
lim# n = map (lim#-rd n)
```

```agda
open import Lower using (_∘ⁿ_)
itn : Func → Ord → Seq
itn F i n = (F ∘ⁿ n) i
```

```agda
itω : (F : Func) (i : Ord) (w : wf (itn F i)) → Ord
itω F i w = lim (itn F i) ⦃ w ⦄
```

```agda
ε : Func
ε-nt : NonTrivial (ε a)
ε-pres-rd : ε preserves Road

ε-pres< : ε preserves _<_
ε-pres< = map ε-pres-rd

ε zero = itω (ω ^_) 0 w
  module EpsilonZero where
  w : wf (itn (ω ^_) 0)
  w {(zero)} = zero₁
  w {suc n} = ^-pres< (w {n})
ε (suc a) = itω (ε a ^_) 0 w
  module EpsilonSuc where
  instance _ = ε-nt
  w : wf (itn (ε a ^_) 0)
  w {(zero)} = zero₁
  w {suc n} = ^-pres< (w {n})
ε (lim f) = lim (ε ∘ f) ⦃ ε-pres< it ⦄

ε-nt {(zero)} = nt-intro $ lim# 2 $ lim# 2 zero₁
ε-nt {suc a} = nt-intro $ lim# 2 $ nt-elim ⦃ ε-nt ⦄
ε-nt {lim f} = nt-intro $ lim# 0 $ nt-elim ⦃ ε-nt ⦄

ε-pres-rd zero = lim#-rd 3 $ set (^-infl< ⦃ ε-nt ⦄ ⦃ _ ⦄)
ε-pres-rd (suc r) = lim#-rd 2 (ε-pres-rd r)
ε-pres-rd (lim {n} r) = lim#-rd n (ε-pres-rd r)
```

```agda
ζ₀ : Ord
ζ₀ = itω ε 0 w where
  w : wf (itn ε 0)
  w {(zero)} = z<l
  w {suc n} = {!   !}
```

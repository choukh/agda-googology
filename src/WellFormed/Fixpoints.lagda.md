```agda
{-# OPTIONS --safe --cubical --lossy-unification #-}
module WellFormed.Fixpoints where

open import WellFormed.Base
open import WellFormed.Properties
open import WellFormed.Arithmetic
```

```agda
private
  instance
    _ = z≤
    _ = ≤-refl
    _ : ⦃ _ : wf f ⦄ → NonZero (lim f)
    _ = _
  variable
    i : Ord
```

```agda
record Fixable : Type where
  constructor mkFixable
  field
    _[_] : Func
    pres< : _[_] preserves _<_
    conti : continuous pres<
    infl< : (_[_] ↾ NonLim) inflates _<_ within NonLim
open Fixable public
```

```agda
normal→fixable : (ℱ : Normal) → ((ℱ [_]) ↾ NonLim) inflates _<_ within NonLim → Fixable
normal→fixable ℱ infl< = mkFixable (ℱ [_]) (pres< ℱ) (conti ℱ) infl<
```

```agda
open import Lower using (_∘ⁿ_)
_⟨_⟩∘ⁿ : Func → (i : Ord) → Seq
(F ⟨ i ⟩∘ⁿ) n = (F ∘ⁿ n) i
```

```agda
iterω : Fixable → Infl↾ NonLim
iterω ℱ = mkInfl↾ iter infl where
  instance w : ⦃ _ : NonLim i ⦄ → wf (ℱ [_] ⟨ i ⟩∘ⁿ)
  w {n = zero} = infl< ℱ
  w {n = suc n} = pres< ℱ w
  iter : Func↾ NonLim
  iter i = lim (ℱ [_] ⟨ i ⟩∘ⁿ)
  infl : iter inflates _<_ within NonLim
  infl {(zero)} = z<l
  infl {suc x} = map (lim {n = 1}) (infl< ℱ)
```

```agda
_∘Suc : Infl↾ NonLim → Infl↾ (0 ≤_)
ℱ ∘Suc = mkInfl↾ (λ x → ℱ [ suc x ]) $ λ {x} →  begin-strict
    x                                           <⟨ zero₁ ⟩
    suc x                                       <⟨ infl< ℱ ⟩
    ℱ [ suc x ]                                 ∎ where open SubTreeReasoning
```

```agda
jump⟨_⟩ : (i : Ord) (ℱ : Infl↾ NonLim) ⦃ nl : NonLim i ⦄ → Fixable
jump⟨ i ⟩ ℱ = normal→fixable ((ℱ ∘Suc) ⟨ ℱ [ i ] ⟩^) infl where
  infl : ((ℱ ∘Suc ⟨ ℱ [ i ] ⟩^ [_]) ↾ NonLim) inflates _<_ within NonLim
  infl {(zero)} =                               begin-strict
    0                                           ≤⟨ it ⟩
    i                                           <⟨ infl< ℱ ⟩
    ℱ [ i ]                                     ∎ where open SubTreeReasoning
  infl {suc x} = begin-strict
    suc x                                       <⟨ {!   !} ⟩
    ((ℱ ∘Suc ⟨ ℱ [ i ] ⟩^ [_]) ↾ NonLim) (suc x) ∎ where open SubTreeReasoning
```

```agda
jump : (ℱ : Infl↾ NonLim) → Fixable
jump ℱ = jump⟨ 0 ⟩ ℱ
```

```agda
fixpt : Fixable → Fixable
fixpt ℱ = jump (iterω ℱ)
```

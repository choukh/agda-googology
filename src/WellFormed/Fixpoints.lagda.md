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
iterω ℱ = mkInfl↾ iter iter-infl<
  module InfiniteIteration where
  instance
    wf-iter : ⦃ _ : NonLim i ⦄ → wf (ℱ [_] ⟨ i ⟩∘ⁿ)
    wf-iter {n = zero} = infl< ℱ
    wf-iter {n = suc n} = pres< ℱ (wf-iter {n = n})
  iter : Func↾ NonLim
  iter i = lim (ℱ [_] ⟨ i ⟩∘ⁿ)
  iter-infl< : iter inflates _<_ within NonLim
  iter-infl< {(zero)} = z<l
  iter-infl< {suc x} = map (lim {n = 1}) (infl< ℱ)
```

```agda
_∘Suc : Infl↾ NonLim → Infl↾ (0 ≤_)
ℱ ∘Suc = mkInfl↾ (λ x → ℱ [ suc x ]) $ λ {x} →  begin-strict
    x                                           <⟨ zero₁ ⟩
    suc x                                       <⟨ infl< ℱ ⟩
    ℱ [ suc x ]                                 ∎ where open SubTreeReasoning
```

```agda
jump⟨_⟩ : (i : Ord) (ℱ : Infl↾ NonLim) ⦃ nl : NonLim i ⦄ → Normal
jump⟨ i ⟩ ℱ = ((ℱ ∘Suc) ⟨ ℱ [ i ] ⟩^)
```

```agda
jump : (ℱ : Infl↾ NonLim) → Normal
jump ℱ = jump⟨ 0 ⟩ ℱ
```

```agda
fixpt : Fixable → Fixable
fixpt ℱ = normal→fixable (jump (iterω ℱ)) infl where
  open InfiniteIteration
  instance _ = wf-iter ℱ
  infl : ((jump (iterω ℱ) [_]) ↾ NonLim) inflates _<_ within NonLim
  infl {(zero)} = iter-infl< ℱ
  infl {suc x} =                              begin-strict
    suc x                                     ≤⟨ s≤s {!   infl {x}  !} ⟩
    suc (jump (iterω ℱ) [ x ])                <⟨ infl< (iterω ℱ) ⟩
    iterω ℱ [ suc (jump (iterω ℱ) [ x ]) ]    ≈⟨ refl ⟩
    jump (iterω ℱ) [ suc x ]                  ∎ where open SubTreeReasoning
```

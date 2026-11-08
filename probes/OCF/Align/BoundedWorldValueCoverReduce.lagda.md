# 中Ω实际模型与保留底槽的末段

本篇校准两槽语义；u=0退化到已覆盖的旧第二地板，不计新强度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueCoverReduce where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
open import OCF.Align.FrozenInnerOuter using (same-add; same-mul)
open import OCF.Align.BoundedCompletionFiniteRunIf using (Rel; rz; rs; rl; ro)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (rel-add; floor-rel)
open import OCF.Align.BoundedWorldValueTwoSlot
open import OCF.Align.BoundedWorldValueCoverIf
open import OCF.Align.BoundedWorldValueIf
import OCF.Align.BoundedWorldValueRun as G
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedCompletionValueAcceptOld as Old
import OCF.Lean.Fold1If as I

rel-mul : ∀ {a b} → Rel hz a b → ∀ n → Rel hz (I.mul a n) (I.mul b n)
rel-mul p zero = p
rel-mul p (suc n) = rel-add (rel-mul p n) p
mid-up : ∀ {a b} → Rel hz a b → ∀ c → Rel hz (mid c (up a)) (Old.act b)
mid-up rz c = rs rz
mid-up (rs p) c = rl (rel-mul (mid-up p c))
mid-up (rl p) c = rl (λ n → mid-up (p n) c)
mid-up (ro {κ = inj₁ ()} p) c
mid-up (ro {κ = inj₂ _} p) c = ro (λ x y xy → mid-up (p x y xy) c)

low-up : ∀ {a b u v} → Rel hz a b → Same u v → ∀ c →
  Same (low u c (up a)) (T.fold v b)
low-up rz uv c = ss zz
low-up (rs p) uv c = ll (same-mul (low-up p uv c))
low-up (rl p) uv c = ll (λ n → low-up (p n) uv c)
low-up (ro {κ = inj₁ ()} p) uv c
low-up {u = u} {v} (ro {κ = inj₂ _} {f} {g} p) uv c = ll D.sums
  where
  WR : Cd → Wd U → Set
  WR x W = Same x (proj₂ W)
  branch : ∀ {x W a b} → WR x W → Same a b →
    Same (low x c (up (f a))) (T.fold (proj₂ W) (g b))
  branch r ab = low-up (p _ _ ab) r c
  sim : Simulation WR Same Same u (tt , v) u v (λ _ e → e) (λ _ e → tt , e)
    (λ x e → low x c (up (f e))) (λ W e → T.fold (proj₂ W) (g e))
    (λ x e → low x c (up (f e))) (λ W e → T.fold (proj₂ W) (g e))
  sim = record { worlds-start = uv ; coordinates-start = uv
    ; add-coordinate = same-add ; add-output = same-add
    ; update = λ _ r → r ; advance = branch ; emit = branch }
  module D = G.Run sim

coordinates : ∀ u n → Rel hz (Middle.ce u n) (Old.Pure.ce n)
coordinates u zero = floor-rel zero
coordinates u (suc n) = rel-add (coordinates u n) (mid-up (coordinates u n) (Middle.cw u n))
outputs : ∀ u n → Same (Middle.oo u n) (T.fold u (Old.Pure.ce n))
outputs u n = low-up (coordinates u n)
  (OCF.Align.BoundedWorldCoverRun.same-self u) (Middle.cw u n)
  where import OCF.Align.BoundedWorldCoverRun
```

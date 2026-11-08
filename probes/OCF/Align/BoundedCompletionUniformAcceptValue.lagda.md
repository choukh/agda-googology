# 全部有限 Ω 和的参照下界

每个阶段调用同一个带前缀的末段回灌定理，比较完整反馈链；
零叶、后继列错位和初始种子均显式保留。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformAcceptValue where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; ss; ll)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-mul)
open import OCF.Align.FrozenAbsorbSeed using (right-add)
open import OCF.Align.BoundedCompletionTerminalValueClosure using (seed-mono)
open import OCF.Align.BoundedNativeValueStrict using (terminal-positive)
import OCF.Align.BoundedCompletionUniformAcceptFamily as F
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.FrozenAbsorbNegUpper as P
import OCF.Align.BoundedCompletionPureAccept as Pure
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

Ω₁ : L.Ordᶜ (L.suc L.zero)
Ω₁ = L.Ω (L.suc L.zero)
high : ℕ → L.Ordᶜ (L.suc L.zero)
high zero = L.zero
high (suc n) = high n L.+ Ω₁
high-self : ∀ n → high n L.≅ high n
high-self zero = L.z≅
high-self (suc n) = L.add-≅ {σ = λ r → r} {σ′ = λ r → r} (high-self n) (L.Ω-refl (L.suc L.zero))
reference : ℕ → L.Ordᶜ L.zero
reference n = L.ψ⁰ (high n)

fold-tail : ∀ n b c → Same (T.fold b (F.stack n ⊞ up c)) (P.P (T.fold b (F.stack n)) c)
fold-tail n b hz = same-refl _
fold-tail n b (hs c) = ll (same-mul (fold-tail n b c))
fold-tail n b (hl f) = ll (λ j → fold-tail n b (f j))

module Advance (n : ℕ) (base : reference n V.≼ B.read (F.family n)) where
  A = F.family n
  tail : L.Ordᶜ L.zero → L.Ordᶜ (L.suc L.zero)
  tail c = high n L.+ L.up L.zero c
  Q : L.Ordᶜ L.zero → L.Ordᶜ L.zero
  Q c = L.ψ L.zero (λ r → r) (tail c)
  chain : ℕ → L.Ordᶜ L.zero
  chain k = iter Q (L.suc L.zero) k
  module Orbit = T.Orbit hz (λ c → F.stack n ⊞ up c)

  tail-bound : ∀ c → L.ψ⁰ (tail c) V.≼ B.read (P.P A (B.forget c))
  tail-bound L.zero = base
  tail-bound (L.suc c) = V.l≼ branch
    where
    branch : ∀ j → iter (L.ψ⁰ (tail c) L.+_) L.zero j V.≼ B.read (P.P A (hs (B.forget c)))
    branch zero = V.z≼
    branch (suc j) = V.≼l j (V.≼-trans (Pure.iter-mono _ _ (tail-bound c) (suc j))
      (V.≅→≼ (L.≅-sym (Pure.read-mul (P.P A (B.forget c)) j))))
  tail-bound (L.lim f) = V.l≼ (λ j → V.≼l j (tail-bound (f j)))

  q-bound : ∀ c → B.forget (Q c) ≤ᵛ P.P A (B.forget c)
  q-bound c = B.reference-lower-reflect (V.≼-trans
    (V.≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r}
      (L.add-≅ {σ = λ r → r} {σ′ = λ r → r} (high-self n)
        (L.upˡ {r = L.zero} (L.upʳ {r = L.zero} (L.≅-refl⁰ c))))))) (tail-bound c))

  branch-lower : ∀ b c → P.P A c ≤ᵛ T.fold b (F.stack n ⊞ up c)
  branch-lower b c = ≤-trans (P.mono (seed-mono (F.stack-self n) z≤) (≤-refl c))
    (same-value (OCF.Lean.FrozenWorldLift.same-sym (fold-tail n b c)))

  output-lower : ∀ k → P.P A (Orbit.C.ce k) ≤ᵛ Orbit.C.oo k
  output-lower k = branch-lower _ _

  coordinates : ∀ k → B.forget (chain k) ≤ᵛ Orbit.C.ce (suc k)
  coordinates zero = ≤-trans (terminal-positive hz (F.stack n)) (right-add hz A)
  coordinates (suc k) = ≤-trans (q-bound (chain k))
    (≤-trans (P.mono (≤-refl A) (coordinates k))
      (≤-trans (output-lower (suc k)) (right-add (Orbit.C.ce (suc k)) (Orbit.C.oo (suc k)))))

  last : ∀ k → Orbit.C.oo k ≤ᵛ Orbit.C.oO k
  last zero = ≤-refl _
  last (suc k) = right-add (Orbit.C.oO k) (Orbit.C.oo (suc k))
  result : B.forget (reference (suc n)) ≤ᵛ F.family (suc n)
  result = l≤ (λ k → ≤l (suc k) (≤-trans
    (B.reference-lower-reflect (tail-bound (chain k)))
    (≤-trans (P.mono (≤-refl A) (coordinates k))
      (≤-trans (output-lower (suc k)) (last (suc k))))))

reference-bound : ∀ n → reference n V.≼ B.read (F.family n)
reference-bound zero = V.≼-refl _
reference-bound (suc n) = B.reference-lower (Advance.result n (reference-bound n))
whole-reference : L.Ordᶜ L.zero
whole-reference = L.lim reference
whole-bound : B.forget whole-reference ≤ᵛ hl F.family
whole-bound = l≤ (λ n → ≤l n (B.reference-lower-reflect (reference-bound n)))
```

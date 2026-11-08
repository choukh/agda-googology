# 动态双 Ω 的 Ω₁ 加法参照下界

记号验收专用。比较目标是原 Level.ψ⁰(Ω₁+Ω₁)，不把动态折叠
当作该参照的定义。参照链无累加，从1起步；模型链从0起步且累加，
以下按错一项覆盖整链。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionOutputAcceptPair where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l; s≤s)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value; same-sym)
open import OCF.Align.FrozenOutputModel using (same-trans)
open import OCF.Align.FrozenAbsorbSeed using (right-add)
import OCF.Align.FrozenAbsorbNegUpper as P
import OCF.Align.FrozenOutputIf as If
import OCF.Align.BoundedCompletionValueAcceptPair as Actual
import OCF.Align.BoundedCompletionValueAcceptPairStrength as Strength
import OCF.Align.BoundedCompletionCalibrateAccept as Cal
import OCF.Align.BoundedCompletionPureAccept as Pure
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

one : Cd
one = hs hz
module Base = P.Orbit one hz
D : Cd
D = Base.value
module Frozen = P.Orbit D hz
module Upper = P.Upper one (≤-refl one)

Ω₁ : L.Ordᶜ (L.suc L.zero)
Ω₁ = L.Ω (L.suc L.zero)
reference : L.Ordᶜ L.zero
reference = L.ψ⁰ (Ω₁ L.+ Ω₁)
tail : L.Ordᶜ L.zero → L.Ordᶜ (L.suc L.zero)
tail c = Ω₁ L.+ L.up L.zero c
Q : L.Ordᶜ L.zero → L.Ordᶜ L.zero
Q c = L.ψ L.zero (λ r → r) (tail c)
chain : ℕ → L.Ordᶜ L.zero
chain n = iter Q (L.suc L.zero) n

base-bound : L.ψ⁰ Ω₁ V.≼ B.read D
base-bound = V.≼-trans Cal.reference≤A (B.read-mono
  (same-value (same-trans (same-sym Strength.first-same) (P.run-initial one If.changing hz))))

tail-bound : ∀ c → L.ψ⁰ (tail c) V.≼ B.read (P.P D (B.forget c))
tail-bound L.zero = base-bound
tail-bound (L.suc c) = V.l≼ branch
  where
  branch : ∀ n → iter (L.ψ⁰ (tail c) L.+_) L.zero n V.≼ B.read (P.P D (hs (B.forget c)))
  branch zero = V.z≼
  branch (suc n) = V.≼l n (V.≼-trans (Pure.iter-mono _ _ (tail-bound c) (suc n))
    (V.≅→≼ (L.≅-sym (Pure.read-mul (P.P D (B.forget c)) n))))
tail-bound (L.lim f) = V.l≼ (λ n → V.≼l n (tail-bound (f n)))

q-bound : ∀ c → B.forget (Q c) ≤ᵛ P.P D (B.forget c)
q-bound c = B.reference-lower-reflect (V.≼-trans
  (V.≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r}
    (L.add-≅ {σ = λ r → r} {σ′ = λ r → r}
      (L.Ω-refl (L.suc L.zero))
      (L.upˡ {r = L.zero} (L.upʳ {r = L.zero} (L.≅-refl⁰ c)))))))
  (tail-bound c))

positive : one ≤ᵛ D
positive = ≤l 0 (≤-refl one)
coordinates : ∀ n → B.forget (chain n) ≤ᵛ Frozen.C.ce (suc n)
coordinates zero = ≤-trans positive (right-add hz D)
coordinates (suc n) = ≤-trans (q-bound (chain n))
  (≤-trans (P.mono (≤-refl D) (coordinates n))
    (right-add (Frozen.C.ce (suc n)) (Frozen.C.oo (suc n))))

last : ∀ n → Frozen.C.oo n ≤ᵛ Frozen.C.oO n
last zero = ≤-refl _
last (suc n) = right-add (Frozen.C.oO n) (Frozen.C.oo (suc n))

reference≤frozen : B.forget reference ≤ᵛ Frozen.value
reference≤frozen = l≤ (λ n → ≤l (suc n) (≤-trans
  (B.reference-lower-reflect (tail-bound (chain n)))
  (≤-trans (P.mono (≤-refl D) (coordinates n)) (last (suc n)))))

reference≤next : B.forget reference ≤ᵛ Strength.Strict.BB₀
reference≤next = ≤-trans reference≤frozen
  (≤-trans Upper.upper-pure (same-value (same-sym
    (P.ActualUpper.target-same one (≤-refl one)))))

strict-reference≤pair : hs (B.forget reference) ≤ᵛ Actual.pair-output
strict-reference≤pair = ≤-trans (s≤s reference≤next)
  (≤-trans Strength.Strict.strict-pair (same-value Strength.pair-same))
```

这给真实动态双 Ω 输出的参照后继下界；尚未证明上界或标签，二者不由
Level 表达式的外观推出。

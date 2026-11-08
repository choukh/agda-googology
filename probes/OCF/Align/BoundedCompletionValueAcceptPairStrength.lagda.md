# 动态双 Ω 下界的严格种子推进

复用既有严格双 Ω 定理，但先证明它的模型 run 与这里的原末段 fold
在实际输入上结构一致。零点取 1，而非旧第二分量研究中的 TΩ1。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionValueAcceptPairStrength where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-mul)
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; mul; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Align.BoundedCompletionFiniteRunIf
open import OCF.Align.BoundedCompletionFiniteRunClosure
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.FrozenOutputIf as If
import OCF.Align.FrozenOutputSim as Sim
import OCF.Align.FrozenAbsorbPair as Pair
import OCF.Align.FrozenAbsorbNegUpper as Pure
import OCF.Align.BoundedCompletionValueAcceptPair as Actual
import OCF.Align.BoundedCompletionFinitePlaceSample as Sample
import OCF.Align.BoundedNativeCompletionClosed as C
import OCF.Lean.Fold1 as Old
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.FrozenAbsorbSeed using (right-add)

one : Cd
one = hs hz
module M = If.Model one
module Strict = Pair.Pair one (≤-refl one)

run-bridge : ∀ {a b} → Rel hz a b → ∀ {u v} → Same u v →
  Same (M.run If.changing u a) (T.fold v b)
run-bridge rz uv = ss zz
run-bridge (rs p) uv = ll (same-mul (run-bridge p uv))
run-bridge (rl p) uv = ll (λ n → run-bridge (p n) uv)
run-bridge (ro {κ = inj₁ ()} p) uv
run-bridge {a = hΩ (inj₂ _) f} {b = hΩ (inj₂ _) g} (ro p) {u} {v} uv = ll D.sums
  where
  WR : Cd → Wd (step S⊥) → Set
  WR c w = Same c (proj₂ w)
  branch : ∀ {w W x y} → WR w W → Same x y →
    Same (M.run If.changing w (f x)) (T.fold (proj₂ W) (g y))
  branch r xy = run-bridge (p _ _ xy) r
  module D = Sim.Sim WR u (tt , v) uv u v uv
    (λ _ e → e) (λ _ e → tt , e) (λ r xy → xy)
    (λ w e → M.run If.changing w (f e)) (λ W e → T.fold (proj₂ W) (g e))
    (λ w e → M.run If.changing w (f e)) (λ W e → T.fold (proj₂ W) (g e)) branch branch

pair-same : Same (M.run If.changing hz Pair.pair) Actual.pair-output
pair-same = run-bridge (rel-add (floor-rel zero) (floor-rel zero)) zz

strict≤normalized : hs Strict.BB₀ ≤ᵛ Sample.normalized 1
strict≤normalized = ≤-trans Strict.strict-pair
  (≤-trans (same-value pair-same) Actual.pair≤normalized)
strict≤C : hs Strict.BB₀ ≤ᵛ C.tree
strict≤C = ≤-trans strict≤normalized (Sample.normalized-below-C 1)

-- B₀ 就是旧第一地板，先通过原fold桥识别，不凭读法。
first-same : Same Strict.B₀ Old.TΩ1
first-same = run-bridge (floor-rel zero) zz

module Orbit = Pure.Orbit one Strict.B₀
coordinates : ∀ n → mul Strict.B₀ n ≤ᵛ Orbit.C.ce n
outputs : ∀ n → Strict.B₀ ≤ᵛ Orbit.C.oo n
coordinates zero = ≤-refl _
coordinates (suc n) = add-mono (coordinates n) (outputs n)
outputs n = ≤-trans (base-coordinate n)
  (Pure.infl one (≤-refl one) (Orbit.C.ce n))
  where
  base-coordinate : ∀ n → Strict.B₀ ≤ᵛ Orbit.C.ce n
  base-coordinate zero = ≤-refl _
  base-coordinate (suc n) = ≤-trans (base-coordinate n)
    (OCF.Lean.Fold1Base.≤⊞ _ _)

last : ∀ n → Orbit.C.oo n ≤ᵛ Orbit.C.oO n
last zero = ≤-refl _
last (suc n) = right-add (Orbit.C.oO n) (Orbit.C.oo (suc n))

multiple≤next : hl (mul Strict.B₀) ≤ᵛ Strict.BB₀
multiple≤next = ≤-trans (l≤ (λ n → ≤l n (≤-trans
  (≤-trans (coordinates n) (Pure.infl one (≤-refl one) (Orbit.C.ce n)))
  (last n))))
  (same-value (same-sym (Pure.run-initial one If.changing Strict.B₀)))
```

进一步与已交付的旧下界比较：原第二样本严格越过旧 TΩ1 的 ω 倍。
这是实际动态双 Ω 的后果，并未将它命名为 ψ₀(Ω₂)。

```agda
open import Data.Empty using (⊥)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)

old-multiple≤next : hl (mul Old.TΩ1) ≤ᵛ Strict.BB₀
old-multiple≤next = ≤-trans (l≤ (λ n → ≤l n
  (same-value (same-mul (same-sym first-same) n)))) multiple≤next

strict-old-multiple≤normalized : hs (hl (mul Old.TΩ1)) ≤ᵛ Sample.normalized 1
strict-old-multiple≤normalized = ≤-trans (s≤s old-multiple≤next) strict≤normalized

strict-old-multiple≤C : hs (hl (mul Old.TΩ1)) ≤ᵛ C.tree
strict-old-multiple≤C = ≤-trans strict-old-multiple≤normalized (Sample.normalized-below-C 1)

no-normalized-old-multiple-bound : Sample.normalized 1 ≤ᵛ hl (mul Old.TΩ1) → ⊥
no-normalized-old-multiple-bound p = ¬s≤ᵛ (hl (mul Old.TΩ1))
  (≤-trans strict-old-multiple≤normalized p)
```

尚未比较整个旧 TΩ2 与第二样本：上文旧轨道从 floor0 起步，新轨道
从1起步而每一步注入 Ω 前缀；需证明坐标及输出部分和的错位覆盖。
这里没有用输入高层值序的普遍折叠单调来省去此义务。

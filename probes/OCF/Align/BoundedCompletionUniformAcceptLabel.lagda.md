# 旧第二地板的 Ω₁·ω 具名下界

有限 Ω 和先按结构重新结合，再经 ψ⁰ 的结构同余；不使用高层值序
上的 ψ⁰ 单调。最终 Lab 来自已有 Generic 的统一标签定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformAcceptLabel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Unit using (tt)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
import OCF.Align.BoundedCompletionUniformAcceptFamily as Family
import OCF.Align.BoundedCompletionUniformAcceptValue as Value
import OCF.Align.BoundedCompletionOutputCoverRun as Cover
import OCF.Align.BoundedNativeCompletionClosed as C
import OCF.Lean.Fold1 as Old
import OCF.Align.Level as L
import OCF.Align.EBO as E
import OCF.Align.Label as Labels
import OCF.Align.Correspond as Correspond
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.OCFSpecBase as V
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

zero-pure : ∀ {a b : L.Ordᶜ L.zero} → a L.≅ b →
  L.add (L.zero {ℓ = L.suc L.zero}) L.suc a L.≅ b
zero-pure L.z≅ = L.z≅
zero-pure (L.s≅ p) = L.s≅ (zero-pure p)
zero-pure (L.l≅ p) = L.l≅ (λ n → zero-pure (p n))

assoc-pure : ∀ {a b : L.Ordᶜ (L.suc L.zero)} → a L.≅ a → b L.≅ b →
  ∀ {c d : L.Ordᶜ L.zero} → c L.≅ d →
  L.add (a L.+ b) L.suc c L.≅ (a L.+ L.add b L.suc d)
assoc-pure aa bb L.z≅ = L.add-≅ {σ = λ r → r} {σ′ = λ r → r} aa bb
assoc-pure aa bb (L.s≅ p) = L.s≅ (assoc-pure aa bb p)
assoc-pure aa bb (L.l≅ p) = L.l≅ (λ n → assoc-pure aa bb (p n))

rotate : ∀ n → Value.high (suc n) L.≅ (Value.Ω₁ L.+ Value.high n)
rotate zero = L.lᵢ≅ L.z≅ (λ x y p → L.upʳ {r = L.zero} (zero-pure p))
rotate (suc n) = L.lᵢ≅ L.z≅ (λ x y p → L.≅-trans
  (L.add-≅ {σ = L.suc} {σ′ = L.suc} (rotate n) p)
  (assoc-pure (L.Ω-refl (L.suc L.zero)) (Value.high-self n) (L.≅-refl⁰ y)))

left-agree : ∀ n → iter (Value.Ω₁ L.+_) L.zero n L.≅ Value.high n
left-agree zero = L.z≅
left-agree (suc n) = L.≅-trans
  (L.add-≅ {σ = λ r → r} {σ′ = λ r → r} (L.Ω-refl (L.suc L.zero)) (left-agree n))
  (L.≅-sym (rotate n))

reference : L.Ordᶜ L.zero
reference = L.ψ⁰ (L.lim (iter (Value.Ω₁ L.+_) L.zero))
reference-agree : reference L.≅ Value.whole-reference
reference-agree = L.l≅ (λ n → L.ψ⁰-≅ (left-agree n))

S = Labels.St 0
module G = Labels.GS S
term : E.T
term = E.ψ [] (E.ψ (E.natT 1) (E.natT 1) ∷ []) ∷ []
one-d : G.𝔸 (E.natT 1)
one-d = G.a∷ (G.aψ (Labels.System.s0 S) G.a[]) G.a[]
argument : G.𝔸 (E.ψ (E.natT 1) (E.natT 1) ∷ [])
argument = G.a∷ (G.aψ (Labels.sγ 0) one-d) G.a[]
derivation : G.𝔸 term
derivation = G.a∷ (G.aψ (Labels.System.s0 S) argument) G.a[]

inner-agree : L.lim (iter (Value.Ω₁ L.+_) L.zero) L.≅ G.⟦ argument ⟧ᵃ
inner-agree = G.node-≅ (Labels.System.inA S (Labels.sγ 0))
  {p = L.zero} {σ = λ r → r} {X = L.suc (L.zero {ℓ = L.suc (L.suc L.zero)})}
  (L.s≅ L.z≅)
  (L.≅-trans (L.s≅ L.z≅) (Labels.Tree.top‴ S (Labels.System.inA S (Labels.System.s0 S))
    (Labels.System.S0 S (Labels.System.s0 S)) {K = L.zero} {a = L.zero} {b = L.zero} L.z≅))

reference-label : Correspond.Lab reference term
reference-label = G.lab reference derivation
  (Labels.Tree.top‴ S (Labels.System.inA S (Labels.System.s0 S))
    (Labels.System.S0 S (Labels.System.s0 S)) inner-agree)

reference≤old2 : B.forget reference ≤ᵛ Old.TΩ (num 2) tt
reference≤old2 = ≤-trans (B.forget-mono (V.≅→≼ reference-agree))
  (≤-trans Value.whole-bound Family.whole≤old2)
reference≤C : B.forget reference ≤ᵛ C.tree
reference≤C = ≤-trans reference≤old2 Cover.old2≤C
```

具名结论为 ψ₀(Ω₁·ω) ≤ Old.TΩ2 ≤ C。这是下界，不是 Old.TΩ2
的精确值；没有据此认定或否定 ψ₀(Ω₂) 的读法。

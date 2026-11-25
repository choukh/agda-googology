# 第 1 站保持连出口
验收文件；编译定理：`folded¹` 直接给实际底上的关系与出口证据，`low1` 实填 `LowAt 1`。
来源：有限层保持用 `YiTBFam.sΩ-LF`，取支用 `YiLTLift.upL`，根累加用 `YiHCRel.G⁰.m-cum`。
实际链第 1 点是两次 `next⁺`；仅用这一点的两次第 0 支，无 `Lift₁` 前提，不给全塔保持。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiS1Low where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ; h₁)
open import OCF.Lean.YiMTTab using (rbᶻ)
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiHCCheck as HC
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiLTLift as LL
open import OCF.Lean.YiRBFam using (tu; OKB)
open import OCF.Lean.YiKPInst using (zq; zpt)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiGIInst using (baseᴱ; betaᴱ)
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiCNKeel as CN
import OCF.Lean.YiGIRel as GR
open import OCF.Lean.YiS1Exit using (QEx; ex-upL0; ex-right)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ)
open import OCF.Lean.YiExSuff using (module ExSuff)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)

row1 : E.T
row1 = E.ψ [] (E.Ωt (E.natT 1)) ∷ []
F : zero ≤ tw 1 → Tr⁺ zero → Tr (tw 1) → Tr⁺ zero
F = ψ (tw 1) (Ok-tw 1) (rbᶻ (tw 1)) (baseᴱ 1) zero
G : Tr zero → Tr (tw 1)
G c = proj₁ (upz {s = sΩ zero} {h = h₁} c (Ωt (h₁ c)))
idx : ℕ → Tr zero
idx = iter (λ c → proj₁ (F (ink self) (baseᴱ 1 zero (ink self)) (G c))) zero
index1-shape : idx 1 ≡ proj₁ (next⁺ (next⁺ (Ωt zero)))
index1-shape = refl

q1K : (o : Ok (fn 1)) (r : Rb (fn 1)) (v : zero ≤ fn 1) → LL.ZP (fn 1) v → (B : Base (fn 1)) → OKB B → (β : Tr⁺ zero) → K.M⁰ row1 (proj₁ (ψ (fn 1) o r B zero v β (proj₁ (Ωt (fn 1)))))
q1K o r v zv B ok β = subst (λ v → K.M⁰ row1 (proj₁ (ψ (fn 1) o r B zero v β (proj₁ (Ωt (fn 1)))))) (sym (LL.zp-pt 1 zv))
  (TF.sΩ-LF o r (tu (zq 0)) B β ok (K.pos⁰ (proj₁ β) (proj₂ β)))
q1 : LL.Q row1 (fn 1)
q1 o r v zv B ok β hβ = HC.of⁰ (q1K o r v zv B ok β)

inner outer : ℕ → L
inner n = h₁ (iter (suc zero +_) (suc zero) n)
outer n = h₁ (iter (proj₁ (next⁺ (Ωt zero)) +_) (proj₁ (next⁺ (Ωt zero))) n)
q-mid : LL.Q row1 (h₁ (proj₁ (next⁺ (Ωt zero))))
q-mid = LL.upL {g = inner} 0 q1
q-idx : LL.Q row1 (h₁ (idx 1))
q-idx = LL.upL {g = outer} 0 q-mid

child : H.M⁰ row1 (proj₁ (F (z≤ (tw 1)) (betaᴱ 1) (G (idx 1))))
child = q-idx (proj₂ (Ok-tw 1) (idx 1)) (proj₂ (rbᶻ (tw 1)) (idx 1)) (z≤ (h₁ (idx 1))) (LL.zp-z (h₁ (idx 1)))
  (λ i u → baseᴱ 1 i (inc (idx 1) u))
  (λ i u → TF.ψ-⊵ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) i (inc 1 (inc (idx 1) u)) (Ωt i) (proj₁ (upz {s = sL} {h = tw} 0 (Ωt zero))))
  (betaᴱ 1) (H.pos⁰ (proj₁ (betaᴱ 1)) (proj₂ (betaᴱ 1)))

ex-q1 : QEx q1
ex-q1 o r v zv B ok β hβ = HC.ex-of⁰ (q1K o r v zv B ok β)

ex-q-idx : QEx q-idx
ex-q-idx = ex-upL0 {g = outer} {q = q-mid} (ex-upL0 {g = inner} {q = q1} ex-q1)

ex-child : H.Exᴴ child
ex-child = ex-q-idx (proj₂ (Ok-tw 1) (idx 1)) (proj₂ (rbᶻ (tw 1)) (idx 1)) (z≤ (h₁ (idx 1))) (LL.zp-z (h₁ (idx 1)))
  (λ i u → baseᴱ 1 i (inc (idx 1) u))
  (λ i u → TF.ψ-⊵ Λ Ok-Λ (rbᶻ Λ) (B₀ Λ) i (inc 1 (inc (idx 1) u)) (Ωt i) (proj₁ (upz {s = sL} {h = tw} 0 (Ωt zero))))
  (betaᴱ 1) (H.pos⁰ (proj₁ (betaᴱ 1)) (proj₂ (betaᴱ 1)))

parts : ℕ → Tr⁺ zero
parts n = F (z≤ (tw 1)) (betaᴱ 1) (G (idx n))

folded : H.M⁰ row1 (proj₁ (F (z≤ (tw 1)) (betaᴱ 1) (proj₁ (Ωt (tw 1)))))
folded = H.G⁰.m-cum parts 1 child

ex-folded : H.Exᴴ folded
ex-folded = ex-right (proj₁ (parts 0)) child ex-child

folded¹ : Σ (GR.R zero (Keel⁻.row keelᴱ 1) (Keel⁻.twc keelᴱ 1)) H.Exᴴ
folded¹ = folded , ex-folded

low1 : CN.LowAt 1
low1 _ = folded¹
```

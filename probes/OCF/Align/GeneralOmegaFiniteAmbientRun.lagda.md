# 原有限observer保持固定ambient读回

验收专用。保持律对全部原Within路径以及全部有证输入统一量化。
目标和反馈层使用同一个原源界；原up只更新σ。Ω分派严格消费
FiniteCompare的原分类见证，反馈仍为原floor起点的无累加迭代。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteAmbientRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaFiniteObserveIf as I
import OCF.Lean.GeneralOmegaFiniteObserveRun as R
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaFiniteRank using (nat; ambient)
open import OCF.Align.GeneralOmegaFiniteAmbientIf
open import OCF.Align.GeneralOmegaFiniteAmbientClosure using (mul)
open import OCF.Align.GeneralOmegaFiniteAmbientCoord using (coord-tr⁻; coord-cong; coord-self)
import OCF.Align.GeneralOmegaFiniteCompare as C
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)

index-eq : ∀ {i j} → i ≡ j → nat i L.≅ᴵ nat j
index-eq {i} e = subst (λ k → nat i L.≅ᴵ nat k) e (L.≅ᴵ-refl (nat i))
tr-cast : ∀ {i j} (e : i ≡ j) {x : L.Ordᶜ (nat j)} → x L.≅ x →
  L.tr⁻ (index-eq e) x L.≅ C.cast (sym e) x
tr-cast refl sx = L.tr⁻-≅ (L.≅ᴵ-refl _) sx

preserve : ∀ {B m ℓ} (p : I.Within B m) {σ : L.Simᴵ ℓ (nat (suc B))} {a b} →
  Read B σ a b → Read m (canonical m) (L.ψ (ambient p) σ a) (R.observe p b)
preserve {m = m} p rz = floor-read m
preserve p (rs r) = rl (mul (preserve p r))
preserve p (rl r) = rl (λ n → preserve p (r n))
preserve p (ru-s r) = preserve p r
preserve p (ru-l r) = preserve p r
preserve {m = m} p (rc e r) = rc (L.ψ-≅ (L.≅ᴵ-refl (nat m)) e) (preserve p r)
preserve {B} {m} p {σ} (ro κ q {f} {g} align sa r)
  with L.ψ-≅ {p = ambient p} {σ = σ} {p′ = ambient p} {σ′ = σ}
    (L.≅ᴵ-refl (nat m)) sa
... | sf rewrite align with I.view p κ | C.match p κ
... | I.keep κ′ fr | C.kept eq dec move rewrite dec =
  ro κ′ (bound m κ′) refl sf
    (λ x e c → subst
      (λ z → Read m (canonical m)
        (L.ψ (ambient p) σ (f (L.into (L.<→◃ q) (L.tr⁻ (index-eq eq) z))))
        (R.observe p (g (fr e))))
      (sym (L.out-into (L.<→◃ (bound m κ′)) x))
      (preserve p (r (L.tr⁻ (index-eq eq) x) (fr e)
        (coord-cong B κ (tr-cast eq (coord-self m κ′ c)) (move c)))))
... | I.collapse k path to | C.cut eq collapsed move rewrite sym eq
  with C.decision p κ | collapsed
... | inj₂ (inj₁ v) | C.above .v = rl outputs
  where
  old : ℕ → L.Ordᶜ (nat (rank B κ))
  old = iter (λ x → L.ψ q (λ z → z) (f (L.into (L.<→◃ q) x))) (L.Ω (nat (rank B κ)))
  new : ℕ → HB (I.F (rank B κ))
  new = I.iterate (λ e → R.observe path (g (to e))) (I.floor (rank B κ))
  coordinates : ∀ n → Read (rank B κ) (canonical (rank B κ)) (old n) (new n)
  coordinates zero = floor-read (rank B κ)
  coordinates (suc n) = rc (L.ψ-≅ (L.≅ᴵ-refl (nat (rank B κ)))
    (self (r (old n) (to (new n)) (move (coordinates n)))))
    (preserve path (r (old n) (to (new n)) (move (coordinates n))))
  outputs : ∀ n → Read m (canonical m)
    (L.ψ (ambient p) σ (f (L.into (L.<→◃ q) (old n))))
    (R.observe p (g (to (new n))))
  outputs n = preserve p (r (old n) (to (new n)) (move (coordinates n)))
... | inj₂ (inj₂ v) | C.same .v = rl outputs
  where
  old : ℕ → L.Ordᶜ (nat (rank B κ))
  old = iter (λ x → L.ψ q (λ z → z) (f (L.into (L.<→◃ q) x))) (L.Ω (nat (rank B κ)))
  new : ℕ → HB (I.F (rank B κ))
  new = I.iterate (λ e → R.observe path (g (to e))) (I.floor (rank B κ))
  coordinates : ∀ n → Read (rank B κ) (canonical (rank B κ)) (old n) (new n)
  coordinates zero = floor-read (rank B κ)
  coordinates (suc n) = rc (L.ψ-≅ (L.≅ᴵ-refl (nat (rank B κ)))
    (self (r (old n) (to (new n)) (move (coordinates n)))))
    (preserve path (r (old n) (to (new n)) (move (coordinates n))))
  outputs : ∀ n → Read m (canonical m)
    (L.ψ (ambient p) σ (f (L.into (L.<→◃ q) (old n))))
    (R.observe p (g (to (new n))))
  outputs n = preserve p (r (old n) (to (new n)) (move (coordinates n)))
```

# 统一形 (四): $\psi_0(\Omega_{\Omega\cdot2})$ 的路径检验与记号侧停点

> 接 [Uniform4Two](Uniform4Two.lagda.md). `firstBad 6`: 宽 3 深 6 的全部路径上, 树的种类与 EBO 的基本列一致 (有限检验). `¬NF-Ω·2`: $\psi_0(\Omega_{\Omega\cdot2})$ 不在 `NF₁` 里, 因为 `Sb` 只含 "可数" 与 "$\Omega+$ 可数", 而现行的 `L0` 与 `limᴸ` 都以 `NF₁` 为前提, 单调性也从它来. 所以 `Lab₀` 这个陈述可写, 现有的证明路线走不到顶; 链点 $\psi_0(\Omega_{\Omega+\theta})$ 都在 `NF₁` 里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4TwoWalk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; walkˢ; kind; Kind; kz; ks; kl; kĉ; kc; sqˢ)
import OCF.Align.EBO as E
open E using (T; PT; fsn; cof; c0; c1; cω; cΩ; sucT; 𝟏; Ωt) renaming (ψ to ψᵗ)
open import OCF.Align.StandardOmega using (walk; NF₁; n∷; nψ; sC; sΩ)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; ψ₀ᵗ)
open import OCF.Align.Uniform4Head using (Ωp)
open import OCF.Align.Uniform4Two
open import OCF.Align.Uniform4Expt using (one)

tΩ·2 : T
tΩ·2 = ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ []))

¬NF-Ω·2 : NF₁ tΩ·2 → ⊥
¬NF-Ω·2 (n∷ (nψ _ _ (n∷ (nψ _ (sC ()) _ _) _ _) _) _ _)
¬NF-Ω·2 (n∷ (nψ _ _ (n∷ (nψ _ (sΩ ()) _ _) _ _) _) _ _)

ev₂ : Ev one ((fz ⊔ fk zero) ⊔ fk zero)
ev₂ = (tt , (λ q → q)) , (λ q → q)

T₂ᵀ : Ordˢ zero
T₂ᵀ = TΩ·2 ev₂ zero

_ : kind T₂ᵀ ≡ kc one
_ = refl

lastArg : T → Bool
lastArg [] = false
lastArg (x ∷ y ∷ ys) = lastArg (y ∷ ys)
lastArg (ψᵗ u [] ∷ []) = false
lastArg (ψᵗ u (a ∷ as) ∷ []) with cof (a ∷ as)
... | cΩ [] = true
... | _ = false

agree : Kind → T → Bool
agree kz [] = true
agree kz (_ ∷ _) = false
agree ks t with cof t
... | c1 = true
... | _ = false
agree kl t with cof t
... | cω = true
... | _ = false
agree kĉ t with cof t
... | cω = true
... | _ = false
agree (kc _) t = lastArg t

kids : ℕ → (Ordˢ zero → T → Bool) → Ordˢ zero → T → Bool
kids d r x t with kind x
... | kl = r (sqˢ x 0) (fsn t 0) ∧ (r (sqˢ x 1) (fsn t 1) ∧ r (sqˢ x 2) (fsn t 2))
... | kĉ = r (sqˢ x 0) (fsn t 0)
... | kc _ = r (sqˢ x 0) (fsn t 0)
... | _ = true

chk : ℕ → Ordˢ zero → T → Bool
chk zero x t = true
chk (suc d) x t = agree (kind x) t ∧ kids d (chk d) x t

firstBad : ℕ → Ordˢ zero → T → List (List ℕ)
firstBad zero x t = []
firstBad (suc d) x t with agree (kind x) t
... | false = [] ∷ []
... | true with kind x
... | kl = pre 0 (firstBad d (sqˢ x 0) (fsn t 0)) ++ (pre 1 (firstBad d (sqˢ x 1) (fsn t 1)) ++ pre 2 (firstBad d (sqˢ x 2) (fsn t 2)))
  where
  pre : ℕ → List (List ℕ) → List (List ℕ)
  pre n [] = []
  pre n (p ∷ ps) = (n ∷ p) ∷ pre n ps
... | kĉ = pre0 (firstBad d (sqˢ x 0) (fsn t 0))
  where
  pre0 : List (List ℕ) → List (List ℕ)
  pre0 [] = []
  pre0 (p ∷ ps) = (0 ∷ p) ∷ pre0 ps
... | kc _ = pre0 (firstBad d (sqˢ x 0) (fsn t 0))
  where
  pre0 : List (List ℕ) → List (List ℕ)
  pre0 [] = []
  pre0 (p ∷ ps) = (0 ∷ p) ∷ pre0 ps
... | _ = []

_ : firstBad 6 T₂ᵀ tΩ·2 ≡ []
_ = refl
```

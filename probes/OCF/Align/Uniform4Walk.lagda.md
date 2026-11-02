# 统一形 (四): 数据树与 EBO 的路径检验

> 接 [Uniform4Base](Uniform4Base.lagda.md), [Uniform4Expt](Uniform4Expt.lagda.md). `T₂ = ψ̄ (Ω̇ 2)`. (A)、(B) 咬人的两条路径上, 数据树给 `kl`, 与 EBO 一致 (朴素帧给 `kc one`). `firstBad 7`: 宽 3 深 7 的全部路径上, 树的种类与 $\psi_0(\Omega_{\Omega+2})$ 的基本列一致 (链只走第 0 点). 这只是有限检验; 定理在 [Uniform4Label](Uniform4Label.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Uniform4Walk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; walkˢ; kind; Kind; kz; ks; kl; kĉ; kc; sqˢ)
import OCF.Align.EBO as E
open E using (T; PT; fsn; cof; c0; c1; cω; cΩ; sucT; 𝟏) renaming (ψ to ψᵗ)
open import OCF.Align.StandardOmega using (walk)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.DecoupleBase using (ΩΩ)
open import OCF.Align.OmegaPlus1Base using (Ω⁺¹)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; _⊔_; Ev)
open import OCF.Align.Uniform4Base
open import OCF.Align.Uniform4Expt using (Ω⁺²; t₂; ψ₁; one)

ev₁ : Ev one Fl
ev₁ = tt , (λ q → q)

T₂ : Ordˢ zero
T₂ = ψ̄ (Ω̇ 2) ev₁ zero

T₁ : Ordˢ zero
T₁ = ψ̄ (Ω̇ 1) ev₁ zero

_ : kind T₂ ≡ kl
_ = refl

-- (B) 路径: EBO 处 ψ₀(ψ₁(ψ_Ω(Ω⁺))), cof ω, 非闭包
_ : kind (walkˢ T₂ (1 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ kl
_ = refl

-- (A) 路径
_ : kind (walkˢ T₂ (1 ∷ 0 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ 0 ∷ 0 ∷ 1 ∷ [])) ≡ kl
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

_ : firstBad 7 T₂ t₂ ≡ []
_ = refl

_ : firstBad 7 T₁ (ψᵗ [] (Ω⁺¹ ∷ []) ∷ []) ≡ []
_ = refl
```

# 塔第 2 项的关系与孩子接口
> 验收文件（读记号）。条件定理：`Lift₂` 给出 Ω 树的关系，`Lift₁` 给出标准底；不改树、折叠或合法性。
> 来源：接口、推导域 `Sp` 与 Ω 树的构造照 `YiLTKid`；根槽位改用 `M¹ (Ω_η) c`，对应参照的奇异共尾基本列。
> 不声称已填 `Lift₂` 或完整 `Lift₁`；保持与出口见 `YiKQFold`、`YiKQSuff`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKQRel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (Mᴴ; M⁰; mz; m1; mL; mΩ; mU; mw; mc; module G⁰; module Gen)
open import OCF.Lean.YiRBFam using (OKB)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Lean.YiLTKid as One
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiANFam using (ψᴺ)
module A = One.Sem (rbᶻ (tw 1))
module G¹ = Gen {Sig (tw 1)} {A.Low¹} {A.Kdˢ} {A.Nu¹}
ℓ² : L
ℓ² = tw 2
h₂ : Tr (tw 1) → L
h₂ c = tw 1 ⊕ ↑ (tw 1) c
o² : Ok ℓ²
o² = Ok-tw 2
r² : Rb ℓ²
r² = rbᶻ ℓ²
Pc : (c : Tr (tw 1)) → zero ≤ h₂ c → Set
Pc c v = (v ≡ z≤ (h₂ c)) ⊎ (v ≡ z≤ (tw 1) ∙ proj₂ (proj₁ o²) c)
record Kid₂ : Set₁ where
  field
    Kd : (c : Tr (tw 1)) → E.T → Tr (h₂ c) → Set
    foldᶜ : ∀ c v → Pc c v → (B : Base (h₂ c)) → OKB B
      → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
      → ∀ {s y} → Kd c s y
      → M⁰ (ψᴺ 0 s) (proj₁ (ψ (h₂ c) (proj₂ o² c) (rbᶻ (h₂ c)) B zero v β y))
root-cof : E.cof (E.ΩTower 3) ≡ E.cΩ []
root-cof = refl
root-fs : ∀ η → E.fsT (E.ΩTower 3) η ≡ E.Ωt (E.Ωt η)
root-fs η = refl
module Top (K : Kid₂) where
  open Kid₂ K public
  Low² : (p : Pos ℓ²) → E.T → Br ℓ² p → Set
  Low² (inj₁ (inj₁ tt)) η c = A.M¹ (E.Ωt η) c
  Low² (inj₁ (inj₂ p)) η c = ⊥
  Low² (inj₂ _) η c = ⊥
  Nu² : Pos ℓ² → E.T → Set
  Nu² (inj₁ (inj₁ tt)) ν = ν ≡ []
  Nu² (inj₁ (inj₂ p)) ν = ⊥
  Nu² (inj₂ _) ν = ⊥
  M² : E.T → Tr ℓ² → Set
  M² = Mᴴ (Sig ℓ²) Low² Kd Nu²
  IsZ : ∀ {a x} → M² a x → Set
  IsZ mz = ⊤
  IsZ _ = ⊥
  Sp : ∀ {a x} → M² a x → Set
  Sp mz = ⊤
  Sp (m1 _ m) = Sp m
  Sp (mL _ h) = ∀ n → Sp (h n)
  Sp (mΩ _ _ h) = ∀ η c l → Sp (h η c l)
  Sp (mU m _) = IsZ m
  Sp (mw m _) = Sp m
  Sp (mc _ m) = Sp m
  data Pw : zero ≤ ℓ² → Set where
    wu : Pw (z≤ ℓ²)
    wi : Pw (ink (z≤ (tw 1)))
  record GB² (B : Base ℓ²) : Set where
    constructor mkGB²
    field
      bK : A.M¹ One.ΩΩ (proj₁ (B (tw 1) (ink self)))
      bC : ∀ c → OKB (λ i u → B i (inc c u))
  open GB² public
  Pres : Set
  Pres = (B : Base ℓ²) → GB² B → ∀ {w} → Pw w
    → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
    → ∀ {s x} (m : M² s x) → Sp m
    → M⁰ (ψᴺ 0 s) (proj₁ (ψ ℓ² o² r² B zero w β x))
  Lift₂ : Set
  Lift₂ = ∀ {η c} → A.M¹ η c → Kd c (E.Ωt η) (proj₁ (Ωt (h₂ c)))
  leaf² : Lift₂ → M² (E.ΩTower 3) (proj₁ (Ωt ℓ²))
  leaf² lf = mΩ {ν = []} refl refl (λ η c l → mU mz (lf l))
  leafSp : (lf : Lift₂) → Sp (leaf² lf)
  leafSp lf η c l = tt
  gb₀ : A.Lift₁ → GB² (B₀ ℓ²)
  gb₀ lf = mkGB² (A.leaf¹ lf) (λ c i u → ⊴r)
```

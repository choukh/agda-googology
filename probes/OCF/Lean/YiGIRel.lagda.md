# 精简块上遗传封闭的全层关系与层号读法

> 验收文件（读记号）。关系逐层用 `YiHCRel.Mᴴ`；定义方式参照 `YiHCFam` 的互递归，槽位余尾改用低层读法 `Rd`，未声称等于原有限族。
> 编译定理：`rd-add`、`rd-child` 给主线 `tw-step`；`Rd` 以向下封闭、极限及各形状读法生成。
> 尚未填 `Leaf`、`Lift`、`LowKeep`；未改树、折叠或合法性。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGIRel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Lean.YiGIBlock
open B hiding (R)

-- 只在验收关系中使用参照的向下封闭与非严格极限。
data Cl (A : E.T → Set) : E.T → Set where
  c0 : ∀ {ν} → E.cof ν ≡ E.c0 → Cl A ν
  ca : ∀ {ν} → A ν → Cl A ν
  cL : ∀ {ν} → E.cof ν ≡ E.cω → (∀ n → Cl A (E.fsn ν n)) → Cl A ν
  cc : ∀ {ν μ} → ν ≤ᵀ μ → Cl A μ → Cl A ν

mapCl : ∀ {A D ν} → (∀ ν → A ν → D ν) → Cl A ν → Cl D ν
mapCl f (c0 e) = c0 e
mapCl f (ca a) = ca (f _ a)
mapCl f (cL e h) = cL e (λ n → mapCl f (h n))
mapCl f (cc le r) = cc le (mapCl f r)

mutual
  R : (ℓ : L) → E.T → Tr ℓ → Set
  R zero = H.M⁰
  R (nd s h) = H.Mᴴ (Sig (nd s h)) (Low (nd s h)) (λ c → R (h c)) (Nu (nd s h))

  Low : (ℓ : L) (p : Pos ℓ) → E.T → Br ℓ p → Set
  Low (nd s h) (inj₂ (c , t)) = Low⁼ (h c) t
  Low (nd (sΩ k) h) (inj₁ t) = Low⁼ k t

  Low⁼ : (a : L) (t : Pos⁼ a) → E.T → Br⁼ a t → Set
  Low⁼ a (inj₁ _) = R a
  Low⁼ a (inj₂ p) = Low a p

  Nu : (ℓ : L) (p : Pos ℓ) → E.T → Set
  Nu (nd s h) (inj₂ (c , t)) = Nu⁼ (h c) t
  Nu (nd (sΩ k) h) (inj₁ t) = Nu⁼ k t

  Nu⁼ : (a : L) → Pos⁼ a → E.T → Set
  Nu⁼ a (inj₁ _) = Rd a
  Nu⁼ a (inj₂ p) = Nu a p

  Rd : L → E.T → Set
  Rd ℓ = Cl (Hd ℓ)

  Hd : L → E.T → Set
  Hd zero ν = ⊥
  Hd (nd s h) ν = (Σ (Ch s) λ c → Rd (h c) ν) ⊎ ShR s h ν

  ShR : (s : Sh) → (Ch s → L) → E.T → Set
  ShR sS h ν = (E.cof ν ≡ E.c1) × Rd (h tt) (E.pred ν)
  ShR sL h ν = ⊥
  ShR (sΩ k) h ν = Σ E.T λ κ → (E.cof ν ≡ E.cΩ κ) × Rd k κ × ((η : E.T) (c : Tr k) → R k η c → Rd (h c) (E.fsT ν η))

rd-child : ∀ s h c {ν} → Rd (h c) ν → Rd (nd s h) ν
rd-child s h c q = ca (inj₁ (c , q))

mutual
  rd-add : ∀ a b {ν} → Rd b ν → Rd (a ⊕ b) ν
  rd-add a zero q = mapCl (λ _ ()) q
  rd-add a (nd s h) q = mapCl (hd-add a s h) q

  hd-add : ∀ a s h ν → Hd (nd s h) ν → Hd (nd s (λ c → a ⊕ h c)) ν
  hd-add a s h ν (inj₁ (c , q)) = inj₁ (c , rd-add a (h c) q)
  hd-add a sS h ν (inj₂ (e , q)) = inj₂ (e , rd-add a (h tt) q)
  hd-add a sL h ν (inj₂ ())
  hd-add a (sΩ k) h ν (inj₂ (κ , e , qk , qh)) = inj₂ (κ , e , qk , λ η c r → rd-add a (h c) (qh η c r))

rd-tw0 : Rd (tw 0) []
rd-tw0 = c0 refl

tw-step : ∀ n {ν} → Rd (↑ (tw n) (proj₁ (O.Ωt (tw n)))) ν → Rd (tw (suc n)) ν
tw-step n q = rd-child (sΩ (tw n)) (λ c → tw n ⊕ ↑ (tw n) c) (proj₁ (O.Ωt (tw n))) (rd-add (tw n) (↑ (tw n) (proj₁ (O.Ωt (tw n)))) q)
```

# 规范Read的完整合法证运输

Bridge的up子证书只沿携RestrictionLink的ambient下降。节点实际back
坐标通过低层运输送入原分支证书，不假原分支对任意Same相容。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedProofRun where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym)
open import OCF.Lean.CRwBase
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedFloor using (self; coord-self; coord-cong)
open import OCF.Align.GeneralOmegaCountableTypedProofIf
open import OCF.Align.GeneralOmegaCountableTypedProofRestrict
open import OCF.Align.GeneralOmegaCountableTypedProofRoute

mutual
  transport : ∀ B l₁ l₂ {x e} → Read B l₂ (canonical B l₂) x e →
    Read B l₁ (canonical B l₁) (L.tr⁻ (proof-shape B l₁ l₂) x) e
  transport B l₁ l₂ = bridge B l₁ l₂ (proof-shape B l₁ l₂) (Route.canonical-law B l₁ l₂)

  coordinate : ∀ B l₁ l₂ κ {x e} → Coord B l₂ κ x e →
    Coord B l₁ κ (L.tr⁻ (rank-shape B l₁ l₂ κ) x) e
  coordinate hz l₁ l₂ () r
  coordinate (hs B) l₁ l₂ (inj₁ κ) r = coordinate B l₁ l₂ κ r
  coordinate (hs B) l₁ l₂ (inj₂ _) r = transport B l₁ l₂ r
  coordinate (hl f) l₁ l₂ (n , κ) r = coordinate (f n) (proj₂ l₁ n) (proj₂ l₂ n) κ r
  coordinate (hΩ () f) l₁ l₂ κ r

  forward-coordinate : ∀ B l₁ l₂ κ {x e} → Coord B l₁ κ x e →
    Coord B l₂ κ (L.tr (rank-shape B l₁ l₂ κ) x) e
  forward-coordinate B l₁ l₂ κ r = coord-cong B l₂ κ
    (L.≅-trans (L.tr-≅ (rank-shape B l₁ l₂ κ) (coord-self B l₁ κ r))
      (L.≅-sym (L.tr⁻-≅ (rank-shape B l₂ l₁ κ) (coord-self B l₁ κ r))))
    (coordinate B l₂ l₁ κ r)

  bridge : ∀ B l₁ l₂ {a b} (e : a L.≅ᴵ b)
    {σ₁ : L.Simᴵ a (height B l₁)} {σ₂ : L.Simᴵ b (height B l₂)} →
    Route.Law B l₁ l₂ e σ₁ σ₂ → ∀ {x y} → Read B l₂ σ₂ x y →
    Read B l₁ σ₁ (L.tr⁻ e x) y
  bridge B l₁ l₂ e law rz = rz
  bridge B l₁ l₂ e law (rs p) = rs (bridge B l₁ l₂ e law p)
  bridge B l₁ l₂ e law (rl p) = rl (λ n → bridge B l₁ l₂ e law (p n))
  bridge B l₁ l₂ e law (ro κ q {f = f} {g = g} eq self p) with L.res⁻ q e in req | law κ q eq
  ... | L.restr _ q₁ _ | Route.matched .q₁ align = ro κ q₁ align
    (subst (λ R →
      L.limᵢ (L.Restr.lt R) (λ y → L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back R (L.out (L.<→◃ (L.Restr.lt R)) y))))) L.≅
      L.limᵢ (L.Restr.lt R) (λ y → L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back R (L.out (L.<→◃ (L.Restr.lt R)) y))))))
      req (L.≅-trans (L.tr⁻-≅ e self) (L.≅-sym (L.tr⁻-≅ e self))))
    (λ x c r → subst
      (λ u → Read B l₁ _ (L.tr⁻ e (f (L.into (L.<→◃ q) (L.tr (rank-shape B l₁ l₂ κ) u)))) (g c))
      (sym (L.out-into (L.<→◃ q₁) x))
      (bridge B l₁ l₂ e law (p _ c (forward-coordinate B l₁ l₂ κ r))))
  bridge B l₁ l₂ (L.s≅ e) {σ₁} {σ₂} law (ru-s p) = ru-s
    (bridge B l₁ l₂ e (Route.suc-law B l₁ l₂ {σ₁ = σ₁} {σ₂ = σ₂} law) p)
  bridge B l₁ l₂ (L.l≅ e) {σ₁} {σ₂} law (ru-l {i = n} p) = ru-l
    (bridge B l₁ l₂ (e n) (Route.lim-law B l₁ l₂ {σ₁ = σ₁} {σ₂ = σ₂} law n) p)
  bridge B l₁ l₂ e law (rc d p) = rc
    (L.tr⁻-≅ e (L.≅-tr⁻ e d)) (bridge B l₁ l₂ e law p)

instance-transport : CanonicalProofTransport
instance-transport = record { transport = transport }
```

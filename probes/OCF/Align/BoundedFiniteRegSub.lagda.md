# 相对世界中的子树证书

不从任意raw坐标取Reg；只从其公共界已有的Reg和RegWorld中取。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegSub where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedFiniteRegIf

reg-one : ∀ n → Reg n (one n)
reg-one zero = tt
reg-one (suc n) = tt

reg-sub : ∀ n {a b W} → RegWorld n W → Reg n b → a ⊲[ W ] b → Reg n a
reg-coordinate : ∀ n κ {c W} → RegWorld n W → Bd (F n) κ c W → RegCoord n κ c
reg-sub zero rw r p = tt
reg-sub (suc n) rw r hself = r
reg-sub (suc n) rw r (hsuc p) = reg-sub (suc n) rw r p
reg-sub (suc n) rw r (hlim j p) = reg-sub (suc n) rw (r j) p
reg-sub (suc n) rw r (hLim {κ = κ} b p) =
  reg-sub (suc n) rw (proj₂ r _ (reg-coordinate (suc n) κ rw b)) p
reg-coordinate zero κ rw b = tt
reg-coordinate (suc n) (inj₁ κ) rw b = reg-coordinate n κ (proj₁ rw) b
reg-coordinate (suc n) (inj₂ _) rw b = reg-sub n (proj₁ rw) (proj₂ rw) b

world-reg : ∀ n {W} → LegalWorld n W → RegWorld n W
world-reg zero l = tt
world-reg (suc n) l = world-reg n (proj₁ l) , proj₁ (proj₂ l)

legal-sub : ∀ n {a b W} → LegalWorld n W → Legal n b → a ⊲[ W ] b → Legal n a
legal-coordinate : ∀ n κ {c W} → LegalWorld n W → Bd (F n) κ c W → LegalCoord n κ c
legal-sub zero lw l p = lgB⊲ p lw l
legal-sub (suc n) lw l hself = l
legal-sub (suc n) lw l (hsuc p) = legal-sub (suc n) lw l p
legal-sub (suc n) lw l (hlim j p) = legal-sub (suc n) lw (proj₂ l j) p
legal-sub (suc n) lw l (hLim {κ = κ} b p) =
  legal-sub (suc n) lw (proj₂ l _ (legal-coordinate (suc n) κ lw b)) p
legal-coordinate zero κ {W = W} lw b = W , lw , b
legal-coordinate (suc n) (inj₁ κ) lw b = legal-coordinate n κ (proj₁ lw) b
legal-coordinate (suc n) (inj₂ _) lw b =
  reg-sub n (world-reg n (proj₁ lw)) (proj₁ (proj₂ lw)) b ,
  legal-sub n (proj₁ lw) (proj₂ (proj₂ lw)) b

coord-reg : ∀ n κ c → LegalCoord n κ c → RegCoord n κ c
coord-reg zero κ c l = tt
coord-reg (suc n) (inj₁ κ) c l = coord-reg n κ c l
coord-reg (suc n) (inj₂ _) c l = proj₁ l
```

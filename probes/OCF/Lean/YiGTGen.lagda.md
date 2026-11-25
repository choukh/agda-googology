# 一般层关系的公共运算
验收文件（读记号）；把 `YiHCRel.Gen` 的公共引理用于 `YiGIRel.R` 的任意目标层。
仅补一般下标的前缀单调与 Ω 下界；不假定 Leaf，不改变树、折叠或合法性。
入口：`nextᴿ`、`cumᴿ`、`zlᴿ`、`app≤ν`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTGen where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath using (Ok; _≤_; self; inc; inu; ink; emb; _∙_)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃)
open import OCF.Lean.YiGIBlock using (chLᵍ)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.Standard using (++-mono)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Pen; cofK; fsTK)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

module Gen (s : Sh) (h : Ch s → L) = H.Gen {Sig (nd s h)} {GR.Low (nd s h)}
  {λ c → GR.R (h c)} {GR.Nu (nd s h)}

weakᴿ : ∀ ℓ {t x y} → GR.R ℓ t x → ℓ ⊢ x ◃ y → GR.R ℓ t y
weakᴿ zero = H.mw
weakᴿ (nd s h) = H.mw

weakenᴿ : ∀ ℓ {t x y} → GR.R ℓ t x → x ⊴ y → GR.R ℓ t y
weakenᴿ ℓ m ⊴r = m
weakenᴿ ℓ m (⊴◃ d) = weakᴿ ℓ m d

closeᴿ : ∀ ℓ {s t x} → s ≤ᵀ t → GR.R ℓ t x → GR.R ℓ s x
closeᴿ zero = H.mc
closeᴿ (nd s h) = H.mc

limᴿ : ∀ ℓ {t x} → E.cof t ≡ E.cω → (∀ n → GR.R ℓ (E.fsn t n) x) → GR.R ℓ t x
limᴿ zero = H.mL
limᴿ (nd s h) = H.mL

nextᴿ : ∀ ℓ {t p} (β : Tr⁺ ℓ) → E.cof t ≡ E.cω
  → (∀ n → E.fsn t n ≡ replicate n p)
  → GR.R ℓ (p ∷ []) (proj₁ β) → GR.R ℓ t (proj₁ (next⁺ β))
nextᴿ zero = H.G⁰.m-next
nextᴿ (nd s h) = Gen.m-next s h

cumᴿ : ∀ ℓ {t} (F : ℕ → Tr⁺ ℓ) (n : ℕ)
  → GR.R ℓ t (proj₁ (F n)) → GR.R ℓ t (proj₁ (limc⁺ F))
cumᴿ zero = H.G⁰.m-cum
cumᴿ (nd s h) = Gen.m-cum s h

zlᴿ : ∀ ℓ {S : Sg} (F : T S → Tr ℓ)
  → (∀ {x y} → Lt S x y → ℓ ⊢ F x ◃ F y)
  → ∀ {t} → GR.R ℓ t (F zero) → ∀ x → GR.R ℓ t (F x)
zlᴿ zero = H.G⁰.m-zl
zlᴿ (nd s h) = Gen.m-zl s h

nodeᴿ : ∀ ℓ (p : Pos ℓ) {t κ} {g : Br ℓ p → Tr ℓ}
  → E.cof t ≡ E.cΩ κ → GR.Nu ℓ p κ
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT t η) (g c))
  → GR.R ℓ t (Ω p g)
nodeᴿ zero ()
nodeᴿ (nd s h) p = H.mΩ

app≤ν : ∀ ν t {a b} → a ≤ᵀ b
  → (E.ψ ν (t ++ a) ∷ []) ≤ᵀ (E.ψ ν (t ++ b) ∷ [])
app≤ν ν t (inj₁ p) = inj₁ (E.hd< (E.ar< (++-mono t p)))
app≤ν ν t (inj₂ refl) = inj₂ refl

Ω≤ψ : ∀ ν t → E.Ωt ν ≤ᵀ (E.ψ ν t ∷ [])
Ω≤ψ ν [] = inj₂ refl
Ω≤ψ ν (_ ∷ _) = inj₁ (E.hd< (E.ar< E.[]<))

emb-pres : ∀ ℓ (o : Ok ℓ) {k} (w : k ≤ ℓ) (y : Tr⁺ k) {a}
  → GR.R k a (proj₁ y) → GR.R ℓ a (proj₁ (emb ℓ o w y))
emb-pres ℓ o self y m = m
emb-pres (nd s h) o (inc c w) y m = H.mU H.mz (emb-pres (h c) (proj₂ o c) w y m)
  where open import Data.Product using (proj₂)
emb-pres (nd s h) o (inu ws) y m = H.mU H.mz
  (emb-pres (h (c₀ s)) (proj₂ o (c₀ s)) (ws (c₀ s)) y m)
  where open import Data.Product using (proj₂)
emb-pres (nd (sΩ k) h) o (ink w) y m = H.mU H.mz
  (emb-pres (h zero) (proj₂ o zero) (w ∙ proj₂ (proj₁ o) zero) y m)
  where open import Data.Product using (proj₂)

nextψ : ∀ ℓ ν t a → E.cof a ≡ E.c1 → (β : Tr⁺ ℓ)
  → GR.R ℓ (E.ψ ν (t ++ E.pred a) ∷ []) (proj₁ β)
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (next⁺ β))
nextψ ℓ ν t a e β m = nextᴿ ℓ β (cofψ1 ν (t ++ a) (cof++1 t a e))
  (λ n → trans (fsnψ1 ν (t ++ a) n (cof++1 t a e))
    (cong (λ z → replicate n (E.ψ ν z)) (pred++ t a e))) m

limψ : ∀ ℓ ν t a → E.cof a ≡ E.cω → (x : Tr ℓ)
  → (∀ n → GR.R ℓ (E.ψ ν (t ++ E.fsn a n) ∷ []) x)
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) x
limψ ℓ ν t a e x m = limᴿ ℓ (cofψω ν (t ++ a) (cof++ω t a e))
  (λ n → subst (λ z → GR.R ℓ z x)
    (sym (trans (fsnψω ν (t ++ a) n (cof++ω t a e))
      (cong (λ z → E.ψ ν z ∷ []) (fsn++ t a n e)))) (m n))

nodeψ : ∀ ℓ ν t a (p : Pos ℓ) {κ} {g : Br ℓ p → Tr ℓ}
  → E.cof a ≡ E.cΩ κ → Pen (E.cmpᵀ (E.sucT κ) ν) → GR.Nu ℓ p κ
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.ψ ν (t ++ E.fsT a η) ∷ []) (g c))
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (Ω p g)
nodeψ ℓ ν t a p e pen nu m = nodeᴿ ℓ p (cofK ν (t ++ a) pen (cof++Ω t a e)) nu
  (λ η c l → subst (λ z → GR.R ℓ z _)
    (sym (trans (fsTK ν (t ++ a) η pen (cof++Ω t a e))
      (cong (λ z → E.ψ ν z ∷ []) (fsT++ t a η e)))) (m η c l))
```

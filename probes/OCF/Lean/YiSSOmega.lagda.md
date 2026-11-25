# ω 层折到自身：比较表折叠
验收文件；编译定理，表与实际相邻路径任意，关系仍为 `YiHCLim.Lim.Mω`。
来源：`YiHCOmega.Tω.Self` 原证明搬到 `YiTBRow.ψ`；`leafω`、`upB` 与关系原样引用，不重证。
不改变树、折叠或合法性；一致路径朝第 0 层另见 `YiLTLim`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSSOmega where

open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiHCRel
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; natT; sucT; cmpᵀ; gt; lt; hd<; ar<)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.Standard using (++-mono)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (Ωᴺ; Pen; cofK; fsTK)
open import OCF.Lean.YiDCRel using (Ω≤; suc-nat)
open import OCF.Lean.YiCLFam using (fn; lev; levP; FD; fd0; fds)
open import OCF.Lean.YiCLLow using (Sb; pth)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiHCFam using (M; Lw⁼; LwP)
open import OCF.Lean.YiLRBridge using (NwB; τ₂)
open import OCF.Lean.YiHCBridge using (MB; LwB; MβB)
open import OCF.Lean.YiHCLim using (module Lim)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ; penB; module Tω)

module Omega (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
          (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s) where
  open Lim G d eG R canR

  module Old = Tω G d eG R canR
  open Old using (ψω; upB; leafω; module Gω) public

  module Self (R′ : ∀ n → G n ≤ G (suc n)) (oc : (k : ℕ) → Ok (G k)) (r : Rb Lω) (B : Base Lω) (β : Tr⁺ Lω) where
    F⁺ : Tr Lω → Tr⁺ Lω
    F⁺ x = ψ Lω (R′ , oc) r B Lω self β x

    F : Tr Lω → Tr Lω
    F x = proj₁ (F⁺ x)

    monoF : {x y : Tr Lω} → Lω ⊢ x ◃ y → Lω ⊢ F x ◃ F y
    monoF = mono Lω (R′ , oc) r B Lω self β

    PFω : ∀ {P₀} → Mω (ψω P₀) (proj₁ β) → ∀ {a x} → Mω a x → Mω (ψω (P₀ ++ a)) (F x)
    PFω {P₀} hP (mz {x = x}) = ++[] (λ z → Mω (ψω z) (F x)) P₀ (Gω.m-zl F monoF hP x)
    PFω {P₀} hP (m1 {t = a} {x = x} e h) =
      Gω.m-next (F⁺ x) (cofψ1 ωᵀ (P₀ ++ a) (cof++1 P₀ a e))
        (λ k → trans (fsnψ1 ωᵀ (P₀ ++ a) k (cof++1 P₀ a e))
                 (cong (λ z → replicate k (E.ψ ωᵀ z)) (pred++ P₀ a e)))
        (PFω hP h)
    PFω {P₀} hP (mL {t = a} {x = x} e h) =
      mL (cofψω ωᵀ (P₀ ++ a) (cof++ω P₀ a e))
        (λ k → subst (λ z → Mω z (F x))
          (sym (trans (fsnψω ωᵀ (P₀ ++ a) k (cof++ω P₀ a e)) (cong ψω (fsn++ P₀ a k e))))
          (PFω hP (h k)))
    PFω hP (mΩ {p = inj₁ ()} _ _ _)
    PFω {P₀} hP (mΩ {t = a} {p = inj₂ (m , t)} {g = g} e nu h) =
      mΩ (cofK ωᵀ (P₀ ++ a) (penB (G m) (eG m) t nu) (cof++Ω P₀ a e)) nu
        (λ η c l → subst (λ z → Mω z (F (g c)))
          (sym (trans (fsTK ωᵀ (P₀ ++ a) η (penB (G m) (eG m) t nu) (cof++Ω P₀ a e))
                 (cong ψω (fsT++ P₀ a η e))))
          (PFω hP (h η c l)))
    PFω {P₀} hP (mU {t = s₀} {s = s₁} {x = x} {c = m} {y = y} h ch) =
      subst (λ z → Mω (ψω z) (proj₁ (Up (G m) (down stop m) (F⁺ x) y))) (++-assoc P₀ s₀ s₁)
        (upB m (F⁺ x) (PFω hP h) ch)
    PFω hP (mw h dd) = mw (PFω hP h) (monoF dd)
    PFω {P₀} hP (mc le h) = mc (appᵘ ωᵀ P₀ le) (PFω hP h)
```

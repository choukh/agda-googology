# ω+1 层沿一致路径折到第 0 层
验收文件；表任意，保持 `YiHCPlus.Plus.M₊`；相邻有限孩子路径须有 `Sb` 证据。
来源：`YiLTLim.FoldU.LFu`、`YiSSPlus.LFf`；回灌链复用 `YiSSPlus.chainω/chainf`。
树、折叠和合法性不改；尚不消去相邻路径的证据前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSSUniform where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiRBCrit using (two; sh; gˢ; wˢ)
open import OCF.Lean.YiRLCrit using (ℓˢ; oˢ)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiCLFam using (fn; levP)
open import OCF.Lean.YiCLLow using (Sb; s0; pth; penJ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiHCFam using (M; LwP; mwN; mcJ; zlJ; nextJ; cumJ; mLJ; mΩP; ΩJ)
open import OCF.Lean.YiLRBridge using (Sᶜ; NwB; τ; τ₂; comp)
open import OCF.Lean.YiHCBridge using (MB; LwB; kcaseB; kcaseB₂; feedB)
open import OCF.Lean.YiLRLow using (cWC; Gᶜ; eᶜ; Rᶜ; canRᶜ)
open import OCF.Lean.YiLTLim using (module LimT)
import OCF.Lean.YiHCPlus as Old
open Old using (gtN; gtS)
open import OCF.Lean.YiSSOmega using (module Omega)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ; gtω-nat; gtω-self; penB; module Tω)

open import OCF.Lean.YiSSPlus using (module Plus)
open import OCF.Lean.YiLTLim using (module LimU; nodeZ; gt0B)
open import OCF.Lean.YiRBFam using (Pt; pt)
open import OCF.Lean.YiHCRel using (M⁰)

module Uniform (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
            (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s)
            (dk : ∀ k → k ≤ⁿ d k) (oc : (k : ℕ) → Ok (G k)) where
  open LimT G d eG R canR
  open Plus G d eG R canR dk oc

  Down : (⊤ → zero ≤ Lω) → Set
  Down vs = (rc : Rb Lω) (C : Base Lω) (t : E.T) → GBω C t
    → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t) (proj₁ β)
    → ∀ {a x} → Mω a x → M⁰ (ψᴺ 0 (t ++ a)) (proj₁ (ψ Lω (R , oc) rc C zero (vs tt) β x))

  module FoldU (r : Rb ℓ₊) (B : Base ℓ₊) (t₀ : E.T) (gb : GB₊ B t₀)
               (vs : ⊤ → zero ≤ Lω) (down : Down vs) where
    open Fold₊ r B t₀ gb
    Fu : Tr⁺ zero → Tr ℓ₊ → Tr⁺ zero
    Fu β x = ψ ℓ₊ o₊ r B zero (inu vs) β x

    LFu : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
        → ∀ {a x} → M₊ a x → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (Fu β x))
    LFu β hβ (mz {x = x}) =
      ++[] (λ z → M⁰ (ψᴺ 0 z) (proj₁ (Fu β x))) t₀
        (zlJ 0 (λ y → proj₁ (Fu β y)) (mono ℓ₊ o₊ r B zero (inu vs) β) hβ x)
    LFu β hβ (m1 {t = a} {x = x} e h) =
      nextJ 0 (Fu β x) (cofψ1 (natT 0) (t₀ ++ a) (cof++1 t₀ a e))
        (λ k → trans (fsnψ1 (natT 0) (t₀ ++ a) k (cof++1 t₀ a e))
                 (cong (λ z → replicate k (E.ψ (natT 0) z)) (pred++ t₀ a e)))
        (LFu β hβ h)
    LFu β hβ (mL {t = a} {x = x} e h) =
      mLJ 0 (cofψω (natT 0) (t₀ ++ a) (cof++ω t₀ a e))
        (λ k → subst (λ z → M⁰ z (proj₁ (Fu β x)))
          (sym (trans (fsnψω (natT 0) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ 0) (fsn++ t₀ a k e))))
          (LFu β hβ (h k)))
    LFu β hβ (mΩ {p = inj₁ ()} _ _ _)
    LFu β hβ (mΩ {t = a} {ν = ν} {p = inj₂ (tt , inj₁ tt)} {g = g} e nu h) =
      mLJ 0 (cofG (natT 0) (t₀ ++ a) (Old.gtN 0 nu) (cof++Ω t₀ a e))
        (λ k → subst (λ z → M⁰ z (proj₁ (limc⁺ (λ k′ → Fu β (g (iter (sω g) zero k′))))))
          (sym (trans (fsnG (natT 0) (t₀ ++ a) k (Old.gtN 0 nu) (cof++Ω t₀ a e))
                      (cong (ψᴺ 0) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
          (cumJ 0 (λ k′ → Fu β (g (iter (sω g) zero k′))) (suc k)
            (LFu β hβ (h (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k)) (chainω e nu h k)))))
    LFu β hβ (mΩ {p = inj₂ (tt , inj₂ (inj₁ ()))} _ _ _)
    LFu β hβ (mΩ {t = a} {ν = ν} {p = inj₂ (tt , inj₂ (inj₂ (m , t)))} {g = g} e nu h) =
      nodeZ (kp ℓ₊ o₊ (inj₂ (tt , inj₂ (inj₂ (m , t)))) (inu vs))
        (λ Z → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ Z)) (λ z → Fu β (g z)) (sf m t g)
        (mLJ 0 (cofG (natT 0) (t₀ ++ a) (gt0B (G m) (eG m) t nu) (cof++Ω t₀ a e))
          (λ k → subst (λ z → M⁰ z (proj₁ (limc⁺ (λ k′ → Fu β (g (iter (sf m t g) (bz⁼ (G m) t) k′))))))
            (sym (trans (fsnG (natT 0) (t₀ ++ a) k (gt0B (G m) (eG m) t nu) (cof++Ω t₀ a e))
                        (cong (ψᴺ 0) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ 0 (λ k′ → Fu β (g (iter (sf m t g) (bz⁼ (G m) t) k′))) (suc k)
              (LFu β hβ (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chainf m t e nu h k))))))
    LFu β hβ (mU {t = a} {s = s₁} {x = x} {c = tt} {y = y} {e = ey} h ch) =
      subst (λ z → M⁰ (ψᴺ 0 z) (proj₁ (Fu β (up x tt y ey)))) (++-assoc t₀ a s₁)
        (down (proj₂ r tt) (cb₊ x) (t₀ ++ a) (gbL h) (Fu β x) (LFu β hβ h) ch)
    LFu β hβ (mw h dd) = mw (LFu β hβ h) (mono ℓ₊ o₊ r B zero (inu vs) β dd)
    LFu β hβ (mc le h) = mc (app≤ 0 t₀ le) (LFu β hβ h)
```

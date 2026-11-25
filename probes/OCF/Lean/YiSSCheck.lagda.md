# ω+1 的一致折叠实例
验收文件；相邻路径取 `inc tt self`，子层证据、表、`OKB` 底及一致下折路径任意。
复用 `YiSSUniform`、`YiLTLim`、`YiLTLift.zp-pt`；本文件区分这个实例与量化一切 `Ok` 的 `Q`。
不改变树、折叠或合法性；任意 `Ok` 的 `Q` 尚未给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSSCheck where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiRBFam using (OKB)
open import OCF.Lean.YiCLFam using (nat; fn)
open import OCF.Lean.YiCLLow using (s0; ss)
open import OCF.Lean.YiRBCrit using (h₁)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiHCRel using (M⁰)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiHCFam using (ΩJ)
open import OCF.Lean.YiHCOmega using (module Tω)
open import OCF.Lean.YiLTLift using (ZP; zs; zu; zp-pt; module Wω; module Uω; module Hω; module Red; SΩ)
open import OCF.Lean.YiKPInst using (zq)
open import OCF.Lean.YiSSPlus using (module Plus)
open import OCF.Lean.YiSSUniform using (module Uniform)
open import OCF.Lean.YiLTKid using (ℓ¹; o¹; module Sem)
import OCF.Align.EboLeanDef as E

module Canon (oc : ∀ n → Ok (fn n)) where
  module U = Uniform fn (λ n → n) (λ _ → refl) (λ _ → inc tt self) (λ n → ss s0 , refl) (λ _ → ≤-refl) oc
  open U
  open Plus fn (λ n → n) (λ _ → refl) (λ _ → inc tt self) (λ n → ss s0 , refl) (λ _ → ≤-refl) oc

  child : (v : zero ≤ Wω.Lω) → ZP Wω.Lω v → Down (λ _ → v)
  child (inu ws) (zu zw) rc C t gb β hβ m =
    Uω.FoldU.LFu oc rc C t gb ws zq (λ n → zp-pt n (zw n)) β hβ m

  good : (B : Base ℓ₊) → OKB B → GB₊ B []
  good B ok = mkGB₊ (λ m si u q → ok _ (inc tt (inc m u)))
                       (λ m {i} si u q → ΩJ i (B _ (inc tt (inc m u))) (ok _ (inc tt (inc m u))))
                       (ok Wω.Lω (inc tt self))
                       (Hω.Gω.m⊴ (Hω.leafω (λ _ → ≤-refl)) (ok Wω.Lω (inc tt self)))

  omega+1 : (r : Rb ℓ₊) → SΩ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) ℓ₊ o₊ r
  omega+1 r (inu vs) (zu zv) B ok β hβ =
    FoldU.LFu r B [] (good B ok) vs (child (vs tt) (zv tt)) β hβ Mβ₊

ocω : ∀ n → Ok (fn n)
ocω n = proj₂ (proj₂ (proj₂ o¹ (suc ωᶜ)) tt) n

module Main (r : Rb ℓ¹) where
  open Sem r
  kidω+1 : Kdˢ (suc ωᶜ) (E.Ωt (E.sucT ωᵀ)) (proj₁ (Ωt (h₁ (suc ωᶜ))))
  kidω+1 v pc B ok β hβ =
    Canon.omega+1 ocω (proj₂ r (suc ωᶜ)) v (Red.zpc r (suc ωᶜ) pc) B ok β hβ
```

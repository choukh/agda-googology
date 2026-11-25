# TreeStep 的 ω+1 局部桥

验收文件；编译定理。`AtStep.result` 将 `TreeStep`、抽象链的 ω 实例和只说记号的 `note` 接合，仍带 `Low` 条件。
`Canon.result` 以既有 `YiLTLim.LFu` 实填 `Low`：相邻路径为 `inc tt self`，子证据、表、OKB 底及一致下折路径任意。
任意 `Ok` 的 `Low` 未填，完整 `StepS` 未得；本文件不否定它。来源：`YiTSMachine`、`YiTSOrbit`、`YiTSExit`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTSBridge where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow hiding (nat; fn)
open import OCF.Lean.YiCLFam using (nat; fn)
open import OCF.Lean.YiTSStep using (module Step)
open import OCF.Lean.YiTSExit using (module Exit)
open import OCF.Lean.YiTSOrbit using (module Atω; base-ok)
open import OCF.Lean.YiLTLift using (module Wω; module Uω; module Hω; ZP; zu; zp-pt)
open import OCF.Lean.YiHCRel using (M⁰; mw)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiRBFam using (OKB)
open import OCF.Lean.YiHCFam using (ΩJ)
open import OCF.Lean.YiKPInst using (zq)
import OCF.Align.EboLeanDef as E

module AtStep (o : Ok (h₁ (suc ωᶜ))) (r : Rb (h₁ (suc ωᶜ))) (B : Base (h₁ (suc ωᶜ)))
              (w : zero ≤ Wω.Lω) (β : Tr⁺ zero) where
  module TS = Step ωᶜ o r B w β
  module X = Exit ωᶜ o r B w β
  module O = Atω (proj₂ o tt) (proj₂ r tt) TS.childBase (TS.childBase Wω.Lω self)

  Low : Set
  Low = ∀ {a z} → Wω.Mω a z → M⁰ (ψᴺ 0 a)
    (proj₁ (ψ Wω.Lω (proj₂ o tt) (proj₂ r tt) TS.childBase zero w β z))

  cover : Wω.Mω (E.Ωt ωᵀ) (proj₁ (TS.childBase Wω.Lω self)) → Low →
          ∀ k → Σ ℕ λ m → M⁰ (ψᴺ 0 (E.γT (E.Ωt (E.sucT ωᵀ)) ωᵀ k)) (proj₁ (TS.parts m))
  cover h low k = suc k , mw (low (O.orbit-ok h k)) (◃l zero)

  result : Wω.Mω (E.Ωt ωᵀ) (proj₁ (TS.childBase Wω.Lω self)) → Low →
    M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ)))
      (proj₁ (ψ (h₁ (suc ωᶜ)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc ωᶜ))))))
  result h low = X.note-covered (E.sucT ωᵀ) refl (cover h low)

module Canon (oc : ∀ n → Ok (fn n)) (r : Rb (h₁ (suc ωᶜ))) (B : Base (h₁ (suc ωᶜ)))
             (ok : OKB B) (ws : ∀ n → zero ≤ fn n) (zw : ∀ n → ZP (fn n) (ws n))
             (β : Tr⁺ zero) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) where
  o : Ok (h₁ (suc ωᶜ))
  o = tt , λ _ → (λ _ → inc tt self) , oc
  module A = AtStep o r B (inu ws) β
  gb : Wω.GBω A.TS.childBase []
  gb = Wω.mkGBω (λ m {i} si u q → ok (fn i) (inc tt (inc m u)))
                  (λ m {i} si u q → ΩJ i (B (fn i) (inc tt (inc m u))) (ok (fn i) (inc tt (inc m u))))
  hΩ : Wω.Mω (E.Ωt ωᵀ) (proj₁ (A.TS.childBase Wω.Lω self))
  hΩ = Hω.Gω.m⊴ base-ok (ok Wω.Lω (inc tt self))
  low : A.Low
  low m = Uω.FoldU.LFu oc (proj₂ r tt) A.TS.childBase [] gb ws zq (λ n → zp-pt n (zw n)) β hβ m
  result : M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ)))
      (proj₁ (ψ (h₁ (suc ωᶜ)) o r B zero (inu (λ _ → inu ws)) β (proj₁ (Ωt (h₁ (suc ωᶜ))))))
  result = A.result hΩ low
```

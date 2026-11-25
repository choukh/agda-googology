# ω+1 处的完整 Q
验收文件；编译定理。qω+1 对一切 Ok、表、OKB 底及一致下折路径成立。
量化中的实际相邻路径无规范形前提；本模块不宣称一般 StepS 或 Lift₁。
来源：YiTSBridge.AtStep，Low 用 YiPJLim.LFu 实填；Ω 读回复用 YiHCOmega。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJQ where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([])
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow hiding (nat; fn)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiRBFam using (OKB)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiHCRel using (M⁰)
open import OCF.Lean.YiHCFam using (ΩJ)
open import OCF.Lean.YiLTLift using (Q; ZP; zu; module Wω; module Hω)
open import OCF.Lean.YiTSBridge using (module AtStep)
open import OCF.Lean.YiTSOrbit using (base-ok)
open import OCF.Lean.YiPJLim using (module LimAny)
import OCF.Align.EboLeanDef as E

module At (o : Ok (h₁ (suc ωᶜ))) (r : Rb (h₁ (suc ωᶜ))) (B : Base (h₁ (suc ωᶜ)))
          (ok : OKB B) (ws : ∀ n → zero ≤ fn n) (β : Tr⁺ zero) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) where
  module A = AtStep o r B (inu ws) β
  module U = LimAny (proj₁ (proj₂ o tt))
  gb : Wω.GBω A.TS.childBase []
  gb = Wω.mkGBω (λ m {i} si u q → ok (fn i) (inc tt (inc m u)))
                  (λ m {i} si u q → ΩJ i (B (fn i) (inc tt (inc m u))) (ok (fn i) (inc tt (inc m u))))
  hΩ : Wω.Mω (E.Ωt ωᵀ) (proj₁ (A.TS.childBase Wω.Lω self))
  hΩ = Hω.Gω.m⊴ base-ok (ok Wω.Lω (inc tt self))
  low : A.Low
  low m = U.FoldU.LFu (proj₂ (proj₂ o tt)) (proj₂ r tt) A.TS.childBase [] gb ws β hβ m
  result : M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ)))
    (proj₁ (ψ (h₁ (suc ωᶜ)) o r B zero (inu (λ _ → inu ws)) β (proj₁ (Ωt (h₁ (suc ωᶜ))))))
  result = A.result hΩ low

qω+1 : Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc ωᶜ))
qω+1 o r (inu vs) (zu zv) B ok β hβ = finish (vs tt) (zv tt)
  where
  finish : (w : zero ≤ Wω.Lω) → ZP Wω.Lω w →
    M⁰ (ψᴺ 0 (E.Ωt (E.sucT ωᵀ)))
      (proj₁ (ψ (h₁ (suc ωᶜ)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc ωᶜ))))))
  finish (inu ws) (zu zw) = At.result o r B ok ws β hβ
```

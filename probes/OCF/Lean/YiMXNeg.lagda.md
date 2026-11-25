# 反例确实属于带 mc 的零层关系
> 验收文件（读记号），编译定理：`bad-mc` 是同一个反例的合法关系推导，故无条件的 `Exit′` 不成立。
> `¬ex-bad` 也否定该具体推导的出口证据；不据此否定规范塔上的出口。
> 来源：复用 `YiHCCheck.of⁰`、`YiCLCrit.ωᶜ-M`；自然数参照的比较沿后继递归。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMXNeg where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.EboLeanDef using (HC; h0; h1; natT; ψ; Ωt)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiANFam using (cof-nat; pred-nat)
open import OCF.Lean.YiCLFam using (nat)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᶜ-M)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼)
open import OCF.Lean.YiKVRel using (readRW)
open import OCF.Lean.YiHCRel using (M⁰; mc; Exᴴ; exitᴴ)
open import OCF.Lean.YiHCCheck using (of⁰)
open import OCF.Lean.YiMXNote using (bad; hbad; hωt; bad<ω; bad-value)

bad-mc : M⁰ bad ωᶜ
bad-mc = mc (inj₁ bad<ω) (of⁰ ωᶜ-M)

bad≢singleton : ∀ u a → bad ≡ (ψ u a ∷ []) → ⊥
bad≢singleton u a ()

bad≢Ω : ∀ u → bad ≡ Ωt u → ⊥
bad≢Ω u ()

hn : ∀ n → HC (natT n)
hn zero = h0 refl
hn (suc n) = h1 (cof-nat n) (subst HC (sym (pred-nat n)) (hn n))

back-nat : ∀ n → readRW (nat n) ≼ Rt (hn n)
back-nat zero = z≼
back-nat (suc n) = s≼s (≼-trans (back-nat n)
  (tree-≼ (sym (pred-nat n)) (hn n) _))

back-ω : readRW ωᶜ ≼ Rt hωt
back-ω = l≼ (λ n → ≼l n (≼-trans (back-nat n)
  (tree-≼ (sym (rep1 n)) (hn n) (hω-inv hωt refl n))))

Exit′ : Set
Exit′ = ∀ {s x} (m : M⁰ s x) → (h : HC s) → Rt h ≼ readRW x

¬Exit′ : Exit′ → ⊥
¬Exit′ ex = bad-value (≼-trans (ex bad-mc hbad) back-ω)

¬ex-bad : Exᴴ bad-mc → ⊥
¬ex-bad ex = bad-value (≼-trans (exitᴴ bad-mc ex hbad) back-ω)
```

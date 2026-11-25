# 有限读回接口未涵盖的可满足输入
验收文件；编译定理。x=lim(ω,ω+1,…) 满足 StepS 的 M⁰ω 与 Q 前提，但没有逐孩子有限读回。
这只否定该输入的有限读回字段，不否定 StepS；MissingLimStep 与 Missingω+2 是待证命题的类型名称。
来源：YiCLCrit 的 ωᶜ-M，经既有 of⁰ 封闭嵌入；Qlim 与 YiPJQ 给两个 Q 前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJGap where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiTBRow hiding (nat; fn)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᶜ-M)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiLTLift using (Q; Qlim)
open import OCF.Lean.YiHCRel using (M⁰; mw; m1)
open import OCF.Lean.YiHCCheck using (of⁰)
open import OCF.Lean.YiANFam using (ψᴺ)
open import OCF.Lean.YiPJQ using (qω+1)
import OCF.Align.EboLeanDef as E

f : ℕ → Tr zero
f zero = ωᶜ
f (suc n) = suc (f n)
a : ∀ n → zero ⊢ f n ◃ f (suc n)
a n = ◃s
x : Tr zero
x = lim f a
input : M⁰ ωᵀ x
input = mw (of⁰ ωᶜ-M) (◃l zero)
inputQ : Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ x)
inputQ = Qlim f a

ω-not-finite : ∀ n → h₁ ωᶜ ≡ fn n → ⊥
ω-not-finite zero ()
ω-not-finite (suc n) ()
no-finite-readback : ((n : ℕ) → Σ ℕ λ j → h₁ (f n) ≡ fn j) → ⊥
no-finite-readback e = ω-not-finite (proj₁ (e zero)) (proj₂ (e zero))

MissingLimStep : Set
MissingLimStep = Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc x))

input₂ : M⁰ (E.sucT ωᵀ) (suc ωᶜ)
input₂ = m1 refl (of⁰ ωᶜ-M)
inputQ₂ : Q (ψᴺ 0 (E.Ωt (E.sucT ωᵀ))) (h₁ (suc ωᶜ))
inputQ₂ = qω+1
Missingω+2 : Set
Missingω+2 = Q (ψᴺ 0 (E.Ωt (E.sucT (E.sucT ωᵀ)))) (h₁ (suc (suc ωᶜ)))
```

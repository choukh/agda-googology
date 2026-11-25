# 合并 (比较表折叠一侧): `YiLTLift.upS`, `upL` 由同一条定理推出

> 验收文件 (读记号), 不进成品. 判决: 编译定理, 无前提. 比较表折叠 `YiTBRow.ψ` 满足 [YiZSUni](YiZSUni.lagda.md) 的 `FoldLaws` (`lawsᵀ`); `upS′`, `upL′` 的陈述与 `YiLTLift.upS`, `upL` 逐字相同, 由 `Lift.genS`, `genL` 推出.
> 不给出什么: 原文件没有改, 原引理仍在.
> 来源: `lawsᵀ` 的各项与 `YiZSUni.lawsᴿ` 同文 (两个折叠在用到的几行上相同).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZSUniT where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiHCRel using (mw; M⁰; module G⁰)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiANFam using (Ωᴺ)
open import OCF.Lean.YiLTLift using (Q; ZP; zs; zu)
open import OCF.Lean.YiSVMono using (_⊴_; ⊴r; ⊴◃; ⊴-◃)
open import OCF.Lean.YiSVStep using (to)
open import OCF.Lean.YiZSUni

fromK : ∀ {ℓ} {x y : Tr ℓ} → x K.⊴ y → x ⊴ y
fromK K.⊴r     = ⊴r
fromK (K.⊴◃ d) = ⊴◃ d

lawsᵀ : FoldLaws TB.Rb (λ r c → proj₂ r c) TB.ψ
lawsᵀ = record
  { f⊵ = λ ℓ o r B j w β x → fromK (TF.ψ-⊵ ℓ o r B j w β x)
  ; fm = λ ℓ o r B j w β d → TB.mono ℓ o r B j w β d
  ; fu = λ o r B j ws β x c y e → refl
  ; fs = λ {h} o r B j ws β ok →
      proj₁ (next⁺ (B (h tt) (inc tt self))) , ⊴◃ (⊴-◃ (ok (h tt) (inc tt self)) (◃l zero)) , stp (add _ rfl) (◃l 1)
  }

module _ {t : E.T} where
  private module U = Lift lawsᵀ zero (M⁰ (Ωᴺ 0)) (M⁰ t) mw mw (λ a → G⁰.m-right a)

  upS′ : ∀ {h : ⊤ → L} → Q t (h tt) → Q t (nd sS h)
  upS′ {h} q o r (inu ws) (zu zw) B ok β hβ =
    U.genS o r ws
      (λ B′ ok′ β′ hβ′ → q (proj₂ o tt) (proj₂ r tt) (ws tt) (zw tt) B′ (λ i u → to (ok′ i u)) β′ hβ′)
      B (λ i u → fromK (ok i u)) β hβ

  upL′ : ∀ {g : ℕ → L} (n : ℕ) → Q t (g n) → Q t (nd sL g)
  upL′ {g} n q o r (inu ws) (zu zw) B ok β hβ =
    U.genL o r ws n
      (λ B′ ok′ β′ hβ′ → q (proj₂ o n) (proj₂ r n) (ws n) (zw n) B′ (λ i u → to (ok′ i u)) β′ hβ′)
      B (λ i u → fromK (ok i u)) β hβ
```

# 后继一步的量化域核对
验收文件；编译否定只针对从任意相邻路径提取字面 `Sb`，以及从下界关系提取精确孩子。
给出 `inu` 相邻路径的合法证据，并保留 `StepS` 与 `Lift₁`：本文件不否定它们，也不主张收窄。
入口：`YiSSCheck` 的实例取 `inc` 相邻路径；`YiLTLift.Q` 量化任意 `Ok`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSSScope where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiHCRel using (M⁰; mz; mw)
open import OCF.Lean.YiHCCheck using (ωᴴ)

Rᵘ : ∀ n → fn n ≤ fn (suc n)
Rᵘ n = inu (λ _ → self)

ofin : ∀ n → Ok (fn n)
ofin zero = tt
ofin (suc n) = tt , λ _ → ofin n

ou : Ok (nd sL fn)
ou = Rᵘ , ofin

no-Sbᵘ : Σ (Sb 1 0) (λ s → Rᵘ 0 ≡ pth s) → ⊥
no-Sbᵘ (ss s0 , ())

no-all-Sb : ((R : ∀ n → fn n ≤ fn (suc n)) → ∀ n → Σ (Sb (suc n) n) (λ s → R n ≡ pth s)) → ⊥
no-all-Sb extract = no-Sbᵘ (extract Rᵘ 0)

relaxed : M⁰ ωᵀ (suc ωᶜ)
relaxed = mw ωᴴ ◃s

no-exact-child : (∀ {x} → M⁰ ωᵀ x → x ≡ ωᶜ) → ⊥
no-exact-child exact with exact relaxed
... | ()
```

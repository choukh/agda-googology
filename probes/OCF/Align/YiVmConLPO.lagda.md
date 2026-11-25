# YiVmCon：两个定义域不等于值序，`Tri` 推出 LPO

**验收文件，档位：编译定理 (否定)。** `Tri` (`tri→vm` 的前提) 推出 LPO；`≼ˣ` 与 `≼ᵖ` 对值序的完备性也各推出 LPO。所以 `YiVmConExact` 的定义域是值序的真子域，一般的 `VMᴸ` 在那里只是条件定理。
不否定什么：这些都不是 `VMᴸ` 或 `Crux` 的反例，只否定 "先把推导改写进 `≼ᵖ`" 这条证法的无条件版本。反例族都只用第 0 层的有限值 (`tα`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmConLPO where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Barrier using (LPO; any; any-witness; true→any)
import OCF.Align.Level as L
open L using (Ordᶜ)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; s≼0; ≼lim⁻; tα; bit; 1≼bit; 𝟏)
open import OCF.Align.YiVmConExact using (Tri; _≼ˣ_; _≼ᵖ_; sˣ; wˣ; lᵖ; wᵖ; ˣ→≼; ᵖ→≼; Cplᵖ)
```

`O` 是第 0 层的零 (层号要写明)。`split`：一个对 `tα α` 的判定 (`tα α ≼ 0` 或 `1 ≼ tα α`) 就给出 LPO 的实例。

```agda
O : Ordᶜ L.zero
O = L.zero

split : ∀ α → tα α ≼ O ⊎ 𝟏 ≼ tα α → (Σ ℕ λ k → α k ≡ true) ⊎ (∀ k → α k ≡ false)
split α (inj₂ q) with ≼lim⁻ q
... | n , r = inj₁ (any-witness n (1≼bit (any α n) r))
split α (inj₁ q) = inj₂ ff where
  ff : ∀ k → α k ≡ false
  ff k with α k in eq
  ... | false = refl
  ... | true  = ⊥-elim (s≼0 (≼-trans (≼l k (subst (λ b → 𝟏 ≼ bit b) (sym (true→any k eq)) (≼-refl 𝟏))) q))

tri→LPO : Tri → LPO
tri→LPO t α = split α (t O (tα α) z≼)

Cplˣ : Set
Cplˣ = ∀ (x y : Ordᶜ L.zero) → x ≼ y → x ≼ˣ y

inv-sˣ : ∀ α → 𝟏 ≼ˣ L.suc (tα α) → tα α ≼ O ⊎ 𝟏 ≼ tα α
inv-sˣ α (sˣ _ e) = inj₁ e
inv-sˣ α (wˣ d)   = inj₂ (ˣ→≼ d)

cplˣ→LPO : Cplˣ → LPO
cplˣ→LPO c α = split α (inv-sˣ α (c 𝟏 (L.suc (tα α)) (s≼s z≼)))

one : Ordᶜ L.zero
one = L.lim (λ _ → 𝟏)

inv-lᵖ : ∀ α → one ≼ᵖ L.suc (tα α) → tα α ≼ O ⊎ 𝟏 ≼ tα α
inv-lᵖ α (wᵖ d) = inj₂ (≼-trans (≼l 0 (≼-refl 𝟏)) (ᵖ→≼ d))
inv-lᵖ α (lᵖ d) = inv-sˣ α (d 0)

cplᵖ→LPO : Cplᵖ → LPO
cplᵖ→LPO c α = split α (inv-lᵖ α (c one (L.suc (tα α)) (l≼ (λ _ → s≼s z≼))))
```

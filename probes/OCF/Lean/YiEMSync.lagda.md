# 第 2 站两个实例的证据就是读回证据
验收文件（导入 `YiSYReduce`，导入闭包含记号模块）；编译定理：继承底实例与标准底实例在同步对象上的证据逐字是 `YiBCCover.oₛ`（`oᴱ≡oₛ`、`oᶻ≡oₛ`，`refl`），所以 `YiEMChain` 对 `oₛ` 的一切陈述原样适用于两个实例。
两个实例的现行链从第 1 个点起都是 ℕ 极限（`chainᴱ-lim`、`chainᶻ-lim`），顶层 way 行嵌入码对仍是码对（`wayᴱ`、`wayᶻ`）。不否定什么，不涉及值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEMSync where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiGIInst using (betaᴱ)
open import OCF.Lean.YiEMRead using (Read⁺; WayIn)
open import OCF.Lean.YiEMChain using (module Feed; module Lim)
open import OCF.Lean.YiBCCover using (ℓₛ; oₛ)
import OCF.Lean.YiSYReduce as SY

oᴱ≡oₛ : SY.oᴱ ≡ oₛ
oᴱ≡oₛ = refl

oᶻ≡oₛ : SY.oᶻ ≡ oₛ
oᶻ≡oₛ = refl

chainᴱ-lim : (m : ℕ) → Σ (ℕ → Tr zero) λ f → Σ ((n : ℕ) → zero ⊢ f n ◃ f (suc n)) λ a → SY.Sᴱ.chain (suc m) ≡ lim f a
chainᴱ-lim = Feed.chain-lim SY.oᴱ SY.Bᴱ

chainᶻ-lim : (m : ℕ) → Σ (ℕ → Tr zero) λ f → Σ ((n : ℕ) → zero ⊢ f n ◃ f (suc n)) λ a → SY.Sᶻ.chain (suc m) ≡ lim f a
chainᶻ-lim = Feed.chain-lim SY.oᶻ (B₀ ℓₛ)

module _ (f : ℕ → Tr zero) (a : (n : ℕ) → zero ⊢ f n ◃ f (suc n)) where
  open Lim f a using (d; offs; wᶜ)

  wayᴱ : (m n : ℕ) (e : Read⁺ (offs m))
    → WayIn (tw 1) (offs m) (offs n) e (way (λ i → tw 1 ⊕ offs i) (proj₁ (proj₂ SY.oᴱ d)) m n)
  wayᴱ = Lim.way-lim f a

  wayᶻ : (m n : ℕ) (e : Read⁺ (offs m))
    → WayIn (tw 1) (offs m) (offs n) e (way (λ i → tw 1 ⊕ offs i) (proj₁ (proj₂ SY.oᶻ d)) m n)
  wayᶻ = Lim.way-lim f a
```

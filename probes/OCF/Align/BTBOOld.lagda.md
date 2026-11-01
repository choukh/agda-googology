# BTBO 修正前的折叠 (历史冻结版)

> 2026-11-01 按 [BTBOFix](BTBOFix.lagda.md) 的四行补丁修正了 [BTBO](../../../src/OCF/BTBO.lagda.md) 的 `ψ<` 与 `ψ₀`. 本文逐字保留修正前的 `ψ<`、`ψ₀`、`ψⁿ`、`BTBO` 四个定义 (名字不变, 建立在 BTBO 现有的 `Ord-Ord` 之上), 供 [Finite](Finite.lagda.md) §2 与 [BTBOSemantics](BTBOSemantics.lagda.md) 的分析引用: 那些分析讨论的是修正前的行为 (压平、极限层对角), 它们的 `refl` 核对必须指向这一版.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BTBOOld where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module BoundedTrich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
open BoundedTrich hiding (_+_)
open Ord-Ord hiding (ψ<; ψ₀; ψⁿ; BTBO)

-- 修正前的 Buchholz's ψ (injᵇ 分支的链只经过目标层; 2026-11-01 前的 src 原文)
ψ< : ∀ {i ℓ} → i < ℓ → Ord ℓ → Ord i
ψ< p zero     = Ω _
ψ< p (suc a)  = lfp (ψ< p a +_)
ψ< p (lim f)  = lim (ψ< p ∘ f)
ψ< {i} {ℓ} p (limᵢ {i = j} q f) with <-dec q p
... | injᵃ j<i  = limᵢ j<i (ψ< p ∘ f ∘ coe)
... | injᵇ i<j  = lfp (ψ< p ∘ f ∘ coe₀ ∘ ↑ i<j)
... | injᶜ refl = lfp (ψ< p ∘ f ∘ coe₀)

-- 修正前的 ψ₀ (后继层逐层复合, 极限层对角)
ψ₀ : ∀ {ℓ} → Ord ℓ → Ord₀
ψ₀ {ℓ = zero}    a = a
ψ₀ {ℓ = suc ℓ}   a = ψ₀ (ψ< zero a)
ψ₀ {ℓ = lim f _} a = lim (λ n → ψ₀ (ψ< (f<l n) a))

ψⁿ : ℕ → Ord₀
ψⁿ = iter (ψ₀ ∘ Ω ∘ ordᴰ) zero

BTBO : Ord₀
BTBO = lim ψⁿ

_ : ψⁿ 1 ≡ ω
_ = refl
```

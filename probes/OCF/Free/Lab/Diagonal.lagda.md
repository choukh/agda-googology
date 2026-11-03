# Diagonal (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Diagonal](../../Align/Diagonal.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Diagonal where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) 
open import OCF.BTBO using (module Ord-Ord)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Level
```

```agda
open Ord-Ord using (iter)
```

## §1 对角线

```agda
module Diagonal (Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))) where

  next : Σ (Ordᶜ zero) HS → Σ (Ordᶜ zero) HS
  next (x , h) = ψ⁰ (Ω (toLevel x h)) , Uniform (toLevel x h)

  Γ : ℕ → Σ (Ordᶜ zero) HS
  Γ = iter next (Ω zero , hs hz)

  γ : ℕ → Ordᶜ zero
  γ n = proj₁ (Γ n)

  cert : ∀ n → HS (γ n)
  cert n = proj₂ (Γ n)

  L : ℕ → Ordᴵ
  L n = toLevel (γ n) (cert n)

  BTBOᴵ : Ordᶜ zero
  BTBOᴵ = lim (λ n → ψ⁰ (Ω (L n)))
```

## §6 结论与边界

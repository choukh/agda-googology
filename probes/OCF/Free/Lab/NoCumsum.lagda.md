# NoCumsum (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [NoCumsum](../../Align/NoCumsum.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.NoCumsum where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Diagonal using (module Diagonal)
open import OCF.Free.Lab.Uniform using (Uniform)
```

## §1 闭合的对角线

```agda
module D = Diagonal Uniform

γ : ℕ → Ordᶜ zero
γ = D.γ

cert : ∀ n → HS (γ n)
cert = D.cert

BTBOᴵ : Ordᶜ zero
BTBOᴵ = D.BTBOᴵ
```

## §4 结论与边界

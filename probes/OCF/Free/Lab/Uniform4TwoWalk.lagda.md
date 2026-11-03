# Uniform4TwoWalk (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform4TwoWalk](../../Align/Uniform4TwoWalk.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform4TwoWalk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) 
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Ord₊ˢ; Ordˢ)
import OCF.Align.EBO as E
open import OCF.Free.Lab.StandardOmega using (walk; NF₁; n∷; nψ; sC; sΩ)
open import OCF.Free.Lab.Uniform3Base using (Flr; fz; fk; _⊔_; Ev; ψ₀ᵗ)
open import OCF.Free.Lab.Uniform4Head using (Ωp)
open import OCF.Free.Tree
```

```agda
open E using (T; PT; fsn; cof; c0; c1; cω; cΩ; sucT; 𝟏; Ωt) renaming (ψ to ψᵗ)
tΩ·2 : T
tΩ·2 = ψ₀ᵗ (Ωt (Ωp ∷ Ωp ∷ []))
```

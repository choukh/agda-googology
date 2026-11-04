# Uniform4Base (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [LadderLabZUniform4Base](LadderLabZUniform4Base.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZUniform4Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZPrefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ; _+ˢ_)
open import OCF.Align.OrdLabZUniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun)
open import OCF.Free.Tree public using (Fl; asl; asr; swp; dupr2)
open import OCF.Align.LadderLabZUniform4Base public using (_<ᴸ_; suc; zero)
```

```agda
open Ord-Ord using (iter)
```

## §2 加法、嵌入、尾巴

```agda
dupr : ∀ {a b ℓ} → Ev ℓ (a ⊔ b) → Ev ℓ (a ⊔ (b ⊔ b))
dupr (u , v) = u , (v , v)

```

## §3 折叠

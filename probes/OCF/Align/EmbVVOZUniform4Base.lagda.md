> **机械克隆, 验收用.** 由 `OrdLabZUniform4Base` 经 `Survey/scripts/embvv/mk_world.py` 生成, 只改导入 (`NF₁` 换成 `EmbVVLZStandardOmega` 的). 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVOZUniform4Base where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.EmbVVOZPrefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ; _+ˢ_)
open import OCF.Align.EmbVVOZUniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun)
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

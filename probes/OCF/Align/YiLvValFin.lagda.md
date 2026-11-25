# YiLvFold 第 4 层：一切有限层号与 ω 的值下界 (条件)

**验收文件，档位：条件定理加编译定理。** `AllLevels`：若对一切 `M` 有 `Interface M` ([YiLvValBase](YiLvValBase.lagda.md) §3)，则对一切 `n`，
`ψ⁰ (Ω ⟨n⟩) ≼ read (foldᶠ n)`，且 `ψ⁰ (Ω ω) ≼ read fold-Ωω`。前提的实例只对 `M = 0, 1, 2` 编译过 (`interface₀`, `interface₁`, `interface₂`)，
一般的 `M` 没有证。无条件的：`n ≤ 3` 的下界，与 `fold-Ωω` 不低于 ψ₀(Ω₃)。参照 `ψ⁰ (Ω ω)` 是各 `ψ⁰ (Ω ⟨n⟩)` 的极限 (`reference-ω-row`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvValFin where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.YiLvFoldFin using (foldᶠ; fold-Ωω)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase
  using (⟨_⟩; Interface; module FromInterface; lower₀; lower₁; interface₀)
open import OCF.Align.YiLvVal2 using (interface₁; lower₂)
open import OCF.Align.YiLvVal3 using (interface₂; lower₃)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼)

reference-ω-row : L.ψ⁰ (L.Ω L.ωᴵ) ≡ L.lim (λ n → L.ψ⁰ (L.Ω ⟨ n ⟩))
reference-ω-row = refl

module AllLevels (I : ∀ M → Interface M) where

  lower-fin : ∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (foldᶠ n)
  lower-fin zero = lower₀
  lower-fin (suc M) = FromInterface.theorem M (I M)

  lower-ω : L.ψ⁰ (L.Ω L.ωᴵ) ≼ read fold-Ωω
  lower-ω = l≼ (λ n → ≼l n (lower-fin n))

below-ω : ∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (foldᶠ n) →
  L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read fold-Ωω
below-ω n low = ≼l n low

Ω₃≼fold-Ωω : L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read fold-Ωω
Ω₃≼fold-Ωω = below-ω 3 lower₃
```

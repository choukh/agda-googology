# YiLvAll：一切有限层号与 ω 的值下界

**验收文件，档位：编译定理 (下界，不是同值)。** `interfaceᴬ : ∀ M → Interface M`，于是 [YiLvValFin](YiLvValFin.lagda.md) 的条件定理成为无条件的：
对一切 `n`，参照 `ψ⁰ (Ω ⟨n⟩)` ≼ 读回的 `foldᶠ n`；参照 `ψ⁰ (Ω ω)` ≼ 读回的 `fold-Ωω`。没有 Funext，没有改折叠。
关系族在 [YiLvAllRel](YiLvAllRel.lagda.md)，树一侧的派发方程在 [YiLvAllTree](YiLvAllTree.lagda.md)，加法在 [YiLvAllAdd](YiLvAllAdd.lagda.md)，
主引理 `FOLD` 在 [YiLvAllFold](YiLvAllFold.lagda.md)。只是下界：不说明值不更高。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvAll where

open import Data.Nat.Base using (ℕ; zero; suc)
open import OCF.Align.YiLvFoldFin using (fin; foldᶠ; fold-Ωω)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩; Interface)
open import OCF.Align.YiLvValFin using (module AllLevels)
open import OCF.Align.YiLvAllRel using (Rel; un0; START)
open import OCF.Align.YiLvAllAdd using (ABSORB)
open import OCF.Align.YiLvAllFold using (FOLD)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)

z<M : ∀ M → L.zero L.<ᴵ L.suc ⟨ M ⟩
z<M zero = L.zero
z<M (suc M) = L.suc (z<M M)

interfaceᴬ : ∀ M → Interface M
interfaceᴬ M = record
  { Rel = λ x η → Rel M x η
  ; start = START M
  ; step = λ r nb d → FOLD M M r L.zero (λ q → L.suc q) nb d
  ; absorb = λ θ r → ABSORB M θ r
  ; lower = λ r s nb d →
      ≼-trans (≅→≼ (L.ψ⁰≅ψ {p = z<M M} {σ = λ q → L.suc q} s))
        (un0 (FOLD M 0 r (z<M M) (λ q → L.suc q) nb d))
  }

lower-all : ∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (foldᶠ n)
lower-all = AllLevels.lower-fin interfaceᴬ

lower-Ωω : L.ψ⁰ (L.Ω L.ωᴵ) ≼ read fold-Ωω
lower-Ωω = AllLevels.lower-ω interfaceᴬ
```

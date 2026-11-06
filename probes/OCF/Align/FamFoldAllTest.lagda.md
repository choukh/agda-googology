# 族增量世界上的真折叠 (六): 一般定义在第 1, 2 级上的检查

> 不含记号. 入口 [FamFold](FamFold.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> [FamFoldAll](FamFoldAll.lagda.md) 的一般定义在 $n=1, 2$ 上的定理 (对具体级数的计算, 不是对一切 $n$ 的定理): 级顶降下来的输入是格的 ℕ-极限, 第 2 格的最外是该级新种类的 $\Omega$-节点. 第 1 级: 两种种类的输入 `H 1` 合法 (`lgH 1`), 不与 `Ω₂ᴴ` 互模拟, 不与任何 `H₀` 嵌入互模拟 (`notPressedᴸ`: 连同合法性, 回应否定一路 `notPressed-e₊` 的提醒). 第 2 级: 中间输入 (`HB S₂`) 的第 2 格的最外是 κ₂ 的节点, 不与任何 `HB S₁` 嵌入互模拟.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FamFoldAllTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop)
open import OCF.Align.HtTowerFTree using (H₀; Ht)
open import OCF.Align.HtTowerFClosed using (Ω₂ᴴ)
open import OCF.Align.DiagK3Zero using (_≈_; ≈l)
open import OCF.Align.DiagK3One using (NoNew; up-noNew)
open import OCF.Align.UipFbClosed using (noNew-≈)
open import OCF.Align.FamFoldIf using (Sk; S₂; NotPressed)
open import OCF.Align.FamFoldAll using (H; lgH; idxK; dnR)

cellsOf : ∀ {S} → HB S → ℕ → HB S
cellsOf (hl f) = f
cellsOf _ = λ _ → hz

isNew : ∀ {S} → HB (step S) → Set
isNew (hΩ (inj₂ tt) _) = ⊤
isNew _ = ⊥

-- 第 1 级
H1-cell₂ : isNew {S₀} (cellsOf (H 1) 2)
H1-cell₂ = tt

H1-new : ¬ NoNew {S₀} (cellsOf (H 1) 2)
H1-new ()

¬H1≈Ω₂ : ¬ (H 1 ≈ Ω₂ᴴ)
¬H1≈Ω₂ ()

¬H1≈up : ∀ (h : H₀) → ¬ (H 1 ≈ up h)
¬H1≈up (hl f) (≈l e) = H1-new (noNew-≈ (e 2) (up-noNew (f 2)))

notPressedᴸ : LgB (H 1) × ¬ (H 1 ≈ Ω₂ᴴ) × (∀ (h : H₀) → ¬ (H 1 ≈ up h))
notPressedᴸ = lgH 1 , ¬H1≈Ω₂ , ¬H1≈up

-- 第 2 级: 中间输入 (HB S₂)
I₂ : HB S₂
I₂ = idxK 1 (dnR 1) (Ωtop (Sk 2))

I₂-cell₂ : isNew {Sk 1} (cellsOf I₂ 2)
I₂-cell₂ = tt

I₂-new : ¬ NoNew {Sk 1} (cellsOf I₂ 2)
I₂-new ()

¬I₂≈up : ∀ (h : Ht) → ¬ (I₂ ≈ up h)
¬I₂≈up (hl f) (≈l e) = I₂-new (noNew-≈ (e 2) (up-noNew (f 2)))
```

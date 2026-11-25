# 验收一侧 (F2 块, 有限层号): 带 ℕ 极限规则的封闭关系接进抽象接口

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `gradedᴴ`: `YiDCRel.gradedᴰ` 的关系换成 `M̂ (YiANFam.M n)`. 接口的 `Lim`, `Leaf`, `LowKeep` 实填 (`limᴴ`, `leafᴴ`, `lowKeepᴴ`); 带条件的出口 `exitᴴ` 填出 `YiExSuff.Exit₀`, 条件是 `YiMHRel.Ex`.
> `M̃ → M̂` (`of̃`). 与 [YiDCRel](YiDCRel.lagda.md), [YiExInst](YiExInst.lagda.md) 的差别: 关系多一条极限规则, `Lim` 律成立, 出口的极限情形用 `hω`.
> 不给出什么: 其余律 (`Zero`, `Succ`, `Node`, `Emb`, `SelfKeep`, `UpKeep`, `Weak`) 没有填; 有限层号上没有塔, 不给 `Keel⁻` 与 `ex`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMHFin where

open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)

open import OCF.Align.Value using (≼-trans)
open import OCF.Lean.YiMEBase using (read; lower⁰)
open import OCF.Lean.YiANFam using (M; Ωᴺ)
open import OCF.Lean.YiAbsSimInst using (𝕍)
open import OCF.Lean.YiAbsGIface using (Graded; module Laws)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
open import OCF.Lean.YiAbsGFin using (blkᶠ; foldᶠ; rowsᶠ)
open import OCF.Lean.YiASIface using (gradedᴬ; domsᴬ)
open import OCF.Lean.YiASProofLow using (lowKeepᶠ)
open import OCF.Lean.YiASProofMin using (mΩt)
open import OCF.Lean.YiDCRel using (M̃; Rdᴰ; Ω≤)
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiExSuff
open import OCF.Lean.YiMHRel
```

## 接口的实例与三条律

```agda
gradedᴴ : Graded blkᶠ foldᶠ rowsᶠ refᴱ 𝕍
gradedᴴ = record gradedᴬ { R = λ n → M̂ (M n) ; Rd = Rdᴰ }

of̃ : ∀ {n s x} → M̃ n s x → M̂ (M n) s x
of̃ (t , le , m) = ĉ le m

open Laws gradedᴴ domsᴬ using (Lim; Leaf; LowKeep)

limᴴ : Lim
limᴴ e h = l̂ e h

leafᴴ : Leaf
leafᴴ {ℓ = n} (m , refl , l) = ĉ (Ω≤ l) (mΩt n)

lowKeepᴴ : LowKeep
lowKeepᴴ {j = j} b w β t₀ gb wl bd gx = keep j t₀ (lowKeepᶠ b w β t₀ gb wl bd gx)
```

## 出口

```agda
open ExSuff gradedᴴ domsᴬ

exitᴴ : Exit₀
exitᴴ = record
  { Ex   = Ex
  ; exit = λ r ex h → ≼-trans (tree-back h) (exit̂ read lower⁰ r ex (back h))
  }
```

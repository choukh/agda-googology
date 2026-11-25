# 前缀 Ω 的合法塔与极限

本篇只复用新候选 `YiSpinePrefix.Ωprefix`，不改原 Ω、层号或合法性。
前缀 Ω 对每个合法输入保持合法；塔相邻项的位置直接来自字面前缀。
不假定前缀 Ω 一般保持 CP，也不用左加法的单调性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPrefixLevels where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (LF)
import OCF.Align.LevelFixCore as F
open import OCF.Align.LevelFixVal using (Legal; CP)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiSpinePrefix using (Ωprefix; prefix-position)

Ωp : LF → LF
Ωp x = V._+ᴸ_ x (V.Ω̂ x)

Legal-Ωp : ∀ x → Legal x → Legal (Ωp x)
Legal-Ωp x lawful = V.Legal-add x (V.Ω̂ x) lawful (V.Legal-Ω̂ x lawful)

Ωprefix-tree : ∀ x → Y.tree (Ωprefix x) ≡ Ωp (Y.tree x)
Ωprefix-tree x = refl

tower : ℕ → Y.Level
tower zero = Y.zero
tower (suc n) = Ωprefix (tower n)

tower-step : ∀ n → CP (Y.tree (tower n)) (Y.tree (tower (suc n)))
tower-step n = prefix-position (tower n)

tower-legal : ∀ n → Legal (Y.tree (tower n))
tower-legal n = Y.legal (tower n)

Λp : Y.Level
Λp = Y.lim tower tower-step

Λp-tree : Y.tree Λp ≡ F.lim (λ n → Y.tree (tower n))
Λp-tree = refl

Λp-legal : Legal (Y.tree Λp)
Λp-legal = Y.legal Λp

ΩprefixΛp : Y.Level
ΩprefixΛp = Ωprefix Λp

ΩprefixΛp-tree : Y.tree ΩprefixΛp ≡ Ωp (Y.tree Λp)
ΩprefixΛp-tree = refl

ΩprefixΛp-legal : Legal (Y.tree ΩprefixΛp)
ΩprefixΛp-legal = Legal-Ωp (Y.tree Λp) Λp-legal
```

Λp 只是前缀塔在同一 Level 类型中的合法 ℕ 极限。
本篇没有证明它与原 Λ 同值，没有证明 Ωprefix 与这个极限交换，
也没有给出一般的 CP 位置保持、ψ、FGH 或覆盖全部实际比较的结论。

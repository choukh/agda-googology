# Reg₂ 止损：规范塔树 Ω₁ 已含合法常值极限分支

只检查冻结的 YiReg2Base.Reg₂，不修订正则性形状。
输入1满足 Legal 与 Reg₂；结构 Ω̂1 仍合法，其根位置也有证据，
但原 Gd 允许一条读回 lim const1 的坐标。这一分支使 Reg₂ 要求 Proper 1 1。
因此本候选的 Ω 保持失败，且规范塔的第2棵树本身不满足 Reg₂。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiReg2Stop where

open import Data.Nat.Base using (ℕ)
open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_×_; _,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore using (LF; Raw; Lgl; Gd)
import OCF.Align.LevelFixCore as F
open F using (module G)
open import OCF.Align.LevelFixVal using (Legal)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiDispBase using (Below; one; e-first)
open import OCF.Align.YiReg2Base using (Reg₂)

one-tree : LF
one-tree = F.suc F.zero

one-legal : Legal one-tree
one-legal = tt

one-reg₂ : Reg₂ one-tree
one-reg₂ = tt

omega-one-legal : Legal (V.Ω̂ one-tree)
omega-one-legal = V.Legal-Ω̂ one-tree one-legal

η : Raw F.zero
η = G.lim (λ _ → G.suc G.zero)

η-lawful : Lgl F.zero η
η-lawful = (λ _ → inj₁ refl) , (λ _ → tt)

η-guard : Gd F.zero (V.cO F.zero) η
η-guard = inj₂ (0 , inj₁ refl) , η-lawful

read-η : V.up F.zero η ≡ F.lim (λ _ → one-tree)
read-η = refl

read-η-legal : Legal (V.up F.zero η)
read-η-legal = V.lgl→Legal F.zero tt η η-lawful

root-bound : Below one-tree (V.Ω̂ one-tree)
root-bound = one e-first

nonbranch-reg : Below one-tree (V.Ω̂ one-tree) × Reg₂ F.zero × Reg₂ one-tree
nonbranch-reg = root-bound , tt , tt

read-terms-reg₂ : ∀ (n : ℕ) → Reg₂ one-tree
read-terms-reg₂ n = tt
```

原 Raw 合法性的相邻步允许自反 Cp，故 η-lawful 与 η-guard 都是实际实例。
新增严格性才失败：1 的目标形状仅能匹配 under-suc，它要求 CP 1 0。
根 Below、下标 Reg₂、第一支 Reg₂ 以及所选极限每项的 Reg₂ 均已给出。

```agda
no-proper-one : Y.Proper one-tree one-tree → ⊥
no-proper-one (Y.under-suc ())

no-reg₂-read : Reg₂ (V.up F.zero η) → ⊥
no-reg₂-read (step , terms) = no-proper-one (step 0)

no-reg₂-Ω₁ : Reg₂ (V.Ω̂ one-tree) → ⊥
no-reg₂-Ω₁ (bound , index , first , branches) = no-reg₂-read (branches η η-guard)

tower-equation : V.Ω̂ one-tree ≡ Y.tree (Y.tower 2)
tower-equation = refl

no-tower2 : Reg₂ (Y.tree (Y.tower 2)) → ⊥
no-tower2 = no-reg₂-Ω₁

no-all-towers : (∀ n → Reg₂ (Y.tree (Y.tower n))) → ⊥
no-all-towers all = no-tower2 (all 2)

ΩPreservesReg₂ : Set
ΩPreservesReg₂ = ∀ x → Legal x → Reg₂ x → Reg₂ (V.Ω̂ x)

no-Ω-preservation₂ : ΩPreservesReg₂ → ⊥
no-Ω-preservation₂ preserves = no-reg₂-Ω₁ (preserves one-tree one-legal one-reg₂)
```

tower-equation 用 refl 确认同一棵既有规范塔树，没有重新定义 Ω 或换掉分支域。
这是整棵塔树的 Reg₂ 否定，因为 Reg₂ 检查原 Gd 的全部合法分支。
并未证明 EBO 的可数基本列轨道实际选中了 η；不能把该坐标称作实际 Reach
选择的列，也不称它为 ψ 列停顿或已构造的实际 γ 输出反例。

本篇未采用函数外延、UIP、裸下标律或记号；没有新增正则性形状。
止损结论只针对冻结 Reg₂ 及原全 Gd 分支域，不扩大成其它正则性方案的否定。

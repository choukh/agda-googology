# EboLean3Lab: 标签 (另列一行, 不算第 3 层)

> **记号侧验收工作**, 读记号与标签, 不进成品. "+ 标签" 一行 (作者 2026-11-05: 第 3 层只算 FGH 可计算所需). 形状同 [EboLeanLab](EboLeanLab.lagda.md), 树类型换成 [EboLean3Tree](EboLean3Tree.lagda.md) 的 `Ord`. **结论 (定理):** `HC` 造的树都有标签 (`lab-tree`), 于是 `lab-NF″` (一切可数标准形) 与 `ebo-lab″` (Ω-塔对一切 $k$). `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EboLean3Lab where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase using (NF; Ctbl)
open import OCF.Align.EboLean3Tree using (Ord; zero; suc; lim; tree; hc; hc-tower)

data _≅_ : Ord → Ord → Set where
  z≅ : zero ≅ zero
  s≅ : ∀ {a b} → a ≅ b → suc a ≅ suc b
  l≅ : ∀ {f g} → (∀ n → f n ≅ g n) → lim f ≅ lim g

≅-refl : ∀ a → a ≅ a
≅-refl zero    = z≅
≅-refl (suc a) = s≅ (≅-refl a)
≅-refl (lim f) = l≅ (λ n → ≅-refl (f n))

data Labᴸ : Ord → T → Set where
  l0 : ∀ {X t} → cof t ≡ c0 → X ≅ zero → Labᴸ X t
  l1 : ∀ {X Y t} → cof t ≡ c1 → X ≅ suc Y → Labᴸ Y (pred t) → Labᴸ X t
  lω : ∀ {X t} {F : ℕ → Ord} → cof t ≡ cω → X ≅ lim F → (∀ n → Labᴸ (F n) (fsn t n)) → Labᴸ X t

lab-tree : ∀ {t} (h : HC t) → Labᴸ (tree h) t
lab-tree (h0 e)   = l0 e z≅
lab-tree (h1 e h) = l1 e (≅-refl _) (lab-tree h)
lab-tree (hω e h) = lω e (≅-refl _) (λ n → lab-tree (h n))

lab-NF″ : ∀ {t} (nt : NF t) (ct : Ctbl t) → Labᴸ (tree (hc nt ct)) t
lab-NF″ nt ct = lab-tree (hc nt ct)

ebo-lab″ : ∀ k → Labᴸ (tree (hc-tower k)) (EBOψ k)
ebo-lab″ k = lab-tree (hc-tower k)
```

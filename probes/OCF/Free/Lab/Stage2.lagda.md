# Stage2 (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Stage2](../../Align/Stage2.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Stage2 where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Uniform using (Good; Good-add; Good-ψ⁰; Good-Ω; Good→HS; l-inv; ψ⁰-cong; add-cong; Ω-monoᵒ; idO)
import OCF.Free.Lab.NoCumsum as N
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω; Lab-≅; cof-ne; γᴱ; diag-fs; fs-rep; fs-ω; βᴱ)
open import OCF.Free.Lab.Label using (γ-label; BTBO-label; Good-lift)
```

```agda
open Ord-Ord using (iter)
open E using (T; cω; cof; cofA; fsn; fsT; γT; Ωt; natT; sucT; dec) renaming (ψ to ψᵗ)
```

## §2 标签工具

```agda
Lab-+ : ∀ {X Y x ys} → Lab X (x ∷ []) → Lab Y ys → Lab (X + Y) (x ∷ ys)
Lab-+ {ys = []}     hX (l0 c e) = Lab-≅ (add-≅ {σ = λ q → q} {σ′ = λ q → q} (≅-refl⁰ _) e) hX
Lab-+ {ys = y ∷ ys} hX (l0 c e) = ⊥-elim (cof-ne y ys c)
Lab-+ {ys = []}     hX (l1 () e l)
Lab-+ {ys = y ∷ ys} hX (l1 c e l) = l1 c (add-≅ (≅-refl⁰ _) e) (Lab-+ hX l)
Lab-+ {ys = []}     hX (lω () e h)
Lab-+ {ys = y ∷ ys} hX (lω c e h) = lω c (add-≅ (≅-refl⁰ _) e) (λ n → Lab-+ hX (h n))

Lab-uniq : ∀ {A B t} → Lab A t → Lab B t → A ≅ B
Lab-uniq (l0 c e) (l0 c′ e′) = ≅-trans e (≅-sym e′)
Lab-uniq (l0 c e) (l1 c′ e′ l′) with trans (sym c) c′
... | ()
Lab-uniq (l0 c e) (lω c′ e′ h′) with trans (sym c) c′
... | ()
Lab-uniq (l1 c e l) (l0 c′ e′) with trans (sym c) c′
... | ()
Lab-uniq (l1 c e l) (l1 c′ e′ l′) = ≅-trans e (≅-trans (s≅ (Lab-uniq l l′)) (≅-sym e′))
Lab-uniq (l1 c e l) (lω c′ e′ h′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (l0 c′ e′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (l1 c′ e′ l′) with trans (sym c) c′
... | ()
Lab-uniq (lω c e h) (lω c′ e′ h′) = ≅-trans e (≅-trans (l≅ (λ n → Lab-uniq (h n) (h′ n))) (≅-sym e′))
```

## §4 事实 3: 朴素代表在哪里断

```agda
Ωᵗ : T
Ωᵗ = Ωt (natT 1)

t2 : T
t2 = ψᵗ [] (βᴱ ++ βᴱ) ∷ []
```

## §6 设计 D2: 有界定义域的 $\hat\Omega$

```agda
≺→⊑ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≺ b → a ⊑ b
≺→⊑ (≺z e)      h = ≺s (≺-respʳ h e)
≺→⊑ (≺s p)      h = ≺s (≺→⊑ p h)
≺→⊑ (≺l n p)    h = ≺l n (≺→⊑ p h)
≺→⊑ (≺i x ex p) h = ≺i x ex (≺→⊑ p h)
≺→⊑ (≺u p)      h = ≺u (≺→⊑ p h)
```

## §8 决定性检验

```agda
b₂ : T
b₂ = βᴱ ++ βᴱ

γ′ᴱ : ℕ → T
γ′ᴱ = γT b₂ []
```

```agda
ctx : T → T
ctx y = ψᵗ [] (ψᵗ Ωᵗ [] ∷ y) ∷ []
```

## §12 结论与边界

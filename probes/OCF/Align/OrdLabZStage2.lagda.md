# Stage2 (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [Stage2](Stage2.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZStage2 where

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
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZUniform using (Good; Good-add; Good-ψ⁰; Good-Ω; Good→HS; l-inv; ψ⁰-cong; add-cong; Ω-monoᵒ; idO)
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; cof-ne; γᴱ; diag-fs; fs-rep; fs-ω; βᴱ)
open import OCF.Align.OrdLabZLabel using (γ-label; BTBO-label; Good-lift)
open import OCF.Align.Stage2 public using (b₂; ctx; t2; Ωᵗ; γ′ᴱ)
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

## §6 设计 D2: 有界定义域的 $\hat\Omega$

```agda
≺→⊑ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≺ b → a ⊑ b
≺→⊑ (≺z e)      h = ≺s (≺-respʳ h e)
≺→⊑ (≺s p)      h = ≺s (≺→⊑ p h)
≺→⊑ (≺l n p)    h = ≺l n (≺→⊑ p h)
≺→⊑ (≺i x ex p) h = ≺i x ex (≺→⊑ p h)
≺→⊑ (≺u p)      h = ≺u (≺→⊑ p h)
```

## §12 结论与边界

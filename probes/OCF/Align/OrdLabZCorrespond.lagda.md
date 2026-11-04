# Correspond (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [Correspond](Correspond.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZCorrespond where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZUniform using (Good; Good-add; Good-ψ; Good-ψ⁰; Good-Ω; Good→HS; gz; s-inv; l-inv; ≅-reflˡ)
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.EBO as E
open import OCF.Align.Correspond public using (H; cmp-suc[]; cof-ne; cofA-ne; cofψ0-ne; cofψ₊-ne; diag-fs; fs-rep; fs-ω; fsT-c1; fsn↓c-gt; gH; g[]; gΩ; gγ; gψ; g∷; hΩ; hψ; βᴱ; γT-γᴱ; γᴱ; 𝔾; 𝔾ᴾ)
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofP; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; natT; fsn; fsT; fsT0; γT; trm; dec)
       renaming (ψ to ψᵗ)
```

## §2 翻译、证书与层号

```agda
⟦_⟧ᴴ : ∀ {ν h} → H ν h → (L : Ordᴵ) → Ordᶜ L
⟦ hΩ ⟧ᴴ   L = Ω L
⟦ hψ d ⟧ᴴ L = ψ zero (λ r → r) (up zero (⟦ d ⟧ᴴ L))

reflH : ∀ {ν h} (d : H ν h) L → ⟦ d ⟧ᴴ L ≅ ⟦ d ⟧ᴴ L
reflH hΩ     L = Ω-refl L
reflH (hψ d) L = ψ-≅ {p = zero} {σ = λ q → suc q} {p′ = zero} {σ′ = λ q → suc q} (≅ᴵ-refl L) (reflH d L)

goodH : ∀ {ν h} (d : H ν h) L → Good (⟦ d ⟧ᴴ L)
goodH hΩ     L = Good-Ω L
goodH (hψ d) L = Good-ψ {p = zero} {σ = λ q → suc q} (goodH d L) (reflH d L)
```

```agda
⟦_⟧   : ∀ {t} → 𝔾 t → Ordᶜ zero
⟦_⟧ᴾ  : ∀ {x} → 𝔾ᴾ x → Ordᶜ zero
good  : ∀ {t} (g : 𝔾 t) → Good ⟦ g ⟧
goodᴾ : ∀ {x} (g : 𝔾ᴾ x) → Good ⟦ g ⟧ᴾ
lvl   : ∀ {t} → 𝔾 t → Ordᴵ

⟦ g[] ⟧      = zero
⟦ g∷ x xs ⟧  = ⟦ x ⟧ᴾ + ⟦ xs ⟧
⟦ gψ a ⟧ᴾ    = ψ⁰ ⟦ a ⟧
⟦ gΩ u ⟧ᴾ    = ψ⁰ (Ω (lvl u))
⟦ gH g d ⟧ᴾ  = ψ⁰ (⟦ d ⟧ᴴ (lvl g))
good g[]       = gz
good (g∷ x xs) = Good-add (goodᴾ x) (≅-refl⁰ _) (good xs)
goodᴾ (gψ a)   = Good-ψ⁰ (good a) (≅-refl⁰ _)
goodᴾ (gΩ u)   = Good-ψ⁰ (Good-Ω (lvl u)) (Ω-refl (lvl u))
goodᴾ (gH g d) = Good-ψ⁰ (goodH d (lvl g)) (reflH d (lvl g))
lvl g = toLevel ⟦ g ⟧ (Good→HS (good g))

cert : ∀ {t} (g : 𝔾 t) → HS ⟦ g ⟧
cert g = Good→HS (good g)
```

## §3 纯推导、匹配与形状的陈述

```agda
𝟘 : Ordᶜ zero
𝟘 = zero
```

## §7 对角线

```agda
diag-≅ : ∀ k → N.γ k ≅ ⟦ gγ k ⟧
diag-≅ zero    = s≅ z≅
diag-≅ (suc k) = ψ⁰-≅ (Ω-≅ (toLevel-≅ (N.cert k) (cert (gγ k)) (diag-≅ k)))
```

## §8 遗传标签

```agda
data Lab : Ordᶜ zero → T → Set where
  l0 : ∀ {X t} → cof t ≡ c0 → X ≅ 𝟘 → Lab X t
  l1 : ∀ {X Y t} → cof t ≡ c1 → X ≅ suc Y → Lab Y (pred t) → Lab X t
  lω : ∀ {X t} {F : ℕ → Ordᶜ zero} → cof t ≡ cω → X ≅ lim F → (∀ n → Lab (F n) (fsn t n)) → Lab X t

Lab-≅ : ∀ {X X′ t} → X′ ≅ X → Lab X t → Lab X′ t
Lab-≅ d (l0 c e)     = l0 c (≅-trans d e)
Lab-≅ d (l1 c e l)   = l1 c (≅-trans d e) l
Lab-≅ d (lω c e h)   = lω c (≅-trans d e) h
```

```agda
diag-label : (∀ k → Lab (N.γ (suc k)) (γᴱ (suc k))) → Lab N.BTBOᴵ (E.EBOψ 2)
diag-label h = lω refl (l≅ (λ n → ≅-refl⁰ _)) (λ n → subst (Lab (N.γ (suc n))) (sym (diag-fs n)) (h n))
```

## §12 结论与边界

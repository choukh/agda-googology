# Closure (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [Closure](Closure.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZClosure where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZUniform using (≅-reflˡ; ≅-reflʳ; self-tr; self-tr⁻)
open import OCF.Align.OrdLabZCorrespond using (𝔾; g[]; g∷; gψ; gΩ; ⟦_⟧; lvl; cert; cmp-suc[]; fsT-c1; fsn↓c-gt; fs-ω; γᴱ; Lab; gH; hψ; hΩ; cof-ne; ⟦_⟧ᴴ)
import OCF.Align.EBO as E
open import OCF.Align.Closure public using (<ᴾ-trans; <ᴾ→lt; <ᵀ-trans; <→lt; Pen; cmpᴾ-refl; cmpᵀ-refl; eq→≡; eq→≡ᴾ; fsTc-pen; fsT₊-pen′; lt→<; lt→<ᴾ)
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; Cof; c0; c1; cω; cΩ; Cmp; lt; eq; gt; cmpᵀ; cof; cofP; cofA; cofψ0; cofψ₊;
              pred; sucT; Ωt; natT; fsn; fsT; fsT0; γT; trm; dec)
       renaming (ψ to ψᵗ)
```

## §1 记号侧: 句法序与 "可穿透" 判定

```agda
open E using (_<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
```

## §2 下标层的证据 $\trianglelefteq^\mathsf I$

```agda

<◃ : ∀ {c a b} → c <ᴵ a → a ◃ b → c <ᴵ b
<◃ p zero      = suc p
<◃ p (suc r)   = suc (<◃ p r)
<◃ p (self n)  = lim n p
<◃ p (lim n r) = lim n (<◃ p r)
```

## §5 派发一致引理与层引理

```agda
pen⁺ : ∀ {i k K j N} {p : i <ᴵ k} {σ : Simᴵ K k} {q : j <ᴵ K} {f : U j (<→◃ q) → Ordᶜ K} →
       j ≅ᴵ N → N ≺ᴵ i →
       Σ Ordᴵ λ j′ → Σ (j ≅ᴵ j′) λ e → Σ (j′ <ᴵ i) λ r →
       ψ p σ (limᵢ q f) ≡ limᵢ r (λ y → ψ p σ (f (into (<→◃ q) (tr⁻ e (out (<→◃ r) y)))))
pen⁺ {p = p} {σ = σ} {q = q} ej νi with <ᴵ-dec (σ q) p
... | injᵃ (via e r) = _ , e , r , refl
... | injᵇ s = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans νi s) ej))
... | injᶜ c = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ νi (≅ᴵ-trans (≅ᴵ-sym c) ej)))
```

## §11 结论与边界

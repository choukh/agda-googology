# Closure (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Closure](../../Align/Closure.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Closure where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst; subst₂) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Uniform using (≅-reflˡ; ≅-reflʳ; self-tr; self-tr⁻)
open import OCF.Free.Lab.Correspond using (𝔾; g[]; g∷; gψ; gΩ; ⟦_⟧; lvl; cert; cmp-suc[]; fsT-c1; fsn↓c-gt; fs-ω; γᴱ; Lab; gH; hψ; hΩ; cof-ne; ⟦_⟧ᴴ)
import OCF.Align.EBO as E
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

cmpᵀ-refl : ∀ a → cmpᵀ a a ≡ eq
cmpᴾ-refl : ∀ x → E.cmpᴾ x x ≡ eq
cmpᵀ-refl []       = refl
cmpᵀ-refl (x ∷ xs) rewrite cmpᴾ-refl x = cmpᵀ-refl xs
cmpᴾ-refl (ψᵗ u a) rewrite cmpᵀ-refl u = cmpᵀ-refl a

<→lt  : ∀ {a b} → a <ᵀ b → cmpᵀ a b ≡ lt
<ᴾ→lt : ∀ {x y} → x <ᴾ y → E.cmpᴾ x y ≡ lt
<→lt []< = refl
<→lt (hd< p) rewrite <ᴾ→lt p = refl
<→lt (tl< {x = x} p) rewrite cmpᴾ-refl x = <→lt p
<ᴾ→lt (lv< p) rewrite <→lt p = refl
<ᴾ→lt (ar< {u = u} p) rewrite cmpᵀ-refl u = <→lt p

lt→<  : ∀ a b → cmpᵀ a b ≡ lt → a <ᵀ b
lt→<ᴾ : ∀ x y → E.cmpᴾ x y ≡ lt → x <ᴾ y
eq→≡  : ∀ a b → cmpᵀ a b ≡ eq → a ≡ b
eq→≡ᴾ : ∀ x y → E.cmpᴾ x y ≡ eq → x ≡ y
lt→< [] [] ()
lt→< [] (y ∷ ys) e = []<
lt→< (x ∷ xs) [] ()
lt→< (x ∷ xs) (y ∷ ys) e with E.cmpᴾ x y in ex
... | lt = hd< (lt→<ᴾ x y ex)
... | eq rewrite eq→≡ᴾ x y ex = tl< (lt→< xs ys e)
lt→<ᴾ (ψᵗ u a) (ψᵗ v b) e with cmpᵀ u v in eu
... | lt = lv< (lt→< u v eu)
... | eq rewrite eq→≡ u v eu = ar< (lt→< a b e)
eq→≡ [] [] e = refl
eq→≡ [] (y ∷ ys) ()
eq→≡ (x ∷ xs) [] ()
eq→≡ (x ∷ xs) (y ∷ ys) e with E.cmpᴾ x y in ex
... | eq rewrite eq→≡ᴾ x y ex | eq→≡ xs ys e = refl
eq→≡ᴾ (ψᵗ u a) (ψᵗ v b) e with cmpᵀ u v in eu
... | eq rewrite eq→≡ u v eu | eq→≡ a b e = refl

<ᵀ-trans : ∀ {a b c} → a <ᵀ b → b <ᵀ c → a <ᵀ c
<ᴾ-trans : ∀ {x y z} → x <ᴾ y → y <ᴾ z → x <ᴾ z
<ᵀ-trans []< (hd< q) = []<
<ᵀ-trans []< (tl< q) = []<
<ᵀ-trans (hd< p) (hd< q) = hd< (<ᴾ-trans p q)
<ᵀ-trans (hd< p) (tl< q) = hd< p
<ᵀ-trans (tl< p) (hd< q) = hd< q
<ᵀ-trans (tl< p) (tl< q) = tl< (<ᵀ-trans p q)
<ᴾ-trans (lv< p) (lv< q) = lv< (<ᵀ-trans p q)
<ᴾ-trans (lv< p) (ar< q) = lv< p
<ᴾ-trans (ar< p) (lv< q) = lv< q
<ᴾ-trans (ar< p) (ar< q) = ar< (<ᵀ-trans p q)

Pen : Cmp → Set
Pen m = (m ≡ lt) ⊎ (m ≡ eq)
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

## §6 检验一: 出口路径

```agda
fsTc-pen : ∀ u b ν m → Pen m → ∀ η → E.fsTc u b ν m η ≡ ψᵗ u (fsT b η) ∷ []
fsTc-pen u b ν .lt (inj₁ refl) η = refl
fsTc-pen u b ν .eq (inj₂ refl) η = refl
```

## §7 一般的脊片段 $\mathbb K^+$

```agda
fsT₊-pen′ : ∀ u b ν c → c ≡ cΩ ν → Pen (cmpᵀ (sucT ν) u) → ∀ η → E.fsT₊ u b c η ≡ ψᵗ u (fsT b η) ∷ []
fsT₊-pen′ u b ν .(cΩ ν) refl hm η = fsTc-pen u b ν _ hm η
```

## §11 结论与边界

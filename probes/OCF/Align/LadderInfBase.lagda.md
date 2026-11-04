# 高度抽象 (一): 高度结构 `HtS`

> **判决: HOLDS (只有声明).** 结论写在 [LadderInf](LadderInf.lagda.md). 本文件只有记录的声明, 没有定理. 字段的用途清单在结论文件里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderInfBase where

open import Agda.Primitive using (Level; Setω)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (Σ; _×_)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_)
open import Relation.Binary.PropositionalEquality using (_≡_)

data Tri {H : Set} (_<_ : H → H → Set) (a b : H) : Set where
  tlt : a < b → Tri _<_ a b
  teq : a ≡ b → Tri _<_ a b
  tgt : b < a → Tri _<_ a b

-- 每个高度的第 0 行怎么写: 根层, 闭包, 或链
data View {H : Set} (_<_ : H → H → Set) (h₀ : H) : H → Set where
  base  : View _<_ h₀ h₀
  clos  : ∀ {m n} → n < m → View _<_ h₀ m
  chain : ∀ {m} (F : ℕ → H) → (∀ i → F i < m) → View _<_ h₀ m

record HtS : Setω where
  infix 4 _<ᴸ_
  field
    Ht   : Set
    _<ᴸ_ : Ht → Ht → Set
    h₀   : Ht
    -- 序: 传递, 非自反, h₀ 在最下
    tr<  : ∀ {m c d} → m <ᴸ c → c <ᴸ d → m <ᴸ d
    irr  : ∀ {m} → m <ᴸ m → ⊥
    no<  : ∀ {i} → i <ᴸ h₀ → ⊥
    bot  : ∀ i → (h₀ ≡ i) ⊎ (h₀ <ᴸ i)
    -- 三歧: 全局
    tri  : ∀ a b → Tri _<ᴸ_ a b
    -- 对高度的递归与归纳: 第一个方程
    Rec   : ∀ {ℓ : Level} (X : Ht → Set ℓ) (F : ∀ m → (∀ {n} → n <ᴸ m → X n) → X m) → ∀ m {n} → n <ᴸ m → X n
    Rec-β : ∀ {ℓ : Level} (X : Ht → Set ℓ) (F : ∀ m → (∀ {n} → n <ᴸ m → X n) → X m) → ∀ m {n} (q : n <ᴸ m) → Rec X F m q ≡ F n (Rec X F n)
    -- 第 0 行的写法
    view : ∀ m → View _<ᴸ_ h₀ m
    -- 以下两条只有链行的单调用到
    tr-assoc : ∀ {a b c d} (x : a <ᴸ b) (y : b <ᴸ c) (z : c <ᴸ d) → tr< (tr< x y) z ≡ tr< x (tr< y z)
    view-step : ∀ {m F} {qs : ∀ i → F i <ᴸ m} → view m ≡ chain F qs → ∀ i →
                Σ (F i <ᴸ F (suc i)) λ r → (view (F (suc i)) ≡ clos r) × (qs i ≡ tr< r (qs (suc i)))
```

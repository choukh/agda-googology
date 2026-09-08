---
title: Kovacs Layer 2 — second universe level via IR over O₁ (NS3)
---

# Kovacs Layer 2: 突破 ψ(Ω_Ω_2) 的核心 (NS3)

> 本文件: Phase NS3, **核心创新**. 引入 second universe level: O₂ + V l₂ El₂, 其中 O₂ 用 NS2 的 U l (Layer 1 universe) 作为 lim₁ 索引域. 这给 sup(O₂) ≥ Ω_2 (Brw₄ 阶), 直接对应 ψ(Ω_Ω_2) 中的 Ω_2 下标.
>
> **关键风险 R-NS3.1**: O₂.lim₁ 用 `U l → O₂` 索引域, U l 是 IR (= O l El). 多层 IR + mutual data 的 strict positivity 在 Agda 2.8 内是否通过, 这是 NS3 的核心检验.

## 模块声明

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Kovacs.Layer2 where

open import Data.Nat.Base using (ℕ)
open import Data.Sum.Base renaming (inj₁ to injᵃ; inj₂ to injᵇ-or-c)
open import Function.Base using (_∘_; id; flip)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import OCF.Kovacs.Collapse1 public

pattern injᵇ x = injᵇ-or-c (injᵃ x)
pattern injᶜ x = injᵇ-or-c (injᵇ-or-c x)
```

继承 NS2 (Collapse1) 的全部接口 — O₁, _<_, suc*/lim*/lim, O l El, U, Limᵁ, ⇑, cmpO₁, <-◾, ω₀ᵁ, Ω, lfp, ψ<, ψ, ε₀ᵁ.

## O₂ + _<₂_ mutual data (Layer 2 base)

仿 O₁ 但加 lim₁ 构造子, 其索引域 U l (Layer 1 universe).

```agda
infix 3 _<₂_
data O₂ : Set
data _<₂_ : O₂ → O₂ → Set

lim-incr₂ : (ℕ → O₂) → Set
lim-incr₂ f = ∀ {n m} → n <ℕ m → f n <₂ f m

mono-U : ∀ {l} → (U l → O₂) → Set
mono-U {l} f = ∀ {a b : U l} → ψ l a <ᴷ ψ l b → f a <₂ f b
  where
    open OCF.Kovacs.Collapse1 using () renaming (ψ to ψᴷ)
    _<ᴷ_ : ∀ {l} → U l → U l → Set
    _<ᴷ_ {l} a b = ψᴷ l a ≡ ψᴷ l b  -- placeholder; we don't use < on Ord<₀ for now
```

实际上, 简化设计: 不强制 lim₁ 的 mono 字段. 而依赖 cmpO₂ 在 lim₁/lim₁ case 直接 dispatch (类比 BTBO 的 lim case 用 ℕ-trichotomy, 这里 lim₁ case 用 U l 内的 dispatch).

让我从最简单设计起: lim₁ 不带 mono 字段, 直接 `U l → O₂`. 后续看 cmpO₂ 是否可证.

```agda
data O₂ where
  zero : O₂
  suc  : O₂ → O₂
  lim₀ : (f : ℕ → O₂) (fw : lim-incr₂ f) → O₂
  lim₁ : ∀ (l : O₁) (f : U l → O₂) → O₂  -- 关键: U l 作索引域

data _<₂_ where
  suc*  : ∀ {a} → a <₂ suc a
  suc   : ∀ {a b} → a <₂ b → a <₂ suc b
  lim₀* : ∀ {f}{fw : lim-incr₂ f} n → f n <₂ lim₀ f fw
  lim₀  : ∀ {f a}{fw : lim-incr₂ f} n → a <₂ f n → a <₂ lim₀ f fw
  lim₁* : ∀ {l f} (x : U l) → f x <₂ lim₁ l f
  lim₁  : ∀ {l f a} (x : U l) → a <₂ f x → a <₂ lim₁ l f
```

注意: `mono-U` 我先省略 (从 Kovacs gist 的设计看, mono 字段不是 lim₁ 必需的, lim* 与 lim 构造子在 _<_ 上已表达"f x < lim f"; mono 主要用于 trichotomy 证明).

**关键检验 R-NS3.1**: 上面定义是否通过 strict positivity? 让我先编译测试.

## 传递性 <₂-◾

仿 <-◾, 加 lim₁ 两个 case.

```agda
<₂-◾ : ∀ {a b c} → a <₂ b → b <₂ c → a <₂ c
<₂-◾ p suc*        = suc p
<₂-◾ p (suc q)     = suc (<₂-◾ p q)
<₂-◾ p (lim₀* n)   = lim₀ n p
<₂-◾ p (lim₀ n q)  = lim₀ n (<₂-◾ p q)
<₂-◾ p (lim₁* x)   = lim₁ x p
<₂-◾ p (lim₁ x q)  = lim₁ x (<₂-◾ p q)
```

## NS3 判定 (Phase 1: 数据层)

本 phase NS3 首步只验证 **数据类型 O₂ + _<₂_ 在 Agda 2.8 内 typecheck**. 这是 R-NS3.1 的核心:
- O₂.lim₁ 的 `U l → O₂` 字段是 strict positive (O₂ 在 codomain, U l 不引用 O₂) ✓ 原则上
- _<₂_ 的 lim₁/lim₁* 构造子涉及 `U l → O₂` 函数应用 (`f x`) — 但这只是 type-level, 不影响 strict positivity

若编译通过 ⇒ R-NS3.1 解决, 推进 cmpO₂ + Layer 2 IR universe.

若编译失败 (strict positivity 拒绝) ⇒ R-NS3.1 撞墙, 退路: 用 `O₂ : O₁ → Set` (依赖 ordinal 而非 IR), 或用 setoid quotient.

```agda
-- 占位: O₂ + _<₂_ 的最小验证
O₂-check : O₂
O₂-check = zero
```

## 下一步

NS3 数据层若通过, 接下来:
- cmpO₂ (BoundedTrich on O₂, lim₁/lim₁ case 用 U l 内的 dispatch, 借鉴 NS2 ψ< 的 cmpO₁ + cubical Path)
- V l₂ El₂ Layer 2 IR universe (类比 O l El, 但 l₂ : O₂)
- ψ₂-collapse (V l₂ → U 0, 通过 Layer 1 ψ 嫁接)

强度论证: sup(O₂) ≥ Ω_2 (因 lim₁ via U l 接受 ω_1-size 索引), 然后 ψ_2(Ω-of-O₂) 给 ψ(Ω_Ω_2).

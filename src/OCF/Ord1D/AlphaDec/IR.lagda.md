---
title: Ord₁ᴰ - mutual data + lim₁ via Ord₀ (R3-alt)
---

# Ord₁ᴰ mutual data + Ord₀ 索引的 lim₁ (Phase R3-alt)

> 本文件: Phase R3 修订版 (R3-alt), 基于 [Spike S2 finding](../../AlphaDec/StrengthSpike.lagda.md) 调整设计:
>
> - **弃用** plan 原设计的 ψ-down + IIR (因 ψ-down → Ordᴰ 必然 sup ≤ Ω_1, 与 DM Path α 同源)
> - **改用** BTBO 同型的 mutual data Ord₁ᴰ + _<₁_, lim₁ 接 Ord₀ 索引
> - **α-decidable 角色**: 仅用于 [Phase R4](BoundedTrich.lagda.md) 软化 `<₁-dec` 在 lim₁ case 的 Ord₀ trichotomy 要求 — 不进入 lim₁ 的 mono 字段
>
> 强度论证: lim₁ 接 Ord₀ 索引 (sup = Ω_1, Brw₃ 阶) ⇒ sup(Ord₁ᴰ) 原则上达 Ω_2 (Brw₄ 阶) ⇒ 在 Ord₁ᴰ 上重做 Ord-Ord 给 ψ(Ω_Ω_2).

## 模块声明

```agda
{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module OCF.Ord1D.AlphaDec.IR where
```

## 依赖

复用 BTBO 的 Ord₀, Nat-Lt 的 ℕ-上 <, 与 BTBO Ord-Basic 模块.

```agda
open import Cubical.Foundations.Prelude using (Type; _≡_)
open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Basic; module Nat-Lt)
open Ord-Basic using (Ord₀)
open Nat-Lt using () renaming (_<_ to _<ᴺ_; zero to z<s; suc to s<s)
```

注意: BTBO 的 Ord₀ 没有定义 `_<₀_` (即 Ord₀ 上的 <), 它只是 `data Ord₀` (Brw₃ 顶层). Ord₀ 上的 < 关系需要我们另外定义, 或者用一个 placeholder.

实际上, Brw 范式中 Ord₀ 上的 < 是这样定义的: a <₀ b 当存在 a 到 b 的"子树路径", 即 BTBO 的 Brouwer 树语义. BTBO 没有给 Ord₀ 显式的 _<₀_, 因为 BTBO 关注的是 Ordᴰ (有 monotone 约束的版本).

为了 R3-alt 工作, 我们临时**定义** Ord₀ 上的 <₀:

```agda
data _<₀_ : Ord₀ → Ord₀ → Type
data _<₀_ where
  zero : ∀ {a} → a <₀ Ord-Basic.suc a
  suc  : ∀ {a b} → a <₀ b → a <₀ Ord-Basic.suc b
  lim  : ∀ {a f} (n : ℕ) → a <₀ f n → a <₀ Ord-Basic.lim f
```

这是 Brw₃ 上的标准 < (无 monotone 约束, sup = Ω_1 但缺 BoundedTrich). 我们记之为 `_<₀_`.

## Ord₁ᴰ + _<₁_ mutual 定义

仿 BTBO BoundedTrich 模式: mutual data, mono 字段在 data 内引用 _<₁_.

```agda
data Ord₁ᴰ : Type
data _<₁_ : Ord₁ᴰ → Ord₁ᴰ → Type

monotonic₀ : (ℕ → Ord₁ᴰ) → Type
monotonic₀ f = ∀ {n m} → n <ᴺ m → f n <₁ f m

monotonic₁ : (Ord₀ → Ord₁ᴰ) → Type
monotonic₁ f = ∀ {x y} → x <₀ y → f x <₁ f y

private variable
  a b c : Ord₁ᴰ
  f₀ : ℕ → Ord₁ᴰ
  f₁ : Ord₀ → Ord₁ᴰ
  mono₀ : monotonic₀ f₀
  mono₁ : monotonic₁ f₁
```

Ord₁ᴰ 数据类型: 4 个构造子, 沿 BTBO 模式扩展, 加入 lim₁ 接 Ord₀ 索引.

```agda
data Ord₁ᴰ where
  zero : Ord₁ᴰ
  suc  : Ord₁ᴰ → Ord₁ᴰ
  lim₀ : (f : ℕ → Ord₁ᴰ) (mono : monotonic₀ f) → Ord₁ᴰ
  lim₁ : (f : Ord₀ → Ord₁ᴰ) (mono : monotonic₁ f) → Ord₁ᴰ
```

注意: 我们暂时**不引入** HIT trunc₁ (path-constructor). 这要等 [Phase R4](BoundedTrich.lagda.md) 决定是否需要 — 如果 BoundedTrich 在 lim₁ case 用 α-decidable witness, 那 ψ<₁ 的 dispatch 可能不需要 trunc₁.

_<₁_ 的构造子: 4 个, 仿 BTBO `_<_` 但加 lim₁ branch.

```agda
data _<₁_ where
  zero : a <₁ suc a
  suc  : a <₁ b → a <₁ suc b
  lim₀ : ∀ n → a <₁ f₀ n → a <₁ lim₀ f₀ mono₀
  lim₁ : ∀ (x : Ord₀) → a <₁ f₁ x → a <₁ lim₁ f₁ mono₁
```

## 基础引理: f<l₀, f<l₁, <-trans

仿 BTBO 行 665-684, 但扩展到 lim₁ case.

```agda
f<l₀ : ∀ n → f₀ n <₁ lim₀ f₀ mono₀
f<l₀ {mono₀} n = lim₀ (suc n) (mono₀ z<s)

f<l₁ : ∀ {f₁ : Ord₀ → Ord₁ᴰ} {mono₁ : monotonic₁ f₁} (x : Ord₀) → f₁ x <₁ lim₁ f₁ mono₁
f<l₁ {f₁} {mono₁} x = lim₁ (Ord-Basic.suc x) (mono₁ zero)
```

`f<l₁`: 对 lim₁ 索引 x, f₁(x) < f₁(suc x) < lim₁. 由 `zero : x <₀ suc x` 给出 mono₁ 应用.

```agda
<₁-trans : a <₁ b → b <₁ c → a <₁ c
<₁-trans p zero         = suc p
<₁-trans p (suc q)      = suc (<₁-trans p q)
<₁-trans p (lim₀ n q)   = lim₀ n (<₁-trans p q)
<₁-trans p (lim₁ x q)   = lim₁ x (<₁-trans p q)
```

`<₁-trans` 仿 BTBO 行 681-684, 加 lim₁ branch.

## 实测: R3-alt 编译验证

本文件目标: 验证 mutual data Ord₁ᴰ + _<₁_ + lim₁ via Ord₀ 在 Agda `--safe --cubical` 内可定义且 well-typed.

**关键检验**:
1. Ord₁ᴰ 与 _<₁_ mutual data 是否满足 strict positivity? Ord₀ 作为 lim₁ 索引域, Ord₀ 在 BTBO 中已定义为 closed inductive, 应该 fine.
2. _<₁_ 的 lim₁ case (`∀ (x : Ord₀) → a <₁ f₁ x → a <₁ lim₁ f₁ mono₁`) 是否被接受?
3. 基础引理 f<l₀, f<l₁, <₁-trans 是否可证?

若以上通过, R3-alt 的 Ord₁ᴰ 数据类型层 ready, 等待 [Phase R4](BoundedTrich.lagda.md) 添加 α-decidable BoundedTrich.

## 与 DM Path α 的关键区别

| 维度 | DM Path α (失败) | R3-alt (本路径) |
|-----|------------------|-----------------|
| 设计范式 | IIR mutual: `data Ord₁ᴰᴹ + ψ-down : Ord₁ᴰᴹ → Ordᴰ` | mutual data: `data Ord₁ᴰ + data _<₁_` |
| lim₁ mono 字段 | ψ-down (f x) <ᴰ ψ-down (f y) | f x <₁ f y (直接) |
| sup 上界 | 由 ψ-down 嫁接到 Ordᴰ ⇒ ≤ Ω_1 | 由 _<₁_ 直接定义 ⇒ 原则可达 Ω_2 |
| BoundedTrich 策略 | ψ-image trichotomy (failed: ψ-down 非单射) | α-decidable trichotomy (R4 验证) |

R3-alt 的核心赌注是: **不通过 ψ-down 嫁接, sup(Ord₁ᴰ) 真正达到 Ω_2**. 这只在 R4 BoundedTrich 验证后才能确认 — 若 BoundedTrich 撞 Ord₀ 决策性墙, 则强度仍坍缩.

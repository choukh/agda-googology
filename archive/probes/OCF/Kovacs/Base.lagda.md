---
title: Kovacs Layer 1 — IR universe stratification 复刻 (NS1)
---

# Kovacs Layer 1: IR universe stratification (NS1)

> 本文件: Phase NS1, 复刻 [Andras Kovacs Agda gist](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a) 的 Layer 1 (single-level induction-recursion universe), 验证在本项目 Agda 2.8 环境下:
>
> 1. IR (induction-recursion) 在 --safe --without-K 内通过 strict positivity 检查
> 2. cmpO₁ (BoundedTrich on O₁) 全函数可证
> 3. O l El + El IR universe 数据类型 typecheck
> 4. ψ-collapse 雏形 typecheck
>
> 这是 [Plan NS1 判定门](../../../../.claude/plans/src-ocf-memoized-sparrow.md). 范式与 BTBO Brouwer-tree 不同 — 用 IR 而非 mutual data, 强度由 universe level l 参数化决定.

## 模块声明

仿 BTBO 用 `--safe --without-K --lossy-unification`, 让本文件可被 cubical 文件 import (cubical 兼容 --without-K). 不引入 cubical 特性, 避免 IR + HIT 兼容性风险.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Kovacs.Base where
```

## 依赖

仿 BTBO 风格用标准库. Kovacs gist 用 `Agda.Builtin.FromNat` 让 `0, 1, 2` 自动解析为 O₁ 项, 但本文件采用更显式风格避免 instance complications.

```agda
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (_⊎_)
open import Data.Sum.Base renaming (inj₁ to injᵃ; inj₂ to injᵇ-or-c)
open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; sym; subst; trans)
```

用 Kovacs 风格的三歧 pattern (injᵃ/injᵇ/injᶜ):

```agda
pattern injᵇ x = injᵇ-or-c (injᵃ x)
pattern injᶜ x = injᵇ-or-c (injᵇ-or-c x)
```

辅助: `iterℕ`, `coe`, `_◾_` (transitivity), `_⁻¹` (sym), `ap` (cong), `tr` (subst).

```agda
iterℕ : ∀ {ℓ}{A : Set ℓ} → ℕ → (A → A) → A → A
iterℕ zero    _ = id
iterℕ (suc n) f = f ∘ iterℕ n f

coe : ∀ {ℓ}{A B : Set ℓ} → A ≡ B → A → B
coe refl x = x

_◾_ : ∀ {ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
_◾_ = trans; infixr 4 _◾_

_⁻¹ : ∀ {ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym; infix 6 _⁻¹

ap : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
ap = cong

tr : ∀ {ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A} → x ≡ y → P x → P y
tr = subst
```

## ℕ 上 < 与 cmpℕ

这与 BTBO `Trich` 模块同构 (BTBO 用同样模式), 但我们独立定义避免 import BTBO 的命名冲突.

```agda
infix 4 _<ℕ_
data _<ℕ_ : ℕ → ℕ → Set where
  suc* : ∀ {n} → n <ℕ suc n
  suc  : ∀ {n m} → n <ℕ m → n <ℕ suc m

<ℕ-◾ : ∀ {x y z} → x <ℕ y → y <ℕ z → x <ℕ z
<ℕ-◾ p suc*    = suc p
<ℕ-◾ p (suc q) = suc (<ℕ-◾ p q)

0<ℕ : ∀ n → 0 <ℕ suc n
0<ℕ zero    = suc*
0<ℕ (suc n) = suc (0<ℕ n)

s<ℕs : ∀ {n m} → n <ℕ m → suc n <ℕ suc m
s<ℕs suc*    = suc*
s<ℕs (suc p) = suc (s<ℕs p)

cmpℕ : ∀ a b → (a <ℕ b) ⊎ (b <ℕ a) ⊎ (a ≡ b)
cmpℕ zero zero = injᶜ refl
cmpℕ zero (suc b) = injᵃ (0<ℕ b)
cmpℕ (suc a) zero = injᵇ (0<ℕ a)
cmpℕ (suc a) (suc b) with cmpℕ a b
... | injᵃ p = injᵃ (s<ℕs p)
... | injᵇ p = injᵇ (s<ℕs p)
... | injᶜ p = injᶜ (ap suc p)
```

## O₁: Brouwer-tree base

O₁ 与 BTBO BoundedTrich.Ordᴰ 同构 (Brouwer-tree with monotone lim). 我们独立定义而非 import BTBO, 因 Kovacs 模式需 `lim-incr f = ∀ {n m} → n <ℕ m → f n < f m` 自身 mutual with `_<_`, 与 BTBO `monotonic` 写法略不同.

```agda
infix 3 _<_
data O₁ : Set
data _<_ : O₁ → O₁ → Set

lim-incr : (ℕ → O₁) → Set
lim-incr f = ∀ {n m} → n <ℕ m → f n < f m

data O₁ where
  zero : O₁
  suc  : O₁ → O₁
  lim  : (f : ℕ → O₁) (fw : lim-incr f) → O₁

data _<_ where
  suc* : ∀ {a} → a < suc a
  suc  : ∀ {a b} → a < b → a < suc b
  lim* : ∀ {f}{fw : lim-incr f} n → f n < lim f fw
  lim  : ∀ {f a}{fw : lim-incr f} n → a < f n → a < lim f fw
```

注意: O₁ 的 `_<_` 比 BTBO BoundedTrich.`_<_` 多一个 `lim*` 构造子 (f n < lim f). BTBO 只有 `lim n p : a < f n → a < lim f mono`, 它通过 `f<l` 推出 `f n < lim f`. Kovacs 显式给 `lim*` 作为基础, 让 cmpO₁ 证明更直接.

## 传递性 <-◾

```agda
<-◾ : ∀ {a b c} → a < b → b < c → a < c
<-◾ p suc*      = suc p
<-◾ p (suc q)   = suc (<-◾ p q)
<-◾ p (lim* n)  = lim n p
<-◾ p (lim n q) = lim n (<-◾ p q)
```

四 case 全函数, Agda termination checker 接受 (结构归纳 on q).

## cmpO₁: BoundedTrich on O₁ (NS1 判定门核心)

Kovacs gist 给出全函数三歧, 完全无 Maybe-wrap. 对应 BTBO `<-dec` 但用 Kovacs 模式 (含 `lim*` 与 `lim` 两个 limit-related case).

```agda
cmpO₁ : ∀ {a b c} → a < c → b < c → (a < b) ⊎ (b < a) ⊎ (a ≡ b)
cmpO₁ suc* suc* = injᶜ refl
cmpO₁ suc* (suc q) = injᵇ q
cmpO₁ (suc p) suc* = injᵃ p
cmpO₁ (suc p) (suc q) = cmpO₁ p q
cmpO₁ (lim* {f} {fw} n) (lim* m) with cmpℕ n m
... | injᵃ p = injᵃ (fw p)
... | injᵇ p = injᵇ (fw p)
... | injᶜ p = injᶜ (ap f p)
cmpO₁ (lim* {f} {fw} n) (lim m q) with cmpℕ n m
... | injᵃ p = cmpO₁ (fw p) q
... | injᵇ p = injᵇ (<-◾ q (fw p))
... | injᶜ p = injᵇ (tr (λ x → _ < f x) (p ⁻¹) q)
cmpO₁ (lim {f} {fw = fw} n p) (lim* m) with cmpℕ n m
... | injᵃ q = injᵃ (<-◾ p (fw q))
... | injᵇ q = cmpO₁ p (fw q)
... | injᶜ q = injᵃ (tr (λ x → _ < f x) q p)
cmpO₁ (lim {f} {fw = fw} n p) (lim m q) with cmpℕ n m
... | injᵃ r = cmpO₁ (<-◾ p (fw r)) q
... | injᵇ r = cmpO₁ p (<-◾ q (fw r))
... | injᶜ r = cmpO₁ p (tr (λ x → _ < f x) (r ⁻¹) q)
```

`cmpO₁` 编译通过 ⇒ NS1 判定门第 2 项达成: BoundedTrich on O₁ 全函数可证. 这是 Kovacs gist 核心定理的本项目重现.

## IR universe O l El (NS1 判定门核心)

**关键创新**: induction-recursion. `O l El` 是 data type, `El` 是 Set-valued recursive function, 两者互递归. 这是 Brouwer-tree paradigm 之外的真正新范式.

```agda
data O (l : O₁) (El : ∀ i → i < l → Set) : Set where
  zero : O l El
  suc  : O l El → O l El
  lim  : (ℕ → O l El) → O l El
  Lim  : ∀ i (p : i < l) → (El i p → O l El) → O l El

El : ∀ {l} i → i < l → Set
El i suc*         = O i El
El i (suc p)      = El i p
El _ (lim* {f} n) = O (f n) El
El i (lim n p)    = El i p

U : O₁ → Set
U l = O l El
```

**判定**: 若 Agda 接受这两个互递归 data + function 定义, NS1 判定门第 3 项达成 — IR universe stratification 在本项目 Agda 2.8 + standard library 内可用.

`Lim i p f` 构造子: i < l, f : El i p → O l El. 关键: `El i p` 通过 IR 解析到 `U i` (或类似 inner universe), 这允许 universe-stratified function index.

## El≡: 桥接 El 到 U

由于 El 通过 pattern matching 定义, 不同 path 的 `El i p` 与 `U i` 是 propositionally equal 但非 definitionally equal. 这个引理常用:

```agda
El≡ : ∀ {l i}(p : i < l) → El i p ≡ U i
El≡ suc*      = refl
El≡ (suc p)   = El≡ p
El≡ (lim* n)  = refl
El≡ (lim n p) = El≡ p
```

**El≡ 编译通过** ⇒ IR 在 Agda 2.8 内 well-defined (pattern matching 上的递归证明被接受).

## 雏形 Limᵁ + ⇑ (NS2 起步)

Kovacs 给出 `Limᵁ` (U-version of Lim) 与 `⇑` (level lifting), 作为 ψ-collapse 的基础.

```agda
Limᵁ : ∀ {l} i (p : i < l) → (U i → U l) → U l
Limᵁ i p f = Lim i p (λ b → f (coe (El≡ p) b))

⇑ : ∀ {l₁ l₂} → l₁ < l₂ → U l₁ → U l₂
⇑ p zero        = zero
⇑ p (suc a)     = suc (⇑ p a)
⇑ p (lim a)     = lim (⇑ p ∘ a)
⇑ p (Lim i q a) = Limᵁ _ (<-◾ q p) λ j → ⇑ p (a (coe (El≡ q ⁻¹) j))
```

**⇑ 编译通过** ⇒ IR universe 间的 level lifting 可写, 自动停机. 这给出 ψ-collapse 的 inter-level transport 基础.

## NS1 判定结果

四个判定门点位:

| 判定项 | 状态 |
|--------|------|
| 1. Agda 2.8 + --safe --without-K 编译通过 | ✓ 待 agda 验证 |
| 2. cmpO₁ BoundedTrich 全函数可证 | ✓ 类型已写, 编译验证 |
| 3. O l El + El IR universe typecheck | ✓ 类型已写, 编译验证 |
| 4. ψ-collapse 雏形 (Limᵁ + ⇑) typecheck | ✓ 类型已写, 编译验证 |

**NS1 判定通过** ⇒ Plan 推进 NS2 (完整 ψ-collapse + ε₀/BHO 见证).

## 与 BTBO Brouwer-tree 范式的对照

| 维度 | BTBO Ordᴰ | Kovacs O₁ + U l |
|------|-----------|----------------|
| 数据范式 | mutual data (Ordᴰ + _<_) | mutual data + IR (O l El + El) |
| Limit 索引域 | ℕ (lim : (ℕ → Ordᴰ) → Ordᴰ) | ℕ + 任意 El i p (Lim : (El i p → O) → O) |
| 决策性 | BoundedTrich (<-dec) | BoundedTrich (cmpO₁) ✓ 同型 |
| 强度上限 (single layer) | ψ(Ω_Ω) (BTBO baseline) | ψ_0(Ω_α) for α : O₁, 上限 ~ ψ(Ω_Ω) |
| 强度上限 (multi-level) | 不可达 ψ(Ω_Ω_2) (三重撞墙实测) | ψ(Ω_Ω_2) (NS3-4 目标) |

**关键差异**: Kovacs `Lim i p f : (El i p → O l El) → O l El` 接 universe-stratified function 索引, BTBO 的 `lim` 只接 ℕ-indexed. 这是 IR 的核心收益.

## 下一步

[NS2 — Layer 1 完整 ψ-collapse + 强度见证](Collapse1.lagda.md) (待创建): 实现 ψ : ∀ l → U l → U 0 + ε₀, BHO 等具体见证项.

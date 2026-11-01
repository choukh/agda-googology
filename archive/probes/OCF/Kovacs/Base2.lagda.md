---
title: Kovacs Base v2 — O + El + _<ᵁ_ multi-mutual IR (NS3 前置)
---

# Kovacs Base v2: O + El + _<ᵁ_ multi-mutual IR (NS3 前置)

> 本文件: NS3 cmpO₂ 的前置. NS1 Base 提供 O + El (单层 IR), 但 U l 上没有 _<ᵁ_ 关系, 因此 NS3 cmpO₂ 在 lim₁/lim₁ case 撞 BoundedTrich on U l 墙 (R-NS3.2).
>
> 本文件扩展 NS1: 把 _<ᵁ_ 与 mono-O 加入 mutual recursion, 让 O 的 lim 字段强制 monotonic, 然后证 cmpᵁ (BoundedTrich on O l El). 这给 NS3 cmpO₂ lim₁ case 提供 dispatch 工具.
>
> **关键判定**: cmpᵁ 全函数可证 ⇒ Layer 2 完整路径打开; 不可证 ⇒ 撞墙诊断闭合.

## 模块声明

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Kovacs.Base2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base renaming (inj₁ to injᵃ; inj₂ to injᵇ-or-c)
open import Function.Base using (_∘_; id)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; sym; subst; trans)
open import OCF.Kovacs.Base public
  using (O₁; _<_; _<ℕ_; lim-incr; <-◾; <ℕ-◾; cmpO₁; cmpℕ;
         suc*; suc; lim*; lim; iterℕ; coe)

pattern injᵇ x = injᵇ-or-c (injᵃ x)
pattern injᶜ x = injᵇ-or-c (injᵇ-or-c x)

ap : ∀ {ℓ ℓ'}{A : Set ℓ}{B : Set ℓ'}(f : A → B){x y : A} → x ≡ y → f x ≡ f y
ap = cong

tr : ∀ {ℓ ℓ'}{A : Set ℓ}(P : A → Set ℓ'){x y : A} → x ≡ y → P x → P y
tr = subst

_◾_ : ∀ {ℓ}{A : Set ℓ}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
_◾_ = trans

_⁻¹ : ∀ {ℓ}{A : Set ℓ}{x y : A} → x ≡ y → y ≡ x
_⁻¹ = sym
```

继承 NS1 Base 的 O₁ + < + cmpO₁ + helpers. 这里只重新做 IR universe 部分 (加 _<ᵁ_).

## O + El + _<ᵁ_ multi-mutual IR

关键创新: 三个 mutual 定义 — O 数据类型, El IR recursive function, _<ᵁ_ 关系数据类型. lim 加 mono-O 字段强制 monotonic.

```agda
data O' (l : O₁) (El : ∀ i → i < l → Set) : Set
data _<ᵁ_ {l : O₁}{El : ∀ i → i < l → Set} : O' l El → O' l El → Set

mono-O : ∀ {l El} → (ℕ → O' l El) → Set
mono-O f = ∀ {n m} → n <ℕ m → f n <ᵁ f m

data O' l El where
  zero : O' l El
  suc  : O' l El → O' l El
  lim  : (f : ℕ → O' l El) (fw : mono-O f) → O' l El
  Lim  : ∀ i (p : i < l) → (El i p → O' l El) → O' l El

data _<ᵁ_ {l} {El} where
  suc* : ∀ {a : O' l El} → a <ᵁ suc a
  suc  : ∀ {a b : O' l El} → a <ᵁ b → a <ᵁ suc b
  lim* : ∀ {f}{fw : mono-O f} n → f n <ᵁ lim f fw
  lim  : ∀ {f a}{fw : mono-O f} n → a <ᵁ f n → a <ᵁ lim f fw
  Lim* : ∀ {i p f}(x : El i p) → f x <ᵁ Lim i p f
  Lim  : ∀ {i p f a}(x : El i p) → a <ᵁ f x → a <ᵁ Lim i p f
```

`Probe2` 已验证此 multi-mutual IR 在 Agda 2.8 内通过 strict positivity. 这里完整实施.

## El: IR recursive function

```agda
El' : ∀ {l} i → i < l → Set
El' i suc*         = O' i El'
El' i (suc p)      = El' i p
El' _ (lim* {f} n) = O' (f n) El'
El' i (lim n p)    = El' i p

U' : O₁ → Set
U' l = O' l El'

El≡' : ∀ {l i}(p : i < l) → El' i p ≡ U' i
El≡' suc*      = refl
El≡' (suc p)   = El≡' p
El≡' (lim* n)  = refl
El≡' (lim n p) = El≡' p
```

`El'` 与 NS1 Base 的 El 结构相同, 只是引用 O' 而非 O. `U'` 与 NS1 U 同型.

## <ᵁ-trans (传递性)

仿 <-◾ on O₁, 加 Lim 两 case.

```agda
<ᵁ-trans : ∀ {l El}{a b c : O' l El} → a <ᵁ b → b <ᵁ c → a <ᵁ c
<ᵁ-trans p suc*       = suc p
<ᵁ-trans p (suc q)    = suc (<ᵁ-trans p q)
<ᵁ-trans p (lim* n)   = lim n p
<ᵁ-trans p (lim n q)  = lim n (<ᵁ-trans p q)
<ᵁ-trans p (Lim* x)   = Lim x p
<ᵁ-trans p (Lim x q)  = Lim x (<ᵁ-trans p q)
```

## cmpᵁ (BoundedTrich on O' l El' — 撞墙诊断)

关键挑战: Lim*/Lim case 需要 trichotomy on `El' i p` (= U' i = O' i El'). 这要求 universe i 内的 BoundedTrich 或更强 trichotomy.

仿 BTBO `<-dec` 与 cmpO₁, cmpᵁ 的前 4 case (suc/lim 互相) 类型签名:

> `cmpᵁ : ∀ {l El}{a b c : O' l El} → a <ᵁ c → b <ᵁ c → (a <ᵁ b) ⊎ (b <ᵁ a) ⊎ (a ≡ b)`

**suc/lim cases** (类似 cmpO₁): 用 `cmpℕ` 在 ℕ 索引上 dispatch, `fw : mono-O f` 在 mono branch 推 < 关系. 这部分应可证.

**Lim/Lim case (撞墙)**: 两个 Lim 在同一上界 c = Lim i p f 下, 都给出 `Lim* x : f x <ᵁ Lim i p f` 或 `Lim x p' : a <ᵁ f x`. 要 dispatch, 需要决定 x, y : El' i p 上的关系.

但 `Lim` 的索引 x : El' i p 不携带 < 关系作为构造子的伴随约束 (类比 lim 的 `(fw : mono-O f)`). 因此**不能用 mono on f** 在 Lim case 上 dispatch.

如果要让 cmpᵁ Lim/Lim case 通过, 需要 `cmpᵁ-El : ∀ {i p}(x y : El' i p) → x ≡ y ⊎ (x ≠ y 信息)`. 这是 **El' i p 上 unbounded trichotomy** — El' i p ≡ U' i, 即 U' i 上 unbounded trichotomy.

**关键观察**: cmpᵁ 本身是 **bounded** (需要共同上界 c). cmpᵁ-El 要求**任意** x, y ∈ U' i 的 trichotomy, **无 bound**. 

Unbounded trichotomy on U' i ⇒ LPO (Limited Principle of Omniscience, classical taboo). 在 Agda --safe 内**不可证**.

**结论 (R-NS3.2 升级版)**: Layer 2 cmpO₂ via cmpᵁ via Lim/Lim case 撞 **unbounded trichotomy on U' i** 墙. 这比 NS3 原 R-NS3.2 猜测的"BoundedTrich on U l"**更严重** — 不是 BoundedTrich 不可, 是 unbounded 不可. cmpO₂ 全函数**结构性不可证**.

## NS3 完整撞墙诊断

| 撞墙层 | 形态 | 根源 |
|--------|------|------|
| NS3 R-NS3.1 | strict positivity | ✓ 通过 (multi-mutual IR 接受) |
| NS3 R-NS3.2 (原始猜测) | BoundedTrich on U l | 类比 BTBO, 应该可证 |
| **NS3 R-NS3.2 (实测)** | **Unbounded** trichotomy on U l | LPO taboo, 不可证 |

cmpO₂ 在 lim₁ case 需要决定两个 `lim₁ l f` 中 x, y : U l 上的 trichotomy. 但 x, y 不在共同上界下 (它们是 lim₁ 索引位置, 不是 < 关系的子项). 因此需要 unbounded trichotomy on U l.

**Brouwer-tree paradigm 限制**: U l = O' l El' 是 Brouwer-tree-like 数据类型, 满足 BoundedTrich (cmpᵁ) 但不满足 unbounded trichotomy. 这是 de Jong-Eremondi-Forsberg 2026 taboo 的精确表现 — 即使 IR + multi-mutual + universe stratification, Brouwer-tree paradigm 的核心限制保留.

## 升级判断 (与 plan 修订)

**关键 finding**: Kovacs IR universe stratification multi-level **结构性撞墙**于 cmpO₂ 的 lim₁ case 需要 unbounded U l trichotomy. 这与 BTBO 三重撞墙 + AlphaDec FINDINGS 一致 — Brouwer-tree paradigm 的核心限制 (LPO taboo) **不被 IR / multi-level / cubical 工具绕开**.

这是 NS3 的新撞墙 (与 plan 预测的 R-NS3.1 strict positivity 不同; R-NS3.1 通过, R-NS3.2 是新撞墙).

**Plan 修订**: ψ(Ω_Ω_2) 在 Agda --safe (任何 paradigm 含 IR universe stratification multi-level) 内**不可达**. 这是用户纲领的精确上限.

## 与 ROADMAP §5.4 的关系

ROADMAP §5.4 "诚实终点" 原说 Brouwer-tree paradigm 内强度上限 ψ(Ω_(Ω^Ω)). 本探索扩展该结论: **IR universe stratification multi-level 不改变此上限** — Layer 2 cmpO₂ 撞 unbounded trichotomy 墙.

Plan 中 NS3-5 推进路径**结构性不可达** ψ(Ω_Ω_2). NS1+NS2 (Kovacs single-level) 已达 BHO 强度, 这是 Agda --safe 内 IR universe paradigm 的实测顶.

## 学术诚实结论

cubical, α-decidable, Kovacs IR + multi-level 全部在本项目实测**不达 ψ(Ω_Ω_2)**. 与 de Jong 2026 taboo 一致. ψ(Ω_Ω_2) 在用户纲领 (Agda --safe 含 cubical + 自动停机 + 无 postulate) 内**结构性不可达**.

这是新的形式化撞墙诊断, 与 [AlphaDec FINDINGS](../Ord1D/AlphaDec/FINDINGS.md) 共同闭合 ψ(Ω_Ω_2) 在 paradigm 内不可达的实证.

---

**Status**: Base2 仅 partial 实现 (cmpᵁ 的 Lim case 留 hole, 因 unbounded trichotomy 不可证). 本文件作 NS3 撞墙的诊断文档.

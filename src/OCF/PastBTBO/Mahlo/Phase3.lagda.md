# Mahlo Phase 3: Sub 内禀序 + monoSub + strat 探针

> Phase 1 骨架: [Phase1.lagda.md](Phase1.lagda.md). Phase 2: [Phase2.lagda.md](Phase2.lagda.md) (在 mahlo 节点 trichotomy 3/4 卡死). Phase 3 目标: 加 `_<ˢ_` 内禀序 + `monoSub` 字段 (3a) + `strat : ∀ s → a <ᴹ b s` 字段 (3b 探针), 落地 full `<ᴹ-dec` + ψ_M.
>
> 撞墙路线源: [FINDINGS_Phase2.md](FINDINGS_Phase2.md). 升级动机: Phase 2 `<ᴹ-dec?` 4 mahlo 子 case 中 3 个 `nothing` (Sub 无内禀序 + b 无 mono).
>
> 语义代价: 3b strat 字段 (`a < b s` 对所有 s) 把"真 Mahlo"弱化为 stratified Σ-reflect, 强度 < Setzer Mahlo. 详 §6.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase3 where

open import OCF.BTBO using (module Trich)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Sum using (_⊎_) renaming (inj₁ to injᵃ; inj₂ to injᵇ)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
```

## 互递归 8 层骨架: Ordᴹ + Opᴹ + Sub + `<ᴹ` + `<ᴼ` + `<ˢ` + monoᴺ + monoSub

Phase 2 6 层基础上, 新增 `_<ˢ_` (Sub 内禀序, IR-recursive on `a`) 与 `monoSub`. mahlo 字段从 3 个 (f/a/b) 升至 5 个 (+ monoSub + strat). monoSub/strat 一起把"任意 `Sub a → Ordᴹ`"窄化为"按 Sub 内禀序单调且与 `a` 分层".

```agda
infix 10 _<ᴹ_ _<ᴼ_ _<ˢ_

data Ordᴹ : Set
data Opᴹ  : Set
Sub : Ordᴹ → Set
data _<ᴹ_ : Ordᴹ → Ordᴹ → Set
data _<ᴼ_ : Opᴹ → Opᴹ → Set
_<ˢ_ : ∀ {a : Ordᴹ} → Sub a → Sub a → Set

monoᴺ : (ℕ → Ordᴹ) → Set
monoᴺ f = ∀ {n m : ℕ} → n <ᴺ m → f n <ᴹ f m

monoSub : (a : Ordᴹ) → (Sub a → Ordᴹ) → Set
monoSub a b = ∀ {s s' : Sub a} → s <ˢ s' → b s <ᴹ b s'

data Ordᴹ where
  zero  : Ordᴹ
  suc   : Ordᴹ → Ordᴹ
  lim   : (f : ℕ → Ordᴹ) → monoᴺ f → Ordᴹ
  mahlo : Opᴹ → (a : Ordᴹ) → (b : Sub a → Ordᴹ)
        → monoSub a b → (∀ s → a <ᴹ b s) → Ordᴹ

data Opᴹ where
  op : (c : Ordᴹ) → (Sub c → Opᴹ) → Opᴹ

Sub zero                = ⊥
Sub (suc _)             = ⊤
Sub (lim _ _)           = ℕ
Sub (mahlo _ a b _ _)   = Σ (Sub a) (λ x → Sub (b x))

_<ˢ_ {a = zero}            ()  _
_<ˢ_ {a = suc _}           _   _   = ⊥
_<ˢ_ {a = lim _ _}         n   m   = n <ᴺ m
_<ˢ_ {a = mahlo _ a b _ _} (s , t) (s' , t') =
   (s <ˢ s') ⊎ Σ[ eq ∈ s ≡ s' ] (subst (Sub ∘ b) eq t <ˢ t')

data _<ᴹ_ where
  zero    : ∀ {a}                     → a <ᴹ suc a
  suc     : ∀ {a b}                   → a <ᴹ b → a <ᴹ suc b
  lim     : ∀ {a f} {mono : monoᴺ f} (n : ℕ)      → a <ᴹ f n → a <ᴹ lim f mono
  mahlo-a : ∀ {f a b} {m : monoSub a b} {σ : ∀ s → a <ᴹ b s} {x}
          → x <ᴹ a → x <ᴹ mahlo f a b m σ
  mahlo-b : ∀ {f a b} {m : monoSub a b} {σ : ∀ s → a <ᴹ b s} {x}
          → (s : Sub a) → x <ᴹ b s → x <ᴹ mahlo f a b m σ

data _<ᴼ_ where
  op-c : ∀ {c c' g g'} → c <ᴹ c' → op c g <ᴼ op c' g'
```

`σ` 是新的 strat 字段 (`∀ s → a <ᴹ b s`), `m` 是 monoSub 字段. `mahlo-a` / `mahlo-b` 构造子签名只多两个 implicit, 不影响递归结构.

## `<ᴹ-trans` (沿 Phase 2)

```agda
<ᴹ-trans : ∀ {a b c} → a <ᴹ b → b <ᴹ c → a <ᴹ c
<ᴹ-trans p zero          = suc p
<ᴹ-trans p (suc q)       = suc (<ᴹ-trans p q)
<ᴹ-trans p (lim n q)     = lim n (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-a q)   = mahlo-a (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-b s q) = mahlo-b s (<ᴹ-trans p q)
```

## `<ˢ-dec`: Sub 内禀序的无条件三歧

`Sub a` 在固定 a 下结构有限 (zero/suc/lim 分别给出 ⊥/⊤/ℕ; mahlo 给出 Σ 嵌套). 三歧无须 bound:

```agda
<ˢ-dec : ∀ {a} (s s' : Sub a) → s <ˢ s' ⊎ s' <ˢ s ⊎ s ≡ s'
<ˢ-dec {a = zero}            ()  _
<ˢ-dec {a = suc _}           tt  tt        = injᵇ (injᵇ refl)
<ˢ-dec {a = lim _ _}         n   m         with <ᴺ-dec n m
... | injᵃ n<m                         = injᵃ n<m
... | injᵇ (injᵃ m<n)                  = injᵇ (injᵃ m<n)
... | injᵇ (injᵇ refl)                 = injᵇ (injᵇ refl)
<ˢ-dec {a = mahlo _ a b _ _} (s , t) (s' , t') with <ˢ-dec s s'
... | injᵃ s<s'                        = injᵃ (injᵃ s<s')
... | injᵇ (injᵃ s'<s)                 = injᵇ (injᵃ (injᵃ s'<s))
... | injᵇ (injᵇ refl) with <ˢ-dec t t'
...   | injᵃ t<t'                      = injᵃ (injᵇ (refl , t<t'))
...   | injᵇ (injᵃ t'<t)               = injᵇ (injᵃ (injᵇ (refl , t'<t)))
...   | injᵇ (injᵇ refl)               = injᵇ (injᵇ refl)
```

注意 `injᵇ (refl , t<t')` 利用 `subst (Sub ∘ b) refl t ≡ t` (def. reduction).

## `<ᴹ-dec`: 完整有界三歧 (用 monoSub + strat)

仿 [BTBO.lagda.md:699-707](../../BTBO.lagda.md). 4 个 mahlo 子 case 全闭合:

```agda
<ᴹ-dec : ∀ {a b c} → a <ᴹ c → b <ᴹ c → a <ᴹ b ⊎ b <ᴹ a ⊎ a ≡ b
<ᴹ-dec zero zero        = injᵇ (injᵇ refl)
<ᴹ-dec zero (suc q)     = injᵇ (injᵃ q)
<ᴹ-dec (suc p) zero     = injᵃ p
<ᴹ-dec (suc p) (suc q)  = <ᴹ-dec p q
<ᴹ-dec (lim {mono = μ} n p) (lim k q) with <ᴺ-dec n k
... | injᵃ n<k         = <ᴹ-dec (<ᴹ-trans p (μ n<k)) q
... | injᵇ (injᵃ k<n)  = <ᴹ-dec p (<ᴹ-trans q (μ k<n))
... | injᵇ (injᵇ refl) = <ᴹ-dec p q
<ᴹ-dec (mahlo-a p)              (mahlo-a q)    = <ᴹ-dec p q
<ᴹ-dec (mahlo-a {σ = σ} p)      (mahlo-b s q)  = <ᴹ-dec (<ᴹ-trans p (σ s)) q
<ᴹ-dec (mahlo-b {σ = σ} s p)    (mahlo-a q)    = <ᴹ-dec p (<ᴹ-trans q (σ s))
<ᴹ-dec (mahlo-b {m = m} s p)    (mahlo-b s' q) with <ˢ-dec s s'
... | injᵃ s<s'        = <ᴹ-dec (<ᴹ-trans p (m s<s')) q
... | injᵇ (injᵃ s'<s) = <ᴹ-dec p (<ᴹ-trans q (m s'<s))
... | injᵇ (injᵇ refl) = <ᴹ-dec p q
```

四个 mahlo 子 case:
- `(mahlo-a, mahlo-a)`: 同 bound a. 递归.
- `(mahlo-a p, mahlo-b s q)`: p : a < a₀, strat (σ s) 给 a₀ <ᴹ b s, trans 给 a <ᴹ b s. 现 p', q 同 bound `b s`. 递归.
- `(mahlo-b s p, mahlo-a q)`: 对称.
- `(mahlo-b s p, mahlo-b s' q)`: `<ˢ-dec s s'` 三歧. mono (m) 给 b s ↔ b s' 的序, trans 把较低的 bound 抬到较高的 bound. 递归.

## Step 5: ψ_M collapser (3b 解锁后)

(占位 — 仿 [Higher.agda:31-38](../../Higher.agda#L31-L38). 完整 ψ_M 见后续 commit.)

## 与 BTBO 框架的关系

- [BTBO.lagda.md](../../BTBO.lagda.md) `BoundedTrich.<-dec` 模板: 沿用 lim/lim 套路, 现把 `<ᴺ-dec` 之上加 `<ˢ-dec`.
- [Higher.agda](../../Higher.agda) `ψ<Ω` 套路: 三歧 fold + suc/lim/limᵢ 分支.
- [../Naive/FINDINGS.md §5](../Naive/FINDINGS.md#5-根本性发现-lmono-不真): 加 monoSub + strat 等价于在"函数空间"上烤入序结构, 与 Naive 缺失 `+-lmono` 的根本性同源.

## Phase 3 进展表

| Step | 3a 状态 | 3b 状态 | 备注 |
|------|---------|---------|------|
| 1. Sub 反射 | ✓ (Phase 2) | ✓ | Σ-closure 不变 |
| 2. `<ᴹ` + `<ᴼ` | ✓ (Phase 2) | ✓ | 多 implicit `m`/`σ` pass-through |
| 3. `<ˢ` + monoSub | ✓ | ✓ | IR 函数版本 + lex 序 |
| 4. strat 字段 | n/a | ✓ | 弱化为 stratified Mahlo |
| 5. full `<ᴹ-dec` | partial (1/2 mahlo case) | ✓ | 4 子 case 全通 |
| 6. ψ_M | ✗ | TODO | 待后续 commit |

详细诊断 → [FINDINGS_Phase3.md](FINDINGS_Phase3.md).

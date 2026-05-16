# Phase 5 Path A spike: Sub 升级为 Ord-indexed

> Phase 4 mahlo 的 `Sub a = Σ ...` 是 Σ-平铺索引, 强度受限. 本 spike **升级 Sub mahlo case 为 `Ord (level a)`** (BTBO 的 Ord-tree, 带 limᵢ 嵌套), 同步改 mahlo 字段 `b : Ord (level a) → Ordᴹ`. 期望: 结构上让 mahlo 节点拥有 Higher.agda `limₙ`-级索引能力.
>
> **关键挑战**: level 必须进 mutual block (因 Sub mahlo case 引用 level a). monoSub / `<ˢ` 在 Ord-indexed Sub 上没有 unconditional trichotomy 的自然定义 — spike 阶段**简化处理** (mahlo case 上 `<ˢ` trivialize), 完整对齐留 Phase 6.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase5A_SubOrd where

open import OCF.BTBO
open import Data.Nat using (ℕ) renaming (zero to zeroᴺ; suc to sucᴺ)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; subst; cong)

open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec)
open BoundedTrich
  using (Ordᴰ; cumsum; cumsum-mono; f<l)
  renaming (_<_ to _<ᴰ_; <-dec to <ᴰ-dec; <-trans to <ᴰ-trans; monotonic to monoᴰ; zero to zeroᴰ; suc to sucᴰ; lim to limᴰ)
open Ord-Ord using (Ord; Ord₀; Ω; lfp; ordᴰ; ψ<; ψ₀; ↑; coe₀)
```

## §A.1 — Mutual block: 把 level 拉进去

`level` 不依赖 `<ᴹ` / `Sub`, 只依赖 Ordᴹ 构造子. 把它 forward-declare 在 mutual block 顶部, 让 Sub mahlo case 引用 `Ord (level a)`.

```agda
infix 10 _<ᴹ_ _<ᴼ_

data Ordᴹ : Set
data Opᴹ  : Set
Sub : Ordᴹ → Set
level : Ordᴹ → Ordᴰ
data _<ᴹ_ : Ordᴹ → Ordᴹ → Set
data _<ᴼ_ : Opᴹ → Opᴹ → Set

monoᴺ : (ℕ → Ordᴹ) → Set
monoᴺ f = ∀ {n m : ℕ} → n <ᴺ m → f n <ᴹ f m

data Ordᴹ where
  zero  : Ordᴹ
  suc   : Ordᴹ → Ordᴹ
  lim   : (f : ℕ → Ordᴹ) → monoᴺ f → Ordᴹ
  mahlo : Opᴹ → (a : Ordᴹ) → (b : Ord (level a) → Ordᴹ) → Ordᴹ
        -- ⚠ Path A 核心: b 从 Sub a 改为 Ord (level a)

data Opᴹ where
  op : (c : Ordᴹ) → (Sub c → Opᴹ) → Opᴹ

Sub zero            = ⊥
Sub (suc _)         = ⊤
Sub (lim _ _)       = ℕ
Sub (mahlo _ a b)   = Ord (level a)    -- ⚠ Path A 核心: 用 Ord-tree 替代 Σ-平铺

level zero            = zeroᴰ
level (suc a)         = level a
level (lim f _)       = limᴰ (cumsum (level ∘ f)) (cumsum-mono (level ∘ f))
level (mahlo _ a _)   = sucᴰ (level a)

data _<ᴹ_ where
  zero    : ∀ {a}                              → a <ᴹ suc a
  suc     : ∀ {a b}                            → a <ᴹ b → a <ᴹ suc b
  lim     : ∀ {a f} {mono : monoᴺ f} (n : ℕ)   → a <ᴹ f n → a <ᴹ lim f mono
  mahlo-a : ∀ {f a b x}                        → x <ᴹ a → x <ᴹ mahlo f a b
  mahlo-b : ∀ {f a b x}
          → (s : Ord (level a)) → x <ᴹ b s → x <ᴹ mahlo f a b
          -- ⚠ s 现在是 Ord (level a) 而非 Sub a

data _<ᴼ_ where
  op-c : ∀ {c c' g g'} → c <ᴹ c' → op c g <ᴼ op c' g'
```

注意: 本 spike **去掉了 Phase 4 的 monoSub 字段**. 因为 Ord (level a) 上的"内禀序"需要重新构造 (BTBO 在 Ord ℓ 上只有 bounded trichotomy, 不像 Sub a 上有的 unconditional `<ˢ-dec`). spike 阶段简化, 完整 monoSub-on-Ord 留 Phase 6.

## §A.2 — `<ᴹ-trans`

仿 Phase 4. mahlo case 多一个 `mahlo-b` 的 s 类型变化, 其它不变:

```agda
<ᴹ-trans : ∀ {a b c} → a <ᴹ b → b <ᴹ c → a <ᴹ c
<ᴹ-trans p zero          = suc p
<ᴹ-trans p (suc q)       = suc (<ᴹ-trans p q)
<ᴹ-trans p (lim n q)     = lim n (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-a q)   = mahlo-a (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-b s q) = mahlo-b s (<ᴹ-trans p q)
```

## §A.3 — Sample 构造: empty Ord-tree-indexed mahlo

验证新签名可构造. 用 `zero : Ord zeroᴰ` 作为 Ord-tree-trivial 例子:

```agda
-- a = zero, level zero = zeroᴰ, Ord zeroᴰ = Ord₀ 包含 Brouwer 树
-- b 必须是 Ord₀ → Ordᴹ. 简单选 b s = zero.
op-trivial : Opᴹ
op-trivial = op zero λ ()

M-test : Ordᴹ
M-test = mahlo op-trivial zero (λ _ → zero)

_ : Sub M-test ≡ Ord₀     -- 验证 Sub mahlo case 展开为 Ord (level zero) = Ord zeroᴰ = Ord₀
_ = refl
```

## §A.4 — Spike 结论 (Path A)

| 项 | 状态 | 备注 |
|----|------|------|
| `level` 进 mutual block | ✓ | 与 Sub 一起 forward-declare |
| mahlo b : Ord (level a) → Ordᴹ | ✓ | strict positivity 通过 |
| Sub (mahlo _ a b) = Ord (level a) | ✓ | IR 接受, Ord-Ord 在 mutual 外预定义 |
| `<ᴹ` mahlo-b 改 Ord-indexed | ✓ | 字段类型变, 构造子结构不变 |
| `<ᴹ-trans` | ✓ | 5 case 平凡递归, 与 Phase 4 同 |
| monoSub / `<ˢ` | **去除** | Ord ℓ 上无 unconditional trichotomy, 留 Phase 6 |
| `<ᴹ-dec?` | **未实现** | 无 monoSub → mahlo-b 子 case 也卡, spike 不投入 |
| Sample 构造 | ✓ | `M-test = mahlo op-trivial zero (const zero)`, Sub = Ord₀ |
| ψ_M | 未实现 | 留 Phase 6, 利用新 Sub 的 Ord-indexed 结构 |

**关键观察**: Sub 升级到 Ord-indexed **结构可行** — level 进 mutual block 没有 positivity / IR 问题. 但下游 (`<ˢ`, monoSub, `<ᴹ-dec?`, ψ_M) 需要重大重写, 因为 Ord ℓ 没有 unconditional trichotomy. 这是 **Phase 4 Sub-Σ → Path A Sub-Ord 的真实代价**: 索引升级换强度, 但失去 Sub 内禀的"任两个元素可三歧比较"性质.

**强度评估**: Path A 给 mahlo 节点提供了 Higher.agda `limₙ`-级索引能力的**结构性接入点**. 但实际强度依赖 ψ_M 设计 (Phase 6), spike 只证明结构可达. 与 Path B 直接拿到 ψ(Ω_(Ω+2)) binding 相比, A 是**长期投入** + **不确定收益**.

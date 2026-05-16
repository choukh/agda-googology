# Mahlo Phase 4: 去 strat + level-indexed ψ_M (超过 Higher.agda)

> Phase 3 ([Phase3.lagda.md](Phase3.lagda.md)) 强度 ≲ Higher.agda (诊断: [FINDINGS_Phase3.md §4.3](FINDINGS_Phase3.md)). Phase 4 转向: **去 strat**, ψ_M 改用 Higher.agda 风格的 level-indexed dispatch (`Ord (level a)` 输出, Ordᴰ trichotomy), **不依赖 mahlo 节点上的 `<ᴹ-dec`** (允许 partial).
>
> 目标: ω-nested mahlo + `ψ₀ ∘ ψ_M` 经 outer `lim n` 达 ψ(Ω_(Ω+ω)) 量级, 首次真正超过 Higher.agda 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))).
>
> 详细诊断 → [FINDINGS_Phase4.md](FINDINGS_Phase4.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase4 where

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
open Ord-Ord using (Ord; Ord₀; Ω; lfp; ordᴰ; ψ<; ψ₀; ψⁿ; ↑; coe₀; iter)
```

## §4a — 8 层互递归骨架 (去 strat 版)

与 Phase 3 同 8 层, 唯一区别: mahlo 构造子去掉 `strat : ∀ s → a <ᴹ b s` 字段 (5 → 4 字段).

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
        → monoSub a b → Ordᴹ      -- ⚠ 去掉了 Phase 3 的 strat 字段

data Opᴹ where
  op : (c : Ordᴹ) → (Sub c → Opᴹ) → Opᴹ

Sub zero              = ⊥
Sub (suc _)           = ⊤
Sub (lim _ _)         = ℕ
Sub (mahlo _ a b _)   = Σ (Sub a) (λ x → Sub (b x))

_<ˢ_ {a = zero}          ()  _
_<ˢ_ {a = suc _}         _   _   = ⊥
_<ˢ_ {a = lim _ _}       n   m   = n <ᴺ m
_<ˢ_ {a = mahlo _ a b _} (s , t) (s' , t') =
   (s <ˢ s') ⊎ (Σ[ eq ∈ s ≡ s' ] (subst (Sub ∘ b) eq t <ˢ t'))

data _<ᴹ_ where
  zero    : ∀ {a}                              → a <ᴹ suc a
  suc     : ∀ {a b}                            → a <ᴹ b → a <ᴹ suc b
  lim     : ∀ {a f} {mono : monoᴺ f} (n : ℕ)   → a <ᴹ f n → a <ᴹ lim f mono
  mahlo-a : ∀ {f a b} {m : monoSub a b} {x}
          → x <ᴹ a → x <ᴹ mahlo f a b m
  mahlo-b : ∀ {f a b} {m : monoSub a b} {x}
          → (s : Sub a) → x <ᴹ b s → x <ᴹ mahlo f a b m

data _<ᴼ_ where
  op-c : ∀ {c c' g g'} → c <ᴹ c' → op c g <ᴼ op c' g'
```

`<ᴹ-trans` 沿 Phase 2/3 5 case 平凡递归, 不读 strat:

```agda
<ᴹ-trans : ∀ {a b c} → a <ᴹ b → b <ᴹ c → a <ᴹ c
<ᴹ-trans p zero          = suc p
<ᴹ-trans p (suc q)       = suc (<ᴹ-trans p q)
<ᴹ-trans p (lim n q)     = lim n (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-a q)   = mahlo-a (<ᴹ-trans p q)
<ᴹ-trans p (mahlo-b s q) = mahlo-b s (<ᴹ-trans p q)
```

`<ˢ-dec` 沿 Phase 3 (不依赖 strat):

```agda
<ˢ-dec : ∀ {a} (s s' : Sub a) → s <ˢ s' ⊎ s' <ˢ s ⊎ s ≡ s'
<ˢ-dec {a = zero}          ()  _
<ˢ-dec {a = suc _}         tt  tt        = injᶜ refl
<ˢ-dec {a = lim _ _}       n   m         with <ᴺ-dec n m
... | injᵃ n<m                       = injᵃ n<m
... | injᵇ m<n                       = injᵇ m<n
... | injᶜ refl                      = injᶜ refl
<ˢ-dec {a = mahlo _ a b _} (s , t) (s' , t') with <ˢ-dec s s'
... | injᵃ s<s'                      = injᵃ (inj₁ s<s')
... | injᵇ s'<s                      = injᵇ (inj₁ s'<s)
... | injᶜ refl with <ˢ-dec t t'
...   | injᵃ t<t'                    = injᵃ (inj₂ (refl , t<t'))
...   | injᵇ t'<t                    = injᵇ (inj₂ (refl , t'<t))
...   | injᶜ refl                    = injᶜ refl
```

### `<ᴹ-dec?` partial (去 strat 代价)

`(mahlo-a, mahlo-b)` 与 `(mahlo-b, mahlo-a)` cross-case 退回 `nothing` (无 strat 桥接 a₀ ↔ b s).

```agda
Tri : Ordᴹ → Ordᴹ → Set
Tri a b = a <ᴹ b ⊎ b <ᴹ a ⊎ a ≡ b

<ᴹ-dec? : ∀ {a b c} → a <ᴹ c → b <ᴹ c → Maybe (Tri a b)
<ᴹ-dec? zero zero       = just (injᶜ refl)
<ᴹ-dec? zero (suc q)    = just (injᵇ q)
<ᴹ-dec? (suc p) zero    = just (injᵃ p)
<ᴹ-dec? (suc p) (suc q) = <ᴹ-dec? p q
<ᴹ-dec? (lim {mono = μ} n p) (lim k q) with <ᴺ-dec n k
... | injᵃ n<k         = <ᴹ-dec? (<ᴹ-trans p (μ n<k)) q
... | injᵇ k<n         = <ᴹ-dec? p (<ᴹ-trans q (μ k<n))
... | injᶜ refl        = <ᴹ-dec? p q
<ᴹ-dec? (mahlo-a p)           (mahlo-a q)    = <ᴹ-dec? p q
<ᴹ-dec? (mahlo-a _)           (mahlo-b _ _)  = nothing  -- ⚠ 去 strat, 无 cross-bridge
<ᴹ-dec? (mahlo-b _ _)         (mahlo-a _)    = nothing
<ᴹ-dec? (mahlo-b {m = m} s p) (mahlo-b s' q) with <ˢ-dec s s'
... | injᵃ s<s'        = <ᴹ-dec? (<ᴹ-trans p (m s<s')) q
... | injᵇ s'<s        = <ᴹ-dec? p (<ᴹ-trans q (m s'<s))
... | injᶜ refl        = <ᴹ-dec? p q
```

Phase 4 不依赖 `<ᴹ-dec?` 全函数化, ψ_M 改用 level-indexed dispatch (§4c).

## §4b — `level : Ordᴹ → Ordᴰ` rank 函数

每嵌一层 mahlo +1 rank (在 Ordᴰ 上). `lim` case 用 cumsum 单调化 (照搬 `ordᴰ` 模板).

```agda
level : Ordᴹ → Ordᴰ
level zero            = zeroᴰ
level (suc a)         = level a
level (lim f _)       = limᴰ (cumsum (level ∘ f)) (cumsum-mono (level ∘ f))
level (mahlo _ a _ _) = sucᴰ (level a)
```

注: mahlo case 暂忽略 b 贡献 (§4c-v1 简单版基线); §4c-v2 / Phase 5 可改用 `sucᴰ (level a ⊔ sup (level ∘ b ∘ enum))`. suc case 不增 rank, 与 `ordᴰ (suc a) = sucᴰ (ordᴰ a)` 不同 — 这里 rank 反映"mahlo 嵌套深度", 不是 Ordᴹ 整体 ordinal 值.

## §4c-v1 — `ψ_M` 简单版: 直接输出到 Ord₀ (BTBO ψⁿ pattern)

为避免 level-indexed `Ord (level a)` 的 cumsum-step proof obligation, v1 大幅简化: ψ_M 直接输出到 Ord₀. mahlo 节点用 BTBO ψⁿ trick (`ψ₀ ∘ Ω ∘ ordᴰ`) 引入 Ω-跳跃. b/level 字段在 v1 暂不使用, 留待 v2+.

```agda
ψ_M : Ordᴹ → Ord₀
ψ_M zero            = Ω zeroᴰ                                    -- ω
ψ_M (suc a)         = lfp ((ψ_M a) Ord-Ord.+_)
ψ_M (lim f _)       = Ord-Ord.lim (ψ_M ∘ f)
ψ_M (mahlo _ a _ _) = ψ₀ {ℓ = ordᴰ (ψ_M a)} (Ω (ordᴰ (ψ_M a)))   -- ψ(Ω_(ψ_M a)), ψⁿ pattern
```

### v2 尝试: 用 level 给 mahlo 提供 Ordᴰ-rank 增量

替代设计: 把 mahlo 节点的 Ω-索引提到 `ordᴰ (ψ_M a) + level (mahlo …)` (Ordᴰ 上的加法). level 在 Ordᴰ 上提供 +rank 贡献.

```agda
ψ_M-v2 : Ordᴹ → Ord₀
ψ_M-v2 zero            = Ω zeroᴰ
ψ_M-v2 (suc a)         = lfp ((ψ_M-v2 a) Ord-Ord.+_)
ψ_M-v2 (lim f _)       = Ord-Ord.lim (ψ_M-v2 ∘ f)
ψ_M-v2 m@(mahlo _ a _ _) = ψ₀ {ℓ = ordᴰ (ψ_M-v2 a) BoundedTrich.+ level m}
                                (Ω (ordᴰ (ψ_M-v2 a) BoundedTrich.+ level m))
```

**v2 强度评估**:
- M^0 = zero: ψ_M-v2 = ω
- M^1 = mahlo .. zero ..: level M^1 = sucᴰ zeroᴰ, ψ_M-v2 = ψ(Ω_(ordᴰ ω + 1)) ≈ ψ(Ω_(ω+1))
- M^n: ψ(Ω_(ordᴰ (ψⁿ⁻¹(0)) + n))
- lim n → ψ(Ω_(ψⁿ(0) + n))

外层 lim 极限: ≈ ψ(Ω_BTBO + ω). 比 v1 略增, 但**仍未超过 Higher.agda** 的 ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) — 因为 ψ_M-v2 没有 Ord-indexed limit, 只有 ℕ-indexed.

### v3 障碍: Sub-enum 不够

**关键洞察**: 让 mahlo 真正超过 Higher.agda 需要 Ord ℓ-indexed limit (Higher.agda 的 `limₙ` 已是 +1 级), 而 Phase 4 mahlo 的 `b : Sub a → Ordᴹ` 索引型 Sub a 是 Σ-平铺, 结构上比 Ord ℓ 简单.

Sub-enum (`enum-Sub : (a : Ordᴹ) → ℕ → Maybe (Sub a)`) 把 b 折成 ℕ-序列, 仍是 ℕ-cofinal, 与 BTBO 同强度. 即使 Cantor pairing 处理 Σ-嵌套, 输出仍可数.

**真正超过 Higher.agda 的路径** (Phase 5 范围, 不在本 Phase 4 实现):
1. **Sub 升级**: 把 `Sub (mahlo _ a b _) = Σ (Sub a) (Sub ∘ b)` 改成更丰富的索引, 例如 `Sub (mahlo _ a b _) = Ord< (level a) _`. 这把 Sub 与 BTBO 的 Ord-Ord 方案耦合, 突破 Σ-平铺限制. 但 mahlo 字段 b 的类型同步要改, 整个互递归结构重写.
2. **Higher^2 (Option α from 之前讨论)**: 不走 Mahlo, 直接在 OrdΩ 之上再加一层 `limₙ'`. 已知可达 ψ(Ω_(Ω+2)), 更高的迭代到 ψ(Ω_(Ω+ω)).
3. **Setzer 真 Mahlo (Design C)**: Opᴹ 语义化 + reflection witness. 理论可达 ψ(M).

**说明**:
- `ψ_M zero = Ω zeroᴰ = ω` ([BTBO.lagda.md:940](../../BTBO.lagda.md#L940) 等式).
- `ψ_M (suc a)`: 标准 Buchholz suc-collapse.
- `ψ_M (lim f _)`: 简单递归, 弃用 mono.
- `ψ_M (mahlo _ a _ _) = ψ(Ω_(ψ_M a))`: 把 mahlo 当作 "ψⁿ 步进", 与 BTBO 的 `ψⁿ = iter (ψ₀ ∘ Ω ∘ ordᴰ) zero` 同模板.

**v1 强度评估** (诚实):
- M^0 = zero: ψ_M M^0 = ω
- M^1 = mahlo .. zero .. ..: ψ_M M^1 = ψ(Ω_ω) = BO
- M^n iterated: ψ_M M^n ≈ ψⁿ(0)
- lim n → ψ_M M^n ≈ BTBO = ψ(Ω_Ω)

**=** BTBO 强度, **不超过** Higher.agda. v1 仅作 sanity check (Phase 4 端到端可跑), 真正超过需 v2 (Sub-enum + b 折入).

## §4d — 强度 demo (基线 BTBO)

仿 [Higher.agda:40-42](../../Higher.agda#L40-L42), 顶级 binding 验证 ψ_M 可计算:

```agda
-- ω-nested mahlo, b 用 const + Sub a → Ordᴹ
-- 注意: monoSub 需要实例化. 因为 ψ_M v1 不读 b, 我们可以塞任何 monoSub 见证 (用 absurd 或 const).
```

(具体 M^n 构造与 monoSub 实例化待 4d-impl. v1 阶段可以 binding `ψ_M zero` / `ψ_M (suc zero)` 等简单值验证.)

```agda
_ : Ord₀
_ = ψ_M zero

_ : Ord₀
_ = ψ_M (suc (suc zero))
```


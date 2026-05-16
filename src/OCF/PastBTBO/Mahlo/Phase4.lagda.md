# Mahlo Phase 4: 去 strat + level-indexed ψ_M (诚实负面结果)

> Phase 3 ([Phase3.lagda.md](Phase3.lagda.md)) 用 strat 字段换 full trichotomy, 强度 ≲ Higher.agda. Phase 4 转向: **去 strat**, ψ_M 改用 level-indexed dispatch, 看能否不依赖 mahlo 上 `<ᴹ-dec` 全函数化, 通过 ω-nested mahlo 真正达到 ψ(Ω_(Ω+ω)).
>
> **实测概要 (诚实结论)**: Phase 4 ψ_M v1/v2 都编译通过, **但实际强度未超过 Higher.agda**. 原因结构性 — Sub a 是 Σ-平铺, 索引能力 = ℕ, 不足以驱动 Ord-tree-indexed limit. **Phase 3 + Phase 4 两轮探索都未能超过 Higher.agda; Mahlo 路径在 Sub-Σ 设计下已饱和**, 需 Phase 5 走根本性不同方向.

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

**4a 实测**: `<ᴹ-dec?` 退回 Phase 2 同型 partial — cross-case 仍 `nothing`. Phase 4 不依赖 `<ᴹ-dec?` 全函数化, ψ_M 改用 level-indexed dispatch (§4c).

## §4b — `level : Ordᴹ → Ordᴰ` rank 函数

每嵌一层 mahlo +1 rank (在 Ordᴰ 上). `lim` case 用 cumsum 单调化 (照搬 `ordᴰ` 模板).

```agda
level : Ordᴹ → Ordᴰ
level zero            = zeroᴰ
level (suc a)         = level a
level (lim f _)       = limᴰ (cumsum (level ∘ f)) (cumsum-mono (level ∘ f))
level (mahlo _ a _ _) = sucᴰ (level a)
```

**4b 实测**: 结构归纳通过, 无终止问题. mahlo case +1 rank, 与 ordᴰ 的 `ordᴰ (suc a) = sucᴰ (ordᴰ a)` 模式同构 (但 suc 不增 rank — rank 只跟踪 mahlo 嵌套).

注: mahlo case 暂忽略 b 贡献 (§4c-v1 简单版基线); §4c-v2 / Phase 5 可改用 `sucᴰ (level a ⊔ sup (level ∘ b ∘ enum))`. suc case 不增 rank, 与 `ordᴰ (suc a) = sucᴰ (ordᴰ a)` 不同 — 这里 rank 反映"mahlo 嵌套深度", 不是 Ordᴹ 整体 ordinal 值.

## §4c-v1 — `ψ_M` 基线版: 直接输出到 Ord₀ (BTBO ψⁿ pattern)

为避免 level-indexed `Ord (level a)` 的 cumsum-step proof obligation, v1 大幅简化: ψ_M 直接输出到 Ord₀. mahlo 节点用 BTBO ψⁿ trick (`ψ₀ ∘ Ω ∘ ordᴰ`) 引入 Ω-跳跃. b/level 字段在 v1 暂不使用, 留待 v2+.

```agda
ψ_M : Ordᴹ → Ord₀
ψ_M zero            = Ω zeroᴰ                                    -- ω
ψ_M (suc a)         = lfp ((ψ_M a) Ord-Ord.+_)
ψ_M (lim f _)       = Ord-Ord.lim (ψ_M ∘ f)
ψ_M (mahlo _ a _ _) = ψ₀ {ℓ = ordᴰ (ψ_M a)} (Ω (ordᴰ (ψ_M a)))   -- ψ(Ω_(ψ_M a)), ψⁿ pattern
```

说明:

- `ψ_M zero = Ω zeroᴰ = ω` ([BTBO.lagda.md L940](../../BTBO.lagda.md#L940) 等式).
- `ψ_M (suc a)`: 标准 Buchholz suc-collapse.
- `ψ_M (lim f _)`: 简单递归, 弃用 mono.
- `ψ_M (mahlo _ a _ _) = ψ(Ω_(ψ_M a))`: 把 mahlo 当作 "ψⁿ 步进", 与 BTBO 的 `ψⁿ = iter (ψ₀ ∘ Ω ∘ ordᴰ) zero` 同模板.

**v1 强度评估 (诚实)**:

- M^0 = zero: ψ_M M^0 = ω
- M^1 = mahlo .. zero .. ..: ψ_M M^1 = ψ(Ω_ω) = BO
- M^n iterated: ψ_M M^n ≈ ψⁿ(0)
- lim n → ψ_M M^n ≈ BTBO = ψ(Ω_Ω)

**= BTBO 强度, 不超过 Higher.agda**. v1 仅作 sanity check (Phase 4 端到端可跑), 真正超过需 v2.

## §4c-v2 — level-bumped Ω-index

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

## §4c-v3 障碍: Sub-enum 也不够

设计假设的 v3:

    ψ_M-v3 (mahlo _ a b _) = ... + lim (n ↦ ψ_M-v3 (b (enum-Sub a n)))

`enum-Sub : (a : Ordᴹ) → ℕ → Maybe (Sub a)` 把 b 折成 ℕ-序列. 即使 Cantor pairing 处理 mahlo 的 Σ-嵌套, 输出仍是 ℕ-cofinal lim. 与 Higher.agda 的 `limₙ ... (Ord ℓ → OrdΩ)` 相比, 缺 Ord-tree 索引层.

**结论**: 在当前 `Sub (mahlo _ a b _) = Σ (Sub a) (Sub ∘ b)` 设计下, Phase 4 任何 ψ_M 变体都不会超过 Higher.agda. **Mahlo 路径的 Sub-Σ 限制是结构性瓶颈**.

## §4d — 强度 demo (基线 BTBO)

仿 [Higher.agda L40-42](../../Higher.agda#L40-L42), 顶级 binding 验证 ψ_M 可计算:

```agda
_ : Ord₀
_ = ψ_M zero

_ : Ord₀
_ = ψ_M (suc (suc zero))
```

(具体 M^n 构造与 monoSub 实例化待 4d-impl. v1 阶段可以 binding `ψ_M zero` / `ψ_M (suc zero)` 等简单值验证.)

## 强度对比 (核心 deliverable)

| 来源 | 估算 |
|------|------|
| BTBO `BTBO = lim ψⁿ` | ψ(Ω_Ω) |
| **Phase 4 v1** | **≈ ψ(Ω_Ω)** — 与 BTBO 持平 |
| **Phase 4 v2** | **≈ ψ(Ω_(Ω+ω))** — 比 BTBO 多 ω-级, **但**: |
| Higher.agda OrdΩ + limₙ | ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) — 估算 by ggg 社区 |
| Phase 4 v2 vs Higher.agda | **v2 ≲ Higher.agda** (v2 的 Ω-塔仅 ℕ-高, Higher.agda 的 limₙ 是 Ord-tree-高) |

**关键定性差**: Higher.agda 的 limₙ 索引在 `Ord ψᴰ(n)` (一棵带 limᵢ 嵌套的 Brouwer 树), Phase 4 v1/v2 的 ψ_M 索引在 `ℕ` (mahlo 嵌套深度). 二者在 cardinality 上都可数, 但 Ord-tree 的内部 limᵢ 嵌套给 Higher.agda 多出 1 个 "Ω-索引深度", Phase 4 没有.

## 与 Phase 3 路线的对比

| 维度 | Phase 3 (strat) | Phase 4 v1 | Phase 4 v2 |
|------|-----------------|------------|------------|
| mahlo 字段数 | 5 | 4 | 4 |
| `<ᴹ-dec` | full 4/4 | partial 2/4 | partial 2/4 |
| ψ_M 实现 | 占位待写 | ✓ Ord₀-直输 | ✓ level-bumped |
| 估算强度 | ≲ Higher.agda | ≈ BTBO | ≈ ψ(Ω_(Ω+ω)) |
| 是否超过 Higher.agda? | ✗ | ✗ | ✗ |

**两轮探索都未能超过 Higher.agda**. Phase 3 用 strat 换 full trichotomy, Phase 4 去 strat + level-indexed ψ_M. 都受 Sub 是 Σ-flat 的限制. **Mahlo 路径在当前 Sub-Σ 设计下的强度上限 ≈ Higher.agda, 不会更高**.

## Phase 5 候选路径 (突破 Sub-Σ 瓶颈)

要真正超过 Higher.agda, 必须在某个维度做结构性升级. 三条候选:

### 路径 A: Sub 升级为 Ord-indexed

把 `Sub (mahlo _ a b _) = Σ (Sub a) (Sub ∘ b)` 改成 `Sub (mahlo _ a b _) = Ord< (level a) _` 或类似 Ord-tree 形. 同步改 b: `b : Ord (level a) → Ordᴹ`. 这让 mahlo 节点拥有 Higher.agda `limₙ`-同级的索引能力. **挑战**: 互递归层数飙升 (Ordᴹ + Ord ℓ + Sub + ...), positivity 风险.

### 路径 B: 不走 Mahlo, 直接 Higher^n 迭代

放弃 Mahlo 编码, 在 OrdΩ 之上再加 `limₙ'` 层, 形成 Higher² ... Higherω. 每迭代 +1 Ω-级, ω-迭代到 ψ(Ω_(Ω+ω)). **优势**: 简单 (Higher.agda 50 行模板可复用), 预测性强. **劣势**: 不是 Mahlo, 是平铺 Buchholz 扩展.

### 路径 C: 真 Setzer Mahlo (Opᴹ 语义化)

给 `Opᴹ = op (c : Ordᴹ) (Sub c → Opᴹ)` 一个语义解释 `⟦_⟧ : Opᴹ → Ordᴹ → Ordᴹ`, mahlo 字段 f 真正代表"反射算子". ψ_M 通过 f 的 closure 性质构造 fixed-point. **优势**: 理论可达 ψ(M_真). **劣势**: 研究级, 互递归 + 语义闭合证明数千行.

**建议下一步**: 走路径 B (Higher^n 迭代) 作为 Phase 5 主线 — 工程上最可行, 强度增量明确. 路径 A/C 作为长期目标.

## Phase 1-4 累积代价 (诚实记账)

| 阶段 | 代码量 | 强度增量 vs 上一步 |
|------|--------|------------------|
| BTBO 基线 | (主线) | ψ(Ω_Ω) |
| Higher.agda | ~50 行 | +1 Ω-级 → ψ((Ω_Ω)+(Ω_(ψ(Ω_Ω)+1))) |
| Phase 1 (Brouwer-MLQ 骨架) | ~40 行 | 0 (仅结构) |
| Phase 2 (`<ᴹ`, partial `<ᴹ-dec`) | ~140 行 | 0 |
| Phase 3 (Sub`<ˢ` + monoSub + strat) | ~160 行 | ≲ Higher.agda |
| **Phase 4 (去 strat + ψ_M v2)** | **~210 行** | **≲ Higher.agda** |

**Mahlo 路径累积 ~550 行代码, 强度上限 ≲ Higher.agda 的 50 行**. 这是 Phase 1-4 的诚实记账. Mahlo 形式化是**结构性贡献** (探索 IR-Mahlo, Sub Σ-closure, 内禀序 `<ˢ`, monoSub, level rank), **不是强度贡献**.

## 给作者的建议

1. **Mahlo 路径的强度上限是 Higher.agda 级别, 不更高**. 这是 Phase 1-4 的实证结论.
2. **若目标是超过 Higher.agda, 推荐走 Higher^n 迭代 (路径 B)** — 工程上最直接, 强度可量化.
3. **Mahlo 形式化的价值在结构** (IR-Mahlo, Sub 内禀序, monoSub), 不在 ordinal 强度. 可以作为类型论研究素材保留.
4. **真 Setzer Mahlo (路径 C)** 是开放问题, 至少需要 Phase 5+6 两轮研究投入, 不建议短期内尝试.

全部 5 个 `.lagda.md` 文件 (Phase1-4 + 后续 Phase5*) 通过 Agda 2.8.0 + stdlib 2.3 + cubical 0.9 + `--safe --without-K --cubical-compatible --lossy-unification --hidden-argument-puns` 编译. 无 postulate, 无 unsafe.

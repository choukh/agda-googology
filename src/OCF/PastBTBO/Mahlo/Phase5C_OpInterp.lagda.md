# Phase 5 Path C spike: Opᴹ 语义化 (v0 toy)

> Phase 4 mahlo 的 `f : Opᴹ` 字段当前是结构装饰, 不参与 ψ_M. 本 spike 给 Opᴹ 一个**语义解释** `⟦_⟧ : Opᴹ → Ordᴹ → Ordᴹ`, 让 mahlo 真正变成"反射算子驱动"的折叠节点 — 是 Setzer 1998 真 IR-Mahlo 的简化版.
>
> **v0 (toy)**: `⟦ op c g ⟧ a = a` (常值 identity). 只验证类型机制 + post-mutual 函数兼容 mutual block. 强度不增, 但证明 ⟦_⟧ 可定义.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.Mahlo.Phase5C_OpInterp where

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

## §C.1 — 8 层互递归骨架 (与 Phase 4 同)

直接复用 Phase 4 的骨架 (去 strat 版). Opᴹ + mahlo 字段不变.

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
  mahlo : Opᴹ → (a : Ordᴹ) → (b : Sub a → Ordᴹ) → monoSub a b → Ordᴹ

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

## §C.2 — `⟦_⟧ : Opᴹ → Ordᴹ → Ordᴹ` (post-mutual)

**关键创新**: Opᴹ 不再是结构装饰, 而是真正的"语义算子". v0 toy 版本: 常值返回 a, 验证类型机制.

```agda
⟦_⟧ : Opᴹ → Ordᴹ → Ordᴹ
⟦ op c g ⟧ a = a       -- v0 toy: constant identity. 验证 ⟦_⟧ 可定义.
                       -- 终止性: 显然 (无递归).
```

**v1 候选** (未启用): `⟦ op c g ⟧ a = suc a + c-encoded` — 用 c 作 ordinal 移位. 终止显然, 强度略增.

**v2 候选** (未启用): `⟦ op c g ⟧ a = mahlo (op c g) a const-a monoSub-trivial` — 递归注入 mahlo. 终止需 careful 分析.

v0 spike 仅证 ⟦_⟧ 可在 mutual block 之外作为后置函数定义.

## §C.3 — `ψ_M-C` 用 ⟦_⟧ 驱动 (撞墙记录)

**初始尝试** (失败):

```text
ψ_M-C : Ordᴹ → Ord₀
ψ_M-C zero            = Ω zeroᴰ
ψ_M-C (suc a)         = lfp ((ψ_M-C a) +_)
ψ_M-C (lim f _)       = lim (ψ_M-C ∘ f)
ψ_M-C (mahlo f a _ _) = ψ_M-C (⟦ f ⟧ a)        -- ❌ Termination check fails
```

**Agda 终止检查拒绝**: 即使 v0 `⟦ op c g ⟧ a = a` 是 identity, Agda 不透传 ⟦_⟧ 的展开. 终止检查器只看到"`ψ_M-C` 递归调用在 `(⟦ f ⟧ a)`", 而 `(⟦ f ⟧ a)` 不是 `mahlo f a _ _` 的句法子项. 拒绝.

**这是 Path C 的核心障碍**: 想"通过 Opᴹ 语义驱动 ψ_M"的设计模式, 与 Agda 句法终止检查不兼容. 即使最简 toy ⟦_⟧ 也失败.

### 备用: 内联 ⟦_⟧ 的 v0 行为, 不通过 ⟦_⟧ 调用

把 mahlo case 写成直接 pattern-match Opᴹ 的 `op c g`, 然后写出与 v0 ⟦_⟧ 等价的右手边:

```agda
ψ_M-C : Ordᴹ → Ord₀
ψ_M-C zero                       = Ω zeroᴰ
ψ_M-C (suc a)                    = lfp ((ψ_M-C a) Ord-Ord.+_)
ψ_M-C (lim f _)                  = Ord-Ord.lim (ψ_M-C ∘ f)
ψ_M-C (mahlo (op c g) a _ _)     = ψ_M-C a
   -- 等价于 v0 ⟦ op c g ⟧ a = a, 但直接 pattern-match, 终止检查能看到 a 是 mahlo 字段
```

**绕过技巧**: 不调用 ⟦_⟧, 而是把它的逻辑"反演"成 ψ_M-C 自己的 case-split. 这让 ψ_M-C 编译通过, **但 ⟦_⟧ 在 ψ_M-C 中没有真正使用** — ⟦_⟧ 作为独立函数仍然存在, 只是被绕开了.

### v1/v2 / 真正用 ⟦_⟧ 的设计 (远未达到)

要让 ψ_M-C 真正通过 ⟦_⟧ 驱动 + 非平凡 ⟦_⟧, 需要其中之一:
1. **Well-founded recursion**: 显式提供 well-founded measure 给 Agda. 复杂.
2. **Sized types**: 用 `--sized-types` 标记 ⟦_⟧ 输出. 项目当前用 `--safe --without-K`, 与 sized types 兼容性需评估.
3. **Inline ⟦_⟧ 的全部 case**: 把 Opᴹ 的所有 op 形式枚举展开. 限制 ⟦_⟧ 必须有静态可分析的结构.
4. **重构 mahlo 字段**: 把 f 从 Opᴹ 改为更受约束的类型 (e.g., 直接的"减小映射" `(a' : Ordᴹ) → a' <ᴹ a → Ordᴹ`). 改回到 Phase 4 mahlo 不带语义的设计.

这些都是 Phase 6+ 研究级方向. spike 仅证 ⟦_⟧ 自身定义可行, 与 ψ_M 集成是另一个未解问题.

## §C.4 — 示例 binding

```agda
op-trivial : Opᴹ
op-trivial = op zero λ ()

monoSub-trivial : monoSub zero (λ ())
monoSub-trivial {()} _

M-test : Ordᴹ
M-test = mahlo op-trivial zero (λ ()) monoSub-trivial

_ : Ord₀
_ = ψ_M-C M-test     -- 用 inline 版 ψ_M-C: mahlo case = ψ_M-C a = ψ_M-C zero = ω

-- ⟦_⟧ 自身可调用 (但 ψ_M-C 没用到):
_ : Ordᴹ
_ = ⟦ op-trivial ⟧ zero       -- = zero (v0 identity)
```

## §C.5 — Spike 结论 (Path C, 含撞墙发现)

| 项 | 状态 | 备注 |
|----|------|------|
| 8 层 mutual block | ✓ | 与 Phase 4 同 |
| `⟦_⟧ : Opᴹ → Ordᴹ → Ordᴹ` 后置函数 | ✓ (v0) | 常值 identity, 编译通过 |
| `ψ_M-C` 直接调用 ⟦_⟧ | ✗ | **Agda 终止检查拒绝** — 不透传 ⟦_⟧ 展开 |
| `ψ_M-C` 内联 ⟦_⟧ v0 逻辑 | ✓ | pattern-match Opᴹ 构造子, 绕过终止问题 |
| v0 终止性 (内联) | ✓ | a 是 mahlo 字段, 结构性递减 |
| 强度评估 | ⚠️ v0 = BTBO 同级 | ⟦ f ⟧ a = a 让 mahlo 退化为 noop |

**关键负面发现**:
- ⟦_⟧ 作为独立函数可定义, **但 ψ_M 中调用 ⟦_⟧ 会让 Agda 终止检查器拒绝**, 即使 v0 ⟦_⟧ 是 identity. 因为终止检查器不展开函数调用.
- 这意味着 Path C 的核心设计模式 (用 Opᴹ 语义驱动 ψ_M) **结构性不兼容 Agda 句法 termination check**. 要真正用 ⟦_⟧, 必须借助 Well-founded recursion / Sized Types / 内联展开等额外机制.
- 内联版本仅是"忽略 mahlo 的 f", 等价于 Phase 4 不用 f 的设计, **强度 = BTBO, 不超过 Higher.agda**.

**Phase 6 真 Setzer 路径需要的额外工作**:
- ψ_M-C 用 ⟦_⟧ 驱动: ~300-500 LOC + Well-founded recursion 框架
- ⟦_⟧ 非平凡版本 (v1/v2) + 单调性证明: ~150-200 LOC
- 总计 Phase 6 路径 C 完整投入: **~500-900 LOC**, 与 plan agent C 估算一致

**当前 spike 价值**: 
1. ✓ 验证 ⟦_⟧ post-mutual 函数兼容 8 层 mutual block (无 positivity 问题).
2. ✗ **暴露 Agda 终止检查与 Opᴹ-驱动 ψ_M 的根本性不兼容** — 这是 Path C 的 Phase 6 主险, 必须早期识别.

诚实评估: Path C 在 spike 阶段**部分失败** (主目标 ψ_M-with-⟦_⟧ 撞墙), 仅 ⟦_⟧ 独立定义部分成功.

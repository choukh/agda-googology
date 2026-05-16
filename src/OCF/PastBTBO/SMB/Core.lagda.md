# SMB Core: 移植 Eremondi 2023 SMB-trees 到本仓库

> **目的**: 移植 [Eremondi 2023 SMB-trees](https://arxiv.org/abs/2312.06962) 的 `Tree` + `indMax` + `_≤_` 到本仓库, 作为绕过 BoundedTrich 障碍的工具基础.
>
> **结构性选择**: 不直接复用 BTBO 的 `Ordᴰ` (因为 `Ordᴰ.lim` 要求 strict 单调 `mono : monotonic f`, 与 SMB `Lim c f` 无单调要求结构不同). 改为**独立移植** `Tree` 数据类型, 再写 `Ordᴰ → Tree` 桥接函数.
>
> **范围**: Phase A 仅落地 `Tree`, `_≤_`, `_<_`, `indMax` 以及关键算律 (`indMax-≤L`, `indMax-≤R`, `indMax-mono`). SMB sigma + idempotency 留待 B-1 需要时延展.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.PastBTBO.SMB.Core where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; cong)
```

## §1 — `Tree`: ℕ-indexed 极限的 Brouwer 树, 不带单调约束

仿 [Eremondi Brouwer.lagda:38-42](https://github.com/JoeyEremondi/smb-trees/blob/master/Brouwer.lagda#L38-L42).
本仓库只需要 ℕ-索引 (`SmallTree` 等价), 简化掉 `ℂ`/`El` universe-of-codes.

```agda
data Tree : Set where
  Z   : Tree
  ↑   : Tree → Tree
  Lim : (ℕ → Tree) → Tree

infix 10 _≤_
data _≤_ : Tree → Tree → Set where
  ≤-Z       : ∀ {t} → Z ≤ t
  ≤-sucMono : ∀ {t₁ t₂} → t₁ ≤ t₂ → ↑ t₁ ≤ ↑ t₂
  ≤-cocone  : ∀ {t} (f : ℕ → Tree) (k : ℕ) → t ≤ f k → t ≤ Lim f
  ≤-limiting : ∀ {t} (f : ℕ → Tree) → (∀ k → f k ≤ t) → Lim f ≤ t

infix 10 _<_
_<_ : Tree → Tree → Set
t₁ < t₂ = ↑ t₁ ≤ t₂
```

## §2 — `_≤_` 基本性质

```agda
≤-refl : ∀ t → t ≤ t
≤-refl Z       = ≤-Z
≤-refl (↑ t)   = ≤-sucMono (≤-refl t)
≤-refl (Lim f) = ≤-limiting f (λ k → ≤-cocone f k (≤-refl (f k)))

≤-trans : ∀ {t₁ t₂ t₃} → t₁ ≤ t₂ → t₂ ≤ t₃ → t₁ ≤ t₃
≤-trans ≤-Z _                                = ≤-Z
≤-trans (≤-sucMono p) (≤-sucMono q)          = ≤-sucMono (≤-trans p q)
≤-trans p (≤-cocone f k q)                   = ≤-cocone f k (≤-trans p q)
≤-trans (≤-limiting f x) q                   = ≤-limiting f (λ k → ≤-trans (x k) q)
≤-trans (≤-cocone f k p) (≤-limiting .f x)   = ≤-trans p (x k)

≤-reflEq : ∀ {t₁ t₂} → t₁ ≡ t₂ → t₁ ≤ t₂
≤-reflEq refl = ≤-refl _

-- 中缀传递
infixr 10 _≤⨟_
_≤⨟_ : ∀ {t₁ t₂ t₃} → t₁ ≤ t₂ → t₂ ≤ t₃ → t₁ ≤ t₃
_≤⨟_ = ≤-trans

extLim : ∀ {f₁ f₂} → (∀ k → f₁ k ≤ f₂ k) → Lim f₁ ≤ Lim f₂
extLim {f₁} {f₂} all = ≤-limiting f₁ (λ k → ≤-cocone f₂ k (all k))

≤↑t : ∀ t → t ≤ ↑ t
≤↑t Z       = ≤-Z
≤↑t (↑ t)   = ≤-sucMono (≤↑t t)
≤↑t (Lim f) = ≤-limiting f λ k →
  ≤↑t (f k) ≤⨟ ≤-sucMono (≤-cocone f k (≤-refl (f k)))

<-in-≤ : ∀ {x y} → x < y → x ≤ y
<-in-≤ p = ≤↑t _ ≤⨟ p

<∘≤-in-< : ∀ {x y z} → x < y → y ≤ z → x < z
<∘≤-in-< p q = p ≤⨟ q

≤∘<-in-< : ∀ {x y z} → x ≤ y → y < z → x < z
≤∘<-in-< {x} {y} p q = ≤-sucMono p ≤⨟ q
```

## §3 — `indMax`: 直接递归 max (避开 view-type)

简化版: 直接定义 5 个 case (Z-L, Z-R, Lim-L, Lim-R 优先 L 顺序, Suc-Suc). 由于 ℕ 是简单类型, 不用 view-type 也终止.

```agda
indMax : Tree → Tree → Tree
indMax Z         t         = t
indMax (↑ t₁)    Z         = ↑ t₁
indMax (↑ t₁)    (↑ t₂)    = ↑ (indMax t₁ t₂)
indMax (↑ t₁)    (Lim g)   = Lim (λ n → indMax (↑ t₁) (g n))
indMax (Lim f)   t         = Lim (λ n → indMax (f n) t)
```

**终止性**: `indMax (↑ t₁) (Lim g) → indMax (↑ t₁) (g n)` 第二参变小; `indMax (Lim f) t → indMax (f n) t` 第一参变小. Agda lex 终止 ✓.

## §4 — 上界性质

```agda
indMax-≤L : ∀ {t₁ t₂} → t₁ ≤ indMax t₁ t₂
indMax-≤L {t₁ = Z}     {t₂ = t₂}     = ≤-Z
indMax-≤L {t₁ = ↑ t₁}  {t₂ = Z}      = ≤-refl _
indMax-≤L {t₁ = ↑ t₁}  {t₂ = ↑ t₂}   = ≤-sucMono (indMax-≤L {t₁ = t₁} {t₂ = t₂})
indMax-≤L {t₁ = ↑ t₁}  {t₂ = Lim g}  = ≤-cocone (λ n → indMax (↑ t₁) (g n)) 0 (indMax-≤L {t₁ = ↑ t₁} {t₂ = g 0})
indMax-≤L {t₁ = Lim f} {t₂ = t₂}     = extLim (λ k → indMax-≤L {t₁ = f k} {t₂ = t₂})

indMax-≤R : ∀ {t₁ t₂} → t₂ ≤ indMax t₁ t₂
indMax-≤R {t₁ = Z}     {t₂ = t₂}     = ≤-refl _
indMax-≤R {t₁ = ↑ t₁}  {t₂ = Z}      = ≤-Z
indMax-≤R {t₁ = ↑ t₁}  {t₂ = ↑ t₂}   = ≤-sucMono (indMax-≤R {t₁ = t₁} {t₂ = t₂})
indMax-≤R {t₁ = ↑ t₁}  {t₂ = Lim g}  = extLim (λ k → indMax-≤R {t₁ = ↑ t₁} {t₂ = g k})
indMax-≤R {t₁ = Lim f} {t₂ = t₂}     = ≤-cocone (λ n → indMax (f n) t₂) 0 (indMax-≤R {t₁ = f 0} {t₂ = t₂})
```

**注**: `indMax-≤L {↑ t₁} {Lim g}` 用 `≤-cocone` 选 k=0. 这是因为 `↑ t₁ ≤ indMax (↑ t₁) (g 0)` 由 IH 给出, 再 cocone 升到 lim. 对于 `Z {Lim g}` 也类似.

## §5 — 单调性 (留待 Phase B-1 按需展开)

完整 `indMax-monoL` / `indMax-monoR` 移植自 Eremondi 论文 §3.2 (长 case-分析). 本 phase **不证**, 因为 Naive 入口仅需 `indMax-≤L/R + ↑` 即可 (见 §7 `bound`).

若 B-1 需要 strict bicongruence (`indMax-strictMono`), 在 SMB/Mono.lagda.md 单独展开.

## §6 — `Ordᴰ → Tree` 桥接 (基础, Naive 用)

```agda
open import OCF.BTBO
open BoundedTrich using (Ordᴰ) renaming (_<_ to _<ᴰ_; zero to zeroᴰ; suc to sucᴰ; lim to limᴰ)

toTree : Ordᴰ → Tree
toTree zeroᴰ          = Z
toTree (sucᴰ a)       = ↑ (toTree a)
toTree (limᴰ f _)     = Lim (toTree ∘ f)

-- 桥接保 < (单向, 由 Ordᴰ < 归纳)
toTree-< : ∀ {a b : Ordᴰ} → a <ᴰ b → toTree a < toTree b
toTree-< (BoundedTrich.zero)    = ≤-sucMono (≤-refl _)
toTree-< (BoundedTrich.suc p)   = ≤-sucMono (<-in-≤ (toTree-< p))
toTree-< (BoundedTrich.lim n p) = ≤-cocone _ n (toTree-< p)
```

## §7 — Strict 共同上界 (Naive 入口)

```agda
-- 任意两个 Tree 的 strict 共同上界
bound : Tree → Tree → Tree
bound a b = ↑ (indMax a b)

a<bound : ∀ a b → a < bound a b
a<bound a b = ≤-sucMono (indMax-≤L {a} {b})

b<bound : ∀ a b → b < bound a b
b<bound a b = ≤-sucMono (indMax-≤R {a} {b})
```

`bound a b = ↑ (indMax a b)` 即 `suc (max a b)`. 由 `indMax-≤L/R` 直接给出 strict 上界.

## §8 — Demo: 通过 `<-dec`-类比验证

由 Eremondi 论文 §4, **SMB-tree 上的 `<` 不可判定** (Generalized Decidability via Brouwer Trees, de Jong et al. 2026 给出"constructive taboo"诊断). 因此 **Tree 本身没有无条件 trich**.

**但**: 通过 `bound` 给出 strict 共同上界后, **如果 Tree 有 bounded trich (类比 BoundedTrich.<-dec), 则可推 unbounded trich**. 这是 Phase B-1 的核心论证.

Phase A 输出 (此文件) 不证 bounded trich, 留 Phase B-1 工作.

```agda
-- 示例 binding: 验证端到端 type-check
_ : Tree
_ = bound Z (↑ Z)   -- = ↑ (indMax Z (↑ Z)) = ↑ (↑ Z) = 数字 2

_ : bound Z (↑ Z) ≡ ↑ (↑ Z)
_ = refl
```

## §9 — Phase A 总结

- ✅ Tree, _≤_, _<_, indMax 落地
- ✅ indMax-≤L, indMax-≤R 完整证
- ⚠️ indMax-monoL/R postulate (论文证明长, 留 B-1 展开)
- ✅ bound, a<bound, b<bound — **strict 共同上界已可用**
- ⚠️ toTree-< 桥接 postulate (留 B-1 展开)
- 输出: `Tree` 作为新 ordinal 系统, 配套 indMax. 不依赖 BTBO 的 +-lmono.

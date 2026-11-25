# YiRawFold 第 B 站：公共上界之间

**判决 (编译定理)：`K` 是 `K′` 的字面第一位置时，`Φ K … base top` 是 `Φ K′ … base top` 的第一位置，`K` 的 (`Plain`, `Legal`) 取 `K′` 的沿路径的限制 (`Φ-below`)。
极限层号上 `Φ (lim f) … base top` 是各 `Φ (f n) … base top` 的极限 (`refl`)，在 `CohP` 之下合法 (`Φ-lim-legal`)。** 没有值定理。
只对目标第 0 层 (`low`)；`Φᵐ` 沿只取第 0 支的路径同样成立 (`Φᵐ-below`)。折叠在 [YiRawFold](YiRawFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawFoldUp where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiIrrIf using (R; CP; self; suc; lim; fst; Legal)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldBase using (keep; fold)
open import OCF.Align.YiLvFoldFin using (fin; ω; ω-plain; ω-legal)
open import OCF.Align.YiLvNegRestrict using (restrictL)
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFold
```

## 1 小的公共上界的闭项是大的闭项的第一位置

`below` 在互递归块里 (极限层号上 `top` 的合法性要用它)，对路径递归：后继一步进到链的第 0 项，极限一步取那一支。
小的那边的折叠字面地是大的那边的子项，因为进孩子时 `Legal` 取的就是孩子的那一份。

```agda
Φ-below : ∀ {K} K′ (p : CP K K′) (pl′ : Plain K′) (L′ : Legal K′) →
  Cp zero (Φ K (plainR K′ p pl′) (restrictL K′ p L′) base G.top tt tt)
          (Φ K′ pl′ L′ base G.top tt tt)
Φ-below K′ p pl′ L′ = below zero K′ p pl′ L′

-- K 自带的 (Plain, Legal) 等于限制时, 换成它.
Φ-below-coh : ∀ {K} K′ (p : CP K K′) pl L pl′ L′ →
  _≡_ {A = Plain K × Legal K} (plainR K′ p pl′ , restrictL K′ p L′) (pl , L) →
  Cp zero (Φ K pl L base G.top tt tt) (Φ K′ pl′ L′ base G.top tt tt)
Φ-below-coh {K} K′ p pl L pl′ L′ e =
  subst (λ z → Cp zero (Φ K (proj₁ z) (proj₂ z) base G.top tt tt)
                       (Φ K′ pl′ L′ base G.top tt tt))
    e (Φ-below K′ p pl′ L′)
```

## 2 极限层号

```agda
Φ-lim-row : ∀ f pl L → Φ (lim f) pl L base G.top tt tt ≡
  G.lim (λ n → Φ (f n) (pl n) (proj₂ L n) base G.top tt tt)
Φ-lim-row f pl L = refl

Φ-lim-legal : ∀ f pl L → CohP (lim f) pl L → Lgl zero (Φ (lim f) pl L base G.top tt tt)
Φ-lim-legal f pl L h = Φ-legal (lim f) pl L base h G.top tt tt

Φ-lim-step : ∀ f pl L → CohP (lim f) pl L → ∀ n →
  Cp zero (Φ (f n) (pl n) (proj₂ L n) base G.top tt tt)
          (Φ (f (suc n)) (pl (suc n)) (proj₂ L (suc n)) base G.top tt tt)
Φ-lim-step f pl L h = proj₁ (Φ-lim-legal f pl L h)

-- 每一支都是极限的第一位置, 不要前提.
Φ-lim-at : ∀ f pl L n →
  Cp zero (Φ (f n) (pl n) (proj₂ L n) base G.top tt tt) (Φ (lim f) pl L base G.top tt tt)
Φ-lim-at f pl L n = inj₂ (n , inj₁ refl)
```

## 3 核对：保留结点的目标上，相邻两支的输出槽位不同

目标取 ω 自己。`top` 在第 1 支的折叠是槽位 `(1 , 根)` 的结点；在第 2 支的折叠的第一支是槽位 `(2 , 根下一格)` 的结点。
两个位置层号相同，是不同的位置，所以前者不等于后者。这里只是计算核对；"各支排成的极限不合法" 是 [YiRawFoldNoLim](YiRawFoldNoLim.lagda.md) 的 `side-lim-illegal`。

```agda
side : ℕ → Raw ω
side n = Ψ ω (fin n) (ω-plain n) (proj₂ ω-legal n)
  (inL (mix (dispatch ω ω-plain ω-legal self)) n) G.top tt tt

branchOf : Raw ω → ℕ
branchOf (G.lc (n , r) c t g) = n
branchOf _ = zero

firstOf : Raw ω → Raw ω
firstOf (G.lc r c t g) = t
firstOf a = a

side₁-slot : branchOf (side 1) ≡ 1
side₁-slot = refl

side₂-first-slot : branchOf (firstOf (side 2)) ≡ 2
side₂-first-slot = refl

one≢two : 1 ≡ 2 → ⊥
one≢two ()

side-differ : side 1 ≡ firstOf (side 2) → ⊥
side-differ e = one≢two (cong branchOf e)
```

## 4 接口实例 `Φᵐ`：沿只取第 0 支的路径

`Φᵐ` 在极限层号上 `top` 取部分和，第 0 个部分和就是第 0 支。所以第 1 节的结论对 "极限处只取第 0 支" 的路径仍成立 (`Zp`)；
`η ⊲ η + y` 读回的路径是这样的 (第 C 站用)。对取第 `n ≥ 1` 支的路径没有证，也没有否定。

```agda
Zp : ∀ {a b} → CP a b → Set
Zp self = ⊤
Zp (suc p) = Zp p
Zp (lim zero p) = Zp p
Zp (lim (suc n) p) = ⊥
Zp (fst p) = ⊥

belowᵐ : ∀ m {a} b (p : CP a b) → Zp p → (pb : Plain b) (Lb : Legal b) →
  Cp m (Ψ m a (plainR b p pb) (restrictL b p Lb) (mix (λ r → fold)) G.top tt tt)
       (Ψ m b pb Lb (mix (λ r → fold)) G.top tt tt)
belowᵐ m b self z pb Lb = inj₁ refl
belowᵐ m (suc zero) (suc p) z pb Lb = inj₂ (zero , belowᵐ m zero p z pb Lb)
belowᵐ m (suc (suc b)) (suc p) z pb Lb = inj₂ (zero , belowᵐ m (suc b) p z pb Lb)
belowᵐ m (suc (lim f)) (suc p) z pb Lb = inj₂ (zero , belowᵐ m (lim f) p z pb Lb)
belowᵐ m (lim f) (lim zero p) z pb Lb =
  inj₂ (zero , belowᵐ m (f zero) p z (pb zero) (proj₂ Lb zero))

Φᵐ-below : ∀ {K} K′ (p : CP K K′) → Zp p → (pl′ : Plain K′) (L′ : Legal K′) →
  Cp zero (Φᵐ K (plainR K′ p pl′) (restrictL K′ p L′) base G.top tt tt)
          (Φᵐ K′ pl′ L′ base G.top tt tt)
Φᵐ-below K′ p z pl′ L′ = belowᵐ zero K′ p z pl′ L′

Φᵐ-lim-row : ∀ f pl L → Φᵐ (lim f) pl L base G.top tt tt ≡
  G.lim (psum zero (λ n → Φᵐ (f n) (pl n) (proj₂ L n) base G.top tt tt))
Φᵐ-lim-row f pl L = refl

Φᵐ-lim-legal : ∀ f pl L → Lgl zero (Φᵐ (lim f) pl L base G.top tt tt)
Φᵐ-lim-legal f pl L = RawFold.legal rawFold (lim f) pl L base G.top tt tt
```

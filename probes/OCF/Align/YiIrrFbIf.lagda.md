# YiIrrFb 接口：两个目标层的折叠与第一次回灌

**档位：定义与接口记录，另有一条编译否定。** 片段是 Ω 结点层号字面为 0 或 1 的树；记录 `FbRows` 写两个目标层的行，
回灌行是 `next₁-additive` 加 `feedback-row`：层号 1 的结点上，`ψ₀` 的链点由 `ψ₁` 的输出推进。
与简报描述不同的两处见 §1 (`zero-not-below-top`)；不否定任何路线。实填在 [YiIrrFb](YiIrrFb.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFbIf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf

L1 : LF
L1 = suc zero

R₁ : Set
R₁ = Raw L1

Ω₂ : LF
Ω₂ = Ω̂ (suc L1)
```

## 1 第 1 层的算术

`Raw 1` 里 `em a` 是第 0 层的值 `a` 的嵌入，`top` 读作 Ω₁，`lc` 是层 0 槽位的结点。
加法对第二个加数递归；`top` 没有放前缀的位置，所以 `x +¹ top` 写成它展开后的结点
(下界 1，第一支 `x + 1`，分支 `η ↦ x + η`)。

**与第 0 层不同的两处，同一个原因。** `Raw 1` 里 `zero` 不是 `top` 的第一位置 (`zero-not-below-top`)，
而 `ψ₁` 的零行给 `top`。所以 (1) "输出为正" 不能写成 `Dn 1 zero (ψ₁ x)`，接口改成它的用途：
任何 `η` 加上输出都严格增长 (`fold-grow₁`)；(2) "ω 倍" 的第 0 项取一份而不是零份 (`copies₁ y 0 = y`)，
否则极限的第一步 `Cp 1 zero y` 在 `y = top` 处不成立。

```agda
embed-add : R₁ → R → R₁
embed-add x G.zero = x
embed-add x (G.suc a) = G.suc (embed-add x a)
embed-add x (G.lim f) = G.lim (λ n → embed-add x (f n))
embed-add x (G.lc () c t g)
embed-add x (G.em () a)
embed-add x G.top = G.suc x

infixl 6 _+¹_
_+¹_ : R₁ → R₁ → R₁
x +¹ G.zero = x
x +¹ G.suc y = G.suc (x +¹ y)
x +¹ G.lim f = G.lim (λ n → x +¹ f n)
x +¹ G.lc r c t g = G.lc r c (x +¹ t) (λ η e → x +¹ g η e)
x +¹ G.em _ a = embed-add x a
x +¹ G.top = G.lc (inj₁ tt) one (G.suc x) (λ η e → embed-add x η)

copies₁ : R₁ → ℕ → R₁
copies₁ y zero = y
copies₁ y (suc n) = y +¹ copies₁ y n

successor₁ : R₁ → R₁
successor₁ y = G.lim (copies₁ y)

zero-not-below-top : Cp L1 G.zero G.top → ⊥
zero-not-below-top (inj₁ ())
zero-not-below-top (inj₂ ())
```

## 2 片段与链点

`Only01`：Ω 结点的层号字面为 0 或 1，对第一支与分支遗传。`Pt k c`：层 `k` 上的链点，守卫无关。

```agda
Only01 : LF → Set
Only01 zero = ⊤
Only01 (suc x) = Only01 x
Only01 (lim f) = ∀ n → Only01 (f n)
Only01 (lc zero c w b t g) =
  Only01 t × (∀ η .(e : Gd zero c η) → Only01 (g η e))
Only01 (lc (suc zero) c w b t g) =
  Only01 t × (∀ η .(e : Gd L1 c η) → Only01 (g η e))
Only01 (lc (suc (suc k)) c w b t g) = ⊥
Only01 (lc (suc (lim f)) c w b t g) = ⊥
Only01 (lc (suc (lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) = ⊥
Only01 (lc (lim f) c w b t g) = ⊥
Only01 (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) = ⊥

record Pt (k : LF) (c : Raw k) : Set where
  constructor pt
  field
    at : Raw k
    .guard : Gd k c at
open Pt public using (at)

startᴸ : ∀ k (c : Raw k) → .(Lgl k c) → .(Nested k c) → Pt k c
startᴸ k c w b = pt c (inj₁ refl , w , b)
```

## 3 接口记录

`ψ₀` 的前四行与 `YiIrrIf.FoldRows` 相同。`ψ₁` 的行：零给 `cO 1`；后继给 `successor₁`；极限逐项；
层号 0 的结点保留 (`keep-row`：槽位、下界不变，第一支与分支各自折叠)；层号 1 的结点走 `Raw 1` 里的加法链。
保留行的第一支取 `ψ₁ t`：`Raw` 的结点要一个第一支，取它才是逐支保留；因此定义域要对第一支遗传 (`dom-first`)。
层号 1 的结点上两个目标层共用一条链 `next₁`，链的推进只用 `ψ₁` (`next₁-additive`)。

```agda
record FbRows : Set₁ where
  field
    Dom : LF → Set
    dom-pred : ∀ x → Dom (suc x) → Dom x
    dom-at : ∀ f → Dom (lim f) → ∀ n → Dom (f n)
    dom-first : ∀ c (w : Lgl zero c) (b : Nested zero c) t
      (g : (η : R) → .(Gd zero c η) → LF) →
      Dom (lc zero c w b t g) → Dom t
    dom-branch₀ : ∀ c (w : Lgl zero c) (b : Nested zero c) t
      (g : (η : R) → .(Gd zero c η) → LF) →
      Dom (lc zero c w b t g) → ∀ η (e : Gd zero c η) → Dom (g η e)
    dom-branch₁ : ∀ c (w : Lgl L1 c) (b : Nested L1 c) t
      (g : (η : R₁) → .(Gd L1 c η) → LF) →
      Dom (lc L1 c w b t g) → ∀ η (e : Gd L1 c η) → Dom (g η e)
    dom-only : ∀ x → Dom x → Only01 x
    dom-legal : ∀ x → Dom x → Legal x
    dom-Ω₂ : Dom Ω₂

    ψ₀ : (x : LF) → .(Dom x) → R
    ψ₁ : (x : LF) → .(Dom x) → R₁
    next₀ : ∀ c (w : Lgl zero c) (b : Nested zero c) t
      (g : (η : R) → .(Gd zero c η) → LF) →
      .(Dom (lc zero c w b t g)) → Point c → Point c
    next₁ : ∀ c (w : Lgl L1 c) (b : Nested L1 c) t
      (g : (η : R₁) → .(Gd L1 c η) → LF) →
      .(Dom (lc L1 c w b t g)) → Pt L1 c → Pt L1 c

  -- 层号 0 的结点: 链点处的 ψ₀. 层号 1 的结点: 链点处的 ψ₁ (推进) 与 ψ₀ (输出).
  out₀ : ∀ c (w : Lgl zero c) (b : Nested zero c) t
    (g : (η : R) → .(Gd zero c η) → LF) →
    .(Dom (lc zero c w b t g)) → Point c → R
  out₀ c w b t g d (point η e) = ψ₀ (g η e) (dom-branch₀ c w b t g d η e)

  step₁ : ∀ c (w : Lgl L1 c) (b : Nested L1 c) t
    (g : (η : R₁) → .(Gd L1 c η) → LF) →
    .(Dom (lc L1 c w b t g)) → Pt L1 c → R₁
  step₁ c w b t g d (pt η e) = ψ₁ (g η e) (dom-branch₁ c w b t g d η e)

  out₁ : ∀ c (w : Lgl L1 c) (b : Nested L1 c) t
    (g : (η : R₁) → .(Gd L1 c η) → LF) →
    .(Dom (lc L1 c w b t g)) → Pt L1 c → R
  out₁ c w b t g d (pt η e) = ψ₀ (g η e) (dom-branch₁ c w b t g d η e)

  field
    -- 目标层 0
    zero-row₀ : ∀ (d : Dom zero) → ψ₀ zero d ≡ one
    suc-row₀ : ∀ x (d : Dom (suc x)) →
      ψ₀ (suc x) d ≡ successor (ψ₀ x (dom-pred x d))
    lim-row₀ : ∀ f (d : Dom (lim f)) →
      ψ₀ (lim f) d ≡ G.lim (λ n → ψ₀ (f n) (dom-at f d n))
    next₀-additive : ∀ c w b t g (d : Dom (lc zero c w b t g)) p →
      coordinate (next₀ c w b t g d p) ≡ coordinate p +ʳ out₀ c w b t g d p
    next₀-grow : ∀ c w b t g (d : Dom (lc zero c w b t g)) p →
      Dn zero (coordinate p) (coordinate (next₀ c w b t g d p))
    gt-row₀ : ∀ c w b t g (d : Dom (lc zero c w b t g)) →
      ψ₀ (lc zero c w b t g) d ≡
      G.lim (λ n → out₀ c w b t g d
        (iterate (next₀ c w b t g d) (start c w b) n))
    -- 回灌: 链在 Raw 1 里, 下一点用 ψ₁ 的输出, 输出是 ψ₀ 沿链的极限
    next₁-additive : ∀ c w b t g (d : Dom (lc L1 c w b t g)) p →
      at (next₁ c w b t g d p) ≡ at p +¹ step₁ c w b t g d p
    next₁-grow : ∀ c w b t g (d : Dom (lc L1 c w b t g)) p →
      Dn L1 (at p) (at (next₁ c w b t g d p))
    feedback-row : ∀ c w b t g (d : Dom (lc L1 c w b t g)) →
      ψ₀ (lc L1 c w b t g) d ≡
      G.lim (λ n → out₁ c w b t g d
        (iterate (next₁ c w b t g d) (startᴸ L1 c w b) n))
    -- 目标层 1
    zero-row₁ : ∀ (d : Dom zero) → ψ₁ zero d ≡ cO L1
    suc-row₁ : ∀ x (d : Dom (suc x)) →
      ψ₁ (suc x) d ≡ successor₁ (ψ₁ x (dom-pred x d))
    lim-row₁ : ∀ f (d : Dom (lim f)) →
      ψ₁ (lim f) d ≡ G.lim (λ n → ψ₁ (f n) (dom-at f d n))
    keep-row : ∀ c w b t g (d : Dom (lc zero c w b t g)) →
      ψ₁ (lc zero c w b t g) d ≡
      G.lc (inj₁ tt) c (ψ₁ t (dom-first c w b t g d))
        (λ η e → ψ₁ (g η e) (dom-branch₀ c w b t g d η e))
    gt-row₁ : ∀ c w b t g (d : Dom (lc L1 c w b t g)) →
      ψ₁ (lc L1 c w b t g) d ≡
      G.lim (λ n → step₁ c w b t g d
        (iterate (next₁ c w b t g d) (startᴸ L1 c w b) n))
    -- 引理
    fold-legal₀ : ∀ x (d : Dom x) → Lgl zero (ψ₀ x d)
    fold-positive₀ : ∀ x (d : Dom x) → Dn zero G.zero (ψ₀ x d)
    position₀ : ∀ x y (dx : Dom x) (dy : Dom y) → CP x y →
      Cp zero (ψ₀ x dx) (ψ₀ y dy)
    fold-legal₁ : ∀ x (d : Dom x) → Lgl L1 (ψ₁ x d)
    fold-nested₁ : ∀ x (d : Dom x) → Nested L1 (ψ₁ x d)
    fold-grow₁ : ∀ x (d : Dom x) η → Dn L1 η (η +¹ ψ₁ x d)
    position₁ : ∀ x y (dx : Dom x) (dy : Dom y) → CP x y →
      Cp L1 (ψ₁ x dx) (ψ₁ y dy)
```

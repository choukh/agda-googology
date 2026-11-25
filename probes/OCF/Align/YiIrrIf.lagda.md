# YiIrr：无关证据块上，目标层 0 折叠的共用接口

构造路 (`YiIrrFold*`) 与否定路 (`YiIrrNeg*`) 共用本文件。块是
[RR5IrrCore](RR5IrrCore.lagda.md)，读回与 Ω 在 [RR5IrrCheck](RR5IrrCheck.lagda.md)。
这三个文件定稿后只增不改；要补内容，另开文件。

**接口说的是什么。** 一个折叠 `ψ`，把层号树送到第 0 层的值，四行照
[YiK2bBase](YiK2bBase.lagda.md) 的 `FoldRows0`：零给 1；后继给 "输出的 ω 倍"；
ℕ 极限逐项；层号为 0 的 Ω 结点走加法链 ηₙ₊₁ = ηₙ + ψ(g ηₙ)，从下界自身起步。
与旧接口的区别只有两处，都来自新块：

1. `ψ` 的证书参数是无关参数。所以 "换证书后输出相等" 不再是要证的东西，
   它是定义性相等 (`RR5IrrCheck.CertIrr`)。
2. 定义域 `Dom` 是记录的字段，由构造路自己给，但必须对分支遗传，并且含规范的 Ω₁。
   这样陈述先落在规范实例的读回域上，不对一切合法树 (AGENTS "量化域先取带证据的读回域")。
   若 `Dom` 取成整个 "只含层号 0 的 Ω 结点且合法" 的片段也成立，构造路另外交。

本文件没有 `ψ`，只有定义、接口记录，以及 "规范 Ω₁ 合法" 这一条实例检查。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrIf where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
```

## 1 层号上的第一位置与合法性

与 `LevelFixVal` 的 `CP`, `Legal` 同形。`Legal` 是树外的谓词，它的守卫参数是普通参数：
证明合法性时可以把守卫当数据用，这不影响树。`irr` 一项恒由 `refl` 满足，
保留它只为让旧证明按六元组原样搬来。

```agda
data CP : LF → LF → Set where
  self : ∀ {a} → CP a a
  suc  : ∀ {a b} → CP a b → CP a (suc b)
  lim  : ∀ {a f} n → CP a (f n) → CP a (lim f)
  fst  : ∀ {a k c t g} .{w : Lgl k c} .{b : Nested k c} →
         CP a t → CP a (lc k c w b t g)

CP-tr : ∀ {a b d} → CP a b → CP b d → CP a d
CP-tr p self = p
CP-tr p (suc q) = suc (CP-tr p q)
CP-tr p (lim n q) = lim n (CP-tr p q)
CP-tr p (fst q) = fst (CP-tr p q)

Legal : LF → Set
Legal zero = ⊤
Legal (suc k) = Legal k
Legal (lim f) = (∀ n → CP (f n) (f (suc n))) × (∀ n → Legal (f n))
Legal (lc k c w b t g) =
  Legal k ×
  (∀ η (e : Gd k c η) → CP t (g η e)) ×
  (∀ η (e : Gd k c η) η′ (e′ : Gd k c η′) → Gd k η η′ → CP (g η e) (g η′ e′)) ×
  (∀ η (e e′ : Gd k c η) → g η e ≡ g η e′) ×
  Legal t × (∀ η (e : Gd k c η) → Legal (g η e))
```

## 2 第 0 层的值与算术

定义照 [YiK2Base](YiK2Base.lagda.md)，只换了块。第 0 层没有 Ω 结点与 `em`。

```agda
R : Set
R = Raw zero

one : R
one = G.suc G.zero

infixl 6 _+ʳ_
_+ʳ_ : R → R → R
x +ʳ G.zero = x
x +ʳ G.suc y = G.suc (x +ʳ y)
x +ʳ G.lim f = G.lim (λ n → x +ʳ f n)
x +ʳ G.lc () c t g
x +ʳ G.em () t
x +ʳ G.top = G.suc x

copies : R → ℕ → R
copies x zero = G.zero
copies x (suc n) = x +ʳ copies x n

successor : R → R
successor x = G.lim (copies x)
```

## 3 片段与链点

`Only0`：Ω 结点的层号字面为 0。它不读守卫，所以分支一项的守卫是无关的。
`Point c`：链上的一点，坐标是数据，守卫是无关的证明。

```agda
Only0 : LF → Set
Only0 zero = ⊤
Only0 (suc x) = Only0 x
Only0 (lim f) = ∀ n → Only0 (f n)
Only0 (lc zero c w b t g) = Only0 t × (∀ η .(e : Gd zero c η) → Only0 (g η e))
Only0 (lc (suc k) c w b t g) = ⊥
Only0 (lc (lim f) c w b t g) = ⊥
Only0 (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) = ⊥

record Point (c : R) : Set where
  constructor point
  field
    coordinate : R
    .guard : Gd zero c coordinate
open Point public using (coordinate)

start : ∀ c → .(Lgl zero c) → .(Nested zero c) → Point c
start c w b = point c (inj₁ refl , w , b)

iterate : ∀ {A : Set} → (A → A) → A → ℕ → A
iterate f a zero = a
iterate f a (suc n) = f (iterate f a n)
```

## 4 接口记录

`Dom` 及其遗传由构造路给出。`ψ` 的第二个参数无关。`out` 是链点处的子折叠。
`position` 是位置保持：两棵定义域里的树，前者是后者的字面第一位置，则输出也是。
自反情形现在由 `refl` 给出，不需要证书一致。

```agda
record FoldRows : Set₁ where
  field
    Dom : LF → Set
    dom-pred : ∀ x → Dom (suc x) → Dom x
    dom-at : ∀ f → Dom (lim f) → ∀ n → Dom (f n)
    dom-branch : ∀ c (w : Lgl zero c) (b : Nested zero c) t
      (g : (η : R) → .(Gd zero c η) → LF) →
      Dom (lc zero c w b t g) → ∀ η (e : Gd zero c η) → Dom (g η e)
    dom-only : ∀ x → Dom x → Only0 x
    dom-legal : ∀ x → Dom x → Legal x
    dom-Ω₁ : Dom (tw 2)

    ψ : (x : LF) → .(Dom x) → R
    next : ∀ c (w : Lgl zero c) (b : Nested zero c) t
      (g : (η : R) → .(Gd zero c η) → LF) →
      .(Dom (lc zero c w b t g)) → Point c → Point c

  out : ∀ c (w : Lgl zero c) (b : Nested zero c) t
    (g : (η : R) → .(Gd zero c η) → LF) →
    .(Dom (lc zero c w b t g)) → Point c → R
  out c w b t g d (point η e) = ψ (g η e) (dom-branch c w b t g d η e)

  field
    zero-row : ∀ (d : Dom zero) → ψ zero d ≡ one
    suc-row : ∀ x (d : Dom (suc x)) →
      ψ (suc x) d ≡ successor (ψ x (dom-pred x d))
    lim-row : ∀ f (d : Dom (lim f)) →
      ψ (lim f) d ≡ G.lim (λ n → ψ (f n) (dom-at f d n))
    next-additive : ∀ c w b t g (d : Dom (lc zero c w b t g)) p →
      coordinate (next c w b t g d p) ≡ coordinate p +ʳ out c w b t g d p
    next-grow : ∀ c w b t g (d : Dom (lc zero c w b t g)) p →
      Dn zero (coordinate p) (coordinate (next c w b t g d p))
    gt-row : ∀ c w b t g (d : Dom (lc zero c w b t g)) →
      ψ (lc zero c w b t g) d ≡
      G.lim (λ n → out c w b t g d
        (iterate (next c w b t g d) (start c w b) n))
    fold-legal : ∀ x (d : Dom x) → Lgl zero (ψ x d)
    fold-positive : ∀ x (d : Dom x) → Dn zero G.zero (ψ x d)
    position : ∀ x y (dx : Dom x) (dy : Dom y) → CP x y →
      Cp zero (ψ x dx) (ψ y dy)
```

## 5 规范实例检查：Ω₁ 在片段里并且合法

接口要求 `Dom (tw 2)`。这里先确认它不被 `Only0` 与 `Legal` 排除，
免得接口对规范实例就不可满足。读回在第 0 层就是逐构造子的拷贝。

```agda
read0 : R → LF
read0 a = up zero a (raw0-Nested a)

read0-cp : ∀ {a} b → Cp zero a b → CP (read0 a) (read0 b)
read0-dn : ∀ {a} b → Dn zero a b → CP (read0 a) (read0 b)
read0-cp b (inj₁ refl) = self
read0-cp b (inj₂ p) = read0-dn b p
read0-dn (G.suc b) p = suc (read0-cp b p)
read0-dn (G.lim f) (n , p) = lim n (read0-cp (f n) p)
read0-dn (G.lc () c t g) p
read0-dn (G.em () a) p
read0-dn G.top ()

read0-legal : ∀ a → Lgl zero a → Legal (read0 a)
read0-legal G.zero l = tt
read0-legal (G.suc a) l = read0-legal a l
read0-legal (G.lim f) (st , lf) =
  (λ n → read0-cp (f (suc n)) (st n)) , (λ n → read0-legal (f n) (lf n))
read0-legal (G.lc () c t g) l
read0-legal (G.em () a) l
read0-legal G.top l = tt

read0-only : ∀ a → Only0 (read0 a)
read0-only G.zero = tt
read0-only (G.suc a) = read0-only a
read0-only (G.lim f) = λ n → read0-only (f n)
read0-only (G.lc () c t g)
read0-only (G.em () a)
read0-only G.top = tt

Ω₁-only : Only0 (tw 2)
Ω₁-only = tt , (λ η e → read0-only η)

Ω₁-legal : Legal (tw 2)
Ω₁-legal =
  tt ,
  (λ η e → read0-cp η (proj₁ e)) ,
  (λ η e η′ e′ d → read0-cp η′ (proj₁ d)) ,
  (λ η e e′ → refl) ,
  tt ,
  (λ η e → read0-legal η (proj₁ (proj₂ e)))
```

`Ω₁-only`, `Ω₁-legal` 说明接口对规范的 Ω₁ 不是空的要求；它们不是折叠。

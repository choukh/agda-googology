# YiIrrNeg 第 1、2 项：接口迫使什么，以及 "证明当数据" 的精确陈述

否定路对 [YiIrrIf](YiIrrIf.lagda.md) 的 `FoldRows` 本身的检查。本篇不构造 `ψ`，
只从一个任意的实例 `F : FoldRows` 推结论，另给几个与 `F` 无关的闭见证。

**结论。**

- **第 1 项（接口本身）：未找到 `FoldRows → ⊥` 或 `FoldRows → WLPO`。** 搜索范围写在文末。
  本篇编译的是这次搜索用到的事实：定义域被迫包含哪些对象（§2），
  在其中两个退化坐标与规范链的头一步上，接口索要的类型各有不依赖 `F` 的闭居民（§3）。
  这些是逐点的核对，属有限检查，不是可满足性的证明。
  可满足性的证明后来另有：[YiIrrNegModel](YiIrrNegModel.lagda.md) 给出 `model : FoldRows`，
  所以 `FoldRows → ⊥` 不可证，`FoldRows → WLPO` 等于直接证明 WLPO。
- **第 2 项（证明当数据）：没有字段迫使输出依赖证明的内容；反过来的陈述是定理。**
  `ψ` 的输出不依赖证书（`refl`）；子折叠 `out` 不依赖结点证据与守卫（`refl`）；
  `next` 虽然把 `w`、`b` 写成相关参数，接口自己推出它不依赖它们（`next-irr`）；
  整条链逐点不依赖任何证明（`chain-irr`）。gt 行另外推出一条函数相等
  （`gt-function-required`），它是必要条件；`next` 不看 `w`、`b` 时它是 `refl`。
- 接口里真正要 "相关的证明" 的地方不在输出，而在 `fold-legal` 与 `position` 这两个
  本身就是证明的字段：它们在 Ω 结点处要一份相关的下界合法证据。规范 Ω₁ 的下界是字面的 1，
  证据是 `tt`；定义域放宽以后的情形见 [YiIrrNegWide](YiIrrNegWide.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrNegForced where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
```

## 1 证明不是数据：从接口推出的四条

链点只有坐标是数据，所以坐标相等的两个链点相等。

```agda
lim-body : R → ℕ → R
lim-body (G.lim f) = f
lim-body _ = λ n → G.zero

point-ext : ∀ {c} (p q : Point c) → coordinate p ≡ coordinate q → p ≡ q
point-ext (point a ea) (point .a eb) refl = refl

module Consequences (F : FoldRows) where
  open FoldRows F

  -- 换证书, 输出定义性相等.
  ψ-certificate-irr : ∀ x (d d′ : Dom x) → ψ x d ≡ ψ x d′
  ψ-certificate-irr x d d′ = refl

  -- 换结点里的两份证明、换定义域证据、换守卫, 子折叠定义性相等.
  out-evidence-irr : ∀ c (w w′ : Lgl zero c) (b b′ : Nested zero c) t
    (g : (η : R) → .(Gd zero c η) → LF)
    (d d′ : Dom (lc zero c w b t g)) η (e e′ : Gd zero c η) →
    out c w b t g d (point η e) ≡ out c w′ b′ t g d′ (point η e′)
  out-evidence-irr c w w′ b b′ t g d d′ η e e′ = refl

  -- next 把 w, b 写成相关参数; 加法行把它的坐标钉死, 所以它不依赖它们.
  next-irr : ∀ c (w w′ : Lgl zero c) (b b′ : Nested zero c) t
    (g : (η : R) → .(Gd zero c η) → LF)
    (d d′ : Dom (lc zero c w b t g)) p →
    next c w b t g d p ≡ next c w′ b′ t g d′ p
  next-irr c w w′ b b′ t g d d′ p = point-ext _ _
    (trans (next-additive c w b t g d p)
      (sym (next-additive c w′ b′ t g d′ p)))

  -- 整条链逐点不依赖任何证明.
  chain-irr : ∀ c (w w′ : Lgl zero c) (b b′ : Nested zero c) t
    (g : (η : R) → .(Gd zero c η) → LF)
    (d d′ : Dom (lc zero c w b t g)) n →
    iterate (next c w b t g d) (start c w b) n ≡
    iterate (next c w′ b′ t g d′) (start c w′ b′) n
  chain-irr c w w′ b b′ t g d d′ zero = refl
  chain-irr c w w′ b b′ t g d d′ (suc n) =
    trans (cong (next c w b t g d) (chain-irr c w w′ b b′ t g d d′ n))
      (next-irr c w w′ b b′ t g d d′
        (iterate (next c w′ b′ t g d′) (start c w′ b′) n))

  gt-pointwise-irr : ∀ c (w w′ : Lgl zero c) (b b′ : Nested zero c) t
    (g : (η : R) → .(Gd zero c η) → LF)
    (d d′ : Dom (lc zero c w b t g)) n →
    out c w b t g d (iterate (next c w b t g d) (start c w b) n) ≡
    out c w′ b′ t g d′ (iterate (next c w′ b′ t g d′) (start c w′ b′) n)
  gt-pointwise-irr c w w′ b b′ t g d d′ n =
    cong (out c w b t g d) (chain-irr c w w′ b b′ t g d d′ n)

  -- 必要条件: gt 行的左边不含证明, 所以两份证明给出的极限体作为函数相等.
  -- 这是 YiK2cIrr.lim-function-equality-required 在新块上的对应;
  -- next 不看 w, b 时它由 refl 满足, 不要函数外延.
  gt-function-required : ∀ c (w w′ : Lgl zero c) (b b′ : Nested zero c) t
    (g : (η : R) → .(Gd zero c η) → LF)
    (d d′ : Dom (lc zero c w b t g)) →
    (λ n → out c w b t g d
      (iterate (next c w b t g d) (start c w b) n)) ≡
    (λ n → out c w′ b′ t g d′
      (iterate (next c w′ b′ t g d′) (start c w′ b′) n))
  gt-function-required c w w′ b b′ t g d d′ = cong lim-body
    (trans (sym (gt-row c w b t g d)) (gt-row c w′ b′ t g d′))
```

## 2 定义域被迫包含的对象

`Dom` 由构造路选，但必须含规范 Ω₁ 并对分支、前驱、极限项遗传。所以它被迫包含
一切带（相关）守卫的正坐标的读回，以及它们的前驱与各项；其中有退化坐标。

```agda
Ω₁-branch : (η : R) → .(Gd zero one η) → LF
Ω₁-branch η e = up zero η (proj₂ (proj₂ e))

Ω₁-form : tw 2 ≡ lc zero one tt tt (suc zero) Ω₁-branch
Ω₁-form = refl

-- 常值极限 lim (1, 1, …): 合法 (相邻项字面相等), 1 是它的第一位置.
cst : R
cst = G.lim (λ n → one)

cst-guard : Gd zero one cst
cst-guard = inj₂ (zero , inj₁ refl) , ((λ n → inj₁ refl) , (λ n → tt)) , (λ n → tt)

-- RR5IrrCheck 的 coord = suc (lim (const 1)), 它有两份不同的守卫.
coord-guard₀ : Gd zero one coord
coord-guard₀ = coord-guard zero

module Forced (F : FoldRows) where
  open FoldRows F

  forced : ∀ η → Gd zero one η → Dom (read0 η)
  forced η e = dom-branch one tt tt (suc zero) Ω₁-branch dom-Ω₁ η e

  dom-cst : Dom (lim (λ n → suc zero))
  dom-cst = forced cst cst-guard

  dom-coord : Dom (suc (lim (λ n → suc zero)))
  dom-coord = forced coord coord-guard₀

  dom-one : Dom (suc zero)
  dom-one = dom-at (λ n → suc zero) dom-cst zero

  dom-zero : Dom zero
  dom-zero = dom-pred zero dom-one

  -- 被迫的值.
  ψ-one : ψ (suc zero) dom-one ≡ successor one
  ψ-one = trans (suc-row zero dom-one) (cong successor (zero-row dom-zero))

  ψ-cst : ψ (lim (λ n → suc zero)) dom-cst ≡ G.lim (λ n → successor one)
  ψ-cst = trans (lim-row (λ n → suc zero) dom-cst)
    (cong (λ z → G.lim (λ n → z)) ψ-one)

  ψ-coord : ψ (suc (lim (λ n → suc zero))) dom-coord ≡
    successor (G.lim (λ n → successor one))
  ψ-coord = trans (suc-row (lim (λ n → suc zero)) dom-coord)
    (cong successor ψ-cst)

  -- 规范链的头两点: 起点是 1, 第二点的坐标是 1 + ω.
  first-out : out one tt tt (suc zero) Ω₁-branch dom-Ω₁ (start one tt tt) ≡
    successor one
  first-out = ψ-one

  second-coordinate :
    coordinate (next one tt tt (suc zero) Ω₁-branch dom-Ω₁ (start one tt tt)) ≡
    one +ʳ successor one
  second-coordinate = trans
    (next-additive one tt tt (suc zero) Ω₁-branch dom-Ω₁ (start one tt tt))
    (cong (one +ʳ_) ψ-one)
```

## 3 在这些对象上，接口索要的类型有不依赖 `F` 的居民

下面的项都是闭的。它们说明：把 §2 的被迫值代进 `fold-legal`、`fold-positive`、`next-grow`
索要的类型之后，这些类型在两个退化坐标与链的头一步上不空。

```agda
add-mono : ∀ x {a} b → Cp zero a b → Cp zero (x +ʳ a) (x +ʳ b)
add-mono-dn : ∀ x {a} b → Dn zero a b → Dn zero (x +ʳ a) (x +ʳ b)
add-mono x b (inj₁ refl) = inj₁ refl
add-mono x b (inj₂ p) = inj₂ (add-mono-dn x b p)
add-mono-dn x G.zero ()
add-mono-dn x (G.suc b) p = add-mono x b p
add-mono-dn x (G.lim f) (n , p) = n , add-mono x (f n) p
add-mono-dn x (G.lc () c t g) p
add-mono-dn x (G.em () a) p
add-mono-dn x G.top ()

add-legal : ∀ x y → Lgl zero x → Lgl zero y → Lgl zero (x +ʳ y)
add-legal x G.zero lx ly = lx
add-legal x (G.suc y) lx ly = add-legal x y lx ly
add-legal x (G.lim f) lx (st , lf) =
  (λ n → add-mono x (f (suc n)) (st n)) , (λ n → add-legal x (f n) lx (lf n))
add-legal x (G.lc () c t g) lx ly
add-legal x (G.em () a) lx ly
add-legal x G.top lx ly = lx

numeral-step : ∀ n → Cp zero (copies one n) (copies one (suc n))
numeral-step zero = inj₂ (inj₁ refl)
numeral-step (suc n) = add-mono one (copies one (suc n)) (numeral-step n)

numeral-legal : ∀ n → Lgl zero (copies one n)
numeral-legal zero = tt
numeral-legal (suc n) = add-legal one (copies one n) tt (numeral-legal n)

ω-legal : Lgl zero (successor one)
ω-legal = numeral-step , numeral-legal

ω-positive : Dn zero G.zero (successor one)
ω-positive = zero , inj₁ refl

-- 常值极限的被迫值 lim (ω, ω, …): 合法, 为正.
cst-value-legal : Lgl zero (G.lim (λ n → successor one))
cst-value-legal = (λ n → inj₁ refl) , (λ n → ω-legal)

cst-value-positive : Dn zero G.zero (G.lim (λ n → successor one))
cst-value-positive = zero , inj₂ ω-positive

-- coord 的被迫值 (lim (ω, ω, …)) · ω: 合法.
times-ω-step : ∀ y → Cp zero G.zero y → ∀ n → Cp zero (copies y n) (copies y (suc n))
times-ω-step y p zero = p
times-ω-step y p (suc n) = add-mono y (copies y (suc n)) (times-ω-step y p n)

times-ω-legal : ∀ y → Lgl zero y → Cp zero G.zero y → Lgl zero (successor y)
times-ω-legal y l p = times-ω-step y p , lawful
  where
  lawful : ∀ n → Lgl zero (copies y n)
  lawful zero = tt
  lawful (suc n) = add-legal y (copies y n) l (lawful n)

coord-value-legal : Lgl zero (successor (G.lim (λ n → successor one)))
coord-value-legal = times-ω-legal (G.lim (λ n → successor one))
  cst-value-legal (inj₂ cst-value-positive)

-- 链的第二点 1 + ω: 带相关守卫 (所以它的读回也被迫在定义域里), 且严格在起点之上.
second-guard : Gd zero one (one +ʳ successor one)
second-guard = inj₂ (zero , inj₁ refl) ,
  add-legal one (successor one) tt ω-legal ,
  raw0-Nested (one +ʳ successor one)

second-grow : Dn zero one (one +ʳ successor one)
second-grow = zero , inj₁ refl

module ForcedChain (F : FoldRows) where
  open FoldRows F
  open Forced F

  dom-second : Dom (read0 (one +ʳ successor one))
  dom-second = forced (one +ʳ successor one) second-guard
```

## 结论与范围

| 档 | 结果 |
|---|---|
| 编译定理 | `ψ-certificate-irr`、`out-evidence-irr`：输出与子折叠不依赖证书、结点证据、守卫（`refl`），对任何实例 |
| 编译定理 | `next-irr`、`chain-irr`、`gt-pointwise-irr`：`next` 与整条链逐点不依赖 `w`、`b`、定义域证据 |
| 编译定理 | `gt-function-required`：gt 行推出两份证明下的极限体作为函数相等（必要条件；`next` 不看证明时为 `refl`） |
| 编译定理 | `Forced.forced`、`ψ-one`、`ψ-cst`、`ψ-coord`、`second-coordinate`：被迫的定义域成员与被迫的值 |
| 有限检查 | `cst-value-legal`、`cst-value-positive`、`coord-value-legal`、`second-guard`、`second-grow`：在两个退化坐标与链的头一步上，接口索要的类型有闭居民 |
| 未找到 | `FoldRows → ⊥`；`FoldRows → WLPO`（不带 Funext）；带 Funext 的版本也没有找到，所以没有 "条件" 文件 |

**第 1 项的搜索范围（明确列出；范围之外没有结论）。**

1. 被迫对象上逐字段核对（纸面，逐条对照定义）：`zero-row`、`suc-row`、`lim-row` 与 `fold-legal`、
   `fold-positive`、`position` 在零、后继、极限、常值极限、常值极限的后继上相容；
   `next-additive`、`next-grow`、`gt-row`、`fold-legal`、`position` 在规范 Ω₁ 上相容
   （链 ηₙ₊₁ = ηₙ + ψ(读回 ηₙ)，ψ 的零行给 1，所以每步严格增长）。其中 §3 的几条写成了闭项。
2. `next-grow` 对一切链点量化，包括守卫只是无关的点。核对过：`Dn η (η + y)` 对一切非零的 `y`
   有不看证明的居民，`y` 为零的情形由无关的正性排除，所以这一字段不要求相关的守卫。
3. 找两条行对同一棵树给出不同值：没有。行按构造子分，一棵树只有一个构造子形式。
4. 仿 `YiWallConditional` 找空守卫域或 "逐点相等而字面不等" 的两棵结点：
   新块里守卫域不空（`RR5IrrCheck.all-guard-nonempty`），被迫对象里只有 Ω₁ 一个结点，没有找到。
5. 仿 `certificate-coherence-required` 找迫使跨证明字面相等、而相等又不可得的字段：
   得到的是 `gt-function-required`，它可由 `refl` 满足。
6. 找迫使从无关证据取出数据的字段：被迫对象的守卫都由 `dom-branch` 以相关参数给出，没有找到。
   定义域放宽后这一条成立，见 [YiIrrNegWide](YiIrrNegWide.lagda.md)。

**可满足性。** 本篇的 "未找到" 本身不等于 "已证明可满足"。编译的实例在
[YiIrrNegModel](YiIrrNegModel.lagda.md)（定义域 `Only0 × Legal × Low0`）；有了它，上面的搜索不必再扩大。

**关于接口的一处备注（不是错误）。** `next`、`out` 与各行把 `w`、`b` 写成相关参数。
`next-irr` 说明这份相关性没有内容；把 `next` 的 `w`、`b` 标成无关参数，接口的强弱不变，
`gt-function-required` 则直接成为 `refl`。行里的 `w`、`b` 保持相关是合适的：
它使各行只对交得出相关证据的结点提要求。

没有 Funext，没有公设，没有洞。没有序数值，强度没有变化。

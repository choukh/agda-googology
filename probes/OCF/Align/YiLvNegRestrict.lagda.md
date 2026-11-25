# YiLvNeg 第 4 项：证书沿第一位置路径的限制与一致

**判决：编译定理 (正面为主)，不用函数外延。** 限制 `restrict` 就是取路径所指的那份子证书。第 0 层的加法、`copies`、`successor`、加法链的输出证书都一致 (`Coh`)；
目标层 0 的折叠满足限制形式的位置保持 (`ψ-legal-restrict`，无前提)，输出证书在一致的定义域证书上一致 (`ψ-legal-coh`)，规范 Ω₁ 满足前提 (`Ω₁-legal-coh`)。
反面：同一个值的两份独立证书各自一致却不相等 (`independent-differ`)，折叠的合法性引理把这个差别带到输出证书里 (`fold-legal-reads-certificate`)。
只做了目标层 0 (层号 0 的结点)；一般目标层没有折叠可检验。入口 [YiLvIf](YiLvIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvNegRestrict where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw0-Nested; tw)
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldBase
open import OCF.Align.YiIrrFold using (ψ; ψ-positive; ψ-legal; ψ-position)
open import OCF.Align.YiLvNegCert using (κ; κ-lgl; Kᶜ; zero≢one)
```

## 1 限制，与加法

`restrict p l`：`a` 是 `b` 的第一位置，`l` 是 `b` 的合法性，取出 `a` 的那一份。它就是 `YiIrrFoldBase.lgl-cp₀`。
`add-weak` 是 `x ⊲ x + y` (极限处取第 0 项)；`add-cp` 是加法对第二个加数保持第一位置。两条路径上的限制都算得出来。

```agda
restrict : ∀ {a b} → Cp zero a b → Lgl zero b → Lgl zero a
restrict = lgl-cp₀

add-weak : ∀ x y → Cp zero x (x +ʳ y)
add-weak x G.zero = inj₁ refl
add-weak x (G.suc y) = inj₂ (add-weak x y)
add-weak x (G.lim f) = inj₂ (zero , add-weak x (f zero))
add-weak x (G.lc () c t g)
add-weak x (G.em () a)
add-weak x G.top = inj₂ (inj₁ refl)

restrict-add-weak : ∀ x y (lx : Lgl zero x) (ly : Lgl zero y) →
  restrict (add-weak x y) (add-legal x y lx ly) ≡ lx
restrict-add-weak x G.zero lx ly = refl
restrict-add-weak x (G.suc y) lx ly = restrict-add-weak x y lx ly
restrict-add-weak x (G.lim f) lx (st , lf) = restrict-add-weak x (f zero) lx (lf zero)
restrict-add-weak x (G.lc () c t g) lx ly
restrict-add-weak x (G.em () a) lx ly
restrict-add-weak x G.top lx ly = refl

restrict-add : ∀ x {a} b (p : Cp zero a b) (lx : Lgl zero x) (lb : Lgl zero b) →
  restrict (add-cp x p) (add-legal x b lx lb) ≡ add-legal x a lx (restrict p lb)
restrict-add-dn : ∀ x {a} b (p : Dn zero a b) (lx : Lgl zero x) (lb : Lgl zero b) →
  lgl-dn₀ (x +ʳ b) (add-dn x b p) (add-legal x b lx lb) ≡ add-legal x a lx (lgl-dn₀ b p lb)
restrict-add x b (inj₁ refl) lx lb = refl
restrict-add x b (inj₂ p) lx lb = restrict-add-dn x b p lx lb
restrict-add-dn x (G.suc b) p lx lb = restrict-add x b p lx lb
restrict-add-dn x (G.lim f) (n , p) lx (st , lf) = restrict-add x (f n) p lx (lf n)
restrict-add-dn x (G.lc () c t g) p lx lb
restrict-add-dn x (G.em () T) p lx lb
restrict-add-dn x G.top () lx lb
```

## 2 一致的证书

`Coh a l`：极限处，第 `n+1` 项的证书沿第 `n` 步限制下来，等于第 `n` 项的证书；各项遗传。这是逐项的相等，不是函数相等。

```agda
Coh : ∀ a → Lgl zero a → Set
Coh G.zero l = ⊤
Coh (G.suc a) l = Coh a l
Coh (G.lim f) (st , lf) =
  (∀ n → restrict (st n) (lf (suc n)) ≡ lf n) × (∀ n → Coh (f n) (lf n))
Coh (G.lc () c t g) l
Coh (G.em () a) l
Coh G.top l = ⊤

add-coh : ∀ x y (lx : Lgl zero x) (ly : Lgl zero y) →
  Coh x lx → Coh y ly → Coh (x +ʳ y) (add-legal x y lx ly)
add-coh x G.zero lx ly cx cy = cx
add-coh x (G.suc y) lx ly cx cy = add-coh x y lx ly cx cy
add-coh x (G.lim f) lx (st , lf) cx (cs , cf) =
  (λ n → trans (restrict-add x (f (suc n)) (st n) lx (lf (suc n)))
    (cong (add-legal x (f n) lx) (cs n))) ,
  (λ n → add-coh x (f n) lx (lf n) cx (cf n))
add-coh x (G.lc () c t g) lx ly cx cy
add-coh x (G.em () a) lx ly cx cy
add-coh x G.top lx ly cx cy = cx

copies-restrict : ∀ x (p : Cp zero G.zero x) (lx : Lgl zero x) n →
  restrict (copies-step x p n) (copies-legal x lx (suc n)) ≡ copies-legal x lx n
copies-restrict x p lx zero = refl
copies-restrict x p lx (suc n) =
  trans (restrict-add x (copies x (suc n)) (copies-step x p n) lx (copies-legal x lx (suc n)))
    (cong (add-legal x (copies x n) lx) (copies-restrict x p lx n))

copies-coh : ∀ x (lx : Lgl zero x) → Coh x lx → ∀ n → Coh (copies x n) (copies-legal x lx n)
copies-coh x lx cx zero = tt
copies-coh x lx cx (suc n) =
  add-coh x (copies x n) lx (copies-legal x lx n) cx (copies-coh x lx cx n)

successor-coh : ∀ x (p : Cp zero G.zero x) (lx : Lgl zero x) → Coh x lx →
  Coh (successor x) (copies-step x p , copies-legal x lx)
successor-coh x p lx cx = copies-restrict x p lx , copies-coh x lx cx
```

## 3 反面：两份独立的证书

[YiLvNegCert](YiLvNegCert.lagda.md) 的坐标 `κ` 有两份合法性证书，第 0 步选了不同的下标。两份各自一致，但不相等。
所以一致只约束一份证书的内部，不给出 "证书唯一"。

```agda
κ-coh : ∀ j → Coh κ (κ-lgl j)
κ-coh j =
  (λ { zero → refl ; (suc n) → refl }) ,
  (λ { zero → tt ; (suc n) → (λ _ → refl) , (λ _ → tt) })

choice : Lgl zero κ → ℕ
choice (st , lf) with st zero
... | inj₁ e = zero
... | inj₂ (inj₁ e) = zero
... | inj₂ (inj₂ (m , q)) = m

independent-differ : κ-lgl 0 ≡ κ-lgl 1 → ⊥
independent-differ e = zero≢one (cong choice e)
```

## 4 目标层 0 的折叠：限制形式的位置保持

`restrictDom`：定义域证书沿字面第一位置路径的限制，递归的走法与 `YiIrrFold.ψ-position` 相同
(Ω 结点处经第一支接到下界自身那一支)。`ψ-legal-restrict`：大树的输出证书沿位置保持给出的路径限制下来，
正是小树在限制后的证书下的输出证书。没有前提，不用函数外延。

```agda
restrictDom : ∀ {x} y → CP x y → Dom y → Dom x
restrictDom y self d = d
restrictDom (suc y) (suc p) d = restrictDom y p (dom-pred y d)
restrictDom (lim f) (lim n p) d = restrictDom (f n) p (dom-at f d n)
restrictDom (lc zero c w b t g) (fst p) d =
  restrictDom (g c (dom-seed c w b t g d))
    (CP-tr p (dom-first c w b t g d c (dom-seed c w b t g d)))
    (dom-branch c w b t g d c (dom-seed c w b t g d))
restrictDom (lc (suc k) c w b t g) (fst p) d = ⊥-elim (proj₁ d)
restrictDom (lc (lim f) c w b t g) (fst p) d = ⊥-elim (proj₁ d)
restrictDom (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) (fst p) d = ⊥-elim (proj₁ d)

ψ-legal-restrict : ∀ x y (dx : Dom x) (dy : Dom y) (p : CP x y) →
  restrict (ψ-position x y dx dy p) (ψ-legal y dy) ≡ ψ-legal x (restrictDom y p dy)
ψ-legal-restrict .zero zero dx dy self = refl
ψ-legal-restrict .(suc y) (suc y) dx dy self = refl
ψ-legal-restrict x (suc y) dx dy (suc p) = ψ-legal-restrict x y dx (dom-pred y dy) p
ψ-legal-restrict .(lim f) (lim f) dx dy self = refl
ψ-legal-restrict x (lim f) dx dy (lim n p) =
  ψ-legal-restrict x (f n) dx (dom-at f dy n) p
ψ-legal-restrict .(lc k c w b t g) (lc k c w b t g) dx dy self = refl
ψ-legal-restrict x (lc zero c w b t g) dx dy (fst p) =
  ψ-legal-restrict x (g c (dom-seed c w b t g dy)) dx
    (dom-branch c w b t g dy c (dom-seed c w b t g dy))
    (CP-tr p (dom-first c w b t g dy c (dom-seed c w b t g dy)))
ψ-legal-restrict x (lc (suc k) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ-legal-restrict x (lc (lim f) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
ψ-legal-restrict x (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) dx dy (fst p) = ⊥-elim (proj₁ dy)
```

## 5 加法链与折叠的输出证书一致

`ChainCoh`：`ChainLegal.collapse-legal` 的输出证书。前提 `natural` 是分支引理沿守卫的限制 (只对 "守卫的合法性互为限制" 的一对守卫要求)；
链上相邻两点的守卫满足这个条件 (`guard-step`，由 §1 的加法引理)，所以输出证书的顶层一致。

```agda
module ChainCoh (c : R) (body : (η : R) → .(Gd zero c η) → R)
  (lawful : ∀ η (e : Gd zero c η) → Lgl zero (body η e))
  (positive : ∀ η .(e : Gd zero c η) → Dn zero G.zero (body η e))
  (monotone : ∀ η (e : Gd zero c η) η′ (e′ : Gd zero c η′) →
    Gd zero η η′ → Cp zero (body η e) (body η′ e′))
  (p₀ : Point c) (e₀ : Gd zero c (coordinate p₀))
  (natural : ∀ η (e : Gd zero c η) η′ (e′ : Gd zero c η′) (q : Gd zero η η′) →
    restrict (proj₁ q) (proj₁ (proj₂ e′)) ≡ proj₁ (proj₂ e) →
    restrict (monotone η e η′ e′ q) (lawful η′ e′) ≡ lawful η e)
  (lawful-coh : ∀ η (e : Gd zero c η) → Coh η (proj₁ (proj₂ e)) → Coh (body η e) (lawful η e))
  (coh₀ : Coh (coordinate p₀) (proj₁ (proj₂ e₀))) where

  open Chain c body lawful positive
  open ChainLegal c body lawful positive monotone p₀ e₀

  guard-step : ∀ n →
    restrict (inj₂ (grow (points n))) (proj₁ (proj₂ (guards (suc n)))) ≡ proj₁ (proj₂ (guards n))
  guard-step n = restrict-add (coordinate (points n)) {a = G.zero} (out (points n))
    (inj₂ (positive (coordinate (points n)) (guards n)))
    (proj₁ (proj₂ (guards n))) (lawful (coordinate (points n)) (guards n))

  collapse-coherent : ∀ n →
    restrict (step n) (lawful (coordinate (points (suc n))) (guards (suc n))) ≡
    lawful (coordinate (points n)) (guards n)
  collapse-coherent n = natural (coordinate (points n)) (guards n)
    (coordinate (points (suc n))) (guards (suc n))
    (inj₂ (grow (points n)) , proj₂ (guards (suc n))) (guard-step n)

  guards-coh : ∀ n → Coh (coordinate (points n)) (proj₁ (proj₂ (guards n)))
  guards-coh zero = coh₀
  guards-coh (suc n) = add-coh (coordinate (points n)) (out (points n))
    (proj₁ (proj₂ (guards n))) (lawful (coordinate (points n)) (guards n))
    (guards-coh n) (lawful-coh (coordinate (points n)) (guards n) (guards-coh n))

  collapse-coh : Coh (collapse p₀) collapse-legal
  collapse-coh = collapse-coherent ,
    (λ n → lawful-coh (coordinate (points n)) (guards n) (guards-coh n))
```

`CohDom x d`：定义域证书 `d` 自身一致。极限处相邻两项的证书互为限制；Ω 结点处下界的证书一致，
分支的证书沿 `Legal.dir` 的路径互为限制 (只对合法性互为限制的一对守卫)，分支遗传 (只对一致的守卫)。

```agda
CohDom : ∀ x → Dom x → Set
CohDom zero d = ⊤
CohDom (suc x) d = CohDom x (dom-pred x d)
CohDom (lim f) d =
  (∀ n → restrictDom (f (suc n)) (proj₁ (proj₁ (proj₂ d)) n) (dom-at f d (suc n)) ≡
     dom-at f d n) ×
  (∀ n → CohDom (f n) (dom-at f d n))
CohDom (lc zero c w b t g) d =
  Coh c (proj₁ (proj₂ (dom-seed c w b t g d))) ×
  (∀ η (e : Gd zero c η) η′ (e′ : Gd zero c η′) (q : Gd zero η η′) →
     restrict (proj₁ q) (proj₁ (proj₂ e′)) ≡ proj₁ (proj₂ e) →
     restrictDom (g η′ e′) (dom-directed c w b t g d η e η′ e′ q)
       (dom-branch c w b t g d η′ e′) ≡ dom-branch c w b t g d η e) ×
  (∀ η (e : Gd zero c η) → Coh η (proj₁ (proj₂ e)) →
     CohDom (g η e) (dom-branch c w b t g d η e))
CohDom (lc (suc k) c w b t g) d = ⊤
CohDom (lc (lim f) c w b t g) d = ⊤
CohDom (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = ⊤

ψ-legal-coh : ∀ x (d : Dom x) → CohDom x d → Coh (ψ x d) (ψ-legal x d)
ψ-legal-coh zero d cd = tt
ψ-legal-coh (suc x) d cd =
  successor-coh (ψ x d) (inj₂ (ψ-positive x d)) (ψ-legal x d) (ψ-legal-coh x d cd)
ψ-legal-coh (lim f) d (cs , cf) =
  (λ n → trans
    (ψ-legal-restrict (f n) (f (suc n)) (dom-at f d n) (dom-at f d (suc n))
      (proj₁ (proj₁ (proj₂ d)) n))
    (cong {B = Lgl zero (ψ (f n) (dom-at f d n))} (λ z → ψ-legal (f n) z) (cs n))) ,
  (λ n → ψ-legal-coh (f n) (dom-at f d n) (cf n))
ψ-legal-coh (lc zero c w b t g) d (c₀ , chain , deep) =
  ChainCoh.collapse-coh c
    (λ η e → ψ (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-legal (g η e) (dom-branch c w b t g d η e))
    (λ η e → ψ-positive (g η e) (dom-branch c w b t g d η e))
    (λ η e η′ e′ q → ψ-position (g η e) (g η′ e′)
      (dom-branch c w b t g d η e) (dom-branch c w b t g d η′ e′)
      (dom-directed c w b t g d η e η′ e′ q))
    (start c w b) (dom-seed c w b t g d)
    (λ η e η′ e′ q compat → trans
      (ψ-legal-restrict (g η e) (g η′ e′)
        (dom-branch c w b t g d η e) (dom-branch c w b t g d η′ e′)
        (dom-directed c w b t g d η e η′ e′ q))
      (cong {B = Lgl zero (ψ (g η e) (dom-branch c w b t g d η e))}
        (λ z → ψ-legal (g η e) z) (chain η e η′ e′ q compat)))
    (λ η e ce → ψ-legal-coh (g η e) (dom-branch c w b t g d η e) (deep η e ce))
    c₀
ψ-legal-coh (lc (suc k) c w b t g) d cd = tt
ψ-legal-coh (lc (lim f) c w b t g) d cd = tt
ψ-legal-coh (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d cd = tt
```

## 6 规范 Ω₁ 满足前提

读回与限制可交换 (`restrictDom-read0`)，所以一致的坐标证书读成一致的定义域证书；`tw 2` 的分支就是读回。

```agda
restrictDom-read0 : ∀ {a} b (p : Cp zero a b) (l : Lgl zero b) →
  restrictDom (read0 b) (read0-cp b p) (read0-dom b l) ≡ read0-dom a (restrict p l)
restrictDom-read0-dn : ∀ {a} b (p : Dn zero a b) (l : Lgl zero b) →
  restrictDom (read0 b) (read0-dn b p) (read0-dom b l) ≡ read0-dom a (lgl-dn₀ b p l)
restrictDom-read0 b (inj₁ refl) l = refl
restrictDom-read0 b (inj₂ p) l = restrictDom-read0-dn b p l
restrictDom-read0-dn (G.suc b) p l = restrictDom-read0 b p l
restrictDom-read0-dn (G.lim f) (n , p) (st , lf) = restrictDom-read0 (f n) p (lf n)
restrictDom-read0-dn (G.lc () c t g) p l
restrictDom-read0-dn (G.em () T) p l
restrictDom-read0-dn G.top () l

read0-cohdom : ∀ a (l : Lgl zero a) → Coh a l → CohDom (read0 a) (read0-dom a l)
read0-cohdom G.zero l ch = tt
read0-cohdom (G.suc a) l ch = read0-cohdom a l ch
read0-cohdom (G.lim f) (st , lf) (cs , cf) =
  (λ n → trans (restrictDom-read0 (f (suc n)) (st n) (lf (suc n)))
    (cong (read0-dom (f n)) (cs n))) ,
  (λ n → read0-cohdom (f n) (lf n) (cf n))
read0-cohdom (G.lc () c t g) l ch
read0-cohdom (G.em () T) l ch
read0-cohdom G.top l ch = tt

Ω₁-cohdom : CohDom (tw 2) dom-Ω₁
Ω₁-cohdom =
  tt ,
  (λ η e η′ e′ q compat → trans
    (restrictDom-read0 η′ (proj₁ q) (proj₁ (proj₂ e′)))
    (cong (read0-dom η) compat)) ,
  (λ η e ce → read0-cohdom η (proj₁ (proj₂ e)) ce)

Ω₁-legal-coh : Coh (ψ (tw 2) dom-Ω₁) (ψ-legal (tw 2) dom-Ω₁)
Ω₁-legal-coh = ψ-legal-coh (tw 2) dom-Ω₁ Ω₁-cohdom
```

层号一侧的同一件事：`Legal` 沿字面第一位置的限制 `restrictL`，以及一致的坐标证书读成一致的层号证书。
乙线里被比较的层号都是坐标的读回，所以 `YiLvIf.compare` 读的路径数据来自这样的证书。

```agda
restrictL : ∀ {a} y → CP a y → Legal y → Legal a
restrictL y self L = L
restrictL (suc y) (suc p) L = restrictL y p L
restrictL (lim f) (lim n p) (st , lg) = restrictL (f n) p (lg n)
restrictL (lc k c w b t g) (fst p) (Lk , tg , dir , irr , Lt , Lg) = restrictL t p Lt

CohL : ∀ a → Legal (read0 a) → Set
CohL G.zero L = ⊤
CohL (G.suc a) L = CohL a L
CohL (G.lim f) (st , lg) =
  (∀ n → restrictL (read0 (f (suc n))) (st n) (lg (suc n)) ≡ lg n) × (∀ n → CohL (f n) (lg n))
CohL (G.lc () c t g) L
CohL (G.em () T) L
CohL G.top L = ⊤

restrictL-read0 : ∀ {a} b (p : Cp zero a b) (l : Lgl zero b) →
  restrictL (read0 b) (read0-cp b p) (read0-legal b l) ≡ read0-legal a (restrict p l)
restrictL-read0-dn : ∀ {a} b (p : Dn zero a b) (l : Lgl zero b) →
  restrictL (read0 b) (read0-dn b p) (read0-legal b l) ≡ read0-legal a (lgl-dn₀ b p l)
restrictL-read0 b (inj₁ refl) l = refl
restrictL-read0 b (inj₂ p) l = restrictL-read0-dn b p l
restrictL-read0-dn (G.suc b) p l = restrictL-read0 b p l
restrictL-read0-dn (G.lim f) (n , p) (st , lf) = restrictL-read0 (f n) p (lf n)
restrictL-read0-dn (G.lc () c t g) p l
restrictL-read0-dn (G.em () T) p l
restrictL-read0-dn G.top () l

read0-legal-coh : ∀ a (l : Lgl zero a) → Coh a l → CohL a (read0-legal a l)
read0-legal-coh G.zero l ch = tt
read0-legal-coh (G.suc a) l ch = read0-legal-coh a l ch
read0-legal-coh (G.lim f) (st , lf) (cs , cf) =
  (λ n → trans (restrictL-read0 (f (suc n)) (st n) (lf (suc n)))
    (cong (read0-legal (f n)) (cs n))) ,
  (λ n → read0-legal-coh (f n) (lf n) (cf n))
read0-legal-coh (G.lc () c t g) l ch
read0-legal-coh (G.em () T) l ch
read0-legal-coh G.top l ch = tt
```

## 7 反面：折叠的合法性引理读证书

层号 `Kᶜ = read0 κ` 在 `Dom` 里有两份证书 (来自 `κ` 的两份合法性)。`ψ` 的输出与证书无关 (`refl`)，
但 `ψ-legal` 给出的两份输出证书不相等：极限行的第 0 步是位置保持算出的路径，它照抄了证书里选的下标。
所以合法性若作数据沿链传，传下去的数据依赖证书；能证的是 §4, §5 的限制形式，不是 "两份独立证书给出相等的输出证书"。

```agda
Kᶜ-dom : ℕ → Dom Kᶜ
Kᶜ-dom j = read0-dom κ (κ-lgl j)

same-output : ψ Kᶜ (Kᶜ-dom 0) ≡ ψ Kᶜ (Kᶜ-dom 1)
same-output = refl

trace : Lgl zero (ψ Kᶜ (Kᶜ-dom 0)) → ℕ
trace (st , lf) with st zero
... | inj₁ e = zero
... | inj₂ (zero , q) = zero
... | inj₂ (suc (suc n) , q) = zero
... | inj₂ (suc zero , inj₁ e) = zero
... | inj₂ (suc zero , inj₂ (m , q)) = m

fold-legal-reads-certificate : ψ-legal Kᶜ (Kᶜ-dom 0) ≡ ψ-legal Kᶜ (Kᶜ-dom 1) → ⊥
fold-legal-reads-certificate e = zero≢one (cong trace e)
```

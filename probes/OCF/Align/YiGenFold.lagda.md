# YiGenFold：`Raw (tw 2)` 上对派发与定义域参数化的折叠

**判决 (编译定理，一步定理)：给了一个对折叠的调用封闭的定义域与其上的派发 (`Disp`)，目标为第 0 层或某一支里一个位置的折叠 `Ψᶠ` 写得出、合法、保持第一位置；
结点处 "不多保留" 无条件成立，"派发完全" 归结为派发在这一个结点上完全 (`honest`)。** 分支槽位上的结点的链由目标在那个位置上的折叠推进，折的是整个分支。
`top` 在分支目标下的行也是参数 (`topᴮ`)；定义域里没有嵌入的孩子。没有值。实例在 [YiGenFoldFin](YiGenFoldFin.lagda.md)，对归一链的约化在 [YiGenFoldGap](YiGenFoldGap.lagda.md)，接口 [YiGenIf](YiGenIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested; cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (R; read0)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (Plain; lev; lev-plain; Tri; below; above; same; Kept)
open import OCF.Align.YiLvFoldAdd using (Pos; successor; copies-step; copies-legal; copies-nested)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold; cO-pos)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawIf using (IsLim; way-sound)
open import OCF.Align.YiRawFoldBase
  using (NdR; NdL; nd; seedL; Ψn; ΨN; Ψn-pos; ΨN-pos; Ψn-legal; ΨN-legal;
         Ψn-nested; ΨN-nested; Ψn-dn; ΨN-dn; Ψn-kept; ΨN-kept; Ψn-lim; ΨN-lim)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ; T₃ᵐ-legal)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; br)
open import OCF.Align.YiOmFoldBase using (RΩ; rplain)
open import OCF.Align.YiGenIf using (OwnFold; Honest)
```

## 1 目标，结点自己那一层，调用的闭包

目标是第 0 层或某一支里的一个位置 (带相关的守卫)。主干上两个位置的层号是 0，那里的结点自己那一层的折叠就是目标第 0 层的折叠 (`own`)。
`Ask τ₀ ξ₀ τ ξ`：从 "把 `ξ₀` 折到 `τ₀`" 出发，折叠的行逐步调用到 "把 `ξ` 折到 `τ`"。结点处调用三样：第一支、各支在同一目标下、各支在结点自己那一层下。
分支函数是全函数，所以后两样对一切带守卫的坐标都算调用；这是行的合法性要的范围，比链实际走到的可数个坐标宽。

```agda
data Tg : Set where
  base : Tg
  at : (η : R) (e : Gd zero raw1 η) (r : Pre (read0 η)) → Tg

tl : Tg → LF
tl base = zero
tl (at η e r) = lev (read0 η) r

tl-plain : ∀ τ → Plain (tl τ)
tl-plain base = tt
tl-plain (at η e r) = lev-plain (read0 η) (rplain η) r

posT : Tg → Pre K₂ω
posT base = root₂
posT (at η e r) = br η e r

own : Pre K₂ω → Tg
own (inj₁ (inj₁ _)) = base
own (inj₂ (inj₁ (inj₁ _))) = base
own (inj₂ (inj₂ (η , e , r))) = at η e r
own (inj₁ (inj₂ ()))
own (inj₂ (inj₁ (inj₂ ())))

data Ask (τ₀ : Tg) (ξ₀ : RΩ) : Tg → RΩ → Set where
  here : Ask τ₀ ξ₀ τ₀ ξ₀
  pred : ∀ {τ a} → Ask τ₀ ξ₀ τ (G.suc a) → Ask τ₀ ξ₀ τ a
  term : ∀ {τ f} → Ask τ₀ ξ₀ τ (G.lim f) → ∀ n → Ask τ₀ ξ₀ τ (f n)
  first : ∀ {τ p c t g} → Ask τ₀ ξ₀ τ (G.lc p c t g) → Ask τ₀ ξ₀ τ t
  obs : ∀ {τ p c t g} → Ask τ₀ ξ₀ τ (G.lc p c t g) →
    ∀ ζ (e : GdL K₂ω p c ζ) → Ask τ₀ ξ₀ τ (g ζ e)
  drive : ∀ {τ p c t g} → Ask τ₀ ξ₀ τ (G.lc p c t g) →
    ∀ ζ (e : GdL K₂ω p c ζ) → Ask τ₀ ξ₀ (own p) (g ζ e)
```

## 2 `top` 的行

目标第 0 层：上一轮 `tw 3` 的闭项 `T₃ᵐ` (行不改)。目标在第 `η` 支的位置 `r` 上：层号里有层号 0 的槽位 `s` 时根保留在 `s` 上，行由 `mk s z` 给；层号就是 0 时与目标第 0 层相同 (`topTri`)。
`mk` 的取法在 [YiGenFoldDom](YiGenFoldDom.lagda.md) (`rowᶠ`)。接口对 `top` 不作要求。

```agda
topTri : ∀ j → Tri zero j → ((s : Pre j) → lev j s ≡ zero → Raw j) → Raw j
topTri j (below () q) mk
topTri j (above s z) mk = mk s z
topTri .zero (same refl) mk = T₃ᵐ

topTri-ind : (P : ∀ j → Raw j → Set) → P zero T₃ᵐ → ∀ j (x : Tri zero j) mk →
  (∀ s z → P j (mk s z)) → P j (topTri j x mk)
topTri-ind P p₀ j (below () q) mk h
topTri-ind P p₀ j (above s z) mk h = h s z
topTri-ind P p₀ .zero (same refl) mk h = p₀
```

## 3 派发的数据

`Dom τ ξ`：允许 "把 `ξ` 折到 `τ`"。它对 §1 的五种调用封闭，不含嵌入的孩子；折叠只无关地用它。`way`：结点处的派发，可以读这份 (无关的) 证据。`topᴮ`：`top` 在分支目标下的行，带合法、嵌套、头为正。
派发任意时输出都合法；携带强度的是 §5 的完全性。

```agda
record Disp : Set₁ where
  field
    Dom : Tg → RΩ → Set
    d-pred : ∀ {τ a} → Dom τ (G.suc a) → Dom τ a
    d-term : ∀ {τ f} → Dom τ (G.lim f) → ∀ n → Dom τ (f n)
    d-first : ∀ {τ} p c t g → Dom τ (G.lc p c t g) → Dom τ t
    d-obs : ∀ {τ} p c t g → Dom τ (G.lc p c t g) →
      ∀ ζ (e : GdL K₂ω p c ζ) → Dom τ (g ζ e)
    d-drive : ∀ {τ} p c t g → Dom τ (G.lc p c t g) →
      ∀ ζ (e : GdL K₂ω p c ζ) → Dom (own p) (g ζ e)
    d-em : ∀ {τ} i a → Dom τ (G.em i a) → ⊥
    way : ∀ τ p c t g → .(Dom τ (G.lc p c t g)) → Way (tl τ) (lev K₂ω p)
    topᴮ : ∀ η (e : Gd zero raw1 η) (r : Pre (read0 η)) → Raw (lev (read0 η) r)
    topᴮ-legal : ∀ η e r → Lgl (lev (read0 η) r) (topᴮ η e r)
    topᴮ-nested : ∀ η e r → Nested (lev (read0 η) r) (topᴮ η e r)
    topᴮ-pos : ∀ η e r → Pos (lev (read0 η) r) (topᴮ η e r)
```

## 4 折叠

对树递归；目标在链行里换成结点自己那一层 (`own`)。主干上的结点取 `YiRawFoldBase.Ψn` 的两行，层号 0；第 `η` 支的位置 `r` 上的结点取 `ΨN`，公共上界 `read0 η`。
分支结点的 `gk` 是目标 `at η e r` 的折叠在**整个分支** `g ζ` 上的值，不去掉前缀。

```agda
module Fold (X : Disp) where
  open Disp X

  Ψᶠ : (τ : Tg) (ξ : RΩ) → .(Dom τ ξ) → .(Lgl K₂ω ξ) → .(Nested K₂ω ξ) → Raw (tl τ)
  ndT : (τ : Tg) (c : R) → .(Lgl zero c) → .(Nested zero c) → Raw (tl τ) →
    (g : (η : R) → .(Gd zero c η) → RΩ) →
    .(∀ η (e : Gd zero c η) → Dom τ (g η e)) →
    .(∀ η (e : Gd zero c η) → Dom base (g η e)) →
    .(∀ η (e : Gd zero c η) → Lgl K₂ω (g η e)) →
    .(∀ η (e : Gd zero c η) → Nested K₂ω (g η e)) → NdR (tl τ) zero
  ndB : (τ : Tg) (η : R) (e : Gd zero raw1 η) (r : Pre (read0 η)) (c : Low (read0 η) r) →
    .(LglLow (read0 η) r c) → .(NestedLow (read0 η) r c) → Raw (tl τ) →
    (g : (ζ : Low (read0 η) r) → .(GdL (read0 η) r c ζ) → RΩ) →
    .(∀ ζ (e′ : GdL (read0 η) r c ζ) → Dom τ (g ζ e′)) →
    .(∀ ζ (e′ : GdL (read0 η) r c ζ) → Dom (at η e r) (g ζ e′)) →
    .(∀ ζ (e′ : GdL (read0 η) r c ζ) → Lgl K₂ω (g ζ e′)) →
    .(∀ ζ (e′ : GdL (read0 η) r c ζ) → Nested K₂ω (g ζ e′)) → NdL (tl τ) (read0 η) r
  Ψᶠ-pos : ∀ τ ξ .(d : Dom τ ξ) .(l : Lgl K₂ω ξ) .(nb : Nested K₂ω ξ) →
    Pos (tl τ) (Ψᶠ τ ξ d l nb)
  Ψᶠ-legal : ∀ τ ξ (d : Dom τ ξ) (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ) →
    Lgl (tl τ) (Ψᶠ τ ξ d l nb)
  Ψᶠ-nested : ∀ τ ξ (d : Dom τ ξ) (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ) →
    Nested (tl τ) (Ψᶠ τ ξ d l nb)
  Ψᶠ-cp : ∀ τ {ξ} ξ′ (d : Dom τ ξ) (d′ : Dom τ ξ′) (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ)
    (l′ : Lgl K₂ω ξ′) (nb′ : Nested K₂ω ξ′) → Cp K₂ω ξ ξ′ →
    Cp (tl τ) (Ψᶠ τ ξ d l nb) (Ψᶠ τ ξ′ d′ l′ nb′)
  Ψᶠ-dn : ∀ τ {ξ} ξ′ (d : Dom τ ξ) (d′ : Dom τ ξ′) (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ)
    (l′ : Lgl K₂ω ξ′) (nb′ : Nested K₂ω ξ′) → Dn K₂ω ξ ξ′ →
    Dn (tl τ) (Ψᶠ τ ξ d l nb) (Ψᶠ τ ξ′ d′ l′ nb′)

  Ψᶠ τ G.zero d l nb = cO (tl τ)
  Ψᶠ τ (G.suc a) d l nb = successor (tl τ) (Ψᶠ τ a (d-pred d) l nb)
  Ψᶠ τ (G.lim f) d l nb = G.lim (λ n → Ψᶠ τ (f n) (d-term d n) (proj₂ l n) (nb n))
  Ψᶠ τ (G.lc (inj₁ (inj₁ u)) c t g) d l nb =
    Ψn (tl τ) zero tt (way τ (inj₁ (inj₁ u)) c t g d)
      (ndT τ c (proj₁ nb) (proj₁ (proj₂ nb))
        (Ψᶠ τ t (d-first (inj₁ (inj₁ u)) c t g d)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
        g (d-obs (inj₁ (inj₁ u)) c t g d) (d-drive (inj₁ (inj₁ u)) c t g d)
        (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
  Ψᶠ τ (G.lc (inj₂ (inj₁ (inj₁ u))) c t g) d l nb =
    Ψn (tl τ) zero tt (way τ (inj₂ (inj₁ (inj₁ u))) c t g d)
      (ndT τ c (proj₁ nb) (proj₁ (proj₂ nb))
        (Ψᶠ τ t (d-first (inj₂ (inj₁ (inj₁ u))) c t g d)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
        g (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d)
        (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
  Ψᶠ τ (G.lc (inj₂ (inj₂ (η , e , r))) c t g) d l nb =
    ΨN (tl τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d)
      (ndB τ η e r c (proj₁ nb) (proj₁ (proj₂ nb))
        (Ψᶠ τ t (d-first (br η e r) c t g d)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
        g (d-obs (br η e r) c t g d) (d-drive (br η e r) c t g d)
        (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
  Ψᶠ τ (G.em i a) d l nb = ⊥-elim-irr (d-em i a d)
  Ψᶠ base G.top d l nb = T₃ᵐ
  Ψᶠ (at η e r) G.top d l nb = topᴮ η e r

  ndT τ c lw nw t g dg dk lg ng = nd c lw nw t
    (λ η e → Ψᶠ τ (g η e) (dg η e) (lg η e) (ng η e))
    (λ η e → Ψᶠ base (g η e) (dk η e) (lg η e) (ng η e))
    (λ η e → Ψᶠ-legal base (g η e) (dk η e) (lg η e) (ng η e))
    (λ η e → raw0-Nested (Ψᶠ base (g η e) (dk η e) (lg η e) (ng η e)))
    (λ η e → Ψᶠ-pos base (g η e) (dk η e) (lg η e) (ng η e))

  ndB τ η e r c lw nw t g dg dk lg ng = nd c lw nw t
    (λ ζ e′ → Ψᶠ τ (g ζ e′) (dg ζ e′) (lg ζ e′) (ng ζ e′))
    (λ ζ e′ → Ψᶠ (at η e r) (g ζ e′) (dk ζ e′) (lg ζ e′) (ng ζ e′))
    (λ ζ e′ → Ψᶠ-legal (at η e r) (g ζ e′) (dk ζ e′) (lg ζ e′) (ng ζ e′))
    (λ ζ e′ → Ψᶠ-nested (at η e r) (g ζ e′) (dk ζ e′) (lg ζ e′) (ng ζ e′))
    (λ ζ e′ → Ψᶠ-pos (at η e r) (g ζ e′) (dk ζ e′) (lg ζ e′) (ng ζ e′))

  Ψᶠ-pos τ G.zero d l nb = cO-pos (tl τ)
  Ψᶠ-pos τ (G.suc a) d l nb = tt
  Ψᶠ-pos τ (G.lim f) d l nb = tt
  Ψᶠ-pos τ (G.lc (inj₁ (inj₁ u)) c t g) d l nb =
    Ψn-pos (tl τ) zero tt (way τ (inj₁ (inj₁ u)) c t g d)
      (ndT τ c (proj₁ nb) (proj₁ (proj₂ nb))
        (Ψᶠ τ t (d-first (inj₁ (inj₁ u)) c t g d)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
        g (d-obs (inj₁ (inj₁ u)) c t g d) (d-drive (inj₁ (inj₁ u)) c t g d)
        (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
  Ψᶠ-pos τ (G.lc (inj₂ (inj₁ (inj₁ u))) c t g) d l nb =
    Ψn-pos (tl τ) zero tt (way τ (inj₂ (inj₁ (inj₁ u))) c t g d)
      (ndT τ c (proj₁ nb) (proj₁ (proj₂ nb))
        (Ψᶠ τ t (d-first (inj₂ (inj₁ (inj₁ u))) c t g d)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
        g (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d)
        (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
  Ψᶠ-pos τ (G.lc (inj₂ (inj₂ (η , e , r))) c t g) d l nb =
    ΨN-pos (tl τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d)
      (ndB τ η e r c (proj₁ nb) (proj₁ (proj₂ nb))
        (Ψᶠ τ t (d-first (br η e r) c t g d)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
        g (d-obs (br η e r) c t g d) (d-drive (br η e r) c t g d)
        (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
  Ψᶠ-pos τ (G.em i a) d l nb = ⊥-elim-irr (d-em i a d)
  Ψᶠ-pos base G.top d l nb = tt
  Ψᶠ-pos (at η e r) G.top d l nb = topᴮ-pos η e r

  Ψᶠ-legal τ G.zero d l nb = cO-Lgl (tl τ)
  Ψᶠ-legal τ (G.suc a) d l nb =
    copies-step (tl τ) (tl-plain τ) (Ψᶠ τ a (d-pred d) l nb) ,
    copies-legal (tl τ) (tl-plain τ) (Ψᶠ τ a (d-pred d) l nb) (Ψᶠ-legal τ a (d-pred d) l nb)
  Ψᶠ-legal τ (G.lim f) d (st , lf) nb =
    (λ n → Ψᶠ-cp τ (f (suc n)) (d-term d n) (d-term d (suc n)) (lf n) (nb n)
      (lf (suc n)) (nb (suc n)) (st n)) ,
    (λ n → Ψᶠ-legal τ (f n) (d-term d n) (lf n) (nb n))
  Ψᶠ-legal τ (G.lc (inj₁ (inj₁ u)) c t g) d (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
    Ψn-legal (tl τ) zero tt (way τ (inj₁ (inj₁ u)) c t g d)
      (ndT τ c lw nw (Ψᶠ τ t (d-first (inj₁ (inj₁ u)) c t g d) lt nt)
        g (d-obs (inj₁ (inj₁ u)) c t g d) (d-drive (inj₁ (inj₁ u)) c t g d) lg ng)
      (record
        { seed = inj₁ refl , lw , nw
        ; tg = λ η e → Ψᶠ-cp τ (g η e) (d-first (inj₁ (inj₁ u)) c t g d)
            (d-obs (inj₁ (inj₁ u)) c t g d η e) lt nt (lg η e) (ng η e) (tg η e)
        ; dir = λ η e η′ e′ q → Ψᶠ-cp τ (g η′ e′) (d-obs (inj₁ (inj₁ u)) c t g d η e)
            (d-obs (inj₁ (inj₁ u)) c t g d η′ e′) (lg η e) (ng η e) (lg η′ e′) (ng η′ e′)
            (dir η e η′ e′ q)
        ; lt = Ψᶠ-legal τ t (d-first (inj₁ (inj₁ u)) c t g d) lt nt
        ; lg = λ η e → Ψᶠ-legal τ (g η e) (d-obs (inj₁ (inj₁ u)) c t g d η e) (lg η e) (ng η e)
        ; lkʳ = λ η e → Ψᶠ-legal base (g η e) (d-drive (inj₁ (inj₁ u)) c t g d η e)
            (lg η e) (ng η e)
        ; nkʳ = λ η e → raw0-Nested
            (Ψᶠ base (g η e) (d-drive (inj₁ (inj₁ u)) c t g d η e) (lg η e) (ng η e)) })
  Ψᶠ-legal τ (G.lc (inj₂ (inj₁ (inj₁ u))) c t g) d (tg , dir , irr , lt , lg)
    (lw , nw , nt , ng) =
    Ψn-legal (tl τ) zero tt (way τ (inj₂ (inj₁ (inj₁ u))) c t g d)
      (ndT τ c lw nw (Ψᶠ τ t (d-first (inj₂ (inj₁ (inj₁ u))) c t g d) lt nt)
        g (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d) lg ng)
      (record
        { seed = inj₁ refl , lw , nw
        ; tg = λ η e → Ψᶠ-cp τ (g η e) (d-first (inj₂ (inj₁ (inj₁ u))) c t g d)
            (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d η e) lt nt (lg η e) (ng η e) (tg η e)
        ; dir = λ η e η′ e′ q → Ψᶠ-cp τ (g η′ e′) (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d η e)
            (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d η′ e′) (lg η e) (ng η e) (lg η′ e′) (ng η′ e′)
            (dir η e η′ e′ q)
        ; lt = Ψᶠ-legal τ t (d-first (inj₂ (inj₁ (inj₁ u))) c t g d) lt nt
        ; lg = λ η e → Ψᶠ-legal τ (g η e) (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d η e)
            (lg η e) (ng η e)
        ; lkʳ = λ η e → Ψᶠ-legal base (g η e) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d η e)
            (lg η e) (ng η e)
        ; nkʳ = λ η e → raw0-Nested
            (Ψᶠ base (g η e) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d η e) (lg η e) (ng η e)) })
  Ψᶠ-legal τ (G.lc (inj₂ (inj₂ (η , e , r))) c t g) d (tg , dir , irr , lt , lg)
    (lw , nw , nt , ng) =
    ΨN-legal (tl τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d)
      (ndB τ η e r c lw nw (Ψᶠ τ t (d-first (br η e r) c t g d) lt nt)
        g (d-obs (br η e r) c t g d) (d-drive (br η e r) c t g d) lg ng)
      (record
        { seed = seedL (read0 η) r c lw nw
        ; tg = λ ζ e′ → Ψᶠ-cp τ (g ζ e′) (d-first (br η e r) c t g d)
            (d-obs (br η e r) c t g d ζ e′) lt nt (lg ζ e′) (ng ζ e′) (tg ζ e′)
        ; dir = λ ζ e′ ζ′ e″ q → Ψᶠ-cp τ (g ζ′ e″) (d-obs (br η e r) c t g d ζ e′)
            (d-obs (br η e r) c t g d ζ′ e″) (lg ζ e′) (ng ζ e′) (lg ζ′ e″) (ng ζ′ e″)
            (dir ζ e′ ζ′ e″ q)
        ; lt = Ψᶠ-legal τ t (d-first (br η e r) c t g d) lt nt
        ; lg = λ ζ e′ → Ψᶠ-legal τ (g ζ e′) (d-obs (br η e r) c t g d ζ e′) (lg ζ e′) (ng ζ e′)
        ; lkʳ = λ ζ e′ → Ψᶠ-legal (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
            (lg ζ e′) (ng ζ e′)
        ; nkʳ = λ ζ e′ → Ψᶠ-nested (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
            (lg ζ e′) (ng ζ e′) })
  Ψᶠ-legal τ (G.em i a) d l nb = ⊥-elim (d-em i a d)
  Ψᶠ-legal base G.top d l nb = T₃ᵐ-legal
  Ψᶠ-legal (at η e r) G.top d l nb = topᴮ-legal η e r

  Ψᶠ-nested τ G.zero d l nb = cO-Nested (tl τ)
  Ψᶠ-nested τ (G.suc a) d l nb =
    copies-nested (tl τ) (Ψᶠ τ a (d-pred d) l nb) (Ψᶠ-nested τ a (d-pred d) l nb)
  Ψᶠ-nested τ (G.lim f) d (st , lf) nb = λ n → Ψᶠ-nested τ (f n) (d-term d n) (lf n) (nb n)
  Ψᶠ-nested τ (G.lc (inj₁ (inj₁ u)) c t g) d (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
    Ψn-nested (tl τ) zero tt (way τ (inj₁ (inj₁ u)) c t g d)
      (ndT τ c lw nw (Ψᶠ τ t (d-first (inj₁ (inj₁ u)) c t g d) lt nt)
        g (d-obs (inj₁ (inj₁ u)) c t g d) (d-drive (inj₁ (inj₁ u)) c t g d) lg ng)
      (record
        { seed = inj₁ refl , lw , nw
        ; lcʳ = lw
        ; ncʳ = nw
        ; nt = Ψᶠ-nested τ t (d-first (inj₁ (inj₁ u)) c t g d) lt nt
        ; ng = λ η e → Ψᶠ-nested τ (g η e) (d-obs (inj₁ (inj₁ u)) c t g d η e) (lg η e) (ng η e)
        ; lkʳ = λ η e → Ψᶠ-legal base (g η e) (d-drive (inj₁ (inj₁ u)) c t g d η e)
            (lg η e) (ng η e)
        ; nkʳ = λ η e → raw0-Nested
            (Ψᶠ base (g η e) (d-drive (inj₁ (inj₁ u)) c t g d η e) (lg η e) (ng η e)) })
  Ψᶠ-nested τ (G.lc (inj₂ (inj₁ (inj₁ u))) c t g) d (tg , dir , irr , lt , lg)
    (lw , nw , nt , ng) =
    Ψn-nested (tl τ) zero tt (way τ (inj₂ (inj₁ (inj₁ u))) c t g d)
      (ndT τ c lw nw (Ψᶠ τ t (d-first (inj₂ (inj₁ (inj₁ u))) c t g d) lt nt)
        g (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d) lg ng)
      (record
        { seed = inj₁ refl , lw , nw
        ; lcʳ = lw
        ; ncʳ = nw
        ; nt = Ψᶠ-nested τ t (d-first (inj₂ (inj₁ (inj₁ u))) c t g d) lt nt
        ; ng = λ η e → Ψᶠ-nested τ (g η e) (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d η e)
            (lg η e) (ng η e)
        ; lkʳ = λ η e → Ψᶠ-legal base (g η e) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d η e)
            (lg η e) (ng η e)
        ; nkʳ = λ η e → raw0-Nested
            (Ψᶠ base (g η e) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d η e) (lg η e) (ng η e)) })
  Ψᶠ-nested τ (G.lc (inj₂ (inj₂ (η , e , r))) c t g) d (tg , dir , irr , lt , lg)
    (lw , nw , nt , ng) =
    ΨN-nested (tl τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d)
      (ndB τ η e r c lw nw (Ψᶠ τ t (d-first (br η e r) c t g d) lt nt)
        g (d-obs (br η e r) c t g d) (d-drive (br η e r) c t g d) lg ng)
      (record
        { seed = seedL (read0 η) r c lw nw
        ; lcʳ = lw
        ; ncʳ = nw
        ; nt = Ψᶠ-nested τ t (d-first (br η e r) c t g d) lt nt
        ; ng = λ ζ e′ → Ψᶠ-nested τ (g ζ e′) (d-obs (br η e r) c t g d ζ e′) (lg ζ e′) (ng ζ e′)
        ; lkʳ = λ ζ e′ → Ψᶠ-legal (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
            (lg ζ e′) (ng ζ e′)
        ; nkʳ = λ ζ e′ → Ψᶠ-nested (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
            (lg ζ e′) (ng ζ e′) })
  Ψᶠ-nested τ (G.em i a) d l nb = ⊥-elim (d-em i a d)
  Ψᶠ-nested base G.top d l nb = raw0-Nested T₃ᵐ
  Ψᶠ-nested (at η e r) G.top d l nb = topᴮ-nested η e r

  Ψᶠ-cp τ ξ′ d d′ l nb l′ nb′ (inj₁ refl) = inj₁ refl
  Ψᶠ-cp τ ξ′ d d′ l nb l′ nb′ (inj₂ p) = inj₂ (Ψᶠ-dn τ ξ′ d d′ l nb l′ nb′ p)

  Ψᶠ-dn τ (G.suc b) d d′ l nb l′ nb′ p = zero , Ψᶠ-cp τ b d (d-pred d′) l nb l′ nb′ p
  Ψᶠ-dn τ (G.lim f) d d′ l nb (st , lf) nb′ (n , p) =
    n , Ψᶠ-cp τ (f n) d (d-term d′ n) l nb (lf n) (nb′ n) p
  Ψᶠ-dn τ (G.lc (inj₁ (inj₁ u)) c t g) d d′ l nb (tg , dir , irr , lt , lg)
    (lw , nw , nt , ng) p =
    Ψn-dn (tl τ) zero tt (way τ (inj₁ (inj₁ u)) c t g d′)
      (ndT τ c lw nw (Ψᶠ τ t (d-first (inj₁ (inj₁ u)) c t g d′) lt nt)
        g (d-obs (inj₁ (inj₁ u)) c t g d′) (d-drive (inj₁ (inj₁ u)) c t g d′) lg ng)
      (Ψᶠ-cp τ t d (d-first (inj₁ (inj₁ u)) c t g d′) l nb lt nt p)
      (inj₁ refl , lw , nw)
      (Ψᶠ-cp τ (g c (inj₁ refl , lw , nw)) d
        (d-obs (inj₁ (inj₁ u)) c t g d′ c (inj₁ refl , lw , nw)) l nb
        (lg c (inj₁ refl , lw , nw)) (ng c (inj₁ refl , lw , nw))
        (Cp-tr K₂ω p (tg c (inj₁ refl , lw , nw))))
  Ψᶠ-dn τ (G.lc (inj₂ (inj₁ (inj₁ u))) c t g) d d′ l nb (tg , dir , irr , lt , lg)
    (lw , nw , nt , ng) p =
    Ψn-dn (tl τ) zero tt (way τ (inj₂ (inj₁ (inj₁ u))) c t g d′)
      (ndT τ c lw nw (Ψᶠ τ t (d-first (inj₂ (inj₁ (inj₁ u))) c t g d′) lt nt)
        g (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d′) (d-drive (inj₂ (inj₁ (inj₁ u))) c t g d′) lg ng)
      (Ψᶠ-cp τ t d (d-first (inj₂ (inj₁ (inj₁ u))) c t g d′) l nb lt nt p)
      (inj₁ refl , lw , nw)
      (Ψᶠ-cp τ (g c (inj₁ refl , lw , nw)) d
        (d-obs (inj₂ (inj₁ (inj₁ u))) c t g d′ c (inj₁ refl , lw , nw)) l nb
        (lg c (inj₁ refl , lw , nw)) (ng c (inj₁ refl , lw , nw))
        (Cp-tr K₂ω p (tg c (inj₁ refl , lw , nw))))
  Ψᶠ-dn τ (G.lc (inj₂ (inj₂ (η , e , r))) c t g) d d′ l nb (tg , dir , irr , lt , lg)
    (lw , nw , nt , ng) p =
    ΨN-dn (tl τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d′)
      (ndB τ η e r c lw nw (Ψᶠ τ t (d-first (br η e r) c t g d′) lt nt)
        g (d-obs (br η e r) c t g d′) (d-drive (br η e r) c t g d′) lg ng)
      (Ψᶠ-cp τ t d (d-first (br η e r) c t g d′) l nb lt nt p)
      (seedL (read0 η) r c lw nw)
      (Ψᶠ-cp τ (g c (seedL (read0 η) r c lw nw)) d
        (d-obs (br η e r) c t g d′ c (seedL (read0 η) r c lw nw)) l nb
        (lg c (seedL (read0 η) r c lw nw)) (ng c (seedL (read0 η) r c lw nw))
        (Cp-tr K₂ω p (tg c (seedL (read0 η) r c lw nw))))
  Ψᶠ-dn τ (G.em i T) d d′ l nb l′ nb′ p = ⊥-elim (d-em i T d′)
  Ψᶠ-dn τ {G.em i a} G.top d d′ l nb l′ nb′ p = ⊥-elim (d-em i a d)
```

## 5 携带强度的两条，落在折叠上

"不多保留" 对任何派发成立：保留时派发自带槽位与层号的方程。"派发完全" 归结为 `way` 在这一个结点上完全。
`ownAt` 把折叠在一棵被问到的树上的值装成接口的 `OwnFold` (常值函数)；`honest-if` 是接口的 `Honest`。折叠本身对定义域里的树一致，见 `honest` 的量化。

```agda
  sound : ∀ τ p c t g (d : Dom τ (G.lc p c t g))
    (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
    (At (tl τ) (lev K₂ω p) → ⊥) → IsLim (Ψᶠ τ (G.lc p c t g) d l nb)
  sound τ (inj₁ (inj₁ u)) c t g d l nb na =
    Ψn-lim (tl τ) zero tt (way τ (inj₁ (inj₁ u)) c t g d) _
      (λ h → na (way-sound (way τ (inj₁ (inj₁ u)) c t g d) h))
  sound τ (inj₂ (inj₁ (inj₁ u))) c t g d l nb na =
    Ψn-lim (tl τ) zero tt (way τ (inj₂ (inj₁ (inj₁ u))) c t g d) _
      (λ h → na (way-sound (way τ (inj₂ (inj₁ (inj₁ u))) c t g d) h))
  sound τ (inj₂ (inj₂ (η , e , r))) c t g d l nb na =
    ΨN-lim (tl τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d) _
      (λ h → na (way-sound (way τ (br η e r) c t g d) h))

  kept : ∀ τ p c t g (d : Dom τ (G.lc p c t g))
    (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
    IsKeep (way τ p c t g d) → Kept (tl τ) (lev K₂ω p) (Ψᶠ τ (G.lc p c t g) d l nb)
  kept τ (inj₁ (inj₁ u)) c t g d l nb h =
    Ψn-kept (tl τ) (tl-plain τ) zero tt (way τ (inj₁ (inj₁ u)) c t g d) _ h
  kept τ (inj₂ (inj₁ (inj₁ u))) c t g d l nb h =
    Ψn-kept (tl τ) (tl-plain τ) zero tt (way τ (inj₂ (inj₁ (inj₁ u))) c t g d) _ h
  kept τ (inj₂ (inj₂ (η , e , r))) c t g d l nb h =
    ΨN-kept (tl τ) (tl-plain τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d) _ h

  honest : ∀ τ p c t g (d : Dom τ (G.lc p c t g))
    (l : Lgl K₂ω (G.lc p c t g)) (nb : Nested K₂ω (G.lc p c t g)) →
    (At (tl τ) (lev K₂ω p) → IsKeep (way τ p c t g d)) →
    (At (tl τ) (lev K₂ω p) → Kept (tl τ) (lev K₂ω p) (Ψᶠ τ (G.lc p c t g) d l nb)) ×
    ((At (tl τ) (lev K₂ω p) → ⊥) → IsLim (Ψᶠ τ (G.lc p c t g) d l nb))
  honest τ p c t g d l nb cm =
    (λ a → kept τ p c t g d l nb (cm a)) , sound τ p c t g d l nb

  ownAt : (τ : Tg) (ξ : RΩ) → .(Dom τ ξ) → .(Lgl K₂ω ξ) → .(Nested K₂ω ξ) → OwnFold (posT τ)
  ownAt base ξ d l nb ξ′ l′ nb′ = Ψᶠ base ξ d l nb
  ownAt (at η e r) ξ d l nb ξ′ l′ nb′ = Ψᶠ (at η e r) ξ d l nb

  honest-if : ∀ τ p c t g (d : Dom τ (G.lc p c t g))
    (l₀ : Lgl K₂ω (G.lc p c t g)) (nb₀ : Nested K₂ω (G.lc p c t g)) →
    (At (tl τ) (lev K₂ω p) → IsKeep (way τ p c t g d)) →
    Honest (posT τ) (ownAt τ (G.lc p c t g) d l₀ nb₀) (G.lc p c t g)
  honest-if base p c t g d l₀ nb₀ cm l nb = honest base p c t g d l₀ nb₀ cm
  honest-if (at η e r) p c t g d l₀ nb₀ cm l nb = honest (at η e r) p c t g d l₀ nb₀ cm
```

## 6 行

都是 `refl`。分支结点的链行：`ΨN` 走到那一支的位置，链的推进用目标 `at η e r` 的折叠在整个分支上的值。

```agda
  zero-row : ∀ τ .(d : Dom τ G.zero) → Ψᶠ τ G.zero d tt tt ≡ cO (tl τ)
  zero-row τ d = refl

  top-row⁰ : ∀ .(d : Dom base G.top) → Ψᶠ base G.top d tt tt ≡ T₃ᵐ
  top-row⁰ d = refl

  node-rowᴮ : ∀ τ η e r c t g (d : Dom τ (G.lc (br η e r) c t g))
    (l : Lgl K₂ω (G.lc (br η e r) c t g)) (nb : Nested K₂ω (G.lc (br η e r) c t g)) →
    Ψᶠ τ (G.lc (br η e r) c t g) d l nb ≡
    ΨN (tl τ) (read0 η) (rplain η) r (way τ (br η e r) c t g d)
      (nd c (proj₁ nb) (proj₁ (proj₂ nb))
        (Ψᶠ τ t (d-first (br η e r) c t g d)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
        (λ ζ e′ → Ψᶠ τ (g ζ e′) (d-obs (br η e r) c t g d ζ e′)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′))
        (λ ζ e′ → Ψᶠ (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′))
        (λ ζ e′ → Ψᶠ-legal (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′))
        (λ ζ e′ → Ψᶠ-nested (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′))
        (λ ζ e′ → Ψᶠ-pos (at η e r) (g ζ e′) (d-drive (br η e r) c t g d ζ e′)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′)))
  node-rowᴮ τ η e r c t g d l nb = refl
```

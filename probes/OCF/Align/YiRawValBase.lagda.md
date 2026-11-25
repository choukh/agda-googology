# YiRawFold 第 4 层：新折叠的值下界，底座与接口

**验收文件，档位：编译定理 (下界，不是同值)。** `lower₀`, `lower₁` (及 `ᵐ` 版)：读回的 `closed (fin 0)`, `closed (fin 1)` 不低于参照的 ψ₀(Ω₀), ψ₀(Ω₁)。
`FromInterface`：对任一层 `M`，给出 `Interface M` (同 [YiLvValBase](YiLvValBase.lagda.md) §3，折叠换成 `YiRawFold.Ψ`) 就有
`closed`, `closedᵐ` 在 `fin (M+1)` 上的下界。没有上界，没有 Funext。被验收的是 [YiRawFoldInst](YiRawFoldInst.lagda.md) 的 `closed`, `closedᵐ`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawValBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Nested; Lgl; Gd; GdL)
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (Legal; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldAdd using (plus)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold)
open import OCF.Align.YiLvFoldFin using (fin; fin-plain; fin-legal)
open import OCF.Align.YiRawFoldBase using (Ext; low; mix; wayOf; inS; inL; Nd; nd; NdR; NdL; Ψn; ΨN)
import OCF.Align.YiRawFold as N
open import OCF.Align.YiRawFoldInst using (closed; closedᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩; Ψ; γ; γ-self; plus≽; suc-lower; Ψ₀≼ψ⁰)
import OCF.Align.Level as L
import OCF.Align.Value as V
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)
```

## 1 目标第 0 层：派发恒为折叠，链的第 0 项

`Way zero k` 没有保留 (槽位在 `Pre zero` 里)，所以目标第 0 层的结点总走链行，第 0 项是起点那一支。

```agda
Ψn-first : ∀ k .(pl : Plain k) (y : Way B.zero k) (Nn : NdR B.zero k) {ℓ} {X : L.Ordᶜ ℓ} →
  (∀ .(e : Gd k (Nd.c Nn) (Nd.c Nn)) → X ≼ read (Nd.gm Nn (Nd.c Nn) e)) →
  X ≼ read (Ψn B.zero k pl y Nn)
Ψn-first k pl (keep () e) Nn h
Ψn-first k pl fold (nd c lw nw t gm gk lk nk pk) h = ≼l 0 (h (inj₁ refl , lw , nw))

ΨN-first : ∀ k (pl : Plain k) r (y : Way B.zero (lev k r)) (Nn : NdL B.zero k r) {ℓ} {X : L.Ordᶜ ℓ} →
  (∀ .(e : GdL k r (Nd.c Nn) (Nd.c Nn)) → X ≼ read (Nd.gm Nn (Nd.c Nn) e)) →
  X ≼ read (ΨN B.zero k pl r y Nn)
ΨN-first (B.suc k) pl (inj₁ _) y Nn h = Ψn-first k pl y Nn h
ΨN-first (B.suc k) pl (inj₂ r) y Nn h = ΨN-first k pl r y Nn h
ΨN-first (B.lim f) pl (n , r) y Nn h = ΨN-first (f n) (pl n) r y Nn h

one≼ : ∀ k (pl : Plain k) (Lg : Legal k) (x : Ext B.zero k) ξ .(l : Lgl k ξ) .(nb : Nested k ξ) →
  V.𝟏 ≼ read (N.Ψ B.zero k pl Lg x ξ l nb)
one≼ k pl Lg x G.zero l nb = ≼-refl _
one≼ k pl Lg x (G.suc a) l nb = ≼l 0 (one≼ k pl Lg x a l nb)
one≼ k pl Lg x (G.lim f) l nb = ≼l 0 (one≼ k pl Lg x (f 0) (proj₂ l 0) (nb 0))
one≼ k pl Lg x (G.lc r c t g) l nb =
  ΨN-first k pl r (wayOf x r) (N.ndL B.zero k pl Lg x r c t g l nb) (λ e →
    one≼ k pl Lg x (g c e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
one≼ (B.suc k) pl Lg x (G.em _ T) l nb = one≼ k pl Lg (inS x) T l nb
one≼ (B.lim f) pl Lg x (G.em n T) l nb = one≼ (f n) (pl n) (proj₂ Lg n) (inL x n) T l nb
one≼ B.zero pl Lg x G.top l nb = ≼l 0 (≼-refl _)
one≼ (B.suc k) pl Lg x G.top l nb =
  Ψn-first k pl (wayOf x (inj₁ tt)) (N.ndT B.zero k pl Lg (inS x)) (λ e →
    one≼ k pl Lg (inS x) (cO k) (cO-Lgl k) (cO-Nested k))
one≼ (B.lim f) pl Lg low G.top l nb = ≼l 0 (one≼ (f 0) (pl 0) (proj₂ Lg 0) low G.top tt tt)
one≼ (B.lim f) pl Lg (mix w) G.top l nb =
  ≼l 0 (one≼ (f 0) (pl 0) (proj₂ Lg 0) (mix (λ r → w (0 , r))) G.top tt tt)
```

## 2 第 0 层的输入

```agda
fold₀ : ∀ pl Lg (x : Ext B.zero B.zero) a .(l : Lgl B.zero a) .(nb : Nested B.zero a) →
  L.ψ⁰ (read a) ≼ read (N.Ψ B.zero B.zero pl Lg x a l nb)
fold₀ pl Lg x G.zero l nb = ≼-refl _
fold₀ pl Lg x (G.suc a) l nb =
  suc-lower (N.Ψ B.zero B.zero pl Lg x a l nb) (fold₀ pl Lg x a l nb)
fold₀ pl Lg x (G.lim f) l nb = l≼ (λ n → ≼l n (fold₀ pl Lg x (f n) (proj₂ l n) (nb n)))
fold₀ pl Lg x (G.lc () c t g) l nb
fold₀ pl Lg x (G.em () a) l nb
fold₀ pl Lg x G.top l nb = suc-lower (cO B.zero) (≼-refl _)
```

## 3 接口与条件定理

与 `YiLvValBase.Interface` 同四个字段；`lower` 对目标第 0 层的一切外部派发写，`closed` 用 `low`，`closedᵐ` 用全折叠的 `mix`。

```agda
record Interface (M : ℕ) : Set₁ where
  field
    Rel : L.Ordᶜ ⟨ M ⟩ → Raw (fin M) → Set
    start : Rel (L.Ω ⟨ M ⟩) (cO (fin M))
    step : ∀ {x η} → Rel x η → .(l : Lgl (fin M) η) .(nb : Nested (fin M) η) →
      Rel (Ψ M x) (N.Ψ (fin M) (fin M) (fin-plain M) (fin-legal M)
        (N.ownT (fin M) (fin-plain M) (fin-legal M)) η l nb)
    absorb : ∀ θ {x η} → Rel x η → Rel x (plus (fin M) θ η)
    lower : ∀ (y : Ext B.zero (fin M)) {x η} → Rel x η → x ≅ x →
      .(l : Lgl (fin M) η) .(nb : Nested (fin M) η) →
      L.ψ⁰ x ≼ read (N.Ψ B.zero (fin M) (fin-plain M) (fin-legal M) y η l nb)

module FromInterface (M : ℕ) (I : Interface M) where
  open Interface I

  module Run (y : Ext B.zero (fin M)) where
    Nd₀ : NdR B.zero (fin M)
    Nd₀ = N.ndT B.zero (fin M) (fin-plain M) (fin-legal M) y

    pts : ℕ → Pt (fin M) (cO (fin M))
    pts = iterate (N.nextᴿ (fin-plain M) Nd₀) (N.startᴿ Nd₀)

    step-at : ∀ (p : Pt (fin M) (cO (fin M))) {x} → Rel x (at p) →
      Rel (Ψ M x) (N.bodyᴿ Nd₀ p)
    step-at (pt η e) r = step r (proj₁ (proj₂ e)) (proj₂ (proj₂ e))

    out-at : ∀ (p : Pt (fin M) (cO (fin M))) {x} → Rel x (at p) → x ≅ x →
      L.ψ⁰ x ≼ read (N.obsᴿ Nd₀ p)
    out-at (pt η e) r s = lower y r s (proj₁ (proj₂ e)) (proj₂ (proj₂ e))

    chain : ∀ i → Rel (γ M i) (at (pts i))
    chain zero = start
    chain (suc i) = absorb (at (pts i)) (step-at (pts i) (chain i))

    value : L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≼ read (Ψn B.zero (fin M) (fin-plain M) fold Nd₀)
    value = l≼ (λ i → ≼l i (out-at (pts i) (chain i) (γ-self M i)))

  theorem : L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≼
    read (closed (fin (suc M)) (fin-plain (suc M)) (fin-legal (suc M)))
  theorem = Run.value low

  theoremᵐ : L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≼
    read (closedᵐ (fin (suc M)) (fin-plain (suc M)) (fin-legal (suc M)))
  theoremᵐ = Run.value (mix (λ r → fold))
```

## 4 第 0 层的实例：ψ₀(Ω₀) 与 ψ₀(Ω₁)

```agda
interface₀ : Interface 0
interface₀ = record
  { Rel = λ x η → x ≼ read η
  ; start = ≼-refl _
  ; step = λ {x} {η} r l nb →
      ≼-trans (Ψ₀≼ψ⁰ x) (≼-trans (V.ψ⁰-mono⁰ r) (fold₀ tt tt (N.ownT B.zero tt tt) η l nb))
  ; absorb = λ θ {x} {η} r → plus≽ θ η r
  ; lower = λ y {x} {η} r s l nb → ≼-trans (V.ψ⁰-mono⁰ r) (fold₀ tt tt y η l nb)
  }

lower₀ : L.ψ⁰ (L.Ω ⟨ 0 ⟩) ≼ read (closed (fin 0) tt tt)
lower₀ = suc-lower (cO B.zero) (≼-refl _)

lower₀ᵐ : L.ψ⁰ (L.Ω ⟨ 0 ⟩) ≼ read (closedᵐ (fin 0) tt tt)
lower₀ᵐ = suc-lower (cO B.zero) (≼-refl _)

lower₁ : L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read (closed (fin 1) tt tt)
lower₁ = FromInterface.theorem 0 interface₀

lower₁ᵐ : L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read (closedᵐ (fin 1) tt tt)
lower₁ᵐ = FromInterface.theoremᵐ 0 interface₀
```

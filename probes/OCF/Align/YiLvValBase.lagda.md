# YiLvFold 第 4 层：有限层号一站的值下界，底座与接口

**验收文件，档位：编译定理 (下界，不是同值)。** `lower₀`, `lower₁`：读回的 `foldᶠ 0`, `foldᶠ 1` 不低于参照的 ψ₀(Ω₀), ψ₀(Ω₁)。
`FromInterface`：对任一层 `M`，给出接口 `Interface M` (链点之间的关系、起点、目标层 `M` 的折叠保持、前缀吸收、目标层 0 的下界) 就有
`ψ⁰ (Ω ⟨M+1⟩) ≼ read (foldᶠ (M+1))`；`interface₀` 是 `M = 0` 的实例。没有上界，没有 Funext。被验收的是 [YiLvFoldFin](YiLvFoldFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvValBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Nested)
open import OCF.Align.RR5IrrCheck using (up; Ω̂; cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (R; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvFoldAdd using (plus; copies; successor)
open import OCF.Align.YiLvFoldBase using (Dom; dom-at; startᴸ; module Node)
open import OCF.Align.YiLvFoldFin
  using (fin; ψ; next; out; foldᶠ; dom-Ωᶠ; Ωᶠ-branch)
open import OCF.Align.YiIrrFoldValue using (read)
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4MonoFragment as MF
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼)
```

## 1 第 0 层：加法、ω 倍、折叠的读回

`plus 0` 与 `copies 0` 读成 `Level` 第 0 层的加法与倍数 (第 0 项一份)。目标层 0 的折叠在第 0 层的输入上不低于 `ψ⁰`；
`one≼fold` 对一切定义域里的树：链行的第 0 项是起点那一支。

```agda
read-plus : ∀ x y → read (plus B.zero x y) ≅ (read x L.+ read y)
read-plus x G.zero = L.≅-refl⁰ (read x)
read-plus x (G.suc y) = L.s≅ (read-plus x y)
read-plus x (G.lim f) = L.l≅ (λ n → read-plus x (f n))
read-plus x (G.lc () c t g)
read-plus x (G.em () a)
read-plus x G.top = L.s≅ (L.≅-refl⁰ (read x))

plus≽ : ∀ θ {y : L.Ordᶜ L.zero} η → y ≼ read η → y ≼ read (plus B.zero θ η)
plus≽ θ η q = ≼-trans q (≼-trans (MF.≼-+ˡ (read θ) (read η))
  (≅→≼ (L.≅-sym (read-plus θ η))))

read-copies : ∀ y {Y : L.Ordᶜ L.zero} → Y ≼ read y → ∀ n →
  iter (Y L.+_) L.zero (suc n) ≼ read (copies B.zero y n)
read-copies y low zero = low
read-copies y low (suc n) =
  ≼-trans (V.+-mono low (read-copies y low n))
    (≅→≼ (L.≅-sym (read-plus y (copies B.zero y n))))

suc-lower : ∀ {k} {x : L.Ordᶜ k} a → L.ψ⁰ x ≼ read a →
  L.ψ⁰ (L.suc x) ≼ read (successor B.zero a)
suc-lower a low = l≼ λ where
  zero → z≼
  (suc n) → ≼l n (read-copies a low n)

fold₀-lower : ∀ a .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  L.ψ⁰ (read a) ≼ read (ψ B.zero (up B.zero a nb) d)
fold₀-lower G.zero nb d = ≼-refl _
fold₀-lower (G.suc a) nb d =
  suc-lower (ψ B.zero (up B.zero a nb) d) (fold₀-lower a nb d)
fold₀-lower (G.lim f) nb d = l≼ (λ n → ≼l n
  (fold₀-lower (f n) (nb n) (dom-at (λ n → up B.zero (f n) (nb n)) d n)))
fold₀-lower (G.lc () c t g) nb d
fold₀-lower (G.em () a) nb d
fold₀-lower G.top nb d = suc-lower (cO B.zero) (≼-refl _)

one≼fold : ∀ X .(d : Dom X) → V.𝟏 ≼ read (ψ B.zero X d)
one≼fold B.zero d = ≼-refl _
one≼fold (B.suc X) d = ≼l 0 (one≼fold X d)
one≼fold (B.lim f) d = ≼l 0 (one≼fold (f 0) (dom-at f d 0))
one≼fold (B.lc k c w b t g) d = ≼l 0
  (one≼fold (g c (inj₁ refl , w , b))
    (Node.branch k c w b t g d c (inj₁ refl , w , b)))
```

## 2 参照与链

`⟨ M ⟩` 是 `Level` 的第 `M` 层下标。`ψ⁰ (Ω ⟨M+1⟩)` 的链在第 `M` 层，从 `Ω ⟨M⟩` 起，每步是目标层 `M` 的折叠 `Ψ M`。
被验收一侧 `foldᶠ (M+1)` 的链也在第 `M` 层 (`Raw (fin M)`)，从 `cO (fin M)` 起，每步加上目标层 `fin M` 的折叠。

```agda
⟨_⟩ : ℕ → L.Ordᴵ
⟨ n ⟩ = L.natᴵ n

Ψ : ∀ M → L.Ordᶜ ⟨ M ⟩ → L.Ordᶜ ⟨ M ⟩
Ψ M = L.ψ {i = ⟨ M ⟩} {k = ⟨ M ⟩} {ℓ = L.suc ⟨ M ⟩} L.zero (λ q → L.suc q)

γ : ∀ M → ℕ → L.Ordᶜ ⟨ M ⟩
γ M = iter (Ψ M) (L.Ω ⟨ M ⟩)

reference-row : ∀ M → L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≡ L.lim (λ i → L.ψ⁰ (γ M i))
reference-row M = refl

γ-self : ∀ M i → γ M i ≅ γ M i
γ-self M zero = L.Ω-≅ (L.≅ᴵ-refl ⟨ M ⟩)
γ-self M (suc i) =
  L.ψ-≅ {p = L.zero} {σ = λ q → L.suc q} {p′ = L.zero} {σ′ = λ q → L.suc q}
    (L.≅ᴵ-refl ⟨ M ⟩) (γ-self M i)

module Top (M : ℕ) where

  step : Pt (fin M) (cO (fin M)) → Pt (fin M) (cO (fin M))
  step = next (fin M) (cO (fin M)) (cO-Lgl (fin M)) (cO-Nested (fin M))
    (Ω̂ (fin M)) (Ωᶠ-branch M) (dom-Ωᶠ (suc M))

  obs : ∀ m → Pt (fin M) (cO (fin M)) → Raw m
  obs m = out m (fin M) (cO (fin M)) (cO-Lgl (fin M)) (cO-Nested (fin M))
    (Ω̂ (fin M)) (Ωᶠ-branch M) (dom-Ωᶠ (suc M))

  pts : ℕ → Pt (fin M) (cO (fin M))
  pts = iterate step (startᴸ (fin M) (cO (fin M)) (cO-Lgl (fin M)) (cO-Nested (fin M)))

  row : foldᶠ (suc M) ≡ G.lim (λ i → obs B.zero (pts i))
  row = refl
```

## 3 接口与条件定理

`Rel` 是第 `M` 层的参照树与 `Raw (fin M)` 的值之间的关系。四个字段对应链的四处：起点、链的一步 (目标层 `M` 的折叠)、
加法链多出的前缀、观察 (目标层 0 的折叠)。证据参数都无关。

```agda
record Interface (M : ℕ) : Set₁ where
  field
    Rel : L.Ordᶜ ⟨ M ⟩ → Raw (fin M) → Set
    start : Rel (L.Ω ⟨ M ⟩) (cO (fin M))
    step : ∀ {x η} → Rel x η → .(nb : Nested (fin M) η) →
      .(d : Dom (up (fin M) η nb)) → Rel (Ψ M x) (ψ (fin M) (up (fin M) η nb) d)
    absorb : ∀ θ {x η} → Rel x η → Rel x (plus (fin M) θ η)
    lower : ∀ {x η} → Rel x η → x ≅ x → .(nb : Nested (fin M) η) →
      .(d : Dom (up (fin M) η nb)) → L.ψ⁰ x ≼ read (ψ B.zero (up (fin M) η nb) d)

module FromInterface (M : ℕ) (I : Interface M) where
  open Interface I
  open Top M using (pts; obs)

  step-at : ∀ (p : Pt (fin M) (cO (fin M))) {x} → Rel x (at p) →
    Rel (Ψ M x) (obs (fin M) p)
  step-at (pt η e) r = step r (proj₂ (proj₂ e))
    (Node.branch (fin M) (cO (fin M)) (cO-Lgl (fin M)) (cO-Nested (fin M))
      (Ω̂ (fin M)) (Ωᶠ-branch M) (dom-Ωᶠ (suc M)) η e)

  out-at : ∀ (p : Pt (fin M) (cO (fin M))) {x} → Rel x (at p) → x ≅ x →
    L.ψ⁰ x ≼ read (obs B.zero p)
  out-at (pt η e) r s = lower r s (proj₂ (proj₂ e))
    (Node.branch (fin M) (cO (fin M)) (cO-Lgl (fin M)) (cO-Nested (fin M))
      (Ω̂ (fin M)) (Ωᶠ-branch M) (dom-Ωᶠ (suc M)) η e)

  chain : ∀ i → Rel (γ M i) (at (pts i))
  chain zero = start
  chain (suc i) = absorb (at (pts i)) (step-at (pts i) (chain i))

  theorem : L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≼ read (foldᶠ (suc M))
  theorem = l≼ (λ i → ≼l i (out-at (pts i) (chain i) (γ-self M i)))
```

## 4 第 0 层的实例：ψ₀(Ω₀) 与 ψ₀(Ω₁)

```agda
Ψ₀≼ψ⁰ : ∀ (x : L.Ordᶜ L.zero) → Ψ 0 x ≼ L.ψ⁰ x
Ψ₀≼ψ⁰ x = ≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → L.suc q} (L.≅-refl⁰ x)))

interface₀ : Interface 0
interface₀ = record
  { Rel = λ x η → x ≼ read η
  ; start = ≼-refl _
  ; step = λ {x} {η} r nb d →
      ≼-trans (Ψ₀≼ψ⁰ x) (≼-trans (V.ψ⁰-mono⁰ r) (fold₀-lower η nb d))
  ; absorb = λ θ {x} {η} r → plus≽ θ η r
  ; lower = λ {x} {η} r s nb d → ≼-trans (V.ψ⁰-mono⁰ r) (fold₀-lower η nb d)
  }

lower₀ : L.ψ⁰ (L.Ω ⟨ 0 ⟩) ≼ read (foldᶠ 0)
lower₀ = suc-lower (cO B.zero) (≼-refl _)

lower₁ : L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read (foldᶠ 1)
lower₁ = FromInterface.theorem 0 interface₀
```

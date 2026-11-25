# YiRawFold 第 4 层：新折叠的 ψ₀(Ω₂) 下界

**验收文件，档位：编译定理 (下界，不是同值)。** `lower₂`, `lower₂ᵐ`：参照 `ψ⁰ (Ω ⟨2⟩)` ≼ 读回的 `closed (fin 2)`, `closedᵐ (fin 2)`。
逐点前序 `_⊴_` 与加法的引理原样取自 [YiLvVal2](YiLvVal2.lagda.md)；本篇只把折叠的四条 (`Ω⊴Φ`, `Ψ₀⊴Φ`, `Ψ₁⊴Φ`, `fold-lower`) 改写在
`YiRawFold.Ψ` 的行上，链的一步由 `node-lower` 给出 (推进用 `own`，观察用任意外部派发)。接口见 [YiRawValBase](YiRawValBase.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawVal2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Nested; Lgl; Gd)
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiIrrIf using (R; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvFoldAdd using (plus; Pos)
open import OCF.Align.YiLvIf using (Plain)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold; startᴸ; module Chain)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiRawFoldBase using (Ext; wayOf; inS; Nd; nd; NdR; Ψn)
import OCF.Align.YiRawFold as N
open import OCF.Align.YiRawFoldInst using (closed; closedᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩; plus≽; suc-lower)
open import OCF.Align.YiLvVal2
  using (T₀; T₁; L1; R₁; ℓ₁; _⊴_; z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; nt; em⊴; u⊴;
         ⊴-+ˡ; Ψ₀; Ψ₁; Ω⊴top; suc-step; tr⁻≼; s≅⁻; l≅⁻; lᵢ≅⁻)
open import OCF.Align.YiRawValBase using (Interface; module FromInterface; one≼; fold₀; ΨN-first)
import OCF.Align.Level as L
import OCF.Align.Value as V
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
```

## 1 目标层 1 的折叠

推进用的外部派发是 `X₁ = ownT 1`；它在根位置上保留 (`X₁-keeps`)，所以层号 0 的结点在目标层 1 上原样保留，与旧折叠的 `wayᵇ (fin 1) 0` 同。
第 0 层的输入上外部派发不起作用 (`Raw 0` 没有结点)，所以那两条对一切外部派发写。

```agda
X₁ : Ext L1 L1
X₁ = N.ownT L1 tt tt

X₁-keeps : wayOf X₁ (inj₁ tt) ≡ keep (inj₁ tt) refl
X₁-keeps = refl

Φ : (η : R₁) → .(Lgl L1 η) → .(Nested L1 η) → R₁
Φ η l nb = N.Ψ L1 L1 tt tt X₁ η l nb

Ω⊴Φ₀ : ∀ (x : Ext L1 B.zero) a .(l : Lgl B.zero a) .(nb : Nested B.zero a) →
  L.Ω ℓ₁ ⊴ N.Ψ L1 B.zero tt tt x a l nb
Ω⊴Φ₀ x G.zero l nb = Ω⊴top
Ω⊴Φ₀ x (G.suc a) l nb = ⊴l 0 (Ω⊴Φ₀ x a l nb)
Ω⊴Φ₀ x (G.lim f) l nb = ⊴l 0 (Ω⊴Φ₀ x (f 0) (proj₂ l 0) (nb 0))
Ω⊴Φ₀ x (G.lc () c t g) l nb
Ω⊴Φ₀ x (G.em () a) l nb
Ω⊴Φ₀ x G.top l nb = ⊴l 0 Ω⊴top

Ω⊴Φ : ∀ η .(l : Lgl L1 η) .(nb : Nested L1 η) → L.Ω ℓ₁ ⊴ Φ η l nb
Ω⊴Φ G.zero l nb = Ω⊴top
Ω⊴Φ (G.suc η) l nb = ⊴l 0 (Ω⊴Φ η l nb)
Ω⊴Φ (G.lim f) l nb = ⊴l 0 (Ω⊴Φ (f 0) (proj₂ l 0) (nb 0))
Ω⊴Φ (G.lc (inj₁ _) c t g) l nb = ⊴b (λ e →
  Ω⊴Φ (g c e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
Ω⊴Φ (G.lc (inj₂ ()) c t g) l nb
Ω⊴Φ (G.em _ a) l nb = Ω⊴Φ₀ (inS X₁) a l nb
Ω⊴Φ G.top l nb = ⊴b (λ e → ⊴l 0 Ω⊴top)

Ψ₀⊴Φ₀ : ∀ (x : Ext L1 B.zero) {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  .(l : Lgl B.zero a) .(nb : Nested B.zero a) → Ψ₀ y ⊴ N.Ψ L1 B.zero tt tt x a l nb
Ψ₀⊴Φ₀ x z≼ a q l nb = Ω⊴Φ₀ x a l nb
Ψ₀⊴Φ₀ x (s≼s p) (G.suc a) refl l nb = suc-step (Ψ₀⊴Φ₀ x p a refl l nb)
Ψ₀⊴Φ₀ x (s≼s p) G.top refl l nb = suc-step (Ψ₀⊴Φ₀ x p G.zero refl tt tt)
Ψ₀⊴Φ₀ x (≼l n p) (G.lim f) refl l nb = ⊴l n (Ψ₀⊴Φ₀ x p (f n) refl (proj₂ l n) (nb n))
Ψ₀⊴Φ₀ x (l≼ h) a q l nb = l⊴ (λ n → Ψ₀⊴Φ₀ x (h n) a q l nb)
Ψ₀⊴Φ₀ x (≼i {p = ()} z ez p) a q l nb
Ψ₀⊴Φ₀ x (i≼ {p = ()} h) a q l nb
Ψ₀⊴Φ₀ x (≼u {r = ()} p) a q l nb
Ψ₀⊴Φ₀ x (u≼ {r = ()} p) a q l nb

Ψ₀⊴Φ : ∀ {y : T₀} {η} → y ⊴ η → .(l : Lgl L1 η) .(nb : Nested L1 η) → Ψ₀ y ⊴ Φ η l nb
Ψ₀⊴Φ {η = η} z⊴ l nb = Ω⊴Φ η l nb
Ψ₀⊴Φ (s⊴s p) l nb = suc-step (Ψ₀⊴Φ p l nb)
Ψ₀⊴Φ (⊴s p) l nb = ⊴l 0 (Ψ₀⊴Φ p l nb)
Ψ₀⊴Φ {η = G.lim F} (⊴l n p) l nb = ⊴l n (Ψ₀⊴Φ p (proj₂ l n) (nb n))
Ψ₀⊴Φ (l⊴ h) l nb = l⊴ (λ n → Ψ₀⊴Φ (h n) l nb)
Ψ₀⊴Φ {η = G.lc (inj₁ _) c t g} (⊴b h) l nb = ⊴b (λ e →
  Ψ₀⊴Φ (h e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
Ψ₀⊴Φ (em⊴ {a = a} q) l nb = Ψ₀⊴Φ₀ (inS X₁) q a refl l nb

Ψ₁⊴Φ : ∀ {x : T₁} {η} → x ⊴ η → .(l : Lgl L1 η) .(nb : Nested L1 η) → Ψ₁ x ⊴ Φ η l nb
Ψ₁⊴Φ {η = η} z⊴ l nb = Ω⊴Φ η l nb
Ψ₁⊴Φ (s⊴s p) l nb = suc-step (Ψ₁⊴Φ p l nb)
Ψ₁⊴Φ (⊴s p) l nb = ⊴l 0 (Ψ₁⊴Φ p l nb)
Ψ₁⊴Φ {η = G.lim F} (⊴l n p) l nb = ⊴l n (Ψ₁⊴Φ p (proj₂ l n) (nb n))
Ψ₁⊴Φ (l⊴ h) l nb = l⊴ (λ n → Ψ₁⊴Φ (h n) l nb)
Ψ₁⊴Φ {η = G.lc (inj₁ _) c t g} (⊴b h) l nb = ⊴b (λ e →
  Ψ₁⊴Φ (h e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
Ψ₁⊴Φ {η = G.lc (inj₁ _) c t g} (nd b h) l nb = nd b (λ y a e q →
  Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) q))
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
Ψ₁⊴Φ (nt h) l nb = nd (s≼s z≼) (λ y a e q →
  Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
Ψ₁⊴Φ (u⊴ p) l nb = Ψ₀⊴Φ p l nb
```

## 2 目标层 0 的折叠把关系送到值前序

层号 0 的结点处两条链同步归纳 (参照是原链，被验收一侧是加法链)。新折叠里推进用的分支 `gk` 与观察的分支 `gm`
是两个不同的外部派发下的折叠，所以两条下界分开给。

```agda
module NodeChain (f : T₀ → T₁) (same : ∀ y → f y ≅ f y)
  (c : R) .(lw : Lgl B.zero c) .(nw : Nested B.zero c)
  (gm gk : (a : R) → .(Gd B.zero c a) → R)
  .(lk : ∀ a (e : Gd B.zero c a) → Lgl B.zero (gk a e))
  .(nk : ∀ a (e : Gd B.zero c a) → Nested B.zero (gk a e))
  (pk : ∀ a .(e : Gd B.zero c a) → Pos B.zero (gk a e))
  (base : V.𝟏 ≼ read c)
  (lowk : ∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a → L.ψ⁰ (f y) ≼ read (gk a e))
  (lowm : ∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a → L.ψ⁰ (f y) ≼ read (gm a e)) where

  open Chain B.zero tt c gk lk nk pk

  pts : ℕ → Pt B.zero c
  pts = iterate next (startᴸ B.zero c lw nw)

  ref-step : T₀ → T₀
  ref-step y = L.ψ {i = L.zero} {k = ℓ₁} {ℓ = ℓ₁} L.zero (λ r → r) (f y)

  δ : ℕ → T₀
  δ = iter ref-step (L.suc L.zero)

  step≤ : ∀ y → ref-step y ≼ L.ψ⁰ (f y)
  step≤ y = ≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r} (same y)))

  herek : ∀ (p : Pt B.zero c) y → y ≼ read (at p) → L.ψ⁰ (f y) ≼ read (step p)
  herek (pt a e) y q = lowk y a e q

  herem : ∀ (p : Pt B.zero c) y → y ≼ read (at p) → L.ψ⁰ (f y) ≼ read (see B.zero gm p)
  herem (pt a e) y q = lowm y a e q

  chain-lower : ∀ n → δ n ≼ read (at (pts n))
  chain-lower zero = base
  chain-lower (suc n) =
    ≼-trans (step≤ (δ n))
      (plus≽ (at (pts n)) (step (pts n)) (herek (pts n) (δ n) (chain-lower n)))

  result : L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f) ≼
    read (collapse B.zero gm (startᴸ B.zero c lw nw))
  result = l≼ (λ n → ≼l n (herem (pts n) (δ n) (chain-lower n)))

node-lower : ∀ (f : T₀ → T₁) → (∀ y → f y ≅ f y) → .(pl : Plain B.zero)
  (w : Way B.zero B.zero) (Nn : NdR B.zero B.zero) → V.𝟏 ≼ read (Nd.c Nn) →
  (∀ (y : T₀) a .(e : Gd B.zero (Nd.c Nn) a) → y ≼ read a → L.ψ⁰ (f y) ≼ read (Nd.gk Nn a e)) →
  (∀ (y : T₀) a .(e : Gd B.zero (Nd.c Nn) a) → y ≼ read a → L.ψ⁰ (f y) ≼ read (Nd.gm Nn a e)) →
  L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f) ≼ read (Ψn B.zero B.zero pl w Nn)
node-lower f s pl (keep () e) Nn b hk hm
node-lower f s pl fold (nd c lw nw t gm gk lk nk pk) b hk hm =
  NodeChain.result f s c lw nw gm gk lk nk pk b hk hm

-- 推进用的外部派发: 层号 0 的结点自己那一层的 own, 与 top 处的 ownT 0.
Own : Ext B.zero L1
Own = N.own L1 tt tt (inj₁ tt)

fold-lower : ∀ (xe : Ext B.zero L1) {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ≅ x →
  .(l : Lgl L1 η) .(nb : Nested L1 η) → L.ψ⁰ x ≼ read (N.Ψ B.zero L1 tt tt xe η l nb)
fold-lower xe {η = η} z⊴ s l nb = one≼ L1 tt tt xe η l nb
fold-lower xe {η = G.suc η} (s⊴s p) s l nb =
  suc-lower (N.Ψ B.zero L1 tt tt xe η l nb) (fold-lower xe p (s≅⁻ s) l nb)
fold-lower xe (⊴s p) s l nb = ≼l 0 (fold-lower xe p s l nb)
fold-lower xe {η = G.lim F} (⊴l n p) s l nb = ≼l n (fold-lower xe p s (proj₂ l n) (nb n))
fold-lower xe (l⊴ h) s l nb = l≼ (λ n → fold-lower xe (h n) (l≅⁻ s n) l nb)
fold-lower xe {η = G.lc (inj₁ _) c t g} (⊴b h) s l nb =
  ΨN-first L1 tt (inj₁ tt) (wayOf xe (inj₁ tt)) (N.ndL B.zero L1 tt tt xe (inj₁ tt) c t g l nb)
    (λ e → fold-lower xe (h e) s
      (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
fold-lower xe {η = G.lc (inj₁ tt) c t g} (nd {f = f} base h) s l nb =
  node-lower f (lᵢ≅⁻ s) tt (wayOf xe (inj₁ tt)) (N.ndL B.zero L1 tt tt xe (inj₁ tt) c t g l nb) base
    (λ y a e q → fold-lower Own (h y a e q) (lᵢ≅⁻ s y)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
    (λ y a e q → fold-lower xe (h y a e q) (lᵢ≅⁻ s y)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
fold-lower xe (nt {f = f} h) s l nb =
  node-lower f (lᵢ≅⁻ s) tt (wayOf xe (inj₁ tt)) (N.ndT B.zero B.zero tt tt (inS xe)) (≼-refl _)
    (λ y a e q → fold-lower (N.own L1 tt tt (inj₁ tt)) (h y a q) (lᵢ≅⁻ s y)
      (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (λ y a e q → fold-lower xe (h y a q) (lᵢ≅⁻ s y) (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
fold-lower xe {η = G.em tt a} (em⊴ q) s l nb =
  ≼-trans (V.ψ⁰-mono⁰ q) (fold₀ tt tt (inS xe) a l nb)
fold-lower xe (u⊴ {y = y} p) s l nb = fold-lower xe p (L.≅-refl⁰ y) l nb
```

## 3 接口与 ψ₀(Ω₂)

```agda
interface₁ : Interface 1
interface₁ = record
  { Rel = λ x η → x ⊴ η
  ; start = Ω⊴top
  ; step = Ψ₁⊴Φ
  ; absorb = λ θ r → ⊴-+ˡ θ r
  ; lower = λ y r s l nb → fold-lower y r s l nb
  }

lower₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (closed (fin 2) tt tt)
lower₂ = FromInterface.theorem 1 interface₁

lower₂ᵐ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (closedᵐ (fin 2) tt tt)
lower₂ᵐ = FromInterface.theoremᵐ 1 interface₁
```

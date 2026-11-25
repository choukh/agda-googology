# YiRawFold 第 4 层：新折叠的 ψ₀(Ω₃) 下界

**验收文件，档位：编译定理 (下界，不是同值)。** `lower₃`, `lower₃ᵐ`：参照 `ψ⁰ (Ω ⟨3⟩)` ≼ 读回的 `closed (fin 3)`, `closedᵐ (fin 3)`，经接口 `interface₂`。
照 [YiLvVal3](YiLvVal3.lagda.md) 的 `C₀` 到 `C₂`, `D` 改写在 `YiRawFold.Ψ` 的行上；目标层 1 上用的外部派发是层号 1 的结点自己的 `own` (`Y₁`)，
它折叠层号 1 的结点、保留层号 0 的结点，进孩子以后就是 [YiRawVal2](YiRawVal2.lagda.md) 的 `X₁` (`Y₁-in`)。目标层 2 在 [YiRawVal3Base](YiRawVal3Base.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawVal3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Nested; Lgl; Gd)
open import OCF.Align.YiIrrIf using (R; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvIf using (Plain)
open import OCF.Align.YiLvFoldAdd using (Pos)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold; startᴸ; module Chain)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiRawFoldBase using (Ext; wayOf; inS; Nd; nd; NdR; Ψn)
import OCF.Align.YiRawFold as N
open import OCF.Align.YiRawFoldInst using (closed; closedᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩; plus≽; suc-lower)
open import OCF.Align.YiLvVal2
  using (ℓ₁; ℓ₂; T₀; T₁; L1; R₁; _⊴_; z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; nt; em⊴; u⊴;
         ⊴-+ˡ; suc-step; Ω⊴top; tr⁻≼; s≅⁻; l≅⁻)
open import OCF.Align.YiLvVal3Base
  using (L2; R₂; _⊴₂_; z₂; ss₂; s₂; l₂; ll₂; b1; b0; nd1; nd0; nt₂; em₂; u₂; ⊴₂-+ˡ; Ω₂⊴top)
open import OCF.Align.YiLvVal3 using (δ₁; δ₁-self; lᵢ≅⁻; up≅⁻)
open import OCF.Align.YiRawValBase using (Interface; module FromInterface; one≼; ΨN-first)
open import OCF.Align.YiRawVal2 using (X₁; Ω⊴Φ; Ω⊴Φ₀) renaming (fold-lower to fold-lower₁)
open import OCF.Align.YiRawVal3Base using (B₂)
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)

Y₁ : Ext L1 L2
Y₁ = N.own L2 tt tt (inj₁ tt)

Y₁-folds : wayOf Y₁ (inj₁ tt) ≡ fold
Y₁-folds = refl

Y₁-keeps : wayOf Y₁ (inj₂ (inj₁ tt)) ≡ keep (inj₁ tt) refl
Y₁-keeps = refl

Y₁-in : inS Y₁ ≡ X₁
Y₁-in = refl
```

## 1 层号 1 的结点上的链

链在 `Raw 1` 里，参照一侧 `δ₁` 每步是目标层 1 的折叠，链点之间是 `_⊴_`；`outAt` 把每一点送到任一观察关系。
两个包装按结点的数据记录分情况，所以链与 `Ψn` 的链行字面相同。

```agda
module Chain1 {K} (q : ℓ₁ L.<ᴵ K) (f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K)
  (c : R₁) .(lw : Lgl L1 c) .(nw : Nested L1 c)
  (gk : (a : R₁) → .(Gd L1 c a) → R₁)
  .(lk : ∀ a (e : Gd L1 c a) → Lgl L1 (gk a e))
  .(nk : ∀ a (e : Gd L1 c a) → Nested L1 (gk a e))
  (pk : ∀ a .(e : Gd L1 c a) → Pos L1 (gk a e))
  (base : L.Ω ℓ₁ ⊴ c)
  (stepL : ∀ (y : T₁) a .(e : Gd L1 c a) → y ⊴ a →
    L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y)) ⊴ gk a e) where

  open Chain L1 tt c gk lk nk pk

  pts : ℕ → Pt L1 c
  pts = iterate next (startᴸ L1 c lw nw)

  stepAt : ∀ (p : Pt L1 c) y → y ⊴ at p →
    L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y)) ⊴ step p
  stepAt (pt a e) y r = stepL y a e r

  chain : ∀ n → δ₁ q f n ⊴ at (pts n)
  chain zero = base
  chain (suc n) = ⊴-+ˡ (at (pts n)) (stepAt (pts n) (δ₁ q f n) (chain n))

  outAt : ∀ m (gm : (a : R₁) → .(Gd L1 c a) → Raw m) (O : T₁ → Raw m → Set) →
    (∀ (y : T₁) a .(e : Gd L1 c a) → y ⊴ a → O y (gm a e)) →
    ∀ n → O (δ₁ q f n) (see m gm (pts n))
  outAt m gm O h n = go (pts n) (chain n) where
    go : ∀ p → δ₁ q f n ⊴ at p → O (δ₁ q f n) (see m gm p)
    go (pt a e) r = h (δ₁ q f n) a e r

fold1⊴ : ∀ {K} (q : ℓ₁ L.<ᴵ K) (f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K)
  {ℓ} (p : ℓ₁ L.<ᴵ ℓ) (σ : L.Simᴵ K ℓ) .(pl : Plain L1) (Nn : NdR L1 L1) →
  L.Ω ℓ₁ ⊴ Nd.c Nn →
  (∀ (y : T₁) a .(e : Gd L1 (Nd.c Nn) a) → y ⊴ a →
    L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y)) ⊴ Nd.gk Nn a e) →
  (∀ (y : T₁) a .(e : Gd L1 (Nd.c Nn) a) → y ⊴ a →
    L.ψ p σ (f (L.into (L.<→◃ q) y)) ⊴ Nd.gm Nn a e) →
  L.lim (λ n → L.ψ p σ (f (L.into (L.<→◃ q) (δ₁ q f n)))) ⊴ Ψn L1 L1 pl fold Nn
fold1⊴ q f p σ pl (nd c lw nw t gm gk lk nk pk) b hk hm =
  l⊴ (λ n → ⊴l n (Chain1.outAt q f c lw nw gk lk nk pk b hk L1 gm
    (λ y Y → L.ψ p σ (f (L.into (L.<→◃ q) y)) ⊴ Y) hm n))

fold1≼ : ∀ {K} (q : ℓ₁ L.<ᴵ K) (f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K) →
  (∀ y → y ≅ y → f (L.into (L.<→◃ q) y) ≅ f (L.into (L.<→◃ q) y)) →
  .(pl : Plain L1) (w : Way B.zero L1) (Nn : NdR B.zero L1) →
  L.Ω ℓ₁ ⊴ Nd.c Nn →
  (∀ (y : T₁) a .(e : Gd L1 (Nd.c Nn) a) → y ⊴ a →
    L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y)) ⊴ Nd.gk Nn a e) →
  (∀ (y : T₁) a .(e : Gd L1 (Nd.c Nn) a) → y ⊴ a → y ≅ y →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (Nd.gm Nn a e)) →
  L.ψ⁰ (L.limᵢ q f) ≼ read (Ψn B.zero L1 pl w Nn)
fold1≼ q f same pl (keep () e) Nn b hk hm
fold1≼ q f same pl fold (nd c lw nw t gm gk lk nk pk) b hk hm =
  l≼ (λ n → ≼l n (Chain1.outAt q f c lw nw gk lk nk pk b hk B.zero gm
    (λ y Y → y ≅ y → L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read Y) hm n (δ₁-self q f same n)))
```

## 2 目标层 1

```agda
Ω₁⊴ψ₁ : ∀ (η : R₂) .(l : Lgl L2 η) .(nb : Nested L2 η) → L.Ω ℓ₁ ⊴ N.Ψ L1 L2 tt tt Y₁ η l nb
Ω₁⊴ψ₁ G.zero l nb = Ω⊴top
Ω₁⊴ψ₁ (G.suc a) l nb = ⊴l 0 (Ω₁⊴ψ₁ a l nb)
Ω₁⊴ψ₁ (G.lim f) l nb = ⊴l 0 (Ω₁⊴ψ₁ (f 0) (proj₂ l 0) (nb 0))
Ω₁⊴ψ₁ (G.lc (inj₁ _) c t g) l nb = ⊴l 0
  (Ω₁⊴ψ₁ (g c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (proj₂ (proj₂ (proj₂ (proj₂ l))) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (proj₂ (proj₂ (proj₂ nb)) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))))
Ω₁⊴ψ₁ (G.lc (inj₂ (inj₁ _)) c t g) l nb = ⊴b (λ e →
  Ω₁⊴ψ₁ (g c e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
Ω₁⊴ψ₁ (G.lc (inj₂ (inj₂ ())) c t g) l nb
Ω₁⊴ψ₁ (G.em _ a) l nb = Ω⊴Φ a l nb
Ω₁⊴ψ₁ G.top l nb = ⊴l 0 (Ω⊴Φ G.top tt tt)

C₀ : ∀ (x : Ext L1 B.zero) {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  ∀ {ℓ} (p : ℓ₁ L.<ᴵ ℓ) (σ : L.Simᴵ L.zero ℓ) →
  .(l : Lgl B.zero a) .(nb : Nested B.zero a) → L.ψ p σ y ⊴ N.Ψ L1 B.zero tt tt x a l nb
C₀ x z≼ a q p σ l nb = Ω⊴Φ₀ x a l nb
C₀ x (s≼s r) (G.suc a) refl p σ l nb = suc-step (C₀ x r a refl p σ l nb)
C₀ x (s≼s r) G.top refl p σ l nb = suc-step (C₀ x r G.zero refl p σ tt tt)
C₀ x (≼l n r) (G.lim f) refl p σ l nb = ⊴l n (C₀ x r (f n) refl p σ (proj₂ l n) (nb n))
C₀ x (l≼ h) a q p σ l nb = l⊴ (λ n → C₀ x (h n) a q p σ l nb)
C₀ x (≼i {p = ()} z ez r) a q p σ l nb
C₀ x (i≼ {p = ()} h) a q p σ l nb
C₀ x (≼u {r = ()} r) a q p σ l nb
C₀ x (u≼ {r = ()} r) a q p σ l nb

C₁ : ∀ {k} {y : L.Ordᶜ k} {a : R₁} → y ⊴ a →
  ∀ {ℓ} (p : ℓ₁ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(l : Lgl L1 a) .(nb : Nested L1 a) → L.ψ p σ y ⊴ N.Ψ L1 L1 tt tt X₁ a l nb
C₁ {a = a} z⊴ p σ l nb = Ω⊴Φ a l nb
C₁ (s⊴s r) p σ l nb = suc-step (C₁ r p σ l nb)
C₁ (⊴s r) p σ l nb = ⊴l 0 (C₁ r p σ l nb)
C₁ {a = G.lim F} (⊴l n r) p σ l nb = ⊴l n (C₁ r p σ (proj₂ l n) (nb n))
C₁ (l⊴ h) p σ l nb = l⊴ (λ n → C₁ (h n) p σ l nb)
C₁ (⊴b {c = c} {t = t} {g = g} h) p σ l nb = ⊴b (λ e →
  C₁ (h e) p σ (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
C₁ (nd {f = f} {c = c} {t = t} {g = g} base h) p σ l nb with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ L.zero) = nd base (λ y a e r →
  C₁ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via _ ())
... | injᶜ ()
C₁ (nt {f = f} h) p σ l nb with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ L.zero) = nd (s≼s z≼) (λ y a e r →
  C₁ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) r)) p σ (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via _ ())
... | injᶜ ()
C₁ (em⊴ {a = a} q) p σ l nb = C₀ (inS X₁) q a refl p σ l nb
C₁ (u⊴ r) p σ l nb = C₁ r p (λ q → σ (L.suc q)) l nb

C₂ : ∀ {k} {x : L.Ordᶜ k} {η : R₂} → x ⊴₂ η →
  ∀ {ℓ} (p : ℓ₁ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(l : Lgl L2 η) .(nb : Nested L2 η) → L.ψ p σ x ⊴ N.Ψ L1 L2 tt tt Y₁ η l nb
C₂ {η = η} z₂ p σ l nb = Ω₁⊴ψ₁ η l nb
C₂ (ss₂ r) p σ l nb = suc-step (C₂ r p σ l nb)
C₂ (s₂ r) p σ l nb = ⊴l 0 (C₂ r p σ l nb)
C₂ {η = G.lim F} (l₂ n r) p σ l nb = ⊴l n (C₂ r p σ (proj₂ l n) (nb n))
C₂ (ll₂ h) p σ l nb = l⊴ (λ n → C₂ (h n) p σ l nb)
C₂ (b1 {c = c} {t = t} {g = g} h) p σ l nb = ⊴l 0
  (C₂ (h (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))) p σ
    (proj₂ (proj₂ (proj₂ (proj₂ l))) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (proj₂ (proj₂ (proj₂ nb)) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))))
C₂ (b0 {c = c} {t = t} {g = g} h) p σ l nb = ⊴b (λ e →
  C₂ (h e) p σ (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
C₂ (nd1 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ l nb
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via () L.zero)
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ _ = fold1⊴ q f p σ tt (N.ndL L1 L2 tt tt Y₁ (inj₁ tt) c t g l nb) base
  (λ y a e r → C₂ (h y a e r) q (λ r → r)
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
  (λ y a e r → C₂ (h y a e r) p σ
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
C₂ (nd0 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ l nb
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via L.z≅ L.zero) = nd base (λ y a e r →
  C₂ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via _ ())
... | injᶜ ()
C₂ (nt₂ {q = q} {f = f} h) p σ l nb with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via () L.zero)
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ _ = fold1⊴ q f p σ tt (N.ndT L1 L1 tt tt (inS Y₁)) Ω⊴top
  (λ y a e r → C₂ (h y a r) q (λ r → r) (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
  (λ y a e r → C₂ (h y a r) p σ (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
C₂ (em₂ r) p σ l nb = C₁ r p σ l nb
C₂ (u₂ r) p σ l nb = C₂ r p (λ q → σ (L.suc q)) l nb
```

## 3 目标层 0

层号 0 的结点处的链与 [YiRawVal2](YiRawVal2.lagda.md) 的 `NodeChain` 相同，参照一侧的结点对字面证明 `q` 一般。

```agda
module NodeChain0 {K} (q : L.zero L.<ᴵ K) (f : L.U L.zero (L.<→◃ q) → L.Ordᶜ K)
  (same : ∀ (y : T₀) → f (L.into (L.<→◃ q) y) ≅ f (L.into (L.<→◃ q) y))
  (c : R) .(lw : Lgl B.zero c) .(nw : Nested B.zero c)
  (gm gk : (a : R) → .(Gd B.zero c a) → R)
  .(lk : ∀ a (e : Gd B.zero c a) → Lgl B.zero (gk a e))
  .(nk : ∀ a (e : Gd B.zero c a) → Nested B.zero (gk a e))
  (pk : ∀ a .(e : Gd B.zero c a) → Pos B.zero (gk a e))
  (base : V.𝟏 ≼ read c)
  (lowk : ∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (gk a e))
  (lowm : ∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (gm a e)) where

  open Chain B.zero tt c gk lk nk pk

  pts : ℕ → Pt B.zero c
  pts = iterate next (startᴸ B.zero c lw nw)

  δ : ℕ → T₀
  δ = iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.suc L.zero)

  herek : ∀ (p : Pt B.zero c) y → y ≼ read (at p) →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (step p)
  herek (pt a e) y r = lowk y a e r

  herem : ∀ (p : Pt B.zero c) y → y ≼ read (at p) →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (see B.zero gm p)
  herem (pt a e) y r = lowm y a e r

  chain-lower : ∀ n → δ n ≼ read (at (pts n))
  chain-lower zero = base
  chain-lower (suc n) =
    ≼-trans (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = q} {σ = λ r → r} (same (δ n)))))
      (plus≽ (at (pts n)) (step (pts n)) (herek (pts n) (δ n) (chain-lower n)))

  result : L.ψ⁰ (L.limᵢ q f) ≼ read (collapse B.zero gm (startᴸ B.zero c lw nw))
  result = l≼ (λ n → ≼l n (herem (pts n) (δ n) (chain-lower n)))

fold0≼ : ∀ {K} (q : L.zero L.<ᴵ K) (f : L.U L.zero (L.<→◃ q) → L.Ordᶜ K) →
  (∀ (y : T₀) → f (L.into (L.<→◃ q) y) ≅ f (L.into (L.<→◃ q) y)) →
  .(pl : Plain B.zero) (w : Way B.zero B.zero) (Nn : NdR B.zero B.zero) →
  V.𝟏 ≼ read (Nd.c Nn) →
  (∀ (y : T₀) a .(e : Gd B.zero (Nd.c Nn) a) → y ≼ read a →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (Nd.gk Nn a e)) →
  (∀ (y : T₀) a .(e : Gd B.zero (Nd.c Nn) a) → y ≼ read a →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (Nd.gm Nn a e)) →
  L.ψ⁰ (L.limᵢ q f) ≼ read (Ψn B.zero B.zero pl w Nn)
fold0≼ q f same pl (keep () e) Nn b hk hm
fold0≼ q f same pl fold (nd c lw nw t gm gk lk nk pk) b hk hm =
  NodeChain0.result q f same c lw nw gm gk lk nk pk b hk hm

Own₀ : Ext B.zero L2
Own₀ = N.own L2 tt tt (inj₂ (inj₁ tt))

D : ∀ (xe : Ext B.zero L2) {k} {x : L.Ordᶜ k} {η : R₂} → x ⊴₂ η → x ≅ x →
  .(l : Lgl L2 η) .(nb : Nested L2 η) → L.ψ⁰ x ≼ read (N.Ψ B.zero L2 tt tt xe η l nb)
D xe {η = η} z₂ s l nb = one≼ L2 tt tt xe η l nb
D xe {η = G.suc η} (ss₂ r) s l nb =
  suc-lower (N.Ψ B.zero L2 tt tt xe η l nb) (D xe r (s≅⁻ s) l nb)
D xe (s₂ r) s l nb = ≼l 0 (D xe r s l nb)
D xe {η = G.lim F} (l₂ n r) s l nb = ≼l n (D xe r s (proj₂ l n) (nb n))
D xe (ll₂ h) s l nb = l≼ (λ n → D xe (h n) (l≅⁻ s n) l nb)
D xe (b1 {c = c} {t = t} {g = g} h) s l nb =
  ΨN-first L2 tt (inj₁ tt) (wayOf xe (inj₁ tt)) (N.ndL B.zero L2 tt tt xe (inj₁ tt) c t g l nb)
    (λ e → D xe (h e) s (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
D xe (b0 {c = c} {t = t} {g = g} h) s l nb =
  ΨN-first L2 tt (inj₂ (inj₁ tt)) (wayOf xe (inj₂ (inj₁ tt)))
    (N.ndL B.zero L2 tt tt xe (inj₂ (inj₁ tt)) c t g l nb)
    (λ e → D xe (h e) s (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
D xe (nd1 {q = q} {f = f} {c = c} {t = t} {g = g} base h) s l nb =
  fold1≼ q f (lᵢ≅⁻ s) tt (wayOf xe (inj₁ tt)) (N.ndL B.zero L2 tt tt xe (inj₁ tt) c t g l nb) base
    (λ y a e r → C₂ (h y a e r) q (λ r → r)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
    (λ y a e r sy → D xe (h y a e r) (lᵢ≅⁻ s y sy)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
D xe (nd0 {q = q} {f = f} {c = c} {t = t} {g = g} base h) s l nb =
  fold0≼ q f (λ y → lᵢ≅⁻ s y (L.≅-refl⁰ y)) tt (wayOf xe (inj₂ (inj₁ tt)))
    (N.ndL B.zero L2 tt tt xe (inj₂ (inj₁ tt)) c t g l nb) base
    (λ y a e r → D Own₀ (h y a e r) (lᵢ≅⁻ s y (L.≅-refl⁰ y))
      (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
    (λ y a e r → D xe (h y a e r) (lᵢ≅⁻ s y (L.≅-refl⁰ y))
      (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
D xe (nt₂ {q = q} {f = f} h) s l nb =
  fold1≼ q f (lᵢ≅⁻ s) tt (wayOf xe (inj₁ tt)) (N.ndT B.zero L1 tt tt (inS xe)) Ω⊴top
    (λ y a e r → C₂ (h y a r) q (λ r → r) (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (λ y a e r sy → D xe (h y a r) (lᵢ≅⁻ s y sy) (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
D xe (em₂ r) s l nb = fold-lower₁ (inS xe) r s l nb
D xe (u₂ r) s l nb = D xe r (up≅⁻ s) l nb
```

## 4 接口与 ψ₀(Ω₃)

```agda
interface₂ : Interface 2
interface₂ = record
  { Rel = λ x η → x ⊴₂ η
  ; start = Ω₂⊴top
  ; step = λ r l nb → B₂ r L.zero (λ q → L.suc q) l nb
  ; absorb = λ θ r → ⊴₂-+ˡ θ r
  ; lower = λ y r s l nb → D y r s l nb
  }

lower₃ : L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read (closed (fin 3) tt tt)
lower₃ = FromInterface.theorem 2 interface₂

lower₃ᵐ : L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read (closedᵐ (fin 3) tt tt)
lower₃ᵐ = FromInterface.theoremᵐ 2 interface₂
```

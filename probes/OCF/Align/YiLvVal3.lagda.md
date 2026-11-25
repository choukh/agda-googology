# YiLvFold 第 4 层：ψ₀(Ω₃) 的值下界

**验收文件，档位：编译定理 (下界，不是同值)。** `lower₃`：参照 `ψ⁰ (Ω ⟨3⟩)` ≼ 读回的 `foldᶠ 3`，经接口 `interface₂`。
范例里没有的一处：目标层 1 上层号 1 的结点要折叠 (`C₂`；链在 `Raw 1` 里，关系是 [YiLvVal2](YiLvVal2.lagda.md) 的 `_⊴_`)。
第 2 层的关系与目标层 2 的引理在 [YiLvVal3Base](YiLvVal3Base.lagda.md)。不否定任何路线；一般层号见 [YiLvValFin](YiLvValFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvVal3 where

open import OCF.Align.YiLvVal3Base

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Nested; Gd; Lgl)
open import OCF.Align.RR5IrrCheck using (up; upT; cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (R; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt; at)
open import OCF.Align.YiLvFoldAdd using (plus; copies; successor)
open import OCF.Align.YiLvFoldBase using (Dom; dom-at; startᴸ; module Node)
open import OCF.Align.YiLvFoldFin using (fin; ψ; next; out; foldᶠ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase
open import OCF.Align.YiLvVal2
  using (ℓ₁; ℓ₂; T₀; T₁; L1; R₁; _⊴_; z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; nt; em⊴; u⊴;
         ⊴-+ˡ; suc-step; Ω⊴top; Ω⊴Φ; Ω⊴Φ₀; tr⁻≼; fold-lower; s≅⁻; l≅⁻)
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
```

## 5 目标层 1：层号 1 的结点折叠

`Chain1` 是层号 1 的结点上的两条链：参照一侧 `δ` 每步是目标层 1 的折叠，被验收一侧是 `Raw 1` 里的加法链；
链点之间是 `_⊴_`。`outAt` 把链的每一点送到任一观察关系。

```agda
δ₁ : ∀ {K} (q : ℓ₁ L.<ᴵ K) (f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K) → ℕ → T₁
δ₁ q f = iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.Ω ℓ₁)

δ₁-self : ∀ {K} (q : ℓ₁ L.<ᴵ K) (f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K) →
  (∀ y → y ≅ y → f (L.into (L.<→◃ q) y) ≅ f (L.into (L.<→◃ q) y)) →
  ∀ n → δ₁ q f n ≅ δ₁ q f n
δ₁-self q f same zero = L.Ω-≅ (L.≅ᴵ-refl ℓ₁)
δ₁-self q f same (suc n) =
  L.ψ-≅ {p = q} {σ = λ r → r} {p′ = q} {σ′ = λ r → r} (L.≅ᴵ-refl ℓ₁)
    (same (δ₁ q f n) (δ₁-self q f same n))

module Chain1 {K} (q : ℓ₁ L.<ᴵ K) (f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K)
  (c : R₁) .(w : Lgl L1 c) .(b : Nested L1 c) (t : LF)
  (g : (a : R₁) → .(Gd L1 c a) → LF) .(d : Dom (B.lc L1 c w b t g))
  (base : L.Ω ℓ₁ ⊴ c)
  (stepL : ∀ (y : T₁) a .(e : Gd L1 c a) → y ⊴ a →
    L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y)) ⊴ out L1 L1 c w b t g d (pt a e)) where

  pts : ℕ → Pt L1 c
  pts = iterate (next L1 c w b t g d) (startᴸ L1 c w b)

  stepAt : ∀ (p : Pt L1 c) y → y ⊴ at p →
    L.ψ q (λ r → r) (f (L.into (L.<→◃ q) y)) ⊴ out L1 L1 c w b t g d p
  stepAt (pt a e) y r = stepL y a e r

  chain : ∀ n → δ₁ q f n ⊴ at (pts n)
  chain zero = base
  chain (suc n) = ⊴-+ˡ (at (pts n)) (stepAt (pts n) (δ₁ q f n) (chain n))

  outAt : ∀ m (O : T₁ → Raw m → Set) →
    (∀ (y : T₁) a .(e : Gd L1 c a) → y ⊴ a → O y (out m L1 c w b t g d (pt a e))) →
    ∀ n → O (δ₁ q f n) (out m L1 c w b t g d (pts n))
  outAt m O h n = go (pts n) (chain n) where
    go : ∀ p → δ₁ q f n ⊴ at p → O (δ₁ q f n) (out m L1 c w b t g d p)
    go (pt a e) r = h (δ₁ q f n) a e r

Ω₁⊴ψ₁ : ∀ (η : R₂) .(nb : Nested L2 η) .(d : Dom (up L2 η nb)) →
  L.Ω ℓ₁ ⊴ ψ L1 (up L2 η nb) d
Ω₁⊴ψ₁ G.zero nb d = Ω⊴top
Ω₁⊴ψ₁ (G.suc a) nb d = ⊴l 0 (Ω₁⊴ψ₁ a nb d)
Ω₁⊴ψ₁ (G.lim f) nb d =
  ⊴l 0 (Ω₁⊴ψ₁ (f 0) (nb 0) (dom-at (λ n → up L2 (f n) (nb n)) d 0))
Ω₁⊴ψ₁ (G.lc (inj₁ _) c t g) nb d = ⊴l 0
  (Ω₁⊴ψ₁ (g c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (proj₂ (proj₂ (proj₂ nb)) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (br₂₁ c t g nb d c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))))
Ω₁⊴ψ₁ (G.lc (inj₂ (inj₁ _)) c t g) nb d = ⊴b (λ e →
  Ω₁⊴ψ₁ (g c e) (proj₂ (proj₂ (proj₂ nb)) c e) (br₂₀ c t g nb d c e))
Ω₁⊴ψ₁ (G.lc (inj₂ (inj₂ ())) c t g) nb d
Ω₁⊴ψ₁ (G.em _ a) nb d = Ω⊴Φ a nb d
Ω₁⊴ψ₁ G.top nb d = ⊴l 0 (Ω⊴Φ G.top tt (br₂T d G.top (inj₁ refl , tt , tt)))

C₀ : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  ∀ {ℓ} (p : ℓ₁ L.<ᴵ ℓ) (σ : L.Simᴵ L.zero ℓ) →
  .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  L.ψ p σ y ⊴ ψ L1 (up B.zero a nb) d
C₀ z≼ a q p σ nb d = Ω⊴Φ₀ a nb d
C₀ (s≼s r) (G.suc a) refl p σ nb d = suc-step (C₀ r a refl p σ nb d)
C₀ (s≼s r) G.top refl p σ nb d = suc-step (C₀ r G.zero refl p σ tt (tt , tt , tt))
C₀ (≼l n r) (G.lim f) refl p σ nb d =
  ⊴l n (C₀ r (f n) refl p σ (nb n) (dom-at (λ n → up B.zero (f n) (nb n)) d n))
C₀ (l≼ h) a q p σ nb d = l⊴ (λ n → C₀ (h n) a q p σ nb d)
C₀ (≼i {p = ()} x ex r) a q p σ nb d
C₀ (i≼ {p = ()} h) a q p σ nb d
C₀ (≼u {r = ()} r) a q p σ nb d
C₀ (u≼ {r = ()} r) a q p σ nb d

C₁ : ∀ {k} {y : L.Ordᶜ k} {a : R₁} → y ⊴ a →
  ∀ {ℓ} (p : ℓ₁ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(nb : Nested L1 a) .(d : Dom (up L1 a nb)) → L.ψ p σ y ⊴ ψ L1 (up L1 a nb) d
C₁ {a = a} z⊴ p σ nb d = Ω⊴Φ a nb d
C₁ (s⊴s r) p σ nb d = suc-step (C₁ r p σ nb d)
C₁ (⊴s r) p σ nb d = ⊴l 0 (C₁ r p σ nb d)
C₁ {a = G.lim F} (⊴l n r) p σ nb d =
  ⊴l n (C₁ r p σ (nb n) (dom-at (λ n → up L1 (F n) (nb n)) d n))
C₁ (l⊴ h) p σ nb d = l⊴ (λ n → C₁ (h n) p σ nb d)
C₁ (⊴b {c = c} {t = t} {g = g} h) p σ nb d = ⊴b (λ e →
  C₁ (h e) p σ (proj₂ (proj₂ (proj₂ nb)) c e) (br₁₀ c t g nb d c e))
C₁ (nd {f = f} {c = c} {t = t} {g = g} base h) p σ nb d with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ L.zero) = nd base (λ y a e r →
  C₁ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ nb)) a e) (br₁₀ c t g nb d a e))
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via _ ())
... | injᶜ ()
C₁ (nt {f = f} h) p σ nb d with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ L.zero) = nd (s≼s z≼) (λ y a e r →
  C₁ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) r)) p σ (proj₂ (proj₂ e)) (br₁T d a e))
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via _ ())
... | injᶜ ()
C₁ (em⊴ {a = a} q) p σ nb d = C₀ q a refl p σ nb d
C₁ (u⊴ r) p σ nb d = C₁ r p (λ q → σ (L.suc q)) nb d

C₂ : ∀ {k} {x : L.Ordᶜ k} {η : R₂} → x ⊴₂ η →
  ∀ {ℓ} (p : ℓ₁ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(nb : Nested L2 η) .(d : Dom (up L2 η nb)) → L.ψ p σ x ⊴ ψ L1 (up L2 η nb) d
C₂ {η = η} z₂ p σ nb d = Ω₁⊴ψ₁ η nb d
C₂ (ss₂ r) p σ nb d = suc-step (C₂ r p σ nb d)
C₂ (s₂ r) p σ nb d = ⊴l 0 (C₂ r p σ nb d)
C₂ {η = G.lim F} (l₂ n r) p σ nb d =
  ⊴l n (C₂ r p σ (nb n) (dom-at (λ n → up L2 (F n) (nb n)) d n))
C₂ (ll₂ h) p σ nb d = l⊴ (λ n → C₂ (h n) p σ nb d)
C₂ (b1 {c = c} {t = t} {g = g} h) p σ nb d = ⊴l 0
  (C₂ (h (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))) p σ
    (proj₂ (proj₂ (proj₂ nb)) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (br₂₁ c t g nb d c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))))
C₂ (b0 {c = c} {t = t} {g = g} h) p σ nb d = ⊴b (λ e →
  C₂ (h e) p σ (proj₂ (proj₂ (proj₂ nb)) c e) (br₂₀ c t g nb d c e))
C₂ (nd1 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ nb d
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via () L.zero)
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ _ = l⊴ (λ n → ⊴l n
  (Chain1.outAt q f c (proj₁ nb) (proj₁ (proj₂ nb))
    (up L2 t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up L2 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d base
    (λ y a e r → C₂ (h y a e r) q (λ r → r)
      (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₁ c t g nb d a e))
    L1 (λ y Y → L.ψ p σ (f (L.into (L.<→◃ q) y)) ⊴ Y)
    (λ y a e r → C₂ (h y a e r) p σ
      (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₁ c t g nb d a e))
    n))
C₂ (nd0 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ nb d
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via L.z≅ L.zero) = nd base (λ y a e r →
  C₂ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₀ c t g nb d a e))
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via _ ())
... | injᶜ ()
C₂ (nt₂ {q = q} {f = f} h) p σ nb d with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via () L.zero)
... | injᵃ (L.via _ (L.suc ()))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ _ = l⊴ (λ n → ⊴l n
  (Chain1.outAt q f G.top (cO-Lgl L1) (cO-Nested L1) (upT L1)
    (λ a e → up L1 a (proj₂ (proj₂ e))) d Ω⊴top
    (λ y a e r → C₂ (h y a r) q (λ r → r) (proj₂ (proj₂ e)) (br₂T d a e))
    L1 (λ y Y → L.ψ p σ (f (L.into (L.<→◃ q) y)) ⊴ Y)
    (λ y a e r → C₂ (h y a r) p σ (proj₂ (proj₂ e)) (br₂T d a e))
    n))
C₂ (em₂ r) p σ nb d = C₁ r p σ nb d
C₂ (u₂ r) p σ nb d = C₂ r p (λ q → σ (L.suc q)) nb d
```

## 6 目标层 0

```agda
module Chain0 {K} (q : L.zero L.<ᴵ K) (f : L.U L.zero (L.<→◃ q) → L.Ordᶜ K)
  (same : ∀ (y : T₀) → f (L.into (L.<→◃ q) y) ≅ f (L.into (L.<→◃ q) y))
  (c : R) .(w : Lgl B.zero c) .(b : Nested B.zero c) (t : LF)
  (g : (a : R) → .(Gd B.zero c a) → LF) .(d : Dom (B.lc B.zero c w b t g))
  (base : V.𝟏 ≼ read c)
  (low : ∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (out B.zero B.zero c w b t g d (pt a e))) where

  pts : ℕ → Pt B.zero c
  pts = iterate (next B.zero c w b t g d) (startᴸ B.zero c w b)

  δ : ℕ → T₀
  δ = iter (λ x → L.ψ q (λ r → r) (f (L.into (L.<→◃ q) x))) (L.suc L.zero)

  here : ∀ (p : Pt B.zero c) y → y ≼ read (at p) →
    L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read (out B.zero B.zero c w b t g d p)
  here (pt a e) y r = low y a e r

  chain-lower : ∀ n → δ n ≼ read (at (pts n))
  chain-lower zero = base
  chain-lower (suc n) =
    ≼-trans (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = q} {σ = λ r → r} (same (δ n)))))
      (plus≽ (at (pts n)) (out B.zero B.zero c w b t g d (pts n))
        (here (pts n) (δ n) (chain-lower n)))

  node-lower : L.ψ⁰ (L.limᵢ q f) ≼ read (ψ B.zero (B.lc B.zero c w b t g) d)
  node-lower = l≼ (λ n → ≼l n (here (pts n) (δ n) (chain-lower n)))

lᵢ≅⁻ : ∀ {j K} {q : j L.<ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} →
  L.limᵢ q f ≅ L.limᵢ q f → ∀ y → y ≅ y →
  f (L.into (L.<→◃ q) y) ≅ f (L.into (L.<→◃ q) y)
lᵢ≅⁻ {q = q} (L.lᵢ≅ e h) y s = h y y (L.≅→R (L.<→◃ q) s)

up≅⁻ : ∀ {k} {y : L.Ordᶜ k} → L.up {k = k} L.zero y ≅ L.up {k = k} L.zero y → y ≅ y
up≅⁻ (L.upˡ e) = L.≅-trans e (L.≅-sym e)
up≅⁻ (L.upʳ e) = L.≅-trans (L.≅-sym e) e

D : ∀ {k} {x : L.Ordᶜ k} {η : R₂} → x ⊴₂ η → x ≅ x →
  .(nb : Nested L2 η) .(d : Dom (up L2 η nb)) →
  L.ψ⁰ x ≼ read (ψ B.zero (up L2 η nb) d)
D {η = η} z₂ s nb d = one≼fold (up L2 η nb) d
D {η = G.suc η} (ss₂ r) s nb d =
  suc-lower (ψ B.zero (up L2 η nb) d) (D r (s≅⁻ s) nb d)
D (s₂ r) s nb d = ≼l 0 (D r s nb d)
D {η = G.lim F} (l₂ n r) s nb d =
  ≼l n (D r s (nb n) (dom-at (λ n → up L2 (F n) (nb n)) d n))
D (ll₂ h) s nb d = l≼ (λ n → D (h n) (l≅⁻ s n) nb d)
D (b1 {c = c} {t = t} {g = g} h) s nb d = ≼l 0
  (D (h (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))) s
    (proj₂ (proj₂ (proj₂ nb)) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (br₂₁ c t g nb d c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))))
D (b0 {c = c} {t = t} {g = g} h) s nb d = ≼l 0
  (D (h (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))) s
    (proj₂ (proj₂ (proj₂ nb)) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (br₂₀ c t g nb d c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))))
D (nd1 {q = q} {f = f} {c = c} {t = t} {g = g} base h) s nb d = l≼ (λ n → ≼l n
  (Chain1.outAt q f c (proj₁ nb) (proj₁ (proj₂ nb))
    (up L2 t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up L2 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d base
    (λ y a e r → C₂ (h y a e r) q (λ r → r)
      (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₁ c t g nb d a e))
    B.zero (λ y Y → y ≅ y → L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read Y)
    (λ y a e r sy → D (h y a e r) (lᵢ≅⁻ s y sy)
      (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₁ c t g nb d a e))
    n (δ₁-self q f (lᵢ≅⁻ s) n)))
D (nd0 {q = q} {f = f} {c = c} {t = t} {g = g} base h) s nb d =
  Chain0.node-lower q f (λ y → lᵢ≅⁻ s y (L.≅-refl⁰ y)) c (proj₁ nb) (proj₁ (proj₂ nb))
    (up L2 t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up L2 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d base
    (λ y a e r → D (h y a e r) (lᵢ≅⁻ s y (L.≅-refl⁰ y))
      (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₀ c t g nb d a e))
D (nt₂ {q = q} {f = f} h) s nb d = l≼ (λ n → ≼l n
  (Chain1.outAt q f G.top (cO-Lgl L1) (cO-Nested L1) (upT L1)
    (λ a e → up L1 a (proj₂ (proj₂ e))) d Ω⊴top
    (λ y a e r → C₂ (h y a r) q (λ r → r) (proj₂ (proj₂ e)) (br₂T d a e))
    B.zero (λ y Y → y ≅ y → L.ψ⁰ (f (L.into (L.<→◃ q) y)) ≼ read Y)
    (λ y a e r sy → D (h y a r) (lᵢ≅⁻ s y sy) (proj₂ (proj₂ e)) (br₂T d a e))
    n (δ₁-self q f (lᵢ≅⁻ s) n)))
D (em₂ r) s nb d = fold-lower r s nb d
D (u₂ r) s nb d = D r (up≅⁻ s) nb d
```

## 7 接口与 ψ₀(Ω₃)

```agda
interface₂ : Interface 2
interface₂ = record
  { Rel = λ x η → x ⊴₂ η
  ; start = Ω₂⊴top
  ; step = λ r nb d → B₂ r L.zero (λ q → L.suc q) nb d
  ; absorb = λ θ r → ⊴₂-+ˡ θ r
  ; lower = D
  }

lower₃ : L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read (foldᶠ 3)
lower₃ = FromInterface.theorem 2 interface₂
```

# YiLvFold 第 4 层：ψ₀(Ω₂) 的值下界

**验收文件，档位：编译定理 (下界，不是同值)。** `lower₂`：参照 `ψ⁰ (Ω ⟨2⟩)` ≼ 读回的 `foldᶠ 2`。办法同
[YiIrrFbValue](YiIrrFbValue.lagda.md)：跨两族的逐点前序 `_⊴_` (`Level` 第 0、1 层的树对 `Raw 1` 的值)，给出接口 `interface₁`
([YiLvValBase](YiLvValBase.lagda.md) §3)。与范例的两处不同：证据全是无关参数；结点上 "压在第一支之下" 换成 "压在起点那一支之下" (`⊴b`)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvVal2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
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
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4MonoFragment as MF
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)

ℓ₁ ℓ₂ : L.Ordᴵ
ℓ₁ = L.suc L.zero
ℓ₂ = L.suc ℓ₁

T₀ T₁ : Set
T₀ = L.Ordᶜ L.zero
T₁ = L.Ordᶜ ℓ₁

L1 : LF
L1 = B.suc B.zero

R₁ : Set
R₁ = Raw L1
```

## 1 逐点前序

`⊴b`：压在起点 (下界 `c`) 那一支之下，就压在结点之下；分支的守卫是无关的，所以前提对一切守卫写。
`nd`, `nt` 的分支前提也只要无关的守卫：链点的守卫是无关的。

```agda
infix 4 _⊴_
data _⊴_ : ∀ {k} → L.Ordᶜ k → R₁ → Set where
  z⊴ : ∀ {k} {η : R₁} → _⊴_ {k} L.zero η
  s⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → L.suc x ⊴ G.suc η
  ⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ⊴ G.suc η
  ⊴l : ∀ {k} {x : L.Ordᶜ k} {F : ℕ → R₁} n → x ⊴ F n → x ⊴ G.lim F
  l⊴ : ∀ {k} {F : ℕ → L.Ordᶜ k} {η} → (∀ n → F n ⊴ η) → L.lim F ⊴ η
  ⊴b : ∀ {k} {x : L.Ordᶜ k} {c t} {g : (a : R) → .(Gd B.zero c a) → R₁} →
    (∀ .(e : Gd B.zero c c) → x ⊴ g c e) → x ⊴ G.lc (inj₁ tt) c t g
  nd : ∀ {f : T₀ → T₁} {c t} {g : (a : R) → .(Gd B.zero c a) → R₁} →
    V.𝟏 ≼ read c →
    (∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a → f y ⊴ g a e) →
    L.limᵢ {i = L.zero} L.zero f ⊴ G.lc (inj₁ tt) c t g
  nt : ∀ {f : T₀ → T₁} →
    (∀ (y : T₀) a → y ≼ read a → f y ⊴ G.em tt a) →
    L.limᵢ {i = L.zero} L.zero f ⊴ G.top
  em⊴ : ∀ {y : T₀} {a} → y ≼ read a → y ⊴ G.em tt a
  u⊴ : ∀ {y : T₀} {η} → y ⊴ η → L.up {k = L.zero} L.zero y ⊴ η
```

## 2 加法

`plus L1 θ (em tt a)` 是 `θ` 加上嵌进来的第 0 层的值，对 `a` 逐构造子展开。

```agda
⊴-embed : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → ∀ a → x ⊴ plus L1 η (G.em tt a)
⊴-embed p G.zero = p
⊴-embed p (G.suc a) = ⊴s (⊴-embed p a)
⊴-embed p (G.lim f) = ⊴l 0 (⊴-embed p (f 0))
⊴-embed p (G.lc () c t g)
⊴-embed p (G.em () a)
⊴-embed p G.top = ⊴s p

⊴-+ʳ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → ∀ η′ → x ⊴ plus L1 η η′
⊴-+ʳ p G.zero = p
⊴-+ʳ p (G.suc y) = ⊴s (⊴-+ʳ p y)
⊴-+ʳ p (G.lim f) = ⊴l 0 (⊴-+ʳ p (f 0))
⊴-+ʳ p (G.lc (inj₁ _) c t g) = ⊴b (λ e → ⊴-+ʳ p (g c e))
⊴-+ʳ p (G.lc (inj₂ ()) c t g)
⊴-+ʳ p (G.em _ a) = ⊴-embed p a
⊴-+ʳ p G.top = ⊴b (λ e → ⊴s p)

em-shift : ∀ θ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a → y ⊴ plus L1 θ (G.em tt a)
em-shift θ z≼ a q = z⊴
em-shift θ (s≼s p) (G.suc a) refl = s⊴s (em-shift θ p a refl)
em-shift θ (s≼s p) G.top refl = s⊴s (em-shift θ p G.zero refl)
em-shift θ (≼l n p) (G.lim f) refl = ⊴l n (em-shift θ p (f n) refl)
em-shift θ (l≼ h) a q = l⊴ (λ n → em-shift θ (h n) a q)
em-shift θ (≼i {p = ()} x ex p) a q
em-shift θ (i≼ {p = ()} h) a q
em-shift θ (≼u {r = ()} p) a q
em-shift θ (u≼ {r = ()} p) a q

σ₀ : L.Simᴵ L.zero ℓ₁
σ₀ q = L.suc q

add-em : ∀ {x : T₁} {η} → x ⊴ η → ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  L.add x σ₀ y ⊴ plus L1 η (G.em tt a)
add-em px z≼ a q = ⊴-embed px a
add-em px (s≼s p) (G.suc a) refl = s⊴s (add-em px p a refl)
add-em px (s≼s p) G.top refl = s⊴s (add-em px p G.zero refl)
add-em px (≼l n p) (G.lim f) refl = ⊴l n (add-em px p (f n) refl)
add-em px (l≼ h) a q = l⊴ (λ n → add-em px (h n) a q)
add-em px (≼i {p = ()} x ex p) a q
add-em px (i≼ {p = ()} h) a q
add-em px (≼u {r = ()} p) a q
add-em px (u≼ {r = ()} p) a q

⊴-add₀ : ∀ {x : T₁} {η} → x ⊴ η → ∀ {y : T₀} {η′} → y ⊴ η′ →
  L.add x σ₀ y ⊴ plus L1 η η′
⊴-add₀ px {η′ = η′} z⊴ = ⊴-+ʳ px η′
⊴-add₀ px (s⊴s q) = s⊴s (⊴-add₀ px q)
⊴-add₀ px (⊴s q) = ⊴s (⊴-add₀ px q)
⊴-add₀ px (⊴l n q) = ⊴l n (⊴-add₀ px q)
⊴-add₀ px (l⊴ h) = l⊴ (λ n → ⊴-add₀ px (h n))
⊴-add₀ px (⊴b h) = ⊴b (λ e → ⊴-add₀ px (h e))
⊴-add₀ px (em⊴ {a = a} q) = add-em px q a refl

⊴-add₁ : ∀ {x : T₁} {η} → x ⊴ η → ∀ {x′ : T₁} {η′} → x′ ⊴ η′ →
  (x L.+ x′) ⊴ plus L1 η η′
⊴-add₁ px {η′ = η′} z⊴ = ⊴-+ʳ px η′
⊴-add₁ px (s⊴s q) = s⊴s (⊴-add₁ px q)
⊴-add₁ px (⊴s q) = ⊴s (⊴-add₁ px q)
⊴-add₁ px (⊴l n q) = ⊴l n (⊴-add₁ px q)
⊴-add₁ px (l⊴ h) = l⊴ (λ n → ⊴-add₁ px (h n))
⊴-add₁ px (⊴b h) = ⊴b (λ e → ⊴-add₁ px (h e))
⊴-add₁ px (nd b h) = nd b (λ y a e q → ⊴-add₁ px (h y a e q))
⊴-add₁ px (nt h) = nd (s≼s z≼) (λ y a e q → ⊴-add₁ px (h y a q))
⊴-add₁ px (u⊴ q) = ⊴-add₀ px q

⊴-+ˡ : ∀ θ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ⊴ plus L1 θ η
⊴-+ˡ θ z⊴ = z⊴
⊴-+ˡ θ (s⊴s p) = s⊴s (⊴-+ˡ θ p)
⊴-+ˡ θ (⊴s p) = ⊴s (⊴-+ˡ θ p)
⊴-+ˡ θ (⊴l n p) = ⊴l n (⊴-+ˡ θ p)
⊴-+ˡ θ (l⊴ h) = l⊴ (λ n → ⊴-+ˡ θ (h n))
⊴-+ˡ θ (⊴b h) = ⊴b (λ e → ⊴-+ˡ θ (h e))
⊴-+ˡ θ (nd b h) = nd b (λ y a e q → ⊴-+ˡ θ (h y a e q))
⊴-+ˡ θ (nt h) = nd (s≼s z≼) (λ y a e q → ⊴-+ˡ θ (h y a q))
⊴-+ˡ θ (em⊴ {a = a} q) = em-shift θ q a refl
⊴-+ˡ θ (u⊴ p) = u⊴ (⊴-+ˡ θ p)
```

## 3 目标层 1 的折叠

`Φ η` 是被验收一侧的 "读回再折叠"。在第 1 层的输入上目标层 1 不折叠任何结点：层号 0 的结点保留在槽位 `inj₁ tt`
(`wayᵇ (fin 1) 0` 化简为保留)；参照一侧 `Ψ₁` 在结点处穿透，分支先过一次层间搬运 `tr⁻`，值不变。

```agda
Φ : (η : R₁) → .(nb : Nested L1 η) → .(Dom (up L1 η nb)) → R₁
Φ η nb d = ψ L1 (up L1 η nb) d

Ψ₁ : T₁ → T₁
Ψ₁ = Ψ 1

Ψ₀ : T₀ → T₁
Ψ₀ = L.ψ {i = ℓ₁} {k = L.zero} {ℓ = ℓ₂} L.zero (λ r → L.suc (L.suc r))

Ω⊴top : L.Ω ℓ₁ ⊴ G.top
Ω⊴top = nt (λ y a q → u⊴ (em⊴ q))

Ω⊴Φ₀ : ∀ a .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  L.Ω ℓ₁ ⊴ ψ L1 (up B.zero a nb) d
Ω⊴Φ₀ G.zero nb d = Ω⊴top
Ω⊴Φ₀ (G.suc a) nb d = ⊴l 0 (Ω⊴Φ₀ a nb d)
Ω⊴Φ₀ (G.lim f) nb d =
  ⊴l 0 (Ω⊴Φ₀ (f 0) (nb 0) (dom-at (λ n → up B.zero (f n) (nb n)) d 0))
Ω⊴Φ₀ (G.lc () c t g) nb d
Ω⊴Φ₀ (G.em () a) nb d
Ω⊴Φ₀ G.top nb d = ⊴l 0 Ω⊴top

Ω⊴Φ : ∀ η .(nb : Nested L1 η) .(d : Dom (up L1 η nb)) → L.Ω ℓ₁ ⊴ Φ η nb d
Ω⊴Φ G.zero nb d = Ω⊴top
Ω⊴Φ (G.suc η) nb d = ⊴l 0 (Ω⊴Φ η nb d)
Ω⊴Φ (G.lim f) nb d =
  ⊴l 0 (Ω⊴Φ (f 0) (nb 0) (dom-at (λ n → up L1 (f n) (nb n)) d 0))
Ω⊴Φ (G.lc (inj₁ _) c t g) nb d = ⊴b (λ e →
  Ω⊴Φ (g c e) (proj₂ (proj₂ (proj₂ nb)) c e)
    (Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
      (up L1 t (proj₁ (proj₂ (proj₂ nb))))
      (λ a e′ → up L1 (g a e′) (proj₂ (proj₂ (proj₂ nb)) a e′)) d c e))
Ω⊴Φ (G.lc (inj₂ ()) c t g) nb d
Ω⊴Φ (G.em _ a) nb d = Ω⊴Φ₀ a nb d
Ω⊴Φ G.top nb d = ⊴b (λ e → ⊴l 0 Ω⊴top)

copies-⊴ : ∀ {A : T₁} {β} → A ⊴ β → ∀ n →
  iter (A L.+_) L.zero (suc n) ⊴ copies L1 β n
copies-⊴ p zero = p
copies-⊴ p (suc n) = ⊴-add₁ p (copies-⊴ p n)

suc-step : ∀ {A : T₁} {β} → A ⊴ β →
  L.lim (iter (A L.+_) L.zero) ⊴ successor L1 β
suc-step p = l⊴ λ where
  zero → z⊴
  (suc n) → ⊴l n (copies-⊴ p n)

Ψ₀⊴Φ₀ : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  Ψ₀ y ⊴ ψ L1 (up B.zero a nb) d
Ψ₀⊴Φ₀ z≼ a q nb d = Ω⊴Φ₀ a nb d
Ψ₀⊴Φ₀ (s≼s p) (G.suc a) refl nb d = suc-step (Ψ₀⊴Φ₀ p a refl nb d)
Ψ₀⊴Φ₀ (s≼s p) G.top refl nb d = suc-step (Ψ₀⊴Φ₀ p G.zero refl tt (tt , tt , tt))
Ψ₀⊴Φ₀ (≼l n p) (G.lim f) refl nb d =
  ⊴l n (Ψ₀⊴Φ₀ p (f n) refl (nb n) (dom-at (λ n → up B.zero (f n) (nb n)) d n))
Ψ₀⊴Φ₀ (l≼ h) a q nb d = l⊴ (λ n → Ψ₀⊴Φ₀ (h n) a q nb d)
Ψ₀⊴Φ₀ (≼i {p = ()} x ex p) a q nb d
Ψ₀⊴Φ₀ (i≼ {p = ()} h) a q nb d
Ψ₀⊴Φ₀ (≼u {r = ()} p) a q nb d
Ψ₀⊴Φ₀ (u≼ {r = ()} p) a q nb d

Ψ₀⊴Φ : ∀ {y : T₀} {η} → y ⊴ η → .(nb : Nested L1 η) .(d : Dom (up L1 η nb)) →
  Ψ₀ y ⊴ Φ η nb d
Ψ₀⊴Φ {η = η} z⊴ nb d = Ω⊴Φ η nb d
Ψ₀⊴Φ (s⊴s p) nb d = suc-step (Ψ₀⊴Φ p nb d)
Ψ₀⊴Φ (⊴s p) nb d = ⊴l 0 (Ψ₀⊴Φ p nb d)
Ψ₀⊴Φ {η = G.lim F} (⊴l n p) nb d =
  ⊴l n (Ψ₀⊴Φ p (nb n) (dom-at (λ n → up L1 (F n) (nb n)) d n))
Ψ₀⊴Φ (l⊴ h) nb d = l⊴ (λ n → Ψ₀⊴Φ (h n) nb d)
Ψ₀⊴Φ {η = G.lc (inj₁ _) c t g} (⊴b h) nb d = ⊴b (λ e →
  Ψ₀⊴Φ (h e) (proj₂ (proj₂ (proj₂ nb)) c e)
    (Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
      (up L1 t (proj₁ (proj₂ (proj₂ nb))))
      (λ a e′ → up L1 (g a e′) (proj₂ (proj₂ (proj₂ nb)) a e′)) d c e))
Ψ₀⊴Φ (em⊴ {a = a} q) nb d = Ψ₀⊴Φ₀ q a refl nb d

tr⁻≼ : ∀ (y : T₀) → L.tr⁻ L.z≅ y ≼ y
tr⁻≼ y = ≅→≼ (L.tr⁻-≅ L.z≅ (L.≅-refl⁰ y))

Ψ₁⊴Φ : ∀ {x : T₁} {η} → x ⊴ η → .(nb : Nested L1 η) .(d : Dom (up L1 η nb)) →
  Ψ₁ x ⊴ Φ η nb d
Ψ₁⊴Φ {η = η} z⊴ nb d = Ω⊴Φ η nb d
Ψ₁⊴Φ (s⊴s p) nb d = suc-step (Ψ₁⊴Φ p nb d)
Ψ₁⊴Φ (⊴s p) nb d = ⊴l 0 (Ψ₁⊴Φ p nb d)
Ψ₁⊴Φ {η = G.lim F} (⊴l n p) nb d =
  ⊴l n (Ψ₁⊴Φ p (nb n) (dom-at (λ n → up L1 (F n) (nb n)) d n))
Ψ₁⊴Φ (l⊴ h) nb d = l⊴ (λ n → Ψ₁⊴Φ (h n) nb d)
Ψ₁⊴Φ {η = G.lc (inj₁ _) c t g} (⊴b h) nb d = ⊴b (λ e →
  Ψ₁⊴Φ (h e) (proj₂ (proj₂ (proj₂ nb)) c e)
    (Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
      (up L1 t (proj₁ (proj₂ (proj₂ nb))))
      (λ a e′ → up L1 (g a e′) (proj₂ (proj₂ (proj₂ nb)) a e′)) d c e))
Ψ₁⊴Φ {η = G.lc (inj₁ _) c t g} (nd b h) nb d = nd b (λ y a e q →
  Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) q))
    (proj₂ (proj₂ (proj₂ nb)) a e)
    (Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
      (up L1 t (proj₁ (proj₂ (proj₂ nb))))
      (λ a e′ → up L1 (g a e′) (proj₂ (proj₂ (proj₂ nb)) a e′)) d a e))
Ψ₁⊴Φ (nt h) nb d = nd (s≼s z≼) (λ y a e q →
  Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (proj₂ (proj₂ e))
    (Node.branch B.zero (cO B.zero) (cO-Lgl B.zero) (cO-Nested B.zero) (upT B.zero)
      (λ a e′ → up B.zero a (proj₂ (proj₂ e′))) d a e))
Ψ₁⊴Φ (u⊴ p) nb d = Ψ₀⊴Φ p nb d
```

## 4 目标层 0 的折叠把关系送到值前序

`NodeLower` 是层号 0 的结点处的一步：两条链同步归纳，参照是原链，被验收一侧是加法链。
链点的守卫无关，所以分支的前提只对无关守卫要求。

```agda
module NodeLower (f : T₀ → T₁) (same : ∀ y → f y ≅ f y)
  (c : R) .(w : Lgl B.zero c) .(b : Nested B.zero c) (t : LF)
  (g : (a : R) → .(Gd B.zero c a) → LF) .(d : Dom (B.lc B.zero c w b t g))
  (base : V.𝟏 ≼ read c)
  (low : ∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a →
    L.ψ⁰ (f y) ≼ read (out B.zero B.zero c w b t g d (pt a e))) where

  pts : ℕ → Pt B.zero c
  pts = iterate (next B.zero c w b t g d) (startᴸ B.zero c w b)

  ref-step : T₀ → T₀
  ref-step y = L.ψ {i = L.zero} {k = ℓ₁} {ℓ = ℓ₁} L.zero (λ r → r) (f y)

  δ : ℕ → T₀
  δ = iter ref-step (L.suc L.zero)

  step≤ : ∀ y → ref-step y ≼ L.ψ⁰ (f y)
  step≤ y = ≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r} (same y)))

  here : ∀ (p : Pt B.zero c) y → y ≼ read (at p) →
    L.ψ⁰ (f y) ≼ read (out B.zero B.zero c w b t g d p)
  here (pt a e) y q = low y a e q

  chain-lower : ∀ n → δ n ≼ read (at (pts n))
  chain-lower zero = base
  chain-lower (suc n) =
    ≼-trans (step≤ (δ n))
      (plus≽ (at (pts n)) (out B.zero B.zero c w b t g d (pts n))
        (here (pts n) (δ n) (chain-lower n)))

  node-lower : L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f) ≼
    read (ψ B.zero (B.lc B.zero c w b t g) d)
  node-lower = l≼ (λ n → ≼l n (here (pts n) (δ n) (chain-lower n)))

s≅⁻ : ∀ {k} {a b : L.Ordᶜ k} → L.suc a ≅ L.suc b → a ≅ b
s≅⁻ (L.s≅ e) = e

l≅⁻ : ∀ {k} {F F′ : ℕ → L.Ordᶜ k} → L.lim F ≅ L.lim F′ → ∀ n → F n ≅ F′ n
l≅⁻ (L.l≅ h) = h

lᵢ≅⁻ : ∀ {f f′ : T₀ → T₁} →
  L.limᵢ {i = L.zero} L.zero f ≅ L.limᵢ {i = L.zero} L.zero f′ →
  ∀ y → f y ≅ f′ y
lᵢ≅⁻ (L.lᵢ≅ e h) y = h y y (L.≅-refl⁰ y)

fold-lower : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ≅ x →
  .(nb : Nested L1 η) .(d : Dom (up L1 η nb)) →
  L.ψ⁰ x ≼ read (ψ B.zero (up L1 η nb) d)
fold-lower {η = η} z⊴ s nb d = one≼fold (up L1 η nb) d
fold-lower {η = G.suc η} (s⊴s p) s nb d =
  suc-lower (ψ B.zero (up L1 η nb) d) (fold-lower p (s≅⁻ s) nb d)
fold-lower (⊴s p) s nb d = ≼l 0 (fold-lower p s nb d)
fold-lower {η = G.lim F} (⊴l n p) s nb d =
  ≼l n (fold-lower p s (nb n) (dom-at (λ n → up L1 (F n) (nb n)) d n))
fold-lower (l⊴ h) s nb d = l≼ (λ n → fold-lower (h n) (l≅⁻ s n) nb d)
fold-lower {η = G.lc (inj₁ _) c t g} (⊴b h) s nb d = ≼l 0
  (fold-lower (h (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))) s
    (proj₂ (proj₂ (proj₂ nb)) c (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb)))
    (Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
      (up L1 t (proj₁ (proj₂ (proj₂ nb))))
      (λ a e′ → up L1 (g a e′) (proj₂ (proj₂ (proj₂ nb)) a e′)) d c
      (inj₁ refl , proj₁ nb , proj₁ (proj₂ nb))))
fold-lower {η = G.lc (inj₁ tt) c t g} (nd {f = f} base h) s nb d =
  NodeLower.node-lower f (lᵢ≅⁻ s) c (proj₁ nb) (proj₁ (proj₂ nb))
    (up L1 t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up L1 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d base
    (λ y a e q → fold-lower (h y a e q) (lᵢ≅⁻ s y)
      (proj₂ (proj₂ (proj₂ nb)) a e)
      (Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
        (up L1 t (proj₁ (proj₂ (proj₂ nb))))
        (λ a e′ → up L1 (g a e′) (proj₂ (proj₂ (proj₂ nb)) a e′)) d a e))
fold-lower (nt {f = f} h) s nb d =
  NodeLower.node-lower f (lᵢ≅⁻ s) (cO B.zero) (cO-Lgl B.zero) (cO-Nested B.zero)
    (upT B.zero) (λ a e → up B.zero a (proj₂ (proj₂ e))) d (≼-refl _)
    (λ y a e q → fold-lower (h y a q) (lᵢ≅⁻ s y) (proj₂ (proj₂ e))
      (Node.branch B.zero (cO B.zero) (cO-Lgl B.zero) (cO-Nested B.zero)
        (upT B.zero) (λ a e′ → up B.zero a (proj₂ (proj₂ e′))) d a e))
fold-lower {η = G.em tt a} (em⊴ q) s nb d =
  ≼-trans (V.ψ⁰-mono⁰ q) (fold₀-lower a nb d)
fold-lower (u⊴ {y = y} p) s nb d = fold-lower p (L.≅-refl⁰ y) nb d
```

## 5 接口与 ψ₀(Ω₂)

```agda
interface₁ : Interface 1
interface₁ = record
  { Rel = λ x η → x ⊴ η
  ; start = Ω⊴top
  ; step = Ψ₁⊴Φ
  ; absorb = λ θ r → ⊴-+ˡ θ r
  ; lower = fold-lower
  }

lower₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (foldᶠ 2)
lower₂ = FromInterface.theorem 1 interface₁
```

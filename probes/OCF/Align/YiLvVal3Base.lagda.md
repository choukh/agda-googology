# YiLvFold 第 4 层：ψ₀(Ω₃) 的下界，第 2 层的逐点前序

**验收文件，档位：定义与编译定理 (引理)。** 第 2 层的逐点前序 `_⊴₂_` (`Level` 的树对 `Raw 2` 的值)，
它对加法、前缀、层间搬运、目标层 2 的折叠封闭 (`ADD₂`, `⊴₂-+ˡ`, `TR₁`, `B₂`)。参照一侧的结点对字面证明 `q` 一般，派发对任意 `p`, `σ` 用 `with` 分情况。
入口 [YiLvVal3](YiLvVal3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvVal3Base where

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

T₂ : Set
T₂ = L.Ordᶜ ℓ₂

L2 : LF
L2 = B.suc L1

R₂ : Set
R₂ = Raw L2
```

## 1 第 2 层的逐点前序

槽位 `inj₁ tt` 是层号 1 的结点，下界与分支的输入在 `Raw 1` 里，用 `_⊴_`；槽位 `inj₂ (inj₁ tt)` 是层号 0 的结点，用 `≼ read`。
参照一侧的结点对字面证明 `q` 一般：加法会把 `q` 换成 `σ q`。

```agda
infix 4 _⊴₂_
data _⊴₂_ : ∀ {k} → L.Ordᶜ k → R₂ → Set where
  z₂ : ∀ {k} {η : R₂} → _⊴₂_ {k} L.zero η
  ss₂ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴₂ η → L.suc x ⊴₂ G.suc η
  s₂ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴₂ η → x ⊴₂ G.suc η
  l₂ : ∀ {k} {x : L.Ordᶜ k} {F : ℕ → R₂} n → x ⊴₂ F n → x ⊴₂ G.lim F
  ll₂ : ∀ {k} {F : ℕ → L.Ordᶜ k} {η} → (∀ n → F n ⊴₂ η) → L.lim F ⊴₂ η
  b1 : ∀ {k} {x : L.Ordᶜ k} {c t} {g : (a : R₁) → .(Gd L1 c a) → R₂} →
    (∀ .(e : Gd L1 c c) → x ⊴₂ g c e) → x ⊴₂ G.lc (inj₁ tt) c t g
  b0 : ∀ {k} {x : L.Ordᶜ k} {c t} {g : (a : R) → .(Gd B.zero c a) → R₂} →
    (∀ .(e : Gd B.zero c c) → x ⊴₂ g c e) → x ⊴₂ G.lc (inj₂ (inj₁ tt)) c t g
  nd1 : ∀ {K} {q : ℓ₁ L.<ᴵ K} {f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K} {c t}
    {g : (a : R₁) → .(Gd L1 c a) → R₂} → L.Ω ℓ₁ ⊴ c →
    (∀ (y : T₁) a .(e : Gd L1 c a) → y ⊴ a → f (L.into (L.<→◃ q) y) ⊴₂ g a e) →
    L.limᵢ q f ⊴₂ G.lc (inj₁ tt) c t g
  nd0 : ∀ {K} {q : L.zero L.<ᴵ K} {f : L.U L.zero (L.<→◃ q) → L.Ordᶜ K} {c t}
    {g : (a : R) → .(Gd B.zero c a) → R₂} → V.𝟏 ≼ read c →
    (∀ (y : T₀) a .(e : Gd B.zero c a) → y ≼ read a →
      f (L.into (L.<→◃ q) y) ⊴₂ g a e) →
    L.limᵢ q f ⊴₂ G.lc (inj₂ (inj₁ tt)) c t g
  nt₂ : ∀ {K} {q : ℓ₁ L.<ᴵ K} {f : L.U ℓ₁ (L.<→◃ q) → L.Ordᶜ K} →
    (∀ (y : T₁) a → y ⊴ a → f (L.into (L.<→◃ q) y) ⊴₂ G.em tt a) →
    L.limᵢ q f ⊴₂ G.top
  em₂ : ∀ {k} {y : L.Ordᶜ k} {a : R₁} → y ⊴ a → y ⊴₂ G.em tt a
  u₂ : ∀ {k} {y : L.Ordᶜ k} {η} → y ⊴₂ η → L.up {k = k} L.zero y ⊴₂ η
```

结点分支的定义域，只在无关位置用。

```agda
br₂₁ : ∀ c t (g : (a : R₁) → .(Gd L1 c a) → R₂) .(nb : Nested L2 (G.lc (inj₁ tt) c t g)) →
  Dom (up L2 (G.lc (inj₁ tt) c t g) nb) → ∀ a (e : Gd L1 c a) →
  Dom (up L2 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e))
br₂₁ c t g nb d a e = Node.branch L1 c (proj₁ nb) (proj₁ (proj₂ nb))
  (up L2 t (proj₁ (proj₂ (proj₂ nb))))
  (λ a e → up L2 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d a e

br₂₀ : ∀ c t (g : (a : R) → .(Gd B.zero c a) → R₂)
  .(nb : Nested L2 (G.lc (inj₂ (inj₁ tt)) c t g)) →
  Dom (up L2 (G.lc (inj₂ (inj₁ tt)) c t g) nb) → ∀ a (e : Gd B.zero c a) →
  Dom (up L2 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e))
br₂₀ c t g nb d a e = Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
  (up L2 t (proj₁ (proj₂ (proj₂ nb))))
  (λ a e → up L2 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d a e

br₂T : Dom (upT L2) → ∀ a (e : Gd L1 G.top a) → Dom (up L1 a (proj₂ (proj₂ e)))
br₂T d a e = Node.branch L1 G.top (cO-Lgl L1) (cO-Nested L1) (upT L1)
  (λ a e → up L1 a (proj₂ (proj₂ e))) d a e

br₁₀ : ∀ c t (g : (a : R) → .(Gd B.zero c a) → R₁)
  .(nb : Nested L1 (G.lc (inj₁ tt) c t g)) →
  Dom (up L1 (G.lc (inj₁ tt) c t g) nb) → ∀ a (e : Gd B.zero c a) →
  Dom (up L1 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e))
br₁₀ c t g nb d a e = Node.branch B.zero c (proj₁ nb) (proj₁ (proj₂ nb))
  (up L1 t (proj₁ (proj₂ (proj₂ nb))))
  (λ a e → up L1 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e)) d a e

br₁T : Dom (upT L1) → ∀ a (e : Gd B.zero (cO B.zero) a) →
  Dom (up B.zero a (proj₂ (proj₂ e)))
br₁T d a e = Node.branch B.zero (cO B.zero) (cO-Lgl B.zero) (cO-Nested B.zero)
  (upT B.zero) (λ a e → up B.zero a (proj₂ (proj₂ e))) d a e
```

## 2 加法与前缀

`plus L2 θ (em tt a)` 对 `a` 逐构造子展开；`a` 的层号 0 的结点落在槽位 `inj₂ (inj₁ tt)`。
参照一侧 `add x σ (limᵢ q f)` 的分支经 `coe` 读输入，`out-into` 只是命题相等，所以在那里搬一次。

```agda
⊴₂-embed₀ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴₂ η → ∀ (a : R) →
  x ⊴₂ plus L2 η (G.em tt (G.em tt a))
⊴₂-embed₀ p G.zero = p
⊴₂-embed₀ p (G.suc a) = s₂ (⊴₂-embed₀ p a)
⊴₂-embed₀ p (G.lim f) = l₂ 0 (⊴₂-embed₀ p (f 0))
⊴₂-embed₀ p (G.lc () c t g)
⊴₂-embed₀ p (G.em () a)
⊴₂-embed₀ p G.top = s₂ p

⊴₂-embed : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴₂ η → ∀ (a : R₁) → x ⊴₂ plus L2 η (G.em tt a)
⊴₂-embed p G.zero = p
⊴₂-embed p (G.suc a) = s₂ (⊴₂-embed p a)
⊴₂-embed p (G.lim f) = l₂ 0 (⊴₂-embed p (f 0))
⊴₂-embed p (G.lc (inj₁ _) c t g) = b0 (λ e → ⊴₂-embed p (g c e))
⊴₂-embed p (G.lc (inj₂ ()) c t g)
⊴₂-embed p (G.em _ a) = ⊴₂-embed₀ p a
⊴₂-embed p G.top = b0 (λ e → s₂ p)

⊴₂-+ʳ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴₂ η → ∀ η′ → x ⊴₂ plus L2 η η′
⊴₂-+ʳ p G.zero = p
⊴₂-+ʳ p (G.suc y) = s₂ (⊴₂-+ʳ p y)
⊴₂-+ʳ p (G.lim f) = l₂ 0 (⊴₂-+ʳ p (f 0))
⊴₂-+ʳ p (G.lc (inj₁ _) c t g) = b1 (λ e → ⊴₂-+ʳ p (g c e))
⊴₂-+ʳ p (G.lc (inj₂ (inj₁ _)) c t g) = b0 (λ e → ⊴₂-+ʳ p (g c e))
⊴₂-+ʳ p (G.lc (inj₂ (inj₂ ())) c t g)
⊴₂-+ʳ p (G.em _ a) = ⊴₂-embed p a
⊴₂-+ʳ p G.top = b1 (λ e → b0 (λ e′ → s₂ p))

ADD₀ : ∀ (σ : L.Simᴵ L.zero ℓ₂) {x : T₂} {η} → x ⊴₂ η → ∀ {y b : T₀} → y ≼ b →
  ∀ a → b ≡ read a → L.add x σ y ⊴₂ plus L2 η (G.em tt (G.em tt a))
ADD₀ σ px z≼ a q = ⊴₂-embed₀ px a
ADD₀ σ px (s≼s p) (G.suc a) refl = ss₂ (ADD₀ σ px p a refl)
ADD₀ σ px (s≼s p) G.top refl = ss₂ (ADD₀ σ px p G.zero refl)
ADD₀ σ px (≼l n p) (G.lim f) refl = l₂ n (ADD₀ σ px p (f n) refl)
ADD₀ σ px (l≼ h) a q = ll₂ (λ n → ADD₀ σ px (h n) a q)
ADD₀ σ px (≼i {p = ()} x ex p) a q
ADD₀ σ px (i≼ {p = ()} h) a q
ADD₀ σ px (≼u {r = ()} p) a q
ADD₀ σ px (u≼ {r = ()} p) a q

ADD₁ : ∀ {k} (σ : L.Simᴵ k ℓ₂) {x : T₂} {η} → x ⊴₂ η → ∀ {y : L.Ordᶜ k} {a} → y ⊴ a →
  L.add x σ y ⊴₂ plus L2 η (G.em tt a)
ADD₁ σ px {a = a} z⊴ = ⊴₂-embed px a
ADD₁ σ px (s⊴s r) = ss₂ (ADD₁ σ px r)
ADD₁ σ px (⊴s r) = s₂ (ADD₁ σ px r)
ADD₁ σ px (⊴l n r) = l₂ n (ADD₁ σ px r)
ADD₁ σ px (l⊴ h) = ll₂ (λ n → ADD₁ σ px (h n))
ADD₁ σ px (⊴b h) = b0 (λ e → ADD₁ σ px (h e))
ADD₁ σ {x} {η} px (nd {f = f} {g = g} base h) = nd0 {q = σ L.zero} base (λ y a e r →
  subst (λ w → L.add x σ (f w) ⊴₂ plus L2 η (G.em tt (g a e)))
    (sym (L.out-into (L.<→◃ (σ L.zero)) y)) (ADD₁ σ px (h y a e r)))
ADD₁ σ {x} {η} px (nt {f = f} h) = nd0 {q = σ L.zero} (s≼s z≼) (λ y a e r →
  subst (λ w → L.add x σ (f w) ⊴₂ plus L2 η (G.em tt (G.em tt a)))
    (sym (L.out-into (L.<→◃ (σ L.zero)) y)) (ADD₁ σ px (h y a r)))
ADD₁ σ px (em⊴ {a = a} q) = ADD₀ σ px q a refl
ADD₁ σ px (u⊴ r) = ADD₁ (λ q → σ (L.suc q)) px r

ADD₂ : ∀ {k} (σ : L.Simᴵ k ℓ₂) {x : T₂} {η} → x ⊴₂ η → ∀ {y : L.Ordᶜ k} {η′} →
  y ⊴₂ η′ → L.add x σ y ⊴₂ plus L2 η η′
ADD₂ σ px {η′ = η′} z₂ = ⊴₂-+ʳ px η′
ADD₂ σ px (ss₂ r) = ss₂ (ADD₂ σ px r)
ADD₂ σ px (s₂ r) = s₂ (ADD₂ σ px r)
ADD₂ σ px (l₂ n r) = l₂ n (ADD₂ σ px r)
ADD₂ σ px (ll₂ h) = ll₂ (λ n → ADD₂ σ px (h n))
ADD₂ σ px (b1 h) = b1 (λ e → ADD₂ σ px (h e))
ADD₂ σ px (b0 h) = b0 (λ e → ADD₂ σ px (h e))
ADD₂ σ {x} {η} px (nd1 {q = q} {f = f} {g = g} base h) = nd1 {q = σ q} base (λ y a e r →
  subst (λ w → L.add x σ (f (L.into (L.<→◃ q) w)) ⊴₂ plus L2 η (g a e))
    (sym (L.out-into (L.<→◃ (σ q)) y)) (ADD₂ σ px (h y a e r)))
ADD₂ σ {x} {η} px (nd0 {q = q} {f = f} {g = g} base h) = nd0 {q = σ q} base (λ y a e r →
  subst (λ w → L.add x σ (f (L.into (L.<→◃ q) w)) ⊴₂ plus L2 η (g a e))
    (sym (L.out-into (L.<→◃ (σ q)) y)) (ADD₂ σ px (h y a e r)))
ADD₂ σ {x} {η} px (nt₂ {q = q} {f = f} h) = nd1 {q = σ q} Ω⊴top (λ y a e r →
  subst (λ w → L.add x σ (f (L.into (L.<→◃ q) w)) ⊴₂ plus L2 η (G.em tt a))
    (sym (L.out-into (L.<→◃ (σ q)) y)) (ADD₂ σ px (h y a r)))
ADD₂ σ px (em₂ r) = ADD₁ σ px r
ADD₂ σ px (u₂ r) = ADD₂ (λ q → σ (L.suc q)) px r

em-shift₂₀ : ∀ θ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  y ⊴₂ plus L2 θ (G.em tt (G.em tt a))
em-shift₂₀ θ z≼ a q = z₂
em-shift₂₀ θ (s≼s p) (G.suc a) refl = ss₂ (em-shift₂₀ θ p a refl)
em-shift₂₀ θ (s≼s p) G.top refl = ss₂ (em-shift₂₀ θ p G.zero refl)
em-shift₂₀ θ (≼l n p) (G.lim f) refl = l₂ n (em-shift₂₀ θ p (f n) refl)
em-shift₂₀ θ (l≼ h) a q = ll₂ (λ n → em-shift₂₀ θ (h n) a q)
em-shift₂₀ θ (≼i {p = ()} x ex p) a q
em-shift₂₀ θ (i≼ {p = ()} h) a q
em-shift₂₀ θ (≼u {r = ()} p) a q
em-shift₂₀ θ (u≼ {r = ()} p) a q

em-shift₂ : ∀ θ {k} {y : L.Ordᶜ k} {a} → y ⊴ a → y ⊴₂ plus L2 θ (G.em tt a)
em-shift₂ θ z⊴ = z₂
em-shift₂ θ (s⊴s r) = ss₂ (em-shift₂ θ r)
em-shift₂ θ (⊴s r) = s₂ (em-shift₂ θ r)
em-shift₂ θ (⊴l n r) = l₂ n (em-shift₂ θ r)
em-shift₂ θ (l⊴ h) = ll₂ (λ n → em-shift₂ θ (h n))
em-shift₂ θ (⊴b h) = b0 (λ e → em-shift₂ θ (h e))
em-shift₂ θ (nd base h) = nd0 {q = L.zero} base (λ y a e r → em-shift₂ θ (h y a e r))
em-shift₂ θ (nt h) = nd0 {q = L.zero} (s≼s z≼) (λ y a e r → em-shift₂ θ (h y a r))
em-shift₂ θ (em⊴ {a = a} q) = em-shift₂₀ θ q a refl
em-shift₂ θ (u⊴ r) = u₂ (em-shift₂ θ r)

⊴₂-+ˡ : ∀ θ {k} {x : L.Ordᶜ k} {η} → x ⊴₂ η → x ⊴₂ plus L2 θ η
⊴₂-+ˡ θ z₂ = z₂
⊴₂-+ˡ θ (ss₂ p) = ss₂ (⊴₂-+ˡ θ p)
⊴₂-+ˡ θ (s₂ p) = s₂ (⊴₂-+ˡ θ p)
⊴₂-+ˡ θ (l₂ n p) = l₂ n (⊴₂-+ˡ θ p)
⊴₂-+ˡ θ (ll₂ h) = ll₂ (λ n → ⊴₂-+ˡ θ (h n))
⊴₂-+ˡ θ (b1 h) = b1 (λ e → ⊴₂-+ˡ θ (h e))
⊴₂-+ˡ θ (b0 h) = b0 (λ e → ⊴₂-+ˡ θ (h e))
⊴₂-+ˡ θ (nd1 base h) = nd1 base (λ y a e r → ⊴₂-+ˡ θ (h y a e r))
⊴₂-+ˡ θ (nd0 base h) = nd0 base (λ y a e r → ⊴₂-+ˡ θ (h y a e r))
⊴₂-+ˡ θ (nt₂ h) = nd1 Ω⊴top (λ y a e r → ⊴₂-+ˡ θ (h y a r))
⊴₂-+ˡ θ (em₂ r) = em-shift₂ θ r
⊴₂-+ˡ θ (u₂ p) = u₂ (⊴₂-+ˡ θ p)

copies-⊴₂ : ∀ {A : T₂} {β} → A ⊴₂ β → ∀ n →
  iter (A L.+_) L.zero (suc n) ⊴₂ copies L2 β n
copies-⊴₂ p zero = p
copies-⊴₂ p (suc n) = ADD₂ (λ q → q) p (copies-⊴₂ p n)

suc-step₂ : ∀ {A : T₂} {β} → A ⊴₂ β → L.lim (iter (A L.+_) L.zero) ⊴₂ successor L2 β
suc-step₂ p = ll₂ λ where
  zero → z₂
  (suc n) → l₂ n (copies-⊴₂ p n)
```

## 3 层间搬运

目标层 2 穿透层号 1 的结点时，分支的输入先过 `tr⁻ (s≅ z≅)`；`_⊴_` 对它封闭。

```agda
tr≼ : ∀ (y : T₀) → L.tr L.z≅ y ≼ y
tr≼ y = ≅→≼ (L.tr-≅ L.z≅ (L.≅-refl⁰ y))

TR₀ : ∀ {w : T₀} {a} → w ⊴ a → L.tr⁻ L.z≅ w ⊴ a
TR₀ z⊴ = z⊴
TR₀ (s⊴s r) = s⊴s (TR₀ r)
TR₀ (⊴s r) = ⊴s (TR₀ r)
TR₀ (⊴l n r) = ⊴l n (TR₀ r)
TR₀ (l⊴ h) = l⊴ (λ n → TR₀ (h n))
TR₀ (⊴b h) = ⊴b (λ e → TR₀ (h e))
TR₀ {w} (em⊴ q) = em⊴ (≼-trans (tr⁻≼ w) q)

TR₁ : ∀ {y : T₁} {a} → y ⊴ a → L.tr⁻ (L.s≅ L.z≅) y ⊴ a
TR₁ z⊴ = z⊴
TR₁ (s⊴s r) = s⊴s (TR₁ r)
TR₁ (⊴s r) = ⊴s (TR₁ r)
TR₁ (⊴l n r) = ⊴l n (TR₁ r)
TR₁ (l⊴ h) = l⊴ (λ n → TR₁ (h n))
TR₁ (⊴b h) = ⊴b (λ e → TR₁ (h e))
TR₁ (nd base h) = nd base (λ y a e r → TR₁ (h (L.tr L.z≅ y) a e (≼-trans (tr≼ y) r)))
TR₁ (nt h) = nt (λ y a r → TR₁ (h (L.tr L.z≅ y) a (≼-trans (tr≼ y) r)))
TR₁ (u⊴ r) = u⊴ (TR₀ r)
```

## 4 目标层 2：全部保留

```agda
Ω₂⊴top : L.Ω ℓ₂ ⊴₂ G.top
Ω₂⊴top = nt₂ {q = L.zero} (λ y a r → u₂ (em₂ r))

Ω₂⊴ψ₂₀ : ∀ a .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  L.Ω ℓ₂ ⊴₂ ψ L2 (up B.zero a nb) d
Ω₂⊴ψ₂₀ G.zero nb d = Ω₂⊴top
Ω₂⊴ψ₂₀ (G.suc a) nb d = l₂ 0 (Ω₂⊴ψ₂₀ a nb d)
Ω₂⊴ψ₂₀ (G.lim f) nb d =
  l₂ 0 (Ω₂⊴ψ₂₀ (f 0) (nb 0) (dom-at (λ n → up B.zero (f n) (nb n)) d 0))
Ω₂⊴ψ₂₀ (G.lc () c t g) nb d
Ω₂⊴ψ₂₀ (G.em () a) nb d
Ω₂⊴ψ₂₀ G.top nb d = l₂ 0 Ω₂⊴top

Ω₂⊴ψ₂₁ : ∀ (a : R₁) .(nb : Nested L1 a) .(d : Dom (up L1 a nb)) →
  L.Ω ℓ₂ ⊴₂ ψ L2 (up L1 a nb) d
Ω₂⊴ψ₂₁ G.zero nb d = Ω₂⊴top
Ω₂⊴ψ₂₁ (G.suc a) nb d = l₂ 0 (Ω₂⊴ψ₂₁ a nb d)
Ω₂⊴ψ₂₁ (G.lim f) nb d =
  l₂ 0 (Ω₂⊴ψ₂₁ (f 0) (nb 0) (dom-at (λ n → up L1 (f n) (nb n)) d 0))
Ω₂⊴ψ₂₁ (G.lc (inj₁ _) c t g) nb d = b0 (λ e →
  Ω₂⊴ψ₂₁ (g c e) (proj₂ (proj₂ (proj₂ nb)) c e) (br₁₀ c t g nb d c e))
Ω₂⊴ψ₂₁ (G.lc (inj₂ ()) c t g) nb d
Ω₂⊴ψ₂₁ (G.em _ a) nb d = Ω₂⊴ψ₂₀ a nb d
Ω₂⊴ψ₂₁ G.top nb d = b0 (λ e → l₂ 0 Ω₂⊴top)

Ω₂⊴ψ₂ : ∀ (η : R₂) .(nb : Nested L2 η) .(d : Dom (up L2 η nb)) →
  L.Ω ℓ₂ ⊴₂ ψ L2 (up L2 η nb) d
Ω₂⊴ψ₂ G.zero nb d = Ω₂⊴top
Ω₂⊴ψ₂ (G.suc a) nb d = l₂ 0 (Ω₂⊴ψ₂ a nb d)
Ω₂⊴ψ₂ (G.lim f) nb d =
  l₂ 0 (Ω₂⊴ψ₂ (f 0) (nb 0) (dom-at (λ n → up L2 (f n) (nb n)) d 0))
Ω₂⊴ψ₂ (G.lc (inj₁ _) c t g) nb d = b1 (λ e →
  Ω₂⊴ψ₂ (g c e) (proj₂ (proj₂ (proj₂ nb)) c e) (br₂₁ c t g nb d c e))
Ω₂⊴ψ₂ (G.lc (inj₂ (inj₁ _)) c t g) nb d = b0 (λ e →
  Ω₂⊴ψ₂ (g c e) (proj₂ (proj₂ (proj₂ nb)) c e) (br₂₀ c t g nb d c e))
Ω₂⊴ψ₂ (G.lc (inj₂ (inj₂ ())) c t g) nb d
Ω₂⊴ψ₂ (G.em _ a) nb d = Ω₂⊴ψ₂₁ a nb d
Ω₂⊴ψ₂ G.top nb d = b1 (λ e → Ω₂⊴ψ₂₁ G.top (proj₂ (proj₂ e)) (br₂T d G.top e))

B₀ : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  ∀ {ℓ} (p : ℓ₂ L.<ᴵ ℓ) (σ : L.Simᴵ L.zero ℓ) →
  .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  L.ψ p σ y ⊴₂ ψ L2 (up B.zero a nb) d
B₀ z≼ a q p σ nb d = Ω₂⊴ψ₂₀ a nb d
B₀ (s≼s r) (G.suc a) refl p σ nb d = suc-step₂ (B₀ r a refl p σ nb d)
B₀ (s≼s r) G.top refl p σ nb d = suc-step₂ (B₀ r G.zero refl p σ tt (tt , tt , tt))
B₀ (≼l n r) (G.lim f) refl p σ nb d =
  l₂ n (B₀ r (f n) refl p σ (nb n) (dom-at (λ n → up B.zero (f n) (nb n)) d n))
B₀ (l≼ h) a q p σ nb d = ll₂ (λ n → B₀ (h n) a q p σ nb d)
B₀ (≼i {p = ()} x ex r) a q p σ nb d
B₀ (i≼ {p = ()} h) a q p σ nb d
B₀ (≼u {r = ()} r) a q p σ nb d
B₀ (u≼ {r = ()} r) a q p σ nb d

B₁ : ∀ {k} {y : L.Ordᶜ k} {a : R₁} → y ⊴ a →
  ∀ {ℓ} (p : ℓ₂ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(nb : Nested L1 a) .(d : Dom (up L1 a nb)) → L.ψ p σ y ⊴₂ ψ L2 (up L1 a nb) d
B₁ {a = a} z⊴ p σ nb d = Ω₂⊴ψ₂₁ a nb d
B₁ (s⊴s r) p σ nb d = suc-step₂ (B₁ r p σ nb d)
B₁ (⊴s r) p σ nb d = l₂ 0 (B₁ r p σ nb d)
B₁ {a = G.lim F} (⊴l n r) p σ nb d =
  l₂ n (B₁ r p σ (nb n) (dom-at (λ n → up L1 (F n) (nb n)) d n))
B₁ (l⊴ h) p σ nb d = ll₂ (λ n → B₁ (h n) p σ nb d)
B₁ (⊴b {c = c} {t = t} {g = g} h) p σ nb d = b0 (λ e →
  B₁ (h e) p σ (proj₂ (proj₂ (proj₂ nb)) c e) (br₁₀ c t g nb d c e))
B₁ (nd {f = f} {c = c} {t = t} {g = g} base h) p σ nb d with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ (L.suc L.zero)) = nd0 {q = L.suc L.zero} base (λ y a e r →
  B₁ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ nb)) a e) (br₁₀ c t g nb d a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via _ ())
... | injᶜ ()
B₁ (nt {f = f} h) p σ nb d with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ (L.suc L.zero)) = nd0 {q = L.suc L.zero} (s≼s z≼) (λ y a e r →
  B₁ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) r)) p σ (proj₂ (proj₂ e)) (br₁T d a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via _ ())
... | injᶜ ()
B₁ (em⊴ {a = a} q) p σ nb d = B₀ q a refl p σ nb d
B₁ (u⊴ r) p σ nb d = B₁ r p (λ q → σ (L.suc q)) nb d

B₂ : ∀ {k} {x : L.Ordᶜ k} {η : R₂} → x ⊴₂ η →
  ∀ {ℓ} (p : ℓ₂ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(nb : Nested L2 η) .(d : Dom (up L2 η nb)) → L.ψ p σ x ⊴₂ ψ L2 (up L2 η nb) d
B₂ {η = η} z₂ p σ nb d = Ω₂⊴ψ₂ η nb d
B₂ (ss₂ r) p σ nb d = suc-step₂ (B₂ r p σ nb d)
B₂ (s₂ r) p σ nb d = l₂ 0 (B₂ r p σ nb d)
B₂ {η = G.lim F} (l₂ n r) p σ nb d =
  l₂ n (B₂ r p σ (nb n) (dom-at (λ n → up L2 (F n) (nb n)) d n))
B₂ (ll₂ h) p σ nb d = ll₂ (λ n → B₂ (h n) p σ nb d)
B₂ (b1 {c = c} {t = t} {g = g} h) p σ nb d = b1 (λ e →
  B₂ (h e) p σ (proj₂ (proj₂ (proj₂ nb)) c e) (br₂₁ c t g nb d c e))
B₂ (b0 {c = c} {t = t} {g = g} h) p σ nb d = b0 (λ e →
  B₂ (h e) p σ (proj₂ (proj₂ (proj₂ nb)) c e) (br₂₀ c t g nb d c e))
B₂ (nd1 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ nb d
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via (L.s≅ L.z≅) L.zero) = nd1 {q = L.zero} base (λ y a e r →
  B₂ (h (L.tr⁻ (L.s≅ L.z≅) y) a e (TR₁ r)) p σ
    (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₁ c t g nb d a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ (L.s≅ ())
B₂ (nd0 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ nb d
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via L.z≅ (L.suc L.zero)) = nd0 {q = L.suc L.zero} base (λ y a e r →
  B₂ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ nb)) a e) (br₂₀ c t g nb d a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via _ ())
... | injᶜ ()
B₂ (nt₂ {q = q} {f = f} h) p σ nb d with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via (L.s≅ L.z≅) L.zero) = nd1 {q = L.zero} Ω⊴top (λ y a e r →
  B₂ (h (L.tr⁻ (L.s≅ L.z≅) y) a (TR₁ r)) p σ (proj₂ (proj₂ e)) (br₂T d a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ (L.s≅ ())
B₂ (em₂ r) p σ nb d = B₁ r p σ nb d
B₂ (u₂ r) p σ nb d = B₂ r p (λ q → σ (L.suc q)) nb d
```


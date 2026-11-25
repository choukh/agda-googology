# YiIrrFb 第 4 层：`ψ₀ Ω₂` 的序数值下界

**验收文件，档位：编译定理 (下界，不是同值)。** `Ω₂-lower`：`Level` 族的参照 `ψ⁰ (Ω 2)` ≼ 读回的 `ψ₀ Ω₂`，
即输出的值不低于参照的 ψ₀(Ω₂)。办法是一个跨两族的逐点前序 `_⊴_` (`Level` 的树对 `Raw 1` 的值)，
对 "加前缀"、加法、目标层 1 的折叠封闭 (§3)，并把目标层 0 的折叠送到值前序 (§4)。没有上界，没有 Funext。
允许导入带记号闭包的 `Value` 与旧验收文件；定义与证书文件不导入本篇。入口 [YiIrrFb](YiIrrFb.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFbValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.RR5IrrCore as B
open B using (module G; Gd; Lgl; Nested; Cp; Dn)
open import OCF.Align.RR5IrrCheck using (up; tw)
open import OCF.Align.YiIrrIf
  using (R; one; _+ʳ_; copies; successor; CP; self; fst; Point; point;
         coordinate; start; iterate)
open import OCF.Align.YiIrrFoldBase using (module ChainLegal)
open import OCF.Align.YiIrrFoldValue using (read; read-add; read-copies)
open import OCF.Align.YiIrrFbIf
open import OCF.Align.YiIrrFbBase
open import OCF.Align.YiIrrFb
open import OCF.Align.YiIrrFbInst
  using (Ω₂-fold) renaming (points to Ω₂-points; guards to Ω₂-guards)
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4MonoFragment as M
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
```

## 1 参照

`ψ⁰ (Ω 2)` 的规则 6：链在第 1 层，从 Ω₁ 起步，每步是目标层 1 的折叠 `Ψ₁`；输出是 `ψ⁰` 沿链的极限。
`Ψ₀` 是同一个折叠在第 0 层的输入上。链用的是原链 (下一点就是折叠的输出)，被验收一侧用加法链。

```agda
Ψ₁ : T₁ → T₁
Ψ₁ = L.ψ {i = ℓ₁} {k = ℓ₁} {ℓ = ℓ₂} L.zero (λ r → L.suc r)

Ψ₀ : T₀ → T₁
Ψ₀ = L.ψ {i = ℓ₁} {k = L.zero} {ℓ = ℓ₂} L.zero (λ r → L.suc (L.suc r))

γ : ℕ → T₁
γ = iter Ψ₁ (L.Ω ℓ₁)

reference : T₀
reference = L.ψ⁰ (L.Ω ℓ₂)

reference-row : reference ≡ L.lim (λ n → L.ψ⁰ (γ n))
reference-row = refl

γ-self : ∀ n → γ n ≅ γ n
γ-self zero = L.Ω-≅ (L.≅ᴵ-refl ℓ₁)
γ-self (suc n) =
  L.ψ-≅ {p = L.zero} {σ = λ r → L.suc r} {p′ = L.zero} {σ′ = λ r → L.suc r}
    (L.≅ᴵ-refl ℓ₁) (γ-self n)
```

## 2 第 0 层的读法

`read` 取自 [YiIrrFoldValue](YiIrrFoldValue.lagda.md)。下面几条对新的 `ψ₀` 重证：它在第 0 层的读回上与 `ψ⁰` 互模拟，
输出的值不小于 1，字面第一位置读成值前序。

```agda
read-fold₀ : ∀ a .(nb : Nested B.zero a) .(d : Dom (up B.zero a nb)) →
  read (ψ₀ (up B.zero a nb) d) ≅ L.ψ⁰ (read a)
read-fold₀ G.zero nb d = L.s≅ L.z≅
read-fold₀ (G.suc a) nb d =
  L.l≅ (read-copies (ψ₀ (up B.zero a nb) d) (L.ψ⁰ (read a)) (read-fold₀ a nb d))
read-fold₀ (G.lim f) nb d =
  L.l≅ (λ n → read-fold₀ (f n) (nb n)
    (dom-at (λ n → up B.zero (f n) (nb n)) d n))
read-fold₀ (G.lc () c t g) nb d
read-fold₀ (G.em () t) nb d
read-fold₀ G.top nb d = L.l≅ (read-copies one (L.suc L.zero) (L.s≅ L.z≅))

suc-lower : ∀ a {k} {x : L.Ordᶜ k} →
  L.ψ⁰ x ≼ read a → L.ψ⁰ (L.suc x) ≼ read (successor a)
suc-lower a low = l≼ (λ n → ≼l n
  (≼-trans (V.iter-≼ low n)
    (≅→≼ (L.≅-sym (read-copies a (read a) (L.≅-refl⁰ (read a)) n)))))

read-cp : ∀ {a} b → Cp B.zero a b → read a ≼ read b
read-dn : ∀ {a} b → Dn B.zero a b → read a ≼ read b
read-cp b (inj₁ refl) = ≼-refl _
read-cp b (inj₂ p) = read-dn b p
read-dn (G.suc b) p = V.≼-suc (read-cp b p)
read-dn (G.lim f) (n , p) = ≼l n (read-cp (f n) p)
read-dn (G.lc () c t g) p
read-dn (G.em () T) p
read-dn G.top ()

one≼fold : ∀ x .(d : Dom x) → V.𝟏 ≼ read (ψ₀ x d)
one≼fold B.zero d = s≼s z≼
one≼fold (B.suc x) d = ≼l 1 (one≼fold x d)
one≼fold (B.lim f) d = ≼l 0 (one≼fold (f 0) (dom-at f d 0))
one≼fold (B.lc B.zero c w b t g) d = ≼l 0
  (one≼fold (g c (inj₁ refl , w , b))
    (Node₀.branch c w b t g d c (inj₁ refl , w , b)))
one≼fold (B.lc (B.suc B.zero) c w b t g) d = ≼l 0
  (one≼fold (g c (inj₁ refl , w , b))
    (Node₁.branch c w b t g d c (inj₁ refl , w , b)))
one≼fold (B.lc (B.suc (B.suc k)) c w b t g) d = s≼s z≼
one≼fold (B.lc (B.suc (B.lim f)) c w b t g) d = s≼s z≼
one≼fold (B.lc (B.suc (B.lc k c₀ w₀ b₀ t₀ g₀)) c w b t g) d = s≼s z≼
one≼fold (B.lc (B.lim f) c w b t g) d = s≼s z≼
one≼fold (B.lc (B.lc k c₀ w₀ b₀ t₀ g₀) c w b t g) d = s≼s z≼
```

## 3 跨两族的逐点前序

`x ⊴ η`：`Level` 的树 `x` (第 0 或第 1 层) 被 `Raw 1` 的值 `η` 逐点压住。前六条与值前序的构造子同形
(`⊴t`：压在第一支之下就压在结点之下)。`nd` 是逐点的一条：两个层 0 分支的结点，输入按值相关时分支相关；
它不比较上确界 (`ψ⁰` 对值前序在结点处不单调，`RR4MonoFragment.mono-fragment-not-cong`)。`nt` 是右边为 `top` 的同一条，
`em⊴` 把第 0 层的值前序嵌进来，`u⊴` 说提升透明。关系里没有守卫与合法性的证据，用到时另给。

```agda
infix 4 _⊴_
data _⊴_ : ∀ {k} → L.Ordᶜ k → R₁ → Set where
  z⊴ : ∀ {k} {η : R₁} → _⊴_ {k} L.zero η
  s⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → L.suc x ⊴ G.suc η
  ⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ⊴ G.suc η
  ⊴l : ∀ {k} {x : L.Ordᶜ k} {F : ℕ → R₁} n → x ⊴ F n → x ⊴ G.lim F
  l⊴ : ∀ {k} {F : ℕ → L.Ordᶜ k} {η} → (∀ n → F n ⊴ η) → L.lim F ⊴ η
  ⊴t : ∀ {k} {x : L.Ordᶜ k} {c t} {g : (a : R) → .(Gd B.zero c a) → R₁} →
    x ⊴ t → x ⊴ G.lc (inj₁ tt) c t g
  nd : ∀ {f : T₀ → T₁} {c t} {g : (a : R) → .(Gd B.zero c a) → R₁} →
    V.𝟏 ≼ read c →
    (∀ (y : T₀) a (e : Gd B.zero c a) → y ≼ read a → f y ⊴ g a e) →
    L.limᵢ {i = L.zero} L.zero f ⊴ G.lc (inj₁ tt) c t g
  nt : ∀ {f : T₀ → T₁} →
    (∀ (y : T₀) a → y ≼ read a → f y ⊴ G.em tt a) →
    L.limᵢ {i = L.zero} L.zero f ⊴ G.top
  em⊴ : ∀ {y : T₀} {a} → y ≼ read a → y ⊴ G.em tt a
  u⊴ : ∀ {y : T₀} {η} → y ⊴ η → L.up {k = L.zero} L.zero y ⊴ η
```

右边再加东西、左边加前缀都保持关系。`em-shift`, `add-em` 对第 0 层的值前序的推导递归；
被比较的右端是 `read a`，不是变量，所以带一个等式参数。

```agda
⊴-embed : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → ∀ a → x ⊴ embed-add η a
⊴-embed p G.zero = p
⊴-embed p (G.suc a) = ⊴s (⊴-embed p a)
⊴-embed p (G.lim f) = ⊴l 0 (⊴-embed p (f 0))
⊴-embed p (G.lc () c t g)
⊴-embed p (G.em () a)
⊴-embed p G.top = ⊴s p

⊴-+ʳ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → ∀ η′ → x ⊴ η +¹ η′
⊴-+ʳ p G.zero = p
⊴-+ʳ p (G.suc y) = ⊴s (⊴-+ʳ p y)
⊴-+ʳ p (G.lim f) = ⊴l 0 (⊴-+ʳ p (f 0))
⊴-+ʳ p (G.lc (inj₁ _) c t g) = ⊴t (⊴-+ʳ p t)
⊴-+ʳ p (G.lc (inj₂ ()) c t g)
⊴-+ʳ p (G.em _ a) = ⊴-embed p a
⊴-+ʳ p G.top = ⊴t (⊴s p)

em-shift : ∀ θ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a → y ⊴ embed-add θ a
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
  L.add x σ₀ y ⊴ embed-add η a
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
  L.add x σ₀ y ⊴ η +¹ η′
⊴-add₀ px {η′ = η′} z⊴ = ⊴-+ʳ px η′
⊴-add₀ px (s⊴s q) = s⊴s (⊴-add₀ px q)
⊴-add₀ px (⊴s q) = ⊴s (⊴-add₀ px q)
⊴-add₀ px (⊴l n q) = ⊴l n (⊴-add₀ px q)
⊴-add₀ px (l⊴ h) = l⊴ (λ n → ⊴-add₀ px (h n))
⊴-add₀ px (⊴t q) = ⊴t (⊴-add₀ px q)
⊴-add₀ px (em⊴ {a = a} q) = add-em px q a refl

⊴-add₁ : ∀ {x : T₁} {η} → x ⊴ η → ∀ {x′ : T₁} {η′} → x′ ⊴ η′ →
  (x L.+ x′) ⊴ η +¹ η′
⊴-add₁ px {η′ = η′} z⊴ = ⊴-+ʳ px η′
⊴-add₁ px (s⊴s q) = s⊴s (⊴-add₁ px q)
⊴-add₁ px (⊴s q) = ⊴s (⊴-add₁ px q)
⊴-add₁ px (⊴l n q) = ⊴l n (⊴-add₁ px q)
⊴-add₁ px (l⊴ h) = l⊴ (λ n → ⊴-add₁ px (h n))
⊴-add₁ px (⊴t q) = ⊴t (⊴-add₁ px q)
⊴-add₁ px (nd b h) = nd b (λ y a e q → ⊴-add₁ px (h y a e q))
⊴-add₁ px (nt h) = nd (s≼s z≼) (λ y a e q → ⊴-add₁ px (h y a q))
⊴-add₁ px (u⊴ q) = ⊴-add₀ px q

⊴-+ˡ : ∀ θ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ⊴ θ +¹ η
⊴-+ˡ θ z⊴ = z⊴
⊴-+ˡ θ (s⊴s p) = s⊴s (⊴-+ˡ θ p)
⊴-+ˡ θ (⊴s p) = ⊴s (⊴-+ˡ θ p)
⊴-+ˡ θ (⊴l n p) = ⊴l n (⊴-+ˡ θ p)
⊴-+ˡ θ (l⊴ h) = l⊴ (λ n → ⊴-+ˡ θ (h n))
⊴-+ˡ θ (⊴t p) = ⊴t (⊴-+ˡ θ p)
⊴-+ˡ θ (nd b h) = nd b (λ y a e q → ⊴-+ˡ θ (h y a e q))
⊴-+ˡ θ (nt h) = nd (s≼s z≼) (λ y a e q → ⊴-+ˡ θ (h y a q))
⊴-+ˡ θ (em⊴ {a = a} q) = em-shift θ q a refl
⊴-+ˡ θ (u⊴ p) = u⊴ (⊴-+ˡ θ p)
```

目标层 1 的折叠保持关系。`Φ η` 是被验收一侧的 "读回再折叠"；它的证据参数无关。
`Ψ₁` 在结点处穿透 (规则 5Ω)，分支的输入先过一次层间搬运 `tr⁻`，值不变。

```agda
Φ : (η : R₁) → .(Lgl L1 η) → .(Nested L1 η) → R₁
Φ η l nb = ψ₁ (up L1 η nb) (up1-dom η l nb)

Ω⊴top : L.Ω ℓ₁ ⊴ G.top
Ω⊴top = nt (λ y a q → u⊴ (em⊴ q))

Ω⊴Φ₀ : ∀ a .(l : Lgl B.zero a) .(nb : Nested B.zero a) →
  L.Ω ℓ₁ ⊴ Φ (G.em tt a) l nb
Ω⊴Φ₀ G.zero l nb = Ω⊴top
Ω⊴Φ₀ (G.suc a) l nb = ⊴l 0 (Ω⊴Φ₀ a l nb)
Ω⊴Φ₀ (G.lim f) l nb = ⊴l 0 (Ω⊴Φ₀ (f 0) (proj₂ l 0) (nb 0))
Ω⊴Φ₀ (G.lc () c t g) l nb
Ω⊴Φ₀ (G.em () a) l nb
Ω⊴Φ₀ G.top l nb = ⊴l 0 Ω⊴top

Ω⊴Φ : ∀ η .(l : Lgl L1 η) .(nb : Nested L1 η) → L.Ω ℓ₁ ⊴ Φ η l nb
Ω⊴Φ G.zero l nb = Ω⊴top
Ω⊴Φ (G.suc η) l nb = ⊴l 0 (Ω⊴Φ η l nb)
Ω⊴Φ (G.lim f) l nb = ⊴l 0 (Ω⊴Φ (f 0) (proj₂ l 0) (nb 0))
Ω⊴Φ (G.lc (inj₁ _) c t g) l nb = ⊴t
  (Ω⊴Φ t (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
Ω⊴Φ (G.lc (inj₂ ()) c t g) l nb
Ω⊴Φ (G.em _ a) l nb = Ω⊴Φ₀ a l nb
Ω⊴Φ G.top l nb = ⊴t (⊴l 0 Ω⊴top)

copies-⊴ : ∀ {A : T₁} {β} → A ⊴ β → ∀ n →
  iter (A L.+_) L.zero (suc n) ⊴ copies₁ β n
copies-⊴ p zero = p
copies-⊴ p (suc n) = ⊴-add₁ p (copies-⊴ p n)

suc-step : ∀ {A : T₁} {β} → A ⊴ β →
  L.lim (iter (A L.+_) L.zero) ⊴ successor₁ β
suc-step p = l⊴ λ where
  zero → z⊴
  (suc n) → ⊴l n (copies-⊴ p n)

Ψ₀⊴Φ₀ : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  .(l : Lgl B.zero a) .(nb : Nested B.zero a) → Ψ₀ y ⊴ Φ (G.em tt a) l nb
Ψ₀⊴Φ₀ z≼ a q l nb = Ω⊴Φ₀ a l nb
Ψ₀⊴Φ₀ (s≼s p) (G.suc a) refl l nb = suc-step (Ψ₀⊴Φ₀ p a refl l nb)
Ψ₀⊴Φ₀ (s≼s p) G.top refl l nb = suc-step (Ψ₀⊴Φ₀ p G.zero refl tt tt)
Ψ₀⊴Φ₀ (≼l n p) (G.lim f) refl l nb =
  ⊴l n (Ψ₀⊴Φ₀ p (f n) refl (proj₂ l n) (nb n))
Ψ₀⊴Φ₀ (l≼ h) a q l nb = l⊴ (λ n → Ψ₀⊴Φ₀ (h n) a q l nb)
Ψ₀⊴Φ₀ (≼i {p = ()} x ex p) a q l nb
Ψ₀⊴Φ₀ (i≼ {p = ()} h) a q l nb
Ψ₀⊴Φ₀ (≼u {r = ()} p) a q l nb
Ψ₀⊴Φ₀ (u≼ {r = ()} p) a q l nb

Ψ₀⊴Φ : ∀ {y : T₀} {η} → y ⊴ η → .(l : Lgl L1 η) .(nb : Nested L1 η) →
  Ψ₀ y ⊴ Φ η l nb
Ψ₀⊴Φ {η = η} z⊴ l nb = Ω⊴Φ η l nb
Ψ₀⊴Φ (s⊴s p) l nb = suc-step (Ψ₀⊴Φ p l nb)
Ψ₀⊴Φ (⊴s p) l nb = ⊴l 0 (Ψ₀⊴Φ p l nb)
Ψ₀⊴Φ (⊴l n p) l nb = ⊴l n (Ψ₀⊴Φ p (proj₂ l n) (nb n))
Ψ₀⊴Φ (l⊴ h) l nb = l⊴ (λ n → Ψ₀⊴Φ (h n) l nb)
Ψ₀⊴Φ (⊴t p) l nb = ⊴t
  (Ψ₀⊴Φ p (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
Ψ₀⊴Φ (em⊴ {a = a} q) l nb = Ψ₀⊴Φ₀ q a refl l nb

tr⁻≼ : ∀ (y : T₀) → L.tr⁻ L.z≅ y ≼ y
tr⁻≼ y = ≅→≼ (L.tr⁻-≅ L.z≅ (L.≅-refl⁰ y))

Ψ₁⊴Φ : ∀ {x : T₁} {η} → x ⊴ η → .(l : Lgl L1 η) .(nb : Nested L1 η) →
  Ψ₁ x ⊴ Φ η l nb
Ψ₁⊴Φ {η = η} z⊴ l nb = Ω⊴Φ η l nb
Ψ₁⊴Φ (s⊴s p) l nb = suc-step (Ψ₁⊴Φ p l nb)
Ψ₁⊴Φ (⊴s p) l nb = ⊴l 0 (Ψ₁⊴Φ p l nb)
Ψ₁⊴Φ (⊴l n p) l nb = ⊴l n (Ψ₁⊴Φ p (proj₂ l n) (nb n))
Ψ₁⊴Φ (l⊴ h) l nb = l⊴ (λ n → Ψ₁⊴Φ (h n) l nb)
Ψ₁⊴Φ (⊴t p) l nb = ⊴t
  (Ψ₁⊴Φ p (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
Ψ₁⊴Φ (nd b h) l nb = nd b (λ y a e q →
  Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) q))
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
Ψ₁⊴Φ (nt h) l nb = nd (s≼s z≼) (λ y a e q →
  Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q))
    (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
Ψ₁⊴Φ (u⊴ p) l nb = Ψ₀⊴Φ p l nb
```

## 4 目标层 0 的折叠把关系送到值前序

`NodeLower` 是结点处的一步：`Level` 的层 0 分支结点对层号 0 的 Ω 结点，下界不小于 1，
分支的折叠逐点 (输入按值相关时) 已有下界，则结点的折叠有下界。两条链同步归纳：参照是原链，
被验收一侧是加法链，后者的坐标不小于前者。它是 `RR4MonoFragment.pointwise-mono₁` 的跨族版本。

```agda
module NodeLower (f : T₀ → T₁) (same : ∀ y → f y ≅ f y)
  (c : R) .(w : Lgl B.zero c) .(b : Nested B.zero c) (t : B.LF)
  (g : (a : R) → .(Gd B.zero c a) → B.LF) (d : Dom (B.lc B.zero c w b t g))
  (base : V.𝟏 ≼ read c)
  (low : ∀ (y : T₀) a (e : Gd B.zero c a) → y ≼ read a →
    L.ψ⁰ (f y) ≼ read (ψ₀ (g a e) (Node₀.branch c w b t g d a e))) where

  open ChainLegal c
    (λ a e → ψ₀ (g a e) (Node₀.branch c w b t g d a e))
    (λ a e → ψ₀-legal (g a e) (Node₀.branch c w b t g d a e))
    (λ a e → ψ₀-positive (g a e) (Node₀.branch c w b t g d a e))
    (λ a e a′ e′ q → ψ₀-position (g a e) (g a′ e′)
      (Node₀.branch c w b t g d a e) (Node₀.branch c w b t g d a′ e′)
      (Node₀.directed c w b t g d a e a′ e′ q))
    (start c w b) (Node₀.seed c w b t g d)

  ref-step : T₀ → T₀
  ref-step y = L.ψ {i = L.zero} {k = ℓ₁} {ℓ = ℓ₁} L.zero (λ r → r) (f y)

  δ : ℕ → T₀
  δ = iter ref-step (L.suc L.zero)

  step≤ : ∀ y → ref-step y ≼ L.ψ⁰ (f y)
  step≤ y = ≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r} (same y)))

  here : ∀ n → L.ψ⁰ (f (δ n)) ≼
    read (ψ₀ (g (coordinate (points n)) (guards n))
      (Node₀.branch c w b t g d (coordinate (points n)) (guards n)))
  chain-lower : ∀ n → δ n ≼ read (coordinate (points n))

  here n = low (δ n) (coordinate (points n)) (guards n) (chain-lower n)

  chain-lower zero = base
  chain-lower (suc n) =
    ≼-trans (step≤ (δ n))
    (≼-trans (here n)
    (≼-trans (M.≼-+ˡ (read (coordinate (points n)))
        (read (ψ₀ (g (coordinate (points n)) (guards n))
          (Node₀.branch c w b t g d (coordinate (points n)) (guards n)))))
      (≅→≼ (L.≅-sym (read-add (coordinate (points n))
        (ψ₀ (g (coordinate (points n)) (guards n))
          (Node₀.branch c w b t g d (coordinate (points n)) (guards n))))))))

  node-lower : L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f) ≼
    read (ψ₀ (B.lc B.zero c w b t g) d)
  node-lower = l≼ (λ n → ≼l n (here n))
```

`fold-lower` 对关系的推导递归。左边的树要自相似 (`x ≅ x`)，只在结点处用：参照链的一步 `ψ` 与 `ψ⁰` 互模拟要它。
合法性与嵌套证据是相关的参数：读回的证书由它们造。

```agda
s≅⁻ : ∀ {k} {a b : L.Ordᶜ k} → L.suc a ≅ L.suc b → a ≅ b
s≅⁻ (L.s≅ e) = e

l≅⁻ : ∀ {k} {F F′ : ℕ → L.Ordᶜ k} → L.lim F ≅ L.lim F′ → ∀ n → F n ≅ F′ n
l≅⁻ (L.l≅ h) = h

lᵢ≅⁻ : ∀ {f f′ : T₀ → T₁} →
  L.limᵢ {i = L.zero} L.zero f ≅ L.limᵢ {i = L.zero} L.zero f′ →
  ∀ y → f y ≅ f′ y
lᵢ≅⁻ (L.lᵢ≅ e h) y = h y y (L.≅-refl⁰ y)

fold-lower : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ≅ x →
  (l : Lgl L1 η) (nb : Nested L1 η) →
  L.ψ⁰ x ≼ read (ψ₀ (up L1 η nb) (up1-dom η l nb))
fold-lower {η = η} z⊴ s l nb = one≼fold (up L1 η nb) (up1-dom η l nb)
fold-lower {η = G.suc η} (s⊴s p) s l nb =
  suc-lower (ψ₀ (up L1 η nb) (up1-dom η l nb)) (fold-lower p (s≅⁻ s) l nb)
fold-lower (⊴s p) s l nb = ≼l 1 (fold-lower p s l nb)
fold-lower (⊴l n p) s l nb = ≼l n (fold-lower p s (proj₂ l n) (nb n))
fold-lower (l⊴ h) s l nb = l≼ (λ n → fold-lower (h n) (l≅⁻ s n) l nb)
fold-lower {η = G.lc (inj₁ tt) c t g} (⊴t p) s l nb =
  ≼-trans
    (fold-lower p s (proj₁ (proj₂ (proj₂ (proj₂ l))))
      (proj₁ (proj₂ (proj₂ nb))))
    (read-cp _ (ψ₀-position
      (up L1 t (proj₁ (proj₂ (proj₂ nb))))
      (up L1 (G.lc (inj₁ tt) c t g) nb)
      (up1-dom t (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
      (up1-dom (G.lc (inj₁ tt) c t g) l nb)
      (fst self)))
fold-lower {η = G.lc (inj₁ tt) c t g} (nd {f = f} base h) s l nb =
  NodeLower.node-lower f (lᵢ≅⁻ s) c (proj₁ nb) (proj₁ (proj₂ nb))
    (up L1 t (proj₁ (proj₂ (proj₂ nb))))
    (λ a e → up L1 (g a e) (proj₂ (proj₂ (proj₂ nb)) a e))
    (up1-dom (G.lc (inj₁ tt) c t g) l nb) base
    (λ y a e q → fold-lower (h y a e q) (lᵢ≅⁻ s y)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
fold-lower (nt {f = f} h) s l nb =
  NodeLower.node-lower f (lᵢ≅⁻ s) one tt tt (B.suc B.zero)
    (λ a e → up B.zero a (proj₂ (proj₂ e)))
    (up1-dom G.top l nb) (s≼s z≼)
    (λ y a e q → fold-lower (h y a q) (lᵢ≅⁻ s y)
      (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
fold-lower {η = G.em tt a} (em⊴ q) s l nb =
  ≼-trans (V.ψ⁰-mono⁰ q)
    (≅→≼ (L.≅-sym (read-fold₀ a nb (up1-dom (G.em tt a) l nb))))
fold-lower (u⊴ {y = y} p) s l nb = fold-lower p (L.≅-refl⁰ y) l nb
```

## 5 Ω₂：两条链同步，下界

`Ω₂-points` 是 `ψ₀ Ω₂` 的 gt 行里那条链 ([YiIrrFbInst](YiIrrFbInst.lagda.md))。参照链的第 n 点被它的第 n 点压住：
起点是 Ω₁ 对 `top`；下一步，参照是 `Ψ₁ γₙ`，被验收一侧是 `ηₙ + ψ₁(读回 ηₙ)`，多出的前缀由 `⊴-+ˡ` 吸收。

```agda
chain-⊴ : ∀ n → γ n ⊴ at (Ω₂-points n)
chain-⊴ zero = Ω⊴top
chain-⊴ (suc n) =
  ⊴-+ˡ (at (Ω₂-points n))
    (Ψ₁⊴Φ (chain-⊴ n) (proj₁ (proj₂ (Ω₂-guards n))) (proj₂ (proj₂ (Ω₂-guards n))))

Ω₂-lower : L.ψ⁰ (L.Ω ℓ₂) ≼ read Ω₂-fold
Ω₂-lower = l≼ (λ n → ≼l n
  (fold-lower (chain-⊴ n) (γ-self n)
    (proj₁ (proj₂ (Ω₂-guards n))) (proj₂ (proj₂ (Ω₂-guards n)))))
```

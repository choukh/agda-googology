# YiRawFold 第 4 层：ψ₀(Ω₃) 的下界，目标层 2 的折叠

**验收文件，档位：编译定理 (引理)。** 第 2 层的逐点前序 `_⊴₂_` 与它的加法、前缀、搬运引理原样取自 [YiLvVal3Base](YiLvVal3Base.lagda.md) §1 到 §3；
本篇把那里的 §4 (`Ω₂⊴ψ₂`, `B₀`, `B₁`, `B₂`：参照的折叠 ⊴₂ 目标层 2 的折叠) 改写在 `YiRawFold.Ψ` 的行上，推进用的外部派发是 `X₂ = ownT 2`。
入口 [YiRawVal3](YiRawVal3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawVal3Base where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Nested; Lgl; Gd)
open import OCF.Align.YiIrrIf using (R)
open import OCF.Align.YiLvFoldBase using (keep)
open import OCF.Align.YiRawFoldBase using (Ext; wayOf; inS)
import OCF.Align.YiRawFold as N
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvVal2 using (ℓ₁; ℓ₂; T₀; T₁; L1; R₁; _⊴_; z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; nt; em⊴; u⊴; tr⁻≼; Ω⊴top)
open import OCF.Align.YiLvVal3Base
  using (T₂; L2; R₂; _⊴₂_; z₂; ss₂; s₂; l₂; ll₂; b1; b0; nd1; nd0; nt₂; em₂; u₂;
         suc-step₂; TR₁; Ω₂⊴top)
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open V using (_≼_; ≼-trans; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)

X₂ : Ext L2 L2
X₂ = N.ownT L2 tt tt

-- 目标层 2 上层号 1, 0 的结点都保留在规范槽位 (与旧折叠的 wayᵇ 同).
X₂-keeps₁ : wayOf X₂ (inj₁ tt) ≡ keep (inj₁ tt) refl
X₂-keeps₁ = refl

X₂-keeps₀ : wayOf X₂ (inj₂ (inj₁ tt)) ≡ keep (inj₂ (inj₁ tt)) refl
X₂-keeps₀ = refl

X₂-keeps₀′ : wayOf (inS X₂) (inj₁ tt) ≡ keep (inj₂ (inj₁ tt)) refl
X₂-keeps₀′ = refl
```

## 1 Ω₂ 在下

```agda
Ω₂⊴ψ₂₀ : ∀ (x : Ext L2 B.zero) a .(l : Lgl B.zero a) .(nb : Nested B.zero a) →
  L.Ω ℓ₂ ⊴₂ N.Ψ L2 B.zero tt tt x a l nb
Ω₂⊴ψ₂₀ x G.zero l nb = Ω₂⊴top
Ω₂⊴ψ₂₀ x (G.suc a) l nb = l₂ 0 (Ω₂⊴ψ₂₀ x a l nb)
Ω₂⊴ψ₂₀ x (G.lim f) l nb = l₂ 0 (Ω₂⊴ψ₂₀ x (f 0) (proj₂ l 0) (nb 0))
Ω₂⊴ψ₂₀ x (G.lc () c t g) l nb
Ω₂⊴ψ₂₀ x (G.em () a) l nb
Ω₂⊴ψ₂₀ x G.top l nb = l₂ 0 Ω₂⊴top

Ω₂⊴ψ₂₁ : ∀ (a : R₁) .(l : Lgl L1 a) .(nb : Nested L1 a) →
  L.Ω ℓ₂ ⊴₂ N.Ψ L2 L1 tt tt (inS X₂) a l nb
Ω₂⊴ψ₂₁ G.zero l nb = Ω₂⊴top
Ω₂⊴ψ₂₁ (G.suc a) l nb = l₂ 0 (Ω₂⊴ψ₂₁ a l nb)
Ω₂⊴ψ₂₁ (G.lim f) l nb = l₂ 0 (Ω₂⊴ψ₂₁ (f 0) (proj₂ l 0) (nb 0))
Ω₂⊴ψ₂₁ (G.lc (inj₁ _) c t g) l nb = b0 (λ e →
  Ω₂⊴ψ₂₁ (g c e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
Ω₂⊴ψ₂₁ (G.lc (inj₂ ()) c t g) l nb
Ω₂⊴ψ₂₁ (G.em _ a) l nb = Ω₂⊴ψ₂₀ (inS (inS X₂)) a l nb
Ω₂⊴ψ₂₁ G.top l nb = b0 (λ e → l₂ 0 Ω₂⊴top)

Ω₂⊴ψ₂ : ∀ (η : R₂) .(l : Lgl L2 η) .(nb : Nested L2 η) →
  L.Ω ℓ₂ ⊴₂ N.Ψ L2 L2 tt tt X₂ η l nb
Ω₂⊴ψ₂ G.zero l nb = Ω₂⊴top
Ω₂⊴ψ₂ (G.suc a) l nb = l₂ 0 (Ω₂⊴ψ₂ a l nb)
Ω₂⊴ψ₂ (G.lim f) l nb = l₂ 0 (Ω₂⊴ψ₂ (f 0) (proj₂ l 0) (nb 0))
Ω₂⊴ψ₂ (G.lc (inj₁ _) c t g) l nb = b1 (λ e →
  Ω₂⊴ψ₂ (g c e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
Ω₂⊴ψ₂ (G.lc (inj₂ (inj₁ _)) c t g) l nb = b0 (λ e →
  Ω₂⊴ψ₂ (g c e) (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
Ω₂⊴ψ₂ (G.lc (inj₂ (inj₂ ())) c t g) l nb
Ω₂⊴ψ₂ (G.em _ a) l nb = Ω₂⊴ψ₂₁ a l nb
Ω₂⊴ψ₂ G.top l nb = b1 (λ e → Ω₂⊴ψ₂₁ G.top (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
```

## 2 参照的折叠在下

```agda
B₀ : ∀ (x : Ext L2 B.zero) {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  ∀ {ℓ} (p : ℓ₂ L.<ᴵ ℓ) (σ : L.Simᴵ L.zero ℓ) →
  .(l : Lgl B.zero a) .(nb : Nested B.zero a) → L.ψ p σ y ⊴₂ N.Ψ L2 B.zero tt tt x a l nb
B₀ x z≼ a q p σ l nb = Ω₂⊴ψ₂₀ x a l nb
B₀ x (s≼s r) (G.suc a) refl p σ l nb = suc-step₂ (B₀ x r a refl p σ l nb)
B₀ x (s≼s r) G.top refl p σ l nb = suc-step₂ (B₀ x r G.zero refl p σ tt tt)
B₀ x (≼l n r) (G.lim f) refl p σ l nb = l₂ n (B₀ x r (f n) refl p σ (proj₂ l n) (nb n))
B₀ x (l≼ h) a q p σ l nb = ll₂ (λ n → B₀ x (h n) a q p σ l nb)
B₀ x (≼i {p = ()} z ez r) a q p σ l nb
B₀ x (i≼ {p = ()} h) a q p σ l nb
B₀ x (≼u {r = ()} r) a q p σ l nb
B₀ x (u≼ {r = ()} r) a q p σ l nb

B₁ : ∀ {k} {y : L.Ordᶜ k} {a : R₁} → y ⊴ a →
  ∀ {ℓ} (p : ℓ₂ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(l : Lgl L1 a) .(nb : Nested L1 a) → L.ψ p σ y ⊴₂ N.Ψ L2 L1 tt tt (inS X₂) a l nb
B₁ {a = a} z⊴ p σ l nb = Ω₂⊴ψ₂₁ a l nb
B₁ (s⊴s r) p σ l nb = suc-step₂ (B₁ r p σ l nb)
B₁ (⊴s r) p σ l nb = l₂ 0 (B₁ r p σ l nb)
B₁ {a = G.lim F} (⊴l n r) p σ l nb = l₂ n (B₁ r p σ (proj₂ l n) (nb n))
B₁ (l⊴ h) p σ l nb = ll₂ (λ n → B₁ (h n) p σ l nb)
B₁ (⊴b {c = c} {t = t} {g = g} h) p σ l nb = b0 (λ e →
  B₁ (h e) p σ (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
B₁ (nd {f = f} {c = c} {t = t} {g = g} base h) p σ l nb with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ (L.suc L.zero)) = nd0 {q = L.suc L.zero} base (λ y a e r →
  B₁ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via _ ())
... | injᶜ ()
B₁ (nt {f = f} h) p σ l nb with L.<ᴵ-dec (σ L.zero) p
... | injᵃ (L.via L.z≅ (L.suc L.zero)) = nd0 {q = L.suc L.zero} (s≼s z≼) (λ y a e r →
  B₁ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) r)) p σ (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via _ ())
... | injᶜ ()
B₁ (em⊴ {a = a} q) p σ l nb = B₀ (inS (inS X₂)) q a refl p σ l nb
B₁ (u⊴ r) p σ l nb = B₁ r p (λ q → σ (L.suc q)) l nb

B₂ : ∀ {k} {x : L.Ordᶜ k} {η : R₂} → x ⊴₂ η →
  ∀ {ℓ} (p : ℓ₂ L.<ᴵ ℓ) (σ : L.Simᴵ k ℓ) →
  .(l : Lgl L2 η) .(nb : Nested L2 η) → L.ψ p σ x ⊴₂ N.Ψ L2 L2 tt tt X₂ η l nb
B₂ {η = η} z₂ p σ l nb = Ω₂⊴ψ₂ η l nb
B₂ (ss₂ r) p σ l nb = suc-step₂ (B₂ r p σ l nb)
B₂ (s₂ r) p σ l nb = l₂ 0 (B₂ r p σ l nb)
B₂ {η = G.lim F} (l₂ n r) p σ l nb = l₂ n (B₂ r p σ (proj₂ l n) (nb n))
B₂ (ll₂ h) p σ l nb = ll₂ (λ n → B₂ (h n) p σ l nb)
B₂ (b1 {c = c} {t = t} {g = g} h) p σ l nb = b1 (λ e →
  B₂ (h e) p σ (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
B₂ (b0 {c = c} {t = t} {g = g} h) p σ l nb = b0 (λ e →
  B₂ (h e) p σ (proj₂ (proj₂ (proj₂ (proj₂ l))) c e) (proj₂ (proj₂ (proj₂ nb)) c e))
B₂ (nd1 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ l nb
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via (L.s≅ L.z≅) L.zero) = nd1 {q = L.zero} base (λ y a e r →
  B₂ (h (L.tr⁻ (L.s≅ L.z≅) y) a e (TR₁ r)) p σ
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ (L.s≅ ())
B₂ (nd0 {q = q} {f = f} {c = c} {t = t} {g = g} base h) p σ l nb
  with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via L.z≅ (L.suc L.zero)) = nd0 {q = L.suc L.zero} base (λ y a e r →
  B₂ (h (L.tr⁻ L.z≅ y) a e (≼-trans (tr⁻≼ y) r)) p σ
    (proj₂ (proj₂ (proj₂ (proj₂ l))) a e) (proj₂ (proj₂ (proj₂ nb)) a e))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via _ ())
... | injᶜ ()
B₂ (nt₂ {q = q} {f = f} h) p σ l nb with L.<ᴵ-dec (σ q) p
... | injᵃ (L.via (L.s≅ L.z≅) L.zero) = nd1 {q = L.zero} Ω⊴top (λ y a e r →
  B₂ (h (L.tr⁻ (L.s≅ L.z≅) y) a (TR₁ r)) p σ (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
... | injᵃ (L.via _ (L.suc (L.suc ())))
... | injᵇ (L.via () L.zero)
... | injᵇ (L.via _ (L.suc ()))
... | injᶜ (L.s≅ ())
B₂ (em₂ r) p σ l nb = B₁ r p σ l nb
B₂ (u₂ r) p σ l nb = B₂ r p (λ q → σ (L.suc q)) l nb
```

# 不累加的世界: 折叠的同余

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). `ψQ`: 与 [CumUpPsi](CumUpPsi.lagda.md) 同形, 少了第 0 层的 `ψ₀`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumPsi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_≈ᴬ_; z≈; s≈; l≈; ≈ᴬ-refl; ≈ᴬ-sym; ≈ᴬ-trans)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
```

## §2 `ψQ`

```agda
ψ⁰Q : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′

ψmQ : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : t′ ⊲ v′) (av′ : a′ ⊲ v′) →
     t ≈ᴬ t′ → x ≈ y → ψᵐ q t x gu v gv uv tv av ≈ ψᵐ q t′ y gu′ v′ gv′ uv′ tv′ av′

ψQ : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : t′ ⊲ v′) (av′ : a′ ⊲ v′) →
     t ≈ᴬ t′ → x ≈ y → ψ q t x gu v gv uv tv av ≈ ψ q t′ y gu′ v′ gv′ uv′ tv′ av′
ψQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e = ψmQ x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e

ψmQ {q = q} {t} {t′} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e
  with mx gu gv uv tv av | mx-is gu gv uv tv av | mx gu′ gv′ uv′ tv′ av′ | mx-is gu′ gv′ uv′ tv′ av′
... | mx′ m gm um tm am mv | is | mx′ m′ gm′ um′ tm′ am′ mv′ | is′ =
  ≈ow (ψ⁰ q t x gu m gm um tm am) mv′ gm′ (ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′) (ψ⁰Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e)

-- 左边是包装: 走进去
ψ⁰lm : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψᵐ q t x gu m gm um tm am ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰rm : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψᵐ q t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰l : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψ q t x gu m gm um tm am ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰l x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e

ψ⁰lm x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e with mx gu gm um tm am | mx-is gu gm um tm am
... | mx′ m₁ g₁ u₁ t₁ a₁ _ | is₁ = ψ⁰Q x y gu gu′ m₁ g₁ u₁ t₁ a₁ is₁ m′ gm′ um′ tm′ am′ is′ et e

ψ⁰r : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ q t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰r x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e = ψ⁰rm x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e

ψ⁰rm {q = q} {t} {t′} x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e with mx gu′ gm′ um′ tm′ am′ | mx-is gu′ gm′ um′ tm′ am′
... | mx′ m₁ g₁ u₁ t₁ a₁ mv | is₁ = ≈ow (ψ⁰ q t x gu m gm um tm am) mv g₁ (ψ⁰ q t′ y gu′ m₁ g₁ u₁ t₁ a₁) (ψ⁰Q x y gu gu′ m gm um tm am is m₁ g₁ u₁ t₁ a₁ is₁ et e)

ψLl : ∀ {p h k u p′ a′ u′ q t t′} (j : h <ᴺ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (km : k ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → ELl j x y → ψL q t j x gu m gm um tm km ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′
ψLl zero x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl (suc j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e

ψLr : ∀ {p a u p′ h k u′ q t t′} (x : 𝓞 p a u) (j : h <ᴺ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (km′ : k ⊲ m′) →
      t ≈ᴬ t′ → ELr x j y → ψ⁰ q t x gu m gm um tm am ≈ ψL q t′ j y gu′ m′ gm′ um′ tm′ km′
ψLr x zero y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψ⁰r x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr x (suc j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e

-- 左边包装
ψ⁰Q (oe es x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l x y gu gu′ m gm um tm (⊲-tr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q (oe (el n) x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l x y gu gu′ m gm um tm (⊲-tr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q (oL j k e₁ x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLl j x y gu gu′ m gm um tm (⊲-tr e₁ um) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q (ow p g x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l x y g gu′ m gm (⊲-tr p um) tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q X@o0 (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q X@o0 (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q X@o0 (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q X@(os x) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q X@(os x) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q X@(os x) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q X@(ol F) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q X@(ol F) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q X@(ol F) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q X@(oi r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q X@(oi r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q X@(oi r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q X@(od j k r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q X@(od j k r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q X@(od j k r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q X@(oc x f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q X@(oc x f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q X@(oc x f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
-- 对角
ψ⁰Q {q = q} o0 o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ≈-Ωat q gm gm′ et
ψ⁰Q (os x) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e) =
  λ n → rep≈ et (m≈ is is′ um tm am um′ tm′ am′ eu et ea) (ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e) gm gm′ n
ψ⁰Q (ol F) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e =
  λ n → ψQ (F n) (G n) gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et (e n)
ψ⁰Q {p} {a} {q = q} {t} {t′} (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (refl , ea , eu , ek , N) with <ᴺ-dec p q
... | injᵃ i = refl , refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i y y′ d)))
... | injᵇ _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat p gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) am) am m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′ ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | injᶜ refl with cmpN (≪∘ r am) tm (lgw gm) | cmpN (≪∘ r′ am′) tm′ (lgw gm′)
...   | keep s | keep s′ = refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q′ = ⊥-elim (clash s q′ ek et)
...   | rise q′ | keep s′ = ⊥-elim (clash s′ q′ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat p gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) am) am m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′ ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q {q = q} {t} {t′} (od {h = h₀} j k r f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , refl , ea , eu , ek , N) with <ᴺ-dec h₀ q
... | injᵃ i = refl , refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i y y′ d)))
... | injᵇ _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₀ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′) n
  ch zero = ≈-Ωat h₀ gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) um) am m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′ ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | injᶜ refl with cmpN (≪∘ r um) tm (lgw gm) | cmpN (≪∘ r′ um′) tm′ (lgw gm′)
...   | keep s | keep s′ = refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q′ = ⊥-elim (clash s q′ ek et)
...   | rise q′ | keep s′ = ⊥-elim (clash s′ q′ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₀ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′) n
  ch zero = ≈-Ωat h₀ gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) um) am m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′ ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q (oc x f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e , N) =
  refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e ,
  (λ {v} {v′} w w′ g g′ vv → ψQ (f (⊲-tr um w) g) (f′ (⊲-tr um′ w′) g′) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et (N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv))
ψ⁰Q o0 (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q o0 (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q o0 (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q o0 (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q o0 (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (os x) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (os x) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (os x) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (os x) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (os x) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (ol F) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (ol F) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (ol F) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (ol F) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (ol F) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oi r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oi r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oi r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oi r f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oi r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (od j k r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (od j k r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (od j k r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (od j k r f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (od j k r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oc x f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oc x f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oc x f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oc x f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q (oc x f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()

-- 第 0 层
```

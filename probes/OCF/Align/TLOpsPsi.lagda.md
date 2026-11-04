# 树的算子语言 (三): 折叠的同余

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumPsi](NoCumPsi.lagda.md) 改写. 两边的高度比较各走各的公共上界 (`H`, `H′`), 结果模 `◁` 相同: 错配由 `no◁◁`, `<irr` 排除, 这是这里唯一新增的东西. 目标高度 $q$, $q′$ 分开写, 只在需要的分支合一, 否则 `teq` 对 `teq` 要 K.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsPsi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import Relation.Binary.PropositionalEquality using (sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_≈ᴬ_; z≈; s≈; l≈; ≈ᴬ-refl; ≈ᴬ-sym; ≈ᴬ-trans)
open import OCF.Align.TLOpsW
open import OCF.Align.TLOpsEq
```

## §2 `ψQ`

```agda
ψ⁰Q : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t H x gu m gm um tm am ≈ ψ⁰ q′ t′ H′ y gu′ m′ gm′ um′ tm′ am′

ψmQ : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : t′ ⊲ v′) (av′ : a′ ⊲ v′) →
     t ≈ᴬ t′ → x ≈ y → ψᵐ q t H x gu v gv uv tv av ≈ ψᵐ q′ t′ H′ y gu′ v′ gv′ uv′ tv′ av′

ψQ : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : t′ ⊲ v′) (av′ : a′ ⊲ v′) →
     t ≈ᴬ t′ → x ≈ y → ψ q t H x gu v gv uv tv av ≈ ψ q′ t′ H′ y gu′ v′ gv′ uv′ tv′ av′
ψQ H H′ Q x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e = ψmQ H H′ Q x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e

ψmQ {q = q} {q′ = q′} {t = t} {t′ = t′} H H′ Q x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e
  with mx gu gv uv tv av | mx-is gu gv uv tv av | mx gu′ gv′ uv′ tv′ av′ | mx-is gu′ gv′ uv′ tv′ av′
... | mx′ m gm um tm am mv | is | mx′ m′ gm′ um′ tm′ am′ mv′ | is′ =
  ≈ow (ψ⁰ q t H x gu m gm um tm am) mv′ gm′ (ψ⁰ q′ t′ H′ y gu′ m′ gm′ um′ tm′ am′) (ψ⁰Q H H′ Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e)

-- 左边是包装: 走进去
ψ⁰lm : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψᵐ q t H x gu m gm um tm am ≈ ψ⁰ q′ t′ H′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰rm : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t H x gu m gm um tm am ≈ ψᵐ q′ t′ H′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰l : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψ q t H x gu m gm um tm am ≈ ψ⁰ q′ t′ H′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰l H H′ Q x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm H H′ Q x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e

ψ⁰lm H H′ Q x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e with mx gu gm um tm am | mx-is gu gm um tm am
... | mx′ m₁ g₁ u₁ t₁ a₁ _ | is₁ = ψ⁰Q H H′ Q x y gu gu′ m₁ g₁ u₁ t₁ a₁ is₁ m′ gm′ um′ tm′ am′ is′ et e

ψ⁰r : ∀ {p a u p′ a′ u′ q q′ t t′} (H : Hk p q) (H′ : Hk p′ q′) (Q : q ≡ q′) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t H x gu m gm um tm am ≈ ψ q′ t′ H′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰r H H′ Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e = ψ⁰rm H H′ Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e

ψ⁰rm {q = q} {q′ = q′} {t = t} {t′ = t′} H H′ Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e with mx gu′ gm′ um′ tm′ am′ | mx-is gu′ gm′ um′ tm′ am′
... | mx′ m₁ g₁ u₁ t₁ a₁ mv | is₁ = ≈ow (ψ⁰ q t H x gu m gm um tm am) mv g₁ (ψ⁰ q′ t′ H′ y gu′ m₁ g₁ u₁ t₁ a₁) (ψ⁰Q H H′ Q x y gu gu′ m gm um tm am is m₁ g₁ u₁ t₁ a₁ is₁ et e)

ψLl : ∀ {p h k u p′ a′ u′ q q′ t t′} (H : Hk h q) (H′ : Hk p′ q′) (Q : q ≡ q′) (j : h ◁ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (km : k ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → ELl j x y → ψL q t H j x gu m gm um tm km ≈ ψ⁰ q′ t′ H′ y gu′ m′ gm′ um′ tm′ am′
ψLl H H′ Q zero x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l H H′ Q x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl H H′ Q (self n₉) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l H H′ Q x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl H H′ Q (suc j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl H H′ Q j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl H H′ Q (lim n₉ j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl H H′ Q j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e

ψLr : ∀ {p a u p′ h k u′ q q′ t t′} (H : Hk p q) (H′ : Hk h q′) (Q : q ≡ q′) (x : 𝓞 p a u) (j : h ◁ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (km′ : k ⊲ m′) →
      t ≈ᴬ t′ → ELr x j y → ψ⁰ q t H x gu m gm um tm am ≈ ψL q′ t′ H′ j y gu′ m′ gm′ um′ tm′ km′
ψLr H H′ Q x zero y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψ⁰r H H′ Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr H H′ Q x (self n₉) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψ⁰r H H′ Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr H H′ Q x (suc j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr H H′ Q x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr H H′ Q x (lim n₉ j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr H H′ Q x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e

-- 左边包装
ψ⁰Q H H′ Q (oe es x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l H H′ Q x y gu gu′ m gm um tm (⊲-tr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q H H′ Q (oe (el n) x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l H H′ Q x y gu gu′ m gm um tm (⊲-tr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q H H′ Q (oL j k e₁ x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLl (hk◁ j H) H′ Q j x y gu gu′ m gm um tm (⊲-tr e₁ um) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q H H′ Q (ow p g x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l H H′ Q x y g gu′ m gm (⊲-tr p um) tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q H H′ Q X@o0 (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q H H′ Q X@o0 (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q H H′ Q X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr H (hk◁ j₂ H′) Q X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q H H′ Q X@o0 (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q H H′ Q X@(os x) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q H H′ Q X@(os x) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q H H′ Q X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr H (hk◁ j₂ H′) Q X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q H H′ Q X@(os x) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q H H′ Q X@(ol F) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q H H′ Q X@(ol F) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q H H′ Q X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr H (hk◁ j₂ H′) Q X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q H H′ Q X@(ol F) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q H H′ Q X@(oi r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q H H′ Q X@(oi r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q H H′ Q X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr H (hk◁ j₂ H′) Q X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q H H′ Q X@(oi r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q H H′ Q X@(od j k r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q H H′ Q X@(od j k r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q H H′ Q X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr H (hk◁ j₂ H′) Q X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q H H′ Q X@(od j k r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q H H′ Q X@(oc x f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q H H′ Q X@(oc x f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q H H′ Q X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr H (hk◁ j₂ H′) Q X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q H H′ Q X@(oc x f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r H H′ Q X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
-- 对角
ψ⁰Q {q = q} H H′ refl o0 o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ≈-Ωat q gm gm′ et
ψ⁰Q H H′ refl (os x) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e) =
  λ n → rep≈ et (m≈ is is′ um tm am um′ tm′ am′ eu et ea) (ψQ H H′ refl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e) gm gm′ n
ψ⁰Q H H′ Q (ol F) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e =
  λ n → ψQ H H′ Q (F n) (G n) gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et (e n)
ψ⁰Q {p} {a} {q = q} {t = t} {t′ = t′} H H′ Q (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (refl , ea , eu , ek , N) with trH H | trH H′
... | tlt i | tlt i′ = Q , refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ H H′ Q (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i′ y y′ d)))
... | tgt _ | tgt _ = λ n → ψQ H H′ Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (hkR H) (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p k′ (hkR H′) (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat p gm gm′ ek
  ch (suc n) = ψQ (hkR H) (hkR H′) refl (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) am) am m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′ ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | tlt i | tgt i′ = ⊥-elim (no◁◁ (subst (_ ◁_) Q i) i′)
... | tgt i | tlt i′ = ⊥-elim (no◁◁ i′ (subst (_◁ _) Q i))
... | tlt i | teq = ⊥-elim (<irr (subst (_ ◁_) Q i))
... | teq | tlt i′ = ⊥-elim (<irr (subst (_ ◁_) (sym Q) i′))
... | tgt i | teq = ⊥-elim (<irr (subst (_◁ _) Q i))
... | teq | tgt i′ = ⊥-elim (<irr (subst (_◁ _) (sym Q) i′))
... | teq | teq with cmpN (≪∘ r am) tm (lgw gm) | cmpN (≪∘ r′ am′) tm′ (lgw gm′)
...   | keep s | keep s′ = refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ H H′ Q (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q′ = ⊥-elim (clash s q′ ek et)
...   | rise q′ | keep s′ = ⊥-elim (clash s′ q′ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ H H′ Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (hkR H) (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p k′ (hkR H′) (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat p gm gm′ ek
  ch (suc n) = ψQ (hkR H) (hkR H′) refl (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) am) am m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′ ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q {q = q} {t = t} {t′ = t′} H H′ Q (od {h = h₀} j k r f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , refl , ea , eu , ek , N) with trH (hk◁ j H) | trH (hk◁ j′ H′)
... | tlt i | tlt i′ = Q , refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ H H′ Q (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i′ y y′ d)))
... | tgt _ | tgt _ = λ n → ψQ H H′ Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (hkD j H) (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₀ k′ (hkD j′ H′) (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′) n
  ch zero = ≈-Ωat h₀ gm gm′ ek
  ch (suc n) = ψQ (hkD j H) (hkD j′ H′) refl (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) um) am m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′ ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | tlt i | tgt i′ = ⊥-elim (no◁◁ (subst (_ ◁_) Q i) i′)
... | tgt i | tlt i′ = ⊥-elim (no◁◁ i′ (subst (_◁ _) Q i))
... | tlt i | teq = ⊥-elim (<irr (subst (_ ◁_) Q i))
... | teq | tlt i′ = ⊥-elim (<irr (subst (_ ◁_) (sym Q) i′))
... | tgt i | teq = ⊥-elim (<irr (subst (_◁ _) Q i))
... | teq | tgt i′ = ⊥-elim (<irr (subst (_◁ _) (sym Q) i′))
... | teq | teq with cmpN (≪∘ r um) tm (lgw gm) | cmpN (≪∘ r′ um′) tm′ (lgw gm′)
...   | keep s | keep s′ = refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ H H′ Q (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q′ = ⊥-elim (clash s q′ ek et)
...   | rise q′ | keep s′ = ⊥-elim (clash s′ q′ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ H H′ Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (hkD j H) (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₀ k′ (hkD j′ H′) (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′) n
  ch zero = ≈-Ωat h₀ gm gm′ ek
  ch (suc n) = ψQ (hkD j H) (hkD j′ H′) refl (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) um) am m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′ ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q H H′ Q (oc x f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e , N) =
  Q , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ψQ H H′ Q x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e ,
  (λ {v} {v′} w w′ g g′ vv → ψQ H H′ Q (f (⊲-tr um w) g) (f′ (⊲-tr um′ w′) g′) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et (N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv))
ψ⁰Q H H′ Q o0 (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q o0 (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q o0 (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q o0 (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q o0 (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (os x) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (os x) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (os x) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (os x) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (os x) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (ol F) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (ol F) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (ol F) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (ol F) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (ol F) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oi r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oi r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oi r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oi r f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oi r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (od j k r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (od j k r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (od j k r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (od j k r f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (od j k r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oc x f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oc x f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oc x f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oc x f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q H H′ Q (oc x f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()

-- 第 0 层
```

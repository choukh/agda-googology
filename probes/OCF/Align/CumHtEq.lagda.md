# 序数高度的世界: 结构等价

> 不含记号, 不含累加. 结论写在 [CumHt](CumHt.lagda.md). `x ≈ y`: 与 [CumUpEq](CumUpEq.lagda.md) 同形, 差别: **高度也只模 `≈ᴴ`** (`CumUp` 是字面的 $\equiv$), 因为 $p$ 位读自世界, 而世界只模 `≈ᴬ` 相同. `mx` 的值模 `≈ᴬ` 与证据无关的定理在 `CumHtTree.m≈`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHtEq where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂; cong)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumHtBase
open import OCF.Align.CumHtTree
```

## §3 `≈`

```agda
infix 4 _≈′_ _≈_
_≈′_ : ∀ {ρ p a u ρ′ p′ a′ u′} → 𝓞′ ρ p a u → 𝓞′ ρ′ p′ a′ u′ → Set
ELl′ : ∀ {r p h k u r′ p′ a′ u′} (j : h <ᴴ ⟨ r , p ⟩) → Bx (Low′ r p j k u) → 𝓞′ r′ p′ a′ u′ → Set
ELr′ : ∀ {r p a u r′ p′ h k u′} → 𝓞′ r p a u → (j : h <ᴴ ⟨ r′ , p′ ⟩) → Bx (Low′ r′ p′ j k u′) → Set
EqW′ : ∀ {r p h k u r′ p′ h′ k′ u′} (j : h <ᴴ ⟨ r , p ⟩) (j′ : h′ <ᴴ ⟨ r′ , p′ ⟩) → Bx (Low′ r p j k u) → Bx (Low′ r′ p′ j′ k′ u′) → Set
EqV′ : ∀ {r p a b u r′ p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) → Vs′ r p a R u → Vs′ r′ p′ a′ R′ u′ → Set
EVC′ : ∀ {r p a b u r′ p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) → Vc′ r p a P u → Vs′ r′ p′ a′ R′ u′ → Set
ELO′ : ∀ {r p b u r′ p′ a′ b′ u′} → 𝓞′ r p b u → (R′ : Strict b′ a′) → Vs′ r′ p′ a′ R′ u′ → Set
EOC′ : ∀ {r p b u r′ p′ a′ b′ u′} → 𝓞′ r p b u → (P : b′ ⊲ a′) → Vc′ r′ p′ a′ P u′ → Set

oe es x ≈′ y = x ≈′ y
oe (el n) x ≈′ y = x ≈′ y
oL j k e x ≈′ y = ELl′ j x y
ow p g x ≈′ y = x ≈′ y
_≈′_ X@o0 (oe es y) = X ≈′ y
_≈′_ X@o0 (oe (el n) y) = X ≈′ y
_≈′_ X@o0 (oL j k₂ e y) = ELr′ X j y
_≈′_ X@o0 (ow p g y) = X ≈′ y
_≈′_ X@(os x) (oe es y) = X ≈′ y
_≈′_ X@(os x) (oe (el n) y) = X ≈′ y
_≈′_ X@(os x) (oL j k₂ e y) = ELr′ X j y
_≈′_ X@(os x) (ow p g y) = X ≈′ y
_≈′_ X@(ol F) (oe es y) = X ≈′ y
_≈′_ X@(ol F) (oe (el n) y) = X ≈′ y
_≈′_ X@(ol F) (oL j k₂ e y) = ELr′ X j y
_≈′_ X@(ol F) (ow p g y) = X ≈′ y
_≈′_ X@(oi r h) (oe es y) = X ≈′ y
_≈′_ X@(oi r h) (oe (el n) y) = X ≈′ y
_≈′_ X@(oi r h) (oL j k₂ e y) = ELr′ X j y
_≈′_ X@(oi r h) (ow p g y) = X ≈′ y
_≈′_ X@(od i k r h) (oe es y) = X ≈′ y
_≈′_ X@(od i k r h) (oe (el n) y) = X ≈′ y
_≈′_ X@(od i k r h) (oL j k₂ e y) = ELr′ X j y
_≈′_ X@(od i k r h) (ow p g y) = X ≈′ y
_≈′_ X@(oc x h) (oe es y) = X ≈′ y
_≈′_ X@(oc x h) (oe (el n) y) = X ≈′ y
_≈′_ X@(oc x h) (oL j k₂ e y) = ELr′ X j y
_≈′_ X@(oc x h) (ow p g y) = X ≈′ y
o0 ≈′ o0 = ⊤
_≈′_ {ρ} {p} {a} {u} {ρ′} {p′} {a′} {u′} (os x) (os y) = (⟨ ρ , p ⟩ ≈ᴴ ⟨ ρ′ , p′ ⟩) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (x ≈′ y)
ol F ≈′ ol G = ∀ n → F n ≈′ G n
_≈′_ {ρ} {p} {a} {u} {ρ′} {p′} {a′} {u′} (oi {k = k} r h) (oi {k = k′} r′ h′) =
  (⟨ ρ , p ⟩ ≈ᴴ ⟨ ρ′ , p′ ⟩) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (k ≈ᴬ k′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqV′ (≪S r) (≪S r′) y y′ → h q g y ≈′ h′ q′ g′ y′)
_≈′_ {ρ} {p} {a} {u} {ρ′} {p′} {a′} {u′} (od {h = h₀} j k r h) (od {h = h₁} j′ k′ r′ h′) =
  (⟨ ρ , p ⟩ ≈ᴴ ⟨ ρ′ , p′ ⟩) × (h₀ ≈ᴴ h₁) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (k ≈ᴬ k′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqW′ j j′ y y′ → h q g y ≈′ h′ q′ g′ y′)
_≈′_ {ρ} {p} {a} {u} {ρ′} {p′} {a′} {u′} (oc x h) (oc x′ h′) =
  (⟨ ρ , p ⟩ ≈ᴴ ⟨ ρ′ , p′ ⟩) × (a ≈ᴬ a′) × (u ≈ᴬ u′) × (x ≈′ x′) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → h q g ≈′ h′ q′ g′)
_ ≈′ _ = ⊥

ELl′ hs0 (bx x) y = x ≈′ y
ELl′ (hl0 n₀) (bx x) y = x ≈′ y
ELl′ hr0 (bx x) y = x ≈′ y
ELl′ (hsS j) x y = ELl′ j x y
ELl′ (hlS n₀ j) x y = ELl′ j x y
ELl′ (hrS j) x y = ELl′ j x y
ELr′ X hs0 (bx y) = X ≈′ y
ELr′ X (hl0 n₀) (bx y) = X ≈′ y
ELr′ X hr0 (bx y) = X ≈′ y
ELr′ X (hsS j) y = ELr′ X j y
ELr′ X (hlS n₀ j) y = ELr′ X j y
ELr′ X (hrS j) y = ELr′ X j y
EqW′ hs0 j′ (bx x) y = ELr′ x j′ y
EqW′ (hl0 n₀) j′ (bx x) y = ELr′ x j′ y
EqW′ hr0 j′ (bx x) y = ELr′ x j′ y
EqW′ (hsS j) j′ x y = EqW′ j j′ x y
EqW′ (hlS n₀ j) j′ x y = EqW′ j j′ x y
EqW′ (hrS j) j′ x y = EqW′ j j′ x y
EqV′ (ss P) R′ y y′ = EVC′ P R′ y y′
EqV′ (sl n P) R′ y y′ = EVC′ P R′ y y′
EVC′ C.self R′ y y′ = ELO′ y R′ y′
EVC′ (C.suc P) R′ y y′ = EVC′ P R′ y y′
EVC′ (C.lim n P) R′ y y′ = EVC′ P R′ y y′
ELO′ x (ss P) y′ = EOC′ x P y′
ELO′ x (sl n P) y′ = EOC′ x P y′
EOC′ x C.self y′ = x ≈′ y′
EOC′ x (C.suc P) y′ = EOC′ x P y′
EOC′ x (C.lim n P) y′ = EOC′ x P y′


_≈_ : ∀ {p a u p′ a′ u′} → 𝓞 p a u → 𝓞 p′ a′ u′ → Set
x ≈ y = x ≈′ y

ELl : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) → Low p j k u → 𝓞 p′ a′ u′ → Set
ELl j x y = ELl′ j x y

ELr : ∀ {p a u p′ h k u′} → 𝓞 p a u → (j : h <ᴴ p′) → Low p′ j k u′ → Set
ELr x j y = ELr′ x j y

EqW : ∀ {p h k u p′ h′ k′ u′} (j : h <ᴴ p) (j′ : h′ <ᴴ p′) → Low p j k u → Low p′ j′ k′ u′ → Set
EqW j j′ x y = EqW′ j j′ x y

EqV : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) → Vs p a R u → Vs p′ a′ R′ u′ → Set
EqV R R′ x y = EqV′ R R′ x y

EVC : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) → Vc p a P u → Vs p′ a′ R′ u′ → Set
EVC P R′ x y = EVC′ P R′ x y

ELO : ∀ {p b u p′ a′ b′ u′} → 𝓞 p b u → (R′ : Strict b′ a′) → Vs p′ a′ R′ u′ → Set
ELO x R′ y = ELO′ x R′ y

EOC : ∀ {p b u p′ a′ b′ u′} → 𝓞 p b u → (P : b′ ⊲ a′) → Vc p′ a′ P u′ → Set
EOC x P y = EOC′ x P y
```

## §4 换视角

```agda
Ll→ : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} → ELl j x y → outL j x ≈ y
Ll→ hs0 (bx x) e = e
Ll→ (hl0 n₀) (bx x) e = e
Ll→ hr0 (bx x) e = e
Ll→ (hsS j) x e = Ll→ j x e
Ll→ (hlS n₀ j) x e = Ll→ j x e
Ll→ (hrS j) x e = Ll→ j x e

→Ll : ∀ {p h k u p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) {y : 𝓞 p′ a′ u′} → outL j x ≈ y → ELl j x y
→Ll hs0 (bx x) e = e
→Ll (hl0 n₀) (bx x) e = e
→Ll hr0 (bx x) e = e
→Ll (hsS j) x e = →Ll j x e
→Ll (hlS n₀ j) x e = →Ll j x e
→Ll (hrS j) x e = →Ll j x e

Lr→ : ∀ {p a u p′ h k u′} (X : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) → ELr X j y → X ≈ outL j y
Lr→ X hs0 (bx y) e = e
Lr→ X (hl0 n₀) (bx y) e = e
Lr→ X hr0 (bx y) e = e
Lr→ X (hsS j) y e = Lr→ X j y e
Lr→ X (hlS n₀ j) y e = Lr→ X j y e
Lr→ X (hrS j) y e = Lr→ X j y e

→Lr : ∀ {p a u p′ h k u′} (X : 𝓞 p a u) (j : h <ᴴ p′) (y : Low p′ j k u′) → X ≈ outL j y → ELr X j y
→Lr X hs0 (bx y) e = e
→Lr X (hl0 n₀) (bx y) e = e
→Lr X hr0 (bx y) e = e
→Lr X (hsS j) y e = →Lr X j y e
→Lr X (hlS n₀ j) y e = →Lr X j y e
→Lr X (hrS j) y e = →Lr X j y e

W→ : ∀ {p h k u p′ h′ k′ u′} (j : h <ᴴ p) (j′ : h′ <ᴴ p′) (x : Low p j k u) (y : Low p′ j′ k′ u′) → EqW j j′ x y → outL j x ≈ outL j′ y
W→ hs0 j′ (bx x) y e = Lr→ x j′ y e
W→ (hl0 n₀) j′ (bx x) y e = Lr→ x j′ y e
W→ hr0 j′ (bx x) y e = Lr→ x j′ y e
W→ (hsS j) j′ x y e = W→ j j′ x y e
W→ (hlS n₀ j) j′ x y e = W→ j j′ x y e
W→ (hrS j) j′ x y e = W→ j j′ x y e

→W : ∀ {p h k u p′ h′ k′ u′} (j : h <ᴴ p) (j′ : h′ <ᴴ p′) (x : Low p j k u) (y : Low p′ j′ k′ u′) → outL j x ≈ outL j′ y → EqW j j′ x y
→W hs0 j′ (bx x) y e = →Lr x j′ y e
→W (hl0 n₀) j′ (bx x) y e = →Lr x j′ y e
→W hr0 j′ (bx x) y e = →Lr x j′ y e
→W (hsS j) j′ x y e = →W j j′ x y e
→W (hlS n₀ j) j′ x y e = →W j j′ x y e
→W (hrS j) j′ x y e = →W j j′ x y e

V→ : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) (y : Vs p a R u) (y′ : Vs p′ a′ R′ u′) → EqV R R′ y y′ → outS R y ≈ outS R′ y′
VC→ : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) (y : Vc p a P u) (y′ : Vs p′ a′ R′ u′) → EVC P R′ y y′ → outC P y ≈ outS R′ y′
LO→ : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (R′ : Strict b′ a′) (y′ : Vs p′ a′ R′ u′) → ELO x R′ y′ → x ≈ outS R′ y′
OC→ : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (P : b′ ⊲ a′) (y′ : Vc p′ a′ P u′) → EOC x P y′ → x ≈ outC P y′
V→ (ss P) R′ y y′ e = VC→ P R′ y y′ e
V→ (sl n P) R′ y y′ e = VC→ P R′ y y′ e
VC→ C.self R′ y y′ e = LO→ y R′ y′ e
VC→ (C.suc P) R′ y y′ e = VC→ P R′ y y′ e
VC→ (C.lim n P) R′ y y′ e = VC→ P R′ y y′ e
LO→ x (ss P) y′ e = OC→ x P y′ e
LO→ x (sl n P) y′ e = OC→ x P y′ e
OC→ x C.self y′ e = e
OC→ x (C.suc P) y′ e = OC→ x P y′ e
OC→ x (C.lim n P) y′ e = OC→ x P y′ e

→V : ∀ {p a b u p′ a′ b′ u′} (R : Strict b a) (R′ : Strict b′ a′) (y : Vs p a R u) (y′ : Vs p′ a′ R′ u′) → outS R y ≈ outS R′ y′ → EqV R R′ y y′
→VC : ∀ {p a b u p′ a′ b′ u′} (P : b ⊲ a) (R′ : Strict b′ a′) (y : Vc p a P u) (y′ : Vs p′ a′ R′ u′) → outC P y ≈ outS R′ y′ → EVC P R′ y y′
→LO : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (R′ : Strict b′ a′) (y′ : Vs p′ a′ R′ u′) → x ≈ outS R′ y′ → ELO x R′ y′
→OC : ∀ {p b u p′ a′ b′ u′} (x : 𝓞 p b u) (P : b′ ⊲ a′) (y′ : Vc p′ a′ P u′) → x ≈ outC P y′ → EOC x P y′
→V (ss P) R′ y y′ e = →VC P R′ y y′ e
→V (sl n P) R′ y y′ e = →VC P R′ y y′ e
→VC C.self R′ y y′ e = →LO y R′ y′ e
→VC (C.suc P) R′ y y′ e = →VC P R′ y y′ e
→VC (C.lim n P) R′ y y′ e = →VC P R′ y y′ e
→LO x (ss P) y′ e = →OC x P y′ e
→LO x (sl n P) y′ e = →OC x P y′ e
→OC x C.self y′ e = e
→OC x (C.suc P) y′ e = →OC x P y′ e
→OC x (C.lim n P) y′ e = →OC x P y′ e
```

## §5 右边的包装透明

```agda
≈ow : ∀ {p a u p′} (x : 𝓞 p a u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → x ≈ y → x ≈ (ow p₀ g₀′ y)
≈owS : ∀ {p h k u p′} (j : h <ᴴ p) (x : Low p j k u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → ELl j x y → ELl j x (ow p₀ g₀′ y)
≈ow o0 p₀ g₀′ y d = d
≈ow (os x₁) p₀ g₀′ y d = d
≈ow (ol F) p₀ g₀′ y d = d
≈ow (oi r h) p₀ g₀′ y d = d
≈ow (od i k r h) p₀ g₀′ y d = d
≈ow (oc x₁ h) p₀ g₀′ y d = d
≈ow (oe es x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈ow (oe (el m) x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈ow (oL j₁ k₁ e₁ x) p₀ g₀′ y d = ≈owS j₁ x p₀ g₀′ y d
≈ow (ow q₁ g₁ x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS hs0 (bx x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS (hl0 n₀) (bx x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS hr0 (bx x) p₀ g₀′ y d = ≈ow x p₀ g₀′ y d
≈owS (hsS j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d
≈owS (hlS n₀ j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d
≈owS (hrS j) x p₀ g₀′ y d = ≈owS j x p₀ g₀′ y d

≈ow⁻ : ∀ {p a u p′} (x : 𝓞 p a u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → x ≈ (ow p₀ g₀′ y) → x ≈ y
≈ow⁻S : ∀ {p h k u p′} (j : h <ᴴ p) (x : Low p j k u) {a′ u₀ v₀} (p₀ : u₀ ⊲ v₀) (g₀′ : Gw u₀) (y : 𝓞 p′ a′ u₀) → ELl j x (ow p₀ g₀′ y) → ELl j x y
≈ow⁻ o0 p₀ g₀′ y d = d
≈ow⁻ (os x₁) p₀ g₀′ y d = d
≈ow⁻ (ol F) p₀ g₀′ y d = d
≈ow⁻ (oi r h) p₀ g₀′ y d = d
≈ow⁻ (od i k r h) p₀ g₀′ y d = d
≈ow⁻ (oc x₁ h) p₀ g₀′ y d = d
≈ow⁻ (oe es x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻ (oe (el m) x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻ (oL j₁ k₁ e₁ x) p₀ g₀′ y d = ≈ow⁻S j₁ x p₀ g₀′ y d
≈ow⁻ (ow q₁ g₁ x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S hs0 (bx x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S (hl0 n₀) (bx x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S hr0 (bx x) p₀ g₀′ y d = ≈ow⁻ x p₀ g₀′ y d
≈ow⁻S (hsS j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d
≈ow⁻S (hlS n₀ j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d
≈ow⁻S (hrS j) x p₀ g₀′ y d = ≈ow⁻S j x p₀ g₀′ y d


≈oe : ∀ {p a u p′ c b u₀} {R : Strict b c} (x : 𝓞 p a u) (stp : Stp R) (y : Vs p′ c R u₀) → x ≈ outS R y → x ≈ oe stp y
≈oeS : ∀ {p h k u p′ c b u₀} {R : Strict b c} (j : h <ᴴ p) (x : Low p j k u) (stp : Stp R) (y : Vs p′ c R u₀) → ELl j x (outS R y) → ELl j x (oe stp y)
≈oe⁻ : ∀ {p a u p′ c b u₀} {R : Strict b c} (x : 𝓞 p a u) (stp : Stp R) (y : Vs p′ c R u₀) → x ≈ oe stp y → x ≈ outS R y
≈oe⁻S : ∀ {p h k u p′ c b u₀} {R : Strict b c} (j : h <ᴴ p) (x : Low p j k u) (stp : Stp R) (y : Vs p′ c R u₀) → ELl j x (oe stp y) → ELl j x (outS R y)
≈oe o0 es y d = d
≈oe (os x) es y d = d
≈oe (ol F) es y d = d
≈oe (oi r h) es y d = d
≈oe (od i k r h) es y d = d
≈oe (oc x h) es y d = d
≈oe o0 (el n) y d = d
≈oe (os x) (el n) y d = d
≈oe (ol F) (el n) y d = d
≈oe (oi r h) (el n) y d = d
≈oe (od i k r h) (el n) y d = d
≈oe (oc x h) (el n) y d = d
≈oe (oe es x) stp y d = ≈oe x stp y d
≈oe (oe (el m) x) stp y d = ≈oe x stp y d
≈oe (oL j₁ k₁ e₁ x) stp y d = ≈oeS j₁ x stp y d
≈oe (ow q₁ g₁ x) stp y d = ≈oe x stp y d
≈oeS hs0 (bx x) stp y d = ≈oe x stp y d
≈oeS (hl0 n₀) (bx x) stp y d = ≈oe x stp y d
≈oeS hr0 (bx x) stp y d = ≈oe x stp y d
≈oeS (hsS j) x stp y d = ≈oeS j x stp y d
≈oeS (hlS n₀ j) x stp y d = ≈oeS j x stp y d
≈oeS (hrS j) x stp y d = ≈oeS j x stp y d
≈oe⁻ o0 es y d = d
≈oe⁻ (os x) es y d = d
≈oe⁻ (ol F) es y d = d
≈oe⁻ (oi r h) es y d = d
≈oe⁻ (od i k r h) es y d = d
≈oe⁻ (oc x h) es y d = d
≈oe⁻ o0 (el n) y d = d
≈oe⁻ (os x) (el n) y d = d
≈oe⁻ (ol F) (el n) y d = d
≈oe⁻ (oi r h) (el n) y d = d
≈oe⁻ (od i k r h) (el n) y d = d
≈oe⁻ (oc x h) (el n) y d = d
≈oe⁻ (oe es x) stp y d = ≈oe⁻ x stp y d
≈oe⁻ (oe (el m) x) stp y d = ≈oe⁻ x stp y d
≈oe⁻ (oL j₁ k₁ e₁ x) stp y d = ≈oe⁻S j₁ x stp y d
≈oe⁻ (ow q₁ g₁ x) stp y d = ≈oe⁻ x stp y d
≈oe⁻S hs0 (bx x) stp y d = ≈oe⁻ x stp y d
≈oe⁻S (hl0 n₀) (bx x) stp y d = ≈oe⁻ x stp y d
≈oe⁻S hr0 (bx x) stp y d = ≈oe⁻ x stp y d
≈oe⁻S (hsS j) x stp y d = ≈oe⁻S j x stp y d
≈oe⁻S (hlS n₀ j) x stp y d = ≈oe⁻S j x stp y d
≈oe⁻S (hrS j) x stp y d = ≈oe⁻S j x stp y d

≈oL : ∀ {p a u p′ a′ h k u₀} (x : 𝓞 p a u) (j : h <ᴴ p′) (e : D⊲ (fd j) k u₀) (y : Low p′ j k u₀) → x ≈ outL j y → _≈_ {a′ = a′} x (oL j k e y)
≈oLS : ∀ {p h₁ k₁ u p′ a′ h k u₀} (j₁ : h₁ <ᴴ p) (x : Low p j₁ k₁ u) (j : h <ᴴ p′) (e : D⊲ (fd j) k u₀) (y : Low p′ j k u₀) → ELl j₁ x (outL j y) → ELl {a′ = a′} j₁ x (oL j k e y)
≈oL o0 j e y d = →Lr o0 j y d
≈oL X@(os x) j e y d = →Lr X j y d
≈oL X@(ol F) j e y d = →Lr X j y d
≈oL X@(oi r h) j e y d = →Lr X j y d
≈oL X@(od i k r h) j e y d = →Lr X j y d
≈oL X@(oc x h) j e y d = →Lr X j y d
≈oL (oe es x) j e y d = ≈oL x j e y d
≈oL (oe (el m) x) j e y d = ≈oL x j e y d
≈oL (oL j₁ k₁ e₁ x) j e y d = ≈oLS j₁ x j e y d
≈oL (ow q₁ g₁ x) j e y d = ≈oL x j e y d
≈oLS hs0 (bx x) j e y d = ≈oL x j e y d
≈oLS (hl0 n₀) (bx x) j e y d = ≈oL x j e y d
≈oLS hr0 (bx x) j e y d = ≈oL x j e y d
≈oLS (hsS j₁) x j e y d = ≈oLS j₁ x j e y d
≈oLS (hlS n₀ j₁) x j e y d = ≈oLS j₁ x j e y d
≈oLS (hrS j₁) x j e y d = ≈oLS j₁ x j e y d

≈oL⁻ : ∀ {p a u p′ a′ h k u₀} (x : 𝓞 p a u) (j : h <ᴴ p′) (e : D⊲ (fd j) k u₀) (y : Low p′ j k u₀) → _≈_ {a′ = a′} x (oL j k e y) → x ≈ outL j y
≈oL⁻S : ∀ {p h₁ k₁ u p′ a′ h k u₀} (j₁ : h₁ <ᴴ p) (x : Low p j₁ k₁ u) (j : h <ᴴ p′) (e : D⊲ (fd j) k u₀) (y : Low p′ j k u₀) → ELl {a′ = a′} j₁ x (oL j k e y) → ELl j₁ x (outL j y)
≈oL⁻ o0 j e y d = Lr→ o0 j y d
≈oL⁻ X@(os x) j e y d = Lr→ X j y d
≈oL⁻ X@(ol F) j e y d = Lr→ X j y d
≈oL⁻ X@(oi r h) j e y d = Lr→ X j y d
≈oL⁻ X@(od i k r h) j e y d = Lr→ X j y d
≈oL⁻ X@(oc x h) j e y d = Lr→ X j y d
≈oL⁻ (oe es x) j e y d = ≈oL⁻ x j e y d
≈oL⁻ (oe (el m) x) j e y d = ≈oL⁻ x j e y d
≈oL⁻ (oL j₁ k₁ e₁ x) j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻ (ow q₁ g₁ x) j e y d = ≈oL⁻ x j e y d
≈oL⁻S hs0 (bx x) j e y d = ≈oL⁻ x j e y d
≈oL⁻S (hl0 n₀) (bx x) j e y d = ≈oL⁻ x j e y d
≈oL⁻S hr0 (bx x) j e y d = ≈oL⁻ x j e y d
≈oL⁻S (hsS j₁) x j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻S (hlS n₀ j₁) x j e y d = ≈oL⁻S j₁ x j e y d
≈oL⁻S (hrS j₁) x j e y d = ≈oL⁻S j₁ x j e y d

-- 用 O k 的值陈述分支
nI : ∀ {p a u p′ a′ u′ k k′} {r : k ≪ a} {r′ : k′ ≪ a′} {f : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} {f′ : ∀ {v} → u′ ⊲ v → Gw v → Vs p′ a′ (≪S r′) v → 𝓞 p′ a′ v} →
     (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqV (≪S r) (≪S r′) y y′ → f q g y ≈ f′ q′ g′ y′) →
     ∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → (z : 𝓞 p k v) (z′ : 𝓞 p′ k′ v′) → z ≈ z′ → f q g (inS (≪S r) z) ≈ f′ q′ g′ (inS (≪S r′) z′)
nI {r = r} {r′} N q q′ g g′ vv z z′ d = N q q′ g g′ vv _ _ (→V (≪S r) (≪S r′) _ _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r′) z′)) d))

nD : ∀ {p a u p′ a′ u′ h₀ h₁ k k′} {j : h₀ <ᴴ p} {j′ : h₁ <ᴴ p′} {f : ∀ {v} → u ⊲ v → Gw v → Low p j k v → 𝓞 p a v} {f′ : ∀ {v} → u′ ⊲ v → Gw v → Low p′ j′ k′ v → 𝓞 p′ a′ v} →
     (∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → ∀ y y′ → EqW j j′ y y′ → f q g y ≈ f′ q′ g′ y′) →
     ∀ {v v′} (q : u ⊲ v) (q′ : u′ ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ≈ᴬ v′ → (z : 𝓞 h₀ k v) (z′ : 𝓞 h₁ k′ v′) → z ≈ z′ → f q g (inL j z) ≈ f′ q′ g′ (inL j′ z′)
nD {j = j} {j′} N q q′ g g′ vv z z′ d = N q q′ g g′ vv _ _ (→W j j′ _ _ (subst₂ _≈_ (sym (out-inL j z)) (sym (out-inL j′ z′)) d))
```

## §6 $\Omega$, 加法, $y\cdot n$

`Ω≈′`: 对 $(r,p,a)$ 字典序递归. $v$ 跑世界, 所以高度也模等价.

```agda
Ω≈′ : ∀ r {p p′ a b} → p ≈ᴬ p′ → a ≈ᴬ b → Ω̇′ r p a ≈ Ω̇′ r p′ b
Ω≈′ r ep (s≈ {a} {b} e) = (refl , ep) , s≈ e , s≈ z≈ , e , (λ q q′ g g′ vv y y′ d → ≈oe {R = ss C.self} y es y′ (V→ (ss C.self) (ss C.self) y y′ d))
Ω≈′ r {p} {p′} ep (l≈ {f} {g} h) = λ n → ≈oe {⟨ r , p ⟩} {f n} {one} {⟨ r , p′ ⟩} {alim g} {g n} {one} {sl n C.self} (Ω̇′ r p (f n)) (el n) (Ω̇′ r p′ (g n)) (Ω≈′ r ep (h n))
Ω≈′ r (s≈ {a = b} {b = b′} ep) z≈ = (refl , s≈ ep) , z≈ , s≈ z≈ ,
  ≈oL {a′ = azero} {k = one} {u₀ = one} (Ω̇′ r b one) hs0 (z⊲ one ,ᵈ C.self) (bx (Ω̇′ r b′ one)) (Ω≈′ r ep (≈ᴬ-refl one)) ,
  (λ {v} {v′} q q′ g g′ vv → ≈oL {a′ = azero} {k = v′} {u₀ = v′} (ow (pos g) g₀ (Ω̇′ r b v)) hs0 (z⊲ v′ ,ᵈ C.self) (bx (ow (pos g′) g₀ (Ω̇′ r b′ v′)))
     (≈ow (Ω̇′ r b v) (pos g′) g₀ (Ω̇′ r b′ v′) (Ω≈′ r ep vv)))
Ω≈′ r (l≈ {f} {g} h) z≈ = λ n → ≈oL {a′ = azero} {k = azero} {u₀ = one} (Ω̇′ r (f n) azero) (hl0 {r = r} {f = g} n) (z⊲ one ,ᵈ z⊲ one) (bx (Ω̇′ r (g n) azero)) (Ω≈′ r (h n) z≈)
Ω≈′ zero z≈ z≈ = (refl , z≈) , z≈ , s≈ z≈ , tt
Ω≈′ (suc s) z≈ z≈ = (refl , z≈) , z≈ , s≈ z≈ ,
  ≈oL {a′ = azero} {k = azero} {u₀ = one} (Ω̇′ s one azero) (hr0 {p′ = one} {p = azero}) (C.self ,ᵈ z⊲ one) (bx (Ω̇′ s one azero)) (Ω≈′ s (≈ᴬ-refl one) z≈) ,
  (λ {v} {v′} q q′ g g′ vv → ≈oL {a′ = azero} {k = azero} {u₀ = v′} (ow (pos g) g₀ (Ω̇′ s v azero)) (hr0 {p′ = v′} {p = azero}) (C.self ,ᵈ z⊲ v′) (bx (ow (pos g′) g₀ (Ω̇′ s v′ azero)))
     (≈ow (Ω̇′ s v azero) (pos g′) g₀ (Ω̇′ s v′ azero) (Ω≈′ s vv z≈)))

Ω≈ : ∀ {H H′ a b} → H ≈ᴴ H′ → a ≈ᴬ b → Ω̇ H a ≈ Ω̇ H′ b
Ω≈ {⟨ r , p ⟩} {⟨ .r , p′ ⟩} (refl , ep) e = Ω≈′ r ep e

≈-Ωat : ∀ {H H′ a b v v′} (g : Gw v) (g′ : Gw v′) → H ≈ᴴ H′ → a ≈ᴬ b → Ω̇at H a g ≈ Ω̇at H′ b g′
≈-Ωat {H} {H′} {a} {b} g g′ eh e = ≈ow (Ω̇ H a) (pos g′) g₀ (Ω̇ H′ b) (Ω≈ eh e)

-- 路径里自由的那一位: 同 r 位时是 0, 否则是低高度的 p 位
fdv : ∀ {h p} (i : h <ᴴ p) → ((rr h ≡ rr p) × (fd i ≡ azero)) ⊎ ((rr h <ᴺ rr p) × (fd i ≡ pp h))
fdv hs0 = inj₁ (refl , refl)
fdv (hl0 n) = inj₁ (refl , refl)
fdv hr0 = inj₂ (zero , refl)
fdv (hsS i) = fdv i
fdv (hlS n i) = fdv i
fdv (hrS i) with fdv i | <v i
... | inj₁ (_ , _) | inj₂ (_ , ())
... | inj₁ (refl , _) | inj₁ x = ⊥-elim (<ᴺ-irr x)
... | inj₂ (x , e) | _ = inj₂ (<ᴺ-tr x zero , e)

≡≈ : ∀ {a b x y} → a ≡ x → b ≡ y → x ≈ᴬ y → a ≈ᴬ b
≡≈ refl refl e = e

fd≈ : ∀ {h h′ p p′} (i : h <ᴴ p) (i′ : h′ <ᴴ p′) → h ≈ᴴ h′ → p ≈ᴴ p′ → fd i ≈ᴬ fd i′
fd≈ {⟨ r , q ⟩} {⟨ .r , q′ ⟩} {⟨ s , y ⟩} {⟨ .s , y′ ⟩} i i′ (refl , eh) (refl , ep) with fdv i | fdv i′
... | inj₁ (_ , e) | inj₁ (_ , e′) = ≡≈ e e′ z≈
... | inj₂ (_ , e) | inj₂ (_ , e′) = ≡≈ e e′ eh
... | inj₁ (refl , _) | inj₂ (x , _) = ⊥-elim (<ᴺ-irr x)
... | inj₂ (x , _) | inj₁ (refl , _) = ⊥-elim (<ᴺ-irr x)

bw≈ : ∀ {p p′ p₁ b a p₂ b′ a′} → p ≈ᴴ p′ → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) → p₁ ≈ᴴ p₂ → b ≈ᴬ b′ → D≈ (fw R) (bw R) (fw R′) (bw R′)
bw≈ ep (sa P) (sa P′) eh e = D≈-z
bw≈ ep (lw i) (lw i′) eh e = fd≈ i i′ eh ep ,≈ e
bw≈ ep (sa P) (lw i′) eh e = ⊥-elim (no-<≈ i′ (≈ᴴ-trans (≈ᴴ-sym eh) ep))
bw≈ ep (lw i) (sa P′) eh e = ⊥-elim (no-<≈ i (≈ᴴ-trans eh (≈ᴴ-sym ep)))

```

```agda
-- 左边 W 对齐, 输出世界规范
module AddE {p p′ a a′ u₀ u₀′} {W : 𝓞 p a u₀} {W′ : 𝓞 p′ a′ u₀′} (ep : p ≈ᴴ p′) (ea : a ≈ᴬ a′) (eu : u₀ ≈ᴬ u₀′) (E : W ≈ W′) (gu : Gw u₀) (gu′ : Gw u₀′) where
  add⁰≈ : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : D⊲ (fw R) (bw R) m) → Mis m u₀ azero w (fw R) (bw R) →
          ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : D⊲ (fw R′) (bw R′) m′) → Mis m′ u₀′ azero w′ (fw R′) (bw R′) →
          x ≈ y → add⁰ W gu R x gx m gm um tm am ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′

  add≈ : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : D⊲ (fw R) (bw R) v)
         v′ (gv′ : Gw v′) (uv′ : u₀′ ⊲ v′) (xv′ : w′ ⊲ v′) (bv′ : D⊲ (fw R′) (bw R′) v′) →
         x ≈ y → add W gu R x gx v gv uv xv bv ≈ add W′ gu′ R′ y gy v′ gv′ uv′ xv′ bv′
  add≈ R R′ x y gx gy v gv uv xv bv v′ gv′ uv′ xv′ bv′ d
    with mx gu gv uv (Dzr xv) bv | mx gu′ gv′ uv′ (Dzr xv′) bv′
  ... | mx′ m gm um tm am mv is | mx′ m′ gm′ um′ tm′ am′ mv′ is′ =
    ≈ow (add⁰ W gu R x gx m gm um (d₂ tm) am) mv′ gm′ (add⁰ W′ gu′ R′ y gy m′ gm′ um′ (d₂ tm′) am′) (add⁰≈ R R′ x y gx gy m gm um (d₂ tm) am is m′ gm′ um′ (d₂ tm′) am′ is′ d)

  addl : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : D⊲ (fw R) (bw R) m)
         m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : D⊲ (fw R′) (bw R′) m′) → Mis m′ u₀′ azero w′ (fw R′) (bw R′) →
         x ≈ y → add W gu R x gx m gm um tm am ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addl R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d with mx gu gm um (Dzr tm) am
  ... | mx′ m₁ g₁ u₁ t₁ a₁ _ is₁ = add⁰≈ R R′ x y gx gy m₁ g₁ u₁ (d₂ t₁) a₁ is₁ m′ gm′ um′ tm′ am′ is′ d

  addr : ∀ {p₁ b w p₂ b′ w′} (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p′ a′) (x : 𝓞 p₁ b w) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
         m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : D⊲ (fw R) (bw R) m) → Mis m u₀ azero w (fw R) (bw R) →
         ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : D⊲ (fw R′) (bw R′) m′) →
         x ≈ y → add⁰ W gu R x gx m gm um tm am ≈ add W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addr R R′ x y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d with mx gu′ gm′ um′ (Dzr tm′) am′
  ... | mx′ m₁ g₁ u₁ t₁ a₁ mv is₁ = ≈ow (add⁰ W gu R x gx m gm um tm am) mv g₁ (add⁰ W′ gu′ R′ y gy m₁ g₁ u₁ (d₂ t₁) a₁) (add⁰≈ R R′ x y gx gy m gm um tm am is m₁ g₁ u₁ (d₂ t₁) a₁ is₁ d)

  addLl : ∀ {p₁ h k w p₂ b′ w′} (t : h <ᴴ p) (j : h <ᴴ p₁) (x : Low p₁ j k w) (R′ : Rel p₂ b′ p′ a′) (y : 𝓞 p₂ b′ w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : D⊲ (fd t) k m)
          m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : D⊲ (fw R′) (bw R′) m′) → Mis m′ u₀′ azero w′ (fw R′) (bw R′) →
          ELl j x y → addL W gu t j x gx m gm um tm km ≈ add⁰ W′ gu′ R′ y gy m′ gm′ um′ tm′ am′
  addLl t hs0 (bx x) R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (hl0 n₀) (bx x) R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t hr0 (bx x) R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addl (lw t) R′ x y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (hsS j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (hlS n₀ j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d
  addLl t (hrS j) x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d = addLl t j x R′ y gx gy m gm um tm km m′ gm′ um′ tm′ am′ is′ d

  addLr : ∀ {p₁ b w p₂ h k w′} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (t : h <ᴴ p′) (j : h <ᴴ p₂) (y : Low p₂ j k w′) (gx : Gw w) (gy : Gw w′)
          m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : D⊲ (fw R) (bw R) m) → Mis m u₀ azero w (fw R) (bw R) →
          ∀ m′ (gm′ : Gw m′) (um′ : u₀′ ⊲ m′) (tm′ : w′ ⊲ m′) (km′ : D⊲ (fd t) k m′) →
          ELr x j y → add⁰ W gu R x gx m gm um tm am ≈ addL W′ gu′ t j y gy m′ gm′ um′ tm′ km′
  addLr R x t hs0 (bx y) gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (hl0 n₀) (bx y) gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t hr0 (bx y) gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addr R (lw t) x y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (hsS j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (hlS n₀ j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d
  addLr R x t (hrS j) y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d = addLr R x t j y gx gy m gm um tm am is m′ gm′ um′ tm′ km′ d

  add⁰≈ (sa P) R′ (oe es x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (sa (⊲-tr (C.suc C.self) P)) R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oe es x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (lw i) R′ x y gx gy m gm um tm (Dr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (sa P) R′ (oe (el n) x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (sa (⊲-tr (C.lim n C.self) P)) R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oe (el n) x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl (lw i) R′ x y gx gy m gm um tm (Dr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (sa P) R′ (oL j k e x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLl j j x R′ y gx gy m gm um tm (D-tr e tm) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ (lw i) R′ (oL j k e x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLl (<tr j i) j x R′ y gx gy m gm um tm (Dfd j i (D-tr e tm) (d₁ am)) m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ R R′ (ow p′ g′ x) y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addl R R′ x y g′ gy m gm um (⊲-tr p′ tm) am m′ gm′ um′ tm′ am′ is′ d
  add⁰≈ R (sa P) X@o0 (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@o0 (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@o0 (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@o0 (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@o0 (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (D-tr e tm′) d
  add⁰≈ R (lw i) X@o0 (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dfd j i (D-tr e tm′) (d₁ am′)) d
  add⁰≈ R R′ X@o0 (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(os x) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(os x) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(os x) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(os x) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(os x) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (D-tr e tm′) d
  add⁰≈ R (lw i) X@(os x) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dfd j i (D-tr e tm′) (d₁ am′)) d
  add⁰≈ R R′ X@(os x) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(ol F) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(ol F) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(ol F) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(ol F) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(ol F) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (D-tr e tm′) d
  add⁰≈ R (lw i) X@(ol F) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dfd j i (D-tr e tm′) (d₁ am′)) d
  add⁰≈ R R′ X@(ol F) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(oi r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oi r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(oi r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oi r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(oi r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (D-tr e tm′) d
  add⁰≈ R (lw i) X@(oi r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dfd j i (D-tr e tm′) (d₁ am′)) d
  add⁰≈ R R′ X@(oi r f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(od j₃ k₃ r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (D-tr e tm′) d
  add⁰≈ R (lw i) X@(od j₃ k₃ r f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dfd j i (D-tr e tm′) (d₁ am′)) d
  add⁰≈ R R′ X@(od j₃ k₃ r f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R (sa P) X@(oc x f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.suc C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oc x f) (oe es y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′) d
  add⁰≈ R (sa P) X@(oc x f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (sa (⊲-tr (C.lim n C.self) P)) X y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ d
  add⁰≈ R (lw i) X@(oc x f) (oe (el n) y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R (lw i) X y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′) d
  add⁰≈ R (sa P) X@(oc x f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X j j y gx gy m gm um tm am is m′ gm′ um′ tm′ (D-tr e tm′) d
  add⁰≈ R (lw i) X@(oc x f) (oL j k₂ e y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addLr R X (<tr j i) j y gx gy m gm um tm am is m′ gm′ um′ tm′ (Dfd j i (D-tr e tm′) (d₁ am′)) d
  add⁰≈ R R′ X@(oc x f) (ow p′ g′ y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = addr R R′ X y gx g′ m gm um tm am is m′ gm′ um′ (⊲-tr p′ tm′) am′ d
  add⁰≈ R R′ o0 o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = ≈ow W um′ gu′ W′ E
  add⁰≈ R R′ (os x) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , d) =
    ep , ea , m≈ is is′ um (Dzr tm) am um′ (Dzr tm′) am′ eu (z≈ ,≈ ex) (bw≈ ep R R′ eh ez) , add≈ R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ d
  add⁰≈ R R′ (ol F) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ d = λ n → add≈ R R′ (F n) (G n) gx gy m gm um tm am m′ gm′ um′ tm′ am′ (d n)
  add⁰≈ (sa P) (sa P′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , ek , N) =
    ep , ea , m≈ is is′ um (Dzr tm) am um′ (Dzr tm′) am′ eu (z≈ ,≈ ex) D≈-z , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (sa P) (sa P′) _ _ g g′ v g (⊲-tr um q) C.self (Dz v) v′ g′ (⊲-tr um′ q′) C.self (Dz v′)
        (nI {r = r} {r′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (V→ (≪S (≪∘ r P)) (≪S (≪∘ r′ P′)) y y′ d′)))
  add⁰≈ (lw i) (lw i′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , ek , N) =
    ep , eh , ea , m≈ is is′ um (Dzr tm) am um′ (Dzr tm′) am′ eu (z≈ ,≈ ex) (bw≈ ep (lw i) (lw i′) eh ez) , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (lw i) (lw i′) _ _ g g′ v g (⊲-tr um q) C.self (D-tr am q) v′ g′ (⊲-tr um′ q′) C.self (D-tr am′ q′)
        (nI {r = r} {r′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ i i′ y y′ d′)))
  add⁰≈ (sa P) (lw i′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , _) = ⊥-elim (no-<≈ i′ (≈ᴴ-trans (≈ᴴ-sym eh₀) ep))
  add⁰≈ (lw i) (sa P′) (oi r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , _) = ⊥-elim (no-<≈ i (≈ᴴ-trans eh₀ (≈ᴴ-sym ep)))
  add⁰≈ (sa P) (sa P′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , eh , ez , ex , ek , N) =
    ep , eh , ea , m≈ is is′ um (Dzr tm) am um′ (Dzr tm′) am′ eu (z≈ ,≈ ex) D≈-z , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (sa P) (sa P′) _ _ g g′ v g (⊲-tr um q) C.self (Dz v) v′ g′ (⊲-tr um′ q′) C.self (Dz v′)
        (nD {j = j} {j′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ j j′ y y′ d′)))
  add⁰≈ (lw i) (lw i′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , eh , ez , ex , ek , N) =
    ep , eh , ea , m≈ is is′ um (Dzr tm) am um′ (Dzr tm′) am′ eu (z≈ ,≈ ex) (bw≈ ep (lw i) (lw i′) eh₀ ez) , ek , (λ {v} {v′} q q′ g g′ vv y y′ d′ →
      add≈ (lw i) (lw i′) _ _ g g′ v g (⊲-tr um q) C.self (D-tr am q) v′ g′ (⊲-tr um′ q′) C.self (D-tr am′ q′)
        (nD {j = j} {j′} {f} {f′} N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv _ _ (W→ (<tr j i) (<tr j′ i′) y y′ d′)))
  add⁰≈ (sa P) (lw i′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , _) = ⊥-elim (no-<≈ i′ (≈ᴴ-trans (≈ᴴ-sym eh₀) ep))
  add⁰≈ (lw i) (sa P′) (od j k r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh₀ , _) = ⊥-elim (no-<≈ i (≈ᴴ-trans eh₀ (≈ᴴ-sym ep)))
  add⁰≈ R R′ (oc x f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ (eh , ez , ex , d , N) =
    ep , ea , m≈ is is′ um (Dzr tm) am um′ (Dzr tm′) am′ eu (z≈ ,≈ ex) (bw≈ ep R R′ eh ez) , add≈ R R′ x y gx gy m gm um tm am m′ gm′ um′ tm′ am′ d ,
    (λ {v} {v′} q q′ g g′ vv →
      add≈ R R′ (f (⊲-tr tm q) g) (f′ (⊲-tr tm′ q′) g′) g g′ v g (⊲-tr um q) C.self (D-tr am q) v′ g′ (⊲-tr um′ q′) C.self (D-tr am′ q′) (N (⊲-tr tm q) (⊲-tr tm′ q′) g g′ vv))
  add⁰≈ R R′ o0 (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ o0 (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (os x) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (ol F) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oi r f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (od j k r f) (oc y f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) o0 gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (os y) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (ol G) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (oi r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()
  add⁰≈ R R′ (oc x f) (od j′ k′ r′ f′) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ ()

rep≈ : ∀ {q q′ t t′ u u′} {y : 𝓞 q t u} {y′ : 𝓞 q′ t′ u′} → q ≈ᴴ q′ → t ≈ᴬ t′ → u ≈ᴬ u′ → y ≈ y′ → (g : Gw u) (g′ : Gw u′) → ∀ n → rep y g n ≈ rep y′ g′ n
rep≈ eq et eu e g g′ zero = tt
rep≈ eq et eu e g g′ (suc zero) = e
rep≈ {u = u} {u′} {y = y} {y′} eq et eu e g g′ (suc (suc m)) =
  AddE.add≈ eq et eu (rep≈ eq et eu e g g′ (suc m)) g g′ (sa C.self) (sa C.self) y y′ g g′ u g C.self C.self (Dz u) u′ g′ C.self C.self (Dz u′) e
```

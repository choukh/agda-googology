# 不累加的世界: 闭包定理

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). **`ψW`: 折叠保 `WF`, 对一切高度, 一切层, 一切目标, 一步. 这条定理不碰链.** `HS-T` 的 $(p,a)$ 部分全在这里.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Level using (HS; hz; hs; hl; _⊑⁰_; _≅_; ≺s; ≺l; ≅→⊑; ≅-refl⁰; z≅; s≅; l≅; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_≈ᴬ_; z≈; s≈; l≈; ≈ᴬ-refl; ≈ᴬ-sym; ≈ᴬ-trans)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumPsi
open import OCF.Align.NoCumLe
```

## §2 折叠保第一位置

`M₀`: 第 0 层. `Mᵗ`: 非第 0 层的目标. 都对推导递归.

```agda
-- 非第 0 层的目标
tmm : ∀ {p a u p′ a′ u′ q t} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t a′ →
      ψ⁰ q t x gu m gm um tm am ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′

tRm : ∀ {p a u p′ a′ u′ q t} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : t ⊲ v) (av : a′ ⊲ v) →
      ψ⁰ q t x gu m gm um tm am ⊴ ψᵐ q t y gu′ v gv uv tv av
tRm d gu gu′ m gm um tm am is v gv uv tv av with mx gu′ gv uv tv av | mx-is gu′ gv uv tv av
... | mx′ m′ gm′ um′ tm′ am′ mv | is′ = rw (tmm d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′)

tLm : ∀ {p a u p′ a′ u′ q t} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t a′ →
      ψᵐ q t x gu v gv uv tv av ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tLm d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ with mx gu gv uv tv av | mx-is gu gv uv tv av
... | mx′ m gm um tm am mv | is = lw₂ (tmm d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′)

tR : ∀ {p a u p′ a′ u′ q t} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
     ∀ m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
     ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : t ⊲ v) (av : a′ ⊲ v) →
     ψ⁰ q t x gu m gm um tm am ⊴ ψ q t y gu′ v gv uv tv av
tR d gu gu′ m gm um tm am is v gv uv tv av = tRm d gu gu′ m gm um tm am is v gv uv tv av

tL : ∀ {p a u p′ a′ u′ q t} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
     ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) →
     ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t a′ →
     ψ q t x gu v gv uv tv av ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tL d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′

tRL : ∀ {p a u p′ h k u′ q t} {x : 𝓞 p a u} (j : h <ᴺ p′) (y : Low p′ j k u′) → x ⊴ outL j y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : t ⊲ v) (kv : k ⊲ v) →
      ψ⁰ q t x gu m gm um tm am ⊴ ψL q t j y gu′ v gv uv tv kv
tRL zero y d gu gu′ m gm um tm am is v gv uv tv kv = tR d gu gu′ m gm um tm am is v gv uv tv kv
tRL (suc j) y d gu gu′ m gm um tm am is v gv uv tv kv = tRL j y d gu gu′ m gm um tm am is v gv uv tv kv

tLL : ∀ {p h k u p′ a′ u′ q t} {y : 𝓞 p′ a′ u′} (j : h <ᴺ p) (x : Low p j k u) → outL j x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (kv : k ⊲ v) →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t a′ →
      ψL q t j x gu v gv uv tv kv ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tLL zero x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tL d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL (suc j) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tLL j x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′

tmm {x} {y} (rf e) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = rf (ψ⁰Q x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ (≈ᴬ-refl _) e)
tmm (s d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l 1 (tR d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm (l n d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l n (tR d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm (fc d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = fc (tR d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm {p′ = p′} {q = q} {t} {x} (ni {k = k} {r = r} {h = h} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ with <ᴺ-dec p′ q
... | injᵃ i = nd (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inS (≪S r) z)) g v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)) (sym (out-inL i (Ω̇at _ k g)))
        (tR (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)))
... | injᵇ _ = l 0 (tR (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
... | injᶜ refl with cmpN (≪∘ r am′) tm′ (lgw gm′)
...   | keep s′ = ni (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inS (≪S r) z)) g v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)) (sym (out-inS (≪S s′) (Ω̇at _ k g)))
        (tR (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)))
...   | rise _ = l 0 (tR (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
tmm {q = q} {t} {x} (nd {h₀ = h₀} {k = k} {i = j} {r = r} {h = h} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ with <ᴺ-dec h₀ q
... | injᵃ i = nd (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inL j z)) g v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)) (sym (out-inL i (Ω̇at _ k g)))
        (tR (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)))
... | injᵇ _ = l 0 (tR (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
... | injᶜ refl with cmpN (≪∘ r um′) tm′ (lgw gm′)
...   | keep s′ = ni (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inL j z)) g v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)) (sym (out-inS (≪S s′) (Ω̇at _ k g)))
        (tR (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (⊲-tr tm′ w) (⊲-tr am′ w)))
...   | rise _ = l 0 (tR (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
tmm (eR {stp = es} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′)
tmm (eR {stp = el n} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′)
tmm (eL {stp = es} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL d gu gu′ m gm um tm (⊲-tr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′
tmm (eL {stp = el n} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL d gu gu′ m gm um tm (⊲-tr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′
tmm (rL {j = j} {e = e} {y = y} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tRL j y d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e um′)
tmm (lL {j = j} {e = e} {x = x} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tLL j x d gu gu′ m gm um tm (⊲-tr e um) m′ gm′ um′ tm′ am′ is′
tmm (rw {w = w} {g = g} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR d gu g m gm um tm am is m′ gm′ (⊲-tr w um′) tm′ am′
tmm (lw₂ {w = w} {g = g} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL d g gu′ m gm (⊲-tr w um) tm am m′ gm′ um′ tm′ am′ is′

-- 总的
ψL′ : ∀ {p a u p′ a′ u′} q t {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) →
      ∀ v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : t ⊲ v′) (av′ : a′ ⊲ v′) →
      ψ q t x gu v gv uv tv av ⊴ ψ q t y gu′ v′ gv′ uv′ tv′ av′
ψL′ q t d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ with mx gu gv uv tv av | mx-is gu gv uv tv av
... | mx′ m gm um tm am mv | is = lw₂ (tR d gu gu′ m gm um tm am is v′ gv′ uv′ tv′ av′)

-- Ω_k 是 ψ_k 的任何值的第一位置
Ωfst : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Ω̇at q t gm ⊴ ψ q t x gu m gm um tm am
Ωfst q t x gu m gm um tm am =
  tR {x = o0 {zero} {azero} {Vs zero azero} {Low zero}} (z⊴ x) gm gu m gm C.self tm (z⊲ m) (iu refl) m gm um tm am
```

## §3 `WF`

```agda
WF : ∀ {p a u} → 𝓞 p a u → Set
WFS : ∀ {p a b} (R : Strict b a) {u} → Vs p a R u → Set
WFC : ∀ {p a b} (P : b ⊲ a) {u} → Vc p a P u → Set
WFL : ∀ {p h k u} (j : h <ᴺ p) → Low p j k u → Set

WF o0 = ⊤
WF (os x) = WF x
WF (ol F) = (∀ n → F n ⊴ F (suc n)) × (∀ n → WF (F n))
WF {u = u} (oi r h) =
  (∀ {v} (q : u ⊲ v) (g : Gw v) y y′ → outS (≪S r) y ⊴ outS (≪S r) y′ → h q g y ⊴ h q g y′) ×
  (∀ {v} (q : u ⊲ v) (g : Gw v) y → outS (≪S r) y ≈ outS (≪S r) y → WFS (≪S r) y → WF (h q g y))
WF {u = u} (od i k r h) =
  (∀ {v} (q : u ⊲ v) (g : Gw v) y y′ → outL i y ⊴ outL i y′ → h q g y ⊴ h q g y′) ×
  (∀ {v} (q : u ⊲ v) (g : Gw v) y → outL i y ≈ outL i y → WFL i y → WF (h q g y))
WF {u = u} (oc x h) =
  (∀ {v} (q : u ⊲ v) (g : Gw v) → x ⊴ h q g) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ⊲ v′ → h q g ⊴ h q′ g′) ×
  WF x × (∀ {v} (q : u ⊲ v) (g : Gw v) → WF (h q g))
WF (oe es x) = WF x
WF (oe (el n) x) = WF x
WF (oL j k e x) = WFL j x
WF (ow w g x) = WF x

WFS (ss P) x = WFC P x
WFS (sl n P) x = WFC P x
WFC C.self x = WF x
WFC (C.suc P) x = WFC P x
WFC (C.lim n P) x = WFC P x
WFL zero x = WF x
WFL (suc j) x = WFL j x

S→W : ∀ {p a b u} (R : Strict b a) (x : Vs p a R u) → WFS R x → WF (outS R x)
C→W : ∀ {p a b u} (P : b ⊲ a) (x : Vc p a P u) → WFC P x → WF (outC P x)
S→W (ss P) x w = C→W P x w
S→W (sl n P) x w = C→W P x w
C→W C.self x w = w
C→W (C.suc P) x w = C→W P x w
C→W (C.lim n P) x w = C→W P x w

W→S : ∀ {p a b u} (R : Strict b a) (x : Vs p a R u) → WF (outS R x) → WFS R x
W→C : ∀ {p a b u} (P : b ⊲ a) (x : Vc p a P u) → WF (outC P x) → WFC P x
W→S (ss P) x w = W→C P x w
W→S (sl n P) x w = W→C P x w
W→C C.self x w = w
W→C (C.suc P) x w = W→C P x w
W→C (C.lim n P) x w = W→C P x w

L→W : ∀ {p h k u} (j : h <ᴺ p) (x : Low p j k u) → WFL j x → WF (outL j x)
L→W zero x w = w
L→W (suc j) x w = L→W j x w

W→L : ∀ {p h k u} (j : h <ᴺ p) (x : Low p j k u) → WF (outL j x) → WFL j x
W→L zero x w = w
W→L (suc j) x w = W→L j x w

-- 分支写成 O k 的值
hMi : ∀ {p a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} → WF (oi r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) {z z′ : 𝓞 p k v} → z ⊴ z′ → h q g (inS (≪S r) z) ⊴ h q g (inS (≪S r) z′)
hMi {r = r} (mon , _) q g {z} {z′} d = mon q g _ _ (subst₂ _⊴_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z′)) d)

hWi : ∀ {p a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} → WF (oi r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) (z : 𝓞 p k v) → z ≈ z → WF z → WF (h q g (inS (≪S r) z))
hWi {r = r} (_ , ww) q g z e w = ww q g _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z)) e) (W→S (≪S r) _ (subst WF (sym (out-inS (≪S r) z)) w))

hMd : ∀ {p a u h₀ k} {i : h₀ <ᴺ p} {r : k ≪ u} {h : ∀ {v} → u ⊲ v → Gw v → Low p i k v → 𝓞 p a v} → WF (od i k r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) {z z′ : 𝓞 h₀ k v} → z ⊴ z′ → h q g (inL i z) ⊴ h q g (inL i z′)
hMd {i = i} (mon , _) q g {z} {z′} d = mon q g _ _ (subst₂ _⊴_ (sym (out-inL i z)) (sym (out-inL i z′)) d)

hWd : ∀ {p a u h₀ k} {i : h₀ <ᴺ p} {r : k ≪ u} {h : ∀ {v} → u ⊲ v → Gw v → Low p i k v → 𝓞 p a v} → WF (od i k r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) (z : 𝓞 h₀ k v) → z ≈ z → WF z → WF (h q g (inL i z))
hWd {i = i} (_ , ww) q g z e w = ww q g _ (subst₂ _≈_ (sym (out-inL i z)) (sym (out-inL i z)) e) (W→L i _ (subst WF (sym (out-inL i z)) w))

ΩW : ∀ p a → Lg a → WF (Ω̇ p a)
ΩW p (asuc c) w = (λ q g y y′ d → eL {stp = es} (eR {stp = es} d)) , (λ q g y _ u → u)
ΩW p (alim f) (st , w) = (λ n → eL {stp = el n} (eR {stp = el (suc n)} (Ω⊴ p (st n)))) , (λ n → ΩW p (f n) (w n))
ΩW zero azero w = tt
ΩW (suc p) azero w =
  (λ q g → lL (rL (rw (Ω⊴ p (pos g))))) , (λ q q′ g g′ vv → lL (rL (lw₂ (rw (Ω⊴ p vv))))) , ΩW p one tt , (λ {v} q g → ΩW p v (lgw g))

-- 加法保 WF
module AddW {p a u₀} (W : 𝓞 p a u₀) (gu : Gw u₀) (E : W ≈ W) (wW : WF W) where
  open AddM W gu E using (mm2)

  aw : ∀ {p₁ b w} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → WF x → ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw R ⊲ v) → WF (add W gu R x gx v gv uv xv bv)
  a⁰ : ∀ {p₁ b w} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → WF x → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → WF (add⁰ W gu R x gx m gm um tm am)
  aL : ∀ {p₁ h k w} (t : h <ᴺ p) (j : h <ᴺ p₁) (x : Low p₁ j k w) (gx : Gw w) → WFL j x → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : k ⊲ m) → WF (addL W gu t j x gx m gm um tm km)

  aw R x gx wx v gv uv xv bv with mx gu gv uv xv bv
  ... | mx′ m gm um tm am mv = a⁰ R x gx wx m gm um tm am

  a⁰ R o0 gx wx m gm um tm am = wW
  a⁰ R (os x) gx wx m gm um tm am = aw R x gx wx m gm um tm am
  a⁰ R (ol F) gx (st , u) m gm um tm am =
    (λ n → mm2 (st n) R R gx gx m gm um tm am m gm um tm am) , (λ n → aw R (F n) gx (u n) m gm um tm am)
  a⁰ (sa P) (oi r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMi {r = r} wx (⊲-tr tm q) g d) (sa P) (sa P) g g v g (⊲-tr um q) C.self (z⊲ v) v g (⊲-tr um q) C.self (z⊲ v)) ,
    (λ {v} q g y py uy → aw (sa P) (h (⊲-tr tm q) g _) g (hWi {r = r} wx (⊲-tr tm q) g _ py (S→W _ y uy)) v g (⊲-tr um q) C.self (z⊲ v))
  a⁰ (lw i) (oi r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMi {r = r} wx (⊲-tr tm q) g d) (lw i) (lw i) g g v g (⊲-tr um q) C.self (⊲-tr am q) v g (⊲-tr um q) C.self (⊲-tr am q)) ,
    (λ {v} q g y py uy → aw (lw i) (h (⊲-tr tm q) g _) g (hWi {r = r} wx (⊲-tr tm q) g _ py (L→W i y uy)) v g (⊲-tr um q) C.self (⊲-tr am q))
  a⁰ (sa P) (od j k r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMd {i = j} {r = r} wx (⊲-tr tm q) g d) (sa P) (sa P) g g v g (⊲-tr um q) C.self (z⊲ v) v g (⊲-tr um q) C.self (z⊲ v)) ,
    (λ {v} q g y py uy → aw (sa P) (h (⊲-tr tm q) g _) g (hWd {i = j} {r = r} wx (⊲-tr tm q) g _ py (L→W j y uy)) v g (⊲-tr um q) C.self (z⊲ v))
  a⁰ (lw i) (od j k r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMd {i = j} {r = r} wx (⊲-tr tm q) g d) (lw i) (lw i) g g v g (⊲-tr um q) C.self (⊲-tr am q) v g (⊲-tr um q) C.self (⊲-tr am q)) ,
    (λ {v} q g y py uy → aw (lw i) (h (⊲-tr tm q) g _) g (hWd {i = j} {r = r} wx (⊲-tr tm q) g _ py (L→W (<tr j i) y uy)) v g (⊲-tr um q) C.self (⊲-tr am q))
  a⁰ R (oc x h) gx (fi , dr , wx , wh) m gm um tm am =
    (λ {v} q g → mm2 (fi (⊲-tr tm q) g) R R gx g m gm um tm am v g (⊲-tr um q) C.self (⊲-tr am q)) ,
    (λ {v} {v′} q q′ g g′ p₁ → mm2 (dr (⊲-tr tm q) (⊲-tr tm q′) g g′ p₁) R R g g′ v g (⊲-tr um q) C.self (⊲-tr am q) v′ g′ (⊲-tr um q′) C.self (⊲-tr am q′)) ,
    aw R x gx wx m gm um tm am ,
    (λ {v} q g → aw R (h (⊲-tr tm q) g) g (wh (⊲-tr tm q) g) v g (⊲-tr um q) C.self (⊲-tr am q))
  a⁰ (sa P) (oe es x) gx wx m gm um tm am = aw (sa (⊲-tr (C.suc C.self) P)) x gx wx m gm um tm am
  a⁰ (lw i) (oe es x) gx wx m gm um tm am = aw (lw i) x gx wx m gm um tm (⊲-tr (C.suc C.self) am)
  a⁰ (sa P) (oe (el n) x) gx wx m gm um tm am = aw (sa (⊲-tr (C.lim n C.self) P)) x gx wx m gm um tm am
  a⁰ (lw i) (oe (el n) x) gx wx m gm um tm am = aw (lw i) x gx wx m gm um tm (⊲-tr (C.lim n C.self) am)
  a⁰ (sa P) (oL j k e x) gx wx m gm um tm am = aL j j x gx wx m gm um tm (⊲-tr e tm)
  a⁰ (lw i) (oL j k e x) gx wx m gm um tm am = aL (<tr j i) j x gx wx m gm um tm (⊲-tr e tm)
  a⁰ R (ow w g′ x) gx wx m gm um tm am = aw R x g′ wx m gm um (⊲-tr w tm) am

  aL t zero x gx wx m gm um tm km = aw (lw t) x gx wx m gm um tm km
  aL t (suc j) x gx wx m gm um tm km = aL t j x gx wx m gm um tm km

rep⊴ : ∀ {q t u} {y : 𝓞 q t u} (e : y ≈ y) (g : Gw u) → ∀ n → rep y g n ⊴ rep y g (suc n)
rep⊴ {y = y} e g zero = z⊴ y
rep⊴ {t = t} {u} {y} e g (suc m) = AddF.add⊴ (rep y g (suc m)) g (rf (rep≈ (≈ᴬ-refl t) (≈ᴬ-refl u) e g g (suc m))) (sa C.self) y g u g C.self C.self (z⊲ u)

repW : ∀ {q t u} {y : 𝓞 q t u} (e : y ≈ y) (g : Gw u) → WF y → ∀ n → WF (rep y g n)
repW e g w zero = tt
repW e g w (suc zero) = w
repW {t = t} {u} {y} e g w (suc (suc m)) =
  AddW.aw (rep y g (suc m)) g (rep≈ (≈ᴬ-refl t) (≈ᴬ-refl u) e g g (suc m)) (repW e g w (suc m)) (sa C.self) y g w u g C.self C.self (z⊲ u)
```

## §4 闭包定理

对项递归. 上升时链 $z_n$ 的 `WF`, 相邻的 `⊴` 都是这条定理自己. **与高度, 阶段无关.**

```agda
ψW  : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) → x ≈ x → WF x → WF (ψ q t x gu v gv uv tv av)
ψWm : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) → x ≈ x → WF x → WF (ψᵐ q t x gu v gv uv tv av)
ψW⁰ : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → x ≈ x → WF x → WF (ψ⁰ q t x gu m gm um tm am)
ψWL : ∀ {p h k u} q t (j : h <ᴺ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (km : k ⊲ m) → outL j x ≈ outL j x → WFL j x → WF (ψL q t j x gu m gm um tm km)

ψW q t x gu v gv uv tv av e w = ψWm q t x gu v gv uv tv av e w

ψWm q t x gu v gv uv tv av e w with mx gu gv uv tv av
... | mx′ m gm um tm am mv = ψW⁰ q t x gu m gm um tm am e w

ψW⁰ q t o0 gu m gm um tm am e w = ΩW q t (lg⊲ tm (lgw gm))
ψW⁰ q t (os x) gu m gm um tm am (_ , _ , _ , e) w =
  (λ n → rep⊴ (ψQ x x gu gu m gm um tm am m gm um tm am (≈ᴬ-refl t) e) gm n) ,
  (λ n → repW (ψQ x x gu gu m gm um tm am m gm um tm am (≈ᴬ-refl t) e) gm (ψW q t x gu m gm um tm am e w) n)
ψW⁰ q t (ol F) gu m gm um tm am e (st , u) =
  (λ n → ψL′ q t (st n) gu gu m gm um tm am m gm um tm am) , (λ n → ψW q t (F n) gu m gm um tm am (e n) (u n))
ψW⁰ {p} {a} q t (oi {k = k} r f) gu m gm um tm am (_ , _ , _ , _ , N) w with <ᴺ-dec p q
... | injᵃ i =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMi {r = r} w (⊲-tr um w₁) g d) g g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)
      (nI {r = r} {r} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWi {r = r} w (⊲-tr um w₁) g _ py (L→W i y uy)))
... | injᵇ _ =
  (λ n → ψL′ q t (hMi {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat p gm gm (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (⊲-tr (≪⊲ r) am) am m gm C.self (⊲-tr (≪⊲ r) am) am (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩW p k (lg⊲ (⊲-tr (≪⊲ r) am) (lgw gm))
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (⊲-tr (≪⊲ r) am) am m gm C.self (⊲-tr (≪⊲ r) am) am
... | injᶜ refl with cmpN (≪∘ r am) tm (lgw gm)
...   | keep s′ =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMi {r = r} w (⊲-tr um w₁) g d) g g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)
      (nI {r = r} {r} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWi {r = r} w (⊲-tr um w₁) g _ py (S→W (≪S s′) y uy)))
...   | rise _ =
  (λ n → ψL′ q t (hMi {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat p gm gm (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (⊲-tr (≪⊲ r) am) am m gm C.self (⊲-tr (≪⊲ r) am) am (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩW p k (lg⊲ (⊲-tr (≪⊲ r) am) (lgw gm))
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (⊲-tr (≪⊲ r) am) am m gm C.self (⊲-tr (≪⊲ r) am) am
ψW⁰ q t (od {h = h₀} j k r f) gu m gm um tm am (_ , _ , _ , _ , _ , N) w with <ᴺ-dec h₀ q
... | injᵃ i =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMd {i = j} {r = r} w (⊲-tr um w₁) g d) g g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)
      (nD {j = j} {j} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWd {i = j} {r = r} w (⊲-tr um w₁) g _ py (L→W i y uy)))
... | injᵇ _ =
  (λ n → ψL′ q t (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat h₀ gm gm (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (⊲-tr (≪⊲ r) um) am m gm C.self (⊲-tr (≪⊲ r) um) am (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩW h₀ k (lg⊲ (⊲-tr (≪⊲ r) um) (lgw gm))
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) um) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) um) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (⊲-tr (≪⊲ r) um) am m gm C.self (⊲-tr (≪⊲ r) um) am
... | injᶜ refl with cmpN (≪∘ r um) tm (lgw gm)
...   | keep s′ =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMd {i = j} {r = r} w (⊲-tr um w₁) g d) g g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)
      (nD {j = j} {j} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWd {i = j} {r = r} w (⊲-tr um w₁) g _ py (S→W (≪S s′) y uy)))
...   | rise _ =
  (λ n → ψL′ q t (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat h₀ gm gm (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (⊲-tr (≪⊲ r) um) am m gm C.self (⊲-tr (≪⊲ r) um) am (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩW h₀ k (lg⊲ (⊲-tr (≪⊲ r) um) (lgw gm))
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) um) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (⊲-tr (≪⊲ r) um) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (⊲-tr (≪⊲ r) um) am m gm C.self (⊲-tr (≪⊲ r) um) am
ψW⁰ q t (oc x f) gu m gm um tm am (_ , _ , _ , ex , N) (fi , dr , wx , wf) =
  (λ {v} w₁ g → ψL′ q t (fi (⊲-tr um w₁) g) gu g m gm um tm am v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)) ,
  (λ {v} {v′} w₁ w₂ g g′ p₁ → ψL′ q t (dr (⊲-tr um w₁) (⊲-tr um w₂) g g′ p₁) g g′ v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) v′ g′ C.self (⊲-tr tm w₂) (⊲-tr am w₂)) ,
  ψW q t x gu m gm um tm am ex wx ,
  (λ {v} w₁ g → ψW q t (f (⊲-tr um w₁) g) g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) (N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v)) (wf (⊲-tr um w₁) g))
ψW⁰ q t (oe es x) gu m gm um tm am e w = ψW q t x gu m gm um tm (⊲-tr (C.suc C.self) am) (≈oe⁻ {R = ss C.self} x es x e) w
ψW⁰ q t (oe (el n) x) gu m gm um tm am e w = ψW q t x gu m gm um tm (⊲-tr (C.lim n C.self) am) (≈oe⁻ {R = sl n C.self} x (el n) x e) w
ψW⁰ q t (oL j k e₁ x) gu m gm um tm am e w = ψWL q t j x gu m gm um tm (⊲-tr e₁ um) (≈oL⁻ (outL j x) j e₁ x (Ll→ j x e)) w
ψW⁰ q t (ow p g′ x) gu m gm um tm am e w = ψW q t x g′ m gm (⊲-tr p um) tm am (≈ow⁻ x p g′ x e) w

ψWL q t zero x gu m gm um tm km e w = ψW q t x gu m gm um tm km e w
ψWL q t (suc j) x gu m gm um tm km e w = ψWL q t j x gu m gm um tm km e w
```

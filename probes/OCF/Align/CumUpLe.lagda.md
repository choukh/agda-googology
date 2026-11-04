# 带高度的世界: 第一位置, 加法

> 不含记号. 结论写在 [CumUp](CumUp.lagda.md). `x ⊴ y`: $x$ 模 `≈` 是 $y$ 的第一位置. 节点的第一位置是 $h(\Omega_k)$, 闭包的第一位置是第一支. 层和世界都可以不同. 这一篇是加法的部分.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpLe where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.CumUpW
open import OCF.Align.CumUpEq
```

## §1 第一位置

```agda
infix 4 _⊴_
data _⊴_ : ∀ {p a u p′ a′ u′} → 𝓞 p a u → 𝓞 p′ a′ u′ → Set where
  rf : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ≈ y → x ⊴ y
  s  : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → x ⊴ os y
  l  : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {F : ℕ → 𝓞 p′ a′ u′} n → x ⊴ F n → x ⊴ ol F
  fc : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} {h : ∀ {v} → u′ ⊲ v → Gw v → 𝓞 p′ a′ v} → x ⊴ y → x ⊴ oc y h
  ni : ∀ {p a u p′ a′ u′ k} {x : 𝓞 p a u} {r : k ≪ a′} {h : ∀ {v} → u′ ⊲ v → Gw v → Vs p′ a′ (≪S r) v → 𝓞 p′ a′ v} →
       (∀ {v} (q : u′ ⊲ v) (g : Gw v) → x ⊴ h q g (inS (≪S r) (Ω̇at p′ k g))) → x ⊴ oi r h
  nd : ∀ {p a u p′ a′ u′ h₀ k} {x : 𝓞 p a u} {i : h₀ <ᴺ p′} {r : k ≪ u′} {h : ∀ {v} → u′ ⊲ v → Gw v → Low p′ i k v → 𝓞 p′ a′ v} →
       (∀ {v} (q : u′ ⊲ v) (g : Gw v) → x ⊴ h q g (inL i (Ω̇at h₀ k g))) → x ⊴ od i k r h
  eR : ∀ {p a u p′ c b u′} {x : 𝓞 p a u} {R : Strict b c} {stp : Stp R} {y : Vs p′ c R u′} → x ⊴ outS R y → x ⊴ oe stp y
  eL : ∀ {p c b u p′ a′ u′} {R : Strict b c} {stp : Stp R} {x : Vs p c R u} {y : 𝓞 p′ a′ u′} → outS R x ⊴ y → oe stp x ⊴ y
  rL : ∀ {p a u p′ a′ h₀ k u′} {x : 𝓞 p a u} {j : h₀ <ᴺ p′} {e : k ⊲ u′} {y : Low p′ j k u′} → x ⊴ outL j y → _⊴_ {a′ = a′} x (oL j k e y)
  lL : ∀ {p a h₀ k u p′ a′ u′} {j : h₀ <ᴺ p} {e : k ⊲ u} {x : Low p j k u} {y : 𝓞 p′ a′ u′} → outL j x ⊴ y → _⊴_ {a = a} (oL j k e x) y
  rw : ∀ {p a u p′ a′ u′ v′} {x : 𝓞 p a u} {w : u′ ⊲ v′} {g : Gw u′} {y : 𝓞 p′ a′ u′} → x ⊴ y → x ⊴ ow w g y
  lw₂ : ∀ {p a u v p′ a′ u′} {w : u ⊲ v} {g : Gw u} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → ow w g x ⊴ y

Ω⊴ : ∀ p {a b} → a ⊲ b → Ω̇ p a ⊴ Ω̇ p b
Ω⊴ p {a} C.self = rf (Ω≈ p (≈ᴬ-refl a))
Ω⊴ p (C.suc P) = ni (λ q g → eR {stp = es} (rw (Ω⊴ p P)))
Ω⊴ p (C.lim n P) = l n (eR {stp = el n} (Ω⊴ p P))

z⊴ : ∀ {p₀ a₀ u₀ p a u} (x : 𝓞 p a u) → o0 {p₀} {a₀} {Vs p₀ a₀} {Low p₀} {u₀} ⊴ x
z⊴L : ∀ {p₀ a₀ u₀ p h k u} (j : h <ᴺ p) (x : Low p j k u) → o0 {p₀} {a₀} {Vs p₀ a₀} {Low p₀} {u₀} ⊴ outL j x
z⊴ o0 = rf tt
z⊴ (os x) = s (z⊴ x)
z⊴ (ol F) = l 0 (z⊴ (F 0))
z⊴ (oi r h) = ni (λ q g → z⊴ (h q g _))
z⊴ (od i k r h) = nd (λ q g → z⊴ (h q g _))
z⊴ (oc x h) = fc (z⊴ x)
z⊴ (oe es x) = eR {stp = es} (z⊴ x)
z⊴ (oe (el n) x) = eR {stp = el n} (z⊴ x)
z⊴ (oL j k e x) = rL (z⊴L j x)
z⊴ (ow w g x) = rw (z⊴ x)
z⊴L zero x = z⊴ x
z⊴L (suc j) x = z⊴L j x
```

## §2 $X\trianglelefteq W\Rightarrow X\trianglelefteq W+x$

```agda
module AddF {p a u₀} (W : 𝓞 p a u₀) (gu : Gw u₀) where
  add⊴ : ∀ {p₀ a₀ w₀ p₁ b w} {X : 𝓞 p₀ a₀ w₀} → X ⊴ W → (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw R ⊲ v) → X ⊴ add W gu R x gx v gv uv xv bv
  add⁰⊴ : ∀ {p₀ a₀ w₀ p₁ b w} {X : 𝓞 p₀ a₀ w₀} → X ⊴ W → (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → X ⊴ add⁰ W gu R x gx m gm um tm am
  addL⊴ : ∀ {p₀ a₀ w₀ p₁ h k w} {X : 𝓞 p₀ a₀ w₀} → X ⊴ W → (t : h <ᴺ p) (j : h <ᴺ p₁) (x : Low p₁ j k w) (gx : Gw w) → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : k ⊲ m) → X ⊴ addL W gu t j x gx m gm um tm km

  add⊴ d R x gx v gv uv xv bv with mx gu gv uv xv bv
  ... | mx′ m gm um tm am mv = rw (add⁰⊴ d R x gx m gm um tm am)

  add⁰⊴ d R o0 gx m gm um tm am = rw d
  add⁰⊴ d R (os x) gx m gm um tm am = s (add⊴ d R x gx m gm um tm am)
  add⁰⊴ d R (ol F) gx m gm um tm am = l 0 (add⊴ d R (F 0) gx m gm um tm am)
  add⁰⊴ {X = X} d (sa P) (oi {k = k} r h) gx m gm um tm am = ni (λ {v} q g →
    subst (λ z → X ⊴ add W gu (sa P) (h (⊲-tr tm q) g (inS (≪S r) z)) g v g (⊲-tr um q) C.self (z⊲ v)) (sym (out-inS (≪S (≪∘ r P)) (Ω̇at _ k g)))
      (add⊴ d (sa P) (h (⊲-tr tm q) g (inS (≪S r) (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (z⊲ v)))
  add⁰⊴ {X = X} d (lw i) (oi {k = k} r h) gx m gm um tm am = nd (λ {v} q g →
    subst (λ z → X ⊴ add W gu (lw i) (h (⊲-tr tm q) g (inS (≪S r) z)) g v g (⊲-tr um q) C.self (⊲-tr am q)) (sym (out-inL i (Ω̇at _ k g)))
      (add⊴ d (lw i) (h (⊲-tr tm q) g (inS (≪S r) (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (⊲-tr am q)))
  add⁰⊴ {X = X} d (sa P) (od j k r h) gx m gm um tm am = nd (λ {v} q g →
    subst (λ z → X ⊴ add W gu (sa P) (h (⊲-tr tm q) g (inL j z)) g v g (⊲-tr um q) C.self (z⊲ v)) (sym (out-inL j (Ω̇at _ k g)))
      (add⊴ d (sa P) (h (⊲-tr tm q) g (inL j (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (z⊲ v)))
  add⁰⊴ {X = X} d (lw i) (od j k r h) gx m gm um tm am = nd (λ {v} q g →
    subst (λ z → X ⊴ add W gu (lw i) (h (⊲-tr tm q) g (inL j z)) g v g (⊲-tr um q) C.self (⊲-tr am q)) (sym (out-inL (<tr j i) (Ω̇at _ k g)))
      (add⊴ d (lw i) (h (⊲-tr tm q) g (inL j (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (⊲-tr am q)))
  add⁰⊴ d R (oc x h) gx m gm um tm am = fc (add⊴ d R x gx m gm um tm am)
  add⁰⊴ d (sa P) (oe es x) gx m gm um tm am = add⊴ d (sa (⊲-tr (C.suc C.self) P)) x gx m gm um tm am
  add⁰⊴ d (lw i) (oe es x) gx m gm um tm am = add⊴ d (lw i) x gx m gm um tm (⊲-tr (C.suc C.self) am)
  add⁰⊴ d (sa P) (oe (el n) x) gx m gm um tm am = add⊴ d (sa (⊲-tr (C.lim n C.self) P)) x gx m gm um tm am
  add⁰⊴ d (lw i) (oe (el n) x) gx m gm um tm am = add⊴ d (lw i) x gx m gm um tm (⊲-tr (C.lim n C.self) am)
  add⁰⊴ d (sa P) (oL j k e x) gx m gm um tm am = addL⊴ d j j x gx m gm um tm (⊲-tr e tm)
  add⁰⊴ d (lw i) (oL j k e x) gx m gm um tm am = addL⊴ d (<tr j i) j x gx m gm um tm (⊲-tr e tm)
  add⁰⊴ d R (ow w g′ x) gx m gm um tm am = add⊴ d R x g′ m gm um (⊲-tr w tm) am

  addL⊴ d t zero x gx m gm um tm km = add⊴ d (lw t) x gx m gm um tm km
  addL⊴ d t (suc j) x gx m gm um tm km = addL⊴ d t j x gx m gm um tm km
```

## §3 右边单调

左边的 $W$ 同一个. `rf` 的一条走 `AddE.add⁰≈`, 这是输出世界规范化 (`mx`) 的用处.

```agda
module AddM {p a u₀} (W : 𝓞 p a u₀) (gu : Gw u₀) (E : W ≈ W) where
  open AddE {W = W} {W′ = W} (≈ᴬ-refl a) (≈ᴬ-refl u₀) E gu gu using (add⁰≈)

  mm : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
       ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → Mis m u₀ w (bw R) →
       ∀ m′ (gm′ : Gw m′) (um′ : u₀ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : bw R′ ⊲ m′) → Mis m′ u₀ w′ (bw R′) →
       add⁰ W gu R x gx m gm um tm am ⊴ add⁰ W gu R′ y gy m′ gm′ um′ tm′ am′

  mR : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
       ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → Mis m u₀ w (bw R) →
       ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (yv : w′ ⊲ v) (bv : bw R′ ⊲ v) →
       add⁰ W gu R x gx m gm um tm am ⊴ add W gu R′ y gy v gv uv yv bv
  mR d R R′ gx gy m gm um tm am is v gv uv yv bv with mx gu gv uv yv bv | mx-is gu gv uv yv bv
  ... | mx′ m′ gm′ um′ tm′ am′ mv | is′ = rw (mm d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′)

  mLn : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw R ⊲ v) →
        ∀ m′ (gm′ : Gw m′) (um′ : u₀ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : bw R′ ⊲ m′) → Mis m′ u₀ w′ (bw R′) →
        add W gu R x gx v gv uv xv bv ⊴ add⁰ W gu R′ y gy m′ gm′ um′ tm′ am′
  mLn d R R′ gx gy v gv uv xv bv m′ gm′ um′ tm′ am′ is′ with mx gu gv uv xv bv | mx-is gu gv uv xv bv
  ... | mx′ m gm um tm am mv | is = lw₂ (mm d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′)

  mm2 : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : bw R ⊲ v) →
        ∀ v′ (gv′ : Gw v′) (uv′ : u₀ ⊲ v′) (yv′ : w′ ⊲ v′) (bv′ : bw R′ ⊲ v′) →
        add W gu R x gx v gv uv xv bv ⊴ add W gu R′ y gy v′ gv′ uv′ yv′ bv′
  mm2 d R R′ gx gy v gv uv xv bv v′ gv′ uv′ yv′ bv′ with mx gu gv uv xv bv | mx-is gu gv uv xv bv
  ... | mx′ m gm um tm am mv | is = lw₂ (mR d R R′ gx gy m gm um tm am is v′ gv′ uv′ yv′ bv′)

  mRL : ∀ {p₁ b w p₂ h k w′} {x : 𝓞 p₁ b w} (t : h <ᴺ p) (j : h <ᴺ p₂) (y : Low p₂ j k w′) → x ⊴ outL j y → (R : Rel p₁ b p a) (gx : Gw w) (gy : Gw w′) →
        ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : bw R ⊲ m) → Mis m u₀ w (bw R) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (yv : w′ ⊲ v) (kv : k ⊲ v) →
        add⁰ W gu R x gx m gm um tm am ⊴ addL W gu t j y gy v gv uv yv kv
  mRL t zero y d R gx gy m gm um tm am is v gv uv yv kv = mR d R (lw t) gx gy m gm um tm am is v gv uv yv kv
  mRL t (suc j) y d R gx gy m gm um tm am is v gv uv yv kv = mRL t j y d R gx gy m gm um tm am is v gv uv yv kv

  mLL : ∀ {p₁ h k w p₂ b′ w′} {y : 𝓞 p₂ b′ w′} (t : h <ᴺ p) (j : h <ᴺ p₁) (x : Low p₁ j k w) → outL j x ⊴ y → (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (kv : k ⊲ v) →
        ∀ m′ (gm′ : Gw m′) (um′ : u₀ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : bw R′ ⊲ m′) → Mis m′ u₀ w′ (bw R′) →
        addL W gu t j x gx v gv uv xv kv ⊴ add⁰ W gu R′ y gy m′ gm′ um′ tm′ am′
  mLL t zero x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLn d (lw t) R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′
  mLL t (suc j) x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLL t j x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′

  mm {x = x} {y} (rf e) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = rf (add⁰≈ R R′ x y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ e)
  mm (s {y = y₀} d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = s (mR d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′)
  mm (l n d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l n (mR d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′)
  mm (fc d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = fc (mR d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′)
  mm {x = x} (ni {k = k} {r = r} {h = h} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = ni (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (sa P) (h (⊲-tr tm′ q) g (inS (≪S r) z)) g v g (⊲-tr um′ q) C.self (z⊲ v)) (sym (out-inS (≪S (≪∘ r P)) (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (sa P) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (z⊲ v)))
  mm {x = x} (ni {k = k} {r = r} {h = h} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = nd (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (lw i) (h (⊲-tr tm′ q) g (inS (≪S r) z)) g v g (⊲-tr um′ q) C.self (⊲-tr am′ q)) (sym (out-inL i (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (lw i) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (⊲-tr am′ q)))
  mm {x = x} (nd {k = k} {i = j} {h = h} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = nd (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (sa P) (h (⊲-tr tm′ q) g (inL j z)) g v g (⊲-tr um′ q) C.self (z⊲ v)) (sym (out-inL j (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (sa P) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (z⊲ v)))
  mm {x = x} (nd {k = k} {i = j} {h = h} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = nd (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (lw i) (h (⊲-tr tm′ q) g (inL j z)) g v g (⊲-tr um′ q) C.self (⊲-tr am′ q)) (sym (out-inL (<tr j i) (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (lw i) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (⊲-tr am′ q)))
  mm (eR {stp = es} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (sa (⊲-tr (C.suc C.self) P)) gx gy m gm um tm am is m′ gm′ um′ tm′ am′
  mm (eR {stp = es} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′)
  mm (eR {stp = el n} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (sa (⊲-tr (C.lim n C.self) P)) gx gy m gm um tm am is m′ gm′ um′ tm′ am′
  mm (eR {stp = el n} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′)
  mm (eL {stp = es} d) (sa P) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (sa (⊲-tr (C.suc C.self) P)) R′ gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′
  mm (eL {stp = es} d) (lw i) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (lw i) R′ gx gy m gm um tm (⊲-tr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′
  mm (eL {stp = el n} d) (sa P) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (sa (⊲-tr (C.lim n C.self) P)) R′ gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′
  mm (eL {stp = el n} d) (lw i) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (lw i) R′ gx gy m gm um tm (⊲-tr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′
  mm (rL {j = j} {e = e} {y = y} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mRL j j y d R gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′)
  mm (rL {j = j} {e = e} {y = y} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mRL (<tr j i) j y d R gx gy m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e tm′)
  mm (lL {j = j} {e = e} {x = x} d) (sa P) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLL j j x d R′ gx gy m gm um tm (⊲-tr e tm) m′ gm′ um′ tm′ am′ is′
  mm (lL {j = j} {e = e} {x = x} d) (lw i) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLL (<tr j i) j x d R′ gx gy m gm um tm (⊲-tr e tm) m′ gm′ um′ tm′ am′ is′
  mm (rw {w = w} {g = g} d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R R′ gx g m gm um tm am is m′ gm′ um′ (⊲-tr w tm′) am′
  mm (lw₂ {w = w} {g = g} d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d R R′ g gy m gm um (⊲-tr w tm) am m′ gm′ um′ tm′ am′ is′
```

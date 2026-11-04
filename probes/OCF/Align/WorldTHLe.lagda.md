# 带高度的世界: 第一位置, 加法

> 不含记号. 结论写在 [WorldTH](WorldTH.lagda.md). `x ⊴ y`: $x$ 模 `≈` 是 $y$ 的第一位置. 节点的第一位置是 $h(\Omega_k)$, 闭包的第一位置是第一支. 层和世界都可以不同. 这一篇是加法的部分.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHLe where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHEq
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
  nd : ∀ {p a u p′ a′ u′ h₀ k} {x : 𝓞 p a u} {i : h₀ <ᴴ p′} {r : (k ≪ u′) × Hb p′ h₀ u′} {h : ∀ {v} → u′ ⊲ v → Gw v → Low p′ i k v → 𝓞 p′ a′ v} →
       (∀ {v} (q : u′ ⊲ v) (g : Gw v) → x ⊴ h q g (inL i (Ω̇at h₀ k g))) → x ⊴ od i k r h
  eR : ∀ {p a u p′ c b u′} {x : 𝓞 p a u} {R : Strict b c} {stp : Stp R} {y : Vs p′ c R u′} → x ⊴ outS R y → x ⊴ oe stp y
  eL : ∀ {p c b u p′ a′ u′} {R : Strict b c} {stp : Stp R} {x : Vs p c R u} {y : 𝓞 p′ a′ u′} → outS R x ⊴ y → oe stp x ⊴ y
  rL : ∀ {p a u p′ a′ h₀ k u′} {x : 𝓞 p a u} {j : h₀ <ᴴ p′} {e : (k ⊲ u′) × Hb p′ h₀ u′} {y : Low p′ j k u′} → x ⊴ outL j y → _⊴_ {a′ = a′} x (oL j k e y)
  lL : ∀ {p a h₀ k u p′ a′ u′} {j : h₀ <ᴴ p} {e : (k ⊲ u) × Hb p h₀ u} {x : Low p j k u} {y : 𝓞 p′ a′ u′} → outL j x ⊴ y → _⊴_ {a = a} (oL j k e x) y
  rw : ∀ {p a u p′ a′ u′ v′} {x : 𝓞 p a u} {w : u′ ⊲ v′} {g : Gw u′} {y : 𝓞 p′ a′ u′} → x ⊴ y → x ⊴ ow w g y
  lw₂ : ∀ {p a u v p′ a′ u′} {w : u ⊲ v} {g : Gw u} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → ow w g x ⊴ y

ΩU : ∀ p {a b p₀ a₀ u₀} {x : 𝓞 p₀ a₀ u₀} → x ⊴ Ω̇ p a → a ⊲ b → x ⊴ Ω̇ p b
ΩU p d C.self = d
ΩU p d (C.suc P) = ni (λ q g → eR {stp = es} (rw (ΩU p d P)))
ΩU p d (C.lim n P) = l n (eR {stp = el n} (ΩU p d P))

Ω⊴ : ∀ p {a b} → HT p → a ⊲ b → Ω̇ p a ⊴ Ω̇ p b
Ω⊴ p {a} H P = ΩU p (rf (Ω≈ (hrefl H) (≈ᴬ-refl a))) P

-- 高度上的单调: 顶行的分支
Ωh⊴ : ∀ {a b} → a ⊲ b → Ω̇ (ht a) azero ⊴ Ω̇ (ht b) azero
Ωh⊴ {a} C.self = rf (Ω≈ (ht≈ (≈ᴬ-refl a)) z≈)
Ωh⊴ (C.suc P) = fc (rL (ΩU (ht _) (Ωh⊴ P) (z⊲ one)))
Ωh⊴ (C.lim n P) = l n (rL (Ωh⊴ P))

z⊴ : ∀ {p₀ a₀ u₀ p a u} (x : 𝓞 p a u) → o0 {p₀} {a₀} {Vs p₀ a₀} {Low p₀} {u₀} ⊴ x
z⊴L : ∀ {p₀ a₀ u₀ p h k u} (j : h <ᴴ p) (x : Low p j k u) → o0 {p₀} {a₀} {Vs p₀ a₀} {Low p₀} {u₀} ⊴ outL j x
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
z⊴L here x = z⊴ x
z⊴L (lh n₉) x = z⊴ x
z⊴L (tp a₉) x = z⊴ x
z⊴L (st j) x = z⊴L j x
z⊴L (ll n₉ j) x = z⊴L j x
z⊴L (tq a₉ j) x = z⊴L j x
```

## §2 $X\trianglelefteq W\Rightarrow X\trianglelefteq W+x$

```agda
module AddF {p a u₀} (W : 𝓞 p a u₀) (gu : Gw u₀) where
  add⊴ : ∀ {p₀ a₀ w₀ p₁ b w} {X : 𝓞 p₀ a₀ w₀} → X ⊴ W → (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : BW R v) → X ⊴ add W gu R x gx v gv uv xv bv
  add⁰⊴ : ∀ {p₀ a₀ w₀ p₁ b w} {X : 𝓞 p₀ a₀ w₀} → X ⊴ W → (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → X ⊴ add⁰ W gu R x gx m gm um tm am
  addL⊴ : ∀ {p₀ a₀ w₀ p₁ h k w} {X : 𝓞 p₀ a₀ w₀} → X ⊴ W → (t : h <ᴴ p) (j : h <ᴴ p₁) (x : Low p₁ j k w) (gx : Gw w) → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : BW {b = k} {a = a} (lw t) m) → X ⊴ addL W gu t j x gx m gm um tm km

  add⊴ d R x gx v gv uv xv bv = rw (add⁰⊴ d R x gx (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ bv))
    where
    M = mx gu gv uv (lbu xv) (proj₁ bv)

  add⁰⊴ d R o0 gx m gm um tm am = rw d
  add⁰⊴ d R (os x) gx m gm um tm am = s (add⊴ d R x gx m gm um tm am)
  add⁰⊴ d R (ol F) gx m gm um tm am = l 0 (add⊴ d R (F 0) gx m gm um tm am)
  add⁰⊴ {X = X} d (sa P) (oi {k = k} r h) gx m gm um tm am = ni (λ {v} q g →
    subst (λ z → X ⊴ add W gu (sa P) (h (⊲-tr tm q) g (inS (≪S r) z)) g v g (⊲-tr um q) C.self (lb0 v , proj₂ am)) (sym (out-inS (≪S (≪∘ r P)) (Ω̇at _ k g)))
      (add⊴ d (sa P) (h (⊲-tr tm q) g (inS (≪S r) (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (lb0 v , proj₂ am)))
  add⁰⊴ {X = X} d (lw i) (oi {k = k} r h) gx m gm um tm am = nd (λ {v} q g →
    subst (λ z → X ⊴ add W gu (lw i) (h (⊲-tr tm q) g (inS (≪S r) z)) g v g (⊲-tr um q) C.self (bw↑ _ am q)) (sym (out-inL i (Ω̇at _ k g)))
      (add⊴ d (lw i) (h (⊲-tr tm q) g (inS (≪S r) (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (bw↑ _ am q)))
  add⁰⊴ {X = X} d (sa P) (od j k r h) gx m gm um tm am = nd (λ {v} q g →
    subst (λ z → X ⊴ add W gu (sa P) (h (⊲-tr tm q) g (inL j z)) g v g (⊲-tr um q) C.self (lb0 v , proj₂ am)) (sym (out-inL j (Ω̇at _ k g)))
      (add⊴ d (sa P) (h (⊲-tr tm q) g (inL j (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (lb0 v , proj₂ am)))
  add⁰⊴ {X = X} d (lw i) (od j k r h) gx m gm um tm am = nd (λ {v} q g →
    subst (λ z → X ⊴ add W gu (lw i) (h (⊲-tr tm q) g (inL j z)) g v g (⊲-tr um q) C.self (bw↑ _ am q)) (sym (out-inL (<tr j i) (Ω̇at _ k g)))
      (add⊴ d (lw i) (h (⊲-tr tm q) g (inL j (Ω̇at _ k g))) g v g (⊲-tr um q) C.self (bw↑ _ am q)))
  add⁰⊴ d R (oc x h) gx m gm um tm am = fc (add⊴ d R x gx m gm um tm am)
  add⁰⊴ d (sa P) (oe es x) gx m gm um tm am = add⊴ d (sa (⊲-tr (C.suc C.self) P)) x gx m gm um tm am
  add⁰⊴ d (lw i) (oe es x) gx m gm um tm am = add⊴ d (lw i) x gx m gm um tm (bw↓ i (C.suc C.self) am)
  add⁰⊴ d (sa P) (oe (el n) x) gx m gm um tm am = add⊴ d (sa (⊲-tr (C.lim n C.self) P)) x gx m gm um tm am
  add⁰⊴ d (lw i) (oe (el n) x) gx m gm um tm am = add⊴ d (lw i) x gx m gm um tm (bw↓ i (C.lim n C.self) am)
  add⁰⊴ d (sa P) (oL j k e x) gx m gm um tm am = addL⊴ d j j x gx m gm um tm (bwEe j e tm (proj₂ am))
  add⁰⊴ d (lw i) (oL j k e x) gx m gm um tm am = addL⊴ d (<tr j i) j x gx m gm um tm (bwTr j i e tm am)
  add⁰⊴ d R (ow w g′ x) gx m gm um tm am = add⊴ d R x g′ m gm um (⊲-tr w tm) am

  addL⊴ d t here x gx m gm um tm km = add⊴ d (lw t) x gx m gm um tm km
  addL⊴ d t (lh n₉) x gx m gm um tm km = add⊴ d (lw t) x gx m gm um tm km
  addL⊴ d t (tp a₉) x gx m gm um tm km = add⊴ d (lw t) x gx m gm um tm km
  addL⊴ d t (st j) x gx m gm um tm km = addL⊴ d t j x gx m gm um tm km
  addL⊴ d t (ll n₉ j) x gx m gm um tm km = addL⊴ d t j x gx m gm um tm km
  addL⊴ d t (tq a₉ j) x gx m gm um tm km = addL⊴ d t j x gx m gm um tm km
```

## §3 右边单调

左边的 $W$ 同一个. `rf` 的一条走 `AddE.add⁰≈`, 这是输出世界规范化 (`mx`) 的用处.

```agda
module AddM {p a u₀} (W : 𝓞 p a u₀) (gu : Gw u₀) (ep : p ≈ᴴ p) (E : W ≈ W) where
  open AddE {W = W} {W′ = W} ep (≈ᴬ-refl a) (≈ᴬ-refl u₀) E gu gu using (add⁰≈)

  mm : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
       ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → Mis m u₀ (ht azero) w (ht (bB R)) (bw R) →
       ∀ m′ (gm′ : Gw m′) (um′ : u₀ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : BW R′ m′) → Mis m′ u₀ (ht azero) w′ (ht (bB R′)) (bw R′) →
       add⁰ W gu R x gx m gm um tm am ⊴ add⁰ W gu R′ y gy m′ gm′ um′ tm′ am′

  mR : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
       ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → Mis m u₀ (ht azero) w (ht (bB R)) (bw R) →
       ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (yv : w′ ⊲ v) (bv : BW R′ v) →
       add⁰ W gu R x gx m gm um tm am ⊴ add W gu R′ y gy v gv uv yv bv
  mR d R R′ gx gy m gm um tm am is v gv uv yv bv =
    rw (mm d R R′ gx gy m gm um tm am is (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ bv) (mx-is gu gv uv (lbu yv) (proj₁ bv)))
    where
    M = mx gu gv uv (lbu yv) (proj₁ bv)

  mLn : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : BW R v) →
        ∀ m′ (gm′ : Gw m′) (um′ : u₀ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : BW R′ m′) → Mis m′ u₀ (ht azero) w′ (ht (bB R′)) (bw R′) →
        add W gu R x gx v gv uv xv bv ⊴ add⁰ W gu R′ y gy m′ gm′ um′ tm′ am′
  mLn d R R′ gx gy v gv uv xv bv m′ gm′ um′ tm′ am′ is′ =
    lw₂ (mm d R R′ gx gy (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ bv) (mx-is gu gv uv (lbu xv) (proj₁ bv)) m′ gm′ um′ tm′ am′ is′)
    where
    M = mx gu gv uv (lbu xv) (proj₁ bv)

  mm2 : ∀ {p₁ b w p₂ b′ w′} {x : 𝓞 p₁ b w} {y : 𝓞 p₂ b′ w′} → x ⊴ y → (R : Rel p₁ b p a) (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : BW R v) →
        ∀ v′ (gv′ : Gw v′) (uv′ : u₀ ⊲ v′) (yv′ : w′ ⊲ v′) (bv′ : BW R′ v′) →
        add W gu R x gx v gv uv xv bv ⊴ add W gu R′ y gy v′ gv′ uv′ yv′ bv′
  mm2 d R R′ gx gy v gv uv xv bv v′ gv′ uv′ yv′ bv′ =
    lw₂ (mR d R R′ gx gy (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ bv) (mx-is gu gv uv (lbu xv) (proj₁ bv)) v′ gv′ uv′ yv′ bv′)
    where
    M = mx gu gv uv (lbu xv) (proj₁ bv)

  mRL : ∀ {p₁ b w p₂ h k w′} {x : 𝓞 p₁ b w} (t : h <ᴴ p) (j : h <ᴴ p₂) (y : Low p₂ j k w′) → x ⊴ outL j y → (R : Rel p₁ b p a) (gx : Gw w) (gy : Gw w′) →
        ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → Mis m u₀ (ht azero) w (ht (bB R)) (bw R) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (yv : w′ ⊲ v) (kv : BW {b = k} {a = a} (lw t) v) →
        add⁰ W gu R x gx m gm um tm am ⊴ addL W gu t j y gy v gv uv yv kv
  mRL t here y d R gx gy m gm um tm am is v gv uv yv kv = mR d R (lw t) gx gy m gm um tm am is v gv uv yv kv
  mRL t (lh n₉) y d R gx gy m gm um tm am is v gv uv yv kv = mR d R (lw t) gx gy m gm um tm am is v gv uv yv kv
  mRL t (tp a₉) y d R gx gy m gm um tm am is v gv uv yv kv = mR d R (lw t) gx gy m gm um tm am is v gv uv yv kv
  mRL t (st j) y d R gx gy m gm um tm am is v gv uv yv kv = mRL t j y d R gx gy m gm um tm am is v gv uv yv kv
  mRL t (ll n₉ j) y d R gx gy m gm um tm am is v gv uv yv kv = mRL t j y d R gx gy m gm um tm am is v gv uv yv kv
  mRL t (tq a₉ j) y d R gx gy m gm um tm am is v gv uv yv kv = mRL t j y d R gx gy m gm um tm am is v gv uv yv kv

  mLL : ∀ {p₁ h k w p₂ b′ w′} {y : 𝓞 p₂ b′ w′} (t : h <ᴴ p) (j : h <ᴴ p₁) (x : Low p₁ j k w) → outL j x ⊴ y → (R′ : Rel p₂ b′ p a) (gx : Gw w) (gy : Gw w′) →
        ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (kv : BW {b = k} {a = a} (lw t) v) →
        ∀ m′ (gm′ : Gw m′) (um′ : u₀ ⊲ m′) (tm′ : w′ ⊲ m′) (am′ : BW R′ m′) → Mis m′ u₀ (ht azero) w′ (ht (bB R′)) (bw R′) →
        addL W gu t j x gx v gv uv xv kv ⊴ add⁰ W gu R′ y gy m′ gm′ um′ tm′ am′
  mLL t here x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLn d (lw t) R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′
  mLL t (lh n₉) x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLn d (lw t) R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′
  mLL t (tp a₉) x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLn d (lw t) R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′
  mLL t (st j) x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLL t j x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′
  mLL t (ll n₉ j) x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLL t j x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′
  mLL t (tq a₉ j) x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′ = mLL t j x d R′ gx gy v gv uv xv kv m′ gm′ um′ tm′ am′ is′

  mm {x = x} {y} (rf e) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = rf (add⁰≈ R R′ x y gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ e)
  mm (s {y = y₀} d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = s (mR d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′)
  mm (l n d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l n (mR d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′)
  mm (fc d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = fc (mR d R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′)
  mm {x = x} (ni {k = k} {r = r} {h = h} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = ni (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (sa P) (h (⊲-tr tm′ q) g (inS (≪S r) z)) g v g (⊲-tr um′ q) C.self (lb0 v , proj₂ am′)) (sym (out-inS (≪S (≪∘ r P)) (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (sa P) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (lb0 v , proj₂ am′)))
  mm {x = x} (ni {k = k} {r = r} {h = h} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = nd (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (lw i) (h (⊲-tr tm′ q) g (inS (≪S r) z)) g v g (⊲-tr um′ q) C.self (bw↑ _ am′ q)) (sym (out-inL i (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (lw i) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (bw↑ _ am′ q)))
  mm {x = x} (nd {k = k} {i = j} {h = h} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = nd (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (sa P) (h (⊲-tr tm′ q) g (inL j z)) g v g (⊲-tr um′ q) C.self (lb0 v , proj₂ am′)) (sym (out-inL j (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (sa P) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (lb0 v , proj₂ am′)))
  mm {x = x} (nd {k = k} {i = j} {h = h} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = nd (λ {v} q g →
    subst (λ z → add⁰ W gu R x gx m gm um tm am ⊴ add W gu (lw i) (h (⊲-tr tm′ q) g (inL j z)) g v g (⊲-tr um′ q) C.self (bw↑ _ am′ q)) (sym (out-inL (<tr j i) (Ω̇at _ k g)))
      (mR (d (⊲-tr tm′ q) g) R (lw i) gx g m gm um tm am is v g (⊲-tr um′ q) C.self (bw↑ _ am′ q)))
  mm (eR {stp = es} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (sa (⊲-tr (C.suc C.self) P)) gx gy m gm um tm am is m′ gm′ um′ tm′ am′
  mm (eR {stp = es} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.suc C.self) am′)
  mm (eR {stp = el n} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (sa (⊲-tr (C.lim n C.self) P)) gx gy m gm um tm am is m′ gm′ um′ tm′ am′
  mm (eR {stp = el n} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ (bw↓ i (C.lim n C.self) am′)
  mm (eL {stp = es} d) (sa P) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (sa (⊲-tr (C.suc C.self) P)) R′ gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′
  mm (eL {stp = es} d) (lw i) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (lw i) R′ gx gy m gm um tm (bw↓ i (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′
  mm (eL {stp = el n} d) (sa P) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (sa (⊲-tr (C.lim n C.self) P)) R′ gx gy m gm um tm am m′ gm′ um′ tm′ am′ is′
  mm (eL {stp = el n} d) (lw i) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d (lw i) R′ gx gy m gm um tm (bw↓ i (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′
  mm (rL {j = j} {e = e} {y = y} d) R (sa P) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mRL j j y d R gx gy m gm um tm am is m′ gm′ um′ tm′ (bwEe j e tm′ (proj₂ am′))
  mm (rL {j = j} {e = e} {y = y} d) R (lw i) gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mRL (<tr j i) j y d R gx gy m gm um tm am is m′ gm′ um′ tm′ (bwTr j i e tm′ am′)
  mm (lL {j = j} {e = e} {x = x} d) (sa P) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLL j j x d R′ gx gy m gm um tm (bwEe j e tm (proj₂ am)) m′ gm′ um′ tm′ am′ is′
  mm (lL {j = j} {e = e} {x = x} d) (lw i) R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLL (<tr j i) j x d R′ gx gy m gm um tm (bwTr j i e tm am) m′ gm′ um′ tm′ am′ is′
  mm (rw {w = w} {g = g} d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mR d R R′ gx g m gm um tm am is m′ gm′ um′ (⊲-tr w tm′) am′
  mm (lw₂ {w = w} {g = g} d) R R′ gx gy m gm um tm am is m′ gm′ um′ tm′ am′ is′ = mLn d R R′ g gy m gm um (⊲-tr w tm) am m′ gm′ um′ tm′ am′ is′
```

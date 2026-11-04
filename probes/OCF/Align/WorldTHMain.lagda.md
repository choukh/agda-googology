# 带高度的世界: 闭包定理

> 不含记号. 结论写在 [WorldTH](WorldTH.lagda.md). **`ψL`, `ψ₀L`: 折叠保第一位置. `ψW`, `ψ₀W`: 折叠保 `WF`. 对一切高度, 一切层, 一切目标, 一步.** `HS-T`: $\psi_0(\Omega_{\Omega\cdot p+a})$ 是 `HS` 序数, 对一切合法的高度 $p$ (`ht` 或顶) 与合法的 $a$; 顶读作 $\Omega^2$. 没有 `Vis`, `Hon`, 不问输出高于下标.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.Free.Level using (HS; hz; hs; hl; _⊑⁰_; _≅_; ≺s; ≺l; ≅→⊑; ≅-refl⁰; z≅; s≅; l≅; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next; next-⊲)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.WorldTHW
open import OCF.Align.WorldTHEq
open import OCF.Align.WorldTHPsi
open import OCF.Align.WorldTHLe
```

## §1 第 0 层的第一位置

```agda
infix 4 _⊴₀_
data _⊴₀_ : Ord₀ → Ord₀ → Set where
  r0 : ∀ {a b} → a ≅ b → a ⊴₀ b
  s0 : ∀ {a b} → a ⊴₀ b → a ⊴₀ FL.suc b
  l0 : ∀ {a f} n → a ⊴₀ f n → a ⊴₀ FL.lim f

⊴₀→⊑⁰ : ∀ {a b} → a ⊴₀ b → a ⊑⁰ b
⊴₀→⊑⁰ (r0 e) = ≅→⊑ e
⊴₀→⊑⁰ (s0 d) c = ≺s (⊴₀→⊑⁰ d c)
⊴₀→⊑⁰ (l0 n d) c = ≺l n (⊴₀→⊑⁰ d c)

Lit₀ : Ord₀ → Set
Lit₀ FL.zero = ⊤
Lit₀ (FL.suc a) = Lit₀ a
Lit₀ (FL.lim f) = (∀ n → f n ⊴₀ f (suc n)) × (∀ n → Lit₀ (f n))
Lit₀ (FL.limᵢ () f)
Lit₀ (FL.up () x)

HS₀ : ∀ a → Lit₀ a → HS a
HS₀ FL.zero u = hz
HS₀ (FL.suc a) u = hs (HS₀ a u)
HS₀ (FL.lim f) (sq , u) = hl (λ n → HS₀ (f n) (u n)) (λ n → ⊴₀→⊑⁰ (sq n))
HS₀ (FL.limᵢ () f) u
HS₀ (FL.up () x) u

z⊴₀ : ∀ y → FL.zero ⊴₀ y
z⊴₀ FL.zero = r0 z≅
z⊴₀ (FL.suc y) = s0 (z⊴₀ y)
z⊴₀ (FL.lim f) = l0 0 (z⊴₀ (f 0))
z⊴₀ (FL.limᵢ () f)
z⊴₀ (FL.up () x)

+fst : ∀ a b → a ⊴₀ a +₀ b
+fst a FL.zero = r0 (≅-refl⁰ a)
+fst a (FL.suc b) = s0 (+fst a b)
+fst a (FL.lim f) = l0 0 (+fst a (f 0))
+fst a (FL.limᵢ () f)
+fst a (FL.up () x)

+⊴ : ∀ c {a b} → a ⊴₀ b → c +₀ a ⊴₀ c +₀ b
+⊴ c (r0 e) = r0 (plus≅ (≅-refl⁰ c) e)
+⊴ c (s0 d) = s0 (+⊴ c d)
+⊴ c (l0 n d) = l0 n (+⊴ c d)

Lit-+ : ∀ a b → Lit₀ a → Lit₀ b → Lit₀ (a +₀ b)
Lit-+ a FL.zero u v = u
Lit-+ a (FL.suc b) u v = Lit-+ a b u v
Lit-+ a (FL.lim f) u (sq , v) = (λ n → +⊴ a (sq n)) , (λ n → Lit-+ a (f n) u (v n))
Lit-+ a (FL.limᵢ () f) u v
Lit-+ a (FL.up () x) u v

rep₀⊴ : ∀ y n → rep₀ y n ⊴₀ rep₀ y (suc n)
rep₀⊴ y zero = z⊴₀ y
rep₀⊴ y (suc m) = +fst (rep₀ y (suc m)) y

Lit-rep : ∀ y → Lit₀ y → ∀ n → Lit₀ (rep₀ y n)
Lit-rep y u zero = tt
Lit-rep y u (suc zero) = u
Lit-rep y u (suc (suc m)) = Lit-+ (rep₀ y (suc m)) y (Lit-rep y u (suc m)) u

em⊴ : ∀ {a b} → a ⊴₀ b → em {one} a ⊴ em {one} b
em⊴ (r0 e) = rf (em≈ (≈ᴬ-refl one) e)
em⊴ (s0 d) = s (em⊴ d)
em⊴ (l0 n d) = l n (em⊴ d)
```

## §2 折叠保第一位置

`M₀`: 第 0 层. `Mᵗ`: 非第 0 层的目标. 都对推导递归.

```agda
module M₀ where
  mm : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
       ∀ m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → Mis m u (ht azero) azero p a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ (ht azero) azero p′ a′ →
       ψ₀⁰ x gu m gm um am ⊴₀ ψ₀⁰ y gu′ m′ gm′ um′ am′

  mR : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
       ∀ m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → Mis m u (ht azero) azero p a →
       ∀ v (gv : Gw v) (uv : u′ ⊲ v) (av : LB p′ a′ v) →
       ψ₀⁰ x gu m gm um am ⊴₀ ψ₀ y gu′ v gv uv av
  mR d gu gu′ m gm um am is v gv uv av = mm d gu gu′ m gm um am is (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M) (mx-is gu′ gv uv (lb0 v) av)
    where
    M = mx gu′ gv uv (lb0 v) av

  mL : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
       ∀ v (gv : Gw v) (uv : u ⊲ v) (av : LB p a v) →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ (ht azero) azero p′ a′ →
       ψ₀ x gu v gv uv av ⊴₀ ψ₀⁰ y gu′ m′ gm′ um′ am′
  mL d gu gu′ v gv uv av m′ gm′ um′ am′ is′ = mm d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M) (mx-is gu gv uv (lb0 v) av) m′ gm′ um′ am′ is′
    where
    M = mx gu gv uv (lb0 v) av

  mRL : ∀ {p a u p′ h k u′} {x : 𝓞 p a u} (j : h <ᴴ p′) (y : Low p′ j k u′) → x ⊴ outL j y → (gu : Gw u) (gu′ : Gw u′) →
        ∀ m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → Mis m u (ht azero) azero p a →
        ∀ v (gv : Gw v) (uv : u′ ⊲ v) (kv : LB h k v) →
        ψ₀⁰ x gu m gm um am ⊴₀ ψ₀L j y gu′ v gv uv kv
  mRL here y d gu gu′ m gm um am is v gv uv kv = mR d gu gu′ m gm um am is v gv uv kv
  mRL (lh n₉) y d gu gu′ m gm um am is v gv uv kv = mR d gu gu′ m gm um am is v gv uv kv
  mRL (tp a₉) y d gu gu′ m gm um am is v gv uv kv = mR d gu gu′ m gm um am is v gv uv kv
  mRL (st j) y d gu gu′ m gm um am is v gv uv kv = mRL j y d gu gu′ m gm um am is v gv uv kv
  mRL (ll n₉ j) y d gu gu′ m gm um am is v gv uv kv = mRL j y d gu gu′ m gm um am is v gv uv kv
  mRL (tq a₉ j) y d gu gu′ m gm um am is v gv uv kv = mRL j y d gu gu′ m gm um am is v gv uv kv

  mLL : ∀ {p h k u p′ a′ u′} {y : 𝓞 p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) → outL j x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
        ∀ v (gv : Gw v) (uv : u ⊲ v) (kv : LB h k v) →
        ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : LB p′ a′ m′) → Mis m′ u′ (ht azero) azero p′ a′ →
        ψ₀L j x gu v gv uv kv ⊴₀ ψ₀⁰ y gu′ m′ gm′ um′ am′
  mLL here x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mL d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (lh n₉) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mL d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (tp a₉) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mL d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (st j) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mLL j x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (ll n₉ j) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mLL j x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (tq a₉ j) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mLL j x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′

  mm {x = x} {y} (rf e) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = r0 (ψ₀⁰Q x y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e)
  mm (s d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 1 (mR d gu gu′ m gm um am is m′ gm′ um′ am′)
  mm (l n d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 n (mR d gu gu′ m gm um am is m′ gm′ um′ am′)
  mm (fc d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 0 (mR d gu gu′ m gm um am is m′ gm′ um′ am′)
  mm (ni d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 0 (mR (d um′ gm′) gu gm′ m gm um am is m′ gm′ C.self am′)
  mm (nd d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 0 (mR (d um′ gm′) gu gm′ m gm um am is m′ gm′ C.self am′)
  mm (eR {stp = es} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mR d gu gu′ m gm um am is m′ gm′ um′ (lbS (C.suc C.self) am′)
  mm (eR {stp = el n} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mR d gu gu′ m gm um am is m′ gm′ um′ (lbS (C.lim n C.self) am′)
  mm (eL {stp = es} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mL d gu gu′ m gm um (lbS (C.suc C.self) am) m′ gm′ um′ am′ is′
  mm (eL {stp = el n} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mL d gu gu′ m gm um (lbS (C.lim n C.self) am) m′ gm′ um′ am′ is′
  mm (rL {j = j} {e = e} {y = y} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mRL j y d gu gu′ m gm um am is m′ gm′ um′ (lbe j e um′ am′)
  mm (lL {j = j} {e = e} {x = x} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mLL j x d gu gu′ m gm um (lbe j e um am) m′ gm′ um′ am′ is′
  mm (rw {w = w} {g = g} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mR d gu g m gm um am is m′ gm′ (⊲-tr w um′) am′
  mm (lw₂ {w = w} {g = g} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mL d g gu′ m gm (⊲-tr w um) am m′ gm′ um′ am′ is′

  tp₀ : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
        ∀ v (gv : Gw v) (uv : u ⊲ v) (av : LB p a v) →
        ∀ v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (av′ : LB p′ a′ v′) →
        ψ₀ x gu v gv uv av ⊴₀ ψ₀ y gu′ v′ gv′ uv′ av′
  tp₀ d gu gu′ v gv uv av v′ gv′ uv′ av′ = mR d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M) (mx-is gu gv uv (lb0 v) av) v′ gv′ uv′ av′
    where
    M = mx gu gv uv (lb0 v) av

open M₀ using () renaming (tp₀ to ψ₀L′)

-- 非第 0 层的目标
tmm : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q t m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q t p′ a′ →
      ψ⁰ q t x gu m gm um tm am ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′

tRm : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
      ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : LB q t v) (av : LB p′ a′ v) →
      ψ⁰ q t x gu m gm um tm am ⊴ ψᵐ q t y gu′ v gv uv tv av
tRm nl d gu gu′ m gm um tm am is v gv uv tv av = rw (tmm nl d gu gu′ m gm um tm am is (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu′ gv uv tv av))
  where
  M = mx gu′ gv uv tv av

tLm : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v) →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q t m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q t p′ a′ →
      ψᵐ q t x gu v gv uv tv av ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tLm nl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = lw₂ (tmm nl d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gv uv tv av) m′ gm′ um′ tm′ am′ is′)
  where
  M = mx gu gv uv tv av

tR : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
     ∀ m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
     ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : LB q t v) (av : LB p′ a′ v) →
     ψ⁰ q t x gu m gm um tm am ⊴ ψ q t y gu′ v gv uv tv av
tR nzs d gu gu′ m gm um tm am is v gv uv tv av = tRm nzs d gu gu′ m gm um tm am is v gv uv tv av
tR nzl d gu gu′ m gm um tm am is v gv uv tv av = tRm nzl d gu gu′ m gm um tm am is v gv uv tv av
tR ns d gu gu′ m gm um tm am is v gv uv tv av = tRm ns d gu gu′ m gm um tm am is v gv uv tv av
tR nh d gu gu′ m gm um tm am is v gv uv tv av = tRm nh d gu gu′ m gm um tm am is v gv uv tv av
tR nt d gu gu′ m gm um tm am is v gv uv tv av = tRm nt d gu gu′ m gm um tm am is v gv uv tv av

tL : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
     ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v) →
     ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q t m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q t p′ a′ →
     ψ q t x gu v gv uv tv av ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tL nzs d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm nzs d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL nzl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm nzl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL ns d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm ns d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL nh d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm nh d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL nt d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm nt d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′

tRL : ∀ {p a u p′ h k u′ q t} (nl : NL q t) {x : 𝓞 p a u} (j : h <ᴴ p′) (y : Low p′ j k u′) → x ⊴ outL j y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Mis m u q t p a →
      ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : LB q t v) (kv : LB h k v) →
      ψ⁰ q t x gu m gm um tm am ⊴ ψL q t j y gu′ v gv uv tv kv
tRL nl here y d gu gu′ m gm um tm am is v gv uv tv kv = tR nl d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (lh n₉) y d gu gu′ m gm um tm am is v gv uv tv kv = tR nl d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (tp a₉) y d gu gu′ m gm um tm am is v gv uv tv kv = tR nl d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (st j) y d gu gu′ m gm um tm am is v gv uv tv kv = tRL nl j y d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (ll n₉ j) y d gu gu′ m gm um tm am is v gv uv tv kv = tRL nl j y d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (tq a₉ j) y d gu gu′ m gm um tm am is v gv uv tv kv = tRL nl j y d gu gu′ m gm um tm am is v gv uv tv kv

tLL : ∀ {p h k u p′ a′ u′ q t} (nl : NL q t) {y : 𝓞 p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) → outL j x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (kv : LB h k v) →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : LB q t m′) (am′ : LB p′ a′ m′) → Mis m′ u′ q t p′ a′ →
      ψL q t j x gu v gv uv tv kv ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tLL nl here x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (lh n₉) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (tp a₉) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (st j) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (ll n₉ j) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (tq a₉ j) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′

tmm nl {x} {y} (rf e) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = rf (ψ⁰Q nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ (hrefl (ho→ht (proj₂ tm)) , ≈ᴬ-refl _) e)
tmm nl (s d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l 1 (tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm nl (l n d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l n (tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm nl (fc d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = fc (tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm {p′ = p′} {q = q} {t} nl {x} (ni {k = k} {r = r} {h = h} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ with hcmp p′ q (proj₂ am′) (proj₂ tm′) (lgw gm′)
... | hlt i b = nd (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inS (≪S r) z)) g v g C.self (lb↑ tm′ w) (lb↑ am′ w)) (sym (out-inL i (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (lb↑ tm′ w) (lb↑ am′ w)))
... | hgt _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
... | heq refl with cmpN (≪∘ r (proj₁ am′)) (proj₁ tm′) (lgw gm′)
...   | keep s′ = ni (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inS (≪S r) z)) g v g C.self (lb↑ tm′ w) (lb↑ am′ w)) (sym (out-inS (≪S s′) (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (lb↑ tm′ w) (lb↑ am′ w)))
...   | rise _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
tmm {q = q} {t} nl {x} (nd {h₀ = h₀} {k = k} {i = j} {r = r} {h = h} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ with hcmp h₀ q (hmm j (proj₂ r) um′ (proj₂ am′)) (proj₂ tm′) (lgw gm′)
... | hlt i b = nd (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inL j z)) g v g C.self (lb↑ tm′ w) (lb↑ am′ w)) (sym (out-inL i (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (lb↑ tm′ w) (lb↑ am′ w)))
... | hgt _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
... | heq refl with cmpN (≪∘ (proj₁ r) um′) (proj₁ tm′) (lgw gm′)
...   | keep s′ = ni (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inL j z)) g v g C.self (lb↑ tm′ w) (lb↑ am′ w)) (sym (out-inS (≪S s′) (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (lb↑ tm′ w) (lb↑ am′ w)))
...   | rise _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
tmm nl (eR {stp = es} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.suc C.self) am′)
tmm nl (eR {stp = el n} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbS (C.lim n C.self) am′)
tmm nl (eL {stp = es} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ m gm um tm (lbS (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′
tmm nl (eL {stp = el n} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ m gm um tm (lbS (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′
tmm nl (rL {j = j} {e = e} {y = y} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tRL nl j y d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (lbe j e um′ am′)
tmm nl (lL {j = j} {e = e} {x = x} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ m gm um tm (lbe j e um am) m′ gm′ um′ tm′ am′ is′
tmm nl (rw {w = w} {g = g} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR nl d gu g m gm um tm am is m′ gm′ (⊲-tr w um′) tm′ am′
tmm nl (lw₂ {w = w} {g = g} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL nl d g gu′ m gm (⊲-tr w um) tm am m′ gm′ um′ tm′ am′ is′

-- 总的
ψL′ : ∀ {p a u p′ a′ u′} q t {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v) →
      ∀ v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : LB q t v′) (av′ : LB p′ a′ v′) →
      ψ q t x gu v gv uv tv av ⊴ ψ q t y gu′ v′ gv′ uv′ tv′ av′
ψL′ (ht azero) azero d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ = lw₂ (rw (em⊴ (ψ₀L′ d gu gu′ v gv uv av v′ gv′ uv′ av′)))
ψL′ (ht azero) (asuc t) d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ = lw₂ (tR nzs d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gv uv tv av) v′ gv′ uv′ tv′ av′)
  where
  M = mx gu gv uv tv av
ψL′ (ht azero) (alim f) d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ = lw₂ (tR nzl d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gv uv tv av) v′ gv′ uv′ tv′ av′)
  where
  M = mx gu gv uv tv av
ψL′ (ht (asuc q)) t d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ = lw₂ (tR ns d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gv uv tv av) v′ gv′ uv′ tv′ av′)
  where
  M = mx gu gv uv tv av
ψL′ (ht (alim f)) t d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ = lw₂ (tR nh d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gv uv tv av) v′ gv′ uv′ tv′ av′)
  where
  M = mx gu gv uv tv av
ψL′ (tφ f) t d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ = lw₂ (tR nt d gu gu′ (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) (mx-is gu gv uv tv av) v′ gv′ uv′ tv′ av′)
  where
  M = mx gu gv uv tv av

-- Ω_k 是 ψ_k 的任何值的第一位置
Ωfst : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → Ω̇at q t gm ⊴ ψ q t x gu m gm um tm am
Ωfst (ht azero) azero x gu m gm um tm am =
  lw₂ (rw (em⊴ (M₀.mR (z⊴ {p₀ = ht azero} {a₀ = azero} {u₀ = m} x) gm gu m gm C.self (lb0 m) (iu refl) m gm um am)))
Ωfst (ht azero) (asuc t) x gu m gm um tm am =
  tR nzs {x = o0 {ht azero} {azero} {Vs (ht azero) azero} {Low (ht azero)}} (z⊴ x) gm gu m gm C.self tm (lb0 m) (iu refl) m gm um tm am
Ωfst (ht azero) (alim f) x gu m gm um tm am =
  tR nzl {x = o0 {ht azero} {azero} {Vs (ht azero) azero} {Low (ht azero)}} (z⊴ x) gm gu m gm C.self tm (lb0 m) (iu refl) m gm um tm am
Ωfst (ht (asuc q)) t x gu m gm um tm am =
  tR ns {x = o0 {ht azero} {azero} {Vs (ht azero) azero} {Low (ht azero)}} (z⊴ x) gm gu m gm C.self tm (lb0 m) (iu refl) m gm um tm am
Ωfst (ht (alim f)) t x gu m gm um tm am =
  tR nh {x = o0 {ht azero} {azero} {Vs (ht azero) azero} {Low (ht azero)}} (z⊴ x) gm gu m gm C.self tm (lb0 m) (iu refl) m gm um tm am
Ωfst (tφ f) t x gu m gm um tm am =
  tR nt {x = o0 {ht azero} {azero} {Vs (ht azero) azero} {Low (ht azero)}} (z⊴ x) gm gu m gm C.self tm (lb0 m) (iu refl) m gm um tm am
```

## §2′ 高度的合法性

```agda
Lh : Hg → Set
Lh (ht a) = Lg a
Lh (tφ f) = f ≡ ht

lhO : ∀ {q m} → HO q m → Lg m → Lh q
lhO {ht a} b w = lg⊲ b w
lhO {tφ f} b w = b

lh→ht : ∀ {p} → Lh p → HT p
lh→ht {ht a} _ = tt
lh→ht {tφ f} e = e

rfB : ∀ {q t m} → LB q t m → (q ≈ᴴ q) × (t ≈ᴬ t)
rfB {t = t} b = hrefl (ho→ht (proj₂ b)) , ≈ᴬ-refl t
```

## §3 `WF`

```agda
WF : ∀ {p a u} → 𝓞 p a u → Set
WFS : ∀ {p a b} (R : Strict b a) {u} → Vs p a R u → Set
WFC : ∀ {p a b} (P : b ⊲ a) {u} → Vc p a P u → Set
WFL : ∀ {p h k u} (j : h <ᴴ p) → Low p j k u → Set

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
WFL here x = WF x
WFL (lh n₉) x = WF x
WFL (tp a₉) x = WF x
WFL (st j) x = WFL j x
WFL (ll n₉ j) x = WFL j x
WFL (tq a₉ j) x = WFL j x

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

L→W : ∀ {p h k u} (j : h <ᴴ p) (x : Low p j k u) → WFL j x → WF (outL j x)
L→W here x w = w
L→W (lh n₉) x w = w
L→W (tp a₉) x w = w
L→W (st j) x w = L→W j x w
L→W (ll n₉ j) x w = L→W j x w
L→W (tq a₉ j) x w = L→W j x w

W→L : ∀ {p h k u} (j : h <ᴴ p) (x : Low p j k u) → WF (outL j x) → WFL j x
W→L here x w = w
W→L (lh n₉) x w = w
W→L (tp a₉) x w = w
W→L (st j) x w = W→L j x w
W→L (ll n₉ j) x w = W→L j x w
W→L (tq a₉ j) x w = W→L j x w

-- 分支写成 O k 的值
hMi : ∀ {p a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} → WF (oi r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) {z z′ : 𝓞 p k v} → z ⊴ z′ → h q g (inS (≪S r) z) ⊴ h q g (inS (≪S r) z′)
hMi {r = r} (mon , _) q g {z} {z′} d = mon q g _ _ (subst₂ _⊴_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z′)) d)

hWi : ∀ {p a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} → WF (oi r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) (z : 𝓞 p k v) → z ≈ z → WF z → WF (h q g (inS (≪S r) z))
hWi {r = r} (_ , ww) q g z e w = ww q g _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z)) e) (W→S (≪S r) _ (subst WF (sym (out-inS (≪S r) z)) w))

hMd : ∀ {p a u h₀ k} {i : h₀ <ᴴ p} {r : (k ≪ u) × Hb p h₀ u} {h : ∀ {v} → u ⊲ v → Gw v → Low p i k v → 𝓞 p a v} → WF (od i k r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) {z z′ : 𝓞 h₀ k v} → z ⊴ z′ → h q g (inL i z) ⊴ h q g (inL i z′)
hMd {i = i} (mon , _) q g {z} {z′} d = mon q g _ _ (subst₂ _⊴_ (sym (out-inL i z)) (sym (out-inL i z′)) d)

hWd : ∀ {p a u h₀ k} {i : h₀ <ᴴ p} {r : (k ≪ u) × Hb p h₀ u} {h : ∀ {v} → u ⊲ v → Gw v → Low p i k v → 𝓞 p a v} → WF (od i k r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) (z : 𝓞 h₀ k v) → z ≈ z → WF z → WF (h q g (inL i z))
hWd {i = i} (_ , ww) q g z e w = ww q g _ (subst₂ _≈_ (sym (out-inL i z)) (sym (out-inL i z)) e) (W→L i _ (subst WF (sym (out-inL i z)) w))

-- 顶行: f 的值只在结构递归里用, 其余由 f ≡ ht 给
lhf : ∀ {f v} → f ≡ ht → Gw v → Lh (f v)
lhf refl g = lgw g

lhz : ∀ {f} → f ≡ ht → Lh (f azero)
lhz refl = tt

ocW : ∀ {f} → (e : f ≡ ht) → WF (Ω̇ (f azero) azero) → (∀ {v} → one ⊲ v → Gw v → WF (Ω̇ (f v) azero)) → WF (Ω̇ (tφ f) azero)
ocW refl w₀ wv =
  (λ {v} q g → lL (rL (rw (Ωh⊴ (z⊲ v))))) , (λ q q′ g g′ vv → lL (rL (lw₂ (rw (Ωh⊴ vv))))) , w₀ , wv

ΩW : ∀ p a → Lh p → Lg a → WF (Ω̇ p a)
ΩW p (asuc c) lp w = (λ q g y y′ d → eL {stp = es} (eR {stp = es} d)) , (λ q g y _ u → u)
ΩW p (alim f) lp (sq , w) = (λ n → eL {stp = el n} (eR {stp = el (suc n)} (Ω⊴ p (lh→ht lp) (sq n)))) , (λ n → ΩW p (f n) lp (w n))
ΩW (ht azero) azero lp w = tt
ΩW (ht (asuc p)) azero lp w =
  (λ q g → lL (rL (rw (Ω⊴ (ht p) tt (pos g))))) , (λ q q′ g g′ vv → lL (rL (lw₂ (rw (Ω⊴ (ht p) tt vv))))) , ΩW (ht p) one lp tt , (λ {v} q g → ΩW (ht p) v lp (lgw g))
ΩW (ht (alim f)) azero (sq , lp) w = (λ n → lL (rL (Ωh⊴ (sq n)))) , (λ n → ΩW (ht (f n)) azero (lp n) tt)
ΩW (tφ f) azero e w = ocW e (ΩW (f azero) azero (lhz e) tt) (λ {v} q g → ΩW (f v) azero (lhf e g) tt)

ΩWB : ∀ {q t m} → LB q t m → Gw m → WF (Ω̇ q t)
ΩWB {q} {t} b g = ΩW q t (lhO (proj₂ b) (lgw g)) (lg⊲ (proj₁ b) (lgw g))

-- 加法保 WF
module AddW {p a u₀} (W : 𝓞 p a u₀) (gu : Gw u₀) (ep : p ≈ᴴ p) (E : W ≈ W) (wW : WF W) where
  open AddM W gu ep E using (mm2)

  aw : ∀ {p₁ b w} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → WF x → ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : BW R v) → WF (add W gu R x gx v gv uv xv bv)
  a⁰ : ∀ {p₁ b w} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → WF x → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : BW R m) → WF (add⁰ W gu R x gx m gm um tm am)
  aL : ∀ {p₁ h k w} (t : h <ᴴ p) (j : h <ᴴ p₁) (x : Low p₁ j k w) (gx : Gw w) → WFL j x → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : BW {b = k} {a = a} (lw t) m) → WF (addL W gu t j x gx m gm um tm km)

  aw R x gx wx v gv uv xv bv = a⁰ R x gx wx (Mx.m M) (Mx.gm M) (Mx.um M) (proj₁ (Mx.tm M)) (Mx.am M , proj₂ bv)
    where
    M = mx gu gv uv (lbu xv) (proj₁ bv)

  a⁰ R o0 gx wx m gm um tm am = wW
  a⁰ R (os x) gx wx m gm um tm am = aw R x gx wx m gm um tm am
  a⁰ R (ol F) gx (sq , u) m gm um tm am =
    (λ n → mm2 (sq n) R R gx gx m gm um tm am m gm um tm am) , (λ n → aw R (F n) gx (u n) m gm um tm am)
  a⁰ (sa P) (oi r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMi {r = r} wx (⊲-tr tm q) g d) (sa P) (sa P) g g v g (⊲-tr um q) C.self (lb0 v , proj₂ am) v g (⊲-tr um q) C.self (lb0 v , proj₂ am)) ,
    (λ {v} q g y py uy → aw (sa P) (h (⊲-tr tm q) g _) g (hWi {r = r} wx (⊲-tr tm q) g _ py (S→W _ y uy)) v g (⊲-tr um q) C.self (lb0 v , proj₂ am))
  a⁰ (lw i) (oi r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMi {r = r} wx (⊲-tr tm q) g d) (lw i) (lw i) g g v g (⊲-tr um q) C.self (bw↑ _ am q) v g (⊲-tr um q) C.self (bw↑ _ am q)) ,
    (λ {v} q g y py uy → aw (lw i) (h (⊲-tr tm q) g _) g (hWi {r = r} wx (⊲-tr tm q) g _ py (L→W i y uy)) v g (⊲-tr um q) C.self (bw↑ _ am q))
  a⁰ (sa P) (od j k r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMd {i = j} {r = r} wx (⊲-tr tm q) g d) (sa P) (sa P) g g v g (⊲-tr um q) C.self (lb0 v , proj₂ am) v g (⊲-tr um q) C.self (lb0 v , proj₂ am)) ,
    (λ {v} q g y py uy → aw (sa P) (h (⊲-tr tm q) g _) g (hWd {i = j} {r = r} wx (⊲-tr tm q) g _ py (L→W j y uy)) v g (⊲-tr um q) C.self (lb0 v , proj₂ am))
  a⁰ (lw i) (od j k r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMd {i = j} {r = r} wx (⊲-tr tm q) g d) (lw i) (lw i) g g v g (⊲-tr um q) C.self (bw↑ _ am q) v g (⊲-tr um q) C.self (bw↑ _ am q)) ,
    (λ {v} q g y py uy → aw (lw i) (h (⊲-tr tm q) g _) g (hWd {i = j} {r = r} wx (⊲-tr tm q) g _ py (L→W (<tr j i) y uy)) v g (⊲-tr um q) C.self (bw↑ _ am q))
  a⁰ R (oc x h) gx (fi , dr , wx , wh) m gm um tm am =
    (λ {v} q g → mm2 (fi (⊲-tr tm q) g) R R gx g m gm um tm am v g (⊲-tr um q) C.self (bw↑ _ am q)) ,
    (λ {v} {v′} q q′ g g′ p₁ → mm2 (dr (⊲-tr tm q) (⊲-tr tm q′) g g′ p₁) R R g g′ v g (⊲-tr um q) C.self (bw↑ _ am q) v′ g′ (⊲-tr um q′) C.self (bw↑ _ am q′)) ,
    aw R x gx wx m gm um tm am ,
    (λ {v} q g → aw R (h (⊲-tr tm q) g) g (wh (⊲-tr tm q) g) v g (⊲-tr um q) C.self (bw↑ _ am q))
  a⁰ (sa P) (oe es x) gx wx m gm um tm am = aw (sa (⊲-tr (C.suc C.self) P)) x gx wx m gm um tm am
  a⁰ (lw i) (oe es x) gx wx m gm um tm am = aw (lw i) x gx wx m gm um tm (bw↓ i (C.suc C.self) am)
  a⁰ (sa P) (oe (el n) x) gx wx m gm um tm am = aw (sa (⊲-tr (C.lim n C.self) P)) x gx wx m gm um tm am
  a⁰ (lw i) (oe (el n) x) gx wx m gm um tm am = aw (lw i) x gx wx m gm um tm (bw↓ i (C.lim n C.self) am)
  a⁰ (sa P) (oL j k e x) gx wx m gm um tm am = aL j j x gx wx m gm um tm (bwEe j e tm (proj₂ am))
  a⁰ (lw i) (oL j k e x) gx wx m gm um tm am = aL (<tr j i) j x gx wx m gm um tm (bwTr j i e tm am)
  a⁰ R (ow w g′ x) gx wx m gm um tm am = aw R x g′ wx m gm um (⊲-tr w tm) am

  aL t here x gx wx m gm um tm km = aw (lw t) x gx wx m gm um tm km
  aL t (lh n₉) x gx wx m gm um tm km = aw (lw t) x gx wx m gm um tm km
  aL t (tp a₉) x gx wx m gm um tm km = aw (lw t) x gx wx m gm um tm km
  aL t (st j) x gx wx m gm um tm km = aL t j x gx wx m gm um tm km
  aL t (ll n₉ j) x gx wx m gm um tm km = aL t j x gx wx m gm um tm km
  aL t (tq a₉ j) x gx wx m gm um tm km = aL t j x gx wx m gm um tm km

rep⊴ : ∀ {q t u} {y : 𝓞 q t u} (H : HT q) (e : y ≈ y) (g : Gw u) → ∀ n → rep H y g n ⊴ rep H y g (suc n)
rep⊴ {y = y} H e g zero = z⊴ y
rep⊴ {t = t} {u} {y} H e g (suc m) = AddF.add⊴ (rep H y g (suc m)) g (rf (rep≈ H H (hrefl H) (≈ᴬ-refl t) (≈ᴬ-refl u) e g g (suc m))) (sa C.self) y g u g C.self C.self (lb0 u , H)

repW : ∀ {q t u} {y : 𝓞 q t u} (H : HT q) (e : y ≈ y) (g : Gw u) → WF y → ∀ n → WF (rep H y g n)
repW H e g w zero = tt
repW H e g w (suc zero) = w
repW {t = t} {u} {y} H e g w (suc (suc m)) =
  AddW.aw (rep H y g (suc m)) g (hrefl H) (rep≈ H H (hrefl H) (≈ᴬ-refl t) (≈ᴬ-refl u) e g g (suc m)) (repW H e g w (suc m)) (sa C.self) y g w u g C.self C.self (lb0 u , H)

emW : ∀ a → Lit₀ a → WF (em {one} a)
emW FL.zero u = tt
emW (FL.suc a) u = emW a u
emW (FL.lim f) (sq , u) = (λ n → em⊴ (sq n)) , (λ n → emW (f n) (u n))
emW (FL.limᵢ () f) u
emW (FL.up () x) u
```

## §4 闭包定理

对项递归. 上升时链 $z_n$ 的 `WF`, 相邻的 `⊴` 都是这条定理自己. **与高度, 阶段无关.**

```agda
ψW  : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v) → x ≈ x → WF x → WF (ψ q t x gu v gv uv tv av)
ψWm : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : LB q t v) (av : LB p a v) → x ≈ x → WF x → WF (ψᵐ q t x gu v gv uv tv av)
ψW⁰ : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (am : LB p a m) → x ≈ x → WF x → WF (ψ⁰ q t x gu m gm um tm am)
ψWL : ∀ {p h k u} q t (j : h <ᴴ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : LB q t m) (km : LB h k m) → outL j x ≈ outL j x → WFL j x → WF (ψL q t j x gu m gm um tm km)
ψ₀W  : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : LB p a v) → x ≈ x → WF x → Lit₀ (ψ₀ x gu v gv uv av)
ψ₀W⁰ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : LB p a m) → x ≈ x → WF x → Lit₀ (ψ₀⁰ x gu m gm um am)
ψ₀WL : ∀ {p h k u} (j : h <ᴴ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (km : LB h k m) → outL j x ≈ outL j x → WFL j x → Lit₀ (ψ₀L j x gu m gm um km)

ψW (ht azero) azero x gu v gv uv tv av e w = emW _ (ψ₀W x gu v gv uv av e w)
ψW (ht azero) (asuc t) x gu v gv uv tv av e w = ψWm (ht azero) (asuc t) x gu v gv uv tv av e w
ψW (ht azero) (alim f) x gu v gv uv tv av e w = ψWm (ht azero) (alim f) x gu v gv uv tv av e w
ψW (ht (asuc q)) t x gu v gv uv tv av e w = ψWm (ht (asuc q)) t x gu v gv uv tv av e w
ψW (ht (alim f)) t x gu v gv uv tv av e w = ψWm (ht (alim f)) t x gu v gv uv tv av e w
ψW (tφ f) t x gu v gv uv tv av e w = ψWm (tφ f) t x gu v gv uv tv av e w

ψWm q t x gu v gv uv tv av e w = ψW⁰ q t x gu (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.tm M) (Mx.am M) e w
  where
  M = mx gu gv uv tv av

ψW⁰ q t o0 gu m gm um tm am e w = ΩWB tm gm
ψW⁰ q t (os x) gu m gm um tm am (_ , _ , _ , e) w =
  (λ n → rep⊴ (ho→ht (proj₂ tm)) (ψQ x x gu gu m gm um tm am m gm um tm am (rfB tm) e) gm n) ,
  (λ n → repW (ho→ht (proj₂ tm)) (ψQ x x gu gu m gm um tm am m gm um tm am (rfB tm) e) gm (ψW q t x gu m gm um tm am e w) n)
ψW⁰ q t (ol F) gu m gm um tm am e (sq , u) =
  (λ n → ψL′ q t (sq n) gu gu m gm um tm am m gm um tm am) , (λ n → ψW q t (F n) gu m gm um tm am (e n) (u n))
ψW⁰ {p} {a} q t (oi {k = k} r f) gu m gm um tm am (_ , _ , _ , _ , N) w with hcmp p q (proj₂ am) (proj₂ tm) (lgw gm)
... | hlt i b =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMi {r = r} w (⊲-tr um w₁) g d) g g v g C.self (lb↑ tm w₁) (lb↑ am w₁) v g C.self (lb↑ tm w₁) (lb↑ am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (lb↑ tm w₁) (lb↑ am w₁)
      (nI {r = r} {r} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWi {r = r} w (⊲-tr um w₁) g _ py (L→W i y uy)))
... | hgt _ =
  (λ n → ψL′ q t (hMi {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (proj₁ (rfB (lb≪ r am))) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (lb≪ r am) am m gm C.self (lb≪ r am) am (rfB (lb≪ r am)) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWB (lb≪ r am) gm
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (lb≪ r am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (lb≪ r am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (lb≪ r am) am m gm C.self (lb≪ r am) am
... | heq refl with cmpN (≪∘ r (proj₁ am)) (proj₁ tm) (lgw gm)
...   | keep s′ =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMi {r = r} w (⊲-tr um w₁) g d) g g v g C.self (lb↑ tm w₁) (lb↑ am w₁) v g C.self (lb↑ tm w₁) (lb↑ am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (lb↑ tm w₁) (lb↑ am w₁)
      (nI {r = r} {r} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWi {r = r} w (⊲-tr um w₁) g _ py (S→W (≪S s′) y uy)))
...   | rise _ =
  (λ n → ψL′ q t (hMi {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (proj₁ (rfB (lb≪ r am))) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (lb≪ r am) am m gm C.self (lb≪ r am) am (rfB (lb≪ r am)) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWB (lb≪ r am) gm
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (lb≪ r am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (lb≪ r am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (lb≪ r am) am m gm C.self (lb≪ r am) am
ψW⁰ q t (od {h = h₀} j k r f) gu m gm um tm am (_ , _ , _ , _ , _ , N) w with hcmp h₀ q (hmm j (proj₂ r) um (proj₂ am)) (proj₂ tm) (lgw gm)
... | hlt i b =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMd {i = j} {r = r} w (⊲-tr um w₁) g d) g g v g C.self (lb↑ tm w₁) (lb↑ am w₁) v g C.self (lb↑ tm w₁) (lb↑ am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (lb↑ tm w₁) (lb↑ am w₁)
      (nD {j = j} {j} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWd {i = j} {r = r} w (⊲-tr um w₁) g _ py (L→W i y uy)))
... | hgt _ =
  (λ n → ψL′ q t (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (proj₁ (rfB (lbd j r um am))) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (lbd j r um am) am m gm C.self (lbd j r um am) am (rfB (lbd j r um am)) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWB (lbd j r um am) gm
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (lbd j r um am) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (lbd j r um am) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (lbd j r um am) am m gm C.self (lbd j r um am) am
... | heq refl with cmpN (≪∘ (proj₁ r) um) (proj₁ tm) (lgw gm)
...   | keep s′ =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMd {i = j} {r = r} w (⊲-tr um w₁) g d) g g v g C.self (lb↑ tm w₁) (lb↑ am w₁) v g C.self (lb↑ tm w₁) (lb↑ am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (lb↑ tm w₁) (lb↑ am w₁)
      (nD {j = j} {j} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWd {i = j} {r = r} w (⊲-tr um w₁) g _ py (S→W (≪S s′) y uy)))
...   | rise _ =
  (λ n → ψL′ q t (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (proj₁ (rfB (lbd j r um am))) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (lbd j r um am) am m gm C.self (lbd j r um am) am (rfB (lbd j r um am)) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWB (lbd j r um am) gm
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (lbd j r um am) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (lbd j r um am) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (lbd j r um am) am m gm C.self (lbd j r um am) am
ψW⁰ q t (oc x f) gu m gm um tm am (_ , _ , _ , ex , N) (fi , dr , wx , wf) =
  (λ {v} w₁ g → ψL′ q t (fi (⊲-tr um w₁) g) gu g m gm um tm am v g C.self (lb↑ tm w₁) (lb↑ am w₁)) ,
  (λ {v} {v′} w₁ w₂ g g′ p₁ → ψL′ q t (dr (⊲-tr um w₁) (⊲-tr um w₂) g g′ p₁) g g′ v g C.self (lb↑ tm w₁) (lb↑ am w₁) v′ g′ C.self (lb↑ tm w₂) (lb↑ am w₂)) ,
  ψW q t x gu m gm um tm am ex wx ,
  (λ {v} w₁ g → ψW q t (f (⊲-tr um w₁) g) g v g C.self (lb↑ tm w₁) (lb↑ am w₁) (N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v)) (wf (⊲-tr um w₁) g))
ψW⁰ q t (oe es x) gu m gm um tm am e w = ψW q t x gu m gm um tm (lbS (C.suc C.self) am) (≈oe⁻ {R = ss C.self} x es x e) w
ψW⁰ q t (oe (el n) x) gu m gm um tm am e w = ψW q t x gu m gm um tm (lbS (C.lim n C.self) am) (≈oe⁻ {R = sl n C.self} x (el n) x e) w
ψW⁰ q t (oL j k e₁ x) gu m gm um tm am e w = ψWL q t j x gu m gm um tm (lbe j e₁ um am) (≈oL⁻ (outL j x) j e₁ x (Ll→ j x e)) w
ψW⁰ q t (ow p g′ x) gu m gm um tm am e w = ψW q t x g′ m gm (⊲-tr p um) tm am (≈ow⁻ x p g′ x e) w

ψWL q t here x gu m gm um tm km e w = ψW q t x gu m gm um tm km e w
ψWL q t (lh n₉) x gu m gm um tm km e w = ψW q t x gu m gm um tm km e w
ψWL q t (tp a₉) x gu m gm um tm km e w = ψW q t x gu m gm um tm km e w
ψWL q t (st j) x gu m gm um tm km e w = ψWL q t j x gu m gm um tm km e w
ψWL q t (ll n₉ j) x gu m gm um tm km e w = ψWL q t j x gu m gm um tm km e w
ψWL q t (tq a₉ j) x gu m gm um tm km e w = ψWL q t j x gu m gm um tm km e w

ψ₀W x gu v gv uv av e w = ψ₀W⁰ x gu (Mx.m M) (Mx.gm M) (Mx.um M) (Mx.am M) e w
  where
  M = mx gu gv uv (lb0 v) av

ψ₀W⁰ o0 gu m gm um am e w = tt
ψ₀W⁰ (os x) gu m gm um am (_ , _ , _ , e) w =
  rep₀⊴ (ψ₀ x gu m gm um am) , Lit-rep (ψ₀ x gu m gm um am) (ψ₀W x gu m gm um am e w)
ψ₀W⁰ (ol F) gu m gm um am e (sq , u) =
  (λ n → ψ₀L′ (sq n) gu gu m gm um am m gm um am) , (λ n → ψ₀W (F n) gu m gm um am (e n) (u n))
ψ₀W⁰ {p} {a} (oi {k = k} r f) gu m gm um am (_ , _ , _ , _ , N) w =
  (λ n → ψ₀L′ (hMi {r = r} w um gm (zS n)) gm gm m gm C.self am m gm C.self am) ,
  (λ n → ψ₀W (f um gm _) gm m gm C.self am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (proj₁ (rfB (lb≪ r am))) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (lb≪ r am) am m gm C.self (lb≪ r am) am (rfB (lb≪ r am)) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWB (lb≪ r am) gm
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (lb≪ r am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (lb≪ r am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (lb≪ r am) am m gm C.self (lb≪ r am) am
ψ₀W⁰ (od {h = h₀} j k r f) gu m gm um am (_ , _ , _ , _ , _ , N) w =
  (λ n → ψ₀L′ (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self am m gm C.self am) ,
  (λ n → ψ₀W (f um gm _) gm m gm C.self am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (proj₁ (rfB (lbd j r um am))) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (lbd j r um am) am m gm C.self (lbd j r um am) am (rfB (lbd j r um am)) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWB (lbd j r um am) gm
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (lbd j r um am) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (lbd j r um am) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (lbd j r um am) am m gm C.self (lbd j r um am) am
ψ₀W⁰ (oc x f) gu m gm um am (_ , _ , _ , ex , N) (fi , dr , wx , wf) = sq , li
  where
  val : Ix m → Ord₀
  val i = ψ₀ (f (⊲-tr um (Ix.up i)) (Ix.gη i)) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (lb↑ am (Ix.up i))
  y₀ : Ord₀
  y₀ = ψ₀ x gu m gm um am
  sq : ∀ n → yss gm y₀ val n ⊴₀ yss gm y₀ val (suc n)
  sq zero = ψ₀L′ (fi (⊲-tr um (Ix.up (ixs gm y₀ val 0))) (Ix.gη (ixs gm y₀ val 0))) gu _ m gm um am _ _ C.self _
  sq (suc n) = ψ₀L′ (dr (⊲-tr um (Ix.up (ixs gm y₀ val n))) (⊲-tr um (Ix.up (ixs gm y₀ val (suc n)))) _ _ (next-⊲ (Ix.η (ixs gm y₀ val n)) (val (ixs gm y₀ val n)))) _ _ _ _ C.self _ _ _ C.self _
  li : ∀ n → Lit₀ (yss gm y₀ val n)
  li zero = ψ₀W x gu m gm um am ex wx
  li (suc n) = ψ₀W (f _ _) _ _ _ C.self _ (N _ _ _ _ (≈ᴬ-refl _)) (wf _ _)
ψ₀W⁰ (oe es x) gu m gm um am e w = ψ₀W x gu m gm um (lbS (C.suc C.self) am) (≈oe⁻ {R = ss C.self} x es x e) w
ψ₀W⁰ (oe (el n) x) gu m gm um am e w = ψ₀W x gu m gm um (lbS (C.lim n C.self) am) (≈oe⁻ {R = sl n C.self} x (el n) x e) w
ψ₀W⁰ (oL j k e₁ x) gu m gm um am e w = ψ₀WL j x gu m gm um (lbe j e₁ um am) (≈oL⁻ (outL j x) j e₁ x (Ll→ j x e)) w
ψ₀W⁰ (ow p g′ x) gu m gm um am e w = ψ₀W x g′ m gm (⊲-tr p um) am (≈ow⁻ x p g′ x e) w

ψ₀WL here x gu m gm um km e w = ψ₀W x gu m gm um km e w
ψ₀WL (lh n₉) x gu m gm um km e w = ψ₀W x gu m gm um km e w
ψ₀WL (tp a₉) x gu m gm um km e w = ψ₀W x gu m gm um km e w
ψ₀WL (st j) x gu m gm um km e w = ψ₀WL j x gu m gm um km e w
ψ₀WL (ll n₉ j) x gu m gm um km e w = ψ₀WL j x gu m gm um km e w
ψ₀WL (tq a₉ j) x gu m gm um km e w = ψ₀WL j x gu m gm um km e w
```

## §5 $\psi_0(\Omega_{\Omega\cdot p+a})$, $\psi_0(\Omega_{\Omega^2+a})$

**定理.** 对一切合法的高度 $p$ (含顶) 与字面合法的 $a$, `Tψ` 是 `HS` 序数. $a$ 的字面第一位置给 `⊑⁰`.

```agda
HS-T : ∀ p a u₀ (g : Gw u₀) (e : LB p a u₀) → HS (Tψ p a u₀ g e)
HS-T p a u₀ g e = HS₀ _ (ψ₀W (Ω̇ p a) g₀ u₀ g (pos g) e (Ω≈ (proj₁ (rfB e)) (≈ᴬ-refl a)) (ΩWB e g))

T-mono : ∀ p {a b u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : LB p a u₀) (e′ : LB p b u₁) → a ⊲ b → Tψ p a u₀ g e ⊑⁰ Tψ p b u₁ g′ e′
T-mono p {u₀ = u₀} {u₁} g g′ e e′ d = ⊴₀→⊑⁰ (ψ₀L′ (Ω⊴ p (ho→ht (proj₂ e)) d) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′)
```

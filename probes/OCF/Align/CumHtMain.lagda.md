# 序数高度的世界: 闭包定理

> 不含记号, 不含累加 (`Nx` 是模块参数). 结论写在 [CumHt](CumHt.lagda.md). **`ψL′`, `ψ₀L′`: 折叠保第一位置. `ψW`, `ψ₀W`: 折叠保 `WF`. 对一切高度, 一切层, 一切目标, 一步.** `HS-T`: $(r,p,a)$ 上的树是 `HS` 序数, 对一切 $r$, 一切合法的 $p$, $a$. 与 [CumUpMain](CumUpMain.lagda.md) 同形, 差别只在高度的比较 (`cmpH`), 两位的证据 (`D⊲`), `WF` 按 $(r,p,a)$ 字典序递归.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.CumHtBase using (Nx)
module OCF.Align.CumHtMain (𝓝 : Nx) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level using (HS; hz; hs; hl; _⊑⁰_; _≅_; ≺s; ≺l; ≅→⊑; ≅-refl⁰; z≅; s≅; l≅; FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumHtBase
open import OCF.Align.CumHtTree
open import OCF.Align.CumHtEq
open import OCF.Align.CumHtLe
open import OCF.Align.CumHtW 𝓝
open import OCF.Align.CumHtPsi 𝓝
open Nx 𝓝
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
HS₀ (FL.lim f) (st , u) = hl (λ n → HS₀ (f n) (u n)) (λ n → ⊴₀→⊑⁰ (st n))
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
Lit-+ a (FL.lim f) u (st , v) = (λ n → +⊴ a (st n)) , (λ n → Lit-+ a (f n) u (v n))
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
       ∀ m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m) → Mis m u azero azero (pp p) a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ azero azero (pp p′) a′ →
       ψ₀⁰ x gu m gm um am ⊴₀ ψ₀⁰ y gu′ m′ gm′ um′ am′

  mR : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
       ∀ m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m) → Mis m u azero azero (pp p) a →
       ∀ v (gv : Gw v) (uv : u′ ⊲ v) (av : D⊲ (pp p′) a′ v) →
       ψ₀⁰ x gu m gm um am ⊴₀ ψ₀ y gu′ v gv uv av
  mR d gu gu′ m gm um am is v gv uv av with mx gu′ gv uv (Dz v) av 
  ... | mx′ m′ gm′ um′ tm′ am′ mv is′ = mm d gu gu′ m gm um am is m′ gm′ um′ am′ is′

  mL : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
       ∀ v (gv : Gw v) (uv : u ⊲ v) (av : D⊲ (pp p) a v) →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ azero azero (pp p′) a′ →
       ψ₀ x gu v gv uv av ⊴₀ ψ₀⁰ y gu′ m′ gm′ um′ am′
  mL d gu gu′ v gv uv av m′ gm′ um′ am′ is′ with mx gu gv uv (Dz v) av 
  ... | mx′ m gm um tm am mv is = mm d gu gu′ m gm um am is m′ gm′ um′ am′ is′

  mRL : ∀ {p a u p′ h k u′} {x : 𝓞 p a u} (j : h <ᴴ p′) (y : Low p′ j k u′) → x ⊴ outL j y → (gu : Gw u) (gu′ : Gw u′) →
        ∀ m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m) → Mis m u azero azero (pp p) a →
        ∀ v (gv : Gw v) (uv : u′ ⊲ v) (kv : D⊲ (pp h) k v) →
        ψ₀⁰ x gu m gm um am ⊴₀ ψ₀L j y gu′ v gv uv kv
  mRL hs0 (bx y) d gu gu′ m gm um am is v gv uv kv = mR d gu gu′ m gm um am is v gv uv kv
  mRL (hl0 n₀) (bx y) d gu gu′ m gm um am is v gv uv kv = mR d gu gu′ m gm um am is v gv uv kv
  mRL hr0 (bx y) d gu gu′ m gm um am is v gv uv kv = mR d gu gu′ m gm um am is v gv uv kv
  mRL (hsS j) y d gu gu′ m gm um am is v gv uv kv = mRL j y d gu gu′ m gm um am is v gv uv kv
  mRL (hlS n₀ j) y d gu gu′ m gm um am is v gv uv kv = mRL j y d gu gu′ m gm um am is v gv uv kv
  mRL (hrS j) y d gu gu′ m gm um am is v gv uv kv = mRL j y d gu gu′ m gm um am is v gv uv kv

  mLL : ∀ {p h k u p′ a′ u′} {y : 𝓞 p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) → outL j x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
        ∀ v (gv : Gw v) (uv : u ⊲ v) (kv : D⊲ (pp h) k v) →
        ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ azero azero (pp p′) a′ →
        ψ₀L j x gu v gv uv kv ⊴₀ ψ₀⁰ y gu′ m′ gm′ um′ am′
  mLL hs0 (bx x) d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mL d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (hl0 n₀) (bx x) d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mL d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL hr0 (bx x) d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mL d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (hsS j) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mLL j x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (hlS n₀ j) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mLL j x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′
  mLL (hrS j) x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′ = mLL j x d gu gu′ v gv uv kv m′ gm′ um′ am′ is′

  mm {x = x} {y} (rf e) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = r0 (ψ₀⁰Q x y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e)
  mm (s d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 1 (mR d gu gu′ m gm um am is m′ gm′ um′ am′)
  mm (l n d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 n (mR d gu gu′ m gm um am is m′ gm′ um′ am′)
  mm (fc d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 0 (mR d gu gu′ m gm um am is m′ gm′ um′ am′)
  mm (ni d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 0 (mR (d um′ gm′) gu gm′ m gm um am is m′ gm′ C.self am′)
  mm (nd d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = l0 0 (mR (d um′ gm′) gu gm′ m gm um am is m′ gm′ C.self am′)
  mm (eR {stp = es} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mR d gu gu′ m gm um am is m′ gm′ um′ (Dr (C.suc C.self) am′)
  mm (eR {stp = el n} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mR d gu gu′ m gm um am is m′ gm′ um′ (Dr (C.lim n C.self) am′)
  mm (eL {stp = es} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mL d gu gu′ m gm um (Dr (C.suc C.self) am) m′ gm′ um′ am′ is′
  mm (eL {stp = el n} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mL d gu gu′ m gm um (Dr (C.lim n C.self) am) m′ gm′ um′ am′ is′
  mm (rL {j = j} {e = e} {y = y} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mRL j y d gu gu′ m gm um am is m′ gm′ um′ (dE j e um′ (d₁ am′))
  mm (lL {j = j} {e = e} {x = x} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mLL j x d gu gu′ m gm um (dE j e um (d₁ am)) m′ gm′ um′ am′ is′
  mm (rw {w = w} {g = g} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mR d gu g m gm um am is m′ gm′ (⊲-tr w um′) am′
  mm (lw₂ {w = w} {g = g} d) gu gu′ m gm um am is m′ gm′ um′ am′ is′ = mL d g gu′ m gm (⊲-tr w um) am m′ gm′ um′ am′ is′

  top : ∀ {p a u p′ a′ u′} {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
        ∀ v (gv : Gw v) (uv : u ⊲ v) (av : D⊲ (pp p) a v) →
        ∀ v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (av′ : D⊲ (pp p′) a′ v′) →
        ψ₀ x gu v gv uv av ⊴₀ ψ₀ y gu′ v′ gv′ uv′ av′
  top d gu gu′ v gv uv av v′ gv′ uv′ av′ with mx gu gv uv (Dz v) av 
  ... | mx′ m gm um tm am mv is = mR d gu gu′ m gm um am is v′ gv′ uv′ av′

open M₀ using () renaming (top to ψ₀L′)

-- 非第 0 层的目标
tmm : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q) t m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q) t (pp p′) a′ →
      ψ⁰ q t x gu m gm um tm am ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′

tRm : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
      ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p′) a′ v) →
      ψ⁰ q t x gu m gm um tm am ⊴ ψᵐ q t y gu′ v gv uv tv av
tRm nl d gu gu′ m gm um tm am is v gv uv tv av with mx gu′ gv uv tv av 
... | mx′ m′ gm′ um′ tm′ am′ mv is′ = rw (tmm nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′)

tLm : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p) a v) →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q) t m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q) t (pp p′) a′ →
      ψᵐ q t x gu v gv uv tv av ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tLm nl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ with mx gu gv uv tv av 
... | mx′ m gm um tm am mv is = lw₂ (tmm nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′)

tR : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
     ∀ m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
     ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p′) a′ v) →
     ψ⁰ q t x gu m gm um tm am ⊴ ψ q t y gu′ v gv uv tv av
tR ns d gu gu′ m gm um tm am is v gv uv tv av = tRm ns d gu gu′ m gm um tm am is v gv uv tv av
tR zps d gu gu′ m gm um tm am is v gv uv tv av = tRm zps d gu gu′ m gm um tm am is v gv uv tv av
tR zpl d gu gu′ m gm um tm am is v gv uv tv av = tRm zpl d gu gu′ m gm um tm am is v gv uv tv av
tR zs d gu gu′ m gm um tm am is v gv uv tv av = tRm zs d gu gu′ m gm um tm am is v gv uv tv av
tR zl d gu gu′ m gm um tm am is v gv uv tv av = tRm zl d gu gu′ m gm um tm am is v gv uv tv av

tL : ∀ {p a u p′ a′ u′ q t} (nl : NL q t) {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
     ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p) a v) →
     ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q) t m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q) t (pp p′) a′ →
     ψ q t x gu v gv uv tv av ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tL ns d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm ns d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL zps d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm zps d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL zpl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm zpl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL zs d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm zs d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′
tL zl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′ = tLm zl d gu gu′ v gv uv tv av m′ gm′ um′ tm′ am′ is′

tRL : ∀ {p a u p′ h k u′ q t} (nl : NL q t) {x : 𝓞 p a u} (j : h <ᴴ p′) (y : Low p′ j k u′) → x ⊴ outL j y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Mis m u (pp q) t (pp p) a →
      ∀ v (gv : Gw v) (uv : u′ ⊲ v) (tv : D⊲ (pp q) t v) (kv : D⊲ (pp h) k v) →
      ψ⁰ q t x gu m gm um tm am ⊴ ψL q t j y gu′ v gv uv tv kv
tRL nl hs0 (bx y) d gu gu′ m gm um tm am is v gv uv tv kv = tR nl d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (hl0 n₀) (bx y) d gu gu′ m gm um tm am is v gv uv tv kv = tR nl d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl hr0 (bx y) d gu gu′ m gm um tm am is v gv uv tv kv = tR nl d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (hsS j) y d gu gu′ m gm um tm am is v gv uv tv kv = tRL nl j y d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (hlS n₀ j) y d gu gu′ m gm um tm am is v gv uv tv kv = tRL nl j y d gu gu′ m gm um tm am is v gv uv tv kv
tRL nl (hrS j) y d gu gu′ m gm um tm am is v gv uv tv kv = tRL nl j y d gu gu′ m gm um tm am is v gv uv tv kv

tLL : ∀ {p h k u p′ a′ u′ q t} (nl : NL q t) {y : 𝓞 p′ a′ u′} (j : h <ᴴ p) (x : Low p j k u) → outL j x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (kv : D⊲ (pp h) k v) →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : D⊲ (pp q) t m′) (am′ : D⊲ (pp p′) a′ m′) → Mis m′ u′ (pp q) t (pp p′) a′ →
      ψL q t j x gu v gv uv tv kv ⊴ ψ⁰ q t y gu′ m′ gm′ um′ tm′ am′
tLL nl hs0 (bx x) d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (hl0 n₀) (bx x) d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl hr0 (bx x) d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (hsS j) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (hlS n₀ j) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′
tLL nl (hrS j) x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ v gv uv tv kv m′ gm′ um′ tm′ am′ is′

tmm nl {x} {y} (rf e) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = rf (ψ⁰Q nl nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ (≈ᴴ-refl _) (≈ᴬ-refl _) e)
tmm nl (s d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l 1 (tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm nl (l n d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = l n (tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm nl (fc d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = fc (tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′)
tmm {p′ = p′} {q = q} {t} nl {x} (ni {k = k} {r = r} {h = h} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ with cmpH p′ q (d₁ am′) (d₁ tm′) (lgw gm′)
... | injᵃ i = nd (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inS (≪S r) z)) g v g C.self (D-tr tm′ w) (D-tr am′ w)) (sym (out-inL i (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (D-tr tm′ w) (D-tr am′ w)))
... | injᵇ _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
... | injᶜ refl with cmpN (≪∘ r (d₂ am′)) (d₂ tm′) (lgw gm′)
... | keep s′ = ni (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inS (≪S r) z)) g v g C.self (D-tr tm′ w) (D-tr am′ w)) (sym (out-inS (≪S s′) (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (D-tr tm′ w) (D-tr am′ w)))
... | rise _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
tmm {q = q} {t} nl {x} (nd {h₀ = h₀} {k = k} {i = j} {r = r} {h = h} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ with cmpH h₀ q (d₁ (dR j r um′ (d₁ am′))) (d₁ tm′) (lgw gm′)
... | injᵃ i = nd (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inL j z)) g v g C.self (D-tr tm′ w) (D-tr am′ w)) (sym (out-inL i (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (D-tr tm′ w) (D-tr am′ w)))
... | injᵇ _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
... | injᶜ refl with cmpN (≪∘ (r₂ r) um′) (d₂ tm′) (lgw gm′)
... | keep s′ = ni (λ {v} w g →
      subst (λ z → ψ⁰ q t x gu m gm um tm am ⊴ ψ q t (h (⊲-tr um′ w) g (inL j z)) g v g C.self (D-tr tm′ w) (D-tr am′ w)) (sym (out-inS (≪S s′) (Ω̇at _ k g)))
        (tR nl (d (⊲-tr um′ w) g) gu g m gm um tm am is v g C.self (D-tr tm′ w) (D-tr am′ w)))
... | rise _ = l 0 (tR nl (d um′ gm′) gu gm′ m gm um tm am is m′ gm′ C.self tm′ am′)
tmm nl (eR {stp = es} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.suc C.self) am′)
tmm nl (eR {stp = el n} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR nl d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (Dr (C.lim n C.self) am′)
tmm nl (eL {stp = es} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ m gm um tm (Dr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′
tmm nl (eL {stp = el n} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL nl d gu gu′ m gm um tm (Dr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′
tmm nl (rL {j = j} {e = e} {y = y} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tRL nl j y d gu gu′ m gm um tm am is m′ gm′ um′ tm′ (dE j e um′ (d₁ am′))
tmm nl (lL {j = j} {e = e} {x = x} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tLL nl j x d gu gu′ m gm um tm (dE j e um (d₁ am)) m′ gm′ um′ tm′ am′ is′
tmm nl (rw {w = w} {g = g} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tR nl d gu g m gm um tm am is m′ gm′ (⊲-tr w um′) tm′ am′
tmm nl (lw₂ {w = w} {g = g} d) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ = tL nl d g gu′ m gm (⊲-tr w um) tm am m′ gm′ um′ tm′ am′ is′

-- 总的
ψL′ : ∀ {p a u p′ a′ u′} q t {x : 𝓞 p a u} {y : 𝓞 p′ a′ u′} → x ⊴ y → (gu : Gw u) (gu′ : Gw u′) →
      ∀ v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p) a v) →
      ∀ v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : D⊲ (pp q) t v′) (av′ : D⊲ (pp p′) a′ v′) →
      ψ q t x gu v gv uv tv av ⊴ ψ q t y gu′ v′ gv′ uv′ tv′ av′
ψL′ ⟨ zero , azero ⟩ azero d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ = lw₂ (rw (em⊴ (ψ₀L′ d gu gu′ v gv uv av v′ gv′ uv′ av′)))
ψL′ ⟨ suc σ , y ⟩ t d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ with mx gu gv uv tv av
... | mx′ m gm um tm am mv is = lw₂ (tR ns d gu gu′ m gm um tm am is v′ gv′ uv′ tv′ av′)
ψL′ ⟨ zero , asuc b ⟩ t d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ with mx gu gv uv tv av
... | mx′ m gm um tm am mv is = lw₂ (tR zps d gu gu′ m gm um tm am is v′ gv′ uv′ tv′ av′)
ψL′ ⟨ zero , alim f ⟩ t d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ with mx gu gv uv tv av
... | mx′ m gm um tm am mv is = lw₂ (tR zpl d gu gu′ m gm um tm am is v′ gv′ uv′ tv′ av′)
ψL′ ⟨ zero , azero ⟩ (asuc t) d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ with mx gu gv uv tv av
... | mx′ m gm um tm am mv is = lw₂ (tR zs d gu gu′ m gm um tm am is v′ gv′ uv′ tv′ av′)
ψL′ ⟨ zero , azero ⟩ (alim f) d gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ with mx gu gv uv tv av
... | mx′ m gm um tm am mv is = lw₂ (tR zl d gu gu′ m gm um tm am is v′ gv′ uv′ tv′ av′)

-- Ω_k 是 ψ_k 的任何值的第一位置
Ωfst : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → Ω̇at q t gm ⊴ ψ q t x gu m gm um tm am
Ωfst ⟨ zero , azero ⟩ azero x gu m gm um tm am =
  lw₂ (rw (em⊴ (M₀.mR (z⊴ {p₀ = H₀} {a₀ = azero} {u₀ = m} x) gm gu m gm C.self (Dz m) (iu refl) m gm um am)))
Ωfst ⟨ suc σ , y ⟩ t x gu m gm um tm am =
  tR ns {x = o0 {H₀} {azero} {Vs H₀ azero} {Low H₀}} (z⊴ x) gm gu m gm C.self tm (Dz m) (iu refl) m gm um tm am
Ωfst ⟨ zero , asuc b ⟩ t x gu m gm um tm am =
  tR zps {x = o0 {H₀} {azero} {Vs H₀ azero} {Low H₀}} (z⊴ x) gm gu m gm C.self tm (Dz m) (iu refl) m gm um tm am
Ωfst ⟨ zero , alim f ⟩ t x gu m gm um tm am =
  tR zpl {x = o0 {H₀} {azero} {Vs H₀ azero} {Low H₀}} (z⊴ x) gm gu m gm C.self tm (Dz m) (iu refl) m gm um tm am
Ωfst ⟨ zero , azero ⟩ (asuc t) x gu m gm um tm am =
  tR zs {x = o0 {H₀} {azero} {Vs H₀ azero} {Low H₀}} (z⊴ x) gm gu m gm C.self tm (Dz m) (iu refl) m gm um tm am
Ωfst ⟨ zero , azero ⟩ (alim f) x gu m gm um tm am =
  tR zl {x = o0 {H₀} {azero} {Vs H₀ azero} {Low H₀}} (z⊴ x) gm gu m gm C.self tm (Dz m) (iu refl) m gm um tm am
```

## §3 `WF`

```agda
WF′ : ∀ {ρ p a u} → 𝓞′ ρ p a u → Set
WFS′ : ∀ {ρ p a b} (R : Strict b a) {u} → Vs′ ρ p a R u → Set
WFC′ : ∀ {ρ p a b} (P : b ⊲ a) {u} → Vc′ ρ p a P u → Set
WFL′ : ∀ {ρ p h k u} (j : h <ᴴ ⟨ ρ , p ⟩) → Bx (Low′ ρ p j k u) → Set

WF′ o0 = ⊤
WF′ (os x) = WF′ x
WF′ (ol F) = (∀ n → F n ⊴ F (suc n)) × (∀ n → WF′ (F n))
WF′ {u = u} (oi r h) =
  (∀ {v} (q : u ⊲ v) (g : Gw v) y y′ → outS (≪S r) y ⊴ outS (≪S r) y′ → h q g y ⊴ h q g y′) ×
  (∀ {v} (q : u ⊲ v) (g : Gw v) y → outS (≪S r) y ≈ outS (≪S r) y → WFS′ (≪S r) y → WF′ (h q g y))
WF′ {u = u} (od i k r h) =
  (∀ {v} (q : u ⊲ v) (g : Gw v) y y′ → outL i y ⊴ outL i y′ → h q g y ⊴ h q g y′) ×
  (∀ {v} (q : u ⊲ v) (g : Gw v) y → outL i y ≈ outL i y → WFL′ i y → WF′ (h q g y))
WF′ {u = u} (oc x h) =
  (∀ {v} (q : u ⊲ v) (g : Gw v) → x ⊴ h q g) ×
  (∀ {v v′} (q : u ⊲ v) (q′ : u ⊲ v′) (g : Gw v) (g′ : Gw v′) → v ⊲ v′ → h q g ⊴ h q′ g′) ×
  WF′ x × (∀ {v} (q : u ⊲ v) (g : Gw v) → WF′ (h q g))
WF′ (oe es x) = WF′ x
WF′ (oe (el n) x) = WF′ x
WF′ (oL j k e x) = WFL′ j x
WF′ (ow w g x) = WF′ x

WFS′ (ss P) x = WFC′ P x
WFS′ (sl n P) x = WFC′ P x
WFC′ C.self x = WF′ x
WFC′ (C.suc P) x = WFC′ P x
WFC′ (C.lim n P) x = WFC′ P x
WFL′ hs0 (bx x) = WF′ x
WFL′ (hl0 n₀) (bx x) = WF′ x
WFL′ hr0 (bx x) = WF′ x
WFL′ (hsS j) x = WFL′ j x
WFL′ (hlS n₀ j) x = WFL′ j x
WFL′ (hrS j) x = WFL′ j x


WF : ∀ {p a u} → 𝓞 p a u → Set
WF x = WF′ x

WFS : ∀ {p a b} (R : Strict b a) {u} → Vs p a R u → Set
WFS R x = WFS′ R x

WFC : ∀ {p a b} (P : b ⊲ a) {u} → Vc p a P u → Set
WFC P x = WFC′ P x

WFL : ∀ {p h k u} (j : h <ᴴ p) → Low p j k u → Set
WFL j x = WFL′ j x

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
L→W hs0 (bx x) w = w
L→W (hl0 n₀) (bx x) w = w
L→W hr0 (bx x) w = w
L→W (hsS j) x w = L→W j x w
L→W (hlS n₀ j) x w = L→W j x w
L→W (hrS j) x w = L→W j x w

W→L : ∀ {p h k u} (j : h <ᴴ p) (x : Low p j k u) → WF (outL j x) → WFL j x
W→L hs0 (bx x) w = w
W→L (hl0 n₀) (bx x) w = w
W→L hr0 (bx x) w = w
W→L (hsS j) x w = W→L j x w
W→L (hlS n₀ j) x w = W→L j x w
W→L (hrS j) x w = W→L j x w

-- 分支写成 O k 的值
hMi : ∀ {p a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} → WF (oi r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) {z z′ : 𝓞 p k v} → z ⊴ z′ → h q g (inS (≪S r) z) ⊴ h q g (inS (≪S r) z′)
hMi {r = r} (mon , _) q g {z} {z′} d = mon q g _ _ (subst₂ _⊴_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z′)) d)

hWi : ∀ {p a u k} {r : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs p a (≪S r) v → 𝓞 p a v} → WF (oi r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) (z : 𝓞 p k v) → z ≈ z → WF z → WF (h q g (inS (≪S r) z))
hWi {r = r} (_ , ww) q g z e w = ww q g _ (subst₂ _≈_ (sym (out-inS (≪S r) z)) (sym (out-inS (≪S r) z)) e) (W→S (≪S r) _ (subst WF (sym (out-inS (≪S r) z)) w))

hMd : ∀ {p a u h₀ k} {i : h₀ <ᴴ p} {r : Rd (fd i) k u} {h : ∀ {v} → u ⊲ v → Gw v → Low p i k v → 𝓞 p a v} → WF (od i k r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) {z z′ : 𝓞 h₀ k v} → z ⊴ z′ → h q g (inL i z) ⊴ h q g (inL i z′)
hMd {i = i} (mon , _) q g {z} {z′} d = mon q g _ _ (subst₂ _⊴_ (sym (out-inL i z)) (sym (out-inL i z′)) d)

hWd : ∀ {p a u h₀ k} {i : h₀ <ᴴ p} {r : Rd (fd i) k u} {h : ∀ {v} → u ⊲ v → Gw v → Low p i k v → 𝓞 p a v} → WF (od i k r h) →
      ∀ {v} (q : u ⊲ v) (g : Gw v) (z : 𝓞 h₀ k v) → z ≈ z → WF z → WF (h q g (inL i z))
hWd {i = i} (_ , ww) q g z e w = ww q g _ (subst₂ _≈_ (sym (out-inL i z)) (sym (out-inL i z)) e) (W→L i _ (subst WF (sym (out-inL i z)) w))

ΩH⊴ : ∀ r {p p′} → p ⊲ p′ → Ω̇′ r p azero ⊴ Ω̇′ r p′ azero
ΩH⊴ r {p} C.self = rf (Ω≈′ r (≈ᴬ-refl p) z≈)
ΩH⊴ r (C.suc P) = fc (rL (ni (λ q g → eR {stp = es} (rw (ΩH⊴ r P)))))
ΩH⊴ r (C.lim n P) = l n (rL (ΩH⊴ r P))

ΩW′ : ∀ r p a → Lg p → Lg a → WF (Ω̇′ r p a)
ΩW′ r p (asuc c) lp w = (λ q g y y′ d → eL {stp = es} (eR {stp = es} d)) , (λ q g y _ u → u)
ΩW′ r p (alim f) lp (st , w) = (λ n → eL {stp = el n} (eR {stp = el (suc n)} (Ω⊴ ⟨ r , p ⟩ (st n)))) , (λ n → ΩW′ r p (f n) lp (w n))
ΩW′ r (asuc b) azero lp w =
  (λ q g → lL (rL (rw (Ω⊴ ⟨ r , b ⟩ (pos g))))) , (λ q q′ g g′ vv → lL (rL (lw₂ (rw (Ω⊴ ⟨ r , b ⟩ vv))))) , ΩW′ r b one lp tt , (λ {v} q g → ΩW′ r b v lp (lgw g))
ΩW′ r (alim f) azero (st , lp) w = (λ n → lL (rL (ΩH⊴ r (st n)))) , (λ n → ΩW′ r (f n) azero (lp n) tt)
ΩW′ zero azero azero lp w = tt
ΩW′ (suc σ) azero azero lp w =
  (λ q g → lL (rL (rw (ΩH⊴ σ (pos g))))) , (λ q q′ g g′ vv → lL (rL (lw₂ (rw (ΩH⊴ σ vv))))) , ΩW′ σ one azero tt tt , (λ {v} q g → ΩW′ σ v azero (lgw g) tt)

ΩW : ∀ H a → Lg (pp H) → Lg a → WF (Ω̇ H a)
ΩW H a = ΩW′ (rr H) (pp H) a

ΩWd : ∀ H a {m} → D⊲ (pp H) a m → Gw m → WF (Ω̇ H a)
ΩWd H a e g = ΩW H a (lg⊲ (d₁ e) (lgw g)) (lg⊲ (d₂ e) (lgw g))

-- 加法保 WF
module AddW {p a u₀} (W : 𝓞 p a u₀) (gu : Gw u₀) (E : W ≈ W) (wW : WF W) where
  open AddM W gu E using (mm2)

  aw : ∀ {p₁ b w} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → WF x → ∀ v (gv : Gw v) (uv : u₀ ⊲ v) (xv : w ⊲ v) (bv : D⊲ (fw R) (bw R) v) → WF (add W gu R x gx v gv uv xv bv)
  a⁰ : ∀ {p₁ b w} (R : Rel p₁ b p a) (x : 𝓞 p₁ b w) (gx : Gw w) → WF x → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (am : D⊲ (fw R) (bw R) m) → WF (add⁰ W gu R x gx m gm um tm am)
  aL : ∀ {p₁ h k w} (t : h <ᴴ p) (j : h <ᴴ p₁) (x : Low p₁ j k w) (gx : Gw w) → WFL j x → ∀ m (gm : Gw m) (um : u₀ ⊲ m) (tm : w ⊲ m) (km : D⊲ (fd t) k m) → WF (addL W gu t j x gx m gm um tm km)

  aw R x gx wx v gv uv xv bv with mx gu gv uv (Dzr xv) bv
  ... | mx′ m gm um tm am mv _ = a⁰ R x gx wx m gm um (d₂ tm) am

  a⁰ R o0 gx wx m gm um tm am = wW
  a⁰ R (os x) gx wx m gm um tm am = aw R x gx wx m gm um tm am
  a⁰ R (ol F) gx (st , u) m gm um tm am =
    (λ n → mm2 (st n) R R gx gx m gm um tm am m gm um tm am) , (λ n → aw R (F n) gx (u n) m gm um tm am)
  a⁰ (sa P) (oi r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMi {r = r} wx (⊲-tr tm q) g d) (sa P) (sa P) g g v g (⊲-tr um q) C.self (Dz v) v g (⊲-tr um q) C.self (Dz v)) ,
    (λ {v} q g y py uy → aw (sa P) (h (⊲-tr tm q) g _) g (hWi {r = r} wx (⊲-tr tm q) g _ py (S→W _ y uy)) v g (⊲-tr um q) C.self (Dz v))
  a⁰ (lw i) (oi r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMi {r = r} wx (⊲-tr tm q) g d) (lw i) (lw i) g g v g (⊲-tr um q) C.self (D-tr am q) v g (⊲-tr um q) C.self (D-tr am q)) ,
    (λ {v} q g y py uy → aw (lw i) (h (⊲-tr tm q) g _) g (hWi {r = r} wx (⊲-tr tm q) g _ py (L→W i y uy)) v g (⊲-tr um q) C.self (D-tr am q))
  a⁰ (sa P) (od j k r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMd {i = j} {r = r} wx (⊲-tr tm q) g d) (sa P) (sa P) g g v g (⊲-tr um q) C.self (Dz v) v g (⊲-tr um q) C.self (Dz v)) ,
    (λ {v} q g y py uy → aw (sa P) (h (⊲-tr tm q) g _) g (hWd {i = j} {r = r} wx (⊲-tr tm q) g _ py (L→W j y uy)) v g (⊲-tr um q) C.self (Dz v))
  a⁰ (lw i) (od j k r h) gx wx m gm um tm am =
    (λ {v} q g y y′ d → mm2 (hMd {i = j} {r = r} wx (⊲-tr tm q) g d) (lw i) (lw i) g g v g (⊲-tr um q) C.self (D-tr am q) v g (⊲-tr um q) C.self (D-tr am q)) ,
    (λ {v} q g y py uy → aw (lw i) (h (⊲-tr tm q) g _) g (hWd {i = j} {r = r} wx (⊲-tr tm q) g _ py (L→W (<tr j i) y uy)) v g (⊲-tr um q) C.self (D-tr am q))
  a⁰ R (oc x h) gx (fi , dr , wx , wh) m gm um tm am =
    (λ {v} q g → mm2 (fi (⊲-tr tm q) g) R R gx g m gm um tm am v g (⊲-tr um q) C.self (D-tr am q)) ,
    (λ {v} {v′} q q′ g g′ p₁ → mm2 (dr (⊲-tr tm q) (⊲-tr tm q′) g g′ p₁) R R g g′ v g (⊲-tr um q) C.self (D-tr am q) v′ g′ (⊲-tr um q′) C.self (D-tr am q′)) ,
    aw R x gx wx m gm um tm am ,
    (λ {v} q g → aw R (h (⊲-tr tm q) g) g (wh (⊲-tr tm q) g) v g (⊲-tr um q) C.self (D-tr am q))
  a⁰ (sa P) (oe es x) gx wx m gm um tm am = aw (sa (⊲-tr (C.suc C.self) P)) x gx wx m gm um tm am
  a⁰ (lw i) (oe es x) gx wx m gm um tm am = aw (lw i) x gx wx m gm um tm (Dr (C.suc C.self) am)
  a⁰ (sa P) (oe (el n) x) gx wx m gm um tm am = aw (sa (⊲-tr (C.lim n C.self) P)) x gx wx m gm um tm am
  a⁰ (lw i) (oe (el n) x) gx wx m gm um tm am = aw (lw i) x gx wx m gm um tm (Dr (C.lim n C.self) am)
  a⁰ (sa P) (oL j k e x) gx wx m gm um tm am = aL j j x gx wx m gm um tm (D-tr e tm)
  a⁰ (lw i) (oL j k e x) gx wx m gm um tm am = aL (<tr j i) j x gx wx m gm um tm (Dfd j i (D-tr e tm) (d₁ am))
  a⁰ R (ow w g′ x) gx wx m gm um tm am = aw R x g′ wx m gm um (⊲-tr w tm) am

  aL t hs0 (bx x) gx wx m gm um tm km = aw (lw t) x gx wx m gm um tm km
  aL t (hl0 n₀) (bx x) gx wx m gm um tm km = aw (lw t) x gx wx m gm um tm km
  aL t hr0 (bx x) gx wx m gm um tm km = aw (lw t) x gx wx m gm um tm km
  aL t (hsS j) x gx wx m gm um tm km = aL t j x gx wx m gm um tm km
  aL t (hlS n₀ j) x gx wx m gm um tm km = aL t j x gx wx m gm um tm km
  aL t (hrS j) x gx wx m gm um tm km = aL t j x gx wx m gm um tm km

rep⊴ : ∀ {q t u} {y : 𝓞 q t u} (e : y ≈ y) (g : Gw u) → ∀ n → rep y g n ⊴ rep y g (suc n)
rep⊴ {y = y} e g zero = z⊴ y
rep⊴ {q = q} {t = t} {u} {y} e g (suc m) = AddF.add⊴ (rep y g (suc m)) g (rf (rep≈ (≈ᴴ-refl q) (≈ᴬ-refl t) (≈ᴬ-refl u) e g g (suc m))) (sa C.self) y g u g C.self C.self (Dz u)

repW : ∀ {q t u} {y : 𝓞 q t u} (e : y ≈ y) (g : Gw u) → WF y → ∀ n → WF (rep y g n)
repW e g w zero = tt
repW e g w (suc zero) = w
repW {q = q} {t = t} {u} {y} e g w (suc (suc m)) =
  AddW.aw (rep y g (suc m)) g (rep≈ (≈ᴴ-refl q) (≈ᴬ-refl t) (≈ᴬ-refl u) e g g (suc m)) (repW e g w (suc m)) (sa C.self) y g w u g C.self C.self (Dz u)

emW : ∀ a → Lit₀ a → WF (em {one} a)
emW FL.zero u = tt
emW (FL.suc a) u = emW a u
emW (FL.lim f) (st , u) = (λ n → em⊴ (st n)) , (λ n → emW (f n) (u n))
emW (FL.limᵢ () f) u
emW (FL.up () x) u
```

## §4 闭包定理

对项递归. 上升时链 $z_n$ 的 `WF`, 相邻的 `⊴` 都是这条定理自己. **与高度, 阶段无关.**

```agda
ψW  : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p) a v) → x ≈ x → WF x → WF (ψ q t x gu v gv uv tv av)
ψWm : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : D⊲ (pp q) t v) (av : D⊲ (pp p) a v) → x ≈ x → WF x → WF (ψᵐ q t x gu v gv uv tv av)
ψW⁰ : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (am : D⊲ (pp p) a m) → x ≈ x → WF x → WF (ψ⁰ q t x gu m gm um tm am)
ψWL : ∀ {p h k u} q t (j : h <ᴴ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : D⊲ (pp q) t m) (km : D⊲ (pp h) k m) → outL j x ≈ outL j x → WFL j x → WF (ψL q t j x gu m gm um tm km)
ψ₀W  : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : D⊲ (pp p) a v) → x ≈ x → WF x → Lit₀ (ψ₀ x gu v gv uv av)
ψ₀W⁰ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : D⊲ (pp p) a m) → x ≈ x → WF x → Lit₀ (ψ₀⁰ x gu m gm um am)
ψ₀WL : ∀ {p h k u} (j : h <ᴴ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (km : D⊲ (pp h) k m) → outL j x ≈ outL j x → WFL j x → Lit₀ (ψ₀L j x gu m gm um km)

ψW ⟨ zero , azero ⟩ azero x gu v gv uv tv av e w = emW _ (ψ₀W x gu v gv uv av e w)
ψW ⟨ suc σ , y ⟩ t x gu v gv uv tv av e w = ψWm ⟨ suc σ , y ⟩ t x gu v gv uv tv av e w
ψW ⟨ zero , asuc b ⟩ t x gu v gv uv tv av e w = ψWm ⟨ zero , asuc b ⟩ t x gu v gv uv tv av e w
ψW ⟨ zero , alim f ⟩ t x gu v gv uv tv av e w = ψWm ⟨ zero , alim f ⟩ t x gu v gv uv tv av e w
ψW ⟨ zero , azero ⟩ (asuc t) x gu v gv uv tv av e w = ψWm ⟨ zero , azero ⟩ (asuc t) x gu v gv uv tv av e w
ψW ⟨ zero , azero ⟩ (alim f) x gu v gv uv tv av e w = ψWm ⟨ zero , azero ⟩ (alim f) x gu v gv uv tv av e w

ψWm q t x gu v gv uv tv av e w with mx gu gv uv tv av
... | mx′ m gm um tm am mv _ = ψW⁰ q t x gu m gm um tm am e w

ψW⁰ q t o0 gu m gm um tm am e w = ΩWd q t tm gm
ψW⁰ q t (os x) gu m gm um tm am (_ , _ , _ , e) w =
  (λ n → rep⊴ (ψQ x x gu gu m gm um tm am m gm um tm am (≈ᴴ-refl q) (≈ᴬ-refl t) e) gm n) ,
  (λ n → repW (ψQ x x gu gu m gm um tm am m gm um tm am (≈ᴴ-refl q) (≈ᴬ-refl t) e) gm (ψW q t x gu m gm um tm am e w) n)
ψW⁰ q t (ol F) gu m gm um tm am e (st , u) =
  (λ n → ψL′ q t (st n) gu gu m gm um tm am m gm um tm am) , (λ n → ψW q t (F n) gu m gm um tm am (e n) (u n))
ψW⁰ {p} {a} q t (oi {k = k} r f) gu m gm um tm am (_ , _ , _ , _ , N) w with cmpH p q (d₁ am) (d₁ tm) (lgw gm)
... | injᵃ i =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMi {r = r} w (⊲-tr um w₁) g d) g g v g C.self (D-tr tm w₁) (D-tr am w₁) v g C.self (D-tr tm w₁) (D-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (D-tr tm w₁) (D-tr am w₁)
      (nI {r = r} {r} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWi {r = r} w (⊲-tr um w₁) g _ py (L→W i y uy)))
... | injᵇ _ =
  (λ n → ψL′ q t (hMi {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (≈ᴴ-refl p) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (Dr (≪⊲ r) am) am m gm C.self (Dr (≪⊲ r) am) am (≈ᴴ-refl p) (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWd p k (Dr (≪⊲ r) am) gm
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (Dr (≪⊲ r) am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (Dr (≪⊲ r) am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (Dr (≪⊲ r) am) am m gm C.self (Dr (≪⊲ r) am) am
... | injᶜ refl with cmpN (≪∘ r (d₂ am)) (d₂ tm) (lgw gm)
... | keep s′ =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMi {r = r} w (⊲-tr um w₁) g d) g g v g C.self (D-tr tm w₁) (D-tr am w₁) v g C.self (D-tr tm w₁) (D-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (D-tr tm w₁) (D-tr am w₁)
      (nI {r = r} {r} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWi {r = r} w (⊲-tr um w₁) g _ py (S→W (≪S s′) y uy)))
... | rise _ =
  (λ n → ψL′ q t (hMi {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (≈ᴴ-refl p) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (Dr (≪⊲ r) am) am m gm C.self (Dr (≪⊲ r) am) am (≈ᴴ-refl p) (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWd p k (Dr (≪⊲ r) am) gm
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (Dr (≪⊲ r) am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (Dr (≪⊲ r) am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (Dr (≪⊲ r) am) am m gm C.self (Dr (≪⊲ r) am) am
ψW⁰ q t (od {h = h₀} j k r f) gu m gm um tm am (_ , _ , _ , _ , _ , N) w with cmpH h₀ q (d₁ (dR j r um (d₁ am))) (d₁ tm) (lgw gm)
... | injᵃ i =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMd {i = j} {r = r} w (⊲-tr um w₁) g d) g g v g C.self (D-tr tm w₁) (D-tr am w₁) v g C.self (D-tr tm w₁) (D-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (D-tr tm w₁) (D-tr am w₁)
      (nD {j = j} {j} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWd {i = j} {r = r} w (⊲-tr um w₁) g _ py (L→W i y uy)))
... | injᵇ _ =
  (λ n → ψL′ q t (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (≈ᴴ-refl h₀) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (dR j r um (d₁ am)) am m gm C.self (dR j r um (d₁ am)) am (≈ᴴ-refl h₀) (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWd h₀ k (dR j r um (d₁ am)) gm
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (dR j r um (d₁ am)) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (dR j r um (d₁ am)) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (dR j r um (d₁ am)) am m gm C.self (dR j r um (d₁ am)) am
... | injᶜ refl with cmpN (≪∘ (r₂ r) um) (d₂ tm) (lgw gm)
... | keep s′ =
  (λ {v} w₁ g y y′ d → ψL′ q t (hMd {i = j} {r = r} w (⊲-tr um w₁) g d) g g v g C.self (D-tr tm w₁) (D-tr am w₁) v g C.self (D-tr tm w₁) (D-tr am w₁)) ,
  (λ {v} w₁ g y py uy → ψW q t (f (⊲-tr um w₁) g _) g v g C.self (D-tr tm w₁) (D-tr am w₁)
      (nD {j = j} {j} {f} {f} N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v) _ _ py) (hWd {i = j} {r = r} w (⊲-tr um w₁) g _ py (S→W (≪S s′) y uy)))
... | rise _ =
  (λ n → ψL′ q t (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self tm am m gm C.self tm am) ,
  (λ n → ψW q t (f um gm _) gm m gm C.self tm am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (≈ᴴ-refl h₀) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (dR j r um (d₁ am)) am m gm C.self (dR j r um (d₁ am)) am (≈ᴴ-refl h₀) (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWd h₀ k (dR j r um (d₁ am)) gm
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (dR j r um (d₁ am)) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (dR j r um (d₁ am)) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (dR j r um (d₁ am)) am m gm C.self (dR j r um (d₁ am)) am
ψW⁰ q t (oc x f) gu m gm um tm am (_ , _ , _ , ex , N) (fi , dr , wx , wf) =
  (λ {v} w₁ g → ψL′ q t (fi (⊲-tr um w₁) g) gu g m gm um tm am v g C.self (D-tr tm w₁) (D-tr am w₁)) ,
  (λ {v} {v′} w₁ w₂ g g′ p₁ → ψL′ q t (dr (⊲-tr um w₁) (⊲-tr um w₂) g g′ p₁) g g′ v g C.self (D-tr tm w₁) (D-tr am w₁) v′ g′ C.self (D-tr tm w₂) (D-tr am w₂)) ,
  ψW q t x gu m gm um tm am ex wx ,
  (λ {v} w₁ g → ψW q t (f (⊲-tr um w₁) g) g v g C.self (D-tr tm w₁) (D-tr am w₁) (N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v)) (wf (⊲-tr um w₁) g))
ψW⁰ q t (oe es x) gu m gm um tm am e w = ψW q t x gu m gm um tm (Dr (C.suc C.self) am) (≈oe⁻ {R = ss C.self} x es x e) w
ψW⁰ q t (oe (el n) x) gu m gm um tm am e w = ψW q t x gu m gm um tm (Dr (C.lim n C.self) am) (≈oe⁻ {R = sl n C.self} x (el n) x e) w
ψW⁰ q t (oL j k e₁ x) gu m gm um tm am e w = ψWL q t j x gu m gm um tm (dE j e₁ um (d₁ am)) (≈oL⁻ (outL j x) j e₁ x (Ll→ j x e)) w
ψW⁰ q t (ow p g′ x) gu m gm um tm am e w = ψW q t x g′ m gm (⊲-tr p um) tm am (≈ow⁻ x p g′ x e) w

ψWL q t hs0 (bx x) gu m gm um tm km e w = ψW q t x gu m gm um tm km e w
ψWL q t (hl0 n₀) (bx x) gu m gm um tm km e w = ψW q t x gu m gm um tm km e w
ψWL q t hr0 (bx x) gu m gm um tm km e w = ψW q t x gu m gm um tm km e w
ψWL q t (hsS j) x gu m gm um tm km e w = ψWL q t j x gu m gm um tm km e w
ψWL q t (hlS n₀ j) x gu m gm um tm km e w = ψWL q t j x gu m gm um tm km e w
ψWL q t (hrS j) x gu m gm um tm km e w = ψWL q t j x gu m gm um tm km e w

ψ₀W x gu v gv uv av e w with mx gu gv uv (Dz v) av
... | mx′ m gm um tm am mv _ = ψ₀W⁰ x gu m gm um am e w

ψ₀W⁰ o0 gu m gm um am e w = tt
ψ₀W⁰ (os x) gu m gm um am (_ , _ , _ , e) w =
  rep₀⊴ (ψ₀ x gu m gm um am) , Lit-rep (ψ₀ x gu m gm um am) (ψ₀W x gu m gm um am e w)
ψ₀W⁰ (ol F) gu m gm um am e (st , u) =
  (λ n → ψ₀L′ (st n) gu gu m gm um am m gm um am) , (λ n → ψ₀W (F n) gu m gm um am (e n) (u n))
ψ₀W⁰ {p} {a} (oi {k = k} r f) gu m gm um am (_ , _ , _ , _ , N) w =
  (λ n → ψ₀L′ (hMi {r = r} w um gm (zS n)) gm gm m gm C.self am m gm C.self am) ,
  (λ n → ψ₀W (f um gm _) gm m gm C.self am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nI {r = r} {r} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 p k m
  z = chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (Dr (≪⊲ r) am) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (≈ᴴ-refl p) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (Dr (≪⊲ r) am) am m gm C.self (Dr (≪⊲ r) am) am (≈ᴴ-refl p) (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWd p k (Dr (≪⊲ r) am) gm
  zW (suc n) = ψW p k (f um gm _) gm m gm C.self (Dr (≪⊲ r) am) am (N₁ _ _ (zP n)) (hWi {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst p k (f um gm _) gm m gm C.self (Dr (≪⊲ r) am) am
  zS (suc n) = ψL′ p k (hMi {r = r} w um gm (zS n)) gm gm m gm C.self (Dr (≪⊲ r) am) am m gm C.self (Dr (≪⊲ r) am) am
ψ₀W⁰ (od {h = h₀} j k r f) gu m gm um am (_ , _ , _ , _ , _ , N) w =
  (λ n → ψ₀L′ (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self am m gm C.self am) ,
  (λ n → ψ₀W (f um gm _) gm m gm C.self am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n)))
  where
  N₁ = nD {j = j} {j} {f} {f} N um um gm gm (≈ᴬ-refl m)
  z : ℕ → 𝓞 h₀ k m
  z = chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (dR j r um (d₁ am)) am)
  zP : ∀ n → z n ≈ z n
  zP zero = ≈-Ωat gm gm (≈ᴴ-refl h₀) (≈ᴬ-refl k)
  zP (suc n) = ψQ (f um gm _) (f um gm _) gm gm m gm C.self (dR j r um (d₁ am)) am m gm C.self (dR j r um (d₁ am)) am (≈ᴴ-refl h₀) (≈ᴬ-refl k) (N₁ _ _ (zP n))
  zW : ∀ n → WF (z n)
  zW zero = ΩWd h₀ k (dR j r um (d₁ am)) gm
  zW (suc n) = ψW h₀ k (f um gm _) gm m gm C.self (dR j r um (d₁ am)) am (N₁ _ _ (zP n)) (hWd {i = j} {r = r} w um gm _ (zP n) (zW n))
  zS : ∀ n → z n ⊴ z (suc n)
  zS zero = Ωfst h₀ k (f um gm _) gm m gm C.self (dR j r um (d₁ am)) am
  zS (suc n) = ψL′ h₀ k (hMd {i = j} {r = r} w um gm (zS n)) gm gm m gm C.self (dR j r um (d₁ am)) am m gm C.self (dR j r um (d₁ am)) am
ψ₀W⁰ (oc x f) gu m gm um am (_ , _ , _ , ex , N) (fi , dr , wx , wf) = st , li
  where
  val : Ix m → Ord₀
  val i = ψ₀ (f (⊲-tr um (Ix.up i)) (Ix.gη i)) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (D-tr am (Ix.up i))
  y₀ : Ord₀
  y₀ = ψ₀ x gu m gm um am
  st : ∀ n → yss gm y₀ val n ⊴₀ yss gm y₀ val (suc n)
  st zero = ψ₀L′ (fi (⊲-tr um (Ix.up (ixs gm y₀ val 0))) (Ix.gη (ixs gm y₀ val 0))) gu _ m gm um am _ _ C.self _
  st (suc n) = ψ₀L′ (dr (⊲-tr um (Ix.up (ixs gm y₀ val n))) (⊲-tr um (Ix.up (ixs gm y₀ val (suc n)))) _ _ (nxt-⊲ (Ix.η (ixs gm y₀ val n)) (val (ixs gm y₀ val n)))) _ _ _ _ C.self _ _ _ C.self _
  li : ∀ n → Lit₀ (yss gm y₀ val n)
  li zero = ψ₀W x gu m gm um am ex wx
  li (suc n) = ψ₀W (f _ _) _ _ _ C.self _ (N _ _ _ _ (≈ᴬ-refl _)) (wf _ _)
ψ₀W⁰ (oe es x) gu m gm um am e w = ψ₀W x gu m gm um (Dr (C.suc C.self) am) (≈oe⁻ {R = ss C.self} x es x e) w
ψ₀W⁰ (oe (el n) x) gu m gm um am e w = ψ₀W x gu m gm um (Dr (C.lim n C.self) am) (≈oe⁻ {R = sl n C.self} x (el n) x e) w
ψ₀W⁰ (oL j k e₁ x) gu m gm um am e w = ψ₀WL j x gu m gm um (dE j e₁ um (d₁ am)) (≈oL⁻ (outL j x) j e₁ x (Ll→ j x e)) w
ψ₀W⁰ (ow p g′ x) gu m gm um am e w = ψ₀W x g′ m gm (⊲-tr p um) am (≈ow⁻ x p g′ x e) w

ψ₀WL hs0 (bx x) gu m gm um km e w = ψ₀W x gu m gm um km e w
ψ₀WL (hl0 n₀) (bx x) gu m gm um km e w = ψ₀W x gu m gm um km e w
ψ₀WL hr0 (bx x) gu m gm um km e w = ψ₀W x gu m gm um km e w
ψ₀WL (hsS j) x gu m gm um km e w = ψ₀WL j x gu m gm um km e w
ψ₀WL (hlS n₀ j) x gu m gm um km e w = ψ₀WL j x gu m gm um km e w
ψ₀WL (hrS j) x gu m gm um km e w = ψ₀WL j x gu m gm um km e w
```

## §5 $\psi_0(\Omega_{\Omega^2\cdot r+\Omega\cdot p+a})$

**定理.** 对一切 $r$ 与字面合法的 $p$, $a$, `Tψ` 是 `HS` 序数. 这一条不说明它有多大, 见 [CumHt](CumHt.lagda.md) 的对照 `HS-Nxˢ`.

```agda
HS-T : ∀ H a u₀ (g : Gw u₀) (e : D⊲ (pp H) a u₀) → HS (Tψ H a u₀ g e)
HS-T H a u₀ g e = HS₀ _ (ψ₀W (Ω̇ H a) g₀ u₀ g (pos g) e (Ω≈ (≈ᴴ-refl H) (≈ᴬ-refl a)) (ΩWd H a e g))

-- 第 a 位单调
T-mono : ∀ H {a b u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : D⊲ (pp H) a u₀) (e′ : D⊲ (pp H) b u₁) → a ⊲ b → Tψ H a u₀ g e ⊑⁰ Tψ H b u₁ g′ e′
T-mono H {u₀ = u₀} {u₁} g g′ e e′ d = ⊴₀→⊑⁰ (ψ₀L′ (Ω⊴ H d) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′)

-- 第 p 位单调
T-monoᴾ : ∀ r {p p′ u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : D⊲ p azero u₀) (e′ : D⊲ p′ azero u₁) → p ⊲ p′ → Tψ ⟨ r , p ⟩ azero u₀ g e ⊑⁰ Tψ ⟨ r , p′ ⟩ azero u₁ g′ e′
T-monoᴾ r {u₀ = u₀} {u₁} g g′ e e′ d = ⊴₀→⊑⁰ (ψ₀L′ (ΩH⊴ r d) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′)

-- 第 r 位, 只到 p = 0 这一支: 下一位的第一支含这一位
ΩR⊴ : ∀ r → Ω̇′ r azero azero ⊴ Ω̇′ (suc r) azero azero
ΩR⊴ r = fc (rL (ΩH⊴ r (z⊲ one)))

T-monoᴿ : ∀ r {u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : D⊲ azero azero u₀) (e′ : D⊲ azero azero u₁) → Tψ ⟨ r , azero ⟩ azero u₀ g e ⊑⁰ Tψ ⟨ suc r , azero ⟩ azero u₁ g′ e′
T-monoᴿ r {u₀ = u₀} {u₁} g g′ e e′ = ⊴₀→⊑⁰ (ψ₀L′ (ΩR⊴ r) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′)

-- 运行世界不进结论: 同一棵树, 在任何足够高的世界上, 树互模拟. 这是 up-sim 的对应物
T-world : ∀ H a {u₀ u₁} (g : Gw u₀) (g′ : Gw u₁) (e : D⊲ (pp H) a u₀) (e′ : D⊲ (pp H) a u₁) → Tψ H a u₀ g e ≅ Tψ H a u₁ g′ e′
T-world H a {u₀} {u₁} g g′ e e′ = ψ₀Q (Ω̇ H a) (Ω̇ H a) g₀ g₀ u₀ g (pos g) e u₁ g′ (pos g′) e′ (Ω≈ (≈ᴴ-refl H) (≈ᴬ-refl a))
```

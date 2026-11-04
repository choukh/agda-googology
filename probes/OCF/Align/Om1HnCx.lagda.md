# $\psi_0(\Omega_{\Omega+1})$, 不累加: 上下文

> 不含记号. 结论写在 [Om1Hn](Om1Hn.lagda.md). 上下文 `Cx` 是语义的: `Rn C x y` 说 $y$ 是 $x$ 过 $C$ 的一次运行. 帧有两种, `Fψ` (折叠) 和 `Fa` (加法), 顶是 `idC`. **上下文不按层分类**, 所以 `oe`, `oL`, `ow` 不需要下移上下文: 这是比 `OCF.Free` 省的第一件事 (判断: 那边的 `Dn`, `sh`, `Inp`, `tr` 一族在这里没有对应).
>
> `dn`: 对 $x\trianglelefteq x'$, $x'$ 的运行有证书, 则 $x$ 也有运行, 也有证书, 计值更低. 这是 `OCF.Free` 的 $\sqsubseteq^E$ 的角色, 这里由 `G-tr`, `G-dn` 证, 不走 $\approx$ 的传递性.
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1HnCx where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
import OCF.Free.Level as FL
open FL using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (ψL′; Ωfst)
open import OCF.Align.NoCumForce hiding (Cl; C′)
```

## §0 值上的小引理

```agda
≅₀-sym : ∀ {a b : Ord₀} → a ≅ b → b ≅ a
≅₀-sym z≅ = z≅
≅₀-sym (s≅ e) = s≅ (≅₀-sym e)
≅₀-sym (l≅ h) = l≅ (λ n → ≅₀-sym (h n))
≅₀-sym (lᵢ≅ {p = ()} e h)
≅₀-sym (upˡ {r = ()} e)
≅₀-sym (upʳ {r = ()} e)

≅₀-trans : ∀ {a b c : Ord₀} → a ≅ b → b ≅ c → a ≅ c
≅₀-trans z≅ z≅ = z≅
≅₀-trans (s≅ e) (s≅ d) = s≅ (≅₀-trans e d)
≅₀-trans (l≅ h) (l≅ k) = l≅ (λ n → ≅₀-trans (h n) (k n))
≅₀-trans (lᵢ≅ {p = ()} e h) d
≅₀-trans (upˡ {r = ()} e) d
≅₀-trans (upʳ {r = ()} e) d
≅₀-trans z≅ (upʳ {r = ()} e)
≅₀-trans (s≅ e) (upʳ {r = ()} d)
≅₀-trans (l≅ h) (upʳ {r = ()} d)

⊴₀-r : ∀ {a b c} → a ⊴₀ b → b ≅ c → a ⊴₀ c
⊴₀-r (r0 e) d = r0 (≅₀-trans e d)
⊴₀-r (s0 p) (s≅ d) = s0 (⊴₀-r p d)
⊴₀-r (s0 p) (upʳ {r = ()} d)
⊴₀-r (l0 n p) (l≅ h) = l0 n (⊴₀-r p (h n))
⊴₀-r (l0 n p) (upʳ {r = ()} d)

⊴₀-l : ∀ {a b c} → a ≅ b → b ⊴₀ c → a ⊴₀ c
⊴₀-l e (r0 d) = r0 (≅₀-trans e d)
⊴₀-l e (s0 p) = s0 (⊴₀-l e p)
⊴₀-l e (l0 n p) = l0 n (⊴₀-l e p)

⊴₀-tr : ∀ {a b c} → a ⊴₀ b → b ⊴₀ c → a ⊴₀ c
⊴₀-tr p (r0 e) = ⊴₀-r p e
⊴₀-tr p (s0 q) = s0 (⊴₀-tr p q)
⊴₀-tr p (l0 n q) = l0 n (⊴₀-tr p q)

≅₀-refl : ∀ (a : Ord₀) → a ≅ a
≅₀-refl FL.zero = z≅
≅₀-refl (FL.suc a) = s≅ (≅₀-refl a)
≅₀-refl (FL.lim f) = l≅ (λ n → ≅₀-refl (f n))
≅₀-refl (FL.limᵢ () f)
≅₀-refl (FL.up () x)

Fp-z : ∀ (y : Ord₀) → Fp azero y
Fp-z FL.zero = fq z≈
Fp-z (FL.suc y) = fs (Fp-z y)
Fp-z (FL.lim f) = fl 0 (Fp-z (f 0))
Fp-z (FL.limᵢ () f)
Fp-z (FL.up () x)
```

## §1 证书沿 $\approx$ 与第一位置往下搬

`G-tr`: 链要重新嫁接, 因为世界只模 $\approx^A$ 相同. 不走 $\approx$ 的传递性, 走 `fo≅`.

```agda
G-tr : ∀ {u u′} (x : 𝓡 u) (y : 𝓡 u′) → Gw u → x ≈ y → G y → G x
G-tr (ow p g x) y gu e b = gw {p = p} {g = g} (G-tr x y g e b)
G-tr (oi () _) y gu e b
G-tr (od () _ _ _) y gu e b
G-tr (oe () _) y gu e b
G-tr (oL () _ _ _) y gu e b
G-tr o0 (ow p g y) gu e (gw b) = G-tr o0 y gu e b
G-tr X@(os x) (ow p g y) gu e (gw b) = G-tr X y gu e b
G-tr X@(ol F) (ow p g y) gu e (gw b) = G-tr X y gu e b
G-tr X@(oc x h) (ow p g y) gu e (gw b) = G-tr X y gu e b
G-tr o0 o0 gu e g0 = g0
G-tr (os x) (os y) gu (_ , _ , _ , e) (gs b) = gs (G-tr x y gu e b)
G-tr (ol F) (ol H) gu e (gl Gs st) = gl Gs′ (λ n → ⊴₀-l (E n) (⊴₀-r (st n) (≅₀-sym (E (suc n)))))
  where
  Gs′ : ∀ n → G (F n)
  Gs′ n = G-tr (F n) (H n) gu (e n) (Gs n)
  E : ∀ n → force (Gs′ n) ≅ force (Gs n)
  E n = fo≅ (Gs′ n) (Gs n) (e n)
G-tr {u} {u′} (oc x h) (oc x′ h′) gu (_ , _ , eu , ex , N) (gc G₀ vs gv up Gh t₀ tS s₀ sS) =
  gc G₀′ vs′ gv′ up′ Gh′ t₀′ tS′ (⊴₀-l E₀ (⊴₀-r s₀ (≅₀-sym (E 0)))) (λ n → ⊴₀-l (E n) (⊴₀-r (sS n) (≅₀-sym (E (suc n)))))
  where
  G₀′ : G x
  G₀′ = G-tr x x′ gu ex G₀
  E₀ : force G₀′ ≅ force G₀
  E₀ = fo≅ G₀′ G₀ ex
  r : ∀ n → Gr (vs n) u
  r n = graftA (vs n) (up n) (lgw (gv n)) u (lgw gu) eu
  vs′ : ℕ → A
  vs′ n = g (gE (r n))
  gv′ : ∀ n → Gw (vs′ n)
  gv′ n = gw (lg (gE (r n))) (⊲-tr (pos gu) (at (r n)))
  up′ : ∀ n → u ⊲ vs′ n
  up′ n = at (r n)
  Gh′ : ∀ n → G (h (up′ n) (gv′ n))
  Gh′ n = G-tr (h (up′ n) (gv′ n)) (h′ (up n) (gv n)) (gv′ n) (N (up′ n) (up n) (gv′ n) (gv n) (eq (gE (r n)))) (Gh n)
  E : ∀ n → force (Gh′ n) ≅ force (Gh n)
  E n = fo≅ (Gh′ n) (Gh n) (N (up′ n) (up n) (gv′ n) (gv n) (eq (gE (r n))))
  t₀′ : vs′ 0 ≈ᴬ rd (force G₀′)
  t₀′ = ≈ᴬ-trans (eq (gE (r 0))) (≈ᴬ-trans t₀ (≅→≈ (≅₀-sym E₀)))
  tS′ : ∀ n → vs′ (suc n) ≈ᴬ rd (force (Gh′ n))
  tS′ n = ≈ᴬ-trans (eq (gE (r (suc n)))) (≈ᴬ-trans (tS n) (≅→≈ (≅₀-sym (E n))))
G-tr o0 (os _) gu () b
G-tr o0 (ol _) gu () b
G-tr o0 (oc _ _) gu () b
G-tr (os _) o0 gu () b
G-tr (os _) (ol _) gu () b
G-tr (os _) (oc _ _) gu () b
G-tr (ol _) o0 gu () b
G-tr (ol _) (os _) gu () b
G-tr (ol _) (oc _ _) gu () b
G-tr (oc _ _) o0 gu () b
G-tr (oc _ _) (os _) gu () b
G-tr (oc _ _) (ol _) gu () b
G-tr x (oi () _) gu e b
G-tr x (od () _ _ _) gu e b
G-tr x (oe () _) gu e b
G-tr x (oL () _ _ _) gu e b

G-dn : ∀ {u u′} (x : 𝓡 u) {y : 𝓡 u′} → Gw u → x ⊴ y → (b : G y) → Σ (G x) (λ a → force a ⊴₀ force b)
G-dn x gx (rw d) (gw b) = G-dn x gx d b
G-dn (ow w g x) gx (lw₂ d) b with G-dn x g d b
... | a , f = gw {p = w} {g = g} a , f
G-dn x gx (rf e) b = let a = G-tr x _ gx e b in a , r0 (fo≅ a b e)
G-dn x gx (s d) (gs b) with G-dn x gx d b
... | a , f = a , s0 f
G-dn x gx (l n d) (gl Gs st) with G-dn x gx d (Gs n)
... | a , f = a , l0 n f
G-dn x gx (fc d) (gc G₀ _ _ _ _ _ _ _ _) with G-dn x gx d G₀
... | a , f = a , l0 0 f
G-dn x gx (ni {r = ()} d) b
G-dn x gx (nd {i = ()} d) b
G-dn x gx (eR {stp = ()} d) b
G-dn x gx (eL {stp = ()} d) b
G-dn x gx (rL {j = ()} d) b
G-dn x gx (lL {j = ()} d) b
```

## §2 上下文

`Hd`: 往下搬的两种情形: 同层, 或者异层但 $x$ 的层在 $x'$ 的世界之下, 而且上下文收这个高度 (`Hb`).

```agda
data Hd (Hb : ℕ → Set) (p : ℕ) (a : A) : ℕ → A → A → Set where
  hom : ∀ {u′} → Hd Hb p a p a u′
  het : ∀ {p′ a′ u′} → Hb p → a ⊲ u′ → Hd Hb p a p′ a′ u′

record Cx : Set₁ where
  field
    Hb : ℕ → Set
    Rn : ∀ {p a u} → 𝓞 p a u → ∀ {w} → 𝓡 w → Set
    mn : ∀ {p a u p′ a′ u′ w w′} {x : 𝓞 p a u} {x′ : 𝓞 p′ a′ u′} {y : 𝓡 w} {y′ : 𝓡 w′} → x ⊴ x′ → Rn x y → Rn x′ y′ → y ⊴ y′
    dn : ∀ {p a u p′ a′ u′ w′} {x : 𝓞 p a u} {x′ : 𝓞 p′ a′ u′} {y′ : 𝓡 w′} → Hd Hb p a p′ a′ u′ → Gw u → x ⊴ x′ → u ⊲ u′ → Rn x′ y′ → (d′ : G y′) →
         Σ A λ w → Σ (𝓡 w) λ y → Rn x y × Σ (G y) λ d → force d ⊴₀ force d′
open Cx public

data IdR : ∀ {p a u} → 𝓞 p a u → ∀ {w} → 𝓡 w → Set where
  idr : ∀ {u w} {x : 𝓡 u} (p : u ⊲ w) (g : Gw u) → IdR x (ow p g x)

idC : Cx
Hb idC _ = ⊥
Rn idC = IdR
mn idC d (idr p g) (idr p′ g′) = rw (lw₂ d)
dn idC hom gu d uu (idr p g) (gw b) = let r = G-dn _ gu d b in _ , ow (⊲-tr uu p) gu _ , idr _ gu , gw (proj₁ r) , proj₂ r
dn idC (het () _) gu d uu r b

data Rψ (C : Cx) (q : ℕ) (t : A) {p a u} (x : 𝓞 p a u) {w} (y : 𝓡 w) : Set where
  rψ : (gx : Gw u) (v : A) (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) → Rn C (ψ q t x gx v gv uv tv av) y → Rψ C q t x y

Fψ : Cx → ℕ → A → Cx
Hb (Fψ C q t) _ = ⊤
Rn (Fψ C q t) = Rψ C q t
mn (Fψ C q t) d (rψ gx v gv uv tv av r) (rψ gx′ v′ gv′ uv′ tv′ av′ r′) =
  mn C (ψL′ q t d gx gx′ v gv uv tv av v′ gv′ uv′ tv′ av′) r r′
dn (Fψ C q t) {x = x} hom gu d uu (rψ gx′ v gv uv tv av r) b with
  dn C hom gv (ψL′ q t d gu gx′ v gv (⊲-tr uu uv) tv av v gv uv tv av) C.self r b
... | w , y , r₀ , d₀ , f = w , y , rψ gu v gv (⊲-tr uu uv) tv av r₀ , d₀ , f
dn (Fψ C q t) {x = x} (het _ ae) gu d uu (rψ gx′ v gv uv tv av r) b with
  dn C hom gv (ψL′ q t d gu gx′ v gv (⊲-tr uu uv) tv (⊲-tr ae uv) v gv uv tv av) C.self r b
... | w , y , r₀ , d₀ , f = w , y , rψ gu v gv (⊲-tr uu uv) tv (⊲-tr ae uv) r₀ , d₀ , f

data Ra (C : Cx) {pw aw u₀} (W : 𝓞 pw aw u₀) (gu₀ : Gw u₀) {p a u} (x : 𝓞 p a u) {w} (y : 𝓡 w) : Set where
  ra : (L : Rel p a pw aw) (gx : Gw u) (v : A) (gv : Gw v) (uv : u₀ ⊲ v) (xv : u ⊲ v) (bv : bw L ⊲ v) → Rn C (add W gu₀ L x gx v gv uv xv bv) y → Ra C W gu₀ x y

HbA : ∀ {pw aw u₀} → 𝓞 pw aw u₀ → ℕ → Set
HbA {pw} W p = p <ᴺ pw

Fa : ∀ {pw aw u₀} → Cx → (W : 𝓞 pw aw u₀) (gu₀ : Gw u₀) → W ≈ W → Cx
Hb (Fa C W gu₀ E) = HbA W
Rn (Fa C W gu₀ E) = Ra C W gu₀
mn (Fa C W gu₀ E) d (ra L gx v gv uv xv bv r) (ra L′ gx′ v′ gv′ uv′ xv′ bv′ r′) =
  mn C (AddM.mm2 W gu₀ E d L L′ gx gx′ v gv uv xv bv v′ gv′ uv′ xv′ bv′) r r′
dn (Fa C W gu₀ E) hom gu d uu (ra L gx′ v gv uv xv bv r) b with
  dn C hom gv (AddM.mm2 W gu₀ E d L L gu gx′ v gv uv (⊲-tr uu xv) bv v gv uv xv bv) C.self r b
... | w , y , r₀ , d₀ , f = w , y , ra L gu v gv uv (⊲-tr uu xv) bv r₀ , d₀ , f
dn (Fa C W gu₀ E) (het i ae) gu d uu (ra L gx′ v gv uv xv bv r) b with
  dn C hom gv (AddM.mm2 W gu₀ E d (lw i) L gu gx′ v gv uv (⊲-tr uu xv) (⊲-tr ae xv) v gv uv xv bv) C.self r b
... | w , y , r₀ , d₀ , f = w , y , ra (lw i) gu v gv uv (⊲-tr uu xv) (⊲-tr ae xv) r₀ , d₀ , f
```

## §3 看见

`Sees C q c`: 输入压过 $\Omega_{q,c}$, 则 $c$ 在输出的第一位置上. 这是 `OCF.Free` 的 `CvP`, 这里加了 $1$. `Seen C c`: 不管输入, $c$ 都在输出的第一位置上.

```agda
Sees : Cx → ℕ → A → Set
Sees C q c = ∀ {p a u} (z : 𝓞 p a u) (gz : Gw u) {w} {y : 𝓡 w} → c ⊲ u → Ω̇at q c gz ⊴ z → Rn C z y → (d : G y) → Fp c (force d) × Fp one (force d)

Seen : Cx → A → Set
Seen C c = ∀ {p a u} (z : 𝓞 p a u) {w} {y : 𝓡 w} → Rn C z y → (d : G y) → Fp c (force d)

Fo : ℕ → Cx → Set
Fo q C = ∀ {p′} → p′ <ᴺ q → Seen C one × Hb C p′

record 𝓥 (q : ℕ) (t : A) (C : Cx) : Set₁ where
  constructor vv
  field
    vfo : Fo q C
    vse : ∀ {c} → c ≪ t → Sees C q c
open 𝓥 public

record 𝓥′ (q : ℕ) (t : A) (C : Cx) : Set₁ where
  constructor vt
  field
    vb : 𝓥 q t C
    vs : Sees C q t
open 𝓥′ public
```

`Over h₀ k C′ D`: $C'$ 的每次运行都是 $D$ 在一个压过 $\Omega_{h_0,k}$ 的 $z$ 上的运行. `q₁`: 输入的高度, 决定要 `Hb` 的范围.

```agda
record Ov (h₀ : ℕ) (k : A) (D : Cx) {w} (y : 𝓡 w) : Set where
  constructor ov
  field
    {uz} : A
    z : 𝓞 h₀ k uz
    gz : Gw uz
    kz : k ⊲ uz
    rz : Rn D z y
    ωz : Ω̇at h₀ k gz ⊴ z

record Over (q₁ h₀ : ℕ) (k : A) (C′ D : Cx) : Set where
  constructor over
  field
    ovr : ∀ {p a u} (t : 𝓞 p a u) {w} {y : 𝓡 w} → Rn C′ t y → Ov h₀ k D y
    ovb : ∀ {p′} → p′ <ᴺ q₁ → Hb C′ p′
open Over public

record FlOver {p a u} (x : 𝓞 p a u) (O C″ : Cx) : Set where
  constructor flo
  field
    flr : ∀ {p₂ a₂ u₂} (t : 𝓞 p₂ a₂ u₂) {w} {y : 𝓡 w} → Rn C″ t y → (d : G y) → Σ A λ w₀ → Σ (𝓡 w₀) λ y₀ → Rn O x y₀ × Σ (G y₀) λ d₀ → force d₀ ⊴₀ force d
    flb : ∀ {p′} → p′ <ᴺ p → Hb C″ p′
open FlOver public

Cl : Set₂
Cl = Cx → Set₁

data Im (F : Cx → Cx) (𝓔 : Cl) (D : Cx) : Set₁ where
  im : (C : Cx) → 𝓔 C → D ≡ F C → Im F 𝓔 D

_∧_ : Cl → Cl → Cl
(𝓖 ∧ 𝓑) C = 𝓖 C × 𝓑 C
```

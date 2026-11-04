# 前缀 (一): 高度 0 的世界折叠, 过 `NoCumPre` 的证书

> 入口 [TLPrefix](TLPrefix.lagda.md). 不含记号. 与 [NoCumHnBridge](NoCumHnBridge.lagda.md) 逐行相同, 只把证书换成 [NoCumPre](NoCumPre.lagda.md) 的 `G` (机械改名). `force-Y`: 高度 0 的 $\Omega_v$ 过世界折叠, 任何 `G` 证书的计值都 $\cong$ `Y v`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLPrefixBridge where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
import OCF.Free.Level as FL
open FL using (_≅_; z≅; s≅; l≅)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲; keep; rise; cmpN; rkT; Tg; tgS; lgS)
import OCF.Align.CumReadCF as C
open C using () renaming (O to Oᶜ; Vs to Vsᶜ; Vc to Vcᶜ)
open import OCF.Align.CumReadCFThm using (ord; Y)
open import OCF.Align.NoCumLit using (Ord₀; _≈ᴬ_; ≈ᴬ-refl)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq using (clash)
open import OCF.Align.NoCumPre using (𝓡; G; g0; gs; gl; gw; gc; force)
```

## §1 关系

```agda
module _ (a : A) (S< : ∀ {b} (R : Strict b a) {u} → Vs zero a R u → Oᶜ b → Set) where
  data Sq₊ : ∀ {u} → 𝓞 zero a u → Oᶜ a → Set where
    qz : ∀ {u} → Sq₊ {u} o0 C.o0
    qs : ∀ {u} {x : 𝓞 zero a u} {y} → Sq₊ x y → Sq₊ (os x) (C.os y)
    qL : ∀ {u} {F : ℕ → 𝓞 zero a u} {H} → (∀ n → Sq₊ (F n) (H n)) → Sq₊ (ol F) (C.ol H)
    qi : ∀ {u k} {r r′ : k ≪ a} {h : ∀ {v} → u ⊲ v → Gw v → Vs zero a (≪S r) v → 𝓞 zero a v} {h′ : Vsᶜ a (≪S r′) → Oᶜ a} →
         (∀ {v} (w : u ⊲ v) (g : Gw v) (z : 𝓞 zero k v) (z′ : Oᶜ k) → S< (≪S r) (inS (≪S r) z) z′ → Sq₊ (h w g (inS (≪S r) z)) (h′ (C.inS (≪S r′) z′))) →
         Sq₊ (oi r h) (C.oi r′ h′)
    qe : ∀ {u b} {R : Strict b a} (stp : Stp R) {x : Vs zero a R u} {y : Vsᶜ a R} → S< R x (C.outS R y) → Sq₊ (oe stp x) (C.oe R y)
    qw : ∀ {u v} {p : u ⊲ v} {g : Gw u} {x : 𝓞 zero a u} {y} → Sq₊ x y → Sq₊ (ow p g x) y

Sq : ∀ {a u} → 𝓞 zero a u → Oᶜ a → Set
SS : ∀ a {b} (R : Strict b a) {u} → Vs zero a R u → Oᶜ b → Set
SC : ∀ c {b} (P : b ⊲ c) {u} → Vc zero c P u → Oᶜ b → Set
Sq {a} = Sq₊ a (SS a)
SS (asuc c) (ss P) x y = SC c P x y
SS (alim f) (sl n P) x y = SC (f n) P x y
SC c C.self x y = Sq x y
SC (asuc c) (C.suc P) x y = SC c P x y
SC (alim f) (C.lim n P) x y = SC (f n) P x y

C→Q : ∀ {c b u} (P : b ⊲ c) {x : 𝓞 zero b u} {y : Oᶜ b} → SC c P (inC P x) y → Sq x y
C→Q C.self d = d
C→Q (C.suc P) d = C→Q P d
C→Q (C.lim n P) d = C→Q P d

Q→C : ∀ {c b u} (P : b ⊲ c) {x : 𝓞 zero b u} {y : Oᶜ b} → Sq x y → SC c P (inC P x) y
Q→C C.self d = d
Q→C (C.suc P) d = Q→C P d
Q→C (C.lim n P) d = Q→C P d

S→Q : ∀ {c b u} (R : Strict b c) {x : 𝓞 zero b u} {y : Oᶜ b} → SS c R (inS R x) y → Sq x y
S→Q (ss P) d = C→Q P d
S→Q (sl n P) d = C→Q P d

Q→S : ∀ {c b u} (R : Strict b c) {x : 𝓞 zero b u} {y : Oᶜ b} → Sq x y → SS c R (inS R x) y
Q→S (ss P) d = Q→C P d
Q→S (sl n P) d = Q→C P d
```

## §2 $\Omega$, 加法, 倍数

```agda
Q-Ω : ∀ a → Sq (Ω̇ zero a) (C.Ω̇ a)
Q-Ω azero = qs qz
Q-Ω (asuc c) = qi (λ w g z z′ d → qe es d)
Q-Ω (alim f) = qL (λ n → qe (el n) (Q-Ω (f n)))

Q-Ωat : ∀ a {v} (g : Gw v) → Sq (Ω̇at zero a g) (C.Ω̇ a)
Q-Ωat a g = qw (Q-Ω a)

Q-add  : ∀ {a b u₀ u′} {W : 𝓞 zero a u₀} {W′ : Oᶜ a} (gu : Gw u₀) (P : b ⊲ a) (P′ : b ⊲ a) {x : 𝓞 zero b u′} {x′ : Oᶜ b} (gx : Gw u′) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : u′ ⊲ v) (bv : azero ⊲ v) → Sq W W′ → Sq x x′ → Sq (add W gu (sa P) x gx v gv uv xv bv) (C.add W′ P′ x′)
Q-add⁰ : ∀ {a b u₀ u′} {W : 𝓞 zero a u₀} {W′ : Oᶜ a} (gu : Gw u₀) (P : b ⊲ a) (P′ : b ⊲ a) {x : 𝓞 zero b u′} {x′ : Oᶜ b} (gx : Gw u′) m (gm : Gw m) (um : u₀ ⊲ m) (tm : u′ ⊲ m) (am : azero ⊲ m) → Sq W W′ → Sq x x′ → Sq (add⁰ W gu (sa P) x gx m gm um tm am) (C.add W′ P′ x′)

Q-add gu P P′ gx v gv uv xv bv dW dx with mx gu gv uv xv bv
... | mx′ m gm um tm am mv = qw (Q-add⁰ gu P P′ gx m gm um tm am dW dx)

Q-add⁰ gu P P′ gx m gm um tm am dW qz = qw dW
Q-add⁰ gu P P′ gx m gm um tm am dW (qs d) = qs (Q-add gu P P′ gx m gm um tm am dW d)
Q-add⁰ gu P P′ gx m gm um tm am dW (qL h) = qL (λ n → Q-add gu P P′ gx m gm um tm am dW (h n))
Q-add⁰ {W = W} {W′ = W′} gu P P′ gx m gm um tm am dW (qi {r = r} {r′ = r′} {h = h} {h′ = h′} H) =
  qi (λ {v} w g z z′ d →
    subst₂ (λ s s′ → Sq (add W gu (sa P) (h (⊲-tr tm w) g (inS (≪S r) s)) g v g (⊲-tr um w) C.self (z⊲ v)) (C.add W′ P′ (h′ (C.inS (≪S r′) s′))))
           (sym (out-inS (≪S (≪∘ r P)) z)) (sym (C.out-inS (≪S (≪∘ r′ P′)) z′))
           (Q-add gu P P′ g v g (⊲-tr um w) C.self (z⊲ v) dW (H (⊲-tr tm w) g z z′ (Q→S (≪S r) (S→Q (≪S (≪∘ r P)) d)))))
Q-add⁰ gu P P′ gx m gm um tm am dW (qe es d) = Q-add gu _ _ gx m gm um tm am dW d
Q-add⁰ gu P P′ gx m gm um tm am dW (qe (el n) d) = Q-add gu _ _ gx m gm um tm am dW d
Q-add⁰ gu P P′ gx m gm um tm am dW (qw {p = p} {g = g′} d) = Q-add gu P P′ g′ m gm um (⊲-tr p tm) am dW d

Q-rep : ∀ {t u} {y : 𝓞 zero t u} {y′ : Oᶜ t} (g : Gw u) → Sq y y′ → ∀ n → Sq (rep y g n) (C.rep y′ n)
Q-rep g d zero = qz
Q-rep g d (suc zero) = d
Q-rep {u = u} g d (suc (suc m)) = Q-add g C.self C.self g u g C.self C.self (z⊲ u) (Q-rep g d (suc m)) d
```

## §3 折叠

```agda
Q-ψ  : ∀ {a u t} {x : 𝓞 zero a u} {x′ : Oᶜ a} (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) (T : Tg t a) (w : Lg a) → Sq x x′ → Sq (ψ zero t x gu v gv uv tv av) (C.ψ t T w x′)
Q-ψ⁰ : ∀ {a u t} {x : 𝓞 zero a u} {x′ : Oᶜ a} (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) (T : Tg t a) (w : Lg a) → Sq x x′ → Sq (ψ⁰ zero t x gu m gm um tm am) (C.ψ t T w x′)

Q-ψ gu v gv uv tv av T w d with mx gu gv uv tv av
... | mx′ m gm um tm am mv = qw (Q-ψ⁰ gu m gm um tm am T w d)

Q-ψ⁰ {t = t} gu m gm um tm am T w qz = Q-Ωat t gm
Q-ψ⁰ gu m gm um tm am T w (qs d) = qL (Q-rep gm (Q-ψ gu m gm um tm am T w d))
Q-ψ⁰ gu m gm um tm am T w (qL h) = qL (λ n → Q-ψ gu m gm um tm am T w (h n))
Q-ψ⁰ {a = a} {t = t} gu m gm um tm am T w (qi {k = k} {r = r} {r′ = r′} {h = h} {h′ = h′} H) with cmpN (≪∘ r am) tm (lgw gm) | rkT r′ T w
... | keep s₁ | keep s₂ =
  qi (λ {v} w₁ g z z′ d →
    subst₂ (λ s s′ → Sq (ψ zero t (h (⊲-tr um w₁) g (inS (≪S r) s)) g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁)) (C.ψ t T w (h′ (C.inS (≪S r′) s′))))
           (sym (out-inS (≪S s₁) z)) (sym (C.out-inS (≪S s₂) z′))
           (Q-ψ g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) T w (H (⊲-tr um w₁) g z z′ (Q→S (≪S r) (S→Q (≪S s₁) d)))))
... | keep s₁ | rise q = ⊥-elim (clash s₁ q (≈ᴬ-refl k) (≈ᴬ-refl t))
... | rise q | keep s₂ = ⊥-elim (clash s₂ q (≈ᴬ-refl k) (≈ᴬ-refl t))
... | rise _ | rise _ = qL (λ n → Q-ψ gm m gm C.self tm am T w (H um gm _ _ (Q→S (≪S r) (chain n))))
  where
  chain : ∀ n → Sq (chainᵒ gm (λ z₁ → ψ zero k (h um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n)
                   (C.chainᵒ (λ z → C.ψ k (inj₁ (≪⊲ r′)) w (h′ (C.inS (≪S r′) z))) n)
  chain zero = Q-Ωat k gm
  chain (suc n) = Q-ψ gm m gm C.self (⊲-tr (≪⊲ r) am) am (inj₁ (≪⊲ r′)) w (H um gm _ _ (Q→S (≪S r) (chain n)))
Q-ψ⁰ gu m gm um tm am T w (qe es d) = Q-ψ gu m gm um tm _ _ _ d
Q-ψ⁰ gu m gm um tm am T w (qe (el n) d) = Q-ψ gu m gm um tm _ _ _ d
Q-ψ⁰ gu m gm um tm am T w (qw {p = p} {g = g′} d) = Q-ψ g′ m gm (⊲-tr p um) tm am T w d
```

## §4 第 0 层, 计值

```agda
Q-force : ∀ {u} {t : 𝓡 u} {t′ : Oᶜ azero} → Sq t t′ → (d : G t) → force d ≅ ord t′
Q-force qz g0 = z≅
Q-force (qs e) (gs d) = s≅ (Q-force e d)
Q-force (qL h) (gl Gs _) = l≅ (λ n → Q-force (h n) (Gs n))
Q-force (qw e) (gw d) = Q-force e d
Q-force (qi {r = ()} _) d
Q-force (qe () _) d

force-Y : ∀ {u v m} (e : v ⊲ u) (y : 𝓞 zero v u) (gu : Gw u) (gm : Gw m) (um : u ⊲ m) (tm : azero ⊲ m) (am : azero ⊲ m) (w : Lg v) → Sq y (C.Ω̇ v) →
          (d : G (ψ zero azero (oL {p = suc zero} {a = azero} zero v e y) gu m gm um tm am)) → force d ≅ Y v w
force-Y {v = v} e y gu gm um tm am w q d with mx gu gm um tm am
force-Y {v = v} e y gu gm um tm am w q (gw d) | mx′ m₁ g₁ u₁ t₁ a₁ _ =
  Q-force (Q-ψ gu m₁ g₁ u₁ t₁ (⊲-tr e u₁) (inj₁ (z⊲ v)) w q) d
```

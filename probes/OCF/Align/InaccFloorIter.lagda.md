# 字面上界: $\psi_1$ 作层号上的函数

> 不含记号. 结论写在 [InaccFloor](InaccFloor.lagda.md). 全部在世界 $\ell$ 里. `P̂` 是 Lv 上的自函数, 不是语法的一层; `WFP̂` 说它保持证书, 证明只对 $x$ 结构递归, 不用 `Acc`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.InaccFloorIter where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.InaccTreeBase hiding (res; res⁻; tr; tr⁻; ι; up; steps; _≺_; _⊑_; via)
open import OCF.Align.Level using
  (Ordᴵ; _<ᴵ_; _≅ᴵ_; _⊑ᴵ_; _≺ᴵ_; via; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑; <ᴵ-dec)
open import OCF.Align.InaccFloorBase
```

## §1 层号的加法

`_⊕_` 是 `add` 的层号版.

```agda
infixl 6 _⊕_
_⊕_ : Lv → Lv → Lv
M ⊕ zero     = M
M ⊕ suc x    = suc (M ⊕ x)
M ⊕ lim h    = lim (λ n → M ⊕ h n)
M ⊕ limᴼ k g = limᴼ k (λ x → M ⊕ g x)

≈⊕ : ∀ {a a′ b b′} → a ≈ a′ → b ≈ b′ → (a ⊕ b) ≈ (a′ ⊕ b′)
≈⊕ e z≈     = e
≈⊕ e (s≈ d) = s≈ (≈⊕ e d)
≈⊕ e (l≈ h) = l≈ (λ n → ≈⊕ e (h n))
≈⊕ e (o≈ h) = o≈ (λ x → ≈⊕ e (h x))

rp : Lv → ℕ → Lv
rp M zero    = zero
rp M (suc n) = M ⊕ rp M n

rp≈ : ∀ {x y} → x ≈ y → ∀ n → rp x n ≈ rp y n
rp≈ e zero    = z≈
rp≈ e (suc n) = ≈⊕ e (rp≈ e n)

L₁ : Lv
L₁ = times zero

P̂ : Lv → Lv
P̂ zero       = L₁
P̂ (suc x)    = lim (rp (P̂ x))
P̂ (lim h)    = lim (λ n → P̂ (h n))
P̂ (limᴼ k g) = limᴼ k (λ x → P̂ (g x))

P̂≈ : ∀ {a b} → a ≈ b → P̂ a ≈ P̂ b
P̂≈ z≈     = ≈-refl _
P̂≈ (s≈ e) = l≈ (rp≈ (P̂≈ e))
P̂≈ (l≈ h) = l≈ (λ n → P̂≈ (h n))
P̂≈ (o≈ h) = o≈ (λ x → P̂≈ (h x))

Ψ₁Ω₁ : Lv
Ψ₁Ω₁ = P̂ L₁

Pit : ℕ → Lv
Pit zero    = Ψ₁Ω₁
Pit (suc n) = P̂ (Pit n)

Ψ₁Ω₂ : Lv
Ψ₁Ω₂ = lim Pit
```

## §2 证书

`W₀` 是证书的弱部分: 每个 `limᴼ` 有一个可容许的分支, 其上有 0. 所有的单调性只要它, 不要步进, 所以 `P̂⊑` 不与 `WFP̂` 互递归.

```agda
module Iter (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) where
  open World ℓ one

  W₀ : Lv → Set
  W₀ zero       = ⊤
  W₀ (suc k)    = W₀ k
  W₀ (lim f)    = ∀ n → W₀ (f n)
  W₀ (limᴼ k g) = (Σ (Ordᴸ k) λ x₀ → Aℓ ℓ k x₀ × zero ≺ᴬ g x₀) × (∀ x → Aℓ ℓ k x → W₀ (g x))

  w₀ : ∀ c → WFᴬ c → W₀ c
  w₀ zero    _ = tt
  w₀ (suc k) w = w₀ k w
  w₀ (lim f) (_ , w) n = w₀ (f n) (w n)
  w₀ (limᴼ zero g) (_ , (x₀ , ax , h , _) , w) = (x₀ , ax , h) , (λ x a → w₀ (g x) (w x a))
  w₀ (limᴼ (suc _) g) (_ , (_ , () , _) , _)
  w₀ (limᴼ (lim _) g) (_ , (_ , () , _) , _)
  w₀ (limᴼ (limᴼ _ _) g) (_ , (_ , () , _) , _)

  W₀-at : ∀ c → W₀ c → (r : Pre c) → Adm c r → W₀ (at c r)
  W₀-at (suc k) w (inj₁ _) _ = w
  W₀-at (suc k) w (inj₂ r) d = W₀-at k w r d
  W₀-at (lim f) w (n , r) d = W₀-at (f n) (w n) r d
  W₀-at (limᴼ zero g) _ (inj₁ (inj₁ _)) _ = tt
  W₀-at (limᴼ (suc _) g) ((_ , () , _) , _) (inj₁ _) _
  W₀-at (limᴼ (lim _) g) ((_ , () , _) , _) (inj₁ _) _
  W₀-at (limᴼ (limᴼ _ _) g) ((_ , () , _) , _) (inj₁ _) _
  W₀-at (limᴼ k g) (_ , w) (inj₂ (x , r)) (a , d) = W₀-at (g x) (w x a) r d

  wS : ∀ {a b} → a ≺ᴬ b → a ≺ᴬ suc b
  wS (viaᴬ r d e) = viaᴬ (inj₂ r) d e
  wL : ∀ {a h} n → a ≺ᴬ h n → a ≺ᴬ lim h
  wL n (viaᴬ r d e) = viaᴬ (n , r) d e
  wO : ∀ {a k g} x → Aℓ ℓ k x → a ≺ᴬ g x → a ≺ᴬ limᴼ k g
  wO x ax (viaᴬ r d e) = viaᴬ (inj₂ (x , r)) (ax , d) e

  inL⊕ : ∀ M y → W₀ y → M ⊑ᴬ (M ⊕ y)
  inL⊕ M zero w r d = viaᴬ r d (≈-refl _)
  inL⊕ M (suc y) w r d = wS (inL⊕ M y w r d)
  inL⊕ M (lim h) w r d = wL 0 (inL⊕ M (h 0) (w 0) r d)
  inL⊕ M (limᴼ k g) ((x₀ , ax , _) , w) r d = wO x₀ ax (inL⊕ M (g x₀) (w x₀ ax) r d)

  tail : ∀ M y → W₀ y → (s : Pre y) → Adm y s → (M ⊕ at y s) ≺ᴬ (M ⊕ y)
  tail M (suc y) w (inj₁ _) _ = viaᴬ (inj₁ tt) tt (≈-refl _)
  tail M (suc y) w (inj₂ s) d = wS (tail M y w s d)
  tail M (lim h) w (n , s) d = wL n (tail M (h n) (w n) s d)
  tail M (limᴼ zero g) ((x₀ , ax , viaᴬ s₀ d₀ e₀) , w) (inj₁ (inj₁ _)) _ =
    wO x₀ ax (≺ᴬ-respˡ (≈⊕ (≈-refl M) e₀) (tail M (g x₀) (w x₀ ax) s₀ d₀))
  tail M (limᴼ (suc _) g) ((_ , () , _) , _) (inj₁ _) _
  tail M (limᴼ (lim _) g) ((_ , () , _) , _) (inj₁ _) _
  tail M (limᴼ (limᴼ _ _) g) ((_ , () , _) , _) (inj₁ _) _
  tail M (limᴼ k g) (_ , w) (inj₂ (x , s)) (a , d) = wO x a (tail M (g x) (w x a) s d)

  -- 两侧单调. 左边必须 ≈
  both : ∀ {x y} → x ≈ y → zero ≺ᴬ y → ∀ v → W₀ v → ∀ u → W₀ u → u ⊑ᴬ v → (x ⊕ u) ⊑ᴬ (y ⊕ v)
  both {y = y} xy h0 v wv zero wu σ r d with ≈⊑ xy r d
  ... | viaᴬ r′ d′ e′ = ≺ᴬ-respˡ e′ (inL⊕ y v wv r′ d′)
  both {x} {y} xy h0 v wv (suc u) wu σ (inj₁ _) _ with σ (inj₁ tt) tt
  ... | viaᴬ s ds e = ≺ᴬ-respˡ (≈⊕ xy e) (tail y v wv s ds)
  both xy h0 v wv (suc u) wu σ (inj₂ r) d = both xy h0 v wv u wu (λ r′ d′ → σ (inj₂ r′) d′) r d
  both xy h0 v wv (lim h) wu σ (n , r) d = both xy h0 v wv (h n) (wu n) (λ r′ d′ → σ (n , r′) d′) r d
  both {y = y} xy h0 v wv (limᴼ zero g) _ σ (inj₁ (inj₁ _)) _ = ≺⊑ h0 (inL⊕ y v wv)
  both xy h0 v wv (limᴼ (suc _) g) ((_ , () , _) , _) σ (inj₁ _) _
  both xy h0 v wv (limᴼ (lim _) g) ((_ , () , _) , _) σ (inj₁ _) _
  both xy h0 v wv (limᴼ (limᴼ _ _) g) ((_ , () , _) , _) σ (inj₁ _) _
  both xy h0 v wv (limᴼ k g) (_ , wu) σ (inj₂ (z , r)) (az , d) =
    both xy h0 v wv (g z) (wu z az) (λ r′ d′ → σ (inj₂ (z , r′)) (az , d′)) r d

  monoR : ∀ M → zero ≺ᴬ M → ∀ v → W₀ v → ∀ u → W₀ u → u ⊑ᴬ v → (M ⊕ u) ⊑ᴬ (M ⊕ v)
  monoR M h0 = both (≈-refl M) h0

  W₀⊕ : ∀ M → W₀ M → zero ≺ᴬ M → ∀ x → W₀ x → W₀ (M ⊕ x)
  W₀⊕ M wM h0 zero w = wM
  W₀⊕ M wM h0 (suc x) w = W₀⊕ M wM h0 x w
  W₀⊕ M wM h0 (lim h) w n = W₀⊕ M wM h0 (h n) (w n)
  W₀⊕ M wM h0 (limᴼ k g) ((x₀ , ax , _) , w) =
    (x₀ , ax , ≺⊑ h0 (inL⊕ M (g x₀) (w x₀ ax))) , (λ x a → W₀⊕ M wM h0 (g x) (w x a))

  W₀rp : ∀ M → W₀ M → zero ≺ᴬ M → ∀ n → W₀ (rp M n)
  W₀rp M wM h0 zero    = tt
  W₀rp M wM h0 (suc n) = W₀⊕ M wM h0 (rp M n) (W₀rp M wM h0 n)

  WF⊕ : ∀ M → WFᴬ M → zero ≺ᴬ M → ∀ x → WFᴬ x → WFᴬ (M ⊕ x)
  WF⊕ M wM h0 zero w = wM
  WF⊕ M wM h0 (suc x) w = WF⊕ M wM h0 x w
  WF⊕ M wM h0 (lim h) (st , w) =
    (λ n → monoR M h0 (h (suc n)) (w₀ _ (w (suc n))) (h n) (w₀ _ (w n)) (st n)) , (λ n → WF⊕ M wM h0 (h n) (w n))
  WF⊕ M wM h0 (limᴼ zero g) (dir , (x₀ , ax , _) , w) =
    dir′ , (x₀ , ax , ≺⊑ h0 (inL⊕ M (g x₀) (w₀ _ (w x₀ ax))) , (λ ())) , (λ x a → WF⊕ M wM h0 (g x) (w x a))
    where
    dir′ : ∀ x y → Aℓ ℓ zero x → Aℓ ℓ zero y → Σ (Ordᴸ zero) λ z → Aℓ ℓ zero z × (M ⊕ g x) ⊑ᴬ (M ⊕ g z) × (M ⊕ g y) ⊑ᴬ (M ⊕ g z)
    dir′ x y a b with dir x y a b
    ... | z , az , gx , gy =
      z , az , monoR M h0 (g z) (w₀ _ (w z az)) (g x) (w₀ _ (w x a)) gx ,
               monoR M h0 (g z) (w₀ _ (w z az)) (g y) (w₀ _ (w y b)) gy
  WF⊕ M wM h0 (limᴼ (suc _) g) (_ , (_ , () , _) , _)
  WF⊕ M wM h0 (limᴼ (lim _) g) (_ , (_ , () , _) , _)
  WF⊕ M wM h0 (limᴼ (limᴼ _ _) g) (_ , (_ , () , _) , _)

  WFrp : ∀ M → WFᴬ M → zero ≺ᴬ M → ∀ n → WFᴬ (rp M n)
  WFrp M wM h0 zero    = tt
  WFrp M wM h0 (suc n) = WF⊕ M wM h0 (rp M n) (WFrp M wM h0 n)

  steprp : ∀ M → W₀ M → zero ≺ᴬ M → ∀ n → rp M n ⊑ᴬ rp M (suc n)
  steprp M wM h0 zero    = λ ()
  steprp M wM h0 (suc n) =
    monoR M h0 (rp M (suc n)) (W₀rp M wM h0 (suc n)) (rp M n) (W₀rp M wM h0 n) (steprp M wM h0 n)

  rp⊑ : ∀ {x y} → x ≈ y → W₀ x → zero ≺ᴬ x → W₀ y → zero ≺ᴬ y → ∀ n → rp x n ⊑ᴬ rp y n
  rp⊑ xy wx hx wy hy zero    = λ ()
  rp⊑ {x} {y} xy wx hx wy hy (suc n) =
    both xy hy (rp y n) (W₀rp y wy hy n) (rp x n) (W₀rp x wx hx n) (rp⊑ xy wx hx wy hy n)
```

## §3 $\psi_1$ 保持证书

`rpb` 与 `P̂⊑`: Bachmann 性质的第 1 层版. `WFP̂`: 证书的闭包定理.

```agda
  z≺L₁ : zero ≺ᴬ L₁
  z≺L₁ = viaᴬ (inj₁ (inj₁ tt)) tt z≈

  x₁ : Aℓ ℓ zero (suc zero)
  x₁ = suc zero , one , refl

  W₀⊞ : ∀ a → W₀ (zero ⊞ em a)
  W₀⊞ zero = tt
  W₀⊞ (suc a) = W₀⊞ a
  W₀⊞ (lim f _) n = W₀⊞ (f n)

  W₀L₁ : W₀ L₁
  W₀L₁ = (suc zero , x₁ , viaᴬ (inj₁ tt) tt z≈) , λ { _ (a , _ , refl) → W₀⊞ a }

  WFL₁ : WFᴬ L₁
  WFL₁ = WF-times tt (viaᴬ (inj₁ tt) tt z≈)

  base⊑ : ∀ y → W₀ y → L₁ ⊑ᴬ P̂ y
  base⊑ zero w r d = viaᴬ r d (≈-refl _)
  base⊑ (suc y) w r d = wL 1 (base⊑ y w r d)
  base⊑ (lim h) w r d = wL 0 (base⊑ (h 0) (w 0) r d)
  base⊑ (limᴼ k g) ((x₀ , ax , _) , w) r d = wO x₀ ax (base⊑ (g x₀) (w x₀ ax) r d)

  H0P̂ : ∀ y → W₀ y → zero ≺ᴬ P̂ y
  H0P̂ y w = ≺⊑ z≺L₁ (base⊑ y w)

  W₀P̂ : ∀ y → W₀ y → W₀ (P̂ y)
  W₀P̂ zero w = W₀L₁
  W₀P̂ (suc y) w n = W₀rp (P̂ y) (W₀P̂ y w) (H0P̂ y w) n
  W₀P̂ (lim h) w n = W₀P̂ (h n) (w n)
  W₀P̂ (limᴼ k g) ((x₀ , ax , _) , w) =
    (x₀ , ax , H0P̂ (g x₀) (w x₀ ax)) , (λ x a → W₀P̂ (g x) (w x a))

  ≈0 : ∀ {c} → zero ≈ c → c ≡ zero
  ≈0 z≈ = refl

  rpb : ∀ y → W₀ y → (s : Pre y) → Adm y s → ∀ n → rp (P̂ (at y s)) n ⊑ᴬ P̂ y
  rpb (suc y) w (inj₁ _) _ n r d = viaᴬ (n , r) d (≈-refl _)
  rpb (suc y) w (inj₂ s) d′ n r d = wL 1 (rpb y w s d′ n r d)
  rpb (lim h) w (k , s) d′ n r d = wL k (rpb (h k) (w k) s d′ n r d)
  rpb (limᴼ zero g) ((x₀ , ax , viaᴬ s₀ d₀ e₀) , w) (inj₁ (inj₁ _)) _ n r d =
    wO x₀ ax (subst (λ c → rp (P̂ c) n ⊑ᴬ P̂ (g x₀)) (≈0 e₀) (rpb (g x₀) (w x₀ ax) s₀ d₀ n) r d)
  rpb (limᴼ (suc _) g) ((_ , () , _) , _) (inj₁ _) _ n
  rpb (limᴼ (lim _) g) ((_ , () , _) , _) (inj₁ _) _ n
  rpb (limᴼ (limᴼ _ _) g) ((_ , () , _) , _) (inj₁ _) _ n
  rpb (limᴼ k g) (_ , w) (inj₂ (x , s)) (a , d′) n r d = wO x a (rpb (g x) (w x a) s d′ n r d)

  P̂⊑ : ∀ x → W₀ x → ∀ y → W₀ y → x ⊑ᴬ y → P̂ x ⊑ᴬ P̂ y
  P̂⊑ zero wx y wy σ = base⊑ y wy
  P̂⊑ (suc x) wx y wy σ (n , r) d with σ (inj₁ tt) tt
  ... | viaᴬ s ds e =
    let wa = W₀-at y wy s ds
        k  = rp⊑ (P̂≈ e) (W₀P̂ x wx) (H0P̂ x wx) (W₀P̂ _ wa) (H0P̂ _ wa) n
    in ⊑ᴬ-trans k (rpb y wy s ds n) r d
  P̂⊑ (lim h) wx y wy σ (n , r) d = P̂⊑ (h n) (wx n) y wy (λ r′ d′ → σ (n , r′) d′) r d
  P̂⊑ (limᴼ zero g) _ y wy σ (inj₁ (inj₁ _)) _ = H0P̂ y wy
  P̂⊑ (limᴼ (suc _) g) ((_ , () , _) , _) _ _ _ (inj₁ _) _
  P̂⊑ (limᴼ (lim _) g) ((_ , () , _) , _) _ _ _ (inj₁ _) _
  P̂⊑ (limᴼ (limᴼ _ _) g) ((_ , () , _) , _) _ _ _ (inj₁ _) _
  P̂⊑ (limᴼ k g) (_ , wx) y wy σ (inj₂ (z , r)) (az , d) =
    P̂⊑ (g z) (wx z az) y wy (λ r′ d′ → σ (inj₂ (z , r′)) (az , d′)) r d

  WFP̂ : ∀ x → WFᴬ x → WFᴬ (P̂ x)
  WFP̂ zero _ = WFL₁
  WFP̂ (suc x) w =
    steprp (P̂ x) (W₀P̂ x (w₀ _ w)) (H0P̂ x (w₀ _ w)) , WFrp (P̂ x) (WFP̂ x w) (H0P̂ x (w₀ _ w))
  WFP̂ (lim h) (st , w) =
    (λ n → P̂⊑ (h n) (w₀ _ (w n)) (h (suc n)) (w₀ _ (w (suc n))) (st n)) , (λ n → WFP̂ (h n) (w n))
  WFP̂ (limᴼ zero g) (dir , (x₀ , ax , _) , w) =
    dir′ , (x₀ , ax , H0P̂ (g x₀) (w₀ _ (w x₀ ax)) , (λ ())) , (λ x a → WFP̂ (g x) (w x a))
    where
    dir′ : ∀ x y → Aℓ ℓ zero x → Aℓ ℓ zero y → Σ (Ordᴸ zero) λ z → Aℓ ℓ zero z × P̂ (g x) ⊑ᴬ P̂ (g z) × P̂ (g y) ⊑ᴬ P̂ (g z)
    dir′ x y a b with dir x y a b
    ... | z , az , gx , gy =
      z , az , P̂⊑ (g x) (w₀ _ (w x a)) (g z) (w₀ _ (w z az)) gx ,
               P̂⊑ (g y) (w₀ _ (w y b)) (g z) (w₀ _ (w z az)) gy
  WFP̂ (limᴼ (suc _) g) (_ , (_ , () , _) , _)
  WFP̂ (limᴼ (lim _) g) (_ , (_ , () , _) , _)
  WFP̂ (limᴼ (limᴼ _ _) g) (_ , (_ , () , _) , _)

  WFPit : ∀ n → WFᴬ (Pit n)
  WFPit zero    = WFP̂ L₁ WFL₁
  WFPit (suc n) = WFP̂ (Pit n) (WFPit n)

  stepPit : ∀ n → Pit n ⊑ᴬ Pit (suc n)
  stepPit zero    = P̂⊑ L₁ W₀L₁ (P̂ L₁) (W₀P̂ L₁ W₀L₁) (base⊑ L₁ W₀L₁)
  stepPit (suc n) = P̂⊑ (Pit n) (w₀ _ (WFPit n)) (Pit (suc n)) (w₀ _ (WFPit (suc n))) (stepPit n)

  -- θ = 1, 2 处的证书
  WF-Ψ₁Ω₁ : WFᴬ Ψ₁Ω₁
  WF-Ψ₁Ω₁ = WFP̂ L₁ WFL₁

  WF-Ψ₁Ω₂ : WFᴬ Ψ₁Ω₂
  WF-Ψ₁Ω₂ = stepPit , WFPit

  -- 定理: ψ₁(Ω₂) 之下的字面比较. `Syn` 里没有这个层号
  cmp-Ψ₁Ω₂ : (p q : Pre Ψ₁Ω₂) → Adm Ψ₁Ω₂ p → Adm Ψ₁Ω₂ q → Tri (at Ψ₁Ω₂ p) (at Ψ₁Ω₂ q)
  cmp-Ψ₁Ω₂ = <-decᴬ Ψ₁Ω₂ WF-Ψ₁Ω₂
```

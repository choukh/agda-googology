# 只剩世界前缀: 无条件的版本

> 不含记号. [NoCumForce](NoCumForce.lagda.md) 的链点是输出的读出, 要 `Hn`. 这里把链点改成 $u+\mathrm{rd}\,y$: **只留世界前缀 $u+$**, 没有 `cumA`, 没有 `asuc`, 没有 $\eta+$ (不是链上累加, 每个链点只前缀一次世界), 极限的基本列不累加 (`lit`). 守卫由 `⊞-fst` 字面给出.
>
> `HS-Tᵖ` 对一切 $p$, $a$ 无条件. **这不是作者要的终点**: 前缀 $u+$ 还在, 第 $k$ 项仍可能高于不累加的树. 它量出累加的职责只剩守卫这一件.
>
> 全文 `--safe --without-K --lossy-unification`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumPre where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
import OCF.Free.Level as FL
open FL using (HS; _≅_; z≅; s≅; l≅)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; ⊲-tr; z⊲; lg⊲; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumPsi
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain

𝓡 : A → Set
𝓡 u = 𝓞 zero azero u

outs : Ord₀ → (ℕ → Ord₀) → ℕ → Ord₀
outs y₀ F zero = y₀
outs y₀ F (suc n) = F n
```

## §0 前缀

```agda
infixl 6 _⊞_
_⊞_ : A → A → A
a ⊞ azero = a
a ⊞ asuc b = asuc (a ⊞ b)
a ⊞ alim f = alim (λ n → a ⊞ f n)

⊞-fst : ∀ a b → a ⊲ a ⊞ b
⊞-fst a azero = C.self
⊞-fst a (asuc b) = C.suc (⊞-fst a b)
⊞-fst a (alim f) = C.lim 0 (⊞-fst a (f 0))

⊞-⊲ : ∀ a {x y} → x ⊲ y → a ⊞ x ⊲ a ⊞ y
⊞-⊲ a C.self = C.self
⊞-⊲ a (C.suc q) = C.suc (⊞-⊲ a q)
⊞-⊲ a (C.lim n q) = C.lim n (⊞-⊲ a q)

Lg-⊞ : ∀ a b → Lg a → Lg b → Lg (a ⊞ b)
Lg-⊞ a azero u v = u
Lg-⊞ a (asuc b) u v = Lg-⊞ a b u v
Lg-⊞ a (alim f) u (st , v) = (λ n → ⊞-⊲ a (st n)) , (λ n → Lg-⊞ a (f n) u (v n))

⊞≈ : ∀ {a a′ b b′} → a ≈ᴬ a′ → b ≈ᴬ b′ → a ⊞ b ≈ᴬ a′ ⊞ b′
⊞≈ e z≈ = e
⊞≈ e (s≈ d) = s≈ (⊞≈ e d)
⊞≈ e (l≈ h) = l≈ (λ n → ⊞≈ e (h n))
```

## §1 证书与计值

```agda
data G : ∀ {u} → 𝓡 u → Set
force : ∀ {u} {x : 𝓡 u} → G x → Ord₀

data G where
  g0 : ∀ {u} → G {u} o0
  gs : ∀ {u} {x : 𝓡 u} → G x → G (os x)
  gl : ∀ {u} {F : ℕ → 𝓡 u} (Gs : ∀ n → G (F n)) → (∀ n → force (Gs n) ⊴₀ force (Gs (suc n))) → G (ol F)
  gw : ∀ {u v} {p : u ⊲ v} {g : Gw u} {x : 𝓡 u} → G x → G (ow p g x)
  gc : ∀ {u} {x : 𝓡 u} {h : ∀ {v} → u ⊲ v → Gw v → 𝓡 v} (G₀ : G x)
       (vs : ℕ → A) (gv : ∀ n → Gw (vs n)) (up : ∀ n → u ⊲ vs n) (Gh : ∀ n → G (h (up n) (gv n))) →
       vs 0 ≈ᴬ u ⊞ rd (force G₀) → (∀ n → vs (suc n) ≈ᴬ u ⊞ rd (force (Gh n))) →
       force G₀ ⊴₀ force (Gh 0) → (∀ n → force (Gh n) ⊴₀ force (Gh (suc n))) → G (oc x h)

force g0 = FL.zero
force (gs d) = FL.suc (force d)
force (gl Gs st) = FL.lim (λ n → force (Gs n))
force (gw d) = force d
force (gc G₀ vs gv up Gh t₀ tS s₀ sS) = FL.lim (outs (force G₀) (λ n → force (Gh n)))

Lit-force : ∀ {u} {x : 𝓡 u} (d : G x) → Lit₀ (force d)
Lit-force g0 = tt
Lit-force (gs d) = Lit-force d
Lit-force (gl Gs st) = st , (λ n → Lit-force (Gs n))
Lit-force (gw d) = Lit-force d
Lit-force (gc G₀ vs gv up Gh t₀ tS s₀ sS) = step , each
  where
  step : ∀ n → outs (force G₀) (λ k → force (Gh k)) n ⊴₀ outs (force G₀) (λ k → force (Gh k)) (suc n)
  step zero = s₀
  step (suc n) = sS n
  each : ∀ n → Lit₀ (outs (force G₀) (λ k → force (Gh k)) n)
  each zero = Lit-force G₀
  each (suc n) = Lit-force (Gh n)

HS-force : ∀ {u} {x : 𝓡 u} (d : G x) → HS (force d)
HS-force d = HS₀ _ (Lit-force d)
```

## §2 证书无关, 单调

```agda
fo≅ : ∀ {u u′} {x : 𝓡 u} {y : 𝓡 u′} (a : G x) (b : G y) → x ≈ y → force a ≅ force b
fo≅ (gw a) b e = fo≅ a b e
fo≅ a@g0 (gw b) e = fo≅ a b e
fo≅ a@(gs _) (gw b) e = fo≅ a b e
fo≅ a@(gl _ _) (gw b) e = fo≅ a b e
fo≅ a@(gc _ _ _ _ _ _ _ _ _) (gw b) e = fo≅ a b e
fo≅ g0 g0 e = z≅
fo≅ (gs a) (gs b) (_ , _ , _ , e) = s≅ (fo≅ a b e)
fo≅ (gl a _) (gl b _) e = l≅ (λ n → fo≅ (a n) (b n) (e n))
fo≅ (gc A₀ vs gv up Gh t₀ tS s₀ sS) (gc B₀ vs′ gv′ up′ Gh′ t₀′ tS′ s₀′ sS′) (_ , _ , eu , ex , N) = l≅ out
  where
  e₀ = fo≅ A₀ B₀ ex
  vv : ∀ n → vs n ≈ᴬ vs′ n
  E  : ∀ n → force (Gh n) ≅ force (Gh′ n)
  vv zero = ≈ᴬ-trans t₀ (≈ᴬ-trans (⊞≈ eu (≅→≈ e₀)) (≈ᴬ-sym t₀′))
  vv (suc n) = ≈ᴬ-trans (tS n) (≈ᴬ-trans (⊞≈ eu (≅→≈ (E n))) (≈ᴬ-sym (tS′ n)))
  E n = fo≅ (Gh n) (Gh′ n) (N (up n) (up′ n) (gv n) (gv′ n) (vv n))
  out : ∀ n → outs (force A₀) (λ k → force (Gh k)) n ≅ outs (force B₀) (λ k → force (Gh′ k)) n
  out zero = e₀
  out (suc n) = E n
fo≅ g0 (gs _) ()
fo≅ g0 (gl _ _) ()
fo≅ g0 (gc _ _ _ _ _ _ _ _ _) ()
fo≅ (gs _) g0 ()
fo≅ (gs _) (gl _ _) ()
fo≅ (gs _) (gc _ _ _ _ _ _ _ _ _) ()
fo≅ (gl _ _) g0 ()
fo≅ (gl _ _) (gs _) ()
fo≅ (gl _ _) (gc _ _ _ _ _ _ _ _ _) ()
fo≅ (gc _ _ _ _ _ _ _ _ _) g0 ()
fo≅ (gc _ _ _ _ _ _ _ _ _) (gs _) ()
fo≅ (gc _ _ _ _ _ _ _ _ _) (gl _ _) ()

fo⊴ : ∀ {u u′} {x : 𝓡 u} {y : 𝓡 u′} → x ⊴ y → (a : G x) (b : G y) → force a ⊴₀ force b
fo⊴ (rw d) a (gw b) = fo⊴ d a b
fo⊴ (lw₂ d) (gw a) b = fo⊴ d a b
fo⊴ (rf e) a b = r0 (fo≅ a b e)
fo⊴ (s d) a (gs b) = s0 (fo⊴ d a b)
fo⊴ (l n d) a (gl b _) = l0 n (fo⊴ d a (b n))
fo⊴ (fc d) a (gc B₀ _ _ _ _ _ _ _ _) = l0 0 (fo⊴ d a B₀)
fo⊴ (ni {r = ()} d) a b
fo⊴ (nd {i = ()} d) a b
fo⊴ (eR {stp = ()} d) a b
fo⊴ (eL {stp = ()} d) a b
fo⊴ (rL {j = ()} d) a b
fo⊴ (lL {j = ()} d) a b
```

## §3 链

```agda
record Cl (u : A) (h : ∀ {v} → u ⊲ v → Gw v → 𝓡 v) : Set where
  field
    y    : Ord₀
    κ    : A
    tie  : κ ≈ᴬ rd y
    lκ   : Lg κ
    gv′  : Gw (u ⊞ κ)
    Gh   : G (h (⊞-fst u κ) gv′)
    st   : y ⊴₀ force Gh
open Cl

C′ : ∀ {u} (x : 𝓡 u) → Gw u → x ≈ x → WF x → G x
C′ o0 gu e w = g0
C′ (os x) gu (_ , _ , _ , e) w = gs (C′ x gu e w)
C′ (ol F) gu e (st , u) = gl Gs (λ m → fo⊴ (st m) (Gs m) (Gs (suc m)))
  where
  Gs : ∀ m → G (F m)
  Gs m = C′ (F m) gu (e m) (u m)
C′ (oi () _) gu e w
C′ (od () _ _ _) gu e w
C′ {u} (oc x h) gu (_ , _ , _ , ex , N) (fi , dr , wx , wh) =
  gc G₀ (λ n → u ⊞ κ (cell n)) (λ n → gv′ (cell n)) (λ n → ⊞-fst u (κ (cell n))) (λ n → Gh (cell n))
     (⊞≈ (≈ᴬ-refl u) (tie (cell 0))) (λ n → ⊞≈ (≈ᴬ-refl u) (tie (cell (suc n)))) (st (cell 0)) (λ n → st (cell (suc n)))
  where
  G₀ = C′ x gu ex wx
  y₀ = force G₀
  mkG : ∀ {q} (q₁ : u ⊲ q) (g : Gw q) → G (h q₁ g)
  mkG q₁ g = C′ (h q₁ g) g (N q₁ q₁ g g (≈ᴬ-refl _)) (wh q₁ g)
  mkW : ∀ κ₀ → Lg κ₀ → Gw (u ⊞ κ₀)
  mkW κ₀ w = gw (Lg-⊞ u κ₀ (lgw gu) w) (⊲-tr (pos gu) (⊞-fst u κ₀))
  P₀ = lit y₀ (Lit-force G₀)
  cell : ℕ → Cl u h
  cell zero = record { y = y₀ ; κ = g P₀ ; tie = eq P₀ ; lκ = lg P₀ ; gv′ = mkW (g P₀) (lg P₀) ; Gh = mkG _ (mkW (g P₀) (lg P₀))
                     ; st = fo⊴ (fi _ _) G₀ (mkG _ (mkW (g P₀) (lg P₀))) }
  cell (suc n) = record { y = y′ ; κ = κ′ ; tie = eq (gE r) ; lκ = lg (gE r) ; gv′ = mkW κ′ (lg (gE r)) ; Gh = mkG _ (mkW κ′ (lg (gE r)))
                        ; st = fo⊴ (dr _ _ (gv′ c) (mkW κ′ (lg (gE r))) (⊞-⊲ u (at r))) (Gh c) (mkG _ (mkW κ′ (lg (gE r)))) }
    where
    c = cell n
    y′ = force (Gh c)
    r : Gr (rd y′) (κ c)
    r = graft₀ (st c) (lit y′ (Lit-force (Gh c))) (el (κ c) (tie c) (lκ c))
    κ′ = g (gE r)
C′ (oe () _) gu e w
C′ (oL () _ _ _) gu e w
C′ (ow p g x) gu e w = gw (C′ x g (≈ow⁻ x p g x e) w)
```

## §4 无条件

```agda
WF-T : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → WF (Tᴰ p a u₀ g e)
WF-T p a u₀ g e = ψW zero azero (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e (Ω≈ p (≈ᴬ-refl a)) (ΩW p a (lg⊲ e (lgw g)))

≈-T : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Tᴰ p a u₀ g e ≈ Tᴰ p a u₀ g e
≈-T p a u₀ g e = ψQ (Ω̇ p a) (Ω̇ p a) g₀ g₀ u₀ g (pos g) (z⊲ u₀) e u₀ g (pos g) (z⊲ u₀) e z≈ (Ω≈ p (≈ᴬ-refl a))

G-Tᵖ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → G (Tᴰ p a u₀ g e)
G-Tᵖ p a u₀ g e = C′ _ g (≈-T p a u₀ g e) (WF-T p a u₀ g e)

Tᵖ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → Ord₀
Tᵖ p a u₀ g e = force (G-Tᵖ p a u₀ g e)

HS-Tᵖ : ∀ p a u₀ (g : Gw u₀) (e : a ⊲ u₀) → HS (Tᵖ p a u₀ g e)
HS-Tᵖ p a u₀ g e = HS-force (G-Tᵖ p a u₀ g e)
```

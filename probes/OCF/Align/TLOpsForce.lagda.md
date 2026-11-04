# 树的算子语言 (十): 去掉前缀的全部义务

> 不含记号. 入口 [TLOps](TLOps.lagda.md). 由 [NoCumForce](NoCumForce.lagda.md) 改写, 高度是 $A$. 链点是输出的字面读出 (`tie`), **没有前缀, 没有累加.** `C′`: `WF` 加 `Hn` 就有证书. **`Hn` 就是不能一般化的那一条义务:** 闭包的第一支的读出以闭包的世界为第一位置, 只在链点上的分支要求. 它在 [TLOpsPre](TLOpsPre.lagda.md) 里由前缀 `⊞-fst` 字面给出, 在这里是一条关于输出的定理, 没有证明. **暂停, 未走通, 不是否定.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsForce where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open FL using (HS; _≅_; z≅; s≅; l≅)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; ⊲-tr; z⊲; lg⊲; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.TLOpsW
open import OCF.Align.TLOpsEq
open import OCF.Align.TLOpsPsi
open import OCF.Align.TLOpsLe
open import OCF.Align.TLOpsMain

𝓡 : A → Set
𝓡 u = 𝓞 azero azero u

outs : Ord₀ → (ℕ → Ord₀) → ℕ → Ord₀
outs y₀ F zero = y₀
outs y₀ F (suc n) = F n
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
       vs 0 ≈ᴬ rd (force G₀) → (∀ n → vs (suc n) ≈ᴬ rd (force (Gh n))) →
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
fo≅ (gc A₀ vs gv up Gh t₀ tS s₀ sS) (gc B₀ vs′ gv′ up′ Gh′ t₀′ tS′ s₀′ sS′) (_ , _ , _ , ex , N) = l≅ out
  where
  e₀ = fo≅ A₀ B₀ ex
  vv : ∀ n → vs n ≈ᴬ vs′ n
  E  : ∀ n → force (Gh n) ≅ force (Gh′ n)
  vv zero = ≈ᴬ-trans t₀ (≈ᴬ-trans (≅→≈ e₀) (≈ᴬ-sym t₀′))
  vv (suc n) = ≈ᴬ-trans (tS n) (≈ᴬ-trans (≅→≈ (E n)) (≈ᴬ-sym (tS′ n)))
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

## §3 守卫

`Fp u y`: $u$ 模 $\approx$ 是 `rd y` 的第一位置. `Hn x`: $x$ 里每个闭包的第一支, 不管证书怎么取, 计值的读出以闭包的世界为第一位置.

```agda
data Fp (u : A) : Ord₀ → Set where
  fq : ∀ {y} → u ≈ᴬ rd y → Fp u y
  fs : ∀ {y} → Fp u y → Fp u (FL.suc y)
  fl : ∀ {f} n → Fp u (f n) → Fp u (FL.lim f)

⊴→Fp : ∀ {a b} → a ⊴₀ b → Fp (rd a) b
⊴→Fp (r0 e) = fq (≅→≈ e)
⊴→Fp (s0 d) = fs (⊴→Fp d)
⊴→Fp (l0 n d) = fl n (⊴→Fp d)

Fp-mono : ∀ {u a b} → Fp u a → a ⊴₀ b → Fp u b
Fp-mono p (s0 d) = fs (Fp-mono p d)
Fp-mono p (l0 n d) = fl n (Fp-mono p d)
Fp-mono (fq e) (r0 d) = fq (≈ᴬ-trans e (≅→≈ d))
Fp-mono (fs p) (r0 (s≅ d)) = fs (Fp-mono p (r0 d))
Fp-mono (fl n p) (r0 (l≅ d)) = fl n (Fp-mono p (r0 (d n)))

Fp→Pj : ∀ {u y g} → Fp u y → g ≈ᴬ rd y → Pj u g
Fp→Pj {g = g} (fq e) d = pj g (≈ᴬ-trans d (≈ᴬ-sym e)) C.self
Fp→Pj (fs p) (s≈ d) = let r = Fp→Pj p d in pj (Pj.p r) (pe r) (C.suc (pa r))
Fp→Pj (fl n p) (l≈ d) = let r = Fp→Pj p (d n) in pj (Pj.p r) (pe r) (C.lim n (pa r))

-- v 是这个闭包的链点: 第一支或某个分支的输出的读出. 只有链点上的分支才要守卫.
data Rdv {u} (x : 𝓡 u) (h : ∀ {v} → u ⊲ v → Gw v → 𝓡 v) (v : A) : Set where
  rd₀ : (d : G x) → v ≈ᴬ rd (force d) → Rdv x h v
  rdS : ∀ {v′} (q′ : u ⊲ v′) (g′ : Gw v′) (d : G (h q′ g′)) → v ≈ᴬ rd (force d) → Rdv x h v

Hn : ∀ {u} → 𝓡 u → Set
Hn o0 = ⊤
Hn (os x) = Hn x
Hn (ol F) = ∀ n → Hn (F n)
Hn (oi () _)
Hn (od () _ _ _)
Hn {u} (oc x h) = Hn x × (∀ {v} (q : u ⊲ v) (g : Gw v) → Rdv x h v → Hn (h q g)) × ((d : G x) → Fp u (force d))
Hn (oe () _)
Hn (oL () _ _ _)
Hn (ow p g x) = Hn x
```

## §4 `C`: 链

```agda
record Cl (u : A) (h : ∀ {v} → u ⊲ v → Gw v → 𝓡 v) : Set where
  field
    y    : Ord₀
    v    : A
    tie  : v ≈ᴬ rd y
    gv′  : Gw v
    up′  : u ⊲ v
    Gh   : G (h up′ gv′)
    st   : y ⊴₀ force Gh
open Cl

C′ : ∀ {u} (x : 𝓡 u) → Gw u → x ≈ x → WF x → Hn x → G x
C′ o0 gu e w n = g0
C′ (os x) gu (_ , _ , _ , e) w n = gs (C′ x gu e w n)
C′ (ol F) gu e (st , u) n = gl Gs (λ m → fo⊴ (st m) (Gs m) (Gs (suc m)))
  where
  Gs : ∀ m → G (F m)
  Gs m = C′ (F m) gu (e m) (u m) (n m)
C′ (oi () _) gu e w n
C′ (od () _ _ _) gu e w n
C′ {u} (oc x h) gu (_ , _ , _ , ex , N) (fi , dr , wx , wh) (hx , hh , gd) =
  gc G₀ (λ n → v (cell n)) (λ n → gv′ (cell n)) (λ n → up′ (cell n)) (λ n → Gh (cell n))
     (tie (cell 0)) (λ n → tie (cell (suc n))) (st (cell 0)) (λ n → st (cell (suc n)))
  where
  G₀ = C′ x gu ex wx hx
  y₀ = force G₀
  mkG : ∀ {q} (q₁ : u ⊲ q) (g : Gw q) → Rdv x h q → G (h q₁ g)
  mkG q₁ g b = C′ (h q₁ g) g (N q₁ q₁ g g (≈ᴬ-refl _)) (wh q₁ g) (hh q₁ g b)
  P₀ = lit y₀ (Lit-force G₀)
  b₀ = Fp→Pj (gd G₀) (eq P₀)
  r₀ = graftA (g P₀) (pa b₀) (lg P₀) u (lgw gu) (≈ᴬ-sym (pe b₀))
  v₀ = g (gE r₀)
  tie₀ : v₀ ≈ᴬ rd y₀
  tie₀ = ≈ᴬ-trans (eq (gE r₀)) (eq P₀)
  gv₀ : Gw v₀
  gv₀ = gw (lg (gE r₀)) (⊲-tr (pos gu) (at r₀))
  cell : ℕ → Cl u h
  cell zero = record { y = y₀ ; v = v₀ ; tie = tie₀ ; gv′ = gv₀ ; up′ = at r₀ ; Gh = mkG (at r₀) gv₀ (rd₀ G₀ tie₀) ; st = fo⊴ (fi (at r₀) gv₀) G₀ (mkG (at r₀) gv₀ (rd₀ G₀ tie₀)) }
  cell (suc n) = record { y = y′ ; v = v′ ; tie = tie′ ; gv′ = gv″ ; up′ = up″ ; Gh = mkG up″ gv″ (rdS (up′ c) (gv′ c) (Gh c) tie′) ; st = fo⊴ (dr (up′ c) up″ (gv′ c) gv″ (at gr₁)) (Gh c) (mkG up″ gv″ (rdS (up′ c) (gv′ c) (Gh c) tie′)) }
    where
    c = cell n
    y′ = force (Gh c)
    gr₁ : Gr (rd y′) (v c)
    gr₁ = graft₀ (st c) (lit y′ (Lit-force (Gh c))) (el (v c) (tie c) (lgw (gv′ c)))
    v′ = g (gE gr₁)
    tie′ = eq (gE gr₁)
    gv″ : Gw v′
    gv″ = gw (lg (gE gr₁)) (⊲-tr (pos (gv′ c)) (at gr₁))
    up″ : u ⊲ v′
    up″ = ⊲-tr (up′ c) (at gr₁)
C′ (oe () _) gu e w n
C′ (oL () _ _ _) gu e w n
C′ (ow p g x) gu e w n = gw (C′ x g (≈ow⁻ x p g x e) w n)
```

## §5 $\psi_0(\Omega_{\Omega\cdot p+a})$, 条件定理

```agda
WF-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → WF (Tᴰ p a u₀ lp g e)
WF-T p a u₀ lp g e = ψW azero azero (hk₀ lp) (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e (Ω≈ p (≈ᴬ-refl a)) (ΩW p a lp (lg⊲ e (lgw g)))

≈-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Tᴰ p a u₀ lp g e ≈ Tᴰ p a u₀ lp g e
≈-T p a u₀ lp g e = ψQ (hk₀ lp) (hk₀ lp) refl (Ω̇ p a) (Ω̇ p a) g₀ g₀ u₀ g (pos g) (z⊲ u₀) e u₀ g (pos g) (z⊲ u₀) e z≈ (Ω≈ p (≈ᴬ-refl a))

G-T : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Hn (Tᴰ p a u₀ lp g e) → G (Tᴰ p a u₀ lp g e)
G-T p a u₀ lp g e h = C′ _ g (≈-T p a u₀ lp g e) (WF-T p a u₀ lp g e) h

Tᴺ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) → Hn (Tᴰ p a u₀ lp g e) → Ord₀
Tᴺ p a u₀ lp g e h = force (G-T p a u₀ lp g e h)

HS-Tᴺ : ∀ p a u₀ (lp : Lg p) (g : Gw u₀) (e : a ⊲ u₀) (h : Hn (Tᴰ p a u₀ lp g e)) → HS (Tᴺ p a u₀ lp g e h)
HS-Tᴺ p a u₀ lp g e h = HS-force (G-T p a u₀ lp g e h)
```

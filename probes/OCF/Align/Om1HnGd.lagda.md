# $\psi_0(\Omega_{\Omega+1})$, 不累加: 遗传好项

> 不含记号. 结论写在 [Om1Hn](Om1Hn.lagda.md). `Gd 𝓖 x`: 对类 $\mathcal G$ 里的上下文, $x$ 是遗传好的. 与 `OCF.Free` 的 `Good` 逐行对应, 但写成对项递归的函数 (与 [NoCumMain](NoCumMain.lagda.md) 的 `WF` 同形), **不带** `WF` 已经给的单调和同余.
>
> 第 0 层的出口是 `X`: `Gd 𝓖 x` 且 `idC` 在类里, 则 `G x`. 这条直接造证书, 不经过 `Hn`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1HnGd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using (zero; suc)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; ⊲-tr; z⊲; ≪S)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (WF; hMi)
open import OCF.Align.NoCumForce hiding (Cl; C′)
open import OCF.Align.Om1HnCx

record ⊤₂ : Set₂ where
  constructor tt₂
```

## §1 规则

```agda
record OsR (𝓖 : Cl) {p a u} (x : 𝓞 p a u) (GX : Cl → Set₂) : Set₂ where
  constructor osr
  field
    𝓚 : Cl
    inc : ∀ {C} → 𝓖 C → 𝓚 C
    gK : GX 𝓚
    clk : ∀ {O C″} → 𝓚 O → FlOver x O C″ → 𝓚 C″
    hon : ∀ {C} → 𝓚 C → ∀ {w} {y : 𝓡 w} → Rn C x y → (d : G y) → Fp one (force d) → Fp u (force d) × Fp a (force d)

record Tr (C : Cx) {w} (y : 𝓡 w) : Set where
  constructor tr
  field
    {tp} : ℕ
    {ta tu} : A
    t : 𝓞 tp ta tu
    rt : Rn C t y

record BrR (𝓖 : Cl) (q₁ h₀ : ℕ) (k u : A) (Y : A → Set) (out : ∀ {v} → Y v → 𝓞 h₀ k v) (GZ : Cl → ∀ {v} → Y v → Set₂) (GF : Cl → ∀ {v} → u ⊲ v → Gw v → Y v → Set₂) : Set₂ where
  constructor brr
  field
    𝓖₀ : Cl
    W : Cx → Cx
    inc : ∀ {C} → 𝓖 C → 𝓖₀ C
    wf : ∀ {C p a u′ w} {z : 𝓞 p a u′} {y : 𝓡 w} → 𝓖₀ C → Rn (W C) z y → Tr C y
    vis : ∀ {C} → 𝓖₀ C → 𝓥′ h₀ k (W C)
    st : ∀ {C C′} → 𝓖₀ C → Over q₁ h₀ k C′ (W C) → 𝓖₀ C′
    prem : ∀ (𝓔 : Cl) → (∀ {C} → 𝓔 C → 𝓖₀ C) → ∀ {v} (q : u ⊲ v) (g : Gw v) (y : Y v) → out y ≈ out y → WF (out y) → GZ (Im W 𝓔) y → GF 𝓔 q g y

record OcR (𝓖 : Cl) {p a u} (x : 𝓞 p a u) (h : ∀ {v} → u ⊲ v → Gw v → 𝓞 p a v) (GX : Cl → Set₂) (GH : Cl → ∀ {v} → u ⊲ v → Gw v → Set₂) : Set₂ where
  constructor ocr
  field
    𝓑 : A → Cl
    g₁ : GX 𝓖
    gH : ∀ {v} (q : u ⊲ v) (g : Gw v) → GH (𝓖 ∧ 𝓑 v) q g
    gd : ∀ {C} → 𝓖 C → ∀ {w} {y : 𝓡 w} → Rn C x y → (d : G y) → Fp u (force d) × Fp a (force d)
    ch₀ : ∀ {C} → 𝓖 C → ∀ {w} {y : 𝓡 w} → Rn C x y → (d : G y) → ∀ {v} → Gw v → v ≈ᴬ rd (force d) → u ⊲ v → 𝓑 v C
    chS : ∀ {C v v′} (q : u ⊲ v) (g : Gw v) → 𝓖 C → 𝓑 v C → ∀ {w} {y : 𝓡 w} → Rn C (h q g) y → (d : G y) → Gw v′ → v′ ≈ᴬ rd (force d) → v ⊲ v′ → 𝓑 v′ C

Gd  : ∀ {p a u} → Cl → 𝓞 p a u → Set₂
GdS : ∀ {p a b} (R : Strict b a) {u} → Cl → Vs p a R u → Set₂
GdC : ∀ {p a b} (P : b ⊲ a) {u} → Cl → Vc p a P u → Set₂
GdL : ∀ {p h k u} (j : h <ᴺ p) → Cl → Low p j k u → Set₂

Gd 𝓖 o0 = ⊤₂
Gd 𝓖 (os x) = OsR 𝓖 x (λ 𝓚 → Gd 𝓚 x)
Gd 𝓖 (ol F) = ∀ n → Gd 𝓖 (F n)
Gd {p} {a} {u} 𝓖 (oi {k = k} r h) = BrR 𝓖 p p k u (Vs p a (≪S r)) (outS (≪S r)) (λ 𝓓 y → GdS (≪S r) 𝓓 y) (λ 𝓔 q g y → Gd 𝓔 (h q g y))
Gd {p} {a} {u} 𝓖 (od {h = h₀} i k r h) = BrR 𝓖 p h₀ k u (Low p i k) (outL i) (λ 𝓓 y → GdL i 𝓓 y) (λ 𝓔 q g y → Gd 𝓔 (h q g y))
Gd 𝓖 (oc x h) = OcR 𝓖 x h (λ 𝓖′ → Gd 𝓖′ x) (λ 𝓖′ q g → Gd 𝓖′ (h q g))
Gd 𝓖 (oe es x) = Gd 𝓖 x
Gd 𝓖 (oe (el n) x) = Gd 𝓖 x
Gd 𝓖 (oL j k e x) = GdL j 𝓖 x
Gd 𝓖 (ow w g x) = Gd 𝓖 x

GdS (ss P) 𝓖 x = GdC P 𝓖 x
GdS (sl n P) 𝓖 x = GdC P 𝓖 x
GdC C.self 𝓖 x = Gd 𝓖 x
GdC (C.suc P) 𝓖 x = GdC P 𝓖 x
GdC (C.lim n P) 𝓖 x = GdC P 𝓖 x
GdL zero 𝓖 x = Gd 𝓖 x
GdL (suc j) 𝓖 x = GdL j 𝓖 x

S→G : ∀ {p a b u} (R : Strict b a) (𝓖 : Cl) (x : Vs p a R u) → GdS R 𝓖 x → Gd 𝓖 (outS R x)
C→G : ∀ {p a b u} (P : b ⊲ a) (𝓖 : Cl) (x : Vc p a P u) → GdC P 𝓖 x → Gd 𝓖 (outC P x)
S→G (ss P) 𝓖 x w = C→G P 𝓖 x w
S→G (sl n P) 𝓖 x w = C→G P 𝓖 x w
C→G C.self 𝓖 x w = w
C→G (C.suc P) 𝓖 x w = C→G P 𝓖 x w
C→G (C.lim n P) 𝓖 x w = C→G P 𝓖 x w

G→S : ∀ {p a b u} (R : Strict b a) (𝓖 : Cl) (x : Vs p a R u) → Gd 𝓖 (outS R x) → GdS R 𝓖 x
G→C : ∀ {p a b u} (P : b ⊲ a) (𝓖 : Cl) (x : Vc p a P u) → Gd 𝓖 (outC P x) → GdC P 𝓖 x
G→S (ss P) 𝓖 x w = G→C P 𝓖 x w
G→S (sl n P) 𝓖 x w = G→C P 𝓖 x w
G→C C.self 𝓖 x w = w
G→C (C.suc P) 𝓖 x w = G→C P 𝓖 x w
G→C (C.lim n P) 𝓖 x w = G→C P 𝓖 x w

L→G : ∀ {p h k u} (j : h <ᴺ p) (𝓖 : Cl) (x : Low p j k u) → GdL j 𝓖 x → Gd 𝓖 (outL j x)
L→G zero 𝓖 x w = w
L→G (suc j) 𝓖 x w = L→G j 𝓖 x w

G→L : ∀ {p h k u} (j : h <ᴺ p) (𝓖 : Cl) (x : Low p j k u) → Gd 𝓖 (outL j x) → GdL j 𝓖 x
G→L zero 𝓖 x w = w
G→L (suc j) 𝓖 x w = G→L j 𝓖 x w
```

## §2 类单调

```agda
Br-mono : ∀ {𝓖 𝓖′ : Cl} {q₁ h₀ k u} {Y : A → Set} {out : ∀ {v} → Y v → 𝓞 h₀ k v} {GZ : Cl → ∀ {v} → Y v → Set₂} {GF : Cl → ∀ {v} → u ⊲ v → Gw v → Y v → Set₂} → (∀ {C} → 𝓖′ C → 𝓖 C) → BrR 𝓖 q₁ h₀ k u Y out GZ GF → BrR 𝓖′ q₁ h₀ k u Y out GZ GF
Br-mono f (brr 𝓖₀ W inc wf vis st prem) = brr 𝓖₀ W (λ c → inc (f c)) wf vis st prem

Gd-mono : ∀ {p a u} {𝓖 𝓖′ : Cl} → (∀ {C} → 𝓖′ C → 𝓖 C) → (x : 𝓞 p a u) → Gd 𝓖 x → Gd 𝓖′ x
GdL-mono : ∀ {p h k u} {𝓖 𝓖′ : Cl} → (∀ {C} → 𝓖′ C → 𝓖 C) → (j : h <ᴺ p) (x : Low p j k u) → GdL j 𝓖 x → GdL j 𝓖′ x
Gd-mono f o0 g = tt₂
Gd-mono f (os x) (osr 𝓚 inc gK clk hon) = osr 𝓚 (λ c → inc (f c)) gK clk hon
Gd-mono f (ol F) g = λ n → Gd-mono f (F n) (g n)
Gd-mono f (oi r h) g = Br-mono f g
Gd-mono f (od i k r h) g = Br-mono f g
Gd-mono f (oc x h) (ocr 𝓑 g₁ gH gd ch₀ chS) =
  ocr 𝓑 (Gd-mono f x g₁) (λ {v} q g → Gd-mono (λ (c , b) → f c , b) (h q g) (gH q g)) (λ c → gd (f c)) (λ c → ch₀ (f c)) (λ q g c → chS q g (f c))
Gd-mono f (oe es x) g = Gd-mono f x g
Gd-mono f (oe (el n) x) g = Gd-mono f x g
Gd-mono f (oL j k e x) g = GdL-mono f j x g
Gd-mono f (ow w g′ x) g = Gd-mono f x g
GdL-mono f zero x g = Gd-mono f x g
GdL-mono f (suc j) x g = GdL-mono f j x g
```

## §3 出口

这条的形状是 [NoCumForce](NoCumForce.lagda.md) 的 `C′`, 多带一个 `bb`.

```agda
record Cell {u} (𝓑 : A → Cl) (h : ∀ {v} → u ⊲ v → Gw v → 𝓡 v) : Set₁ where
  field
    y    : Ord₀
    v    : A
    tie  : v ≈ᴬ rd y
    gv′  : Gw v
    up′  : u ⊲ v
    bb   : 𝓑 v idC
    Gh   : G (h up′ gv′)
    st   : y ⊴₀ force Gh
open Cell

X : ∀ {u} (x : 𝓡 u) → Gw u → x ≈ x → WF x → (𝓖 : Cl) → 𝓖 idC → Gd 𝓖 x → G x
X o0 gu e w 𝓖 i g = g0
X (os x) gu (_ , _ , _ , e) w 𝓖 i g = gs (X x gu e w (OsR.𝓚 g) (OsR.inc g i) (OsR.gK g))
X (ol F) gu e (st₁ , u) 𝓖 i g = gl Gs (λ m → fo⊴ (st₁ m) (Gs m) (Gs (suc m)))
  where
  Gs : ∀ m → G (F m)
  Gs m = X (F m) gu (e m) (u m) 𝓖 i (g m)
X (oi () _) gu e w 𝓖 i g
X (od () _ _ _) gu e w 𝓖 i g
X {u} (oc x h) gu (_ , _ , _ , ex , N) (fi , dr , wx , wh) 𝓖 i (ocr 𝓑 g₁ gH gd ch₀ chS) =
  gc G₀ (λ n → v (cell n)) (λ n → gv′ (cell n)) (λ n → up′ (cell n)) (λ n → Gh (cell n))
     (tie (cell 0)) (λ n → tie (cell (suc n))) (st (cell 0)) (λ n → st (cell (suc n)))
  where
  G₀ = X x gu ex wx 𝓖 i g₁
  y₀ = force G₀
  mkG : ∀ {q} (q₁ : u ⊲ q) (g : Gw q) → 𝓑 q idC → G (h q₁ g)
  mkG {q} q₁ g b = X (h q₁ g) g (N q₁ q₁ g g (≈ᴬ-refl _)) (wh q₁ g) (𝓖 ∧ 𝓑 q) (i , b) (gH q₁ g)
  P₀ = lit y₀ (Lit-force G₀)
  b₀ = Fp→Pj (proj₁ (gd i (idr C.self gu) (gw G₀))) (eq P₀)
  r₀ = graftA (g P₀) (pa b₀) (lg P₀) u (lgw gu) (≈ᴬ-sym (pe b₀))
  v₀ = g (gE r₀)
  tie₀ : v₀ ≈ᴬ rd y₀
  tie₀ = ≈ᴬ-trans (eq (gE r₀)) (eq P₀)
  gv₀ : Gw v₀
  gv₀ = gw (lg (gE r₀)) (⊲-tr (pos gu) (at r₀))
  bb₀ : 𝓑 v₀ idC
  bb₀ = ch₀ i (idr C.self gu) (gw G₀) gv₀ tie₀ (at r₀)
  cell : ℕ → Cell 𝓑 h
  cell zero = record { y = y₀ ; v = v₀ ; tie = tie₀ ; gv′ = gv₀ ; up′ = at r₀ ; bb = bb₀ ; Gh = mkG (at r₀) gv₀ bb₀ ; st = fo⊴ (fi (at r₀) gv₀) G₀ (mkG (at r₀) gv₀ bb₀) }
  cell (suc n) = record { y = y′ ; v = v′ ; tie = tie′ ; gv′ = gv″ ; up′ = up″ ; bb = bb′ ; Gh = mkG up″ gv″ bb′ ; st = fo⊴ (dr (up′ c) up″ (gv′ c) gv″ (at gr₁)) (Gh c) (mkG up″ gv″ bb′) }
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
    bb′ : 𝓑 v′ idC
    bb′ = chS (up′ c) (gv′ c) i (bb c) (idr C.self (gv′ c)) (gw (Gh c)) gv″ tie′ (at gr₁)
X (oe () _) gu e w 𝓖 i g
X (oL () _ _ _) gu e w 𝓖 i g
X (ow p g′ x) gu e w 𝓖 i g = gw (X x g′ (≈ow⁻ x p g′ x e) w 𝓖 i g)
```

## §4 分支的规则沿帧搬

折叠和加法的非上升情形都是这一条: 新的 $\mathcal G_0$ 是 $C\mapsto\mathcal A(C)\wedge\mathcal G_0(F\,C)$, 新的 $W$ 是 $W\circ F$.

```agda
brMap : ∀ {𝓧 𝓐₁ : Cl} {q₁ q₁′ h₀ k u u′} {Y Y′ : A → Set} {out : ∀ {v} → Y v → 𝓞 h₀ k v} {out′ : ∀ {v} → Y′ v → 𝓞 h₀ k v}
        {GZ : Cl → ∀ {v} → Y v → Set₂} {GZ′ : Cl → ∀ {v} → Y′ v → Set₂} {GF : Cl → ∀ {v} → u ⊲ v → Gw v → Y v → Set₂} {GF′ : Cl → ∀ {v} → u′ ⊲ v → Gw v → Y′ v → Set₂}
        (old : BrR 𝓧 q₁ h₀ k u Y out GZ GF) (F : Cx → Cx) (𝓐 : Cl) →
        (∀ {C p a u₁ w} {t : 𝓞 p a u₁} {y : 𝓡 w} → Rn (F C) t y → Tr C y) →
        (∀ {C} → 𝓐₁ C → 𝓐 C × 𝓧 (F C)) →
        (∀ {C C′} → 𝓐 C → BrR.𝓖₀ old (F C) → Over q₁′ h₀ k C′ (BrR.W old (F C)) → 𝓐 C′) →
        (∀ {C′ D} → Over q₁′ h₀ k C′ D → Over q₁ h₀ k (F C′) D) →
        (cv : ∀ {v} → Y′ v → Y v) (qc : ∀ {v} → u′ ⊲ v → u ⊲ v) →
        (∀ {v} (y : Y′ v) → out (cv y) ≡ out′ y) →
        (∀ (𝓓 : Cl) {v} (y : Y′ v) → GZ′ 𝓓 y → Gd 𝓓 (out′ y)) →
        (∀ (𝓓 : Cl) {v} (y : Y v) → Gd 𝓓 (out y) → GZ 𝓓 y) →
        (∀ (𝓔 : Cl) {v} (q : u′ ⊲ v) (g : Gw v) (y : Y′ v) → out′ y ≈ out′ y → WF (out′ y) → (∀ {C} → 𝓔 C → 𝓐 C × BrR.𝓖₀ old (F C)) → GF (Im F 𝓔) (qc q) g (cv y) → GF′ 𝓔 q g y) →
        BrR 𝓐₁ q₁′ h₀ k u′ Y′ out′ GZ′ GF′
brMap {𝓧} {𝓐₁} {q₁} {q₁′} {h₀} {k} {u} {u′} {Y} {Y′} {out} {out′} {GZ} {GZ′} {GF} {GF′} (brr 𝓖₀ W inc wf vis st prem) F 𝓐 lift hinc hA hOv cv qc eo g′ →g CL =
  brr (λ C → 𝓐 C × 𝓖₀ (F C)) (λ C → W (F C))
      (λ c → proj₁ (hinc c) , inc (proj₂ (hinc c)))
      (λ { (a , c) r → let tr t r₁ = wf c r in lift r₁ })
      (λ { (a , c) → vis c })
      (λ { (a , c) o → hA a c o , st c (hOv o) })
      (λ 𝓔 sub {v} q g y e w z →
         CL 𝓔 q g y e w sub
           (prem (Im F 𝓔) (λ { (im C c refl) → proj₂ (sub c) }) (qc q) g (cv y)
             (subst (λ t → t ≈ t) (sym (eo y)) e) (subst WF (sym (eo y)) w)
             (→g (Im W (Im F 𝓔)) (cv y)
               (subst (Gd (Im W (Im F 𝓔))) (sym (eo y))
                 (Gd-mono (λ { (im _ (im C c refl) refl) → im C c refl }) (out′ y) (g′ (Im (λ C → W (F C)) 𝓔) y z))))))
```

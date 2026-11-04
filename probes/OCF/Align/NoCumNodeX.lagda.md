# 第 0 层是值: 出口

> 不含记号. 结论写在 [NoCumNode](NoCumNode.lagda.md). `X`: `Gd 𝓖 x` 且 `idC` 在类里, 则 $\psi_0(x)$ 有证书. 这是 [Om1HnGd](Om1HnGd.lagda.md) 的 `X` 的形状, 但对一切层的 $x$, 而且上升在这里做.
>
> `XR`: 上升到 $(0,0)$. $(h_0,k)\neq(0,0)$ 时链走数据的折叠, 与 `PsiR` 同形 (`st` 给类). $(h_0,k)=(0,0)$ 时链是值, **不要 `st`**: 输入 $\ulcorner a\urcorner$ 对任何类都好 (`GdV`), 世界是 $1$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNodeX where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
import OCF.Free.Level as FL
open FL using (_≅_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; ⊲-tr; lg⊲; z⊲; ≪S; ≪∘; ≪⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumPsi using (ψQ)
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (WF; WFL; ψW; ψL′; ΩW; Ωfst; hWi; hWd; hMi; hMd)
open import OCF.Align.NoCumForce using (outs; Fp; fq; fs; fl; Fp-mono; ⊴→Fp; Fp→Pj)
open import OCF.Align.NoCumNodeE hiding (zP)
open import OCF.Align.Om1HnCx using (⊴₀-tr; ⊴₀-l; ⊴₀-r; ≅₀-refl; ≅₀-sym; ≅₀-trans; Fp-z)
open import OCF.Align.NoCumNodeCx
open import OCF.Align.NoCumNodeGd
open import OCF.Align.NoCumNodeOmega using (ΩG; ⊤₁; tt₁)
open import OCF.Align.NoCumNodePsi using (Psi; mxF)
```

## §1 值的读回对任何类都好

```agda
GdV : ∀ (𝓓 : Cl) a → Gd 𝓓 ⌜ a ⌝
GdV 𝓓 FL.zero = tt₂
GdV 𝓓 (FL.suc a) = osr (λ _ → ⊤₁) (λ _ → tt₁) (GdV (λ _ → ⊤₁) a) (λ _ _ → tt₁) (λ _ r d o → o , Fp-z _)
GdV 𝓓 (FL.lim f) = λ n → GdV 𝓓 (f n)
GdV 𝓓 (FL.limᵢ () f)
GdV 𝓓 (FL.up () x)

lfv⊴ : ∀ {m} (gm : Gw m) {a b} → a ⊴₀ b → lfv gm a ⊴ lfv gm b
lfv⊴ gm p = lw₂ (rw (⌜⌝⊴ p))

zt : ∀ h k → Is0 h k ⊎ Nz h k
zt zero azero = inj₁ is0
zt zero (asuc c) = inj₂ nza
zt zero (alim f) = inj₂ nzl
zt (suc h) k = inj₂ nzs

record Cell {p a u m} (um : u ⊲ m) (am : a ⊲ m) (𝓑 : A → Cl) (h : ∀ {v} → u ⊲ v → Gw v → 𝓞 p a v) : Set₁ where
  field
    y    : Ord₀
    v    : A
    tie  : v ≈ᴬ rd y
    gv′  : Gw v
    up′  : m ⊲ v
    bb   : 𝓑 v idC
    Gh   : Ev (h (⊲-tr um up′) gv′) gv′ v gv′ C.self (⊲-tr am up′)
    st   : y ⊴₀ val (h (⊲-tr um up′) gv′) Gh
open Cell
```

## §2 出口

```agda
X : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) → x ≈ x → WF x → (𝓖 : Cl) → 𝓖 idC → Gd 𝓖 x → Ev x gu v gv uv av
X⁰ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a → x ≈ x → WF x → (𝓖 : Cl) → 𝓖 idC → Gd 𝓖 x → E x gu m gm um am
XL : ∀ {p h k u a} (j : h <ᴺ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (km : k ⊲ m) (am : a ⊲ m) → outL j x ≈ outL j x → WFL j x → (𝓖 : Cl) → 𝓖 idC → GdL j 𝓖 x → EL {a = a} j x gu m gm um km am
XR : ∀ {p a u h₀ k} {Y : A → Set} (out : ∀ {v} → Y v → 𝓞 h₀ k v) (inn : ∀ {v} → 𝓞 h₀ k v → Y v) (oin : ∀ {v} (z : 𝓞 h₀ k v) → out (inn z) ≡ z)
     {GZ : Cl → ∀ {v} → Y v → Set₂} (h : ∀ {v} → u ⊲ v → Gw v → Y v → 𝓞 p a v) m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) (kM : k ⊲ m) (𝓖 : Cl) → 𝓖 idC →
     (∀ z → z ≈ z → h um gm (inn z) ≈ h um gm (inn z)) → (∀ z → z ≈ z → WF z → WF (h um gm (inn z))) →
     (∀ {z z′} → z ⊴ z′ → h um gm (inn z) ⊴ h um gm (inn z′)) →
     (∀ (𝓓 : Cl) {v} (z : 𝓞 h₀ k v) → Gd 𝓓 z → GZ 𝓓 (inn z)) →
     Is0 h₀ k ⊎ Nz h₀ k →
     BrR 𝓖 p h₀ k u Y out GZ (λ 𝓔 q₁ g y → Gd 𝓔 (h q₁ g y)) →
     Rs gm am kM (λ z → h um gm (inn z)) (λ z → Ev (h um gm (inn z)) gm m gm C.self am) (λ z d → val (h um gm (inn z)) d)

X x gu v gv uv av e w 𝓖 i g = X⁰ x gu _ _ _ _ (Mi gu gv uv av) e w 𝓖 i g

X⁰ o0 gu m gm um am is e w 𝓖 i g = tt
X⁰ (os x) gu m gm um am is (_ , _ , _ , e) w 𝓖 i (osr 𝓚 inc gK clk hon) = X x gu m gm um am e w 𝓚 (inc i) gK
X⁰ (ol F) gu m gm um am is e (st₁ , u₁) 𝓖 i g = Es , (λ n → val⊴ᵉ (st₁ n) (Es n) (Es (suc n)))
  where
  Es : ∀ n → Ev (F n) gu m gm um am
  Es n = X (F n) gu m gm um am (e n) (u₁ n) 𝓖 i (g n)
X⁰ {p} (oi {k = k} r h) gu m gm um am is (_ , _ , _ , _ , N) w 𝓖 i g =
  XR (outS (≪S r)) (inS (≪S r)) (out-inS (≪S r)) h m gm um am (⊲-tr (≪⊲ r) am) 𝓖 i
    (λ z e′ → nI {r = r} {r} {h} {h} N um um gm gm (≈ᴬ-refl m) z z e′) (λ z e′ w′ → hWi {r = r} w um gm z e′ w′)
    (λ d → hMi {r = r} w um gm d)
    (λ 𝓓 z gz → G→S (≪S r) 𝓓 (inS (≪S r) z) (subst (Gd 𝓓) (sym (out-inS (≪S r) z)) gz)) (zt p k) g
X⁰ (od {h = h₀} j k r h) gu m gm um am is (_ , _ , _ , _ , _ , N) w 𝓖 i g =
  XR (outL j) (inL j) (out-inL j) h m gm um am (⊲-tr (≪⊲ r) um) 𝓖 i
    (λ z e′ → nD {j = j} {j} {h} {h} N um um gm gm (≈ᴬ-refl m) z z e′) (λ z e′ w′ → hWd {i = j} {r = r} w um gm z e′ w′)
    (λ d → hMd {i = j} {r = r} w um gm d)
    (λ 𝓓 z gz → G→L j 𝓓 (inL j z) (subst (Gd 𝓓) (sym (out-inL j z)) gz)) (zt h₀ k) g
X⁰ {p} {a} {u} (oc x h) gu m gm um am is (_ , _ , _ , ex , N) (fi , dr , wx , wh) 𝓖 i (ocr 𝓑 g₁ gH gd ch₀ chS) =
  oc′ G₀ (λ n → v (cell n)) (λ n → gv′ (cell n)) (λ n → up′ (cell n)) (λ n → Gh (cell n))
      (tie (cell 0)) (λ n → tie (cell (suc n))) (st (cell 0)) (λ n → st (cell (suc n)))
  where
  G₀ : Ev x gu m gm um am
  G₀ = X x gu m gm um am ex wx 𝓖 i g₁
  y₀ = val x G₀
  T₀ : Tm
  T₀ = tmk x gu m gm um am
  R₀ : Rn idC x T₀
  R₀ = idr gu m gm um am
  mkG : ∀ {q} (q₁ : m ⊲ q) (g : Gw q) → 𝓑 q idC → Ev (h (⊲-tr um q₁) g) g q g C.self (⊲-tr am q₁)
  mkG {q} q₁ g b = X (h (⊲-tr um q₁) g) g q g C.self (⊲-tr am q₁) (N (⊲-tr um q₁) (⊲-tr um q₁) g g (≈ᴬ-refl q)) (wh (⊲-tr um q₁) g) (𝓖 ∧ 𝓑 q) (i , b) (gH (⊲-tr um q₁) g)
  P₀ = lit y₀ (Lit-val x G₀)
  fpm : Fp m y₀
  fpm = mxF is (proj₁ (gd i R₀ G₀)) (Fp-z y₀) (proj₂ (gd i R₀ G₀))
  b₀ = Fp→Pj fpm (eq P₀)
  r₀ = graftA (g P₀) (pa b₀) (lg P₀) m (lgw gm) (≈ᴬ-sym (pe b₀))
  v₀ = g (gE r₀)
  tie₀ : v₀ ≈ᴬ rd y₀
  tie₀ = ≈ᴬ-trans (eq (gE r₀)) (eq P₀)
  gv₀ : Gw v₀
  gv₀ = gw (lg (gE r₀)) (⊲-tr (pos gm) (at r₀))
  bb₀ : 𝓑 v₀ idC
  bb₀ = ch₀ i R₀ G₀ gv₀ tie₀ (⊲-tr um (at r₀))
  cell : ℕ → Cell um am 𝓑 h
  cell zero = record { y = y₀ ; v = v₀ ; tie = tie₀ ; gv′ = gv₀ ; up′ = at r₀ ; bb = bb₀ ; Gh = mkG (at r₀) gv₀ bb₀ ; st = val⊴ᵉ (fi (⊲-tr um (at r₀)) gv₀) G₀ (mkG (at r₀) gv₀ bb₀) }
  cell (suc n) = record { y = y′ ; v = v′ ; tie = tie′ ; gv′ = gv″ ; up′ = up″ ; bb = bb′ ; Gh = mkG up″ gv″ bb′ ; st = val⊴ᵉ (dr (⊲-tr um (up′ c)) (⊲-tr um up″) (gv′ c) gv″ (at gr₁)) (Gh c) (mkG up″ gv″ bb′) }
    where
    c = cell n
    y′ = val _ (Gh c)
    gr₁ : Gr (rd y′) (v c)
    gr₁ = graft₀ (st c) (lit y′ (Lit-val _ (Gh c))) (el (v c) (tie c) (lgw (gv′ c)))
    v′ = g (gE gr₁)
    tie′ = eq (gE gr₁)
    gv″ : Gw v′
    gv″ = gw (lg (gE gr₁)) (⊲-tr (pos (gv′ c)) (at gr₁))
    up″ : m ⊲ v′
    up″ = ⊲-tr (up′ c) (at gr₁)
    bb′ : 𝓑 v′ idC
    bb′ = chS (⊲-tr um (up′ c)) (gv′ c) i (bb c) (idr (gv′ c) (v c) (gv′ c) C.self (⊲-tr am (up′ c))) (Gh c) gv″ tie′ (at gr₁)
X⁰ (oe es x) gu m gm um am is e w 𝓖 i g = X x gu m gm um (⊲-tr (C.suc C.self) am) (≈oe⁻ {R = ss C.self} x es x e) w 𝓖 i g
X⁰ (oe (el n) x) gu m gm um am is e w 𝓖 i g = X x gu m gm um (⊲-tr (C.lim n C.self) am) (≈oe⁻ {R = sl n C.self} x (el n) x e) w 𝓖 i g
X⁰ (oL j k e₁ x) gu m gm um am is e w 𝓖 i g = XL j x gu m gm um (⊲-tr e₁ um) am (≈oL⁻ (outL j x) j e₁ x (Ll→ j x e)) w 𝓖 i g
X⁰ (ow p₁ g′ x) gu m gm um am is e w 𝓖 i g = X x g′ m gm (⊲-tr p₁ um) am (≈ow⁻ x p₁ g′ x e) w 𝓖 i g

XL zero x gu m gm um km am e w 𝓖 i g = X x gu m gm um km e w 𝓖 i g
XL (suc j) x gu m gm um km am e w 𝓖 i g = XL j x gu m gm um km am e w 𝓖 i g

XR {p} {a} {u} {h₀} {k} {Y} out inn oin {GZ} h m gm um am kM 𝓖 i N₁ W₁ Mo zg (inj₂ nz) (brr 𝓖₀ W₀ inc wf vis st₂ prem) =
  rg nz Es (λ n → val⊴ᵉ (Mo (zS n)) (Es n) (Es (suc n)))
  where
  zz : ℕ → 𝓞 h₀ k m
  zz = chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inn z₁)) gm m gm C.self kM am)
  zP : ∀ j → zz j ≈ zz j
  zP zero = ≈-Ωat h₀ gm gm (≈ᴬ-refl k)
  zP (suc j) = ψQ (h um gm (inn (zz j))) (h um gm (inn (zz j))) gm gm m gm C.self kM am m gm C.self kM am (≈ᴬ-refl k) (N₁ _ (zP j))
  zW : ∀ j → WF (zz j)
  zW zero = ΩW h₀ k (lg⊲ kM (lgw gm))
  zW (suc j) = ψW h₀ k (h um gm (inn (zz j))) gm m gm C.self kM am (N₁ _ (zP j)) (W₁ _ (zP j) (zW j))
  zS : ∀ j → zz j ⊴ zz (suc j)
  zS zero = Ωfst h₀ k (h um gm (inn (zz zero))) gm m gm C.self kM am
  zS (suc j) = ψL′ h₀ k (Mo (zS j)) gm gm m gm C.self kM am m gm C.self kM am
  Gz : ∀ j → Gd (Im W₀ 𝓖₀) (zz j)
  Gz zero = Gd-mono (λ { (im C₁ c refl) → vb (vis c) }) (Ω̇ h₀ k) (ΩG h₀ k)
  Gz (suc j) =
    Psi h₀ k (h um gm (inn (zz j))) gm m gm C.self kM am 𝓖₀ (Im W₀ 𝓖₀)
      (λ { (im C₁ c refl) → st₂ c (over (λ { t₂ (rψ gx v gv uv tv av r) → ov (ψ h₀ k t₂ gx v gv uv tv av) gv tv r (Ωfst h₀ k t₂ gx v gv uv tv av) }) (λ i₁ → tt)) })
      (λ { (im C₁ c refl) → vis c })
      (N₁ _ (zP j)) (W₁ _ (zP j) (zW j))
      (prem 𝓖₀ (λ c → c) um gm (inn (zz j)) (subst (λ t₁ → t₁ ≈ t₁) (sym (oin _)) (zP j)) (subst WF (sym (oin _)) (zW j)) (zg (Im W₀ 𝓖₀) (zz j) (Gz j)))
  Es : ∀ n → Ev (h um gm (inn (zz n))) gm m gm C.self am
  Es n = X (h um gm (inn (zz n))) gm m gm C.self am (N₁ _ (zP n)) (W₁ _ (zP n) (zW n)) 𝓖 i
    (prem 𝓖 inc um gm (inn (zz n)) (subst (λ t₁ → t₁ ≈ t₁) (sym (oin _)) (zP n)) (subst WF (sym (oin _)) (zW n))
      (zg (Im W₀ 𝓖) (zz n) (Gd-mono (λ { (im C₁ c refl) → im C₁ (inc c) refl }) (zz n) (Gz n))))
XR {p} {a} {u} {Y = Y} out inn oin {GZ} h m gm um am kM 𝓖 i N₁ W₁ Mo zg (inj₁ is0) (brr 𝓖₀ W₀ inc wf vis st₂ prem) =
  rv is0 vz Es tS St
  where
  Ee : ∀ a → Lit₀ a → Ev (h um gm (inn (lfv gm a))) gm m gm C.self am
  Ee a La = X (h um gm (inn zₐ)) gm m gm C.self am (N₁ _ eₐ) (W₁ _ eₐ wₐ) 𝓖 i
    (prem 𝓖 inc um gm (inn zₐ) (subst (λ t₁ → t₁ ≈ t₁) (sym (oin zₐ)) eₐ) (subst (λ t₁ → WF t₁) (sym (oin zₐ)) wₐ) (zg (Im W₀ 𝓖) zₐ (GdV (Im W₀ 𝓖) a)))
    where
    zₐ : 𝓞 zero azero m
    zₐ = lfv gm a
    eₐ : zₐ ≈ zₐ
    eₐ = ez gm gm (≅₀-refl a)
    wₐ : WF zₐ
    wₐ = ⌜⌝W a La
  cell : ℕ → Σ Ord₀ Lit₀
  cell zero = v₁ , tt
  cell (suc n) = val _ (Ee (proj₁ (cell n)) (proj₂ (cell n))) , Lit-val _ (Ee (proj₁ (cell n)) (proj₂ (cell n)))
  vz : ℕ → Ord₀
  vz n = proj₁ (cell (suc n))
  Es : ∀ n → Ev (h um gm (inn (lfv gm (outs v₁ vz n)))) gm m gm C.self am
  Es zero = Ee v₁ tt
  Es (suc n) = Ee (vz n) (proj₂ (cell (suc n)))
  tS : ∀ n → vz n ≅ val _ (Es n)
  tS zero = ≅₀-refl _
  tS (suc n) = ≅₀-refl _
  Sz : ∀ n → outs v₁ vz n ⊴₀ outs v₁ vz (suc n)
  St : ∀ n → val _ (Es n) ⊴₀ val _ (Es (suc n))
  Sz zero = Fp→⊴₁ (one-val _ (Es 0))
  Sz (suc n) = ⊴₀-l (tS n) (⊴₀-r (St n) (≅₀-sym (tS (suc n))))
  St n = val⊴ᵉ (Mo (lfv⊴ gm (Sz n))) (Es n) (Es (suc n))
```

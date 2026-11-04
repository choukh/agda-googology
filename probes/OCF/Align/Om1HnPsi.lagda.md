# $\psi_0(\Omega_{\Omega+1})$, 不累加: 折叠保 `Gd`

> 不含记号. 结论写在 [Om1Hn](Om1Hn.lagda.md). `Psi`: $x$ 对 $\mathcal X$ 好, 类 $\mathcal G$ 里的 $C$ 看得见目标 ($C\in$ `𝓥′ q t`) 且 $C\circ\psi_{q,t}\in\mathcal X$, 则 $\psi_{q,t}x$ 对 $\mathcal G$ 好. 对项递归, 与 [NoCumMain](NoCumMain.lagda.md) 的 `ψW` 同形, 不按阶段分.
>
> 上升的情形 (`PsiR`) 是全文的要点: 链 $z_n$ 对 $\{W\,C : C\in\mathcal G_0\}$ 好; `st` 说 $W\,C\circ\psi_{h_0,k}\in\mathcal G_0$, 因为它的运行都压过 $\Omega_{h_0,k}$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Om1HnPsi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; ⊲-tr; lg⊲; z⊲; ≪S; ≪∘; ≪⊲; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumLit using (_⊴₀_; Ord₀; ≈ᴬ-refl; r0)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq
open import OCF.Align.NoCumPsi using (ψQ)
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (WF; WFL; ψW; ΩW; Ωfst; hWi; hWd)
open import OCF.Align.NoCumForce hiding (Cl; C′)
open import OCF.Align.Om1HnCx
open import OCF.Align.Om1HnGd hiding (X)
open import OCF.Align.Om1HnAdd
open import OCF.Align.Om1HnOmega using (ΩG)
```

## §1 上下文沿地板上升

```agda
record Up (q : ℕ) (t : A) (C : Cx) {w} {y : 𝓡 w} (d : G y) : Set where
  constructor up
  field
    {u₁} : A
    z₁ : 𝓞 q t u₁
    g₁ : Gw u₁
    tu : t ⊲ u₁
    ω₁ : Ω̇at q t g₁ ⊴ z₁
    {w₁} : A
    {y₁} : 𝓡 w₁
    r₁ : Rn C z₁ y₁
    d₁ : G y₁
    s₁ : force d₁ ⊴₀ force d

vUp : ∀ {q t C C′} → 𝓥′ q t C → (∀ {p′} → p′ <ᴺ q → Hb C′ p′) →
      (∀ {p a u} (z : 𝓞 p a u) {w} {y : 𝓡 w} → Rn C′ z y → (d : G y) → Up q t C d) → 𝓥′ q t C′
vUp {q} {t} {C} {C′} (vt (vv fo se) vs₀) hb upp = vt (vv fo′ se′) vs′
  where
  fo′ : Fo q C′
  fo′ i = (λ z r d → let U = upp z r d in Fp-mono (proj₂ (vs₀ (Up.z₁ U) (Up.g₁ U) (Up.tu U) (Up.ω₁ U) (Up.r₁ U) (Up.d₁ U))) (Up.s₁ U)) , hb i
  se′ : ∀ {c} → c ≪ t → Sees C′ q c
  se′ r′ z gz cu ω r d with upp z r d
  ... | up z₁ g₁ tu ω₁ r₁ d₁ s₁ with dn C hom g₁ ω₁ C.self r₁ d₁
  ...   | _ , _ , r₂ , d₂ , s₂ =
    let f = se r′ (Ω̇at q t g₁) g₁ (⊲-tr (≪⊲ r′) tu) (lw₂ (rw (Ω⊴ q (≪⊲ r′)))) r₂ d₂
    in Fp-mono (proj₁ f) (⊴₀-tr s₂ s₁) , Fp-mono (proj₂ f) (⊴₀-tr s₂ s₁)
  vs′ : Sees C′ q t
  vs′ z gz cu ω r d with upp z r d
  ... | up z₁ g₁ tu ω₁ r₁ d₁ s₁ =
    let f = vs₀ z₁ g₁ tu ω₁ r₁ d₁ in Fp-mono (proj₁ f) s₁ , Fp-mono (proj₂ f) s₁

upψ : ∀ {q t C w} {y : 𝓡 w} {p a u} {x : 𝓞 p a u} → Rψ C q t x y → (d : G y) → Up q t C d
upψ {q} {t} {x = x} (rψ gx v gv uv tv av r) d = up (ψ q t x gx v gv uv tv av) gv tv (Ωfst q t x gx v gv uv tv av) r d (r0 (≅₀-refl _))

hAψ : ∀ {q t C C′ D h₀ k} → 𝓥′ q t C → (∀ {p a u w} {z : 𝓞 p a u} {y : 𝓡 w} → Rn D z y → Tr (Fψ C q t) y) → Over q h₀ k C′ D → 𝓥′ q t C′
hAψ a wfD o = vUp a (ovb o) (λ z r d → aux (wfD (Ov.rz (ovr o z r))) d)
  where
  aux : ∀ {C q t w} {y : 𝓡 w} → Tr (Fψ C q t) y → (d : G y) → Up q t C d
  aux (tr t′ r′) d = upψ r′ d

liftψ : ∀ {q t C p a u w} {t₁ : 𝓞 p a u} {y : 𝓡 w} → Rn (Fψ C q t) t₁ y → Tr C y
liftψ (rψ gx v gv uv tv av r) = tr _ r

ovψ : ∀ {q t q₁ h₀ k C′ D} → Over q h₀ k C′ D → Over q₁ h₀ k (Fψ C′ q t) D
ovψ o = over (λ { t (rψ gx v gv uv tv av r) → ovr o _ r }) (λ i → tt)

mxF : ∀ {m u t a} {y : Ord₀} → Mis m u t a → Fp u y → Fp t y → Fp a y → Fp m y
mxF (iu refl) a b c = a
mxF (it refl) a b c = b
mxF (ia refl) a b c = c
```

## §2 主定理

```agda
Psi : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) (𝓧 𝓖 : Cl) →
      (∀ {C} → 𝓖 C → 𝓧 (Fψ C q t)) → (∀ {C} → 𝓖 C → 𝓥′ q t C) → x ≈ x → WF x → Gd 𝓧 x → Gd 𝓖 (ψ q t x gu v gv uv tv av)
Psim : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v) (𝓧 𝓖 : Cl) →
      (∀ {C} → 𝓖 C → 𝓧 (Fψ C q t)) → (∀ {C} → 𝓖 C → 𝓥′ q t C) → x ≈ x → WF x → Gd 𝓧 x → Gd 𝓖 (ψᵐ q t x gu v gv uv tv av)
Psi⁰ : ∀ {p a u} q t (x : 𝓞 p a u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a → (𝓧 𝓖 : Cl) →
      (∀ {C} → 𝓖 C → 𝓧 (Fψ C q t)) → (∀ {C} → 𝓖 C → 𝓥′ q t C) → x ≈ x → WF x → Gd 𝓧 x → Gd 𝓖 (ψ⁰ q t x gu m gm um tm am)
PsiL : ∀ {p h k u} q t (j : h <ᴺ p) (x : Low p j k u) (gu : Gw u) m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (km : k ⊲ m) (𝓧 𝓖 : Cl) →
      (∀ {C} → 𝓖 C → 𝓧 (Fψ C q t)) → (∀ {C} → 𝓖 C → 𝓥′ q t C) → outL j x ≈ outL j x → WFL j x → GdL j 𝓧 x → Gd 𝓖 (ψL q t j x gu m gm um tm km)
PsiR : ∀ {p a u h₀ k} {Y : A → Set} (out : ∀ {v} → Y v → 𝓞 h₀ k v) (inn : ∀ {v} → 𝓞 h₀ k v → Y v) (oin : ∀ {v} (z : 𝓞 h₀ k v) → out (inn z) ≡ z)
       {GZ : Cl → ∀ {v} → Y v → Set₂} (h : ∀ {v} → u ⊲ v → Gw v → Y v → 𝓞 p a v) q t m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) (kM : k ⊲ m) (𝓧 𝓖 : Cl) →
       (∀ {C} → 𝓖 C → 𝓧 (Fψ C q t)) → (∀ {C} → 𝓖 C → 𝓥′ q t C) →
       (∀ z → z ≈ z → h um gm (inn z) ≈ h um gm (inn z)) → (∀ z → z ≈ z → WF z → WF (h um gm (inn z))) →
       (∀ (𝓓 : Cl) {v} (z : 𝓞 h₀ k v) → Gd 𝓓 z → GZ 𝓓 (inn z)) →
       BrR 𝓧 p h₀ k u Y out GZ (λ 𝓔 q₁ g y → Gd 𝓔 (h q₁ g y)) →
       ∀ n → Gd 𝓖 (ψ q t (h um gm (inn (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inn z₁)) gm m gm C.self kM am) n))) gm m gm C.self tm am)

Psi q t x gu v gv uv tv av 𝓧 𝓖 H H₂ e w g = Psim q t x gu v gv uv tv av 𝓧 𝓖 H H₂ e w g

Psim q t x gu v gv uv tv av 𝓧 𝓖 H H₂ e w g with mx gu gv uv tv av | mx-is gu gv uv tv av
... | mx′ m gm um tm am mv | is = Psi⁰ q t x gu m gm um tm am is 𝓧 𝓖 H H₂ e w g

Psi⁰ q t o0 gu m gm um tm am is 𝓧 𝓖 H H₂ e w g = Gd-mono (λ c → vb (H₂ c)) (Ω̇ q t) (ΩG q t)
Psi⁰ {p} {a} {u} q t (os x₀) gu m gm um tm am is 𝓧 𝓖 H H₂ (_ , _ , _ , e) w (osr 𝓚 inc gK clk hon) =
  λ n → Gd-mono (λ c → H₂ c , inc (H c)) (rep X gm n) (repG n)
  where
  𝓐 : Cl
  𝓐 C = 𝓥′ q t C × 𝓚 (Fψ C q t)
  X = ψ q t x₀ gu m gm um tm am
  eX : X ≈ X
  eX = ψQ x₀ x₀ gu gu m gm um tm am m gm um tm am (≈ᴬ-refl t) e
  eRe : ∀ n → rep X gm n ≈ rep X gm n
  eRe = rep≈ (≈ᴬ-refl t) (≈ᴬ-refl m) eX gm gm
  Yfl : ∀ {p₀ a₀ w₀} {Y : 𝓞 p₀ a₀ w₀} → Y ⊴ X → ∀ n → Y ⊴ rep X gm (suc n)
  Yfl d zero = d
  Yfl d (suc n) = AddF.add⊴ (rep X gm (suc n)) gm (Yfl d n) (sa C.self) X gm m gm C.self C.self (z⊲ m)
  XX : X ⊴ X
  XX = rf eX
  ΩX : Ω̇at q t gm ⊴ X
  ΩX = Ωfst q t x₀ gu m gm um tm am
  -- 地板: C″ 的运行压过 O 上 W 的运行
  floorV : ∀ n {O C″} → 𝓥′ q t O → (∀ {p′} → p′ <ᴺ q → Hb C″ p′) →
           (∀ {p₂ a₂ u₂} (t₂ : 𝓞 p₂ a₂ u₂) {w₂} {y : 𝓡 w₂} → Rn C″ t₂ y → (d : G y) → Σ A λ w₀ → Σ (𝓡 w₀) λ y₀ → Rn O (rep X gm (suc n)) y₀ × Σ (G y₀) λ d₀ → force d₀ ⊴₀ force d) → 𝓥′ q t C″
  floorV n cv hb fle = vUp cv hb (λ z r d → let _ , _ , r₀ , d₀ , s₀ = fle z r d in up (rep X gm (suc n)) gm tm (Yfl ΩX n) r₀ d₀ s₀)
  flX : ∀ n {O C″} → 𝓚 (Fψ O q t) →
        (∀ {p₂ a₂ u₂} (t₂ : 𝓞 p₂ a₂ u₂) {w₂} {y : 𝓡 w₂} → Rn C″ t₂ y → (d : G y) → Σ A λ w₀ → Σ (𝓡 w₀) λ y₀ → Rn O (rep X gm (suc n)) y₀ × Σ (G y₀) λ d₀ → force d₀ ⊴₀ force d) → 𝓚 (Fψ C″ q t)
  flX n {O} {C″} ck fle = clk ck (flo (λ { t₂ (rψ gx v gv uv tv av r) d →
    let _ , _ , r₀ , d₀ , s₀ = fle _ r d in
    let _ , _ , r₂ , d₂ , s₂ = dn O hom gm (Yfl XX n) C.self r₀ d₀ in
    _ , _ , rψ gu m gm um tm am r₂ , d₂ , ⊴₀-tr s₂ s₀ }) (λ i → tt))
  clA : ∀ n {O C″} → 𝓐 O → FlOver (rep X gm (suc n)) O C″ → 𝓐 C″
  clA n (cv , ck) f = floorV n cv (flb f) (flr f) , flX n ck (flr f)
  hoA : ∀ n {C} → 𝓐 C → ∀ {w₁} {y : 𝓡 w₁} → Rn C (rep X gm (suc n)) y → (d : G y) → Fp m (force d) × Fp t (force d)
  hoA n {C} (cv , ck) r d with vs cv (rep X gm (suc n)) gm tm (Yfl ΩX n) r d
  ... | ft , _ with dn C hom gm (Yfl XX n) C.self r d
  ...   | _ , _ , r₂ , d₂ , s₂ =
    let hx = hon ck (rψ gu m gm um tm am r₂) d₂ (proj₂ (vs cv X gm tm ΩX r₂ d₂))
    in mxF is (Fp-mono (proj₁ hx) s₂) ft (Fp-mono (proj₂ hx) s₂) , ft
  press : ∀ n {C} → 𝓐 C → 𝓐 (Fa C (rep X gm (suc n)) gm (eRe (suc n)))
  press n {C} (cv , ck) =
    floorV n cv (λ i → i) (λ { z (ra L gx v gv uv xv bv r) d → dn C hom gm (AddF.add⊴ W₂ gm (rf (eRe (suc n))) L z gx v gv uv xv bv) uv r d }) ,
    clk ck (flo (λ { t₂ (rψ gx v gv uv tv av (ra L g₂ v₂ gv₂ uv₂ xv₂ bv₂ r)) d →
      let _ , _ , r₂ , d₂ , s₂ = dn C hom gm (AddF.add⊴ W₂ gm (Yfl XX n) L _ g₂ v₂ gv₂ uv₂ xv₂ bv₂) uv₂ r d
      in _ , _ , rψ gu m gm um tm am r₂ , d₂ , s₂ }) (λ i → tt))
    where
    W₂ = rep X gm (suc n)
  gX : Gd 𝓐 X
  gX = Psi q t x₀ gu m gm um tm am 𝓚 𝓐 proj₂ proj₁ e w gK
  repG : ∀ n → Gd 𝓐 (rep X gm n)
  repG zero = tt₂
  repG (suc zero) = gX
  repG (suc (suc n)) =
    AddG.Add (rep X gm (suc n)) gm (eRe (suc n)) 𝓐 (repG (suc n)) (clA n) (hoA n)
      (sa C.self) X gm m gm C.self C.self (z⊲ m) 𝓐 𝓐 (λ c → c) (press n) gX
Psi⁰ q t (ol F) gu m gm um tm am is 𝓧 𝓖 H H₂ e (st₁ , u₁) g = λ n → Psi q t (F n) gu m gm um tm am 𝓧 𝓖 H H₂ (e n) (u₁ n) (g n)
Psi⁰ {p} {a} q t (oi {k = k} r h) gu m gm um tm am is 𝓧 𝓖 H H₂ (_ , _ , _ , _ , N) w g with <ᴺ-dec p q
... | injᵃ i =
  brMap g (λ C → Fψ C q t) (𝓥′ q t) liftψ (λ c → H₂ c , H c) (λ a₁ c o → hAψ a₁ (λ r₁ → BrR.wf g c r₁) o) ovψ
    (λ y → inS (≪S r) (outL i y)) (λ q₁ → ⊲-tr um q₁) (λ y → out-inS (≪S r) (outL i y))
    (λ 𝓓 y z → L→G i 𝓓 y z) (λ 𝓓 y z → G→S (≪S r) 𝓓 y z)
    (λ 𝓔 {v} q₁ g₁ y e′ w′ sub gf →
      Psi q t (h (⊲-tr um q₁) g₁ (inS (≪S r) (outL i y))) g₁ v g₁ C.self (⊲-tr tm q₁) (⊲-tr am q₁) (Im (λ C → Fψ C q t) 𝓔) 𝓔 (λ c → im _ c refl) (λ c → proj₁ (sub c))
        (nI {r = r} {r} {h} {h} N (⊲-tr um q₁) (⊲-tr um q₁) g₁ g₁ (≈ᴬ-refl v) _ _ e′) (hWi {r = r} w (⊲-tr um q₁) g₁ _ e′ w′) gf)
... | injᵇ _ =
  PsiR (outS (≪S r)) (inS (≪S r)) (out-inS (≪S r)) h q t m gm um tm am (⊲-tr (≪⊲ r) am) 𝓧 𝓖 H H₂
    (λ z e′ → nI {r = r} {r} {h} {h} N um um gm gm (≈ᴬ-refl m) z z e′) (λ z e′ w′ → hWi {r = r} w um gm z e′ w′)
    (λ 𝓓 z gz → G→S (≪S r) 𝓓 (inS (≪S r) z) (subst (Gd 𝓓) (sym (out-inS (≪S r) z)) gz)) g
... | injᶜ refl with cmpN (≪∘ r am) tm (lgw gm)
...   | keep s₁ =
  brMap g (λ C → Fψ C q t) (𝓥′ q t) liftψ (λ c → H₂ c , H c) (λ a₁ c o → hAψ a₁ (λ r₁ → BrR.wf g c r₁) o) ovψ
    (λ y → inS (≪S r) (outS (≪S s₁) y)) (λ q₁ → ⊲-tr um q₁) (λ y → out-inS (≪S r) (outS (≪S s₁) y))
    (λ 𝓓 y z → S→G (≪S s₁) 𝓓 y z) (λ 𝓓 y z → G→S (≪S r) 𝓓 y z)
    (λ 𝓔 {v} q₁ g₁ y e′ w′ sub gf →
      Psi q t (h (⊲-tr um q₁) g₁ (inS (≪S r) (outS (≪S s₁) y))) g₁ v g₁ C.self (⊲-tr tm q₁) (⊲-tr am q₁) (Im (λ C → Fψ C q t) 𝓔) 𝓔 (λ c → im _ c refl) (λ c → proj₁ (sub c))
        (nI {r = r} {r} {h} {h} N (⊲-tr um q₁) (⊲-tr um q₁) g₁ g₁ (≈ᴬ-refl v) _ _ e′) (hWi {r = r} w (⊲-tr um q₁) g₁ _ e′ w′) gf)
...   | rise _ =
  PsiR (outS (≪S r)) (inS (≪S r)) (out-inS (≪S r)) h q t m gm um tm am (⊲-tr (≪⊲ r) am) 𝓧 𝓖 H H₂
    (λ z e′ → nI {r = r} {r} {h} {h} N um um gm gm (≈ᴬ-refl m) z z e′) (λ z e′ w′ → hWi {r = r} w um gm z e′ w′)
    (λ 𝓓 z gz → G→S (≪S r) 𝓓 (inS (≪S r) z) (subst (Gd 𝓓) (sym (out-inS (≪S r) z)) gz)) g
Psi⁰ q t (od {h = h₀} j k r h) gu m gm um tm am is 𝓧 𝓖 H H₂ (_ , _ , _ , _ , _ , N) w g with <ᴺ-dec h₀ q
... | injᵃ i =
  brMap g (λ C → Fψ C q t) (𝓥′ q t) liftψ (λ c → H₂ c , H c) (λ a₁ c o → hAψ a₁ (λ r₁ → BrR.wf g c r₁) o) ovψ
    (λ y → inL j (outL i y)) (λ q₁ → ⊲-tr um q₁) (λ y → out-inL j (outL i y))
    (λ 𝓓 y z → L→G i 𝓓 y z) (λ 𝓓 y z → G→L j 𝓓 y z)
    (λ 𝓔 {v} q₁ g₁ y e′ w′ sub gf →
      Psi q t (h (⊲-tr um q₁) g₁ (inL j (outL i y))) g₁ v g₁ C.self (⊲-tr tm q₁) (⊲-tr am q₁) (Im (λ C → Fψ C q t) 𝓔) 𝓔 (λ c → im _ c refl) (λ c → proj₁ (sub c))
        (nD {j = j} {j} {h} {h} N (⊲-tr um q₁) (⊲-tr um q₁) g₁ g₁ (≈ᴬ-refl v) _ _ e′) (hWd {i = j} {r = r} w (⊲-tr um q₁) g₁ _ e′ w′) gf)
... | injᵇ _ =
  PsiR (outL j) (inL j) (out-inL j) h q t m gm um tm am (⊲-tr (≪⊲ r) um) 𝓧 𝓖 H H₂
    (λ z e′ → nD {j = j} {j} {h} {h} N um um gm gm (≈ᴬ-refl m) z z e′) (λ z e′ w′ → hWd {i = j} {r = r} w um gm z e′ w′)
    (λ 𝓓 z gz → G→L j 𝓓 (inL j z) (subst (Gd 𝓓) (sym (out-inL j z)) gz)) g
... | injᶜ refl with cmpN (≪∘ r um) tm (lgw gm)
...   | keep s₁ =
  brMap g (λ C → Fψ C q t) (𝓥′ q t) liftψ (λ c → H₂ c , H c) (λ a₁ c o → hAψ a₁ (λ r₁ → BrR.wf g c r₁) o) ovψ
    (λ y → inL j (outS (≪S s₁) y)) (λ q₁ → ⊲-tr um q₁) (λ y → out-inL j (outS (≪S s₁) y))
    (λ 𝓓 y z → S→G (≪S s₁) 𝓓 y z) (λ 𝓓 y z → G→L j 𝓓 y z)
    (λ 𝓔 {v} q₁ g₁ y e′ w′ sub gf →
      Psi q t (h (⊲-tr um q₁) g₁ (inL j (outS (≪S s₁) y))) g₁ v g₁ C.self (⊲-tr tm q₁) (⊲-tr am q₁) (Im (λ C → Fψ C q t) 𝓔) 𝓔 (λ c → im _ c refl) (λ c → proj₁ (sub c))
        (nD {j = j} {j} {h} {h} N (⊲-tr um q₁) (⊲-tr um q₁) g₁ g₁ (≈ᴬ-refl v) _ _ e′) (hWd {i = j} {r = r} w (⊲-tr um q₁) g₁ _ e′ w′) gf)
...   | rise _ =
  PsiR (outL j) (inL j) (out-inL j) h q t m gm um tm am (⊲-tr (≪⊲ r) um) 𝓧 𝓖 H H₂
    (λ z e′ → nD {j = j} {j} {h} {h} N um um gm gm (≈ᴬ-refl m) z z e′) (λ z e′ w′ → hWd {i = j} {r = r} w um gm z e′ w′)
    (λ 𝓓 z gz → G→L j 𝓓 (inL j z) (subst (Gd 𝓓) (sym (out-inL j z)) gz)) g
Psi⁰ q t (oc x h) gu m gm um tm am is 𝓧 𝓖 H H₂ (_ , _ , _ , ex , N) (fi , dr , wx , wf₁) (ocr 𝓑 g₁ gH gd ch₀ chS) =
  ocr (λ v C → 𝓑 v (Fψ C q t))
    (Psi q t x gu m gm um tm am 𝓧 𝓖 H H₂ ex wx g₁)
    (λ {v} w₁ g → Psi q t (h (⊲-tr um w₁) g) g v g C.self (⊲-tr tm w₁) (⊲-tr am w₁) (𝓧 ∧ 𝓑 v) _ (λ (c , b) → H c , b) (λ (c , b) → H₂ c)
       (N (⊲-tr um w₁) (⊲-tr um w₁) g g (≈ᴬ-refl v)) (wf₁ (⊲-tr um w₁) g) (gH (⊲-tr um w₁) g))
    (λ c r d →
       let hx = gd (H c) (rψ gu m gm um tm am r) d
           ft = proj₁ (vs (H₂ c) (ψ q t x gu m gm um tm am) gm tm (Ωfst q t x gu m gm um tm am) r d)
       in mxF is (proj₁ hx) ft (proj₂ hx) , ft)
    (λ c r d gv₁ t₁ q₁ → ch₀ (H c) (rψ gu m gm um tm am r) d gv₁ t₁ (⊲-tr um q₁))
    (λ {C} {v} q₁ g c b r d gv₁ t₁ q′ → chS (⊲-tr um q₁) g (H c) b (rψ g v g C.self (⊲-tr tm q₁) (⊲-tr am q₁) r) d gv₁ t₁ q′)
Psi⁰ q t (oe es x) gu m gm um tm am is 𝓧 𝓖 H H₂ e w g = Psi q t x gu m gm um tm (⊲-tr (C.suc C.self) am) 𝓧 𝓖 H H₂ (≈oe⁻ {R = ss C.self} x es x e) w g
Psi⁰ q t (oe (el n) x) gu m gm um tm am is 𝓧 𝓖 H H₂ e w g = Psi q t x gu m gm um tm (⊲-tr (C.lim n C.self) am) 𝓧 𝓖 H H₂ (≈oe⁻ {R = sl n C.self} x (el n) x e) w g
Psi⁰ q t (oL j k e₁ x) gu m gm um tm am is 𝓧 𝓖 H H₂ e w g = PsiL q t j x gu m gm um tm (⊲-tr e₁ um) 𝓧 𝓖 H H₂ (≈oL⁻ (outL j x) j e₁ x (Ll→ j x e)) w g
Psi⁰ q t (ow p₁ g′ x) gu m gm um tm am is 𝓧 𝓖 H H₂ e w g = Psi q t x g′ m gm (⊲-tr p₁ um) tm am 𝓧 𝓖 H H₂ (≈ow⁻ x p₁ g′ x e) w g

PsiL q t zero x gu m gm um tm km 𝓧 𝓖 H H₂ e w g = Psi q t x gu m gm um tm km 𝓧 𝓖 H H₂ e w g
PsiL q t (suc j) x gu m gm um tm km 𝓧 𝓖 H H₂ e w g = PsiL q t j x gu m gm um tm km 𝓧 𝓖 H H₂ e w g

PsiR {p} {a} {u} {h₀} {k} {Y} out inn oin {GZ} h q t m gm um tm am kM 𝓧 𝓖 H H₂ N₁ W₁ zg (brr 𝓖₀ W₀ inc wf vis st prem) n =
  Psi q t (h um gm (inn (zz n))) gm m gm C.self tm am 𝓧 𝓖 H H₂ (N₁ _ (zP n)) (W₁ _ (zP n) (zW n))
    (prem 𝓧 inc um gm (inn (zz n)) (subst (λ t₁ → t₁ ≈ t₁) (sym (oin _)) (zP n)) (subst WF (sym (oin _)) (zW n))
       (zg (Im W₀ 𝓧) (zz n) (Gd-mono (λ { (im C₁ c refl) → im C₁ (inc c) refl }) (zz n) (Gz n))))
  where
  zz : ℕ → 𝓞 h₀ k m
  zz = chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inn z₁)) gm m gm C.self kM am)
  zP : ∀ i → zz i ≈ zz i
  zP zero = ≈-Ωat h₀ gm gm (≈ᴬ-refl k)
  zP (suc i) = ψQ (h um gm (inn (zz i))) (h um gm (inn (zz i))) gm gm m gm C.self kM am m gm C.self kM am (≈ᴬ-refl k) (N₁ _ (zP i))
  zW : ∀ i → WF (zz i)
  zW zero = ΩW h₀ k (lg⊲ kM (lgw gm))
  zW (suc i) = ψW h₀ k (h um gm (inn (zz i))) gm m gm C.self kM am (N₁ _ (zP i)) (W₁ _ (zP i) (zW i))
  Gz : ∀ i → Gd (Im W₀ 𝓖₀) (zz i)
  Gz zero = Gd-mono (λ { (im C₁ c refl) → vb (vis c) }) (Ω̇ h₀ k) (ΩG h₀ k)
  Gz (suc i) =
    Psi h₀ k (h um gm (inn (zz i))) gm m gm C.self kM am 𝓖₀ (Im W₀ 𝓖₀)
      (λ { (im C₁ c refl) → st c (over (λ { t₂ (rψ gx v gv uv tv av r) → ov (ψ h₀ k t₂ gx v gv uv tv av) gv tv r (Ωfst h₀ k t₂ gx v gv uv tv av) }) (λ i₁ → tt)) })
      (λ { (im C₁ c refl) → vis c })
      (N₁ _ (zP i)) (W₁ _ (zP i) (zW i))
      (prem 𝓖₀ (λ c → c) um gm (inn (zz i)) (subst (λ t₁ → t₁ ≈ t₁) (sym (oin _)) (zP i)) (subst WF (sym (oin _)) (zW i)) (zg (Im W₀ 𝓖₀) (zz i) (Gz i)))
```

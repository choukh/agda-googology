# 验收: 第 0 层是值的 $\psi_0(\Omega_{\Omega+1})$

> **验收文件.** 只有本文件读记号 (`BTBOᴵ`, `Lab`). 结论写在 [NoCumNode](NoCumNode.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumNodeAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.Level using (_≅_; ≅-trans; ≅-sym; l≅; ≺l; ≺s; ≺z; ≅→⊑; _⊑⁰_; _≺_)
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
import OCF.Align.EBO as E′
open import OCF.Align.Correspond using (Lab; Lab-≅)
open import OCF.Align.Label using (BTBO-label)
open import OCF.Align.BTBOValNeg using (HS-≅)
open import OCF.Align.BTBOFullLv using (SV-L; pos-L; z<SV)
import OCF.Free.Level as FL
open import OCF.BTBO using (module Trich)
open Trich renaming (_<_ to _<ᴺ_) using () renaming (zero to zᴺ)
open import OCF.Align.CumReadCF using (azero; asuc; A; z⊲; _⊲_; ⊲-tr)
open import OCF.Align.CumReadCFThm using (Y)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumUpAcceptSim using (Ix; Ix-r; fr; Y-sim)
open import OCF.Align.NoCumLit using (⊴₀→⊑⁰; Ord₀; rd; _≈ᴬ_; _⊴₀_; r0; s0; l0; z≈; ≈ᴬ-refl)
open import OCF.Align.NoCumW
open import OCF.Align.NoCumEq using (_≈_; Ω≈; ≈-Ωat; Mis; iu)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.NoCumPsi using (ψQ)
open import OCF.Align.NoCumLe
open import OCF.Align.NoCumMain using (ψL′)
open import OCF.Align.NoCumForce using (outs; Fp)
open import OCF.Align.NoCumOmega using (T⁰)
open import OCF.Align.NoCumAcceptOmega using (Ix-rd; Ix-≈; T⁰≅; term)
open import OCF.Align.NoCumHnBridge using (Sq; Q-Ω; qw)
open import OCF.Align.NoCumHnAccept using (fr≅; ixOf)
open import OCF.Align.NoCumNodeE
open import OCF.Align.NoCumNodeBase using (V-Q)
open import OCF.Align.NoCumNodeMain using (G₁; GΩ; vᴱ; T₁)
open import OCF.Align.Om1HnCx using (⊴₀-tr; ⊴₀-l; ⊴₀-r; ≅₀-refl; ≅₀-trans; ≅₀-sym)
```

## §1 $\psi_0(\Omega_\Omega)$ 这一站不变

```agda
V₁ : ∀ {v u₁} (e : v ⊲ u₁) (y : 𝓞 0 v u₁) (w : C.Lg v) → Sq y (C.Ω̇ v) → (gu : Gw u₁) (v₂ : A) (gv : Gw v₂) (uv : u₁ ⊲ v₂) (av : azero ⊲ v₂)
     (d : Ev (oL {p = 1} {a = azero} zᴺ v e y) gu v₂ gv uv av) → vᴱ (oL {p = 1} {a = azero} zᴺ v e y) gu v₂ gv uv av d FL.≅ Y v w
V₁ {v} e y w q gu v₂ gv uv av d = V-Q (inj₁ (z⊲ v)) w q d

anyΩ : ∀ {m gm um am} (d : E (Ω̇ 1 azero) g₀ m gm um am) → fr (val (Ω̇ 1 azero) {g₀} {m} {gm} {um} {am} d) ≅ BTBOᴵ
anyΩ {m} {gm} {um} {am} (oc′ G₀ vs gv up₁ Gh t₀ tS s₀ sS) = l≅ outt
  where
  X₀ = oL {p = 1} {a = azero} zᴺ one C.self (Ω̇ 0 one)
  y₀ = vᴱ X₀ g₀ m gm um am G₀
  E₀ : fr y₀ ≅ N.γ 1
  E₀ = ≅-trans (fr≅ (V₁ C.self (Ω̇ 0 one) tt (Q-Ω one) g₀ m gm um am G₀)) (term 0)
  X₁ : ∀ n → 𝓞 1 azero (vs n)
  X₁ n = oL {p = 1} {a = azero} zᴺ (vs n) C.self (ow (pos (gv n)) g₀ (Ω̇ 0 (vs n)))
  yh : ℕ → Ord₀
  yh n = vᴱ (X₁ n) (gv n) (vs n) (gv n) C.self (⊲-tr am (up₁ n)) (Gh n)
  IX : ∀ n → Ix (vs n) (N.L (suc n))
  EE : ∀ n → fr (yh n) ≅ N.γ (suc (suc n))
  IX zero = ixOf y₀ t₀ E₀
  IX (suc n) = ixOf (yh n) (tS n) (EE n)
  EE n = ≅-trans (fr≅ (V₁ C.self _ (lgw (gv n)) (qw (Q-Ω (vs n))) (gv n) (vs n) (gv n) C.self (⊲-tr am (up₁ n)) (Gh n)))
                 (Y-sim (lgw (gv n)) (IX n) (z<SV (SV-L (suc n)) (pos-L (suc n))))
  outt : ∀ n → fr (outs y₀ yh n) ≅ N.γ (suc n)
  outt zero = E₀
  outt (suc n) = EE n

vΩ : Ord₀
vΩ = vᴱ (Ω̇ 1 azero) g₀ one g₀ C.self (z⊲ one) GΩ

same-Ω : fr vΩ ≅ BTBOᴵ
same-Ω = anyΩ GΩ

same-T⁰ : fr vΩ ≅ fr T⁰
same-T⁰ = ≅-trans same-Ω (≅-sym T⁰≅)

label-Ω : Lab (fr vΩ) (E′.EBOψ 2)
label-Ω = Lab-≅ same-Ω BTBO-label
```

## §2 第 0 项, 严格高于 $\psi_0(\Omega_\Omega)$

对任何证书 `d`. 路径: 第 1 项 $\psi_0(\psi_\Omega(\Omega_\Omega))$ 压过 $\psi_0(\psi_\Omega(1))$, 它的第 2 段是 $\psi_0(W\oplus W)$, $W=\Omega_\Omega$; $W\oplus W$ 压过 $W\oplus 1$, 计值是 $\lim\mathrm{rep}_0(b)$, $b=\psi_0(W)$, 第 2 段 $b+b\trianglerighteq b+1$.

```agda
record VW {p a u} (x : 𝓞 p a u) : Set where
  constructor vw
  field
    {gw₁} : Gw u
    {v₁′} : A
    {gv₁} : Gw v₁′
    {uv₁} : u ⊲ v₁′
    {av₁} : a ⊲ v₁′
    cW : Ev x gw₁ v₁′ gv₁ uv₁ av₁
vW : ∀ {p a u} {x : 𝓞 p a u} → VW x → Ord₀
vW {x = x} (vw {gw₁ = gw₁} {v₁′ = v₁′} {gv₁ = gv₁} {uv₁ = uv₁} {av₁ = av₁} c) = vᴱ x gw₁ v₁′ gv₁ uv₁ av₁ c

Ω₀⊴Ω₁ : Ω̇ 0 azero ⊴ Ω̇ 1 azero
Ω₀⊴Ω₁ = fc (rL {j = zᴺ} (Ω⊴ 0 (C.suc C.self)))

O₀ : 𝓞 0 azero one
O₀ = o0

Wo : ∀ {m₁} (g₁ : Gw m₁) (um₁ : one ⊲ m₁) (tm₁ am₁ : azero ⊲ m₁) → 𝓞 1 azero m₁
Wo g₁ um₁ tm₁ am₁ = ψ 1 azero O₀ g₀ _ g₁ um₁ tm₁ am₁

eW : ∀ {m₁} (g₁ : Gw m₁) (um₁ : one ⊲ m₁) (tm₁ am₁ : azero ⊲ m₁) → Wo g₁ um₁ tm₁ am₁ ≈ Ω̇ 1 azero
eW g₁ um₁ tm₁ am₁ with mx g₀ g₁ um₁ tm₁ am₁
... | mx′ m₂ g₂ um₂ tm₂ am₂ mv₂ = Ω≈ 1 z≈

eWW : ∀ {m₁} (g₁ : Gw m₁) (um₁ : one ⊲ m₁) (tm₁ am₁ : azero ⊲ m₁) → Wo g₁ um₁ tm₁ am₁ ≈ Wo g₁ um₁ tm₁ am₁
eWW g₁ um₁ tm₁ am₁ = ψQ {q = 1} O₀ O₀ g₀ g₀ _ g₁ um₁ tm₁ am₁ _ g₁ um₁ tm₁ am₁ z≈ tt

Ww : ∀ {m₁} (g₁ : Gw m₁) (um₁ : one ⊲ m₁) (tm₁ am₁ : azero ⊲ m₁) (r : VW (Wo g₁ um₁ tm₁ am₁)) → fr (vW r) ≅ BTBOᴵ
Ww g₁ um₁ tm₁ am₁ (vw {gw₁ = gq} {v₁′ = v′} {gv₁ = gv′} {uv₁ = uq} {av₁ = aq} c) =
  ≅-trans (fr≅ (val≅ᵉ (Wo g₁ um₁ tm₁ am₁) (Ω̇ 1 azero) {gq} {v′} {gv′} {uq} {aq} {g₀} {one} {g₀} {C.self} {z⊲ one} c GΩ (eW g₁ um₁ tm₁ am₁))) same-Ω

oW : ∀ {m₁} (g₁ : Gw m₁) (um₁ : one ⊲ m₁) (tm₁ am₁ : azero ⊲ m₁) → Ω̇ 0 azero ⊴ Wo g₁ um₁ tm₁ am₁
oW g₁ um₁ tm₁ am₁ with mx g₀ g₁ um₁ tm₁ am₁
... | mx′ m₂ g₂ um₂ tm₂ am₂ mv₂ = rw (rw Ω₀⊴Ω₁)

-- W ⊕ 0 的值就是 W 的值
peel : ∀ {p a u₀ u} {pp : u₀ ⊲ u} {g : Gw u₀} {x : 𝓞 p a u₀} (r : VW (ow pp g x)) → Σ (VW x) λ r′ → vW r′ FL.≅ vW r
peel {pp = pp} {g} (vw {gw₁ = gu} {v₁′ = v} {gv₁ = gv} {uv₁ = uv} {av₁ = av} d) =
  vw {gw₁ = g} {v₁′ = Mx.m (Mz gu gv uv av)} {gv₁ = Mx.gm (Mz gu gv uv av)} {uv₁ = ⊲-tr pp (Mx.um (Mz gu gv uv av))} {av₁ = Mx.am (Mz gu gv uv av)} d , ≅₀-refl _

Eadd0 : ∀ {u₀} (W : 𝓞 1 azero u₀) (gu : Gw u₀) v (gv : Gw v) (uv : u₀ ⊲ v) (xv : one ⊲ v) (bv : azero ⊲ v) gq v′ (gv′ : Gw v′) (uq : v ⊲ v′) (aq : azero ⊲ v′) →
        (d : Ev (add W gu (lw zᴺ) O₀ g₀ v gv uv xv bv) gq v′ gv′ uq aq) → Σ (VW W) λ r → vW r FL.≅ vᴱ (add W gu (lw zᴺ) O₀ g₀ v gv uv xv bv) gq v′ gv′ uq aq d
Eadd0 W gu v gv uv xv bv gq v′ gv′ uq aq d with mx gu gv uv xv bv
... | mx′ m gm um tm am mv =
  let r₁ = vw {gw₁ = gq} {v₁′ = v′} {gv₁ = gv′} {uv₁ = uq} {av₁ = aq} d
      P₁ = peel r₁
      P₂ = peel (proj₁ P₁)
  in proj₁ P₂ , ≅₀-trans (proj₂ P₂) (proj₂ P₁)

oneW : ∀ {p a u} {x : 𝓞 p a u} (r : VW x) → Fp one (vW r)
oneW {x = x} (vw {gw₁ = gw₁} {v₁′ = v₁′} {gv₁ = gv₁} {uv₁ = uv₁} {av₁ = av₁} c) = one-val x {gw₁} {Mx.m (Mz gw₁ gv₁ uv₁ av₁)} {Mx.gm (Mz gw₁ gv₁ uv₁ av₁)} {Mx.um (Mz gw₁ gv₁ uv₁ av₁)} {Mx.am (Mz gw₁ gv₁ uv₁ av₁)} c

oneᴱ : ∀ {p a u} (x : 𝓞 p a u) (gu : Gw u) v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v) (d : Ev x gu v gv uv av) → Fp one (vᴱ x gu v gv uv av d)
oneᴱ x gu v gv uv av d = one-val x {gu} {Mx.m (Mz gu gv uv av)} {Mx.gm (Mz gu gv uv av)} {Mx.um (Mz gu gv uv av)} {Mx.am (Mz gu gv uv av)} d

-- rep W 2 = W ⊕ W 压过 W ⊕ 1, 值压过 b + 1, b 是 W 的值
repStep : ∀ {m₁} (g₁ : Gw m₁) (W : 𝓞 1 azero m₁) → W ≈ W → Ω̇ 0 azero ⊴ W → ∀ v (gv : Gw v) (uv : m₁ ⊲ v) (av : azero ⊲ v) (d : Ev (rep W g₁ 2) g₁ v gv uv av) →
          Σ (VW W) λ r → FL.suc (vW r) ⊴₀ vᴱ (rep W g₁ 2) g₁ v gv uv av d
repStep {m₁} g₁ W E₁ o v gv uv av d = r , ⊴₀-tr (⊴₀-tr (r0 (FL.s≅ e)) (l0 2 (+₀⊴ʳ a (Fp→⊴₁ (oneᴱ (add W g₁ (lw zᴺ) O₀ g₀ m₁ g₁ C.self (pos g₁) (z⊲ m₁)) g₁ m₁ g₁ C.self (z⊲ m₁) cQ))))) (proj₂ D)
  where
  Q⁰ = add⁰ W g₁ (lw zᴺ) (Ω̇ 0 azero) g₀ m₁ g₁ C.self (pos g₁) (z⊲ m₁)
  mm : Q⁰ ⊴ rep W g₁ 2
  mm = AddM.mR W g₁ E₁ o (lw zᴺ) (sa C.self) g₀ g₁ m₁ g₁ C.self (pos g₁) (z⊲ m₁) (iu refl) m₁ g₁ C.self C.self (z⊲ m₁)
  D = E-dn Q⁰ {gy = g₁} {m′ = Mx.m (Mz g₁ gv uv av)} {gm′ = Mx.gm (Mz g₁ gv uv av)} {um′ = Mx.um (Mz g₁ gv uv av)} {am′ = Mx.am (Mz g₁ gv uv av)} mm g₁ m₁ g₁ C.self (z⊲ m₁) (iu refl) d (Mi g₁ gv uv av)
  cQ = proj₁ D
  a = vᴱ (add W g₁ (lw zᴺ) O₀ g₀ m₁ g₁ C.self (pos g₁) (z⊲ m₁)) g₁ m₁ g₁ C.self (z⊲ m₁) cQ
  R = Eadd0 W g₁ m₁ g₁ C.self (pos g₁) (z⊲ m₁) g₁ m₁ g₁ C.self (z⊲ m₁) cQ
  r = proj₁ R
  e = proj₂ R

record Up₀ (y : Ord₀) : Set where
  constructor up₀
  field
    b₀ : Ord₀
    ok₀ : fr b₀ ≅ BTBOᴵ
    st₀ : FL.suc b₀ ⊴₀ y


lemmaX : ∀ {v} (gv : Gw v) (uv : one ⊲ v) (tv av : azero ⊲ v) gq v′ (gv′ : Gw v′) (uq : v ⊲ v′) (aq : azero ⊲ v′)
         (c : Ev (ψ 1 azero (Ω̇ 0 azero) g₀ v gv uv tv av) gq v′ gv′ uq aq) → Up₀ (vᴱ (ψ 1 azero (Ω̇ 0 azero) g₀ v gv uv tv av) gq v′ gv′ uq aq c)
lemmaX gv uv tv av gq v′ gv′ uq aq c with mx g₀ gv uv tv av
lemmaX gv uv tv av gq v′ gv′ uq aq (Es , st) | mx′ m g um₁ tm₁ am₁ mv =
  up₀ (vW (proj₁ F)) (Ww g um₁ tm₁ am₁ (proj₁ F)) (l0 2 (proj₂ F))
  where
  M₁ = Mz gq gv′ uq aq
  M₂ = Mz g (Mx.gm M₁) (⊲-tr mv (Mx.um M₁)) (Mx.am M₁)
  F = repStep g (Wo g um₁ tm₁ am₁) (eWW g um₁ tm₁ am₁) (oW g um₁ tm₁ am₁) (Mx.m M₂) (Mx.gm M₂) (Mx.um M₂) (Mx.am M₂) (Es 2)

frm : ∀ {a b : Ord₀} → a ⊴₀ b → fr a ⊑⁰ fr b
frm (r0 e) = ≅→⊑ (fr≅ e)
frm (s0 p) c = ≺s (frm p c)
frm (l0 n p) c = ≺l n (frm p c)

-- 第 1 项压过 ψ₀(ψ_Ω(1))
term1 : ∀ {m} (gm : Gw m) (am : one ⊲ m) (B : Ev (ψ 1 azero (oe es (Ω̇at 1 azero gm)) gm m gm C.self (⊲-tr (C.suc C.self) am) am) gm m gm C.self (⊲-tr (C.suc C.self) am)) →
        Up₀ (vᴱ (ψ 1 azero (oe es (Ω̇at 1 azero gm)) gm m gm C.self (⊲-tr (C.suc C.self) am) am) gm m gm C.self (⊲-tr (C.suc C.self) am) B)
term1 {m} gm am B = up₀ (Up₀.b₀ U) (Up₀.ok₀ U) (⊴₀-tr (Up₀.st₀ U) (proj₂ D))
  where
  kM = ⊲-tr (C.suc C.self) am
  X₀ = ψ 1 azero (Ω̇ 0 azero) g₀ m gm (pos gm) (z⊲ m) (z⊲ m)
  Y₀ = ψ 1 azero (oe es (Ω̇at 1 azero gm)) gm m gm C.self kM am
  d₂ : X₀ ⊴ Y₀
  d₂ = ψL′ 1 azero (eR {stp = es} (rw Ω₀⊴Ω₁)) g₀ gm m gm (pos gm) (z⊲ m) (z⊲ m) m gm C.self kM am
  M₃ = Mz gm gm C.self kM
  M₅ = Mz gm gm C.self (z⊲ m)
  D = E-dn X₀ {gy = gm} {m′ = Mx.m M₃} {gm′ = Mx.gm M₃} {um′ = Mx.um M₃} {am′ = Mx.am M₃} d₂ gm (Mx.m M₅) (Mx.gm M₅) (Mx.um M₅) (Mx.am M₅) (Mi gm gm C.self (z⊲ m)) B (Mi gm gm C.self kM)
  U = lemmaX gm (pos gm) (z⊲ m) (z⊲ m) gm m gm C.self (z⊲ m) (proj₁ D)

strict : ∀ {m gm um am} (d : E (Ω̇ 1 one) g₀ m gm um am) → BTBOᴵ ≺ fr (val (Ω̇ 1 one) {g₀} {m} {gm} {um} {am} d)
strict (rv () vz Es tS st)
strict {m} {gm} {um} {am} (rg nz Es st) = frm (l0 1 (Up₀.st₀ U)) (≺z (≅-sym (Up₀.ok₀ U)))
  where
  U = term1 gm am (Es 1)

strictᵉ : (d : Ev (Ω̇ 1 one) g₀ one g₀ C.self C.self) → BTBOᴵ ≺ fr (vᴱ (Ω̇ 1 one) g₀ one g₀ C.self C.self d)
strictᵉ d = strict {Mx.m (Mz g₀ g₀ C.self C.self)} {Mx.gm (Mz g₀ g₀ C.self C.self)} {Mx.um (Mz g₀ g₀ C.self C.self)} {Mx.am (Mz g₀ g₀ C.self C.self)} d

BTBO≺T₁ : BTBOᴵ ≺ fr T₁
BTBO≺T₁ = strictᵉ G₁
```

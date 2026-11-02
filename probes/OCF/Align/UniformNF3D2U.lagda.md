# 抽象类族上的折叠定理 (七): 第 2 层、链点与帧的塔

> 接 [UniformNF3D2T](UniformNF3D2T.lagda.md). 结论先说:
>
> 1. **`Gᴺ₂`: $\psi_0(\psi_\Omega(\Omega_2))$ 的证书 (§1).** 最小的非平凡深度 1 点, 只用 `FF₁` 与 `Vis 2`.
> 2. **`Gᴺθ n`: $\psi_0(\psi_\Omega(\Omega_{\theta_n}))$, $\theta_n$ 是 `Ω̂A 1 (Ω̂A 0)` 的第 $n$ 个链点的层号 (§2).** 覆盖来自守卫 `Br₁`.
> 3. **`Frm`: 帧对闭包封闭 (§3).** `frmΩ̂ : Frm E → Frm (Ω̂A 1 E)`. `Gᴺfr n`: 塔 $E_0=\Omega_\Omega$, $E_{n+1}=$ `Ω̂A 1 E_n`, 对一切 $n$ 同一个定理.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D2U where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (⊑ᴵ-≅ˡ; _≅ˢ_; s≅; z≅; ŝ≅; kd-≅; Ωˢ-≅; Ωˢ-refl; _≈ᴿ_; _≈₁_; fold-≅1; cloR)
open import OCF.Align.Uniform3Base using (Flr; flo; cvFlo; toFlo; fz; fk; _⊔_; Ev; InF; inl; inr; ink; Run; A; Dem; fold; Ω̂A; ∅ᴿ; bound-≅; ⊔∼; fk∼; ∼ᶠ-refl; _∼ᶠ_; Top; Bd; bound; iF; evF; FM)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ-HS)
open import OCF.Align.UniformNF3D1O using (Obs; idO; fo1; run)
open import OCF.Align.UniformNF3D1G using (FFl; ffl; F≅; B1₁ᴱ; B1ᴱ; _⊑ᴱ_; Ctx; PFl; pfl; 𝟏; ⊑ᴱ-trans; ≅→⊑ᴱ; suc-rᴱ; ŝ-rᴱ; Ω1ᴱ)
open import OCF.Align.UniformNF3D1C
open import OCF.Align.UniformNF3D1CF using (NZ-of)
open import OCF.Align.UniformNF3D2F using (VF; Pd)
open import OCF.Align.UniformNF3D2C using (Stage; stage; pfS; vS; dmS; demUp)
open import OCF.Align.UniformNF3D2H using (PCg; module FF1; module Aux)
open import OCF.Align.UniformNF3D2S using (read1; vEΩ; dmEΩ)
open import OCF.Align.UniformNF3D1H using (ffl-Ω̂)
open import OCF.Align.UniformNF3D2T using (module Step1; 𝓟⊤; pCg⊤; stage∅; toT)
```

## §1 第 2 层

```agda
module SqS = Step1 ffl-Ω̂ dmEΩ vEΩ stage∅
open FF1 ffl-Ω̂ dmEΩ vEΩ using (FF₁; Fk₁)

Vis2 : ∀ {ℓ} {ev : Ev ℓ (fz ⊔ (fk zero ⊔ flo (suc (suc zero))))} {z : zero <ᴵ ℓ} → Vis (suc (suc zero)) (fo1 {k = suc (suc zero)} idO (Ω̂A 0) ∅ᴿ ev z)
Vis2 {ev = ev} {z = z} = vis (ffl-Ω̂ , pfS stage∅ , tt) (λ _ → SqS.tw₁ (refl , tt)) cp₂
  where
  cp₂ : ∀ {b} → b ≺ᴵ suc (suc zero) → CvP (fo1 {k = suc (suc zero)} idO (Ω̂A 0) ∅ᴿ ev z) b
  cp₂ (via e zero) t et fl′ G = ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (s⊑′ (toLevel-≺ (hs hz) (forceᴺ-HS _ G) (SqS.tw₁ {ev′ = ev} {p′ = z} (refl , tt) t et (fl′ (s≅ z≅ z≅) (Ω1ᴱ _)) G)))
  cp₂ (via e (suc zero)) t et fl′ G = ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (read1 idO tt _ (SqS.self₁ {ev = ev} {p = z} et) (Aux.one1 ffl-Ω̂ stage∅ {ev = ev} {p = z} t et) G)
  cp₂ (via e (suc (suc ()))) t et fl′ G

T₂ : ∀ {ℓ} → Ev ℓ (fz ⊔ (fk zero ⊔ flo (suc (suc zero)))) → zero <ᴵ ℓ → Ordˢ zero
T₂ ev z = fold 1 (flo (suc (suc zero))) (cvFlo (suc (suc zero))) (Ω̂A 0) (Ωˢ (suc (suc zero))) ∅ᴿ ev z

Gᴺ₂ : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ flo (suc (suc zero))))) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (T₂ ev z))
Gᴺ₂ ev z = Good→N (refl , tt) (Fk₁ stage∅ {ev = ev} {p = z} tt {𝓖₁ = Vis (suc (suc zero))} {𝓖₂ = VF 𝓟⊤ zero} (λ { (refl , _) → Vis2 }) (λ v → v) (refl , tt) (Ωg (suc (suc zero))) (Ωˢ-refl (suc (suc zero))))
```

## §2 链点

```agda
module Chain {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ fk zero))) (z : zero <ᴵ ℓ) where
  open SqS.V ev z

  record CP : Set where
    constructor cp-mk
    field
      lvη : Ordᴵ
      leη : Bd B ⊑ᴵ lvη
      brη : SqS.Br₁ lvη idO
  open CP public

  G₀ : Goodᴺ (toZ t₀)
  G₀ = Good→N (refl , tt) (Fk₁ stage∅ {ev = ev} {p = z} tt {𝓖₁ = Vis (suc zero)} {𝓖₂ = VF 𝓟⊤ zero} (λ v → SqS.c1 v) (λ v → v) (refl , tt) (Ωg (suc zero)) (Ωˢ-refl (suc zero)))

  cp0 : CP
  cp0 = cp-mk (lvG G₀) (bd⊑ (refl , tt) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G₀ (rdT {ev′ = ev} {p′ = z} (refl , tt) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G₀)) (ch₀ (refl , tt) G₀)

  Gnext : (c : CP) → Goodᴺ (toZ (gT (lvη c) (leη c)))
  Gnext (cp-mk η e b) = Good→N ((refl , tt) , b) (Fk₁ stage∅ {ev = evT η e} {p = tg η e} (nzη e) {𝓖₁ = Vis η} {𝓖₂ = VF 𝓟⊤ zero ∧ (λ O → SqS.Br₁ η O)} (λ (v , b′) → SqS.cT v b′) proj₁ ((refl , tt) , b) (Ωg η) (Ωˢ-refl η))

  cpS : CP → CP
  cpS c@(cp-mk η e b) = cp-mk (lvG (Gnext c)) (bd⊑ (refl , tt) (Ωˢ η) (Ωˢ-refl η) (Gnext c) (rdT {ev′ = evT η e} {p′ = tg η e} (refl , tt) (Ωˢ η) (Ωˢ-refl η) (Gnext c))) (chS η e (refl , tt) b (Gnext c))

  cpn : ℕ → CP
  cpn zero    = cp0
  cpn (suc n) = cpS (cpn n)

  θn : ℕ → Ordᴵ
  θn n = lvη (cpn n)

  Gᴺθ : ∀ n → Goodᴺ (toZ (gT (θn n) (leη (cpn n))))
  Gᴺθ n = Gnext (cpn n)
```

## §3 帧的塔

```agda
record Frm {flE} (E : A 1 flE) : Set₂ where
  constructor frm
  field
    fE  : FFl E
    dmE : ∀ {X K} (q : InF K flE) → Dem X q
    vE  : ∀ {𝓟 : Pd} {pCg : PCg 𝓟} {fl} {Q : Run fl} → Stage 𝓟 pCg Q → ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ flE)) (p : i <ᴵ ℓ) → Wit i (VF 𝓟 i) → Good true (VF 𝓟 i) (E Q ev p)
open Frm public

nzB : ∀ {φ i ℓ η} (B : Top i ℓ (φ ⊔ fk zero)) → Bd B ⊑ᴵ η → NZ η
nzB {η = η} B e with ⊑ᴵ-trans (s⊑ z≅ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)
... | s⊑ _ q = NZ-of q

module Close {flE} {E : A 1 flE} (F : Frm E) where
  fEE = fE F
  rEE = FFl.rE fEE

  rE₂ : Ω̂A 1 E ≈₁ Ω̂A 1 E
  rE₂ {fl} {fl′} {P} {P′} s H ev p ev′ p′ ei =
    ŝ≅ (kd-≅ ei) (bound-≅ (⊔∼ (⊔∼ s (∼ᶠ-refl flE)) (fk∼ z≅)) ((proj₁ ev , proj₁ (proj₂ ev)) , proj₂ (proj₂ ev)) p ((proj₁ ev′ , proj₁ (proj₂ ev′)) , proj₂ (proj₂ ev′)) p′ ei)
       (fold-≅1 {cv = cvFlo (suc zero)} {cv′ = cvFlo (suc zero)} (∼ᶠ-refl flE) rEE (Ωˢ-refl (suc zero)) s H ev p ev′ p′ ei)
       (λ η e η′ e′ eη → toT η (nzB (bound ((fl ⊔ flE) ⊔ fk zero) ((proj₁ ev , proj₁ (proj₂ ev)) , proj₂ (proj₂ ev)) p) e) (λ x → x ≅ˢ _) (toT η′ (nzB (bound ((fl′ ⊔ flE) ⊔ fk zero) ((proj₁ ev′ , proj₁ (proj₂ ev′)) , proj₂ (proj₂ ev′)) p′) e′) (λ x → _ ≅ˢ x)
          (fold-≅1 {cv = cvFlo η} {cv′ = cvFlo η′} (∼ᶠ-refl flE) rEE (Ωˢ-≅ eη) s H _ _ _ _ ei)))

  s1₂ : ∀ {fl} {Q : Run fl} → PFl Q → ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ (flE ⊔ fk zero))) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ Ω̂A 1 E Q ev p
  s1₂ {Q = Q} pf ev p = ŝ-rᴱ (B1₁ᴱ {φ = fk zero} {E = E} {Q = Q} {cv = λ e → e} {ev = ev} {p = p} (FFl.s1E fEE pf (proj₁ ev , proj₁ (proj₂ ev)) p) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

  st₂ : ∀ {fl} {Q : Run fl} → PFl Q → ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ (flE ⊔ fk zero))) (p : i <ᴵ ℓ) → Ord₊ˢ.suc (Q (proj₁ ev) p) ⊑ᴱ Ω̂A 1 E Q ev p
  st₂ {Q = Q} pf ev p = ŝ-rᴱ (B1₁ᴱ {φ = fk zero} {E = E} {Q = Q} {cv = λ e → e} {ev = ev} {p = p} (FFl.stE fEE pf (proj₁ ev , proj₁ (proj₂ ev)) p) (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)))

  pE₂ : ∀ {fl} {Q : Run fl} → PFl Q → PFl (Ω̂A 1 E Q)
  pE₂ {fl} {Q} pf = pfl rr
    (λ {i} ev p → ⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (Ωˢ-refl i))) (s1₂ pf ev p))
    (λ {φ} {k} {i} {ℓ} {cv} ev p y ey oy → B1ᴱ {φ = φ} {P = Ω̂A 1 E Q} {cv = cv} {ev = ev} {p = p} rr (s1₂ pf (proj₁ ev) p) y ey)
    where
    rr : Ω̂A 1 E Q ≈ᴿ Ω̂A 1 E Q
    rr = rE₂ (∼ᶠ-refl fl) (PFl.rP pf)

  frmΩ̂ : Frm (Ω̂A 1 E)
  frmΩ̂ = frm (ffl rE₂ pE₂ s1₂ st₂)
    (λ { (inl q) → dmE F q ; (inr ink) → inj₂ z≅ })
    (λ S ev p w → Step1.V.val fEE (dmE F) (vE F) S ev p w)

frm₀ : Frm (Ω̂A 0)
frm₀ = frm ffl-Ω̂ dmEΩ vEΩ

FlE : ℕ → Flr
FlE zero    = fk zero
FlE (suc n) = FlE n ⊔ fk zero

En : ∀ n → A 1 (FlE n)
En zero    = Ω̂A 0
En (suc n) = Ω̂A 1 (En n)

frmn : ∀ n → Frm (En n)
frmn zero    = frm₀
frmn (suc n) = Close.frmΩ̂ (frmn n)

Gᴺfr : ∀ n {ℓ} (ev : Ev ℓ (fz ⊔ FlE n)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (En n ∅ᴿ ev z))
Gᴺfr n ev z = Good→N (refl , tt) (vE (frmn n) stage∅ ev z (refl , tt))
```

## §4 下一步卡在哪里 (纸面, 没有编译)

深度 2 的后继行是 `repA 1 P F₂ m`: 换的是**帧**, 不是底. 帧副本 `F₂ P` 不是 `Frm`: `vE` 对一切好底与一切类族量化, 而 `F₂ P` 只在 `fo2 O X P B ∈ 𝓚` 的上下文里好. 所以 `Frm` 要相对化为 "对类族 $\le\mathcal R(B)$". 帧内部的折叠又把底从 $Q$ 换到 $B\sqsupseteq Q$, 于是要 `fo2 O X P Q ∈ 𝓚` 推出 `fo2 O X P B ∈ 𝓚`. 这不是 `FlOver`: 小尾巴 $t$ 处 $F_t\,P\,B$ 不高于 $F_a\,P\,Q$. 它是逐点的 "底抬高" 封闭性, 要 $F_t\,P\,Q\sqsubseteq^\mathsf E F_t\,P\,B$, 其中的存在性部分 (由高底的证书得低底的证书) 我没有证明路径.

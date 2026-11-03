# 一切深度 (七): 闭包, 塔

> 接 [UniformNF3D3H](UniformNF3D3H.lagda.md). 由 [UniformNF3D2T](UniformNF3D2T.lagda.md) 经脚本克隆. 结论先说:
>
> 1. **`Step1.V.val`: 对任意深度的好帧 $E$, 闭包 `Ω̂U E` 在 $E$ 的好点上好.** 与 D2T 同一个证明.
> 2. **`RFΘf`: 闭包算子 $\Theta$ 在世界 `wᶿ` ("脊头的值在点的地板集里") 上好, 对一切深度, 没有对 $d$ 的归纳.** 算子吃任意世界上的任意好帧.
> 3. **`GΘ n`: 塔的第 $n$ 层有记号无关的证书, 对一切 $n$.** `T n`: `T 0` 是 $\psi_0(\Omega_\Omega)$, `T 1` 是 $\psi_0(\Omega_\Omega^2)$, `T 2` 是 $\psi_0(\psi_\Omega(\psi_\Omega(\Omega_\Omega)))$. 与带标签树的互模拟与验收在 [UniformNF3D3Accept](UniformNF3D3Accept.lagda.md).
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D3T where

open import Agda.Primitive using (Level)
open import Level using (Lift; lower) renaming (lift to ↑)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.Prefix using (Z; Ord₊ˢ; Ordˢ; toZ; Ωˢ)
open import OCF.Align.UniformNF3Eq using (kd-≅; z≅; selfΩ̂0; _≅ᶻ_; ŝ≅; ⊑ᴵ-≅ʳ; ⊑ᴵ-≅ˡ; ≅ᴵ→⊑ᴵ; ≅ᶻ-sym; _≅ˢ_; toZ-≅; Ωˢ-≅; Ωˢ-refl; _≈ᴿ_)
open import OCF.Align.Uniform3Base using (bound-≅; ⊔∼; fk∼; fz∼; _∼ᶠ_; ∼ᶠ-refl; Flr; cloA; flo; cvFlo; toFlo; fz; fk; _⊔_; Ev; InF; inl; inr; ink; liftEv; Run; A; Top; bound; Bd; ubd; Fc; evF; iF; FM; FB; Dem; fold; Ω̂A; ∅ᴿ)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D3O using (fold-≅U; Fr; Sp; sf; fold1; _≈S_; _≈U_; Obs; idO; fo1; run; _≈ᵒ_; run-≅)
open import OCF.Align.UniformNF3D3N using (_⊑ᵒ_; Ω-monoᵒ; fold1-cong)
open import OCF.Align.UniformNF3D3G using (fold-congᴱ; suc-fold₁; suc-fold; σ₀; pfl-Ω̂; pfl; pfl-of; leHd; ŝ-rᴱ; FlU; SF; SF≈; FFl; ffl; F≅; B1₁ᴱ; fold1-congᴱ; _⊑ᴱ_; Ctx; ctx-refl; PFl; pfl∅; 𝟏; ⊑ᴱ-trans; ≅→⊑ᴱ; Ω1ᴱ; Ω<ᴱ; Ω-strict)
open import OCF.Align.UniformNF3D3C
open import OCF.Align.UniformNF3D3CF using (NZ-of)
open import OCF.Align.UniformNF3D3F using (VF; Pd)
open import OCF.Align.UniformNF3D3H using (module Aux; module FF1)
open import OCF.Align.UniformNF3D3W
open import OCF.Align.UniformNF3D3S using (mapV; read1; zlt; ≺ᴵ-up; Ωvia; τ; h2N; demUp; PCg; one⊑; NZ-≅₁; module Step; Stage; stage)
open import OCF.Align.Stage2Label using (one⁰)
```

## §1 `toT`

```agda
trans<′ : ∀ {x a b} → x <ᴵ a → a <ᴵ b → x <ᴵ b
trans<′ x zero      = suc x
trans<′ x (suc q)   = suc (trans<′ x q)
trans<′ x (lim n q) = lim n (trans<′ x q)

toT : ∀ {d flE} {E : Fr (suc d) flE} {Q : Sp (suc d)} (η : Ordᴵ) → NZ η → ∀ {ℓ i} {u : Ev ℓ (sf Q)} {v : Ev ℓ flE} {w : Ev ℓ (fk η)} {p : i <ᴵ ℓ} {a : Level} (𝓧 : Ordˢ i → Set a) →
      𝓧 (fold1 (flo η) (cvFlo η) E (Ωˢ η) Q (u , (v , toFlo η (λ q → w (suc q)))) p) → 𝓧 (fold1 (fk η) (λ e q → e (suc q)) E (Ωˢ η) Q (u , (v , w)) p)
toT (suc j)   nz {w = w} {p = p} 𝓧 x with <ᴵ-dec (w (suc zero)) p
... | injᵃ (via e r) = x
... | injᵇ _ = x
... | injᶜ _ = x
toT (lim f s) nz 𝓧 x = x
```

## §2 帧上的闭包

```agda
Ω̂U : ∀ {d flE} → Fr (suc d) flE → Fr (suc d) (flE ⊔ fk zero)
Ω̂U {flE = flE} E s ev p =
  cloA 0 {sf s ⊔ flE}
    (λ e q → fold1 (fk zero) (λ e′ → e′) E (Ωˢ (suc zero)) s (proj₁ (proj₁ e) , (proj₂ (proj₁ e) , proj₂ e)) q)
    (λ η e q → fold1 (fk η) (λ e′ q′ → e′ (suc q′)) E (Ωˢ η) s (proj₁ (proj₁ e) , (proj₂ (proj₁ e) , proj₂ e)) q)
    ((proj₁ ev , proj₁ (proj₂ ev)) , proj₂ (proj₂ ev)) p

ω1b : ∀ {b x L} → b ≅ᴵ x → x <ᴵ L → zero <ᴵ L → NZ b → Ωˢ (suc zero) ⊑ᴱ Ωˢ b
ω1b {b} e q z nb = ω1′ (⊑ᴵ-≅ʳ (one⊑ z q (NZ-≅₁ nb e)) (≅ᴵ-sym e))
  where
  ω1′ : suc zero ⊑ᴵ b → Ωˢ (suc zero) ⊑ᴱ Ωˢ b
  ω1′ (s⊑ z≅ r) = Ω<ᴱ z≅ r

readT : ∀ {𝓟 : Pd} {i} {O : Obs i} (t : Ordˢ i) → VF 𝓟 i O → t ≅ˢ t → Ωˢ i ⊑ᴱ t → (𝟏 ⊑ᴱ t) → (G : Goodᴺ (toZ (run O t))) → suc i ⊑ᴵ lvG G
readT {i = zero} t (refl , _) et fi one G = read1 idO tt t et one G
readT {i = suc j} t v et fi one G = cp (proj₁ v) (via (≅ᴵ-refl (suc j)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G
readT {i = lim f s} t v et fi one G = cp (proj₁ v) (via (≅ᴵ-refl (lim f s)) zero) t et (λ ex₀ h₀ → ⊑ᴱ-trans (Ωup ex₀ h₀ (via (≅ᴵ-refl _) zero)) fi) G

module Step1 {n flE} {E : Fr (suc n) flE} {wE : Wld (suc n)} (rX : RF (suc n) wE E) (S : FF1.Pack rX) where
  open FF1 rX using (Fk₁; module A′; QS; 𝓟S; pfS; bS; wS; sgS; weS)
  Q : Sp (suc n)
  Q = QS S
  𝓟 : Pd
  𝓟 = 𝓟S S
  fl : Flr
  fl = sf Q
  fE : FFl E
  fE = fX rX
  pf : SF Q
  pf = pfS S
  open A′ S hiding (𝓟)

  Fo : ∀ k {i ℓ} → Ordˢ k → Ev ℓ (fl ⊔ (flE ⊔ flo k)) → i <ᴵ ℓ → Ordˢ i
  Fo k t ev p = fold1 (flo k) (cvFlo k) E t Q ev p

  CQ₁ : ∀ {i} → Obs i → Ordᴵ → Set
  CQ₁ {i} O b = ∀ {k′ ℓ′} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t → FlΩ b t →
                (G : Goodᴺ (toZ (run O (Fo k′ t ev′ p′)))) → suc b ⊑ᴵ lvG G

  record Br₁ {i} (η : Ordᴵ) (O : Obs i) : Set where
    constructor br-mk
    field
      br  : ∀ {b} → b ≺ᴵ η → CQ₁ O b
      η₋  : Ordᴵ
      ℓ₋  : Ordᴵ
      ev₋ : Ev ℓ₋ (fl ⊔ (flE ⊔ flo η₋))
      p₋  : i <ᴵ ℓ₋
      G₋  : Goodᴺ (toZ (run O (Fo η₋ (Ωˢ η₋) ev₋ p₋)))
      eη  : η ≅ᴵ lvG G₋
      h₋  : η₋ ≺ᴵ η
  open Br₁

  head≈ : ∀ {i} {O : Obs i} {k₁ k₂ ℓ₁ ℓ₂} {ev₁ : Ev ℓ₁ (fl ⊔ (flE ⊔ flo k₁))} {ev₂ : Ev ℓ₂ (fl ⊔ (flE ⊔ flo k₂))} {p₁ : i <ᴵ ℓ₁} {p₂ : i <ᴵ ℓ₂} →
          Ctx O → fo1 {k = k₁} O E Q ev₁ p₁ ≈ᵒ fo1 {k = k₂} O E Q ev₂ p₂
  head≈ {O = O} c = fo1 (ctx-refl O c) rE rQ

  self₁ : ∀ {i k ℓ} {ev : Ev ℓ (fl ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {t : Ordˢ k} → t ≅ˢ t → Fo k t ev p ≅ˢ Fo k t ev p
  self₁ {ev = ev} {p = p} et = F≅ {ev = ev} {ev′ = ev} rE rQ et p p (≅ᴵ-refl _)

  CQ₁′ : ∀ {i} → Ordᴵ → Obs i → Ordᴵ → Set
  CQ₁′ {i} η₀ O b = ∀ {k′ ℓ′} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t → Ωˢ η₀ ⊑ᴱ t →
                    (G : Goodᴺ (toZ (run O (Fo k′ t ev′ p′)))) → suc b ⊑ᴵ lvG G

  rd : ∀ {i η₀ ℓ₀ b} {O : Obs i} {ev₀ : Ev ℓ₀ (fl ⊔ (flE ⊔ flo η₀))} {p₀ : i <ᴵ ℓ₀} → Ctx O →
       (G₀ : Goodᴺ (toZ (run O (Fo η₀ (Ωˢ η₀) ev₀ p₀)))) → b ≺ᴵ lvG G₀ → CQ₁′ η₀ O b
  rd {i} {η₀} {O = O} {ev₀ = ev₀} {p₀ = p₀} cO G₀ h {ev′ = ev′} {p′ = p′} t et fl′ G =
    s⊑′ (≺ᴵ-up h (⊑ᴵ-trans (≅ᴵ→⊑ᴵ (toLevel-≅ (forceᴺ-HS _ G₀) (forceᴺ-HS _ (proj₁ L)) (forceᴺ-≅ d G₀ (proj₁ L))))
                             (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L))))
    where
    d = toZ-≅ (run-≅ {O = O} {O′ = O} (ctx-refl O cO) (self₁ {ev = ev₀} {p = p₀} (Ωˢ-refl η₀)))
    L = fold1-congᴱ {E = E} {P = Q} {ev = ev₀} {ev′ = ev′} {p = p₀} {p′ = p′} {x = Ωˢ η₀} {y = t} rE rQ fl′ (ctx-refl O cO) G

  tw₁ : ∀ {i k′ ℓ′} {O : Obs i} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p′ : i <ᴵ ℓ′} → VF 𝓟 i O → Tw (fo1 {k = k′} O E Q ev′ p′)
  tw₁ {i = zero} {k′ = k′} {ev′ = ev′} {p′ = p′} (refl , _) s es os G = proj₂ L (h2N (proj₁ L))
    where
    L = B1₁ᴱ {φ = flo k′} {E = E} {Q = Q} {cv = cvFlo k′} {ev = ev′} {p = p′} (FFl.s1E fE pf (proj₁ ev′ , proj₁ (proj₂ ev′)) p′) s es idO G
  tw₁ {i = suc _} {ev′ = ev′} {p′ = p′} v s es os G = tw (proj₁ v) tt _ (self₁ {ev = ev′} {p = p′} es) (one1 {ev = ev′} {p = p′} s es) G
  tw₁ {i = lim _ _} {ev′ = ev′} {p′ = p′} v s es os G = tw (proj₁ v) tt _ (self₁ {ev = ev′} {p = p′} es) (one1 {ev = ev′} {p = p′} s es) G

  growQ : ∀ {i a η₋ η′ ℓ₋ ℓ′} {O : Obs i} {ev₋ : Ev ℓ₋ (fl ⊔ (flE ⊔ flo η₋))} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo η′))} {p₋ : i <ᴵ ℓ₋} {p′ : i <ᴵ ℓ′} →
          Ctx O → η₋ ≅ᴵ a → a <ᴵ η′ →
          (G₋ : Goodᴺ (toZ (run O (Fo η₋ (Ωˢ η₋) ev₋ p₋)))) (G′ : Goodᴺ (toZ (run O (Fo η′ (Ωˢ η′) ev′ p′)))) → lvG G₋ ≺ᴵ lvG G′
  growQ {a = a} {η₋} {η′} {O = O} {ev₋ = ev₋} {ev′ = ev′} {p₋ = p₋} {p′ = p′} cO e q G₋ G′ =
    ≺ᴵ-respˡ (toLevel-≅ (forceᴺ-HS _ G₋) (forceᴺ-HS _ (proj₁ Sx)) e₃) (toLevel-≺ (forceᴺ-HS _ (proj₁ Sx)) (forceᴺ-HS _ G′) (proj₂ L (proj₂ Sx)))
    where
    ev₂ : ∀ {b} → b <ᴵ η′ → Ev _ (fl ⊔ (flE ⊔ flo b))
    ev₂ {b} r = proj₁ ev′ , (proj₁ (proj₂ ev′) , toFlo b (λ x → cvFlo η′ (proj₂ (proj₂ ev′)) (trans<′ x r)))
    evs : Ev _ (fl ⊔ (flE ⊔ flo (suc a)))
    evs = proj₁ ev′ , (proj₁ (proj₂ ev′) , toFlo (suc a) (λ x → cvFlo η′ (proj₂ (proj₂ ev′)) (τ q x)))
    Os = fo1 {k = suc a} O E Q evs p′
    Oa = fo1 {k = a} O E Q (ev₂ q) p′
    L = Ω<ᴱ (≅ᴵ-refl a) q {O = Os} {O′ = fo1 O E Q ev′ p′} (head≈ cO) G′
    Sx = Ω-strict a {O = Oa} {O′ = Os} (head≈ cO) (fE , pf , cO) (proj₁ L)
    e₃ = forceᴺ-≅ (toZ-≅ (run-≅ {O = fo1 O E Q ev₋ p₋} {O′ = Oa} (head≈ cO) (Ωˢ-≅ e))) G₋ (proj₁ Sx)

  pickB : ∀ {i η b x y k′ ℓ′ ℓ₀} {O : Obs i} {ev₀ : Ev ℓ₀ (fl ⊔ (flE ⊔ flo η))} {p₀ : i <ᴵ ℓ₀} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p′ : i <ᴵ ℓ′} →
          Ctx O → Br₁ η O → η ≅ᴵ x → b ≅ᴵ y → (G₀ : Goodᴺ (toZ (run O (Fo η (Ωˢ η) ev₀ p₀)))) → b ≺ᴵ lvG G₀ →
          (y ≺ᴵ x ⊎ x ≺ᴵ y ⊎ y ≅ᴵ x) → (t : Ordˢ k′) → t ≅ˢ t → FlΩ b t → (G : Goodᴺ (toZ (run O (Fo k′ t ev′ p′)))) → suc b ⊑ᴵ lvG G
  pickB cO B ex eb G₀ h (injᵃ s) t et fl′ G = br B (≺ᴵ-respˡ eb (≺ᴵ-respʳ s (≅ᴵ-sym ex))) t et fl′ G
  pickB cO B ex eb G₀ h (injᵇ s) t et fl′ G =
    rd cO G₀ h t et (fl′ (Ωˢ-refl _) (Ωvia (≺ᴵ-respˡ ex (≺ᴵ-respʳ s (≅ᴵ-sym eb))))) G
  pickB cO B ex eb G₀ h (injᶜ c) t et fl′ G =
    rd cO G₀ h t et (fl′ (Ωˢ-refl _) (≅→⊑ᴱ (Ωˢ-≅ (≅ᴵ-trans ex (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym eb)))))) G

  cT : ∀ {i η ℓ′} {O : Obs i} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo η))} {p′ : i <ᴵ ℓ′} → VF 𝓟 i O → Br₁ η O → Vis η (fo1 {k = η} O E Q ev′ p′)
  cT {i} v b = vis (fE , pf , cxT i v) (λ _ → tw₁ v) (λ h t et fl′ G → br b h t et fl′ G)

  c1 : ∀ {i ℓ′} {O : Obs i} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo (suc zero)))} {p′ : i <ᴵ ℓ′} → VF 𝓟 i O → Vis (suc zero) (fo1 {k = suc zero} O E Q ev′ p′)
  c1 {i} {O = O} {ev′ = ev′} {p′ = p′} v = vis (fE , pf , cxT i v) (λ _ → tw₁ v) cp₁
    where
    cp₁ : ∀ {b} → b ≺ᴵ suc zero → CvP (fo1 {k = suc zero} O E Q ev′ p′) b
    cp₁ (via e zero) t et fl′ G = ⊑ᴵ-≅ˡ (s≅ (≅ᴵ-sym e)) (read1 O (cxT i v) _ (self₁ {ev = ev′} {p = p′} et) (one1 {ev = ev′} {p = p′} t et) G)
    cp₁ (via e (suc ())) t et fl′ G
```

## §2 闭包的值

```agda
  module V {i ℓ} (ev : Ev ℓ (fl ⊔ (flE ⊔ fk zero))) (p : i <ᴵ ℓ) where
    evl : Ev ℓ ((fl ⊔ flE) ⊔ fk zero)
    evl = (proj₁ ev , proj₁ (proj₂ ev)) , proj₂ (proj₂ ev)

    B : Top i ℓ ((fl ⊔ flE) ⊔ fk zero)
    B = bound ((fl ⊔ flE) ⊔ fk zero) evl p

    Lη : ∀ η → Bd B ⊑ᴵ η → Ordᴵ
    Lη η e = Mlev (Fc B) (suc η) (FB B e)

    lf : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) (fl ⊔ flE)
    lf η e = liftEv (fl ⊔ flE) (λ q → lim 0 q) (proj₁ (evF B))

    w′ : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) (fk η)
    w′ η e q = lim 1 q

    evη : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) (fl ⊔ (flE ⊔ fk η))
    evη η e = proj₁ (lf η e) , (proj₂ (lf η e) , w′ η e)

    evT : ∀ η (e : Bd B ⊑ᴵ η) → Ev (Lη η e) (fl ⊔ (flE ⊔ flo η))
    evT η e = proj₁ (lf η e) , (proj₂ (lf η e) , toFlo η (λ q → w′ η e (suc q)))

    tg : ∀ η (e : Bd B ⊑ᴵ η) → i <ᴵ Lη η e
    tg η e = lim 0 (iF B)

    t₀ : Ordˢ i
    t₀ = Fo (suc zero) (Ωˢ (suc zero)) ev p

    gT : ∀ η → Bd B ⊑ᴵ η → Ordˢ i
    gT η e = Fo η (Ωˢ η) (evT η e) (tg η e)

    gη : ∀ η → Bd B ⊑ᴵ η → Ordˢ i
    gη η e = fold1 (fk η) (λ e′ q → e′ (suc q)) E (Ωˢ η) Q (evη η e) (tg η e)

    one⊑η : ∀ η → Bd B ⊑ᴵ η → suc zero ⊑ᴵ η
    one⊑η η e = ⊑ᴵ-trans (s⊑ z≅ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)

    nzη : ∀ {η} → Bd B ⊑ᴵ η → NZ η
    nzη e with one⊑η _ e
    ... | s⊑ _ q = NZ-of q

    TT : ∀ η (e : Bd B ⊑ᴵ η) {a : Level} (𝓧 : Ordˢ i → Set a) → 𝓧 (gT η e) → 𝓧 (gη η e)
    TT η e 𝓧 x = toT {E = E} {Q = Q} η (nzη e) {u = proj₁ (lf η e)} {v = proj₂ (lf η e)} {w = w′ η e} {p = tg η e} 𝓧 x

    bd⊑ : ∀ {O : Obs i} → VF 𝓟 i O → ∀ {k′ ℓ′} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p′ : i <ᴵ ℓ′} (t : Ordˢ k′) → t ≅ˢ t →
          (G : Goodᴺ (toZ (run O (Fo k′ t ev′ p′)))) → suc i ⊑ᴵ lvG G → Bd B ⊑ᴵ lvG G
    bd⊑ {O} v {ev′ = ev′} {p′ = p′} t et G (s⊑ e q) =
      ubd B (via e q) (λ { (inl k) → demUp k (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)) (dT rX (bS S) (wS S) (sgS S) (weS S) (cxT i v) (pT i v) (proj₁ ev′ , proj₁ (proj₂ ev′)) p′ (proj₁ L) k)
                         ; (inr ink) → inj₂ z≅ })
      where L = leF ev′ p′ t et (ctx-refl O (cxT i v)) G

    rdT : ∀ {O : Obs i} {k′ ℓ′} {ev′ : Ev ℓ′ (fl ⊔ (flE ⊔ flo k′))} {p′ : i <ᴵ ℓ′} → VF 𝓟 i O → (t : Ordˢ k′) → (et : t ≅ˢ t) → (G : Goodᴺ (toZ (run O (Fo k′ t ev′ p′)))) → suc i ⊑ᴵ lvG G
    rdT {ev′ = ev′} {p′ = p′} v t et G = readT _ v (self₁ {ev = ev′} {p = p′} et) (flw1 {ev = ev′} {p = p′} t et) (one1 {ev = ev′} {p = p′} t et) G

    ch₀ : ∀ {O} → VF 𝓟 i O → (G : Goodᴺ (toZ (run O t₀))) → Br₁ (lvG G) O
    ch₀ {O} v G = br-mk brB (suc zero) ℓ ev p G (≅ᴵ-refl _) two
      where
      cO = cxT i v
      z₁ : zero <ᴵ lvG G
      z₁ = zlt (read1 O cO t₀ (self₁ {ev = ev} {p = p} (Ωˢ-refl (suc zero))) (one1 {ev = ev} {p = p} (Ωˢ (suc zero)) (Ωˢ-refl (suc zero))) G)
      two : suc zero ≺ᴵ lvG G
      two = toLevel-≺ (hs hz) (forceᴺ-HS _ G) (tw₁ {ev′ = ev} {p′ = p} v (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) (Ω1ᴱ (suc zero)) G)
      brB : ∀ {b} → b ≺ᴵ lvG G → CQ₁ O b
      brB {b = zero} h {ev′ = ev′} {p′ = p′} t et fl′ G′ = read1 O cO _ (self₁ {ev = ev′} {p = p′} et) (one1 {ev = ev′} {p = p′} t et) G′
      brB {b = suc b} h@(via e q) t et fl′ G′ = rd {ev₀ = ev} {p₀ = p} cO G h t et (fl′ (Ωˢ-refl _) (ω1b e q z₁ tt)) G′
      brB {b = lim f s} h@(via e q) t et fl′ G′ = rd {ev₀ = ev} {p₀ = p} cO G h t et (fl′ (Ωˢ-refl _) (ω1b e q z₁ tt)) G′

    chS : ∀ {O} η e → VF 𝓟 i O → Br₁ η O → (G : Goodᴺ (toZ (run O (gT η e)))) → Br₁ (lvG G) O
    chS {O} η e v b G = br-mk brN η (Lη η e) (evT η e) (tg η e) G (≅ᴵ-refl _) gr
      where
      cO = cxT i v
      gr : η ≺ᴵ lvG G
      gr = ≺ᴵ-respˡ (eη b) (grr (h₋ b))
        where
        grr : η₋ b ≺ᴵ η → lvG (G₋ b) ≺ᴵ lvG G
        grr (via e′ q) = growQ cO e′ q (G₋ b) G
      brN : ∀ {b′} → b′ ≺ᴵ lvG G → CQ₁ O b′
      brN {b′} h t et fl′ G′ = go gr h
        where
        go : η ≺ᴵ lvG G → b′ ≺ᴵ lvG G → suc b′ ⊑ᴵ lvG G′
        go (via ex qx) h′@(via eb qb) = pickB {ev₀ = evT η e} {p₀ = tg η e} cO b ex eb G h′ (<ᴵ-dec qb qx) t et fl′ G′

    selfV : Ω̂U E Q ev p ≅ˢ Ω̂U E Q ev p
    selfV = ŝ≅ refl (≅ᴵ-refl _) (self₁ {ev = ev} {p = p} (Ωˢ-refl (suc zero)))
       (λ η e η′ e′ eq → TT η e (λ x → x ≅ˢ gη η′ e′) (TT η′ e′ (λ x → gT η e ≅ˢ x) (F≅ {ev = evT η e} {ev′ = evT η′ e′} rE rQ (Ωˢ-≅ eq) (tg η e) (tg η′ e′) (≅ᴵ-refl i))))

    val : Wit i (VF 𝓟 i) → Good true (VF 𝓟 i) (Ω̂U E Q ev p)
    val wT = bŝ (λ η O → Br₁ η O)
       (λ {η} {η′} eq b → br-mk (λ h → br b (≺ᴵ-respʳ h (≅ᴵ-sym eq))) (η₋ b) (ℓ₋ b) (ev₋ b) (p₋ b) (G₋ b) (≅ᴵ-trans (≅ᴵ-sym eq) (eη b)) (≺ᴵ-respʳ (h₋ b) eq))
       (Fk₁ S {ev = ev} {p = p} tt {𝓖₁ = Vis (suc zero)} {𝓖₂ = VF 𝓟 i} (λ v → c1 v) (λ v → v) wT (Ωg (suc zero)) (Ωˢ-refl (suc zero)))
       (λ η e w → TT η e (Good true (VF 𝓟 i ∧ (λ O → Br₁ η O))) (Fk₁ S {ev = evT η e} {p = tg η e} (nzη e) {𝓖₁ = Vis η} {𝓖₂ = VF 𝓟 i ∧ (λ O → Br₁ η O)} (λ (v , b) → cT v b) proj₁ w (Ωg η) (Ωˢ-refl η)))
       (self₁ {ev = ev} {p = p} (Ωˢ-refl (suc zero)))
       (λ η e η′ e′ eq → TT η e (λ x → x ≅ˢ gη η′ e′) (TT η′ e′ (λ x → gT η e ≅ˢ x) (F≅ {ev = evT η e} {ev′ = evT η′ e′} rE rQ (Ωˢ-≅ eq) (tg η e) (tg η′ e′) (≅ᴵ-refl i))))
       (λ η e → TT η e (λ x → t₀ ⊑ᵒ x) (fold1-cong rE rQ (Ω-monoᵒ (one⊑η η e))))
       (λ η e η′ e′ h → TT η e (λ x → x ⊑ᵒ gη η′ e′) (TT η′ e′ (λ x → gT η e ⊑ᵒ x) (fold1-cong rE rQ (Ω-monoᵒ h))))
       (λ {O} v G → bd⊑ v (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G (rdT {ev′ = ev} {p′ = p} v (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) G))
       (λ {O} η e v b → TT η e (λ x → (G : Goodᴺ (toZ (run O x))) → Bd B ⊑ᴵ lvG G) (λ G → bd⊑ v (Ωˢ η) (Ωˢ-refl η) G (rdT {ev′ = evT η e} {p′ = tg η e} v (Ωˢ η) (Ωˢ-refl η) G)))
       ch₀
       (λ {O} η e v b → TT η e (λ x → (G : Goodᴺ (toZ (run O x))) → Br₁ (lvG G) O) (chS η e v b))
```


## §3 闭包算子

`Ω̂U-≅`: 闭包的互模拟, 分支经 `toT` 回到紧地板. `leU`, `s1U`, `stU`: 闭包的三条地板, 都读第 0 点.

```agda
nzB : ∀ {φ i ℓ η} (B : Top i ℓ (φ ⊔ fk zero)) → Bd B ⊑ᴵ η → NZ η
nzB {η = η} B e with ⊑ᴵ-trans (s⊑ z≅ (proj₂ (evF B) zero)) (⊑ᴵ-trans (FM B) e)
... | s⊑ _ q = NZ-of q

≈S→∼ : ∀ {n : ℕ} {s s′ : Sp n} → s ≈S s′ → sf s ∼ᶠ sf s′
≈S→∼ {n = zero} _ = fz∼
≈S→∼ {n = suc n} (sφ , _ , ss) = ⊔∼ (≈S→∼ ss) sφ

Ω̂U-≅ : ∀ {n flE flE′} {E : Fr (suc n) flE} {E′ : Fr (suc n) flE′} {s s′ : Sp (suc n)} → flE ∼ᶠ flE′ → E ≈U E′ → s ≈S s′ → Ω̂U E s ≈ᴿ Ω̂U E′ s′
Ω̂U-≅ {flE = flE} {flE′} {E} {E′} {s} {s′} sE rE ss ev p ev′ p′ ei =
  ŝ≅ (kd-≅ ei) (bound-≅ (⊔∼ (⊔∼ (≈S→∼ ss) sE) (fk∼ z≅)) evl p evl′ p′ ei)
     (fold-≅U {cv = cvFlo (suc zero)} {cv′ = cvFlo (suc zero)} sE rE (Ωˢ-refl (suc zero)) ss ev p ev′ p′ ei)
     (λ η e η′ e′ eη → toT η (nzB (bound ((sf s ⊔ flE) ⊔ fk zero) evl p) e) (λ x → x ≅ˢ _) (toT η′ (nzB (bound ((sf s′ ⊔ flE′) ⊔ fk zero) evl′ p′) e′) (λ x → _ ≅ˢ x)
        (fold-≅U {cv = cvFlo η} {cv′ = cvFlo η′} sE rE (Ωˢ-≅ eη) ss _ _ _ _ ei)))
  where
  evl : Ev _ ((sf s ⊔ flE) ⊔ fk zero)
  evl = (proj₁ ev , proj₁ (proj₂ ev)) , (λ {c} q → proj₂ (proj₂ ev) {c} q)
  evl′ : Ev _ ((sf s′ ⊔ flE′) ⊔ fk zero)
  evl′ = (proj₁ ev′ , proj₁ (proj₂ ev′)) , (λ {c} q → proj₂ (proj₂ ev′) {c} q)

module Fl {n flE} {E : Fr (suc n) flE} (fE : FFl E) {Q : Sp (suc n)} (pf : SF Q) {i ℓ} (ev : Ev ℓ (sf Q ⊔ (flE ⊔ fk zero))) (p : i <ᴵ ℓ) where
  e₀ : Ev ℓ (sf Q ⊔ flE)
  e₀ = proj₁ ev , proj₁ (proj₂ ev)

  Ω₁ = Ωˢ (suc zero)
  eΩ₁ = Ωˢ-refl (suc zero)

  s1U : Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ Ω̂U E Q ev p
  s1U = ŝ-rᴱ (B1₁ᴱ {φ = fk zero} {E = E} {Q = Q} {cv = λ e → e} {ev = ev} {p = p} (FFl.s1E fE pf e₀ p) Ω₁ eΩ₁)

  stU : Ord₊ˢ.suc (E Q e₀ p) ⊑ᴱ Ω̂U E Q ev p
  stU = ŝ-rᴱ (⊑ᴱ-trans (suc-fold₁ fE pf {k = zero} {ev = proj₁ ev , (proj₁ (proj₂ ev) , tt)} {p = p} {a = Ord₊ˢ.zero} z≅)
               (fold1-congᴱ {k = zero} {k′ = suc zero} {ev = proj₁ ev , (proj₁ (proj₂ ev) , tt)} {ev′ = ev} {p = p} {p′ = p} {x = 𝟏} {y = Ω₁} (FFl.rE fE) (SF≈ pf) (Ω1ᴱ (suc zero))))

wᶿ : ∀ {n : ℕ} → Wld (suc n)
wᶿ b (fl , P , w , r , s) = Lift _ (∀ {i ℓ} (ev : Ev ℓ (sf (er s) ⊔ fl)) (p : i <ᴵ ℓ) → 𝓕b b (P (er s) ev p))

upθ : ∀ {n : ℕ} {φ} {X : Fr (suc n) φ} b (s : WSp (suc n)) b′ (s′ : WSp (suc n)) → SG b s → wᶿ b s → SG b′ s′ → Rais (suc n) X b s b′ s′ → wᶿ b′ s′
upθ b s b′ (fl′ , P′ , w′ , r′ , t′) _ _ _ (sub , hb , hf) = ↑ hf
```

第 0 层的算子 `Θ₀`: 点上方的 `Stage` 由世界读出: 门槛来自 `cl` 与头的 `flX`.

```agda
Θ₀ : Fr 1 (fk zero)
Θ₀ Q ev p = Ω̂A 0 (proj₁ (proj₂ Q) tt) ev p

fΘ₀ : FFl Θ₀
fΘ₀ = ffl (λ { (sφ , H , _) → selfΩ̂0 (⊔∼ fz∼ sφ) (H tt) })
          (λ pf → pfl-Ω̂ (proj₁ pf))
          (λ pf ev p → ŝ-rᴱ (PFl.fS (proj₁ pf) {φ = fk zero} {cv = λ e → e} ev p (Ωˢ (suc zero)) (Ωˢ-refl (suc zero)) (Ω1ᴱ (suc zero))))
          (λ {Q} pf ev p → ŝ-rᴱ (⊑ᴱ-trans
             (suc-fold {φ = fz} {P = proj₁ (proj₂ Q) tt} {cv = λ _ → σ₀} {ev = proj₁ ev , tt} {p = p} {a = Ord₊ˢ.zero} (PFl.rP (proj₁ pf)) (PFl.f0 (proj₁ pf)) z≅)
             (fold-congᴱ {φ = fz} {φ′ = fk zero} {P = proj₁ (proj₂ Q) tt} {cv = λ _ → σ₀} {cv′ = λ e → e} {ev = proj₁ ev , tt} {ev′ = ev} {p = p} {p′ = p} {x = 𝟏} {y = Ωˢ (suc zero)} (PFl.rP (proj₁ pf)) (Ω1ᴱ (suc zero)))))

stageΘ : ∀ {fl} {Q : Fr 0 fl} {w : Wld 0} (r : RF 0 w Q) (b : Base) → w b (↑ tt) → Stage (𝓟b b) (pCb b) (Q tt)
stageΘ {Q = Q} r b we = stage (fX r)
  (λ ev p qa cO π cC fl′ → cl b (uF b (RFP.flX r b (↑ tt) (↑ tt) we ev p) qa) cO π cC fl′)
  (λ ev p wv → vX r b (↑ tt) (↑ tt) we ev p wv)
  (λ cO π ev p G q → dT r b (↑ tt) (↑ tt) we cO π ev p G q)

RFΘ₀ : RF 1 wᶿ Θ₀
RFΘ₀ = rfp fΘ₀ v dt fl′ (λ b s b′ s′ → upθ {X = Θ₀} b s b′ s′)
  where
  v : ∀ b (s : WSp 1) → SG b s → wᶿ b s → ∀ {i ℓ} (ev : Ev ℓ (sf (er s) ⊔ fk zero)) (p : i <ᴵ ℓ) → Wit i (VF (𝓟b b) i) → Good true (VF (𝓟b b) i) (Θ₀ (er s) ev p)
  v b (fl , Q , w , r , _) (b‡ , sub , we , _) _ {i} ev p wv =
    Good-mono (mapV i sub) (Step.V.val (stageΘ r b‡ we) ev p (wit-map i (mapV i sub) wv))
  dt : ∀ b (s : WSp 1) → SG b s → wᶿ b s → ∀ {i ℓ} {O : Obs i} → Ctx O → 𝓟b b O → (ev : Ev ℓ (sf (er s) ⊔ fk zero)) (p : i <ᴵ ℓ) (G : Goodᴺ (toZ (run O (Θ₀ (er s) ev p)))) → ∀ {K} (q : InF K (sf (er s) ⊔ fk zero)) → Dem (lvG G) q
  dt b s@(fl , Q , w , r , _) (b‡ , sub , we , _) _ {O = O} cO π ev p G (inl q) =
    demUp q (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)) (dT r b‡ (↑ tt) (↑ tt) we cO (sub π) (proj₁ ev) p (proj₁ L) q)
    where L = leHd {E = Θ₀} {Q = er s} fΘ₀ (sfW s) ev p (ctx-refl O cO) G
  dt b s _ _ cO π ev p G (inr ink) = inj₂ z≅
  fl′ : ∀ b (s : WSp 1) → SG b s → wᶿ b s → ∀ {i ℓ} (ev : Ev ℓ (sf (er s) ⊔ fk zero)) (p : i <ᴵ ℓ) → 𝓕b b (Θ₀ (er s) ev p)
  fl′ b s _ we ev p = uF b (lower we (proj₁ ev) p) (leHd {E = Θ₀} {Q = er s} fΘ₀ (sfW s) ev p)
```

一般层的算子 `Θ n`: 吃任意世界上的任意好帧 $E$, 输出 `Ω̂U E`. **这里没有对 $n$ 的归纳:** 帧的好性是脊里带的数据.

```agda
Θ : ∀ n → Fr (suc (suc n)) (fk zero)
Θ n Q ev p = Ω̂U (proj₁ (proj₂ Q)) (proj₂ (proj₂ Q)) (proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)) p

fΘ : ∀ n → FFl (Θ n)
fΘ n = ffl (λ { {_} {_} (sφ , H , ss) ev p ev′ p′ ei → Ω̂U-≅ sφ H ss _ p _ p′ ei })
           (λ {Q} pf → pfl-of (λ ev p ev′ p′ ei → Ω̂U-≅ (∼ᶠ-refl _) (FFl.rE (proj₁ pf)) (SF≈ (proj₂ pf)) _ p _ p′ ei)
                               (λ ev p → Fl.s1U (proj₁ pf) (proj₂ pf) (proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)) p))
           (λ pf ev p → Fl.s1U (proj₁ pf) (proj₂ pf) (proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)) p)
           (λ pf ev p → Fl.stU (proj₁ pf) (proj₂ pf) (proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)) p)

RFΘ : ∀ n → RF (suc (suc n)) wᶿ (Θ n)
RFΘ n = rfp (fΘ n) v dt fl′ (λ b s b′ s′ → upθ {X = Θ n} b s b′ s′)
  where
  v : ∀ b (s : WSp (suc (suc n))) → SG b s → wᶿ b s → ∀ {i ℓ} (ev : Ev ℓ (sf (er s) ⊔ fk zero)) (p : i <ᴵ ℓ) → Wit i (VF (𝓟b b) i) → Good true (VF (𝓟b b) i) (Θ n (er s) ev p)
  v b (fl , E , w , r , s) (b‡ , sub , we , sg) _ {i} ev p wv =
    Good-mono (mapV i sub) (Step1.V.val r (FF1.pk b‡ s sg we) (proj₁ (proj₁ ev) , (proj₂ (proj₁ ev) , proj₂ ev)) p (wit-map i (mapV i sub) wv))
  dt : ∀ b (s : WSp (suc (suc n))) → SG b s → wᶿ b s → ∀ {i ℓ} {O : Obs i} → Ctx O → 𝓟b b O → (ev : Ev ℓ (sf (er s) ⊔ fk zero)) (p : i <ᴵ ℓ) (G : Goodᴺ (toZ (run O (Θ n (er s) ev p)))) → ∀ {K} (q : InF K (sf (er s) ⊔ fk zero)) → Dem (lvG G) q
  dt b s₀@(fl , E , w , r , s) (b‡ , sub , we , sg) _ {O = O} cO π ev p G (inl q) =
    demUp q (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)) (dT r b‡ s sg we cO (sub π) (proj₁ ev) p (proj₁ L) q)
    where L = leHd {E = Θ n} {Q = er s₀} (fΘ n) (sfW s₀) ev p (ctx-refl O cO) G
  dt b s _ _ cO π ev p G (inr ink) = inj₂ z≅
  fl′ : ∀ b (s : WSp (suc (suc n))) → SG b s → wᶿ b s → ∀ {i ℓ} (ev : Ev ℓ (sf (er s) ⊔ fk zero)) (p : i <ᴵ ℓ) → 𝓕b b (Θ n (er s) ev p)
  fl′ b s _ we ev p = uF b (lower we (proj₁ ev) p) (leHd {E = Θ n} {Q = er s} (fΘ n) (sfW s) ev p)
```

## §4 塔

```agda
Θf : ∀ n → Fr (suc n) (fk zero)
Θf zero    = Θ₀
Θf (suc n) = Θ n

RFΘf : ∀ n → RF (suc n) wᶿ (Θf n)
RFΘf zero    = RFΘ₀
RFΘf (suc n) = RFΘ n

∅U : Fr 0 fz
∅U _ ev p = ∅ᴿ tt p

pfl∅U : PFl (∅U tt)
pfl∅U = pfl r∅U (λ {i} ev p → ≅→⊑ᴱ (Ωˢ-refl i)) fS∅
  where
  r∅U : ∅U tt ≈ᴿ ∅U tt
  r∅U ev p ev′ p′ ei = Ωˢ-≅ ei
  fS∅ : ∀ {φ k i ℓ} {cv : ∀ {L} → Ev L φ → Simᴵ k L} (ev : Ev ℓ ((fz ⊔ fz) ⊔ φ)) (p : i <ᴵ ℓ) (y : Ordˢ k) → y ≅ˢ y →
        𝟏 ⊑ᴱ y → Ord₊ˢ.suc (Ωˢ i) ⊑ᴱ fold 0 φ cv (∅U tt) y ev p
  fS∅ {φ = φ} {i = i} {cv = cv} ev p y ey h =
    ⊑ᴱ-trans (suc-fold {φ = fz} {P = ∅U tt} {cv = λ _ → σ₀} {ev = proj₁ ev , tt} {p = p} {a = Ord₊ˢ.zero} r∅U (λ {i′} ev′ p′ → ≅→⊑ᴱ (Ωˢ-refl i′)) z≅)
             (fold-congᴱ {φ = fz} {φ′ = φ} {P = ∅U tt} {cv = λ _ → σ₀} {cv′ = cv} {ev = proj₁ ev , tt} {ev′ = ev} {p = p} {p′ = p} r∅U h)

w∅ : Wld 0
w∅ b _ = Lift _ (∀ {i ℓ} (ev : Ev ℓ (fz ⊔ fz)) (p : i <ᴵ ℓ) → 𝓕b b (∅U tt ev p))

val∅ : ∀ {𝓟 : Pd} {i ℓ} (ev : Ev ℓ (fz ⊔ fz)) (p : i <ᴵ ℓ) → Wit i (VF 𝓟 i) → Good true (VF 𝓟 i) (∅U tt ev p)
val∅ {i = zero}    ev p w = b1 z≅
val∅ {i = suc j}   ev p w = Good-mono (λ v → Vis-mono ≺-suc (proj₁ v)) (Ωg (suc j))
val∅ {i = lim f s} ev p w = Good-mono (λ v → Vis-mono ≺-suc (proj₁ v)) (Ωg (lim f s))

RF∅ : RF 0 w∅ ∅U
RF∅ = rfp pfl∅U (λ b s _ _ ev p w → val∅ ev p w) (λ b s _ _ cO π ev p G → λ { (inl ()) ; (inr ()) }) (λ b s _ we ev p → lower we ev p) (λ _ _ _ _ _ _ _ ())

𝓟⊤ : Pd
𝓟⊤ _ = ⊤

b⊤ : Base
b⊤ = base 𝓟⊤ (λ _ _ _ → tt) (λ _ → ⊤) (λ _ _ → tt) (λ _ _ _ _ _ → tt)

ws : ∀ n → WSp (suc n)
ws zero    = fz , ∅U , w∅ , RF∅ , ↑ tt
ws (suc n) = fk zero , Θf n , wᶿ , RFΘf n , ws n

sg : ∀ n → SG b⊤ (ws n)
sg zero    = b⊤ , (λ _ → tt) , ↑ (λ _ _ → tt) , ↑ tt
sg (suc n) = b⊤ , (λ _ → tt) , ↑ (λ _ _ → tt) , sg n

T : ∀ n {ℓ} → Ev ℓ (sf (er (ws n)) ⊔ fk zero) → zero <ᴵ ℓ → Ordˢ zero
T n ev z = Θf n (er (ws n)) ev z

Gθ : ∀ n {ℓ} (ev : Ev ℓ (sf (er (ws n)) ⊔ fk zero)) (z : zero <ᴵ ℓ) → Good true (VF 𝓟⊤ zero) (T n ev z)
Gθ n ev z = vX (RFΘf n) b⊤ (ws n) (sg n) (↑ (λ _ _ → tt)) ev z (refl , tt)

GΘ : ∀ n {ℓ} (ev : Ev ℓ (sf (er (ws n)) ⊔ fk zero)) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (T n ev z))
GΘ n ev z = Good→N (refl , tt) (Gθ n ev z)
```

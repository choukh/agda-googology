# 抽象类族上的折叠定理 (五): 深度 1 的闭包, $\psi_0(\Omega_\Omega^2)$

> 接 [UniformNF3D2S](UniformNF3D2S.lagda.md), [UniformNF3D2H](UniformNF3D2H.lagda.md). 结论先说:
>
> 1. **`Step1.V.val`: 帧 $E$ 上的闭包 `Ω̂A 1 E` 作用在好底上是好的.** 与 `Step.V.val` 同形, 把 `fold 0` 换成 `fold 1`, 把 `Fk` 换成 `Fk₁`.
> 2. **`Gᴺsq`: `Goodᴺ (toZ (Ω̂A 1 (Ω̂A 0) ∅ᴿ ev z))`, 对一切环境与证据.** 这是 $\psi_0(\Omega_\Omega^2)$. 构造不读记号. 验收在 [UniformNF3D2Accept](UniformNF3D2Accept.lagda.md).
> 3. **分支的根地板.** 闭包的分支是 `fold 1 (fk η) … (Ωˢ η)`, 非紧. `toT`: $\Omega_\eta$ ($\eta\ne0$) 的头部没有后继行, 根上的地板不被读到, 在派发之后它与紧地板的折叠定义性相等.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D2T where

open import Agda.Primitive using (Level)
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
open import OCF.Align.UniformNF3Eq using (_≅ᶻ_; ŝ≅; ⊑ᴵ-≅ʳ; ⊑ᴵ-≅ˡ; ≅ᴵ→⊑ᴵ; ≅ᶻ-sym; _≅ˢ_; toZ-≅; Ωˢ-≅; Ωˢ-refl; _≈ᴿ_; _≈₁_)
open import OCF.Align.Uniform3Base using (flo; cvFlo; toFlo; fz; fk; _⊔_; Ev; InF; inl; inr; ink; liftEv; Run; A; Top; bound; Bd; ubd; Fc; evF; iF; FM; FB; Dem; fold; Ω̂A; ∅ᴿ)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D1O using (Obs; idO; fo1; run; _≈ᵒ_; run-≅)
open import OCF.Align.UniformNF3D1N using (_⊑ᵒ_; Ω-monoᵒ; fold1-cong)
open import OCF.Align.UniformNF3D1G using (FFl; F≅; B1₁ᴱ; fold1-congᴱ; _⊑ᴱ_; Ctx; ctx-refl; PFl; pfl∅; 𝟏; ⊑ᴱ-trans; ≅→⊑ᴱ; Ω1ᴱ; Ω<ᴱ; Ω-strict)
open import OCF.Align.UniformNF3D1C
open import OCF.Align.UniformNF3D1H using (ffl-Ω̂)
open import OCF.Align.UniformNF3D1CF using (NZ-of)
open import OCF.Align.UniformNF3D2F using (VF; Pd)
open import OCF.Align.UniformNF3D2C using (Stage; stage; pfS; pOvS; vS; dmS; module FrameL; demUp)
open import OCF.Align.UniformNF3D2H using (PCg; module Aux; module FF1)
open import OCF.Align.UniformNF3D2S using (read1; zlt; ≺ᴵ-up; Ωvia; τ; vEΩ; dmEΩ; h2N; module Step)
open import OCF.Align.Stage2Label using (one⁰)
```

## §1 `Br₁` 与行引理

```agda
trans<′ : ∀ {x a b} → x <ᴵ a → a <ᴵ b → x <ᴵ b
trans<′ x zero      = suc x
trans<′ x (suc q)   = suc (trans<′ x q)
trans<′ x (lim n q) = lim n (trans<′ x q)

toT : ∀ {flE fl} {E : A 1 flE} {Q : Run fl} (η : Ordᴵ) → NZ η → ∀ {ℓ i} {u : Ev ℓ fl} {v : Ev ℓ flE} {w : Ev ℓ (fk η)} {p : i <ᴵ ℓ} {a : Level} (𝓧 : Ordˢ i → Set a) →
      𝓧 (fold 1 (flo η) (cvFlo η) E (Ωˢ η) Q (u , (v , toFlo η (λ q → w (suc q)))) p) → 𝓧 (fold 1 (fk η) (λ e q → e (suc q)) E (Ωˢ η) Q (u , (v , w)) p)
toT (suc j)   nz {w = w} {p = p} 𝓧 x with <ᴵ-dec (w (suc zero)) p
... | injᵃ (via e r) = x
... | injᵇ _ = x
... | injᶜ _ = x
toT (lim f s) nz 𝓧 x = x

module Step1 {flE} {E : A 1 flE} (fE : FFl E) (dmE : ∀ {X K} (q : InF K flE) → Dem X q)
             (vE : ∀ {𝓟 : Pd} {pCg : PCg 𝓟} {fl} {Q : Run fl} → Stage 𝓟 pCg Q → ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ flE)) (p : i <ᴵ ℓ) → Wit i (VF 𝓟 i) → Good true (VF 𝓟 i) (E Q ev p))
             {𝓟 : Pd} {pCg : PCg 𝓟} {fl} {Q : Run fl} (S : Stage 𝓟 pCg Q) where
  open Aux fE S
  open FF1 fE dmE vE using (Fk₁)
  open Step S using (ω1b; readT)

  Fo : ∀ k {i ℓ} → Ordˢ k → Ev ℓ (fl ⊔ (flE ⊔ flo k)) → i <ᴵ ℓ → Ordˢ i
  Fo k t ev p = fold 1 (flo k) (cvFlo k) E t Q ev p

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
    gη η e = fold 1 (fk η) (λ e′ q → e′ (suc q)) E (Ωˢ η) Q (evη η e) (tg η e)

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
      ubd B (via e q) (λ { (inl (inl k)) → demUp k (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)) (dmS S (cxT i v) (pT i v) (proj₁ ev′) p′ (proj₁ L) k)
                         ; (inl (inr k)) → dmE k ; (inr ink) → inj₂ z≅ })
      where L = leF pf ev′ p′ t et (ctx-refl O (cxT i v)) G

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

    selfV : Ω̂A 1 E Q ev p ≅ˢ Ω̂A 1 E Q ev p
    selfV = ŝ≅ refl (≅ᴵ-refl _) (self₁ {ev = ev} {p = p} (Ωˢ-refl (suc zero)))
       (λ η e η′ e′ eq → TT η e (λ x → x ≅ˢ gη η′ e′) (TT η′ e′ (λ x → gT η e ≅ˢ x) (F≅ {ev = evT η e} {ev′ = evT η′ e′} rE rQ (Ωˢ-≅ eq) (tg η e) (tg η′ e′) (≅ᴵ-refl i))))

    val : Wit i (VF 𝓟 i) → Good true (VF 𝓟 i) (Ω̂A 1 E Q ev p)
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

## §3 实例: $\psi_0(\Omega_\Omega^2)$

```agda
𝓟⊤ : Pd
𝓟⊤ _ = ⊤

pCg⊤ : PCg 𝓟⊤
pCg⊤ _ _ _ = tt

val∅ : ∀ {i ℓ} (ev : Ev ℓ fz) (p : i <ᴵ ℓ) → Wit i (VF 𝓟⊤ i) → Good true (VF 𝓟⊤ i) (∅ᴿ ev p)
val∅ {i = zero}    ev p w = b1 z≅
val∅ {i = suc j}   ev p w = Good-mono (λ v → Vis-mono ≺-suc (proj₁ v)) (Ωg (suc j))
val∅ {i = lim f s} ev p w = Good-mono (λ v → Vis-mono ≺-suc (proj₁ v)) (Ωg (lim f s))

stage∅ : Stage 𝓟⊤ pCg⊤ ∅ᴿ
stage∅ = stage pfl∅ (λ _ _ _ _ _ _ _ → tt) val∅ (λ _ _ _ _ _ → λ ())

Gᴺsq : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ fk zero))) (z : zero <ᴵ ℓ) → Goodᴺ (toZ (Ω̂A 1 (Ω̂A 0) ∅ᴿ ev z))
Gᴺsq ev z = Good→N (refl , tt) (Step1.V.val ffl-Ω̂ dmEΩ vEΩ stage∅ ev z (refl , tt))
```

`selfsq`: 证书树的自互模拟, 验收用它比较不同证书的计值.

```agda
selfsq : ∀ {ℓ} (ev : Ev ℓ (fz ⊔ (fk zero ⊔ fk zero))) (z : zero <ᴵ ℓ) → toZ (Ω̂A 1 (Ω̂A 0) ∅ᴿ ev z) ≅ᶻ toZ (Ω̂A 1 (Ω̂A 0) ∅ᴿ ev z)
selfsq ev z = toZ-≅ (Step1.V.selfV ffl-Ω̂ dmEΩ vEΩ stage∅ ev z)
```

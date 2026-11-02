# 抽象类族上的折叠定理 (二): 帧副本的后继行

> 接 [UniformNF3D2F](UniformNF3D2F.lagda.md). 判据的决定性一行在这里: 第 $m+1$ 份是以第 $m$ 份为底的同一个帧.
>
> 结论先说:
>
> 1. **`Row.outR` (§3): 只要帧作用在一切好底上 (`ih`), 后继行就好.** $k\ne0$. 证明里读 `𝓚` 的只有 `clk`、`cgk`、`ho`, 全是 `bs` 的字段.
> 2. **`clk`/`FlOver` 确实覆盖帧副本.** `Kₘ`: 第 $m$ 份为底的上下文 `fo1 O E (Rp m)` 压在 $b$ 之上, 所以在 `𝓚` 里. 吸收者不用新的.
> 3. **新的只有副本的类族 `𝓟′`:** "$\mathcal P$, 且第 1 份的值压在 $C_0$ 下 $b$ 的值之上 (`Cp`), 且 `fo1 O E Q ∈ 𝓚` (`Kp`)". 它不是按阶段写的: 对任意 $\mathcal P$, 任意底.
> 4. `Row0` (§4): $k=0$, 类族不变.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示. 定义与证明不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformNF3D2C where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; toZ; Ωˢ)
import OCF.Align.UniformNF3Eq
open import OCF.Align.UniformNF3Eq using (_≅ˢ_; ≅ᶻ-sym; toZ-≅; _≈ᴿ_; _≈₁_; fold-≅1; repR)
open import OCF.Align.Uniform3Base using (Flr; fz; fk; fb; _⊔_; Ev; Run; A; InF; ink; inb; inl; inr; Dem; DemB; isB; flo; cvFlo; repA; fold; wk; _∼ᶠ_; ⊔∼; ∼ᶠ-refl)
open import OCF.Align.NotFree using (Goodᴺ; forceᴺ; forceᴺ-HS; forceᴺ-≅)
open import OCF.Align.UniformNF3D1O using (Obs; idO; fo1; run; _≈ᵒ_; run-≅)
open import OCF.Align.UniformNF3D1N using (Goodᴺ-tr; _⊑ᵒ_)
open import OCF.Align.UniformNF3D1G using (_⊑ᴱ_; Ctx; ctx-refl; PFl; pfl; FFl; ⊑ᴱ-trans; ≅→⊑ᴱ; suc-rᴱ; B1ᴱ; B1₁ᴱ; F≅; 𝟏; module FramePF)
open import OCF.Align.UniformNF3D1C
open import OCF.Align.UniformNF3D2F using (FL; Pd; VF; ⊑ᴱ→ᵒ)
```

## §1 阶段与帧的地板

`Stage 𝓟 pCg B`: 底 $B$ 在类族 `VF 𝓟` 里好. `pOvS` 是类族对 "压在 $a\sqsupseteq B$ 之上" 的封闭性, `dmS` 说类族支配 $B$ 的地板. `vS` 只在类有居留时要求.

```agda
record Stage (𝓟 : Pd) (pCg : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → 𝓟 C′ → 𝓟 C) {fl} (B : Run fl) : Set₁ where
  constructor stage
  field
    pfS  : PFl B
    pOvS : ∀ {i j ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) {a : Ordˢ i} {O : Obs i} {C″ : Obs j} → B ev p ⊑ᴱ a → Ctx O → 𝓟 O → Ctx C″ → FL a O C″ → 𝓟 C″
    vS   : ∀ {i ℓ} (ev : Ev ℓ fl) (p : i <ᴵ ℓ) → Wit i (VF 𝓟 i) → Good true (VF 𝓟 i) (B ev p)
    dmS  : ∀ {i ℓ} {O : Obs i} → Ctx O → 𝓟 O → (ev : Ev ℓ fl) (p : i <ᴵ ℓ) (G : Goodᴺ (toZ (run O (B ev p)))) → ∀ {K} (q : InF K fl) → Dem (lvG G) q
open Stage public

demUp : ∀ {K φ} (q : InF K φ) {X Y} → X ⊑ᴵ Y → Dem X q → Dem Y q
demUp ink u (inj₁ h) = inj₁ (≺ᴵ-up′ h u)
  where
  ≺ᴵ-up′ : ∀ {b A′ B′} → b ≺ᴵ A′ → A′ ⊑ᴵ B′ → b ≺ᴵ B′
  ≺ᴵ-up′ (via e q) h′ = ≺ᴵ-respˡ e (sim h′ q)
demUp ink u (inj₂ z) = inj₂ z
demUp inb u h = ⊑ᴵ-trans h u
demUp (inl q) u h = demUp q u h
demUp (inr q) u h = demUp q u h

demFlo : ∀ k {X K} (q : InF K (flo k)) → k ⊑ᴵ X → Dem X q
demFlo (suc k) ink (s⊑ e q) = inj₁ (via e q)
demFlo (lim f s) inb h = h

pT : ∀ {𝓟 : Pd} i {O : Obs i} → VF 𝓟 i O → 𝓟 O
pT zero v = proj₂ v
pT (suc _) v = proj₂ v
pT (lim _ _) v = proj₂ v

cxV : ∀ {𝓟 : Pd} i {O : Obs i} → VF 𝓟 i O → Ctx O
cxV zero (refl , _) = tt
cxV (suc _) v = cx (proj₁ v)
cxV (lim _ _) v = cx (proj₁ v)

mapV : ∀ {𝓟 𝓠 : Pd} i {O : Obs i} → (𝓠 O → 𝓟 O) → VF 𝓠 i O → VF 𝓟 i O
mapV zero h (e , x) = e , h x
mapV (suc _) h (e , x) = e , h x
mapV (lim _ _) h (e , x) = e , h x

putV : ∀ {𝓟 𝓠 : Pd} i {O : Obs i} → 𝓠 O → VF 𝓟 i O → VF 𝓠 i O
putV zero x (e , _) = e , x
putV (suc _) x (e , _) = e , x
putV (lim _ _) x (e , _) = e , x
```

## §2 帧作用在底上的地板

```agda
module FrameL {flE} {E : A 1 flE} (fE : FFl E) where
  rE = FFl.rE fE

  leE : ∀ {fl} {B : Run fl} → PFl B → ∀ {i ℓ} (ev : Ev ℓ (fl ⊔ flE)) (p : i <ᴵ ℓ) → B (proj₁ ev) p ⊑ᴱ E B ev p
  leE pf ev p = ⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (PFl.rP pf (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl _)))) (FFl.stE fE pf ev p)

  leF : ∀ {fl k i ℓ} {B : Run fl} → PFl B → (ev : Ev ℓ (fl ⊔ (flE ⊔ flo k))) (p : i <ᴵ ℓ) (t : Ordˢ k) → t ≅ˢ t →
        B (proj₁ ev) p ⊑ᴱ fold 1 (flo k) (cvFlo k) E t B ev p
  leF {k = k} {B = B} pf ev p t et =
    B1₁ᴱ {φ = flo k} {E = E} {Q = B} {cv = cvFlo k} {ev = ev} {p = p} (leE pf (proj₁ ev , proj₁ (proj₂ ev)) p) t et

  flB : ∀ {fl k i ℓ} {B : Run fl} {O : Obs i} → PFl B → Ctx O → (ev : Ev ℓ (fl ⊔ (flE ⊔ flo k))) (p : i <ᴵ ℓ) →
        FL (B (proj₁ ev) p) O (fo1 {k = k} O E B ev p)
  flB {O = O} pf cO ev p t et G = leF pf ev p t et (ctx-refl O cO) G
```

`RpM`: 第 $m$ 份 `Rp m`, 它的地板与单调.

```agda
module RpM {flE} {E : A 1 flE} (fE : FFl E) {fl} {Q : Run fl} (pf : PFl Q) {k} {b : Ordˢ k} (eb : b ≅ˢ b) where
  open FrameL fE
  rQ = PFl.rP pf
  ψf = flE ⊔ flo k
  Fb : A 1 ψf
  Fb = fold 1 (flo k) (cvFlo k) E b

  rF : Fb ≈₁ Fb
  rF = fold-≅1 {cv = cvFlo k} {cv′ = cvFlo k} (∼ᶠ-refl flE) rE eb

  Rp : ℕ → Run (fl ⊔ ψf)
  Rp m = repA 0 Q Fb (suc m)

  rp : ∀ m → Rp m ≈ᴿ Rp m
  rp m = repR (∼ᶠ-refl fl) (∼ᶠ-refl ψf) rQ rF (suc m)

  s1R : ∀ m {j ℓ₁} (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) → Ord₊ˢ.suc (Ωˢ j) ⊑ᴱ Rp m ev₁ p₁
  pfR : ∀ m → PFl (Rp m)
  s1R zero ev₁ p₁ = B1₁ᴱ {φ = flo k} {E = E} {Q = Q} {cv = cvFlo k} {ev = ev₁} {p = p₁} (FFl.s1E fE pf (proj₁ ev₁ , proj₁ (proj₂ ev₁)) p₁) b eb
  s1R (suc m) ev₁ p₁ = B1₁ᴱ {φ = flo k} {E = E} {Q = Rp m} {cv = cvFlo k} {ev = ev₁ , proj₂ ev₁} {p = p₁} (FFl.s1E fE (pfR m) (ev₁ , proj₁ (proj₂ ev₁)) p₁) b eb
  pfR m = pfl (rp m)
    (λ {j} ev₁ p₁ → ⊑ᴱ-trans (suc-rᴱ (≅→⊑ᴱ (Ωˢ-refl′ j))) (s1R m ev₁ p₁))
    (λ {φ} {k₂} {j} {ℓ₁} {cv} ev₁ p₁ y ey oy → B1ᴱ {φ = φ} {P = Rp m} {cv = cv} {ev = ev₁} {p = p₁} (rp m) (s1R m (proj₁ ev₁) p₁) y ey)
    where
    Ωˢ-refl′ : ∀ j → Ωˢ j ≅ˢ Ωˢ j
    Ωˢ-refl′ = OCF.Align.UniformNF3Eq.Ωˢ-refl

  selfR : ∀ m {j ℓ₁} (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) → Rp m ev₁ p₁ ≅ˢ Rp m ev₁ p₁
  selfR m ev₁ p₁ = rp m ev₁ p₁ ev₁ p₁ (≅ᴵ-refl _)

  leS : ∀ m {j ℓ₁} (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) → Rp m ev₁ p₁ ⊑ᴱ Rp (suc m) ev₁ p₁
  leS m ev₁ p₁ = leF (pfR m) (ev₁ , proj₂ ev₁) p₁ b eb

  leR : ∀ m {j ℓ₁} (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) → Rp 0 ev₁ p₁ ⊑ᴱ Rp m ev₁ p₁
  leR zero ev₁ p₁ = ≅→⊑ᴱ (selfR 0 ev₁ p₁)
  leR (suc m) ev₁ p₁ = ⊑ᴱ-trans (leR m ev₁ p₁) (leS m ev₁ p₁)

  leQ : ∀ m {j ℓ₁} (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) → Q (proj₁ ev₁) p₁ ⊑ᴱ Rp m ev₁ p₁
  leQ m ev₁ p₁ = ⊑ᴱ-trans (leF pf ev₁ p₁ b eb) (leR m ev₁ p₁)
```

## §3 后继行, $k\ne0$

```agda
module Row {flE} {E : A 1 flE} (fE : FFl E) (dmE : ∀ {X K} (q : InF K flE) → Dem X q)
           {𝓟 : Pd} {pCg : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → 𝓟 C′ → 𝓟 C} {fl} {Q : Run fl} (S : Stage 𝓟 pCg Q)
           {k} (nk : NZ k) {i ℓ} {ev : Ev ℓ (fl ⊔ (flE ⊔ flo k))} {p : i <ᴵ ℓ} {𝓖′ : Cl i}
           (H₂ : ∀ {O} → 𝓖′ O → VF 𝓟 i O) (w : Wit i 𝓖′) {b : Ordˢ k} (eb : b ≅ˢ b) (𝓚 : Cl k)
           (Kc : ∀ {O} → 𝓖′ O → 𝓚 (fo1 O E Q ev p))
           (clk : ∀ {O C″} → 𝓚 O → FlOver b O C″ → 𝓚 C″)
           (cgk : ∀ {C C′} → Ctx C → C ≈ᵒ C′ → 𝓚 C′ → 𝓚 C)
           (ho : ∀ {C} → 𝓚 C → Hon k b C)
           (ih : ∀ {𝓟₂ : Pd} {pCg₂ : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → 𝓟₂ C′ → 𝓟₂ C} {fl₂} {B : Run fl₂} → Stage 𝓟₂ pCg₂ B →
                 ∀ {j ℓ₁} {ev₁ : Ev ℓ₁ (fl₂ ⊔ (flE ⊔ flo k))} {p₁ : j <ᴵ ℓ₁} {𝓖₂ : Cl j} →
                 (∀ {O} → 𝓖₂ O → 𝓚 (fo1 O E B ev₁ p₁)) → (∀ {O} → 𝓖₂ O → VF 𝓟₂ j O) → Wit j 𝓖₂ → Good true 𝓖₂ (fold 1 (flo k) (cvFlo k) E b B ev₁ p₁)) where
  open FrameL fE
  pf = pfS S
  open RpM fE pf eb
```

**类族.** `C₀ O₀ = fo1 O₀ E Q ev p`, `H₀ O₀` 是 $C_0$ 下 $b$ 的证书. `Cp O`: 第 1 份在 $O$ 下的值压在某个 $O_0\in$ `𝓖′` 的 $C_0$ 下 $b$ 的值之上. `Kp O`: `fo1 O E Q ∈ 𝓚`, 对任意环境.

```agda
  C₀ : Obs i → Obs k
  C₀ O₀ = fo1 O₀ E Q ev p

  Cp : ∀ {j} → Obs j → Set
  Cp {j} O = Σ (Obs i) λ O₀ → 𝓖′ O₀ × (∀ {ℓ₁} (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) (G : Goodᴺ (toZ (run O (Rp 0 ev₁ p₁)))) →
             Σ (Goodᴺ (toZ (run (C₀ O₀) b))) λ H → forceᴺ _ H ⊑ forceᴺ _ G)

  Kp : ∀ {j} → Obs j → Set
  Kp {j} O = ∀ {ℓ₁} {ev₁ : Ev ℓ₁ (fl ⊔ ψf)} {p₁ : j <ᴵ ℓ₁} → 𝓚 (fo1 O E Q ev₁ p₁)

  𝓟′ : Pd
  𝓟′ O = 𝓟 O × (Cp O × Kp O)

  pCg′ : ∀ {j} {C C′ : Obs j} → Ctx C → C ≈ᵒ C′ → 𝓟′ C′ → 𝓟′ C
  pCg′ {C = C} {C′ = C′} c₀ o (π , (O₀ , c , f) , κ) =
    pCg c₀ o π ,
    (O₀ , c , (λ ev₁ p₁ G →
      let d = toZ-≅ (run-≅ o (selfR 0 ev₁ p₁))
          G′ = Goodᴺ-tr d G
          Rr = f ev₁ p₁ G′
      in proj₁ Rr , ⊑-trans (proj₂ Rr) (≅→⊑ (forceᴺ-≅ (≅ᶻ-sym d) G′ G)))) ,
    (λ {ℓ₁} {ev₁} {p₁} → cgk (fE , pf , c₀) (fo1 o rE rQ) (κ {ev₁ = ev₁} {p₁ = p₁}))

  ovk : ∀ {j j′ ℓ₂} {O : Obs j} {C″ : Obs j′} {a : Ordˢ j} {ev₂ : Ev ℓ₂ (fl ⊔ ψf)} {p₂ : j <ᴵ ℓ₂} → Ctx O → (cp : Cp O) →
        Rp 0 ev₂ p₂ ⊑ᴱ a → FL a O C″ → FL b (C₀ (proj₁ cp)) C″
  ovk {O = O} {ev₂ = ev₂} {p₂ = p₂} cO (O₀ , c , f) qa fl′ t et G =
    let R₁ = fl′ t et G
        R₂ = qa (ctx-refl O cO) (proj₁ R₁)
        R₃ = f ev₂ p₂ (proj₁ R₂)
    in proj₁ R₃ , ⊑-trans (proj₂ R₃) (⊑-trans (proj₂ R₂) (proj₂ R₁))

  Kₘ : ∀ m {j ℓ₂} {O : Obs j} {ev₁ : Ev _ ((fl ⊔ ψf) ⊔ ψf)} {p₁ : j <ᴵ ℓ₂} → Ctx O → Cp O → 𝓚 (fo1 O E (Rp m) ev₁ p₁)
  Kₘ m {O = O} {ev₁ = ev₁} {p₁ = p₁} cO cp@(O₀ , c , f) =
    clk (Kc c) (flo-over (fE , pfR m , cO) (ovk cO cp (leR m (proj₁ ev₁) p₁) (flB (pfR m) cO ev₁ p₁)))

  pOv′ : ∀ m {i₁ j ℓ₁} (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : i₁ <ᴵ ℓ₁) {a : Ordˢ i₁} {O : Obs i₁} {C″ : Obs j} → Rp m ev₁ p₁ ⊑ᴱ a → Ctx O → 𝓟′ O → Ctx C″ → FL a O C″ → 𝓟′ C″
  pOv′ m ev₁ p₁ {O = O} {C″ = C″} qa cO (π , cp@(O₀ , c , f) , κ) xC fl′ =
    pOvS S (proj₁ ev₁) p₁ (⊑ᴱ-trans (leQ m ev₁ p₁) qa) cO π xC fl′ ,
    (O₀ , c , (λ ev₃ p₃ G → ovk cO cp (⊑ᴱ-trans (leR m ev₁ p₁) qa) fl′ _ (rp 0 ev₃ p₃ ev₃ p₃ (≅ᴵ-refl _)) G)) ,
    (λ {ℓ₃} {ev₃} {p₃} → clk (Kc c) (flo-over (fE , pf , xC) (λ t et G → ovk cO cp (⊑ᴱ-trans (leR m ev₁ p₁) qa) fl′ _ (F≅ rE rQ et p₃ p₃ (≅ᴵ-refl _)) G)))

  dm′ : ∀ m {j ℓ₁} {O : Obs j} → Ctx O → 𝓟′ O → (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) (G : Goodᴺ (toZ (run O (Rp m ev₁ p₁)))) → ∀ {K} (q : InF K (fl ⊔ ψf)) → Dem (lvG G) q
  dm′ m {O = O} cO (π , cp , κ) ev₁ p₁ G (inl q) =
    demUp q (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)) (dmS S cO π (proj₁ ev₁) p₁ (proj₁ L) q)
    where L = leQ m ev₁ p₁ (ctx-refl O cO) G
  dm′ m cO x ev₁ p₁ G (inr (inl q)) = dmE q
  dm′ m {O = O} cO (π , cp@(O₀ , c , f) , κ) ev₁ p₁ G (inr (inr q)) =
    demFlo k q (⊑ᴵ-trans (ho (Kc c) (proj₁ Rr)) (toLevel-⊑ (forceᴺ-HS _ (proj₁ Rr)) (forceᴺ-HS _ G) (⊑-trans (proj₂ Rr) (proj₂ L))))
    where
    L = leR m ev₁ p₁ (ctx-refl O cO) G
    Rr = f ev₁ p₁ (proj₁ L)

  Sₘ : ∀ m → Stage 𝓟′ pCg′ (Rp m)
  Sₘ zero = stage (pfR 0) (pOv′ 0)
    (λ {j} ev₁ p₁ wv → ih S {ev₁ = ev₁} {p₁ = p₁} {𝓖₂ = VF 𝓟′ j} (λ v → proj₂ (proj₂ (pT j v))) (mapV j proj₁) wv)
    (dm′ 0)
  Sₘ (suc m) = stage (pfR (suc m)) (pOv′ (suc m))
    (λ {j} ev₁ p₁ wv → ih (Sₘ m) {ev₁ = ev₁ , proj₂ ev₁} {p₁ = p₁} {𝓖₂ = VF 𝓟′ j} (λ v → Kₘ m (cxV j v) (proj₁ (proj₂ (pT j v)))) (λ v → v) wv)
    (dm′ (suc m))

  inj : ∀ {O} → 𝓖′ O → VF 𝓟′ i O
  inj {O} c = putV {𝓟 = 𝓟} {𝓠 = 𝓟′} i (pT i (H₂ c) ,
      (O , c , (λ ev₁ p₁ G →
        let d = toZ-≅ (run-≅ (ctx-refl O cO) (rp 0 ev₁ p₁ ev p (≅ᴵ-refl i)))
            G′ = Goodᴺ-tr d G
        in G′ , ≅→⊑ (forceᴺ-≅ (≅ᶻ-sym d) G′ G))) ,
      (λ {ℓ₁} {ev₁} {p₁} → cgk (fE , pf , cO) (fo1 (ctx-refl O cO) rE rQ) (Kc c))) (H₂ c)
    where cO = cxV i (H₂ c)

  outR : Good true 𝓖′ (fold 1 (flo k) (cvFlo k) E (Ord₊ˢ.suc b) Q ev p)
  outR = bl hh mo
    where
    hh : ∀ m → Good true 𝓖′ (repA 0 Q Fb m ev p)
    hh zero = Good-mono H₂ (vS S (proj₁ ev) p (wit-map i H₂ w))
    hh (suc m) = Good-mono inj (vS (Sₘ m) ev p (wit-map i inj w))
    mo : ∀ m → repA 0 Q Fb m ev p ⊑ᵒ repA 0 Q Fb (suc m) ev p
    mo zero = ⊑ᴱ→ᵒ (rQ (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i)) (leF pf ev p b eb)
    mo (suc m) = ⊑ᴱ→ᵒ (selfR m ev p) (leS m ev p)
```

## §4 后继行, $k=0$

第 0 层的尾巴不读上下文, 地板是 `fz`, 类族不变. `ih` 不带 `𝓚`.

```agda
module Row0 {flE} {E : A 1 flE} (fE : FFl E) (dmE : ∀ {X K} (q : InF K flE) → Dem X q)
            {𝓟 : Pd} {pCg : ∀ {i} {C C′ : Obs i} → Ctx C → C ≈ᵒ C′ → 𝓟 C′ → 𝓟 C} {fl} {Q : Run fl} (S : Stage 𝓟 pCg Q)
            {i ℓ} {ev : Ev ℓ (fl ⊔ (flE ⊔ fz))} {p : i <ᴵ ℓ} {𝓖′ : Cl i}
            (H₂ : ∀ {O} → 𝓖′ O → VF 𝓟 i O) (w : Wit i 𝓖′) {b : Ordˢ zero} (eb : b ≅ˢ b)
            (ih : ∀ {fl₂} {B : Run fl₂} → Stage 𝓟 pCg B → ∀ {j ℓ₁} {ev₁ : Ev ℓ₁ (fl₂ ⊔ (flE ⊔ fz))} {p₁ : j <ᴵ ℓ₁} {𝓖₂ : Cl j} →
                  (∀ {O} → 𝓖₂ O → VF 𝓟 j O) → Wit j 𝓖₂ → Good true 𝓖₂ (fold 1 fz (cvFlo zero) E b B ev₁ p₁)) where
  open FrameL fE
  pf = pfS S
  open RpM fE pf eb

  dm′ : ∀ m {j ℓ₁} {O : Obs j} → Ctx O → 𝓟 O → (ev₁ : Ev ℓ₁ (fl ⊔ ψf)) (p₁ : j <ᴵ ℓ₁) (G : Goodᴺ (toZ (run O (Rp m ev₁ p₁)))) → ∀ {K} (q : InF K (fl ⊔ ψf)) → Dem (lvG G) q
  dm′ m {O = O} cO π ev₁ p₁ G (inl q) =
    demUp q (toLevel-⊑ (forceᴺ-HS _ (proj₁ L)) (forceᴺ-HS _ G) (proj₂ L)) (dmS S cO π (proj₁ ev₁) p₁ (proj₁ L) q)
    where L = leQ m ev₁ p₁ (ctx-refl O cO) G
  dm′ m cO x ev₁ p₁ G (inr (inl q)) = dmE q
  dm′ m cO x ev₁ p₁ G (inr (inr ()))

  Sₘ : ∀ m → Stage 𝓟 pCg (Rp m)
  Sₘ zero = stage (pfR 0) (λ ev₁ p₁ qa → pOvS S (proj₁ ev₁) p₁ (⊑ᴱ-trans (leQ 0 ev₁ p₁) qa))
    (λ {j} ev₁ p₁ wv → ih S {ev₁ = ev₁} {p₁ = p₁} {𝓖₂ = VF 𝓟 j} (λ v → v) wv) (dm′ 0)
  Sₘ (suc m) = stage (pfR (suc m)) (λ ev₁ p₁ qa → pOvS S (proj₁ ev₁) p₁ (⊑ᴱ-trans (leQ (suc m) ev₁ p₁) qa))
    (λ {j} ev₁ p₁ wv → ih (Sₘ m) {ev₁ = ev₁ , proj₂ ev₁} {p₁ = p₁} {𝓖₂ = VF 𝓟 j} (λ v → v) wv) (dm′ (suc m))

  outR : Good true 𝓖′ (fold 1 fz (cvFlo zero) E (Ord₊ˢ.suc b) Q ev p)
  outR = bl hh mo
    where
    hh : ∀ m → Good true 𝓖′ (repA 0 Q Fb m ev p)
    hh zero = Good-mono H₂ (vS S (proj₁ ev) p (wit-map i H₂ w))
    hh (suc m) = Good-mono H₂ (vS (Sₘ m) ev p (wit-map i H₂ w))
    mo : ∀ m → repA 0 Q Fb m ev p ⊑ᵒ repA 0 Q Fb (suc m) ev p
    mo zero = ⊑ᴱ→ᵒ (rQ (proj₁ ev) p (proj₁ ev) p (≅ᴵ-refl i)) (leF pf ev p b eb)
    mo (suc m) = ⊑ᴱ→ᵒ (selfR m ev p) (leS m ev p)
```

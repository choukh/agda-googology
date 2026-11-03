# Uniform3Rel (验收副本)

> **验收用, 不在主线闭包内.** 脚本从 [Uniform3Rel](../../Align/Uniform3Rel.lagda.md) 切出: 只留 `UniformNF5Accept` 的定义级切片里、主线 `OCF.Free.*` 之外的块, 代码行逐字, 导入改指 `OCF.Free.*`. 讲解见原文件.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Lab.Uniform3Rel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong) 
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Lab.Level
open import OCF.Free.Lab.Prefix using (Z; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; out-intoˢ; toZ; Ωˢ; trˢ; tr⁻ˢ; addˢ; H1-pen)
import OCF.Align.EBO as E
open import OCF.Free.Lab.Correspond using (Lab; l0; l1; lω)
open import OCF.Free.Lab.StandardOmega using (NF₁; NF₁-fsn)
open import OCF.Free.Lab.SystemOmega using (Occ; oh; od; os; ot)
open import OCF.Free.Lab.Stage2 using (Ωᵗ)
open import OCF.Free.Lab.Stage2Label using (one⁰)
open import OCF.Free.Lab.DecoupleBase using (ΩΩ)
open import OCF.Free.Lab.Decouple using (Idx; lvI; Ieq)
open import OCF.Free.Lab.GoodLBase
open import OCF.Free.Lab.OmegaExpBase using (cofW; H1W; gtW; ne-w; 1<γ)
open import OCF.Free.Lab.UniformS
open import OCF.Free.Lab.Uniform3Base
open import OCF.Free.Lab.Uniform3 using (good∅ᴿ)
open import OCF.Free.Lab.Relative using (UpK; uz; us; Eqᴬ; zᴬ; sᴬ; lᴬ; lᵢᴬ; uᴬ; ŝᴬ; ĉᴬ; Rᴬ; _≅ᴬ_; R→≅ᴬ; ≅→Rᴬ; ≅ᴬ-sym; R-flipᴬ; flipRᴬ; ≅ᴬ→≅ˢ₀; trˢ-≅ᴬ; tr⁻ˢ-≅ᴬ; backˢ-≅ᴬ; back⁻ˢ-≅ᴬ; ≅ᴬ-tr⁻ˢ; Ωˢ-≅ᴬ; R-convᴬ; addˢ-≅ᴬ) public
```

```agda
open Ord-Ord using (iter)
open E using (T; PT; natT; fsT; cof; cΩ; Ωt; _<ᵀ_; cofA; []<) renaming (ψ to ψᵗ)
```

## §1 目标下界与可忽略的地板项

```agda
Up : Ordᴵ → Ordᴵ → Set
Up c i = (c ≺ᴵ i) ⊎ (c ≅ᴵ i)

≼≺ : ∀ {a b d} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → b ≺ᴵ d → a ≺ᴵ d
≼≺ (inj₁ s) s′ = ≺ᴵ-trans s s′
≼≺ (inj₂ e) s′ = ≺ᴵ-respˡ e s′

Up-≅ : ∀ {c i i′} → Up c i → i ≅ᴵ i′ → Up c i′
Up-≅ (inj₁ s)  e = inj₁ (≺ᴵ-respʳ s e)
Up-≅ (inj₂ e′) e = inj₂ (≅ᴵ-trans e′ e)

Up-≺ : ∀ {c i j} → Up c i → i ≺ᴵ j → Up c j
Up-≺ u s = inj₁ (≼≺ u s)

Ign : Ordᴵ → Ordᴵ → Set
Ign c K = (K ≅ᴵ zero) ⊎ ((K ≺ᴵ c) ⊎ (K ≅ᴵ c))
```

```agda
one three : Ordᴵ
one = suc zero
three = suc (suc (suc zero))

s⊑s→≼ : ∀ {a c} → suc a ⊑ᴵ suc c → (a ≺ᴵ c) ⊎ (a ≅ᴵ c)
s⊑s→≼ (s⊑ e zero)    = inj₂ e
s⊑s→≼ (s⊑ e (suc q)) = inj₁ (via e q)

≼→⊑ : ∀ {a b} → (a ≺ᴵ b) ⊎ (a ≅ᴵ b) → a ⊑ᴵ b
≼→⊑ (inj₁ (via e q)) = ⊑ᴵ-trans (≅ᴵ→⊑ᴵ e) (Sim→⊑ᴵ (λ q′ → <ᴵ-trans q′ q))
≼→⊑ (inj₂ e) = ≅ᴵ→⊑ᴵ e
```

```agda
IgnK : ∀ {K φ} → Ordᴵ → InF K φ → Set
IgnK {K} c k = Ign c K ⊎ ((isB k ≡ true) × (K ⊑ᴵ suc c))

IgnL : Ordᴵ → Flr → Set
IgnL c φ = ∀ {K} (k : InF K φ) → IgnK c k

floIgn : ∀ {c} k → k ⊑ᴵ suc c → IgnL c (flo k)
floIgn zero      le ()
floIgn (suc k″)  le ink = inj₁ (inj₂ (s⊑s→≼ le))
floIgn (lim f s) le inb = inj₂ (refl , le)

DemIgn : ∀ {K φ c η} (k : InF K φ) → IgnK c k → suc c ⊑ᴵ η → Dem η k
DemIgn k (inj₁ (inj₁ k0)) le = dem k (inj₂ k0)
DemIgn k (inj₁ (inj₂ kc)) le = dem k (inj₁ (≺-of-⊑ (⊑ᴵ-trans (sB kc) le)))
DemIgn {K} {η = η} k (inj₂ (b , kle)) le = subst (λ bb → DemB bb η K) (sym b) (⊑ᴵ-trans kle le)
```

## §2 依目标的地板见证

```agda
LW[_] : ∀ {φ} → Ordᴵ → Run φ → T → Set
LW[_] {φ} c R u = ∀ {i ℓ w} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (Iw : Idx w) → i ≅ᴵ lvI Iw → kd i ≡ false → Up c i →
                  LabL₊ i Ll (R ev p) (ψᵗ w u ∷ [])

FW[_] : Ordᴵ → Flr → T → PT → T → Set
FW[ c ] φ ps y ys = ∀ {K} (k : InF K φ) →
                    IgnK c k ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Ob w ps y ys

FW→FW[] : ∀ {c φ ps y ys} → FW φ ps y ys → FW[ c ] φ ps y ys
FW→FW[] F k with F k
... | inj₁ k0 = inj₁ (inj₁ (inj₁ k0))
... | inj₂ w = inj₂ w

FlrLab[_] : Ordᴵ → Flr → T → Set
FlrLab[ c ] φ ps = ∀ {K} (k : InF K φ) →
                   IgnK c k ⊎ Σ T λ w → Σ (Idx w) λ Iw → ((K ≺ᴵ lvI Iw) ⊎ (K ≅ᴵ lvI Iw)) × Occ w ps

FlrLab→[] : ∀ {c φ ps} → FlrLab φ ps → FlrLab[ c ] φ ps
FlrLab→[] F k with F k
... | inj₁ k0 = inj₁ (inj₁ (inj₁ k0))
... | inj₂ w = inj₂ w
```

```agda
module _ {c φ} {ps : T} {y : PT} {ys : T} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
         (fw : FW[ c ] (φ ⊔ fk zero) ps y ys) (cs : cof (y ∷ ys) ≡ cΩ []) where

  pickWᵗ : ∀ {i ℓ w} → Up c i → (Iw : Idx w) → i ≅ᴵ lvI Iw → (B : Top i ℓ (φ ⊔ fk zero)) →
           Σ T λ w′ → Σ (Idx w′) λ Iw′ → (Bd B ⊑ᴵ suc (lvI Iw′)) × (∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ []))
  pickWᵗ {i} {ℓ} {w} u Iw ei B = Pick.pw Pk , Pick.pI Pk ,
      ubd B (≼→≺s (≼-trans (inj₂ ei) (Pick.pc Pk))) (λ k → pd k (Pick.pF Pk k)) , Pick.pP Pk
    where
    P′ : T → Set
    P′ w′ = ∀ θ → Occ w′ (ψᵗ w (ps ++ fsT (y ∷ ys) θ) ∷ [])
    wit : ∀ {K} (k : InF K (φ ⊔ fk zero)) → IgnK c k ⊎ (Σ T λ w₁ → Σ (Idx w₁) λ I₁ → (K ≼ lvI I₁) × P′ w₁)
    wit k with fw k
    ... | inj₁ g = inj₁ g
    ... | inj₂ (w₁ , I₁′ , kw , ob′) = inj₂ (w₁ , I₁′ , kw , (λ θ → od (ob′ θ)))
    Pk : Pick P′ (φ ⊔ fk zero) (IgnK c) (lvI Iw)
    Pk = pickMax (φ ⊔ fk zero) (IgnK c) wit Iw (λ θ → oh) (inj₂ (≅ᴵ-refl _))
    cW : suc c ⊑ᴵ suc (lvI (Pick.pI Pk))
    cW = sB (≼-trans u (≼-trans (inj₂ ei) (Pick.pc Pk)))
    pd : ∀ {K} (k : InF K (φ ⊔ fk zero)) → IgnK c k ⊎ (K ≼ lvI (Pick.pI Pk)) → Dem (suc (lvI (Pick.pI Pk))) k
    pd k (inj₁ g)  = DemIgn k g cW
    pd k (inj₂ kw) = dem k (inj₁ (≼→≺s kw))

  cloWᵗ : LW[ c ] t (ps ++ fsT (y ∷ ys) (natT 1)) →
          (∀ θ Y hY → Lab Y θ → NF₁ θ → natT 1 <ᵀ θ → LW[ c ] (g (toLevel Y hY)) (ps ++ fsT (y ∷ ys) θ)) →
          LW[ c ] (cloA 0 t g) (ps ++ (y ∷ ys))
  cloWᵗ h₀ hg {w = []} ev p Iw ei ki u = ⊥-elim (ne-w Iw ei ki refl)
  cloWᵗ h₀ hg {w = x ∷ xs} ev p Iw ei ki u =
    gŝ ki (trans (cofW (x ∷ xs) ps y ys) (trans (cong (cofA (x ∷ xs)) cs) (H1-pen x xs)))
       (proj₁ (proj₂ Pk)) (proj₁ (proj₂ (proj₂ Pk)))
       (λ θ → subst (Occ _) (sym (H1W x xs ps y ys cs θ)) (proj₂ (proj₂ (proj₂ Pk)) θ))
       (subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs (natT 1))) (h₀ ev p Iw ei ki u))
       (λ θ Y hY lY nθ lt e → subst (LabL₊ _ Ll _) (sym (H1W x xs ps y ys cs θ))
            (hg θ Y hY lY nθ lt (evη φ B (toLevel Y hY) e) (lim 0 (iF B)) Iw ei ki u))
    where
    B = bound (φ ⊔ fk zero) ev p
    Pk = pickWᵗ u Iw ei B
```

## §4 折叠尊重 $\cong^\mathsf A$; 分支的互模拟

```agda
infix 4 _≈ᴬ_
_≈ᴬ_ : ∀ {φ ψ} → Run φ → Run ψ → Set
_≈ᴬ_ {φ} {ψ} R R′ = ∀ {i i′ ℓ ℓ′} (ev : Ev ℓ φ) (p : i <ᴵ ℓ) (ev′ : Ev ℓ′ ψ) (p′ : i′ <ᴵ ℓ′) → i ≅ᴵ i′ → R ev p ≅ᴬ R′ ev′ p′

limRᴬ : ∀ {φ ψ} {F : ℕ → Run φ} {G : ℕ → Run ψ} → (∀ n → F n ≈ᴬ G n) → limA 0 F ≈ᴬ limA 0 G
limRᴬ h ev p ev′ p′ ei = lᴬ (λ n → h n ev p ev′ p′ ei)

sucRᴬ : ∀ {φ ψ} {R : Run φ} {R′ : Run ψ} → R ≈ᴬ R′ → sucRun R ≈ᴬ sucRun R′
sucRᴬ h ev p ev′ p′ ei = lᴬ (iter-R _≅ᴬ_ (λ e′ → addˢ-≅ᴬ (kd-≅ ei) (h ev p ev′ p′ ei) e′) zᴬ)

limᵢRᴬ : ∀ {φ ψ j j′} {ac : ∀ {L} → Ev L φ → j <ᴵ L} {ac′ : ∀ {L} → Ev L ψ → j′ <ᴵ L}
         {H : Ordˢ j → Run φ} {H′ : Ordˢ j′ → Run ψ} →
         j ≅ᴵ j′ → (∀ x y → x ≅ᴬ y → H x ≈ᴬ H′ y) → limᵢA 0 ac H ≈ᴬ limᵢA 0 ac′ H′
limᵢRᴬ {ac = ac} {ac′ = ac′} {H = H} {H′ = H′} e h ev p ev′ p′ ei with <ᴵ-dec (ac ev) p | <ᴵ-dec (ac′ ev′) p′
... | injᵃ (via e₁ r₁) | injᵃ (via e₂ r₂) = lᵢᴬ (≅ᴵ-trans (≅ᴵ-sym e₁) (≅ᴵ-trans e e₂)) λ x y d →
  subst₂ (λ a b → H (tr⁻ˢ e₁ a) ev p ≅ᴬ H′ (tr⁻ˢ e₂ b) ev′ p′)
         (sym (out-intoˢ (<→◃ r₁) x)) (sym (out-intoˢ (<→◃ r₂) y))
         (h _ _ (tr⁻ˢ-≅ᴬ e₁ (≅ᴬ-tr⁻ˢ e₂ (R→≅ᴬ (<→◃ r₁) d))) ev p ev′ p′ ei)
... | injᵃ r | injᵇ s  = ⊥-elim (clash₁ e ei r s)
... | injᵃ r | injᶜ c′ = ⊥-elim (clash₂ e ei r c′)
... | injᵇ s | injᵃ r  = ⊥-elim (clash₁ (≅ᴵ-sym e) (≅ᴵ-sym ei) r s)
... | injᶜ c′ | injᵃ r = ⊥-elim (clash₂ (≅ᴵ-sym e) (≅ᴵ-sym ei) r c′)
... | injᵇ _ | injᵇ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᵇ _ | injᶜ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᵇ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)
... | injᶜ _ | injᶜ _  = lᴬ (λ m → h _ _ (iter-R _≅ᴬ_ (λ d → h _ _ d ev (ac ev) ev′ (ac′ ev′) e) (Ωˢ-≅ᴬ e) m) ev p ev′ p′ ei)

ĉRᴬ : ∀ {φ ψ c c′ t₀ t₀′} {g : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z}
      {O₀ : Run φ} {O : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {O₀′ : Run ψ} {O′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
      O₀ ≈ᴬ O₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → O η e ≈ᴬ O′ η′ e′) → ĉA 0 c t₀ g O₀ O ≈ᴬ ĉA 0 c′ t₀′ g′ O₀′ O′
ĉRᴬ ec dt dg h₀ h ev p ev′ p′ ei = ĉᴬ ec dt dg (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

ŝRᴬ : ∀ {φ ψ c c′} {T₀ : Run φ} {G : (η : Ordᴵ) → c ⊑ᴵ η → Run φ} {T₀′ : Run ψ} {G′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Run ψ} →
      c ≅ᴵ c′ → T₀ ≈ᴬ T₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → G η e ≈ᴬ G′ η′ e′) → ŝA 0 c T₀ G ≈ᴬ ŝA 0 c′ T₀′ G′
ŝRᴬ ec h₀ h ev p ev′ p′ ei = ŝᴬ (kd-≅ ei) ec (h₀ ev p ev′ p′ ei) (λ η e η′ e′ eη → h η e η′ e′ eη ev p ev′ p′ ei)

wkRᴬ : ∀ {φ φ′ ψ ψ′} {R : Run φ} {R′ : Run φ′} (le : ∀ {L} → Ev L ψ → Ev L φ) (le′ : ∀ {L} → Ev L ψ′ → Ev L φ′) →
       R ≈ᴬ R′ → wk 0 le R ≈ᴬ wk 0 le′ R′
wkRᴬ le le′ h ev p ev′ p′ ei = h (le ev) p (le′ ev′) p′ ei

cloRᴬ : ∀ {φ φ′} {t : Run (φ ⊔ fk zero)} {g : (η : Ordᴵ) → Run (φ ⊔ fk η)}
        {t′ : Run (φ′ ⊔ fk zero)} {g′ : (η : Ordᴵ) → Run (φ′ ⊔ fk η)} → φ ∼ᶠ φ′ →
        t ≈ᴬ t′ → (∀ η η′ → η ≅ᴵ η′ → g η ≈ᴬ g′ η′) → cloA 0 t g ≈ᴬ cloA 0 t′ g′
cloRᴬ {φ} {φ′} s ht hg ev p ev′ p′ ei =
  ŝᴬ (kd-≅ ei) (bound-≅ (⊔∼ s (fk∼ z≅)) ev p ev′ p′ ei) (ht ev p ev′ p′ ei)
     (λ η e η′ e′ eη → hg η η′ eη _ (lim 0 (iF (bound (φ ⊔ fk zero) ev p))) _ (lim 0 (iF (bound (φ′ ⊔ fk zero) ev′ p′))) ei)
```

```agda

flo-∼ : ∀ {k k′} → k ≅ᴵ k′ → flo k ∼ᶠ flo k′
flo-∼ z≅     = fz∼
flo-∼ (s≅ e) = fk∼ e
flo-∼ (l≅ h) = fb∼ (l≅ h)
```

```agda
∅ᴿ-ᴬ : ∅ᴿ ≈ᴬ ∅ᴿ
∅ᴿ-ᴬ ev p ev′ p′ ei = Ωˢ-≅ᴬ ei
```

## §5 层对齐的好性与目标类型

```agda
record GRᴬ {φ} (R : Run φ) (u : T) : Set where
  constructor grᴬ
  field
    gWᴬ : LW R u
    g0ᴬ : L0 R u
    gRᴬ : R ≈ᴬ R

GA0ᴬ : ∀ {fl} → Run fl → T → Set
GA0ᴬ {fl} P π = FlrLab fl π × GRᴬ P π

∅ᴿ-good : GA0ᴬ ∅ᴿ []
∅ᴿ-good = FlrLab-fz , grᴬ (gW (proj₂ good∅ᴿ)) (g0 (proj₂ good∅ᴿ)) ∅ᴿ-ᴬ

```

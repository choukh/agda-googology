# Lemma 4.23：突出集的封闭性

Setzer [Se98] Lemma 4.23。设 `Ag(A)`。

- (a) A 向下封闭、向上封闭以 A 为界：对 x ∈ A 取 κ := x̃，`A ∩ x̃ ≅ W(A) ∩ x̃`，Lemma 4.17 (b) 给 `W(A) ∩ x̃⁺` 的封闭性，而 x ≺ x̃⁺，再由段性质落回 A。向上封闭时把 x、y、界 c 用一个公共的 m ∈ A 盖住（三分取 max），全部落在 W(A) ∩ m̃⁺ 里。
- (b) κ, c ∈ A，κ ∈ R，ψ_κ c ∈ OT ⟹ ψ_κ c ∈ A：Lemma 4.17 (c) 在 θ := (max{κ,c})~ 处。
- (c) `Ag(A⁺)`：见 [Lemma423c](Lemma423c.lagda.md)。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Lemma423 (F : OTFacts) where

open OTFacts F

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Order
open import Mahlo.Inacc.Closure
open import Mahlo.Inacc.Arith
open import Mahlo.Inacc.BoolLemmas
open import Mahlo.Inacc.OTLemmas
open import Mahlo.Inacc.WO.K
open import Mahlo.Inacc.WO.Base
open import Mahlo.Inacc.WO.CLemmas
open import Mahlo.Inacc.WO.OrderLemmas F
open import Mahlo.Inacc.WO.Lemma47 F
open import Mahlo.Inacc.WO.Lemma413 F
open import Mahlo.Inacc.WO.Dist F
open import Mahlo.Inacc.WO.Closed F
open import Mahlo.Inacc.WO.Closed2 F
open import Mahlo.Inacc.WO.Lemma417b F
open import Mahlo.Inacc.WO.Lemma417c F

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

private variable
  ℓ : Level

module Ag423 {A : Pred ℓ} (ag : Ag A) where

  oA : A ⊆ OT
  oA = proj₁ ag

  A⊆W : A ⊆ 𝒲 A
  A⊆W = Ag⇒A⊆𝒲 ag

  h : A ⊆ M A
  h p = 𝒲-M (A⊆W p)

  seg : ∀ {x} → A x → (A ∣ x) ≅ (𝒲 A ∣ x)
  seg = proj₂ (proj₂ ag)

  -- W(A) 在 x ∈ A 以下落回 A
  W→A : ∀ {x z} → A x → 𝒲 A z → z ⪯ x → A z
  W→A ax wz z⪯x = proj₁ (proj₂ (seg ax) (wz , z⪯x))

  -- A ∩ x̃ ≅ W(A) ∩ x̃（x ∈ A）
  Ex̃ : ∀ {x} → A x → (A ∩ ↓ (tilde x)) ≅ (𝒲 A ∩ ↓ (tilde x))
  Ex̃ ax = (λ (az , oz , z≺x̃) → A⊆W az , oz , z≺x̃)
        , (λ (wz , oz , z≺x̃) → W→A ax wz (≺⇒⪯ (≺⪯-trans z≺x̃ (tilde⪯ (oA ax)))) , oz , z≺x̃)

  -- 在 x ∈ A 处实例化 Lemma 4.17 (b)
  module At {x : Tm} (ax : A x) = L417b h (tilde-OT (oA ax)) (Ex̃ ax)

  -- x ∈ W(A) ∩ x̃⁺
  x∈W⁺ : ∀ {x} → A x → (𝒲 A ∩ ↓ (plus (tilde x))) x
  x∈W⁺ ax = A⊆W ax , oA ax , x≺plus-tilde (oA ax)

  -- z ⪯ x ∈ A 且 z ∈ W(A) ∩ x̃⁺ ⟹ z ∈ A
  back : ∀ {x z} → A x → (𝒲 A ∩ ↓ (plus (tilde x))) z → z ⪯ x → A z
  back ax (wz , _ , _) z⪯x = W→A ax wz z⪯x

  0∈A : ∀ {x} → A x → A zer
  0∈A ax = W→A ax 0∈𝒲 (0⪯ _)
```

## (a) 向下封闭

```agda
  Ag-WDC : WDC A
  Ag-WDC = record
    { wdc-+ = λ nz o ax →
        let (l , r) = wdc-+ (wdc (At.W⁺-DC ax)) nz o (x∈W⁺ ax)
        in back ax l (≺⇒⪯ (≺-+ˡ nz o)) , back ax r (≺⇒⪯ (≺-+ʳ nz o))
    ; wdc-φ = λ o ax →
        let (l , r) = wdc-φ (wdc (At.W⁺-DC ax)) o (x∈W⁺ ax)
        in back ax l (≺⇒⪯ (≺-φˡ o)) , back ax r (≺⇒⪯ (≺-φʳ o))
    ; wdc-Ω = λ o ax → back ax (wdc-Ω (wdc (At.W⁺-DC ax)) o (x∈W⁺ ax)) (≺⇒⪯ (≺-Ω o))
    ; wdc-ψ = λ o ax → back ax (wdc-ψ (wdc (At.W⁺-DC ax)) o (x∈W⁺ ax)) (κ⁻⪯ψ o)
    }

  Ag-DC : DC A
  Ag-DC = record
    { wdc = Ag-WDC
    ; dc-split = λ nzy nzz o ax →
        let (l , r) = dc-split (At.W⁺-DC ax) nzy nzz o (x∈W⁺ ax)
        in back ax l (⪯-prefix nzz o) , back ax r (⪯-app nzy nzz o)
    ; dc-tilde = λ ox ax → back ax (dc-tilde (At.W⁺-DC ax) ox (x∈W⁺ ax)) (tilde⪯ ox)
    ; dc-mFi   = λ ox ax → back ax (dc-mFi (At.W⁺-DC ax) ox (x∈W⁺ ax)) (mFi⪯ ox)
    ; dc-mI    = λ ox ax → back ax (dc-mI (At.W⁺-DC ax) ox (x∈W⁺ ax)) (mI⪯ ox)
    ; dc-κ⁻    = λ rκ oκ aκ → back aκ (dc-κ⁻ (At.W⁺-DC aκ) rκ oκ (x∈W⁺ aκ)) (≺⇒⪯ (κ⁻≺κ rκ oκ))
    }
```

## (a) 向上封闭，以 A 为界

```agda
  -- 三个元素的公共上界（三分）
  max2 : ∀ {x y} → A x → A y → ∃ λ m → A m × x ⪯ m × y ⪯ m
  max2 {x} {y} ax ay with ⪯-total x y
  ... | inj₁ x⪯y = y , ay , x⪯y , ⪯-refl
  ... | inj₂ y⪯x = x , ax , ⪯-refl , y⪯x

  max3 : ∀ {x y c} → A x → A y → A c → ∃ λ m → A m × x ⪯ m × y ⪯ m × c ⪯ m
  max3 ax ay ac =
    let (m , am , x⪯m , y⪯m) = max2 ax ay
        (n , an , m⪯n , c⪯n) = max2 am ac
    in n , an , ⪯-trans x⪯m m⪯n , ⪯-trans y⪯m m⪯n , c⪯n

  -- 元素 x ⪯ m ∈ A 落在 W(A) ∩ m̃⁺
  in⁺ : ∀ {m x} → A m → A x → x ⪯ m → (𝒲 A ∩ ↓ (plus (tilde m))) x
  in⁺ am ax x⪯m = A⊆W ax , oA ax , ⪯≺-trans x⪯m (x≺plus-tilde (oA am))

  -- 守卫 z ≺ c ∈ A ⟹ z ≺ m̃⁺（c ⪯ m）
  guard : ∀ {m z c} → A m → A c → c ⪯ m → z ≺ c → z ≺ plus (tilde m)
  guard am ac c⪯m z≺c = ≺-trans z≺c (⪯≺-trans c⪯m (x≺plus-tilde (oA am)))

  Ag-WUC : WUC A (_≺C A)
  Ag-WUC = record
    { wuc-+ = λ {b} {p} nz o (c , ac , z≺c) ab ap →
        let (m , am , b⪯m , p⪯m , c⪯m) = max3 ab ap ac
        in back am (wuc-+ (wuc (At.W⁺-UC am)) nz o (guard am ac c⪯m z≺c) (in⁺ am ab b⪯m) (in⁺ am ap p⪯m))
                   (≺⇒⪯ (≺⪯-trans z≺c c⪯m))
    ; wuc-φ = λ o (c , ac , z≺c) ab ad →
        let (m , am , b⪯m , d⪯m , c⪯m) = max3 ab ad ac
        in back am (wuc-φ (wuc (At.W⁺-UC am)) o (guard am ac c⪯m z≺c) (in⁺ am ab b⪯m) (in⁺ am ad d⪯m))
                   (≺⇒⪯ (≺⪯-trans z≺c c⪯m))
    ; wuc-Ω = λ o (c , ac , z≺c) ab →
        let (m , am , b⪯m , c⪯m) = max2 ab ac
        in back am (wuc-Ω (wuc (At.W⁺-UC am)) o (guard am ac c⪯m z≺c) (in⁺ am ab b⪯m)) (≺⇒⪯ (≺⪯-trans z≺c c⪯m))
    ; wuc-0 = λ (c , ac , _) → 0∈A ac
    ; wuc-I = λ (c , ac , I≺c) → back ac (wuc-I (wuc (At.W⁺-UC ac)) (guard ac ac ⪯-refl I≺c)) (≺⇒⪯ I≺c)
    }

  Ag-UC : UC A (_≺C A)
  Ag-UC = record
    { wuc = Ag-WUC
    ; uc-app = λ {y} {z} nzz o (c , ac , w≺c) ay az →
        let (m , am , y⪯m , z⪯m , c⪯m) = max3 ay az ac
        in back am (uc-app (At.W⁺-UC am) nzz o (guard am ac c⪯m w≺c) (in⁺ am ay y⪯m) (in⁺ am az z⪯m))
                   (≺⇒⪯ (≺⪯-trans w≺c c⪯m))
    ; uc-+ = λ ox oy o (c , ac , w≺c) ax ay →
        let (m , am , x⪯m , y⪯m , c⪯m) = max3 ax ay ac
        in back am (uc-+ (At.W⁺-UC am) ox oy o (guard am ac c⪯m w≺c) (in⁺ am ax x⪯m) (in⁺ am ay y⪯m))
                   (≺⇒⪯ (≺⪯-trans w≺c c⪯m))
    ; uc-φ = λ ox oy o (c , ac , w≺c) ax ay →
        let (m , am , x⪯m , y⪯m , c⪯m) = max3 ax ay ac
        in back am (uc-φ (At.W⁺-UC am) ox oy o (guard am ac c⪯m w≺c) (in⁺ am ax x⪯m) (in⁺ am ay y⪯m))
                   (≺⇒⪯ (≺⪯-trans w≺c c⪯m))
    ; uc-Ω = λ ox o (c , ac , w≺c) ax →
        let (m , am , x⪯m , c⪯m) = max2 ax ac
        in back am (uc-Ω (At.W⁺-UC am) ox o (guard am ac c⪯m w≺c) (in⁺ am ax x⪯m)) (≺⇒⪯ (≺⪯-trans w≺c c⪯m))
    ; uc-plus = λ ox o (c , ac , w≺c) ax →
        let (m , am , x⪯m , c⪯m) = max2 ax ac
        in back am (uc-plus (At.W⁺-UC am) ox o (guard am ac c⪯m w≺c) (in⁺ am ax x⪯m)) (≺⇒⪯ (≺⪯-trans w≺c c⪯m))
    }
```

## (b) 对 ψ 封闭

```agda
  -- κ 的侧条件（κ = I，或 κ⁻ ∈ W(A)|θ）
  ksOf : ∀ {θ} (oθ : OT θ) (cθ : isCarT θ ≡ true) (wθ : 𝒲 A θ) (E : (𝒲 A ∩ ↓ θ) ≅ (A ∩ ↓ θ))
       → ∀ κ → isRR κ ≡ true → A (regTm κ) → regTm κ ⪯ θ → L417c.KSide h oθ cθ wθ E κ
  ksOf oθ cθ wθ E IR     _ _ _   = inj₁ refl
  ksOf oθ cθ wθ E (ΩR w) r a k⪯θ =
    inj₂ (A⊆W (dc-κ⁻ Ag-DC r (oA a) a) , ≺⇒⪯ (≺⪯-trans (κ⁻≺κ r (oA a)) k⪯θ))

  Ag-ψ : ∀ {κ c} → A (regTm κ) → A c → OT ⟨ psi κ c ⟩ → A ⟨ psi κ c ⟩
  Ag-ψ {κ} {c} aκ ac o = W→A aθ wψ (≺⇒⪯ ψ≺θ)
    where
      oκ : OT (regTm κ)
      oκ = oA aκ
      rκ : isRR κ ≡ true
      rκ = proj₁ (proj₂ (proj₂ (OT-ψ⁻ o)))
      -- z := max{κ, c}，θ := z̃
      mz = max2 aκ ac
      z = proj₁ mz
      az : A z
      az = proj₁ (proj₂ mz)
      κ⪯z : regTm κ ⪯ z
      κ⪯z = proj₁ (proj₂ (proj₂ mz))
      c⪯z : c ⪯ z
      c⪯z = proj₂ (proj₂ (proj₂ mz))
      θ = tilde z
      oθ : OT θ
      oθ = tilde-OT (oA az)
      aθ : A θ
      aθ = dc-tilde Ag-DC (oA az) az
      κ⪯θ : regTm κ ⪯ θ
      κ⪯θ = tilde-max (oA az) oκ (Car-reg κ) κ⪯z
      cθ : isCarT θ ≡ true
      cθ with tilde-Car (oA az)
      ... | inj₁ ca = ca
      ... | inj₂ e0 = ⊥-elim (≺⇒¬⪯ (0≺reg κ) (subst (λ t → regTm κ ⪯ t) e0 κ⪯θ))
      E : (𝒲 A ∩ ↓ θ) ≅ (A ∩ ↓ θ)
      E = (λ (wz , oz , z≺θ) → W→A aθ wz (≺⇒⪯ z≺θ) , oz , z≺θ)
        , (λ (az′ , oz , z≺θ) → A⊆W az′ , oz , z≺θ)
      ks : L417c.KSide h oθ cθ (A⊆W aθ) E κ
      ks = ksOf oθ cθ (A⊆W aθ) E κ rκ aκ κ⪯θ
      ψ≺θ : ⟨ psi κ c ⟩ ≺ θ
      ψ≺θ = ≺⪯-trans (ψ≺κ o) κ⪯θ
      wψ : 𝒲 A ⟨ psi κ c ⟩
      wψ = L417c.L4-17c h oθ cθ (A⊆W aθ) E (A⊆W ac)
             (⪯≺-trans c⪯z (x≺plus-tilde (oA az))) κ ks o
             (≺-trans ψ≺θ (≺plus oθ))
```

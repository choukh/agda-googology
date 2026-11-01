# Lemma 4.23 (c)：A⁺ 是突出集

Setzer [Se98] Lemma 4.23 (c)：`Ag(A) ⟹ Ag(A⁺) ∧ A ⊆ A⁺ ∧ ∀x ∈ A. x⁺ ∈ A⁺`，其中 `A⁺ := ⋃_{z ∈ A} ((W(A) ∩ z⁺) ∪ {z⁺})`。

对 x ∈ A：(i) `A⁺ ∩ x ⊆ A`；(ii) `A⁺ ∩ x⁺ ≅ W(A) ∩ x⁺`（z⁺ ≺ x⁺ 时 z⁺ ∈ W(A) 由 W(A) ∩ x̃⁺ 的向上封闭）；`A⁺ ⊆ M(A⁺)`（z⁺ = Ω′_{w+1} 用 w ∈ A ⊆ A⁺ ∩ z⁺ 搭出）；(iii) `W(A) ∩ x⁺ ≅ W(A⁺) ∩ x⁺`（Lemma 4.13 (b)，A 与 A⁺ 在 x̃ 以下一致）；(iv) `x⁺ ∈ W(A⁺)`（Lemma 4.17 (b) 对 A⁺ 在 κ := x⁺，`uc-plus` 于 x̃）。于是 `A⁺|x⁺ ≅ W(A⁺)|x⁺`，对 A⁺ 的每个元素 y（y ⪯ 某 x⁺）限制即得 `A⁺ ⊑ W(A⁺)`。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Lemma423c (F : OTFacts) where

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
open import Mahlo.Inacc.WO.Lemma423 F

open import Level using (Level; _⊔_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

private variable
  ℓ : Level

module Ag423c {A : Pred ℓ} (ag : Ag A) where

  open Ag423 ag

  A⁺ : Pred ℓ
  A⁺ = A ⁺

  A⊆A⁺ : A ⊆ A⁺
  A⊆A⁺ {x} ax = x , ax , inj₁ (A⊆W ax , ≺plus (oA ax))

  A⁺⊆OT : A⁺ ⊆ OT
  A⁺⊆OT (z , az , inj₁ (w , _)) = 𝒲⊆OT w
  A⁺⊆OT (z , az , inj₂ refl)    = plus-OT (oA az)

  plus∈A⁺ : ∀ {x} → A x → A⁺ (plus x)
  plus∈A⁺ {x} ax = x , ax , inj₂ refl

  -- (i) A⁺ ∩ x ⊆ A（x ∈ A）
  A⁺∩x⊆A : ∀ {x} → A x → (A⁺ ∩ ↓ x) ⊆ A
  A⁺∩x⊆A ax ((z , az , inj₁ (wy , _)) , _ , y≺x) = W→A ax wy (≺⇒⪯ y≺x)
  A⁺∩x⊆A {x} ax ((z , az , inj₂ refl) , _ , z⁺≺x) =
    back ax (uc-plus (At.W⁺-UC ax) (oA az) (plus-OT (oA az)) (≺-trans z⁺≺x (x≺plus-tilde (oA ax)))
                     (in⁺ ax az (≺⇒⪯ (≺-trans (≺plus (oA az)) z⁺≺x))))
            (≺⇒⪯ z⁺≺x)

  -- (ii) A⁺ ∩ x⁺ ≅ W(A) ∩ x⁺（x ∈ A）：z⁺ ≺ x⁺ 时 z ≺ z⁺ ≺ x⁺ = x̃⁺，向上封闭给 z⁺ ∈ W(A)
  ii⊆ : ∀ {x} → A x → (A⁺ ∩ ↓ (plus x)) ⊆ (𝒲 A ∩ ↓ (plus x))
  ii⊆ ax ((z , az , inj₁ (wy , _)) , oy , y≺x⁺) = wy , oy , y≺x⁺
  ii⊆ {x} ax ((z , az , inj₂ refl) , oy , z⁺≺x⁺) =
    proj₁ (uc-plus (At.W⁺-UC ax) (oA az) (plus-OT (oA az)) g (A⊆W az , oA az , ≺-trans (≺plus (oA az)) g))
    , oy , z⁺≺x⁺
    where
      g : plus z ≺ plus (tilde x)
      g = subst (λ t → plus z ≺ t) (sym (tilde-plus (oA ax))) z⁺≺x⁺

  ii⊇ : ∀ {x} → A x → (𝒲 A ∩ ↓ (plus x)) ⊆ (A⁺ ∩ ↓ (plus x))
  ii⊇ {x} ax (wy , oy , y≺x⁺) = (x , ax , inj₁ (wy , y≺x⁺)) , oy , y≺x⁺

  -- A⁺ ⊆ M(A⁺)：z⁺ = Ω′_{w+1}，Ω_w = z̃ ∈ A，w ∈ A ⊆ A⁺ ∩ z⁺ ⊆ C^{z⁺}(A⁺)
  A⁺⊆M : A⁺ ⊆ M A⁺
  A⁺⊆M (z , az , inj₁ (wy , _)) = C-mono (λ _ → A⊆A⁺) (𝒲-M wy)
  A⁺⊆M (z , az , inj₂ refl)     = fromForm (plus-form (oA az))
    where
      oz⁺ : OT (plus z)
      oz⁺ = plus-OT (oA az)
      c0 : C (plus z) A⁺ zer
      c0 = c! OT-0 (here [])
      c1 : C (plus z) A⁺ one
      c1 = C-φ⁺ OT-one c0 c0
      mk : ∀ w → OT (w ▹ phi zer zer) → C (plus z) A⁺ w → C (plus z) A⁺ (w ▹ phi zer zer)
      mk zer      _  _  = c1
      mk (w ▹ r)  ow cw = C-+⁺ tt ow cw c1
      fromForm : (∃ λ w → plus z ≡ ⟨ Om (w ▹ phi zer zer) ⟩ × Ω w ≡ tilde z) → M A⁺ (plus z)
      fromForm (w , e , eΩ) =
        subst (λ t → C (plus z) A⁺ t) (sym e) (C-Ω⁺ (subst OT e oz⁺) (mk w ow1 cw))
        where
          ow1 : OT (w ▹ phi zer zer)
          ow1 = proj₁ (OT-Ω⁻ (subst OT e oz⁺))
          ow : OT w
          ow = proj₁ (OT-▹⁻ᵃ ow1)
          az̃ : A (tilde z)
          az̃ = dc-tilde Ag-DC (oA az) az
          -- w ∈ A，w ⪯ Ω_w
          aw-w⪯ : A w × w ⪯ Ω w
          aw-w⪯ with Ω-view w
          ... | Ω-0 e0 eZ  = subst A (sym (isZero-sound e0)) (0∈A az)
                             , subst (λ t → w ⪯ t) (sym eZ) (subst (λ t → t ⪯ zer) (sym (isZero-sound e0)) ⪯-refl)
          ... | Ω-Fi _ eF  = subst A (trans (sym eΩ) eF) az̃ , ≡⇒⪯ (sym eF)
          ... | Ω-Om e₀ e₁ eO =
            let oΩw : OT ⟨ Om w ⟩
                oΩw = OT-Ω⁺ ow e₁ e₀
            in wdc-Ω Ag-WDC oΩw (subst A (trans (sym eΩ) eO) az̃) , subst (λ t → w ⪯ t) (sym eO) (≺⇒⪯ (≺-Ω oΩw))
          w≺z⁺ : w ≺ plus z
          w≺z⁺ = ⪯≺-trans (⪯-trans (proj₂ aw-w⪯) (⪯-trans (≡⇒⪯ eΩ) (tilde⪯ (oA az)))) (≺plus (oA az))
          cw : C (plus z) A⁺ w
          cw = A∩a⊆C (A⊆A⁺ (proj₁ aw-w⪯) , ow , w≺z⁺)

  -- (iii) W(A) ∩ x⁺ ≅ W(A⁺) ∩ x⁺（Lemma 4.13 (b)，A 与 A⁺ 在 x̃ 以下一致）
  private
    f→ : ∀ {x} → A x → ∀ {x′} → x′ ≺ tilde x → A x′ → A⁺ x′
    f→ ax _ = A⊆A⁺
    g← : ∀ {x} → A x → ∀ {x′} → x′ ≺ tilde x → A⁺ x′ → A x′
    g← ax q a⁺ = A⁺∩x⊆A ax (a⁺ , A⁺⊆OT a⁺ , ≺⪯-trans q (tilde⪯ (oA ax)))
    y≺x̃⁺ : ∀ {x y} → OT x → y ≺ plus x → y ≺ plus (tilde x)
    y≺x̃⁺ {x} {y} ox q = subst (λ t → y ≺ t) (sym (tilde-plus ox)) q

  iii→ : ∀ {x} → A x → ∀ {y} → y ≺ plus x → 𝒲 A y → 𝒲 A⁺ y
  iii→ ax q wy = 𝒲-cong-plus h A⁺⊆M (tilde-OT (oA ax)) (f→ ax) (g← ax) (y≺x̃⁺ (oA ax) q) wy

  iii← : ∀ {x} → A x → ∀ {y} → y ≺ plus x → 𝒲 A⁺ y → 𝒲 A y
  iii← ax q w⁺ = 𝒲-cong-plus A⁺⊆M h (tilde-OT (oA ax)) (g← ax) (f→ ax) (y≺x̃⁺ (oA ax) q) w⁺

  E⁺ : ∀ {x} → A x → (A⁺ ∩ ↓ (plus x)) ≅ (𝒲 A⁺ ∩ ↓ (plus x))
  E⁺ ax = (λ p → iii→ ax (proj₂ (proj₂ p)) (proj₁ (ii⊆ ax p)) , proj₁ (proj₂ p) , proj₂ (proj₂ p))
        , (λ (w⁺ , oy , y≺x⁺) → ii⊇ ax (iii← ax y≺x⁺ w⁺ , oy , y≺x⁺))

  -- (iv) x⁺ ∈ W(A⁺)：Lemma 4.17 (b) 对 A⁺ 在 κ := x⁺，uc-plus 于 x̃
  module At⁺ {x : Tm} (ax : A x) = L417b A⁺⊆M (plus-OT (oA ax)) (E⁺ ax)

  x⁺∈W⁺ : ∀ {x} → A x → 𝒲 A⁺ (plus x)
  x⁺∈W⁺ {x} ax =
    subst (𝒲 A⁺) (tilde-plus ox)
      (proj₁ (uc-plus (At⁺.W⁺-UC ax) (tilde-OT ox) (plus-OT (tilde-OT ox)) g wx̃))
    where
      ox : OT x
      ox = oA ax
      x̃≺x⁺ : tilde x ≺ plus x
      x̃≺x⁺ = ⪯≺-trans (tilde⪯ ox) (≺plus ox)
      wx̃ : (𝒲 A⁺ ∩ ↓ (plus (plus x))) (tilde x)
      wx̃ = iii→ ax x̃≺x⁺ (A⊆W (dc-tilde Ag-DC ox ax)) , tilde-OT ox , ≺-trans x̃≺x⁺ (≺plus (plus-OT ox))
      g : plus (tilde x) ≺ plus (plus x)
      g = subst (λ t → t ≺ plus (plus x)) (sym (tilde-plus ox)) (≺plus (plus-OT ox))

  -- Ag(A⁺)
  Ag⁺ : Ag A⁺
  Ag⁺ = A⁺⊆OT , A⁺⊆OT , seg⁺
    where
      -- x ∈ A：A⁺ 与 W(A⁺) 在 ⪯ x⁺ 处一致
      at : ∀ {x} → A x → ∀ {y′} → y′ ⪯ plus x → (A⁺ y′ → 𝒲 A⁺ y′) × (𝒲 A⁺ y′ → A⁺ y′)
      at ax y′⪯x⁺ with ⪯⇒≺⊎≡ y′⪯x⁺
      ... | inj₂ refl  = (λ _ → x⁺∈W⁺ ax) , (λ _ → plus∈A⁺ ax)
      ... | inj₁ y′≺x⁺ =
        (λ a⁺ → iii→ ax y′≺x⁺ (proj₁ (ii⊆ ax (a⁺ , A⁺⊆OT a⁺ , y′≺x⁺))))
        , (λ w⁺ → proj₁ (ii⊇ ax (iii← ax y′≺x⁺ w⁺ , 𝒲⊆OT w⁺ , y′≺x⁺)))
      wit : ∀ {y} → A⁺ y → ∃ λ x → A x × y ⪯ plus x
      wit (z , az , inj₁ (_ , y≺z⁺)) = z , az , ≺⇒⪯ y≺z⁺
      wit (z , az , inj₂ refl)       = z , az , ⪯-refl
      seg⁺ : ∀ {y} → A⁺ y → (A⁺ ∣ y) ≅ (𝒲 A⁺ ∣ y)
      seg⁺ a⁺ with wit a⁺
      ... | x , ax , y⪯x⁺ =
        (λ (a′ , y′⪯y) → proj₁ (at ax (⪯-trans y′⪯y y⪯x⁺)) a′ , y′⪯y)
        , (λ (w′ , y′⪯y) → proj₂ (at ax (⪯-trans y′⪯y y⪯x⁺)) w′ , y′⪯y)
```

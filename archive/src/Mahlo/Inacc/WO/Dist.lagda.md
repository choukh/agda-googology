# 突出集：Lemma 4.21、4.24 与段的代数

Setzer [Se98] §4.4。`Ag(A) := A ⊆ OT ∧ A ⊑ W(A)`。

- 4.21 (a) `Ag(A) ⟹ Prog(A, B) → A ⊆ B`：**突出集上的归纳原理**（Notation 4.22）。
- 4.21 (b) `Ag(A) ⟹ A ∩ Ω₁ ⊑ OT`。
- 4.21 (c) `Ag(A) ⟹ Prog(B) → A ∩ Ω₁ ⊆ B`：可数部分是通常意义的良序。
- 4.24 突出集的唯一性：`Aᵢ ≅ W(Aᵢ) ∩ aᵢ`，`a₀ ⪯ a₁` ⟹ `A₀ ≅ A₁ ∩ a₀`。

4.23 依赖 4.17，另放。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import Mahlo.Inacc.WO.Facts

module Mahlo.Inacc.WO.Dist (F : OTFacts) where

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

open import Level using (Level; _⊔_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  ℓ ℓ′ ℓ″ : Level
  A B : Pred ℓ
```

## 1. 段的代数

```agda
⊑-trans : ∀ {C : Pred ℓ″} → A ⊑ B → B ⊑ C → A ⊑ C
⊑-trans {A = A} {B = B} {C = C} (oA , sAB) (oB , sBC) = oA , seg
  where
    seg : ∀ {x} → A x → (A ∣ x) ≅ (C ∣ x)
    seg {x} p = ≅-trans (sAB p) (sBC (proj₁ (proj₁ (sAB p) (p , ⪯-refl))))

⊑⇒⊆ : A ⊑ B → A ⊆ B
⊑⇒⊆ (_ , s) p = proj₁ (proj₁ (s p) (p , ⪯-refl))

-- 段的两个方向：a ∈ A，z ⪯ a
⊑→ : A ⊑ B → ∀ {a z} → A a → A z → z ⪯ a → B z
⊑→ (_ , s) p q t = proj₁ (proj₁ (s p) (q , t))

⊑← : A ⊑ B → ∀ {a z} → A a → B z → z ⪯ a → A z
⊑← (_ , s) p w t = proj₁ (proj₂ (s p) (w , t))

-- 段与「∩ a」相容
⊑-∩ : ∀ {a} → A ⊑ B → (A ∩ ↓ a) ⊑ (B ∩ ↓ a)
⊑-∩ {A = A} {B = B} {a} (oA , s) = (λ (p , _) → oA p) , seg
  where
    seg : ∀ {x} → (A ∩ ↓ a) x → ((A ∩ ↓ a) ∣ x) ≅ ((B ∩ ↓ a) ∣ x)
    seg (p , _) = (λ ((q , r) , t) → (proj₁ (proj₁ (s p) (q , t)) , r) , t)
                , (λ ((q , r) , t) → (proj₁ (proj₂ (s p) (q , t)) , r) , t)

-- 从 A ≅ W(A) ∩ a 得 Ag(A) 与 A ⊆ M(A)
≅𝒲∩⇒Ag : ∀ {a} → A ≅ (𝒲 A ∩ ↓ a) → Ag A
≅𝒲∩⇒Ag {A = A} {a} (f , g) = oA , oA , seg
  where
    oA : A ⊆ OT
    oA p = 𝒲⊆OT (proj₁ (f p))
    seg : ∀ {x} → A x → (A ∣ x) ≅ (𝒲 A ∣ x)
    seg {x} p = (λ (q , t) → proj₁ (f q) , t)
              , (λ (w , t) → g (w , 𝒲⊆OT w , ⪯≺-trans t (proj₂ (proj₂ (f p)))) , t)

≅𝒲∩⇒⊆M : ∀ {a} → A ≅ (𝒲 A ∩ ↓ a) → A ⊆ M A
≅𝒲∩⇒⊆M (f , _) p = 𝒲-M (proj₁ (f p))
```

## 2. Lemma 4.21

(a)：令 `C := {y ∈ OT | y ∈ A → y ∈ B}`，证 `𝒜^A(C) ∩ W(A) ⊆ C`：y ∈ A 时 `τ^A(y) ≅ A ∩ y`（Remark 4.20）⊆ C，故 `A ∩ y ⊆ B`，由 Prog 得 y ∈ B。于是 `W(A) ⊆ C`，而 `A ⊆ W(A)`。

```agda
Ag-ind : Ag A → Prog A B → A ⊆ B
Ag-ind {A = A} {B = B} ag prog {x} p = proj₂ (𝒲-ind {B = C′} step (Ag⇒A⊆𝒲 ag p)) p
  where
    C′ : Pred _
    C′ y = OT y × (A y → B y)
    step : (𝒜 A C′ ∩ 𝒲 A) ⊆ C′
    step ((m , τ⊆C) , w) =
      M⊆OT m , λ y∈A → prog y∈A (λ (z∈A , oz , z≺y) → proj₂ (τ⊆C (Rem4-20⊇ (z∈A , oz , z≺y))) z∈A)

-- (b)
Ag-Ω₁⊑OT : Ag A → (A ∩ ↓ Ω₁) ⊑ OT
Ag-Ω₁⊑OT ag = ⊑-trans (⊑-∩ (proj₂ ag)) 𝒲∩Ω₁⊑OT

-- (c)：对 B′ := {y | y ≺ Ω₁ → y ∈ B} 用 (a)；Prog(A, B′) 由 Prog(Ω₁, B) 与 (b) 得
Ag-Prog₁ : Ag A → Prog₁ B → (A ∩ ↓ Ω₁) ⊆ B
Ag-Prog₁ {A = A} {B = B} ag prog (p , ox , x≺Ω₁) = Ag-ind ag prog′ p (ox , x≺Ω₁)
  where
    prog′ : Prog A (λ y → ↓ Ω₁ y → B y)
    prog′ {x = y} y∈A ih (oy , y≺Ω₁) =
      prog (oy , y≺Ω₁) λ {z} ((oz , z≺Ω₁) , (_ , z≺y)) →
        ih (proj₁ (proj₁ (proj₂ (proj₂ (Ag-Ω₁⊑OT ag) (y∈A , oy , y≺Ω₁)) (oz , ≺⇒⪯ z≺y)))
            , oz , z≺y)
           (oz , z≺Ω₁)
```

## 3. Lemma 4.24：突出集的唯一性

`A₀ ≅ W(A₀) ∩ D₀`，`A₁ ≅ W(A₁) ∩ D₁`，D₀ ⊆ D₁ 都是向下封闭的「截段」 ⟹ `A₀ ≅ A₁ ∩ D₀`。原文 D 是 `≺ a`，先 WLOG a₀ = a₁；这里截段一般化（`≺ a` 与 `⪯ b` 两种都要用），且直接做。要点：A₀ 与 A₁ 在 z 以下一致 ⟹ W(A₀)、W(A₁) 在 ⪯ z 处一致（Lemma 4.13 (b)）。

```agda
Cut : ∀ {ℓ} → Pred ℓ → Set ℓ
Cut D = ∀ {w z} → w ⪯ z → D z → D w

module _ {A₀ : Pred ℓ} {A₁ : Pred ℓ′} {D₀ D₁ : Pred ℓ″}
         (mono₀ : Cut D₀) (mono₁ : Cut D₁) (D₀⊆D₁ : D₀ ⊆ D₁)
         (E₀ : A₀ ≅ (𝒲 A₀ ∩ D₀)) (E₁ : A₁ ≅ (𝒲 A₁ ∩ D₁)) where

  private
    mkAg : ∀ {ℓa ℓd} {A : Pred ℓa} {D : Pred ℓd} → Cut D → A ≅ (𝒲 A ∩ D) → Ag A
    mkAg mono E = (λ p → 𝒲⊆OT (proj₁ (proj₁ E p)))
                , (λ p → 𝒲⊆OT (proj₁ (proj₁ E p)))
                , (λ p → (λ (q , t) → proj₁ (proj₁ E q) , t)
                       , (λ (w , t) → proj₂ E (w , mono t (proj₂ (proj₁ E p))) , t))
    ag₀ : Ag A₀
    ag₀ = mkAg mono₀ E₀
    ag₁ : Ag A₁
    ag₁ = mkAg mono₁ E₁
    h₀ : A₀ ⊆ M A₀
    h₀ p = 𝒲-M (proj₁ (proj₁ E₀ p))
    h₁ : A₁ ⊆ M A₁
    h₁ p = 𝒲-M (proj₁ (proj₁ E₁ p))
    d₀ : ∀ {y} → A₀ y → D₀ y
    d₀ p = proj₂ (proj₁ E₀ p)

  -- 在 z 以下一致 ⟹ W 在 ⪯ z 处一致
  agree⇒𝒲₀₁ : ∀ {z} → OT z → (A₀ ∩ ↓ z) ⊆ A₁ → (A₁ ∩ ↓ z) ⊆ A₀
             → ∀ {w} → w ⪯ z → 𝒲 A₀ w → 𝒲 A₁ w
  agree⇒𝒲₀₁ oz f g =
    𝒲-cong-⪯ h₀ h₁ oz (λ q p → f (p , proj₁ ag₀ p , q)) (λ q p → g (p , proj₁ ag₁ p , q))

  agree⇒𝒲₁₀ : ∀ {z} → OT z → (A₀ ∩ ↓ z) ⊆ A₁ → (A₁ ∩ ↓ z) ⊆ A₀
             → ∀ {w} → w ⪯ z → 𝒲 A₁ w → 𝒲 A₀ w
  agree⇒𝒲₁₀ oz f g =
    𝒲-cong-⪯ h₁ h₀ oz (λ q p → g (p , proj₁ ag₁ p , q)) (λ q p → f (p , proj₁ ag₀ p , q))

  L4-24⊆ : A₀ ⊆ (A₁ ∩ D₀)
  L4-24⊆ {x = y} p = Ag-ind ag₀ main p , d₀ p
    where
      main : Prog A₀ A₁
      main {x = y} y∈A₀ ih = proj₂ E₁ (𝒲y∈A₁ , D₀⊆D₁ (d₀ y∈A₀))
        where
          oy : OT y
          oy = proj₁ ag₀ y∈A₀
          -- 副归纳：A₁ ∩ y ⊆ A₀
          side : Prog A₁ (λ z → z ≺ y → A₀ z)
          side {x = z} z∈A₁ sih z≺y =
            proj₂ E₀ (agree⇒𝒲₁₀ oz f g ⪯-refl (proj₁ (proj₁ E₁ z∈A₁)) , mono₀ (≺⇒⪯ z≺y) (d₀ y∈A₀))
            where
              oz : OT z
              oz = proj₁ ag₁ z∈A₁
              f : (A₀ ∩ ↓ z) ⊆ A₁
              f (q , ow , w≺z) = ih (q , ow , ≺-trans w≺z z≺y)
              g : (A₁ ∩ ↓ z) ⊆ A₀
              g (q , ow , w≺z) = sih (q , ow , w≺z) (≺-trans w≺z z≺y)
          A₁∩y⊆A₀ : (A₁ ∩ ↓ y) ⊆ A₀
          A₁∩y⊆A₀ (q , _ , z≺y) = Ag-ind ag₁ side q z≺y
          𝒲y∈A₁ : 𝒲 A₁ y
          𝒲y∈A₁ = agree⇒𝒲₀₁ oy ih A₁∩y⊆A₀ ⪯-refl (proj₁ (proj₁ E₀ y∈A₀))

  L4-24⊇ : (A₁ ∩ D₀) ⊆ A₀
  L4-24⊇ (p , dy) = Ag-ind ag₁ prog p dy
    where
      prog : Prog A₁ (λ y → D₀ y → A₀ y)
      prog {x = y} y∈A₁ ih dy =
        proj₂ E₀ (agree⇒𝒲₁₀ oy f g ⪯-refl (proj₁ (proj₁ E₁ y∈A₁)) , dy)
        where
          oy : OT y
          oy = proj₁ ag₁ y∈A₁
          f : (A₀ ∩ ↓ y) ⊆ A₁
          f (q , _ , _) = proj₁ (L4-24⊆ q)
          g : (A₁ ∩ ↓ y) ⊆ A₀
          g (q , ow , w≺y) = ih (q , ow , w≺y) (mono₀ (≺⇒⪯ w≺y) dy)

  L4-24 : A₀ ≅ (A₁ ∩ D₀)
  L4-24 = L4-24⊆ , L4-24⊇
```

两种截段的单调性：

```agda
cut-≺ : ∀ a → Cut (λ z → z ≺ a)
cut-≺ a w⪯z z≺a = ⪯≺-trans w⪯z z≺a

cut-⪯ : ∀ b → Cut (λ z → z ⪯ b)
cut-⪯ b w⪯z z⪯b = ⪯-trans w⪯z z⪯b
```

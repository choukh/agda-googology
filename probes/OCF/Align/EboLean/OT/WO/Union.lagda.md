# 𝕎 := ⋃ 突出集：Definition 4.25，Lemmas 4.26–4.29

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Union` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Setzer [Se98] §4.5。这是整个证明唯一用到宇宙的地方：`𝕎 y :⟺ ∃ X : P(N). Ag(X) ∧ y ∈ X`，对 `Pred 0ℓ = Tm → Set` 量化，所以 `𝕎 : Pred 1ℓ`（一个类）。

- 4.26 (a) `Ag(X) ⟺ X ⊑ 𝕎`（X 集合）；(b) `B ⊑ 𝕎 ⟹ Ag(B)`（B 类）。
- 4.27 `Ag(𝕎)`。
- 4.28 (a) 每个元素都被某个 Ag 子集盖住 ⟹ Ag；(b) `Ag(A) ⟹ Ag(A ∩ y)`。
- 4.29 (a) 𝕎 向下封闭、向上封闭以 𝕎 为界（Lemma 4.23 (a) 在 𝕎 处）；(c) 推广为 `𝕎` 对 `x⁺` 封闭；另有对 ψ 封闭（4.23 (b)）。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Union (F : OTFacts) where

open OTFacts F

open import OCF.Align.EboLean.OT.Syntax
open import OCF.Align.EboLean.OT.Order
open import OCF.Align.EboLean.OT.Closure
open import OCF.Align.EboLean.OT.Arith
open import OCF.Align.EboLean.OT.BoolLemmas
open import OCF.Align.EboLean.OT.OTLemmas
open import OCF.Align.EboLean.OT.WO.K
open import OCF.Align.EboLean.OT.WO.Base
open import OCF.Align.EboLean.OT.WO.CLemmas
open import OCF.Align.EboLean.OT.WO.OrderLemmas F
open import OCF.Align.EboLean.OT.WO.Lemma47 F
open import OCF.Align.EboLean.OT.WO.Lemma413 F
open import OCF.Align.EboLean.OT.WO.Dist F
open import OCF.Align.EboLean.OT.WO.Closed F
open import OCF.Align.EboLean.OT.WO.Closed2 F
open import OCF.Align.EboLean.OT.WO.Lemma423 F
open import OCF.Align.EboLean.OT.WO.Lemma423c F

open import Level using (Level; _⊔_; 0ℓ; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

private variable
  ℓ : Level
```

## Definition 4.25

```agda
𝕎 : Pred (suc 0ℓ)
𝕎 y = ∃ λ (X : Pred 0ℓ) → Ag X × X y

𝕎⊆OT : 𝕎 ⊆ OT
𝕎⊆OT (X , agX , p) = proj₁ agX p

-- 𝕎 的元素属于 M(X)，X 与另一个在 x 以下与之一致的类共享 C^x
𝕎-M-of : ∀ {B : Pred ℓ} {x} → (X : Pred 0ℓ) → Ag X → X x → (∀ {z} → z ≺ x → X z → B z) → (∀ {z} → z ≺ x → B z → X z)
       → M B x
𝕎-M-of X agX p f g = proj₁ (C-cong f g) (𝒲-M (Ag⇒A⊆𝒲 agX p))
```

## Lemma 4.26

(a) →：`Ag(X) ⟹ X ⊑ 𝕎`。设 a ∈ X，b ∈ 𝕎（见证集 B），b ⪯ a。令 X′ := X|b，B′ := B|b；两者都 ≅ W(·) ∩ (⪯ b)（Lemma 4.13 (b)），Lemma 4.24 给 B′ ≅ X′，于是 b ∈ X。

```agda
private
  hOf : ∀ {ℓa} {X : Pred ℓa} → Ag X → X ⊆ M X
  hOf agX p = 𝒲-M (Ag⇒A⊆𝒲 agX p)

  -- X|b ≅ W(X|b) ∩ (⪯ b)，只要 b ⪯ a ∈ X
  restrictE : (X : Pred 0ℓ) → Ag X → ∀ {a b} → OT b → X a → b ⪯ a
            → (X ∣ b) ≅ (𝒲 (X ∣ b) ∩ (λ z → z ⪯ b))
  restrictE X agX {a} {b} ob a∈X b⪯a = to , from
    where
      hX : X ⊆ M X
      hX = hOf agX
      hX′ : (X ∣ b) ⊆ M (X ∣ b)
      hX′ (p , q) = C-mono (λ z≺x p′ → p′ , ⪯-trans (≺⇒⪯ z≺x) q) (hX p)
      f : ∀ {z} → z ≺ b → X z → (X ∣ b) z
      f z≺b p = p , ≺⇒⪯ z≺b
      g : ∀ {z} → z ≺ b → (X ∣ b) z → X z
      g _ = proj₁
      to : (X ∣ b) ⊆ (𝒲 (X ∣ b) ∩ (λ z → z ⪯ b))
      to (p , q) = 𝒲-cong-⪯ hX hX′ ob f g q (Ag⇒A⊆𝒲 agX p) , q
      from : (𝒲 (X ∣ b) ∩ (λ z → z ⪯ b)) ⊆ (X ∣ b)
      from (w , q) = ⊑← (proj₂ agX) a∈X (𝒲-cong-⪯ hX′ hX ob g f q w) (⪯-trans q b⪯a) , q

Ag⇒⊑𝕎 : (X : Pred 0ℓ) → Ag X → X ⊑ 𝕎
Ag⇒⊑𝕎 X agX = proj₁ agX , seg
  where
    seg : ∀ {a} → X a → (X ∣ a) ≅ (𝕎 ∣ a)
    seg {a} a∈X = (λ (p , q) → (X , agX , p) , q) , from
      where
        from : (𝕎 ∣ a) ⊆ (X ∣ a)
        from {x = b} ((B , agB , b∈B) , b⪯a) =
          proj₁ (proj₁ (proj₁ (L4-24 (cut-⪯ b) (cut-⪯ b) (λ d → d) EB EX) (b∈B , ⪯-refl))) , b⪯a
          where
            ob : OT b
            ob = proj₁ agB b∈B
            EX : (X ∣ b) ≅ (𝒲 (X ∣ b) ∩ (λ z → z ⪯ b))
            EX = restrictE X agX ob a∈X b⪯a
            EB : (B ∣ b) ≅ (𝒲 (B ∣ b) ∩ (λ z → z ⪯ b))
            EB = restrictE B agB ob b∈B ⪯-refl
```

(b)：`B ⊑ 𝕎 ⟹ Ag(B)`（B 任意层级）。b ∈ B ⊆ 𝕎 的见证 Y 与 B 在 b 以下一致，故 `B ⊆ M(B)`、`W(Y)|b ≅ W(B)|b`。

```agda
⊑𝕎⇒Ag : ∀ {B : Pred ℓ} → B ⊑ 𝕎 → Ag B
⊑𝕎⇒Ag {B = B} B⊑𝕎 = proj₁ B⊑𝕎 , proj₁ B⊑𝕎 , seg
  where
    B⊆𝕎 : B ⊆ 𝕎
    B⊆𝕎 = ⊑⇒⊆ B⊑𝕎

    module Wit {b} (b∈B : B b) (Y : Pred 0ℓ) (agY : Ag Y) (b∈Y : Y b) where
      Y⊑𝕎 : Y ⊑ 𝕎
      Y⊑𝕎 = Ag⇒⊑𝕎 Y agY
      f : ∀ {z} → z ≺ b → Y z → B z
      f z≺b q = ⊑← B⊑𝕎 b∈B (⊑→ Y⊑𝕎 b∈Y q (≺⇒⪯ z≺b)) (≺⇒⪯ z≺b)
      g : ∀ {z} → z ≺ b → B z → Y z
      g z≺b q = ⊑← Y⊑𝕎 b∈Y (⊑→ B⊑𝕎 b∈B q (≺⇒⪯ z≺b)) (≺⇒⪯ z≺b)

    hB : B ⊆ M B
    hB {x = b} p with B⊆𝕎 p
    ... | Y , agY , b∈Y = 𝕎-M-of Y agY b∈Y (Wit.f p Y agY b∈Y) (Wit.g p Y agY b∈Y)

    seg : ∀ {a} → B a → (B ∣ a) ≅ (𝒲 B ∣ a)
    seg {a} a∈B with B⊆𝕎 a∈B
    ... | Y , agY , a∈Y = to , from
      where
        open Wit a∈B Y agY a∈Y
        hY : Y ⊆ M Y
        hY = hOf agY
        oa : OT a
        oa = proj₁ agY a∈Y
        to : (B ∣ a) ⊆ (𝒲 B ∣ a)
        to (q , t) = 𝒲-cong-⪯ hY hB oa f g t (Ag⇒A⊆𝒲 agY (⊑← Y⊑𝕎 a∈Y (⊑→ B⊑𝕎 a∈B q t) t)) , t
        from : (𝒲 B ∣ a) ⊆ (B ∣ a)
        from (w , t) =
          ⊑← B⊑𝕎 a∈B (⊑→ Y⊑𝕎 a∈Y (⊑← (proj₂ agY) a∈Y (𝒲-cong-⪯ hB hY oa g f t w) t) t) t , t
```

## Lemma 4.27、4.28

```agda
Ag𝕎 : Ag 𝕎
Ag𝕎 = ⊑𝕎⇒Ag (𝕎⊆OT , λ _ → ≅-refl)

𝕎⊆M : 𝕎 ⊆ M 𝕎
𝕎⊆M = hOf Ag𝕎

𝕎⊆𝒲𝕎 : 𝕎 ⊆ 𝒲 𝕎
𝕎⊆𝒲𝕎 = Ag⇒A⊆𝒲 Ag𝕎

-- 4.28 (a)：每个元素都被某个 Ag 子集盖住 ⟹ Ag
covered⇒Ag : ∀ {A : Pred ℓ} → (∀ {x} → A x → ∃ λ (Y : Pred 0ℓ) → Ag Y × Y x × Y ⊆ A) → Ag A
covered⇒Ag {A = A} cov = ⊑𝕎⇒Ag (oA , seg)
  where
    oA : A ⊆ OT
    oA p = let (Y , agY , q , _) = cov p in proj₁ agY q
    seg : ∀ {x} → A x → (A ∣ x) ≅ (𝕎 ∣ x)
    seg {x} p = (λ (q , t) → let (Y , agY , r , _) = cov q in (Y , agY , r) , t)
              , (λ (w , t) → let (Y , agY , r , Y⊆A) = cov p in Y⊆A (⊑← (Ag⇒⊑𝕎 Y agY) r w t) , t)

-- 4.28 (b)：Ag(A) ⟹ Ag(A ∩ y)
Ag-∩↓ : ∀ {A : Pred ℓ} → Ag A → ∀ y → Ag (A ∩ ↓ y)
Ag-∩↓ {A = A} agA y = (λ (p , _) → proj₁ agA p) , (λ (p , _) → proj₁ agA p) , seg
  where
    hA : A ⊆ M A
    hA = hOf agA
    hA′ : (A ∩ ↓ y) ⊆ M (A ∩ ↓ y)
    hA′ (p , oy , a≺y) = C-mono (λ z≺a p′ → p′ , C⊆OT′ z≺a p′ , ≺-trans z≺a a≺y) (hA p)
      where
        C⊆OT′ : ∀ {z a} → z ≺ a → A z → OT z
        C⊆OT′ _ q = proj₁ agA q
    seg : ∀ {a} → (A ∩ ↓ y) a → ((A ∩ ↓ y) ∣ a) ≅ (𝒲 (A ∩ ↓ y) ∣ a)
    seg {a} (p , oa , a≺y) = to , from
      where
        f : ∀ {z} → z ≺ a → A z → (A ∩ ↓ y) z
        f z≺a q = q , proj₁ agA q , ≺-trans z≺a a≺y
        g : ∀ {z} → z ≺ a → (A ∩ ↓ y) z → A z
        g _ = proj₁
        to : ((A ∩ ↓ y) ∣ a) ⊆ (𝒲 (A ∩ ↓ y) ∣ a)
        to ((q , _) , t) = 𝒲-cong-⪯ hA hA′ oa f g t (Ag⇒A⊆𝒲 agA q) , t
        from : (𝒲 (A ∩ ↓ y) ∣ a) ⊆ ((A ∩ ↓ y) ∣ a)
        from (w , t) = (⊑← (proj₂ agA) p (𝒲-cong-⪯ hA′ hA oa g f t w) t , 𝒲⊆OT w , ⪯≺-trans t a≺y) , t
```

## Lemma 4.29：𝕎 的封闭性

```agda

𝕎-UC : UC 𝕎 (_≺C 𝕎)
𝕎-UC = Ag423.Ag-UC Ag𝕎

-- (c) 的推广：𝕎 对 x⁺ 封闭（x ∈ X ⟹ x⁺ ∈ X⁺，Ag(X⁺)）
𝕎-plus : ∀ {x} → 𝕎 x → 𝕎 (plus x)
𝕎-plus (X , agX , p) = X ⁺ , Ag423c.Ag⁺ agX , Ag423c.plus∈A⁺ agX p

-- 对 ψ 封闭（Lemma 4.23 (b) 在 𝕎 处）
𝕎-ψ : ∀ {κ c} → 𝕎 (regTm κ) → 𝕎 c → OT ⟨ psi κ c ⟩ → 𝕎 ⟨ psi κ c ⟩
𝕎-ψ = Ag423.Ag-ψ Ag𝕎
```

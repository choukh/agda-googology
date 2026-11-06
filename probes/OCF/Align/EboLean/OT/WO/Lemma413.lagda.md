# Lemma 4.13 (b)(c)(d)：W(A) 只依赖 A 的一段；W(A) ∩ Ω₁ 是 OT 的段

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Lemma413` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Setzer [Se98] Lemma 4.13。(a) 在 [Base](Base.lagda.md)。

(b) 原文：`A ∩ Ω_a ≅ B ∩ Ω_a`，`A ⊆ M(A)`，`B ⊆ M(B)` ⟹ `M(A) ∩ Ω_{a+1} ≅ M(B) ∩ Ω_{a+1}` 且 `W(A) ∩ Ω_{a+1} ≅ W(B) ∩ Ω_{a+1}`。这里用更一般的形式：A 与 B 在 c 以下一致，则对所有 `ỹ ⪯ c` 的 y，`C^y(A) ≅ C^y(B)`（Lemma 4.7 (a)：C^y 只看 A ∩ ỹ），从而 M、τ、W 在这些 y 上一致；`y ≺ c⁺ ⟹ ỹ ⪯ c` 给出原文的形式。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Lemma413 (F : OTFacts) where

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

open import Level using (Level)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private variable
  ℓ ℓ′ : Level
  A B : Pred ℓ
```

## (b)

```agda
module _ {A : Pred ℓ} {B : Pred ℓ′} (hA : A ⊆ M A) (hB : B ⊆ M B) {c : Tm} (oc : OT c)
         (f : ∀ {x} → x ≺ c → A x → B x) (g : ∀ {x} → x ≺ c → B x → A x) where

  C-cong-c : ∀ {y} → OT y → tilde y ⪯ c → C y A ≅ C y B
  C-cong-c oy p =
    ≅-trans (C-tilde hA oy)
      (≅-trans (C-cong (λ q → f (≺⪯-trans q p)) (λ q → g (≺⪯-trans q p)))
               (≅-sym (C-tilde hB oy)))

  M-cong-c : ∀ {y} → tilde y ⪯ c → M A y → M B y
  M-cong-c p m = proj₁ (C-cong-c (M⊆OT m) p) m

  τ-cong-c : ∀ {y} → OT y → tilde y ⪯ c → τ A y ≅ τ B y
  τ-cong-c oy p = (λ (d , q) → proj₁ (C-cong-c oy p) d , q)
                , (λ (d , q) → proj₂ (C-cong-c oy p) d , q)

  𝒲-cong-c : ∀ {y} → tilde y ⪯ c → 𝒲 A y → 𝒲 B y
  𝒲-cong-c {y} p (sup m f′) =
    sup (M-cong-c p m)
        (λ {z} t → 𝒲-cong-c
                     (⪯-trans (tilde-mono (C⊆OT (proj₁ t)) (M⊆OT m) (≺⇒⪯ (proj₂ t))) p)
                     (f′ (proj₂ (τ-cong-c (M⊆OT m) p) t)))

  -- 原文的形式：y ≺ c⁺

  𝒲-cong-plus : ∀ {y} → y ≺ plus c → 𝒲 A y → 𝒲 B y
  𝒲-cong-plus q w = 𝒲-cong-c (≺plus⇒tilde⪯ (𝒲⊆OT w) oc q) w

  -- y ⪯ c 也够（ỹ ⪯ y ⪯ c）
  𝒲-cong-⪯ : ∀ {y} → y ⪯ c → 𝒲 A y → 𝒲 B y
  𝒲-cong-⪯ q w = 𝒲-cong-c (⪯-trans (tilde⪯ (𝒲⊆OT w)) q) w
```

## (c) `A ≅ B ⟹ W(A) ≅ W(B)`

```agda


```

## (d) `W(A) ∩ Ω₁ ⊑ OT`

`x ∈ W(A)`，`x ≺ Ω₁`：`τ^A(x) ≅ x`（Lemma 4.9 (c)），所以 `x ⊆ W(A)`。

```agda
𝒲∩Ω₁⊑OT : (𝒲 A ∩ ↓ Ω₁) ⊑ OT
𝒲∩Ω₁⊑OT {A = A} = (λ (w , _) → 𝒲⊆OT w) , seg
  where
    seg : ∀ {x} → (𝒲 A ∩ ↓ Ω₁) x → ((𝒲 A ∩ ↓ Ω₁) ∣ x) ≅ (OT ∣ x)
    seg {x} (w , ox , x≺Ω₁) = (λ ((w′ , _) , q) → 𝒲⊆OT w′ , q) , from
      where
        from : (OT ∣ x) ⊆ ((𝒲 A ∩ ↓ Ω₁) ∣ x)
        from {x = z} (oz , z⪯x) with ⪯⇒≺⊎≡ z⪯x
        ... | inj₂ refl = (w , ox , x≺Ω₁) , z⪯x
        ... | inj₁ z≺x  =
          (𝒲-τ w (proj₂ (τ-Ω₁ ox x≺Ω₁) (oz , z≺x)) , oz , ≺-trans z≺x x≺Ω₁) , z⪯x
```

# Lemma 4.30：从一个集合 B 把 a 拉进 𝕎

> **EboLean 删节拷贝 (记号侧验收工作, 读 Setzer 的记号 OT_I).** 归档 `Mahlo.Inacc.WO.Lemma430` 的拷贝, 只改了模块名, 并删去了 EBO 路线 ([EboLean](../../../EboLean.lagda.md)) 用不到的定义 (由定义级切片判定, 删后从头编译核对). 讲解文字照旧, 可能提到已删的定义; 归档原文未动.

Setzer [Se98] Lemma 4.30：`a ∈ M(𝕎) ∩ I`，`B : P(N)`，`τ^𝕎(a) ⪯ B ⊆ 𝕎|a` ⟹ `a ∈ 𝕎`。

这是 MLTT 里「选择公理成立」被用到的地方：B ⊆ 𝕎 的每个元素各有见证集，取 `g : B̂ → P(N)`（Σ 的投影），`C := (⋃_{y : B̂} g y) ∩ a` 是**集合**（对小类型 B̂ 的 Σ）。然后 C ≅ 𝕎 ∩ a，`W(C) ∩ a ⊆ C`（d ∈ W(C)，d ≺ a：d̃ ∈ C^d(C) 落进 C^a(C) ≅ C^a(𝕎)（Lemma 4.7 (g)），d̃ ∈ 𝕎，d⁺ ∈ 𝕎，段性质把 d 拉回 C），`C′ := C ∪ {a}` 是突出集且含 a。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

open import OCF.Align.EboLean.OT.WO.Facts

module OCF.Align.EboLean.OT.WO.Lemma430 (F : OTFacts) where

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
open import OCF.Align.EboLean.OT.WO.Lemma47ef F
open import OCF.Align.EboLean.OT.WO.Lemma423 F
open import OCF.Align.EboLean.OT.WO.Lemma423c F
open import OCF.Align.EboLean.OT.WO.Union F

open import Level using (Level; _⊔_; 0ℓ; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃; Σ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
```

## 工具：WDC 的限制、C 与 𝕎 在 a 以下一致时的搬运

```agda
WDC-∩↓ : ∀ {ℓ} {A : Pred ℓ} → WDC A → ∀ d → WDC (A ∩ ↓ d)
WDC-∩↓ {A = A} w d = record
  { wdc-+ = λ nz o (ax , ox , x≺d) →
      let (l , r) = wdc-+ w nz o ax
      in (l , proj₁ (OT-▹⁻ nz o) , ≺-trans (≺-+ˡ nz o) x≺d)
       , (r , proj₂ (OT-▹⁻ nz o) , ≺-trans (≺-+ʳ nz o) x≺d)
  ; wdc-φ = λ o (ax , ox , x≺d) →
      let (l , r) = wdc-φ w o ax
      in (l , proj₁ (OT-φ⁻ o) , ≺-trans (≺-φˡ o) x≺d)
       , (r , proj₁ (proj₂ (OT-φ⁻ o)) , ≺-trans (≺-φʳ o) x≺d)
  ; wdc-Ω = λ o (ax , ox , x≺d) → wdc-Ω w o ax , proj₁ (OT-Ω⁻ o) , ≺-trans (≺-Ω o) x≺d
  ; wdc-ψ = λ o (ax , ox , x≺d) → wdc-ψ w o ax , κ⁻-OT′ o , ⪯≺-trans (κ⁻⪯ψ o) x≺d
  }
  where
    κ⁻-OT′ : ∀ {κ c} → OT ⟨ psi κ c ⟩ → OT (κ⁻ κ)
    κ⁻-OT′ {κ = ΩR z} o = tilde-OT o
    κ⁻-OT′ {κ = IR}   o = OT-0

private
  hOf : ∀ {ℓ} {X : Pred ℓ} → Ag X → X ⊆ M X
  hOf agX p = 𝒲-M (Ag⇒A⊆𝒲 agX p)
```

## Lemma 4.30

```agda
module L430 {a : Tm} (ma : M 𝕎 a) (a≺I : a ≺ I′) (B : Pred 0ℓ)
            (cover : ∀ {y} → τ 𝕎 a y → ∃ λ b → B b × y ⪯ b) (B⊆𝕎a : B ⊆ (𝕎 ∣ a)) where

  oa : OT a
  oa = M⊆OT ma

  -- 见证集的选取（Σ 投影 = MLTT 的 AC）
  B̂ : Set
  B̂ = Σ Tm B

  g : B̂ → Pred 0ℓ
  g (b , bb) = proj₁ (proj₁ (B⊆𝕎a bb))

  gAg : ∀ y → Ag (g y)
  gAg (b , bb) = proj₁ (proj₂ (proj₁ (B⊆𝕎a bb)))

  g∋ : ∀ y → g y (proj₁ y)
  g∋ (b , bb) = proj₂ (proj₂ (proj₁ (B⊆𝕎a bb)))

  -- S := (⋃_{y : B̂} g y) ∩ a，一个集合
  S : Pred 0ℓ
  S x = (∃ λ (y : B̂) → g y x) × x ≺ a

  AgS : Ag S
  AgS = covered⇒Ag λ ((y , gx) , x≺a) →
          (g y ∩ ↓ a) , Ag-∩↓ (gAg y) a , (gx , proj₁ (gAg y) gx , x≺a) , (λ (q , _ , r) → (y , q) , r)

  S⊆𝕎 : S ⊆ 𝕎
  S⊆𝕎 ((y , gx) , _) = g y , gAg y , gx

  hS : S ⊆ M S
  hS = hOf AgS

  -- τ^𝕎(a) ⊆ 𝕎
  τ⊆𝕎 : τ 𝕎 a ⊆ 𝕎
  τ⊆𝕎 {x = y} t@(cy , y≺a) with cover t
  ... | b , bb , y⪯b = ⊑← (proj₂ Ag𝕎) b∈𝕎 w𝕎y y⪯b
    where
      b∈𝕎 : 𝕎 b
      b∈𝕎 = proj₁ (B⊆𝕎a bb)
      b⪯a : b ⪯ a
      b⪯a = proj₂ (B⊆𝕎a bb)
      w𝕎y : 𝒲 𝕎 y
      w𝕎y with ⪯⇒≺⊎≡ y⪯b
      ... | inj₂ refl = 𝕎⊆𝒲𝕎 b∈𝕎
      ... | inj₁ y≺b  = 𝒲-τ (𝕎⊆𝒲𝕎 b∈𝕎) (C-anti 𝕎⊆M (𝕎⊆OT b∈𝕎) oa b⪯a cy , y≺b)

  -- S ≅ 𝕎 ∩ a
  S≅ : S ≅ (𝕎 ∩ ↓ a)
  S≅ = (λ s@((y , gx) , x≺a) → S⊆𝕎 s , proj₁ (gAg y) gx , x≺a)
     , (λ (wx , ox , x≺a) →
          let (b , bb , x⪯b) = cover (A∩a⊆C (wx , ox , x≺a) , x≺a)
          in ((b , bb) , ⊑← (Ag⇒⊑𝕎 (g (b , bb)) (gAg (b , bb))) (g∋ (b , bb)) wx x⪯b) , x≺a)

  -- S 与 𝕎 在 a 以下一致
  f𝕎 : ∀ {z} → z ≺ a → S z → 𝕎 z
  f𝕎 _ = S⊆𝕎
  g𝕎 : ∀ {z} → z ≺ a → 𝕎 z → S z
  g𝕎 z≺a wz = proj₂ S≅ (wz , 𝕎⊆OT wz , z≺a)

  -- W(S) ∩ a ⊆ S：d̃ ∈ C^d(S) ⊆ C^a(S) ⊆ C^a(𝕎)，d̃ ∈ 𝕎，d⁺ ∈ 𝕎，段性质
  WS∩a⊆S : ∀ {d} → 𝒲 S d → d ≺ a → S d
  WS∩a⊆S {d} wd d≺a = proj₂ S≅ (𝕎d , od , d≺a)
    where
      od : OT d
      od = 𝒲⊆OT wd
      sd̃ : C d S (tilde d)
      sd̃ = dc-tilde (C-DC (WDC-∩↓ (Ag423.Ag-WDC AgS) d)) od (𝒲-M wd)
      sd̃a : C a S (tilde d)
      sd̃a = L4-7g hS od oa d≺a a≺I (tilde d) (tilde-OT od) ⪯-refl sd̃
      d̃∈𝕎 : 𝕎 (tilde d)
      d̃∈𝕎 = τ⊆𝕎 (C-mono (λ _ → S⊆𝕎) sd̃a , ⪯≺-trans (tilde⪯ od) d≺a)
      d⁺∈𝕎 : 𝕎 (plus d)
      d⁺∈𝕎 = subst 𝕎 (tilde-plus od) (𝕎-plus d̃∈𝕎)
      W𝕎d : 𝒲 𝕎 d
      W𝕎d = 𝒲-cong-⪯ hS 𝕎⊆M od (λ z≺d → f𝕎 (≺-trans z≺d d≺a)) (λ z≺d → g𝕎 (≺-trans z≺d d≺a)) ⪯-refl wd
      𝕎d : 𝕎 d
      𝕎d = ⊑← (proj₂ Ag𝕎) d⁺∈𝕎 W𝕎d (≺⇒⪯ (≺plus od))

  -- S′ := S ∪ {a}
  S′ : Pred 0ℓ
  S′ x = S x ⊎ x ≡ a

  S′⊆OT : S′ ⊆ OT
  S′⊆OT (inj₁ s)    = proj₁ AgS s
  S′⊆OT (inj₂ refl) = oa

  fS′ : ∀ {z} → z ≺ a → S′ z → 𝕎 z
  fS′ _   (inj₁ s)    = S⊆𝕎 s
  fS′ z≺a (inj₂ refl) = ⊥-elim (≺-irrefl z≺a)
  gS′ : ∀ {z} → z ≺ a → 𝕎 z → S′ z
  gS′ z≺a wz = inj₁ (g𝕎 z≺a wz)
  -- S 与 S′ 在 a 以下一致
  fSS′ : ∀ {z} → z ≺ a → S z → S′ z
  fSS′ _ = inj₁
  gS′S : ∀ {z} → z ≺ a → S′ z → S z
  gS′S _   (inj₁ s)    = s
  gS′S z≺a (inj₂ refl) = ⊥-elim (≺-irrefl z≺a)

  hS′ : S′ ⊆ M S′
  hS′ (inj₁ s)    = C-mono (λ _ → inj₁) (hS s)
  hS′ (inj₂ refl) = proj₂ (C-cong fS′ gS′) ma

  -- τ^{S′}(a) ⊆ W(S′)
  τS′⊆W : τ S′ a ⊆ 𝒲 S′
  τS′⊆W {x = y} (cy , y≺a) =
    𝒲-cong-⪯ hS hS′ oa fSS′ gS′S (≺⇒⪯ y≺a)
      (Ag⇒A⊆𝒲 AgS (g𝕎 y≺a (τ⊆𝕎 (proj₁ (C-cong fS′ gS′) cy , y≺a))))

  a∈WS′ : 𝒲 S′ a
  a∈WS′ = sup (hS′ (inj₂ refl)) τS′⊆W

  AgS′ : Ag S′
  AgS′ = S′⊆OT , S′⊆OT , seg
    where
      x⪯a : ∀ {x} → S′ x → x ⪯ a
      x⪯a (inj₁ (_ , x≺a)) = ≺⇒⪯ x≺a
      x⪯a (inj₂ refl)      = ⪯-refl
      seg : ∀ {x} → S′ x → (S′ ∣ x) ≅ (𝒲 S′ ∣ x)
      seg {x} s′ = to , from
        where
          to : (S′ ∣ x) ⊆ (𝒲 S′ ∣ x)
          to (inj₁ s , t)    = 𝒲-cong-⪯ hS hS′ oa fSS′ gS′S (≺⇒⪯ (proj₂ s)) (Ag⇒A⊆𝒲 AgS s) , t
          to (inj₂ refl , t) = a∈WS′ , t
          from : (𝒲 S′ ∣ x) ⊆ (S′ ∣ x)
          from {x = z} (w , t) with ⪯⇒≺⊎≡ (⪯-trans t (x⪯a s′))
          ... | inj₂ refl = inj₂ refl , t
          ... | inj₁ z≺a  = inj₁ (WS∩a⊆S (𝒲-cong-⪯ hS′ hS oa gS′S fSS′ (≺⇒⪯ z≺a) w) z≺a) , t

  L4-30 : 𝕎 a
  L4-30 = S′ , AgS′ , inj₂ refl
```

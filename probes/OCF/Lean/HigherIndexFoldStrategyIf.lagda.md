# 分量内部的低指标策略

旧Path不能容纳合法c=flL U的完整分量地板，已有编译否定。新接口只改
研究分支的事件策略，不改旧Path或旧运行器：归base的低指标也继承动态β。
策略按原种类位置递归计算，不由记号或值判定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexFoldStrategyIf where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (AdmK)
open import OCF.Lean.HigherIndexClassIf
open import OCF.Lean.HigherIndexFoldIf using (k; g; Source)

data Route (A : Set) : Set where
  fixed : Route A
  changing : (to : Cd → A) (fr : A → Cd) →
    (∀ a → to (fr a) ≡ a) → (∀ e → fr (to e) ≡ e) → Route A

route : ∀ c κ → Route (E (Native c) κ)
route hz (inj₁ _ , inj₁ ())
route hz (inj₁ _ , inj₂ _) = changing (λ e → e) (λ e → e) (λ _ → refl) (λ _ → refl)
route hz (inj₂ d , κ) = fixed
route (hs c) (inj₁ κ) = route c κ
route (hs c) (inj₂ _) = fixed
route (hl f) (n , κ) = route (f n) κ
route (hΩ (inj₁ ()) f) κ
route (hΩ (inj₂ _) f) (inj₁ _ , inj₁ ())
route (hΩ (inj₂ _) f) (inj₁ _ , inj₂ _) = changing (λ e → e) (λ e → e) (λ _ → refl) (λ _ → refl)
route (hΩ (inj₂ _) f) (inj₂ e , κ) = route (f e) κ

Path : Cd → HB U → HB Source → Set
Path β B hz = ⊤
Path β B (hs a) = Path β B a
Path β B (hl f) = ∀ n → Path β B (f n)
Path β B (hΩ (inj₁ _ , inj₁ (inj₁ ())) f)
Path β B (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) =
  ∀ e → β ⊲ e → LgB e → Path (hs e) B (f e)
Path β B (hΩ (inj₁ _ , inj₂ _) f) =
  ∀ e → (a : AdmK k ((tt , β) , B) e) → Path (proj₂ (proj₁ a)) (hs e) (f e)
Path β B (hΩ (inj₂ c , κ) f) with route c κ
... | fixed = (c ⊲[ tt , β ] B × Position (tt , β) c κ) × (∀ e → Path β B (f e))
... | changing to fr rt tr = (c ⊲[ tt , β ] B × Position (tt , β) c κ) ×
  (∀ e → β ⊲ e → LgB e → Path (hs e) B (f (to e)))

record LocalFold : Set₁ where
  field
    fold : ∀ β → LgB β → ∀ B → LgB B → ∀ t → t ⊲[ tt , β ] B →
      (a : HB Source) → Path β B a → HB (Native t)
```

changing的下一界给e⊲hs e，正修复反例中的hs β⊲β缺口。它尚未给
任意raw反馈坐标的全组件证书；全高floor的实例仍需独立证明。

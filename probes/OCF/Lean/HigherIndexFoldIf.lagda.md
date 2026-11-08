# 含Ω坐标的动态源路径

源是原lΩ1的树；低世界β与高公共界B分开。指标旧Ω改变β，高指标
按J₁改变低世界及B；分量节点携带实际Position，不要求固定世界覆盖全部raw种类。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexFoldIf where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (AdmK)
open import OCF.Lean.HigherIndexClassIf

k : LH
k = ls lz
g : HB U → LH
g c = prefix ⊕L upL k c
Source : KS
Source = Lv (lΩ k g)

Path : Cd → HB U → HB Source → Set
Path β B hz = ⊤
Path β B (hs a) = Path β B a
Path β B (hl f) = ∀ n → Path β B (f n)
Path β B (hΩ (inj₁ _ , inj₁ (inj₁ ())) f)
Path β B (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) =
  ∀ e → β ⊲ e → LgB e → Path (hs e) B (f e)
Path β B (hΩ (inj₁ _ , inj₂ _) f) =
  ∀ e → (a : AdmK k ((tt , β) , B) e) → Path (proj₂ (proj₁ a)) (hs e) (f e)
Path β B (hΩ (inj₂ c , κ) f) =
  (c ⊲[ tt , β ] B × Position (tt , β) c κ) × (∀ e → Path β B (f e))

record LocalFold : Set₁ where
  field
    fold : ∀ β → LgB β → ∀ B → LgB B → ∀ t → t ⊲[ tt , β ] B →
      (a : HB Source) → Path β B a → HB (Native t)
```

本接口仅给函数类型；运行器另给逐构造子真实算法。首次非空实例将是
原θ(flL U)的全部分支，包含实际Ω坐标，不把全高层floor持证当作默认事实。

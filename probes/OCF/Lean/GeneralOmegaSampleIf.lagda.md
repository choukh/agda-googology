# 实际采样坐标的统一合法世界接口

所有种类共享一个World，不逐kind修改世界。成对比较只在右反馈完成
树这一字面共同界及由它生成的同一个合法世界内陈述。接口不要求
原run保任意第一位置。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaSampleIf where
open import Data.Product using (_×_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.LHRecTy using (LH; Lv)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)

record SampleWorlds : Set₁ where
  field
    World : ∀ x → Cd → Wd (Lv x)
    legal : ∀ x d → LgW (Lv x) (World x d)
    admitted : ∀ x κ d → Bd (Lv x) κ (code x κ d) (World x d)
    growth : ∀ x {d e} → leg d ⊲ leg e → _≤w_ (Lv x) (World x d) (World x e)
    pair : ∀ x κ {d e} → leg d ⊲ leg e →
      Bd (Lv x) κ (code x κ d) (World x e) ×
      Bd (Lv x) κ (code x κ e) (World x e) ×
      Pr (Lv x) κ (World x e) (code x κ d) (code x κ e)
```

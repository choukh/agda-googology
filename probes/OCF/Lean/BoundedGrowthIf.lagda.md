# 动态公共界：世界扩张证据

保留旧分量时使用复合上下文，不要求两条路径证明相等。公共界增长
不自动给出目标世界；以下字段明确保留这项义务。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedGrowthIf where
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (pw)
open import OCF.Lean.BoundedContextRun using (path-context)

record WorldGrowth (P k : LH) (w : Wd (Lv k))
  (B C : HB (Lv k)) (r : B ⊲[ w ] C)
  (W : Wd (Lv (P ⊕L upL k B))) : Set where
  field
    future : Wd (Lv (P ⊕L upL k C))
    legal-future : LgW (Lv (P ⊕L upL k C)) future
    extends : _≤w_ (Lv (P ⊕L upL k B)) W
      (pw (path-context P k r) future)
```

成功实例不能只有零树；后续实际后继扩张以 `(W,0)` 保留完整旧世界，
树搬运对任意混合分支进行。此接口没有声称任意 C 的世界扩张可求。

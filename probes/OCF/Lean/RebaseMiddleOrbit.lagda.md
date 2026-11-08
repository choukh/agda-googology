# 完整中Ω旧轨道到重定位Native链的一步延迟

把跨运行器证明中的真实坐标、Seed和原输出和单独导出，供low末段
使用。参数是单次分支关系与目标坐标膨胀，不是假定整个输出覆盖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RebaseMiddleOrbit where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (chain)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedCompletionUniformIf
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; prefix-rel; right-rel; up-value; floor-value)
open import OCF.Align.BoundedWorldValueTwoSlot using (U; V; mid)
open import OCF.Align.BoundedWorldSeedIf
import OCF.Align.BoundedWorldSeedClosure as S
open import OCF.Align.BoundedWorldSeedCompose using (trans0)
import OCF.Align.BoundedWorldSeedMiddle as Old
open import OCF.Lean.RebaseMiddleIf
open import OCF.Lean.RebaseMiddleRun using (native-seed; middle-bound; recover-up; one-seed; chain-seed; read-positive)
open import OCF.Align.BoundedWorldRebaseIf using (enc)
import OCF.Lean.Fold1Fold as F
import OCF.Lean.RebaseOutputChain as Padding

module Compare (u v : HB U) (su : Seed0 u) (sv : Seed0 v)
  (f g : HB U → HB V)
  (source : ∀ e → Seed0 e → Seed1 (f e))
  (target : ∀ e → Seed0 e → Seed1 (g e))
  (target-inflate : ∀ e → Seed0 e → Value (hs hz) (up e) (g e))
  (rel : ∀ x y → Value hz x y → Value (hs hz) (f x) (g y))
  (uv : Value hz u v) where

  module Original = F.Col _⊞_ _⊞_ u u (λ _ e → e)
    (λ b e → mid b (f e)) (λ b e → mid b (f e))
  H : HB U → HB U
  H e = eval (v ⊞ e) (g (v ⊞ e))
  keeps : ∀ e → Seed0 e → Seed0 (H e)
  keeps e se = native-seed (v ⊞ e) (g (v ⊞ e)) (S.add0 sv se) (target (v ⊞ e) (S.add0 sv se))
  captured : ∀ e → Seed0 e → Value hz (v ⊞ e) (H e)
  captured e se = trans0 (recover-up (S.self0 cap) (v ⊞ e))
    (middle-bound cap cap (S.up1 cap) (target (v ⊞ e) cap)
      (target-inflate (v ⊞ e) cap) (S.self0 cap))
    where cap = S.add0 sv se
  inflates : ∀ e → Seed0 e → Value hz e (H e)
  inflates e se = trans0 (right-rel v (S.self0 se)) (captured e se)
  positive : ∀ e → Seed0 e → Value hz (hs hz) (H e)
  positive e se = read-positive (enc (v ⊞ e) (g (v ⊞ e)))
  module Cover = Padding.Cover H keeps inflates positive

  current : ∀ n → Original.cw n ≡ Original.ce n
  current zero = refl
  current (suc n) = refl
  old-coordinates : ∀ n → Seed0 (Original.ce n)
  old-outputs : ∀ n → Seed0 (Original.oo n)
  old-coordinates zero = su
  old-coordinates (suc n) = S.add0 (old-coordinates n) (old-outputs n)
  old-outputs n rewrite current n = Old.preserve (old-coordinates n) (source _ (old-coordinates n))

  coordinates : ∀ n → Value hz (Original.ce n) (chain H (suc n))
  outputs : ∀ n → Value hz (Original.oo n) (H (chain H (suc n)))
  coordinates zero = trans0 (prefix-rel uv (hs hz)) (right-rel (hs hz) (captured _ one-seed))
  coordinates (suc n) = add-rel (coordinates n) (outputs n)
  outputs n rewrite current n = middle-bound
    (old-coordinates n) (S.add0 sv (chain-seed H keeps (suc n)))
    (source _ (old-coordinates n)) (target _ (S.add0 sv (chain-seed H keeps (suc n))))
    (rel _ _ (right-rel v (coordinates n))) (right-rel v (coordinates n))

  sums : ∀ n → Value hz (Original.oO n) (Ops.partial U (λ j → H (chain H j)) (suc n))
  sums zero = right-rel (H (chain H zero)) (outputs zero)
  sums (suc n) = add-rel (sums n) (outputs (suc n))
```

以原最低中Ω地板的分支up实例化，初始中槽仍为真实floor0。

```agda
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
module Actual = Compare (floor zero) (floor zero) S.floor0 S.floor0 up up
  (λ e se → S.up1 se) (λ e se → S.up1 se)
  (λ e se → up-value hz (S.self0 se))
  (λ x y xy → up-value hz xy) (floor-value zero)
```

Original仍包含原动态mid的全部坐标和输出，Cover的原partial目标并未
替换。对low的使用还须逐项低输出比较及原terminal的补偿定理。

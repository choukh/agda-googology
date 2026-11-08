# 原 Old.TΩ3 的完整两低槽输出

不是取第三地板的某个采样：这里模拟全部最高回灌坐标、全部输出项及其
原部分和，再得到整个旧闭项与两低槽语义的双向值比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldValueWhole where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ll; same-value; same-sym)
open import OCF.Align.FrozenInnerOuter using (same-add)
open import OCF.Align.BoundedCompletionFiniteRunIf using (Rel; rz; rs; rl; ro)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (rel-add; floor; floor-rel)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedWorldCoverIf using (act)
open import OCF.Align.BoundedWorldValueTwoSlot
open import OCF.Align.BoundedWorldValueBridge using (low-bridge)
import OCF.Lean.Fold1 as Old
import OCF.Lean.Fold1If as I
open I using (_≤ᵛ_)
import OCF.Lean.Fold1Fold as F

rel-mul : ∀ {a b} → Rel (num 1) a b → ∀ n → Rel (num 1) (I.mul a n) (I.mul b n)
rel-mul p zero = p
rel-mul p (suc n) = rel-add (rel-mul p n) p
coordinate : ∀ {a b} → Rel (num 1) a b → ∀ W → Rel (num 1)
  (F.Φ (num 3) tt (num 2) (hsuc hself) W (up a)) (act b)
coordinate rz W = rs rz
coordinate (rs p) W = rl (rel-mul (coordinate p W))
coordinate (rl p) W = rl (λ n → coordinate (p n) W)
coordinate (ro p) W = ro (λ x y xy → coordinate (p x y xy) W)

module Actual = F.Col _⊞_ _⊞_ (((tt , hz) , floor zero) , floor 1) (floor 1)
  (λ W e → proj₁ W , e)
  (λ W e → F.Φ (num 3) tt (num 2) (hsuc hself) W (up e))
  (λ W e → F.Φ (num 3) tt hz (hsuc (hsuc (hsuc hself))) W (up e))
module Model = F.Col _⊞_ _⊞_ tt (floor 1) (λ _ _ → tt)
  (λ _ e → act e) (λ _ e → low hz (floor zero) e)

coordinates : ∀ n → Rel (num 1) (Actual.ce n) (Model.ce n)
coordinates zero = floor-rel 1
coordinates (suc n) = rel-add (coordinates n) (coordinate (coordinates n) (Actual.cw n))
outputs : ∀ n → Same (Actual.oo n) (Model.oo n)
outputs zero = low-bridge (coordinates zero) (floor-rel zero) zz (floor 1)
outputs (suc n) = low-bridge (coordinates (suc n)) (floor-rel zero) zz (Actual.ce (suc n))
sums : ∀ n → Same (Actual.oO n) (Model.oO n)
sums zero = outputs zero
sums (suc n) = same-add (sums n) (outputs (suc n))

output : Cd
output = hl Model.oO
old-three : Same (Old.TΩ (num 3) tt) output
old-three = ll sums
old-three≤output : Old.TΩ (num 3) tt ≤ᵛ output
old-three≤output = same-value old-three
output≤old-three : output ≤ᵛ Old.TΩ (num 3) tt
output≤old-three = same-value (same-sym old-three)
```

新用的字段是：底槽采用Same、中槽采用Rel0，并且每次更新只改一槽，
保留另一槽的关系。初始中槽为原floor0而不是1；每次中Ω回灌仍用mid，
输出仍用low。因此此定理没有把Old3变成UniformStage的固定seed轨道。
后续尚需证明这个确切output被某个真实规范输出覆盖；这里未声称进入C。

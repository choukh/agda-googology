# 带中槽前缀的完整反馈模拟

所有ce、oo、oO同时比较；prefix随两边各自的实际中槽更新递归。
没有把prefix或low的结果冻结成常数，也没有用low-up消去真实中Ω。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldPrefixRun where
open import Data.Nat using (zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedCompletionUniformClosure using (add-rel; up-value)
open import OCF.Align.BoundedWorldPrefixIf
open import OCF.Align.BoundedWorldValueTwoSlot
import OCF.Lean.TwoSlotValueRun as Joint

module Compare {u v b d p q} (uv : u ≤ᵛ v) (bd : Value hz b d) (pq : Value (hs hz) p q) where
  module L = Middle u b p
  module R = Middle v d q
  coordinates : ∀ n → Value hz (L.ce n) (R.ce n)
  advance : ∀ n → Value hz
    (mid (L.cw n) (p ⊞ up (L.ce n))) (mid (R.cw n) (q ⊞ up (R.ce n)))
  coordinates zero = bd
  coordinates (suc n) = add-rel (coordinates n) (advance n)
  advance zero = Joint.middle (add-rel pq (up-value hz bd)) bd
  advance (suc n) = Joint.middle (add-rel pq (up-value hz (coordinates (suc n)))) (coordinates (suc n))
  outputs : ∀ n → L.oo n ≤ᵛ R.oo n
  outputs zero = Joint.lower (add-rel pq (up-value hz bd)) bd uv
  outputs (suc n) = Joint.lower (add-rel pq (up-value hz (coordinates (suc n)))) (coordinates (suc n)) uv
  sums : ∀ n → L.oO n ≤ᵛ R.oO n
  sums zero = outputs zero
  sums (suc n) = add-mono (sums n) (outputs (suc n))

instance-prefix : PrefixComparison
instance-prefix = record { sums = λ uv bd pq → Compare.sums uv bd pq }

whole : ∀ {u v b d p q} → u ≤ᵛ v → Value hz b d → Value (hs hz) p q →
  hl (Middle.oO u b p) ≤ᵛ hl (Middle.oO v d q)
whole uv bd pq = l≤ (λ n → OCF.Lean.Fold1If.≤l n (Compare.sums uv bd pq n))
```

后篇将本定理填到真实旧第三地板的非零前缀。右侧仍是两槽真实语义，
尚未由本篇识别为某个固定seed的Uniform输出。

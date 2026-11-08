# 保留中槽读取的前缀反馈接口

前缀p仍在mid/low中递归，每次中Ω事件更新中槽；底槽u固定。
接口比较整条轨道及输出部分和，不假定low是terminal与mid复合。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedWorldPrefixIf where
open import Data.Nat using (ℕ)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedCompletionUniformIf using (Value)
open import OCF.Align.BoundedWorldValueTwoSlot
import OCF.Lean.Fold1Fold as F

module Middle (u : Cd) (b : HB U) (p : HB V) = F.Col _⊞_ _⊞_ b b (λ _ e → e)
  (λ b′ e → mid b′ (p ⊞ up e))
  (λ b′ e → low u b′ (p ⊞ up e))

record PrefixComparison : Set where
  field
    sums : ∀ {u v b d p q} → u ≤ᵛ v → Value hz b d → Value (hs hz) p q →
      ∀ n → Middle.oO u b p n ≤ᵛ Middle.oO v d q n
```

目标参数明确，尚未把右侧Middle识别为真实Uniform/normal的输出。
运行证明及真实前缀实例须另行填充；接口本身不计为完成覆盖。

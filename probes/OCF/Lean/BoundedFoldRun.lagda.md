# 局部塔直接回灌

这是具体算法，不以 Local 存在性作结论。零送1，后继取重复和，
自然极限逐点，keep递归保留；same/above使用目标型输出回灌原始坐标。
分支递归的源始终是整个 Safe β B，绝不投称某个分量。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedFoldRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldIf
open import OCF.Lean.BoundedFoldClass
open import OCF.Lean.TowerCollapseIf using (module Ops)

chain : ∀ {S} → (HB S → HB S) → ℕ → HB S
chain f zero = hs hz
chain f (suc n) = chain f n ⊞ f (chain f n)

diagonal : ∀ {S R} → (HB S → HB S) → (HB S → HB R) → HB R
diagonal {R = R} f g = Ops.sum R (λ n → g (chain f n))

module Run (β : HB S⊥) (lb : LgB β) (B : HB U) (lB : LgB B) where
  fold : ∀ t → t ⊲[ (tt , β) ] B → HB (Safe β B) → HB (T t)
  fold t pt hz = hs hz
  fold t pt (hs a) = Ops.repeat (T t) (fold t pt a)
  fold t pt (hl f) = hl (λ n → fold t pt (f n))
  fold t pt (hΩ (κ , p) g) with decide β pt lb lB (classify β B κ p)
  ... | keep κ′ fr = hΩ κ′ (λ c → fold t pt (g (fr c)))
  ... | same to = diagonal (λ c → fold t pt (g (to c))) (λ c → fold t pt (g (to c)))
  ... | above i pi ti to = diagonal
    (λ c → fold i (⊲ᴮ-tr (hsuc hself) pi) (g (to c)))
    (λ c → fold t pt (g (to c)))

  instance-local : Local β B
  instance-local = record { fold = fold }
```

一般输入合法性仍未证明；尤其世界 ext 只完成 t=0 的 base keep，
不能以此自动推所有目标与回灌步的第一位置。这是当前明确证明义务。

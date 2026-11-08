# 任意先后实际样本共享较后合法世界

完成前缀定理给原chain逐点步进；将它送入统一World后，全部较早
采样都在较后同一个合法世界内比较。没有重置原H或其反馈链。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaSampleIndexed where
open import Data.Nat using (ℕ; suc; _≤_)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecFl using (Lg-flL)
open import OCF.Lean.GeneralOmegaConsumeIf using (code)
open import OCF.Lean.GeneralOmegaSampleIf using (module SampleWorlds)
open import OCF.Lean.GeneralOmegaSampleWorld using (World; legal; admitted; growth; instance-worlds)
import OCF.Lean.GeneralOmegaSampleRun as S
open import OCF.Lean.GeneralOmegaLegPrefixRun using (sample-indexed)

module Node (x : LH) (κ : K (Lv x)) (f : E (Lv x) κ → HB (Lv x)) where
  open S.Node x κ f
  pair : ∀ {j n} → j ≤ n →
    Bd (Lv x) κ (code x κ (feedback j)) (world n) ×
    Bd (Lv x) κ (code x κ (feedback n)) (world n) ×
    Pr (Lv x) κ (world n) (code x κ (feedback j)) (code x κ (feedback n))
  pair p = SampleWorlds.pair instance-worlds x κ (sample-indexed H p)
  world-growth : ∀ {j n} → j ≤ n → _≤w_ (Lv x) (world j) (world n)
  world-growth p = growth x (sample-indexed H p)
  earlier-accessed : ∀ {j n} → j ≤ n → sample j ⊲[ world n ] hΩ κ f
  earlier-accessed p = bounded-source (sample-indexed H p)
  branches-ordered : LgB (hΩ κ f) → ∀ {j n} → j ≤ n → sample j ⊲[ world n ] sample n
  branches-ordered l p = branches-step l (sample-indexed H p)

module Floor (k : LH) (g : HB (Lv k) → LH) where
  module Original = S.Floor k g
  open Original.Actual
  source-steps : ∀ {j n} → j ≤ n → sample j ⊲[ world n ] sample n
  source-steps p = branches-step (Lg-flL (lΩ k g)) (sample-indexed H p)
```

准入与源枝步进都已实例化原完整lΩ地板。source-steps的世界随右项
变化，不可误读为某个固定world内的全枝列；实际输出值仍仅使用
SampleRun.sample-value，不假定run保第一位置。

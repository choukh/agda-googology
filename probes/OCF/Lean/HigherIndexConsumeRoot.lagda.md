# 原完整高层闭项的完整Old.TΩ1下界

沿原最高Ω及两个实际低指标的首反馈进入第三节点；第三节点是原
前缀组件2的地板，不将动态低界错误重置成0。该节点的所有反馈都
编码为低层pure(leg d)，故完整旧纯轨道覆盖适用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeRoot where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.LHRecTy using (Lv; lΩ)
open import OCF.Lean.LHRecLay using (lvl)
open import OCF.Lean.HigherIndexFoldIf using (k; g)
open import OCF.Lean.HigherIndexConsumeCode using (from; pure)
open import OCF.Lean.HigherIndexConsumePositive using (old-act; positive; mul-partial)
open import OCF.Lean.HigherIndexConsumeLowest using (old-compare)
open import OCF.Lean.HigherIndexConsumeTrace
import OCF.Lean.HigherIndexConsumeDiagonal as D
import OCF.Lean.HigherIndexConsumeClosed as C
import OCF.Lean.Fold1 as Old

module N = Node third-node
bare : Cd → State
bare d = state N.nβ N.nlb N.nB N.nlB (N.branch e) (proj₂ N.cert e tt)
  where
  e = from (lΩ k g) N.kind (pure (Lv (lvl (lΩ k g) N.kind)) d)
reader : Cd → Cd
reader d = result (bare d)
reader-lower : ∀ d → old-act d ≤ᵛ reader d
reader-lower hz = positive (State.β (bare hz)) (State.lb (bare hz))
  (State.B (bare hz)) (State.lB (bare hz)) (State.tree (bare hz)) (State.support (bare hz))
reader-lower (hs d) = l≤ (λ n → ≤l n (mul-partial (reader-lower d) n))
reader-lower (hl f) = l≤ (λ n → ≤l n (reader-lower (f n)))
reader-lower (hΩ () f)

action : ∀ d → old-act d ≤ᵛ result (probe d third)
action d = ≤-trans (old-compare (Data.Unit.tt , hz) (inflation d)) (reader-lower (leg d))
  where
  import Data.Unit
  open import Data.Product using (_,_)

module Third = D.Cover (λ d → result (probe d third)) action
third-whole : Old.TΩ1 ≤ᵛ result third
third-whole = Third.whole

raw-lower : Old.TΩ1 ≤ᵛ C.raw
raw-lower = ≤-trans third-whole
  (≤-trans (advance-lower (advance (advance initial)))
    (≤-trans (advance-lower (advance initial)) (advance-lower initial)))
closed-lower : Old.TΩ1 ≤ᵛ C.tree
closed-lower = ≤-trans raw-lower C.raw-lower
```

closed-lower比较两个完整闭项，非有限样本、非只比较坐标，也没有用
增长率反推序数。尚未给本tree的EBO下界或统一上界；全Ω直接坍缩这一
新算法的更高值义务仍在，不能从本下界读成ψ₀Λ。

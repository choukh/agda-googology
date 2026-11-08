# 原完整ΛL闭项覆盖旧第一可数参照

原闭项仍使用完整flL ΛL。这里只提取其真实第1分量证明下界，并且
比较全部旧TΩ1轨道、输出和；不把这条下界当作ψ₀Λ验收完成。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaConsumeValueClosed where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.LHRecTy using (Lv)
open import OCF.Lean.LHRecLay using (ΛL; twL)
open import OCF.Lean.LHRecFl using (ΣF)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.HigherIndexConsumePositive using (old-act)
open import OCF.Lean.HigherIndexConsumeLowest using (old-compare)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Align.GeneralOmegaConsumeValuePure
import OCF.Lean.HigherIndexConsumeDiagonal as Diagonal
import OCF.Lean.GeneralOmegaConsumeClosed as Closed
import OCF.Lean.Fold1 as Old

encoded : Cd → HB (Lv ΛL)
encoded d = ι 1 (up (hz ⊞ pure S⊥ d))
encoded-pure : ∀ d → Pure d (encoded d)
encoded-pure hz = pz
encoded-pure (hs d) = ps (encoded-pure d)
encoded-pure (hl f) = pl (λ n → encoded-pure (f n))

module Prefix (A : HB (Lv ΛL)) where
  branch : Cd → Cd
  branch d = run ΛL (A ⊞ encoded (leg d))
  action : ∀ d → old-act d ≤ᵛ branch d
  action d = ≤-trans (old-compare (tt , hz) (inflation d))
    (pure-suffix ΛL (encoded-pure (leg d)) A)
  module Cover = Diagonal.Cover branch action

first : Old.TΩ1 ≤ᵛ run ΛL (ΣF twL 1)
first = Prefix.Cover.whole hz
old≤raw : Old.TΩ1 ≤ᵛ Closed.raw
old≤raw = ≤l 1 first
old≤tree : Old.TΩ1 ≤ᵛ Closed.tree
old≤tree = ≤-trans old≤raw Closed.raw-lower
```

Prefix.Cover的coordinates、outputs、sums对所有自然数成立，新链仍从1
开始，旧链从0开始。最外层仅选择原第1分量；完整源地板和最终闭项
未被替换。此处没有EBO阶段2或全部阶段覆盖，也没有新闭项的上界。

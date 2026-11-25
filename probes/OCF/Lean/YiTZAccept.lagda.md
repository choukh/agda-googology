# 树侧比较到第 0 项的末端接线
验收文件；条件定理，树侧 Bound 仍未实填。
记号值仅在末端调用已有 YiMTValue.k1ᶻ；颈结点出口复用 YiC0Reduce，不重证旧块对应。
本件导入闭包含记号与旧块；不把它导入树侧证明。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTZAccept where
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTVRead as R
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiMTValue as MV
import OCF.Lean.YiC0Reduce as CR
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiTZLocal as T
import OCF.Align.Level as L
import OCF.Align.Value as W

module Actual = T.At CR.o-neck
opaque
  output-wire : Actual.output ≡ CR.neck-out
  output-wire = trans Actual.output-eq (sym CR.neck-out-eq)

read-bound : {x y : B.Tr B.zero} → V.val B.zero x V.≼ V.val B.zero y → K.readRW x W.≼ K.readRW y
read-bound {x} {y} p = W.≼-trans (W.≅→≼ (L.≅-sym (R.read-val x)))
  (W.≼-trans (R.readV-mono p) (W.≅→≼ (R.read-val y)))
source-to-neck : Actual.Bound → K.readRW (MT.twᶻ 1) W.≼ K.readRW (proj₁ CR.neck-out)
source-to-neck p = subst₂ W._≼_ (cong K.readRW T.source-eq)
  (cong (λ t → K.readRW (proj₁ t)) output-wire)
  (read-bound {x = proj₁ T.source} {y = proj₁ Actual.output} p)

neck-low : Actual.Bound → CR.NeckLow
neck-low p = W.≼-trans (MV.k1ᶻ CR.hc₀)
  (W.≼-trans (CS.rr≼ (MT.twᶻ 1)) (source-to-neck p))
first-row : Actual.Bound → UL.FirstRow
first-row p = CR.first-row (neck-low p)
from-cover : Actual.Cover → UL.FirstRow
from-cover p = first-row (Actual.cover→bound p)
```

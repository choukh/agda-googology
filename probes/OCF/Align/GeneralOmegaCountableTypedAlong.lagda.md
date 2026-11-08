# 原保留种类沿路的坐标读回

直接消费原 along/frA，不把两个位置证明视为相等。目标种类的秩
与沿该条路径取出的低层严格对应；这是 keep 的反向坐标一步，
不是任意两份低层合法证之间的搬运。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedAlong where
open import Data.Unit using (tt)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F; module C)
open import OCF.Lean.GeneralOmegaCountableObserveClass using (omega; omega-legal)
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedClass using (cast)
open import OCF.Align.GeneralOmegaCountableTypedFloor using (floor-read)
open import OCF.Lean.GeneralOmegaCountableNextCapturePoint using (pointFloor)
import OCF.Align.Level as L

along-rank : ∀ {i t : Cd} (p : hs i ⊲ t) lt →
  rank t lt (C.along p) ≡ height i (lgB⊲ p tt lt)
along-rank hself lt = refl
along-rank (hsuc p) lt = along-rank p lt
along-rank (hlim n p) lt = along-rank p (proj₂ lt n)
along-rank (hLim {κ = ()} e p) lt

along-read : ∀ {i t : Cd} (p : hs i ⊲ t) lt {x e} →
  Coord t lt (C.along p) x e →
  Read i (lgB⊲ p tt lt) (canonical i (lgB⊲ p tt lt))
    (cast (along-rank p lt) x) (C.frA p e)
along-read hself lt r = r
along-read (hsuc p) lt r = along-read p lt r
along-read (hlim n p) lt r = along-read p (proj₂ lt n) r
along-read (hLim {κ = ()} e p) lt r

-- 真正非有限低层坐标：ω整个逐点地板，经其后继新增种类读回。
omega-coordinate : Read omega omega-legal (canonical omega omega-legal)
  (L.Ω (height omega omega-legal)) (C.frA {S⊥} {omega} hself (pointFloor omega))
omega-coordinate = along-read {omega} {hs omega} hself omega-legal
  (floor-read omega omega-legal)
```

两个结构定理对所有原可数高度和全部原路径成立，实例保留完整ω地板。
若源cl秩路径与目标保留路径诱导出不同合法证，本篇没有将它们合并；
后续需要显式旧层同构下的Read运输，不能省略tr⁻。

# 冻结的完整新闭项严格高于 BTBO

使用原高源中真正的闭包站，而不只选两层链的最低分量。该站的种子
覆盖低行，第二个真实输出为正，故严格超过低行；再沿原两层链入终点。
这里只给严格下界，不把它写成 ψ₀(Ω_{Ω+1}) 或原 EmbVV 高值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueHighStrict where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Align.LadderOrdBase using (clos)
open import OCF.Align.LadderOrdPos using (HB; end)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
open import OCF.Align.LadderOrdTree (HB ω²ᶜ)
open import OCF.Align.ValueJudgeBase
import OCF.Align.TotalValueBuildHighActual as H
import OCF.Align.TotalValueBuildHighChain (HB ω²ᶜ) as C
import OCF.Align.TotalValueClosingStrict (HB ω²ᶜ) as G
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Accept

first-closing : H.inner zero <ᴸ H.inner 1
first-closing = tt
first-closing-view : view (H.inner 1) ≡ clos first-closing
first-closing-view = refl

strict-lower : suc N.BTBOᴵ ≼ Accept.read (proj₁ Final.closed)
strict-lower = ≼-trans (s≼s H.base-lower)
  (≼-trans (G.closing-strict first-closing first-closing-view)
    (≼-trans (C.component (H.outer zero) H.inner H.inner-path H.inner-view 1)
      (≼-trans (C.component end H.outer H.outer-path H.outer-view zero)
        Accept.original-lower)))
```

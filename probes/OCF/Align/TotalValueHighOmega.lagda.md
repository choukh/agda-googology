# 原完整新闭项的 BTBO 加 ω 下界

使用同一真实闭包站的全部输出正性，而非只用第二支。这里仍只给
下界，没有把有限加法增量读作更高Ω下标的折叠层。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueHighOmega where
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Align.LadderOrdBase using (HtB; clos)
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueClosureOmega using (plus-omega; plus-omega-mono)
import OCF.Align.TotalValueClosureOmega as O
import OCF.Align.LadderOrdTree as Tree
import OCF.Align.ValLabLadder as Val
import OCF.Align.TotalValueClosingStrict as Strict
import OCF.Align.TotalValueBuildHighChain as Chain
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

module Closing (S : HtB) where
  open Tree S
  open Val S using (e₀; ev₀; rowC-eq)
  module H = Chain S
  module G = Strict S
  module Row {n m} (r : n <ᴸ m) where
    module X = G.Row r
    c = X.Parts.c X.parts
    t = X.Parts.t X.parts
    g = X.Parts.g X.parts
    module N = O.Node c t g t g
    lower : plus-omega (H.value n) ≼ A.read (R.run X.raw)
    lower = subst (λ z → plus-omega (H.value n) ≼ A.read (R.run z))
      (sym (X.Parts.shape X.parts))
      (N.lower (H.value n) X.seed-lower X.next-positive)
  closing-omega : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r →
    plus-omega (H.value n) ≼ H.value m
  closing-omega r ve = subst
    (λ x → plus-omega (H.value _) ≼ A.read (R.run (toZ (ψ̄ᵠ ok₀ e₀ x ev₀ zero))))
    (sym (rowC-eq r ve)) (Row.lower r)

open import OCF.Align.LadderOrdPos using (HB; end)
open import OCF.Align.LadderOrdCode using (ω²ᶜ)
import OCF.Align.TotalValueBuildHighActual as H
import OCF.Align.TotalValueHighStrict as F
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Accept
module C = Chain (HB ω²ᶜ)
module G = Closing (HB ω²ᶜ)

omega-lower : plus-omega N.BTBOᴵ ≼ Accept.read (proj₁ Final.closed)
omega-lower = ≼-trans (plus-omega-mono H.base-lower)
  (≼-trans (G.closing-omega F.first-closing F.first-closing-view)
    (≼-trans (C.component (H.outer zero) H.inner H.inner-path H.inner-view 1)
      (≼-trans (C.component end H.outer H.outer-path H.outer-view zero)
        Accept.original-lower)))
```

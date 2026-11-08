# 完整闭项加 ω 下界与生成保持的独立复核

这里加载冻结的实际算法定理，不另造闭项。加 ω 的下界来自同一
闭包的全部观察输出正性；不把它读作更高 Ω 下标的折叠值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegOmegaReview where
open import Data.Product using (proj₁)
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.ValueJudgeBase using (_≼_)
open import OCF.Align.TotalValueClosureOmega using (plus-omega)
import OCF.Align.TotalValueHighOmega as High
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Accept
import OCF.Align.TotalValueBuildRelatedGenTransport as Transport
import OCF.Align.TotalValueBuildRelatedGenPsi as Psi
import OCF.Align.TotalValueBuildRelatedGenPsiHeight as Height
import OCF.Align.TotalValueTailRecoveryPair as Pair
import OCF.Align.TotalValueTailRecoveryMarker as Marker
import OCF.Align.TotalValueTailRecoverySuccessor as Successor

actual-lower : plus-omega N.BTBOᴵ ≼ Accept.read (proj₁ Final.closed)
actual-lower = High.omega-lower

module At (S : HtB) where
  open Transport S public using (transport; transport-back)
  open Psi S public using (psi-gen)
  open Height S public using (height-gen)
  open Pair S public using (floor-pair; move-pair; back-pair; chain-pair)
  open Marker S public using (floor-marker; run-marker)
  module OriginalSuccessor = Successor S
```

后继模块的 coordinates-gen 覆盖原 chain 的全部坐标；whole-clean
保留全部分支，逐字去掉当前 marker。它没有把原 ι 与下降侧 ι↓
配对，也没有由两端各有 Gen 推出两端相关。chain-pair 仍显式要求
一步配对条件；因此本入口不宣称全参数恢复或最高闭项的具名上界。

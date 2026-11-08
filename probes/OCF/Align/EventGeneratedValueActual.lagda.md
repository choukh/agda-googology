# 接回原 Ω₃² 闭项源的动态层

使用原 `top₃ Ω₃²`、原 Ωd 的事件回调、原从底 0 到底 1 的路径，
不删除三前缀。配对结论覆盖任意完整相关事件历史，不把动态层
等同成固定层。最终闭项的整个值模拟尚未由此得到。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventGeneratedValueActual where

open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([])
open import OCF.Align.CumReadCF using (azero; z⊲)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldClosed
import OCF.Align.EventGeneratedIf as G
import OCF.Align.EventGeneratedBuild as Build
open import OCF.Align.EventGeneratedValueReplay
import OCF.Align.EventGeneratedValueFirst as First

module Source = G.At κ₁ (λ c → three ⊞ nbᴱ hz (λ _ h → h ⊞ Ω₃ᴱ) c)
module F = First.At (top₃ Ω₃²) (Lg-top₃ Ω₃² Lg-Ω₃²) (o₁⁺ Ω₃²) (o₂⁺ Ω₃²)
open F.R

body : ∀ H → Bu (top₃ Ω₃²) (azero , H)
body H {W′} q l = Source.node (proj₁ W′) (proj₂ W′)

initial : ∀ H → (azero , H) ≤ (one , H)
initial H = z⊲ one , here

first-history : Hist → Hist
first-history H = hc (κcε accᴸ κ₁ (body H) (initial H) (tt , tt) hself Act
  (n0 ⨾ nw (initial H) n1) (F.entered tt) zero)

first-history-related : ∀ {H J} → HistoryShape H J →
  HistoryShape (first-history H) (first-history J)
first-history-related h = cons (event₁ tt (F.entered-related tt)) h

actual-pair : ∀ {H J} → HistoryShape H J →
  Source.Pair one (first-history H) (first-history J)
actual-pair {H} {J} h = Source.Generated.pair Build.closed-square one
  (first-history H) (first-history J) (replay κ₁ (first-history-related h))

-- 原闭项的空历史实例；没有以此替代上面的全历史字段。
initial-pair : Source.Pair one (first-history []) (first-history [])
initial-pair = actual-pair nil
```

`actual-pair.layers` 为后续异型数据关系提供两种原动态层的 Shape；
两侧位置都指向同一原 source。它不是高层数据关系本身，更没有
把 RunNi/BNi/Chn 对这种对应的保持隐藏成已经成立。

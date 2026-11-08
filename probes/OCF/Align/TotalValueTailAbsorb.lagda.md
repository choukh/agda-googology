# 累计前驱嵌入的值读回及下一次折叠吸收

V3 给的有界前驱嵌入不只是可回灌数据，也能按原 Ordᴰ 结构读成值界。
后继的所有旧前驱先进入 top 的像，再由该像的严格界进入目标。
极限逐支限制原映射，未假设映射逐字保持树构造子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailAbsorb where
open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueTailPureUpper using (readD)
open import OCF.Align.TotalValueBuildStrict using (SV)
import OCF.Align.TotalValueCumulativeAbsorb as V
import OCF.Align.TotalValueCumulativeEb as E
module T = E.Blocks V.𝕋₀

eb-sound : ∀ a {y} → T.Eb a y → readD a ≼ y
eb-sound B.zero e = z≼
eb-sound (B.suc a) e = ≼-trans (s≼s (eb-sound a restricted))
  (≺→s≼ (T.below e B.zero))
  where
  restricted : T.Eb a (T.map e B.zero)
  restricted = record
    { map = λ p → T.map e (B.suc p)
    ; below = λ p → T.mono e (B.suc p) B.zero p
    ; mono = λ p q r → T.mono e (B.suc p) (B.suc q) r
    ; coh = λ p q r → T.coh e (B.suc p) (B.suc q) r }
eb-sound (B.lim f st) e = l≼ (λ n → eb-sound (f n) (record
  { map = λ p → T.map e (B.lim n p)
  ; below = λ p → T.below e (B.lim n p)
  ; mono = λ p q r → T.mono e (B.lim n p) (B.lim n q) r
  ; coh = λ p q r → T.coh e (B.lim n p) (B.lim n q) r }))

cumulative-absorbed : ∀ {a} → SV a →
  readD (S.ordᴰ (V.bkᴵ a)) ≼ ψ⁰ (Ω a)
cumulative-absorbed sa = eb-sound _ (V.V3 sa)
```

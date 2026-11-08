# 全 Q 输出严格性与搬运域的独立复核

此入口只消费冻结结果，不修改原 Q、运行器或成品。全 Q 定理保留
实际观察子树的全分支；闭包 raw seed/g 决定分支，但不被误当成输出。
最高源严格性实填，外部参照值界仍是 final-upper 的显式前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegGeneratedReview where
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Align.TotalValueBuildStrict using (SV)
import OCF.Align.LadderOrdTree as T
import OCF.Align.TotalValueTailHighGenerated as G
import OCF.Align.TotalValueTailHighFinal as H
import OCF.Free.TotalOrbitRun as R
import OCF.Align.TotalValueTransportSuccessor as Transport

module At (S : HtB) where
  open T S
  all-output : ∀ {m c φ χ w ℓ} (ok : Ok w) (e : Eh h₀ m w χ)
    (x : Q m c φ χ) (ev : Ev ℓ φ) (p : zero <ᴵ ℓ) →
    SV (R.run (toZ (ψ̄ᵠ ok e x ev p)))
  all-output = G.output-sv S

  -- 搬运只保原关系；不把两个程序断言为命题相等。
  open Transport S public using (successor-marker; successor-marker-back)

highest : SV H.native
highest = H.high-sv

open H public using (final-upper)
```

Regular 的 rc 量化实际 observer 的各个 η/e；其 value 按原 Trace.bound
实例化，不假定坐标本身 SV。qi 与两类 Ω 的证明仍使用完整原 iter/chain，
非恒定或首支替代。后继搬运 helper 只给 Rq，Ω 坐标往返通过 out-intoU
逐点等式处理，无函数外延，也没有任意 raw 自相关前提。

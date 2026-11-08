# 完整高源分解与底行完成的独立复核入口

保留两类不同结论：最高原对象的整树同形分解；底行整个新输出在
最后合法化之后的 BTBO 精确值。后者的前提均由实际底行实填，不能
把同一个上界外推到最高闭项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegTailHighReview where
open import Data.Product using (proj₁; _,_)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Align.ValueJudgeBase
import OCF.Align.LadderOrdTree as T
import OCF.Align.TotalValueTailHighBaseFinal as Base
import OCF.Align.TotalValueTailHighShape as High
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Read
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Free.TotalOrbitRun as R
import OCF.Free.LiteralCompletion as C
open import OCF.Lean.FrozenWorldLift using (Same)

whole-shape : Same (proj₁ Final.closed)
  (C.leg (Final.forget High.double-output))
whole-shape = High.closed-shape

module At (S : HtB) where
  open T S
  completed-base : ∀ {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
    (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) →
    N.BTBOᴵ ≈ᵛ Read.read (C.leg (Final.forget
      (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p)))))
  completed-base ok env ev p =
    Base.Actual.lower S ok env ev p , Base.Actual.upper S ok env ev p
```

检查要点：chain 的第零项是原 𝟏L 经 ψ̄ 与新 run 的完整读回，非
被替换成数值一。BaseFinal 的 SV、BTBO 的 HS/St 和外部上界均实际
构造；其完成控制经旧累计嵌入 V2/V3，而不是一般 leg 值单调律。

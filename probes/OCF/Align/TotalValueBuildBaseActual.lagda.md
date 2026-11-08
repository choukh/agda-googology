# 原完整 base 新运行覆盖旧 BTBO 参照闭包

累计嵌入提升已实填：V1 → V2 → V3 消费两端遗传严格性，允许新反馈
多走一步。这里消除 BaseWhole 的最后参数，得到原全部 HtB/源高度/
合法环境的无条件结论。没有更改 rowB、run、坐标或完成算法。
该结论尚未沿更高 rowC 的 cap/ι↓ 传到完整 ω² 端行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildBaseActual (S : HtB) where
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.OrdLabZUniform using (Uniform)
open import OCF.Align.ValueJudgeBase using (_≼_)
import OCF.Align.TotalValueBuildBaseWhole S as W
import OCF.Align.TotalValueCumulativeLift as L
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.TotalOrbitRun as R

module Full = W.From (λ {a} {b} sa sb v → L.lift a b sa sb (Uniform b) v)

whole : ∀ {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) →
  N.BTBOᴵ ≼ A.read (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p)))
whole ok env ev p = Full.Actual.whole ok env ev p
```

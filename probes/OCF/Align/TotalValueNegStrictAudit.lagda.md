# 严格终点下界与底行精确值的独立审查

ValueJudgeBase 的严格值关系定义为后继的弱值界，但该关系已有对全部
Ordᶜ 的良基性与反自返定理。下面明确导出终点不能反向落入 BTBO，
并把全参数 rowB 的两向界组装为值等价。没有假设任何回调保值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueNegStrictAudit where
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary using (¬_)
open import OCF.Free.Level
open import OCF.Align.ValueJudgeBase
import OCF.Align.TotalValueHighStrict as High
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Accept

no-reverse : ∀ {a b : Ordᶜ zero} → suc a ≼ b → ¬ (b ≼ a)
no-reverse {a} h q = ≺ᵛ-irrefl a (≼-trans h q)

not-btbo-upper : ¬ (Accept.read (proj₁ Final.closed) ≼ N.BTBOᴵ)
not-btbo-upper = no-reverse {a = N.BTBOᴵ}
  {b = Accept.read (proj₁ Final.closed)} High.strict-lower

open import OCF.Align.LadderOrdBase using (HtB)
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
import OCF.Align.LadderOrdTree as T
import OCF.Align.TotalValueBuildBaseActual as Lower
import OCF.Align.TotalValueTailBaseWholeUpper as Upper
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

module Base (S : HtB) where
  open T S
  exact : ∀ {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
    (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) →
    N.BTBOᴵ ≈ᵛ A.read (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p)))
  exact ok env ev p = Lower.whole S ok env ev p , Upper.whole-upper S ok env ev p
```

这里没有终点的具名上界；原高源中实际闭包站的严格增量保证它不能
与这个底行同值。反自返无需额外合法性前提，因而没有遗漏待填证书。

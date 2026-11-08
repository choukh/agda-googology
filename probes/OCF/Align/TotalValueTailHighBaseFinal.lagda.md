# 完整原 base 的最后完成仍与 BTBO 同值

这是真实无限反馈实例，不另选替代运行器。原 rowB 的所有新反馈与
累计输出先由前文夹到 BTBO；再以该固定外部参照吸收 Literal.leg。
本篇不推出高端行同样有 BTBO 上界（它已有严格超 BTBO 下界）。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailHighBaseFinal (S : HtB) where
open import OCF.Lean.CRwBase using (Cd)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_)
open import OCF.Align.OrdLabZLevel
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueBuildStrict using (St-γ)
open import OCF.Align.TotalValueBuildStrictBase using (St; stl)
open import OCF.Align.TotalValueTailHighExternal using (external-upper)
import OCF.Align.TotalValueGammaBounds as G
import OCF.Align.TotalValueCumulativeAbsorb as V
import OCF.Align.TotalValueBuildBaseOrbit S as Orbit
import OCF.Align.TotalValueTailBaseWholeUpper S as Upper
import OCF.Align.TotalValueBuildBaseActual S as Lower
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.LiteralCompletion as C
open import OCF.Align.RadicalValueNativeFinal using (forget)
import OCF.Align.RadicalValueNativeAccept as Read

btbo-legal : HS N.BTBOᴵ
btbo-legal = hl (λ n → N.cert (suc n)) (λ n → V.≺→⊑₀ (G.strict (suc n)))
btbo-strict : St N.BTBOᴵ
btbo-strict = stl (λ n → St-γ (suc n)) (λ n → ≺→s≼ (G.strict (suc n)))
btbo-next : ψ⁰ (Ω (toLevel N.BTBOᴵ btbo-legal)) ≼ N.BTBOᴵ
btbo-next = l≼ (λ n → ≼l (suc n) (≼-refl _))

module Actual {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) where
  native : Ordᴵ
  native = R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p))
  completed : Cd
  completed = C.leg (forget native)
  upper : Read.read completed ≼ N.BTBOᴵ
  upper = ≼-trans (external-upper native (Orbit.Actual.actual-whole ok env ev p)
    N.BTBOᴵ btbo-legal btbo-strict (Upper.whole-upper ok env ev p)) btbo-next
  lower : N.BTBOᴵ ≼ Read.read completed
  lower = ≼-trans (Lower.whole ok env ev p)
    (≼-trans (≅→≼ (Read.forget-shape native))
      (Read.read-lower (Read.inflation (forget native))))
  exact : (N.BTBOᴵ ≼ Read.read completed) × (Read.read completed ≼ N.BTBOᴵ)
  exact = lower , upper
```

actual-whole 的 SV、旧 BTBO 的 HS/St、whole-upper 都在 Actual 中
实填，无保值或吸收假设。最终树与实际未完成 base 输出因此同值；
其基本列并不相同，未比较 FGH。完整最高 Final 的上界仍需高行
回灌的外部参照，以及其实际 SV 或相应更细的吸收证据。

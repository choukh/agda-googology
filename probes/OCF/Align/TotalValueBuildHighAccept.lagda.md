# 冻结成品的具名 ψ₀(Ω_Ω) 下界

标签只标参照树，不进入成品定义、合法性或新运行器。完整原 NC
参照已由既有 BTBO-label 验收；本篇把其整个值下界接到实际未改的
RadicalValueNativeFinal.closed。尚不宣称保住旧 EmbVV 更高端值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildHighAccept where
open import Data.Product using (Σ; _×_; _,_; proj₁)
open import OCF.Free.Level
open import OCF.Align.ValueJudgeBase using (_≼_)
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.OrdLabZLabel using (BTBO-label)
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.EBO as E
import OCF.Align.RadicalValueNativeFinal as Final
import OCF.Align.RadicalValueNativeAccept as Accept
open import OCF.Align.TotalValueBuildHighActual using (closed-lower)

reference : Ordᶜ zero
reference = N.BTBOᴵ

reference-label : Lab reference (E.EBOψ 2)
reference-label = BTBO-label

reference-lower : reference ≼ Accept.read (proj₁ Final.closed)
reference-lower = closed-lower

named-lower : Σ (Ordᶜ zero) (λ X →
  Lab X (E.EBOψ 2) × X ≼ Accept.read (proj₁ Final.closed))
named-lower = reference , reference-label , reference-lower
```

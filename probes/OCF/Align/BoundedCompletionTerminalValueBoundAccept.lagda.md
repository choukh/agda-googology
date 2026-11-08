# 新严格下界在既有ε₀参照上的读法

验收专用。将实际双Ω输出得到的严格下界接到已通过Lab参照验收的
ε₀，明确给出ε₀·ω+1的下界；不将它升级命名为ψ₀(Ω₂)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionTerminalValueBoundAccept where
open import OCF.Lean.CRwBase using (hl)
open import OCF.Lean.Fold1If using (mul; s≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (mul-≤)
import OCF.Lean.Fold1 as Old
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as S
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionCalibrateAccept as A
import OCF.Align.BoundedCompletionValueAcceptPairStrength as P
import OCF.Align.BoundedNativeCompletionClosed as C

reference : L.Ordᶜ L.zero
reference = L.suc A.epsilon-times-omega-reference

reference≤C : reference S.≼ B.read C.tree
reference≤C = S.≼-trans (S.s≼s A.reference-multiples≤)
  (S.≼-trans
    (B.read-mono (s≤s (l≤ (λ n → ≤l n (mul-≤ A.epsilon≤A n)))))
    (B.read-mono P.strict-old-multiple≤C))
```

左边是既有ε₀参照的标准重复加法极限再取后继。右边始终原合法C。
更强的未命名闭树下界hs(P.Strict.BB₀)仍在PairStrength中保留；本篇只
给易对照的粗界，没有舍弃那个完整动态回灌结果。

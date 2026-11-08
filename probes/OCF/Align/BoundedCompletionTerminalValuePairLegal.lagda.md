# 动态双Ω下界本身的合法性

下界不只是一棵raw树。这里直接用原Fold1的Lg*加法闭包与末段合法性，
证明本轮选中的完整双Ω输出是合法可数布劳威尔树。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionTerminalValuePairLegal where
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1Base using (Lg*; ℓT; Lg*-⊞; lg-top*)
import OCF.Align.BoundedDescentValueBridgeTerminal as Last
import OCF.Align.BoundedCompletionValueAcceptPair as P
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)

pair-input-legal : Lg* (ℓT (hs hz)) P.pair
pair-input-legal = Lg*-⊞ (ℓT (hs hz)) (floor 0) (floor 0)
  (lg-top* (hs hz)) (lg-top* (hs hz))

pair-output-legal : LgB P.pair-output
pair-output-legal = Last.terminal-legal P.pair pair-input-legal
```

与Pair.pair≤C合起来交付合法闭项及其实际值下界关系。此处没有由
较大树C合法反推其raw下界合法，也没有对所有规范输出作合法性声称。

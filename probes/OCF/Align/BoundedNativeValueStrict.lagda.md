# 原可数输出严格超过旧闭项的 raw 值

上一篇已将旧闭项放入原外层第1项。原第2项仍是末段折叠的实际输出，
该函数对每棵 raw 输入都至少输出1；因而部分和给出严格后继下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeValueStrict where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans; ⊞-≤ʳ)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedNativeValueFirst
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeFloor as N
import OCF.Lean.Fold1 as Old

terminal-positive : ∀ b (h : HB (Native hz)) → one ≤ᵛ T.fold b h
terminal-positive b hz = s≤s z≤
terminal-positive b (hs h) = ≤l 0 (terminal-positive b h)
terminal-positive b (hl f) = ≤l 0 (terminal-positive b (f 0))
terminal-positive b (hΩ (inj₁ ()) g)
terminal-positive b (hΩ (inj₂ _) g) = ≤l 0 (terminal-positive b (g b))

old-in-first-sum : Old.TΩ1 ≤ᵛ Outer.C.oO 1
old-in-first-sum = ≤-trans old-below-component
  (≤-trans first-lower (right≤ (Outer.C.oo 0) (Outer.C.oo 1)))

strict-old-lower : hs Old.TΩ1 ≤ᵛ N.countable-output
strict-old-lower = ≤l 2 (≤-trans (s≤s old-in-first-sum)
  (⊞-≤ʳ (Outer.C.oO 1)
    (terminal-positive (proj₂ (Outer.C.cw 2)) (T.native-branch (Outer.C.ce 2)))))

not-bounded-by-old : N.countable-output ≤ᵛ Old.TΩ1 → ⊥
not-bounded-by-old p = ¬s≤ᵛ Old.TΩ1 (≤-trans strict-old-lower p)
```

这是关于原始 countable-output 的定理，不含合法性前提，故只作 raw 值
验收。它排除了该输出的值不超过旧 TΩ1 的判断；没有给 EBO 下界或精确
记号值，也没有由 raw 值关系推出输入合法性。

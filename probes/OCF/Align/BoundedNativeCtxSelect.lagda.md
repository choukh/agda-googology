# 共界比较选择的局部修复实验

对有Component视图的同一Source输入，c⊲t时统一Ctx；其余分支明确
调用原fold，未声称该部分已修复或全函数保合法。旧NativeRun不改。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeCtxSelect where
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf using (Path)
import OCF.Align.BoundedNativeFoldRun as OldRun
open import OCF.Align.BoundedNativeCtxRepair
import OCF.Align.BoundedNativeViewNegOutput as Old
open import OCF.Align.BoundedNativeViewNegCopies using (one; B; pc; legal-B)

experiment : ∀ B → LgB B → ∀ c → c ⊲ B → ∀ t → t ⊲ B →
  ∀ a x → Component c a x → Path B x → HB (Native t)
experiment B lB c pc t pt a x shape path with cmpB pc pt tt lB
... | inj₂ q = repair q shape
... | inj₁ hself = repair hself shape
... | inj₁ (hsuc q) = OldRun.fold B lB t pt x path
... | inj₁ (hlim n q) = OldRun.fold B lB t pt x path
... | inj₁ (hLim {κ = ()} b q)

output : HB (Native B)
output = experiment B legal-B one pc B hself Old.floor Old.input
  (original-component Old.floor) (Old.put-path Old.floor)
legal-output : LgB output
legal-output = legal-repaired
```

这里的output通过实际cmpB结果选择repair，不是手动另挑一个有利目标。
与原反例相同的合法B、源/目标路径、input及Path均保留。仅有这一已证
保留区域与具体输入合法结论；c>t仍旧算法，没有推断整体实验保合法。

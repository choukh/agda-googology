# leg 不排除实际所需的目标拷贝冲突

把先前常值极限反例换成真实 root 回灌所产生的累加极限。
原采样基树 lim(const1) 合法；L=0⊞leg(该树) 的前两项为1、2。
本篇只证该目标上的原运行器反例，不声称它就是完整闭项的某棵输出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReachNegLeg where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.LHRecFl using (Lg-flL)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf using (Path)
open import OCF.Align.BoundedNativeFoldRun using (fold)
open import OCF.Align.BoundedNativeLegalWorld using (canonical; canonical-legal)
open import OCF.Align.BoundedNativeViewNegCopies using (one; D; legal-D; one-to-D)
import OCF.Align.BoundedNativeViewNegOutput as Old

raw : Cd
raw = hl (λ _ → one)
legal-raw : LgB raw
legal-raw = (λ n → hself) , (λ n → tt)
L : Cd
L = hz ⊞ leg raw
legal-L : LgB L
legal-L = Lg-⊞ hz (leg raw) tt (Lg-leg raw)
pc : one ⊲ L
pc = hlim 1 (hsuc hself)

W : Wd (Native L)
W zero = (tt , hz) , hz
W (suc zero) = ((tt , one) , D) , hz
W (suc (suc n)) = canonical _
legal-W : LgW (Native L) W
legal-W zero = (tt , tt) , tt
legal-W (suc zero) = ((tt , tt) , legal-D) , tt
legal-W (suc (suc n)) = canonical-legal _

put-path : ∀ a → Path L (Old.put a)
put-path hz = tt
put-path (hs a) = put-path a
put-path (hl f) = λ n → put-path (f n)
put-path (hΩ κ g) = pc , (λ c ad → put-path (g c))

output : HB (Native L)
output = fold L legal-L L hself Old.input (put-path Old.floor)
branch : HB (Native hz) → HB (Native L)
branch c = fold L legal-L L hself (Old.put (up c)) (put-path (up c))

no-repeat-zero : Ops.repeat (Native L) (hs hz) ⊲[ W ] hz → ⊥
no-repeat-zero ()
no-repeat-one : Ops.repeat (Native L) (hs hz) ⊲[ W ] hs hz → ⊥
no-repeat-one (hsuc p) = no-repeat-zero p
no-branch-path : branch (hs hz) ⊲[ W ] branch D → ⊥
no-branch-path (hLim hself p) = no-repeat-one p
no-legal-output : LgB output → ⊥
no-legal-output l = no-branch-path (proj₁ l legal-W one-to-D hself one-to-D)

legal-input : LgB Old.input
legal-input = Old.legal-input
```

前提均给实例。L的形状来自合法采样的leg，并没有通过任意裸下标比较构造。
未改原fold；仍未据此判定整个 NativeFloor.native-output 或 countable-output 不合法。

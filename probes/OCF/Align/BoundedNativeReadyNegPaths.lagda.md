# 相干世界仍不能消除任意Path的路由差异

同一个固定源节点逐项重复，Path在目标的第0和第1副本间切换。
本篇否定任意Path的相干Good保持，不涉及原θ-path是否具有必要的一致性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReadyNegPaths where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf using (Path)
open import OCF.Align.BoundedNativeFoldRun using (fold)
open import OCF.Align.BoundedNativeReadyGood using (Good)
open import OCF.Align.BoundedNativeZeroWorld using (seed)
open import OCF.Align.BoundedNativeViewNegCopies using (one; B; legal-B)
import OCF.Align.BoundedNativeViewNegOutput as X

path0 : ∀ a → Path B (X.put a)
path0 hz = tt
path0 (hs a) = path0 a
path0 (hl f) = λ n → path0 (f n)
path0 (hΩ κ g) = hlim 0 hself , λ e ad → path0 (g e)
paths : ℕ → Path B X.input
paths zero = path0 X.floor
paths (suc n) = X.put-path X.floor

input : HB Source
input = hl (λ _ → X.input)
legal-input : LgB input
legal-input = (λ n → hself) , (λ n → X.legal-input)
input-path : Path B input
input-path = paths
output : HB (Native B)
output = fold B legal-B B hself input input-path
first : HB (Native B)
first = fold B legal-B B hself X.input (paths 0)
second : HB (Native B)
second = fold B legal-B B hself X.input (paths 1)
V : Wd (Native B)
V = seed B (tt , hz)

no-first-zero : first ⊲[ V ] hz → ⊥
no-first-zero ()
no-first-one : first ⊲[ V ] hs hz → ⊥
no-first-one (hsuc p) = no-first-zero p
no-first-finite : ∀ n → first ⊲[ V ] Ops.partial (Native B) (λ _ → hs hz) n → ⊥
no-first-finite zero p = no-first-one p
no-first-finite (suc n) (hsuc p) = no-first-finite n p
no-first-repeat : first ⊲[ V ] Ops.repeat (Native B) (hs hz) → ⊥
no-first-repeat (hlim n p) = no-first-finite n p
no-first-second : first ⊲[ V ] second → ⊥
no-first-second (hLim hself p) = no-first-repeat p
no-first-second (hLim (hsuc hself) p) = no-first-one p

no-good-output : Good B output → ⊥
no-good-output l = no-first-second (proj₁ l (tt , tt) 0)
```

legal-input、input-path、legal-B与合法底世界(tt,0)都是具体实例。
输出甚至不满足seed域的相邻项步进。未否定实际native-output；此例的
Path逐项改选副本，原θ-path是否排除此行为须有独立证明，不能只靠seed-view。

下面填充同一原始输入的Mixed前提。证书也不排除路径逐项换副本，
所以不能据此宣称对任意Path的保持定理。

```agda
open import OCF.Align.BoundedNativeReadyGood using (floor-good)
import OCF.Align.BoundedNativeReadyMixed as M

put-mixed : ∀ a → Good one a → M.Mixed B (X.put a)
put-mixed hz l = tt
put-mixed (hs a) l = put-mixed a l
put-mixed (hl f) (st , l) =
  (λ lv n → X.put-position (st lv n)) , (λ n → put-mixed (f n) (l n))
put-mixed (hΩ κ g) (mo , l) = hlim 0 hself ,
  (λ lv e d p → X.put-position (mo lv e d p)) , (λ e le → put-mixed (g e) (l e le))

actual-mixed : M.Mixed B input
actual-mixed = (λ lv n → hself) , (λ n → put-mixed X.floor (floor-good one))
```

# 真实合法采样进入非零极限目标的最高反馈

这是一条实际展开定理，不是完整闭项非法的证明。合法采样 e=hs(hs raw)
经过原 root 的sh/nxt后，最高反馈坐标调用的目标恰为前篇L。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReachNegCall where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf
import OCF.Align.BoundedNativeFoldRun as R
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeTerminalReady as Ready
open import OCF.Align.BoundedNativeReachNegLeg using (raw; legal-raw; L)

e : Cd
e = hs (hs raw)
legal-e : LgB e
legal-e = legal-raw

ad = adm-sh {B = hz} e tt
shift : Cd
shift = sh₀ hz e
shift-shape : shift ≡ hs (hs L)
shift-shape = refl
bound : Cd
bound = nxt₀ hz shift ad
legal-bound : LgB bound
legal-bound = lg-nx ad tt
pzero : hz ⊲ bound
pzero = ⊲ᴮ-tr hself (nx-up ad)
ptarget : L ⊲ bound
ptarget = hsuc (hsuc (hsuc hself))

A : HB Source
A = N.θ (hs L)
body : HB (Native L) → HB Source
body c = A ⊞ ι (inj₂ (hs L)) (up c)
source-shape : N.θ shift ≡ hΩ (inj₂ (hs L) , inj₂ tt) body
source-shape = refl

path-source : Path bound (N.θ shift)
path-source = N.θ-path shift bound (hsuc hself)
path-body : ∀ c → Path bound (body c)
path-body c = proj₂ path-source c tt

coordinate : HB (Native L) → HB (Native L)
coordinate c = R.fold bound legal-bound L ptarget (body c) (path-body c)
point : HB (Native L) → HB (Native hz)
point c = R.fold bound legal-bound hz pzero (body c) (path-body c)

actual-sample : Ready.native-branch e ≡ diagonal coordinate point
actual-sample = refl
```

actual-sample 核对的是原 NativeFloor.native-output 的整个该分支，以及原
运行器使用的路径证明；没有换目标路径或复制fold。它说明leg合法化不能
排除非零极限目标L进入实际最高反馈。但是coordinate的输入含前缀A，
与ReachNegLeg里单独源分量地板反例不同，尚未证明这条实际反馈输出非法。
翻译账：只有原闭项的定义展开，不引入新规则或证书条件。

精确可达范围补充：e 是原 native-output 的一个合法坐标，尚未证明它等于
末段可数折叠的任何 Outer.ce n。因此“实际”仅指原闭项分支的定义展开，
不表示末段反馈已经采到了这个 e；外层采样可达仍是独立义务。

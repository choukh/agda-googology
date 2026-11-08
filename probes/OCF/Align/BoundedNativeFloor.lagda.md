# 原 P 地板的动态路径与实际下降项

输入就是现有 flL P，含所有原始可数坐标的分量，不截为固定界子族。
指标分支进入 e+1 后，θ(e)中的分量均有字面路径；这给实际动态Path实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeFloor where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
import OCF.Lean.CRwPath as CP
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecLay using (ΩL; _⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; Lg-flL; cxI; gcF)
import OCF.Lean.LHRecLeg as Leg
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)
open import OCF.Align.BoundedNativeFoldIf
import OCF.Align.BoundedNativeFoldRun as R
import OCF.Align.BoundedDescentValueBridgeTerminal as Last

module PathsTool = CP I₁

component-path : ∀ c B → c ⊲ B → ∀ (a : HB (Native c)) → Path B (ι (inj₂ c) a)
component-path c B p hz = tt
component-path c B p (hs a) = component-path c B p a
component-path c B p (hl f) = λ n → component-path c B p (f n)
component-path c B p (hΩ κ g) = p , λ e ad → component-path c B p (g e)

θ : Cd → HB Source
θ = Leg.New.θ (cxI lz (λ c → ls lz ⊕L upL lz c))
  (gcF (λ d → ι (inj₂ d) (flL (ls lz ⊕L upL lz d))))

θ-path : ∀ e B → e ⊲ B → Path B (θ e)
θ-path hz B p = tt
θ-path (hs e) B p = PathsTool.PH-⊞ Paths _ _
  (θ-path e B (⊲ᴮ-tr (hsuc hself) p))
  (component-path e B (⊲ᴮ-tr (hsuc hself) p) _)
θ-path (hl f) B p = λ n → θ-path (f n) B (⊲ᴮ-tr (hlim n hself) p)

input : HB Source
input = flL (ΩL (ls lz))
legal-input : LgB input
legal-input = Lg-flL (ΩL (ls lz))

input-path : ∀ B → Path B input
input-path B = tt , λ e ad → θ-path e (hs e) (hsuc hself)

native-output : HB (Native hz)
native-output = R.fold hz tt hz hself input (input-path hz)

countable-output : Cd
countable-output = Last.terminal native-output
```

`native-output` 与 `countable-output` 都由具体已定义函数计算，不含公理或接口参数。
尚未证明 native-output 满足末段所需 Lg*，也未证明 countable-output 合法与强度，
故它们目前是可运行研究闭项，不是已验收的成品候选。
与原地板的关系必须另证：保留指标时已将目标坐标 e 改送 sh₀ B e，不能
把本次动态路径实例或可运行性当作保值结论。

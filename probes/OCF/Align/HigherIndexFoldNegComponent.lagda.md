# 真实含Ω组件地板不能取得当前全raw路径证书

使用冻结HigherIndexFoldIf，输入是原组件注入与原flL，合法性由原定理
给出。否定当前Path对该输入的覆盖，不否定原输入合法、不否定新折叠
路线。问题在组件内部的指标仍按全raw分支、固定低世界取Path。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HigherIndexFoldNegComponent where
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecFl using (flL; Lg-flL; Lg-ι)
open import OCF.Lean.HigherIndexClassIf using (U)
open import OCF.Lean.HigherIndexFoldIf
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (no-successor-back)

omega : HB U
omega = flL k
legal-omega : LgB omega
legal-omega = Lg-flL k

B : HB U
B = hs omega
legal-B : LgB B
legal-B = legal-omega
component-path : ∀ β → omega ⊲[ tt , β ] B
component-path β = hsuc hself

input : HB Source
input = ι (inj₂ omega) (flL (g omega))
legal-input : LgB input
legal-input = Lg-ι (inj₂ omega) (flL (g omega)) (Lg-flL (g omega))

-- 原组件根的raw坐标2+β产生内部组件坐标1+β。
obstruction : ∀ β → Path β B input → hs β ⊲ β
obstruction β p = proj₁ (proj₂ (proj₁ (proj₂ p (hs (hs β)))))

no-input-path : ∀ β → Path β B input → ⊥
no-input-path β p = no-successor-back β (obstruction β p)

-- 低世界和公共高界都有合法实例，未用非法世界制造反例。
legal-low-world : ∀ β → LgB β → LgW U (tt , β)
legal-low-world β lb = tt , lb
```

任意合法β均可作为低界，例如β=0；高公共界B=hs omega合法，组件
omega有字面路径进入B，输入本身也合法。Path却要求内部raw分支在
原β处合法分类，坐标hsβ的可入证据不能给出。

这与HigherIndexFoldClosed的正面input=θ omega不冲突：那里最外指标
旧Ω有动态低界更新规则；这里指标嵌在组件之内，当前Path把其当作
普通组件节点。后续可研究继承的指标动态策略，不能据此关闭带证路线。

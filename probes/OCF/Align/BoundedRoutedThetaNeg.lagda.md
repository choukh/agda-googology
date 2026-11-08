# 严格对象自反尚不能覆盖原θ路由

原θ的同一旧前缀在相邻项中携带不同位置路径。即使其base种类的实际
决定不读取该差别，严格树-Path对的self也不会自动识别它们。
本篇检验的是新RoutedGood，不从其失败推出原输出不合法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedRoutedThetaNeg where
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedRoutedIf
import OCF.Align.BoundedNativeFloor as N

one : Cd
one = hs hz
L : Cd
L = leg (hl (λ _ → one))
v : Wd (Native hz)
v = tt , hz

no-zero : ∀ {p} → RoutedPos L v (N.θ one) p hz tt → ⊥
no-zero ()

no-step : RoutedPos L v
  (N.θ one) (N.θ-path one L (hlim 0 hself))
  (N.θ (hs one)) (N.θ-path (hs one) L (hlim 1 hself)) → ⊥
no-step (omegaR hself (sucR (omegaR hself p))) = no-zero p
no-step (omegaR (hsuc hself) (omegaR hself p)) = no-zero p

no-routed-theta : RoutedGood L (N.θ L) (N.θ-path L L hself) → ⊥
no-routed-theta r = no-step (proj₁ r (tt , tt) 0)
```

这里使用原θ与原θ-path，未替换实际路径。结论精确否定上述新证书对该
实例的覆盖；它不否定目标0的实际fold位置、Good或可数输出合法性。

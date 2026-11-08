# 稳定分支对前缀加法封闭

该定理对所有世界与稳定树成立，没有逐站前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldStableAdd where

open import OCF.Lean.Fab6Base using (hsuc)
open import OCF.Lean.NegFab6Idx
open import OCF.Lean.WorldStable
open import OCF.Lean.WorldAlgebra using (add-cong)

stable-add : ∀ {B} {a b : W B} → Stable a → Stable b → Stable (a ⊕ b)
stable-add sa stz = sa
stable-add sa (sts sb) = sts (stable-add sa sb)
stable-add sa (stl sb) = stl (λ n → stable-add sa (sb n))
stable-add sa (stn sb ub) = stn
  (λ e p → stable-add (stable-lift (hsuc p) sa) (sb e p))
  (λ e p q → add-cong (independent (hsuc p) (hsuc q) sa) (ub e p q))
```

这解决前缀进入分支时的证据稳定性；不意味着 Ω-分支按第一位置单调，
因而仍不是合法性证书或序数值定理。无新增构造子，无记号依赖。

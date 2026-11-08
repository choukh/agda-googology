# 原全保留与原前缀反馈的统一计算

仅提供原函数的Same计算证据；有向关系运输另由关系归纳，不把Same
当作函数外延或任意折叠同余。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformCompute where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.Lean.CRwBase
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeFoldRun
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteBridgeDecision
open import OCF.Align.BoundedCompletionFinitePlaceDecision
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionFiniteValueKeep
open import OCF.Align.BoundedCompletionFiniteValueRebuild using (self-keep)
open import OCF.Align.BoundedCompletionFiniteValueCompute using (same-partial)
import OCF.Align.BoundedCompletionFiniteValueFirst as Existing
open import OCF.Align.BoundedCompletionFiniteValueIf using (coordinate)
import OCF.Align.BoundedCompletionFiniteValueAffine as A
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ

F : ∀ n → HB (Native (num n)) → HB (Native (num n))
F n a = at n n {B = num n} (legal-num n) hself hself a

self-run : ∀ n a → Same (F n a) (A.Affine.Action.run (Native (num n)) a)
self-run n hz = ss zz
self-run n (hs a) = ll (same-partial (self-run n a))
self-run n (hl f) = ll (λ j → self-run n (f j))
self-run n (hΩ κ g)
  with decide {B = num n} {t = num n} hself (legal-num n) (raise hself (classify (num n) κ))
     | self-keep n κ
... | .(keep κ fr) | retained fr fe = oo (λ e → subst
  (λ d → Same (F n (g d)) (A.Affine.Action.run (Native (num n)) (g e)))
  (sym (fe e)) (self-run n (g e)))

coordinate-run : ∀ n c → Same (coordinate n c)
  (A.Affine.Action.run (Native (num n)) (Θ.model n ⊞ c))
coordinate-run n hz = Existing.Actual.up-run n (Θ.model n)
coordinate-run n (hs c) = ll (same-partial (coordinate-run n c))
coordinate-run n (hl f) = ll (λ j → coordinate-run n (f j))
coordinate-run n (hΩ κ g)
  with decide {B = num n} {t = num n} hself (legal-num n) (raise hself (classify (num n) κ))
     | decide {B = num (suc n)} {t = num n} (hsuc hself) (legal-num (suc n))
         (raise hself (raise (hsuc hself) (classify (num n) κ)))
     | up-component n n κ {B = num n} {B′ = num (suc n)}
         (legal-num n) (legal-num (suc n)) hself hself hself (hsuc hself)
     | self-keep n κ
... | .(keep κ fr) | .(keep κ fr) | kept .κ .fr | retained fr fe = oo (λ e → subst
  (λ d → Same (coordinate n (g d))
    (A.Affine.Action.run (Native (num n)) (Θ.model n ⊞ g e)))
  (sym (fe e)) (coordinate-run n (g e)))
```

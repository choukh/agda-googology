# 两个真实分类器的共同数值界接口

源与目标均保留同一num n公共界，Countable的原same/above仍分开。
above的反馈高度必须逐字是num k，不能仅凭值相等替换。分支坐标
逆送携异族遗传关系，不让任意源g接受Same。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteIf where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.GeneralOmegaCountableObserveIf as C
import OCF.Lean.GeneralOmegaFiniteObserveIf as F
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; num-legal)
open import OCF.Align.GeneralOmegaCountableFiniteRel

data Match {n m A A′} (p : F.Within n m) (pt : num m ⊲ num n)
  (Q : A → A′ → Set) : C.C.Dc C.F (num n) (num m) A → F.View n m A′ → Set where
  kept : ∀ {κ κ′ fr fr′} (k : Kind m κ κ′) →
    (∀ {a b} → Coord m k a b → Q (fr a) (fr′ b)) →
    Match p pt Q (C.C.keep κ fr) (F.keep κ′ fr′)
  same : ∀ {q to to′} → (∀ {a b} → Rel m a b → Q (to a) (to′ b)) →
    Match p pt Q (C.C.same to) (F.collapse m q to′)
  above : ∀ {k pr tr q to to′} → (∀ {a b} → Rel k a b → Q (to a) (to′ b)) →
    Match p pt Q (C.C.above (num k) pr tr to) (F.collapse k q to′)

record Classification : Set where
  field
    matched : ∀ {n m κ κ′} (p : F.Within n m) (pt : num m ⊲ num n) (k : Kind n κ κ′) →
      Match p pt (Coord n k) (C.classify (num n) (num-legal n) (num m) pt κ) (F.view p κ′)

one : Match (F.lower F.here) (hsuc hself) (Coord 1 high)
  (C.classify (num 1) (num-legal 1) (num 0) (hsuc hself) (inj₂ tt))
  (F.view (F.lower F.here) (inj₂ tt))
one = same (λ r → r)
```

one是原非零公共界的真实同层坍缩实例。全n分类桥须由原cl/dcl、
cmpB和沿途坐标函数证明，不由本记录的存在自动推出。

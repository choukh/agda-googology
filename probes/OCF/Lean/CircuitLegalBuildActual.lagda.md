# 原整源输出正规化后可在当前世界再次运行

直接消费 ThirdRunFamily 的整个原 Φ 输出族。没有用预给地板替换输出，
没有更换世界，也没有把 Gd 当成旧 desc 所要求的全 PH 族。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.CircuitLegalBuildActual where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb)
import OCF.Lean.ThirdFold as F
import OCF.Lean.ThirdRunFamilyBuild as Family
open import OCF.Lean.CircuitLegalBuildNormal using (normal-gd)

module Run (n : ℕ) (w : Wd (Sb n)) (lw : LgW (Sb n) w)
  (fb : HB (Sb n)) (M : HB (Sb n)) (lm : LgB M)
  (h : HB (Tw (Sb n) M)) (nd : F.Gd (Sb n) w lw M h) where
  module A = Family.Run n w lw fb M lm h nd

  normal-certificate : ∀ t (pt : t ⊲[ w ] M) b → A.F.Gd t (A.normal t pt b)
  normal-certificate t pt b = normal-gd n w lw t (lgB⊲ pt lw lm)
    (A.output t pt b) (proj₂ (A.run t pt b))

  -- 第二次调用完整原 Φ，允许所有 s⊲t 和当前 GT s 种子。
  again : ∀ t (pt : t ⊲[ w ] M) (b : A.F.GT t)
    s → s ⊲[ w ] t → A.F.GT s → A.F.GT s
  again t pt b s ps seed = A.R.Φ t (A.R.wfC t) (lgB⊲ pt lw lm)
    s ps seed (A.normal t pt b) (normal-certificate t pt b)

  shape-again : ∀ t pt b s ps seed → A.R.Sh (proj₁ (again t pt b s ps seed))
  shape-again t pt b s ps seed = A.R.Sh-Φ t (A.R.wfC t) (lgB⊲ pt lw lm)
    s ps seed (A.normal t pt b) (normal-certificate t pt b)

-- 非零真实输入覆盖全原底，不是常零源；整源定理不限制为这个实例。
module Nonzero (n : ℕ) (w : Wd (Sb n)) (lw : LgW (Sb n) w) where
  module A = Run n w lw hz (hs hz) tt (hs hz) tt
  normal-certificate = A.normal-certificate hz (hsuc hself)
  actual = A.again hz (hsuc hself)
```

该定理消去的是“同类型富合法化后是否仍有原当前 Gd”这一接线缺口。
下一扩张世界仍不能由本篇获得 Gd；已有 LegalTransport 的否定范围
不变。也没有证明第二次输出保第一次的序数值、或最终 EBO 覆盖。

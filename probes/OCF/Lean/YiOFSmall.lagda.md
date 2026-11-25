# 较小层号的偏移比较
不读记号；编译定理：输入 suc zero 时，源 Ω 折叠值不高于偏移层的 Ω 折叠值。
来源：YiTQSmall.one-two 与 YiTNRow.Actual zero；按 one → two → three 剥后继。
不把本实例外推到原 Offset 或 Cover。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOFSmall where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTNRow as R
import OCF.Lean.YiTQSmall as Q
import OCF.Lean.YiTYLocal as Y
import OCF.Lean.YiTZLocal as T
module A = R.Actual B.zero
module C = R.Actual (B.suc B.zero)
opaque
  unfolding Q.low Q.high Y.source-fold
  small-offset : V.val B.zero (Y.source-fold (B.suc B.zero))
    V.≼ V.val B.zero (proj₁ C.A.low)
  small-offset = V.≼-trans Q.one-two A.A.predecessor-low
```

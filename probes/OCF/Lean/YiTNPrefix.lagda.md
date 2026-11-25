# 偏移比较的首个前缀
不读记号；编译定理：标准 one 层的 Ω 折叠值不高于偏移源折叠值。
仅为固定前缀，不外推所有源累计前缀或 Cover。
来源：YiTQSmall.one-two 与 YiTNRow 的实际零孩子实例。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTNPrefix where
open import Data.Product using (proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTQSmall as Q
import OCF.Lean.YiTZSmall as Z
import OCF.Lean.YiTNRow as R
import OCF.Lean.YiTNShape as S
import OCF.Lean.YiTNShift as L
module A = R.Actual B.zero
opaque
  unfolding S.curve S.line Q.low Q.high Z.high
  first-prefix : V.val B.zero (proj₁ Z.high) V.≼ V.val B.zero (proj₁ L.Actual.folded)
  first-prefix = V.≼l 0 (V.≼-trans Q.one-two A.A.predecessor-low)
```

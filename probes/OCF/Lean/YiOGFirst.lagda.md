# 原 ActualMissing 的第 1 前缀已填
不读记号；编译定理：源累计前缀 1 的值不高于目标累计前缀 1。
全部 Base 路径与 β 前提均已实填；原 ActualMissing 的 n ≥ 2 部分尚未构造。
来源：YiOGBaseAll.base-transfer-one、YiOGTransfer.transfer-one、YiOGActual 的出口。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGFirst where
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiOGState as S
import OCF.Lean.YiOGActual as A
import OCF.Lean.YiOGTransfer as X
import OCF.Lean.YiOGBaseAll as C
same-level-one : A.SameLevelMissing
same-level-one = X.transfer-one C.base-transfer-one
prefix-one : V.val B.zero (proj₁ (S.G.piece 1)) V.≼ V.val B.zero (proj₁ (S.T.piece 1))
prefix-one = A.second-from-same same-level-one
prefix-one-cover : Σ ℕ λ m → V.val B.zero (proj₁ (S.G.piece 1)) V.≼ V.val B.zero (proj₁ (S.T.piece m))
prefix-one-cover = 1 , prefix-one
```

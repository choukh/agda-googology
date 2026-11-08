# 方格候选的完整零底源：统一固定基座

本篇只研究原 `closedGrid`，不更改定义。零底仍运行整个指标高源，
不是源高度零、有限截断或常值输出。先把它与轮数、外种子的关系写清，
再为其具名强度验收准备真实对象。本篇若仅有接线，不计新增强度。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GridValueBase where

open import Data.Nat using (ℕ; zero; z≤n)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
import OCF.Lean.OutputDrivenGrid as G

base : Cd
base = G.At.cell hz tt zero zero

all-zero-depth : ∀ c (lc : LgB c) rounds → G.At.cell c lc zero rounds ≡ base
all-zero-depth c lc rounds = refl

base-in-grid : base ≤ᵛ G.closedGrid
base-in-grid = G.cell-in-closed {d = zero} {r = zero} {k = zero} z≤n z≤n
```

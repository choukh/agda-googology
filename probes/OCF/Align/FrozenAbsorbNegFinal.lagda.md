# 实际生成域的同点改界吸收不成立

反例不是任意分支函数，而是共享接口的两个首生成元之和。
在与实际 OT/NT 桥接的零点 A=Original.TΩ1、种子 0 上，改界输出
不低于某树的后继，冻结输出不高于该树。因此 FrozenOutputReduce
所需的逐生成元同点吸收律被否定。此结果不否定实际轨道的错位覆盖或终点下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenAbsorbNegFinal where
open import Data.Empty using (⊥)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
open import OCF.Align.FrozenOutputIf using (Generated; initial; plus; changing; frozen; module Model)
open import OCF.Align.FrozenAbsorbNegUpper using (pair; module ActualUpper)
open import OCF.Align.FrozenAbsorbSeed using (positive-actual-base)
import OCF.Align.FrozenAbsorbPair as P
import OCF.Lean.Fold1 as Original

module General (A : Cd) (positive : hs hz ≤ᵛ A) where
  open Model A
  module L = P.Pair A positive
  module U = ActualUpper A positive

  generated-pair : Generated pair
  generated-pair = plus initial initial

  no-pair-absorption : run changing hz pair ≤ᵛ run frozen hz pair → ⊥
  no-pair-absorption p = ¬s≤ᵛ L.BB₀ (≤-trans L.strict-pair (≤-trans p U.upper))

  no-generated-absorption :
    (∀ c → Generated c → run changing hz c ≤ᵛ run frozen hz c) → ⊥
  no-generated-absorption absorb = no-pair-absorption (absorb pair generated-pair)

module Actual = General Original.TΩ1 positive-actual-base
```

前提实例齐全：positive-actual-base 已证；Generated pair 直接是 plus initial initial。
否定精确命中共享接口 Model 的 at-zero 律，不把同点比较加强成终点定义约束。
翻译账：只新增值关系定理，未改树、折叠、合法性、生成域或闭项证书。

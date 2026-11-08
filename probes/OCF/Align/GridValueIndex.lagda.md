# 方格最底指标界的全部轮数：固定增量而非重新坍缩迭代

本篇定位原 `Driven.next` 的一条完整有效规则，不另造候选。
第零底的零高度槽每轮运行同一个完整高源，结果就是 `GridBaseFirst.first`。
因此该底的**指标界**仅反复追加同一合法化增量并取后继。
其他高度槽的状态仍能变化；本篇绝不据此断言所有轮数或整个方格同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GridValueIndex where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import OCF.Lean.CRwBase
import OCF.Lean.OutputDrivenWorld as W
import OCF.Lean.OutputDrivenFamily as F
import OCF.Lean.ThirdRichLegBuild as Rich
import OCF.Align.GridBaseFirst as B

module D = W.Driven zero tt tt

delta : Cd
delta = Rich.legS zero B.first

zero-output : ∀ (s : D.State) → D.output s hz ≡ B.first
zero-output s = refl

index-step : ∀ (s : D.State) → D.index (D.next s) ≡ hs (D.index s ⊞ delta)
index-step s = refl

repeatIndex : ℕ → Cd → Cd
repeatIndex zero a = a
repeatIndex (suc r) a = repeatIndex r (hs (a ⊞ delta))

module Actual (rounds : ℕ) (c : Cd) (lc : LgB c) where
  module P = F.Family rounds c lc

  all-states : ∀ r s → D.index (P.iterate zero tt tt r s) ≡ repeatIndex r (D.index s)
  all-states zero s = refl
  all-states (suc r) s = all-states r (D.next s)

  initial-index : D.index (P.iterate zero tt tt rounds (P.start zero tt tt)) ≡ repeatIndex rounds c
  initial-index = all-states rounds (P.start zero tt tt)
```

这条等式区分两个经常混淆的迭代：`first` 内部包含完整原跨底回灌链；
但世界构造的 `rounds` 在最底指标界上重复的是固定增量 `delta`，不是
`c ↦ ψ₀(Ω_c)`。若整体新增强度来自轮数，必须分析非零高度槽的真正
交互及后续下降，不能仅凭“又迭代了一次高源”把指标界读作 Ω 塔。

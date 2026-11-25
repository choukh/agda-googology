# 第八轮真实 γ 种子的两类证据实例

本篇只在第4层装配已有实际历史与新结构证据，不进树侧定义依赖。
沿用第八轮的完整 Env 与第七轮的显式需求包络，不声称已扩成全部 γ 调用关系。
新包中实际比较仍走判定型，保留支只走结构型。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiDispSeed where

open import Data.List.Relation.Unary.Any using (here; there)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.YiLevelBase as Y
import OCF.Align.YiCtxBase as K
import OCF.Align.YiCtxFork as W
import OCF.Align.YiRTransport as R
open import OCF.Align.YiDActual using (ActualDemand; root-demand)
import OCF.Align.YiGammaSeed as H
open import OCF.Align.YiDispBase
open import OCF.Align.YiDispCountable using (OnlyΩ; with-seed-structure)

seed-mixed : InvDS (ActualDemand R.ν) OnlyΩ H.Enew R.seed-tree
seed-mixed = with-seed-structure H.seed-history-invD

selected : DispEv (Y.tree R.ν) W.b
selected = retained-ev seed-mixed W.field-b (here refl) refl

selected-keep : choice selected ≡ keep
selected-keep = refl

actual-root : DispEv F.zero F.zero
actual-root = actual-ev seed-mixed K.at (there (here refl)) root-demand

actual-collapse : choice actual-root ≡ collapse
actual-collapse = refl
```

因此旧 γ 种子的结构缺口已在本目标 Ω 上填上；实际(1,0)的collapse也保留。
这个非空实例不是 γ 下一输出的保持定理，更不是全部层号的覆盖定理。

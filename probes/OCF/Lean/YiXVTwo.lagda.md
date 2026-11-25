# YiXV：第 1 行的层号 2 前缀上界
> 验收文件。编译定理 `pre1-upper`：`read (pre 1) ≼ ψ⁰ (Ω 2)`，其中 `pre` 是第 1 个回灌点的实际前缀列。
> `YiXVChain2` 的所有底、模拟与起点参数在此实填；没有 `Need1` 或全塔上界。
> 构造与回灌底来自 `YiXVStart`、`YiXVLocal`、`YiXVCarry`、`YiXVAnchor`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVTwo where

open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLegBlock using (zero; suc)
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold using (ns)
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiXVStart using (B2; pre)
import OCF.Lean.YiXVLocal as I
import OCF.Lean.YiXVCarry as K
import OCF.Lean.YiXVAnchor as H
open import OCF.Lean.YiXVChain2 using (module Chain)
open import OCF.Align.YiLvValBase using (⟨_⟩)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)

module C = Chain I.D1 K.γ₁ (ns B2 (suc zero) (ins self)) K.γ₁U H.γ₁-closed I.zeroU refl

pre1-upper : read (pre 1) ≼ L.ψ⁰ (L.Ω ⟨ 2 ⟩)
pre1-upper = C.upper₂
```

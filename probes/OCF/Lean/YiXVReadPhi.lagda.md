# YiXVReadPhi
> 验收文件。档位：编译定理。重用 WorldInput.phi-good 与 ReadRules.phi-mono 的统一出口。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadPhi where
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
import OCF.Lean.YiXVReadWorldStart as Start
import OCF.Lean.YiXVReadRules as Rules
module Frame {root r} (p : r P.≤ᵀ root) where
  φ = W.φ p
  good : ∀ {X} → A.Gd X → A.Gd (φ X)
  good = W.φ-good p
  module R = Rules.Rules root r p (Fold.B₀ (J.ℓ r)) (W.seed root) (Start.initial-any root r p)
  mono : ∀ {X Y} → A.Le X Y → A.Le (φ X) (φ Y)
  mono = R.φ-mono p
```

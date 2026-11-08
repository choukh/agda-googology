# 富累加的实际分支捕获

对任意分支函数，不假设其沿坐标单调。原 `g d` 出现在真正
`θ (hs d)` 中；两个加法分别给右项包含与左前缀包含。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Lean.ThirdRichLegValueTheta where

open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (Ctx)
open import OCF.Lean.ThirdRichLegIf using (module New)
open import OCF.Lean.ThirdRichLegValueIf

module Capture {T U : KS} (c : Ctx T (step U)) (g : HB U → HB T) where
  open New c g

  branch : ∀ d → g d ≼ʳ θ (hs d)
  branch d = rt (right (θ d) (g d)) (left (θ d ⊞ g d) (g (hs d)))

  legal-coordinate : ∀ (d : HB U) → LgB d → LgB (hs d)
  legal-coordinate d ld = ld
```

第二条不是说新坐标仍在旧世界的同一界下。它只证明低层合法性保留；
原世界是否访问 `hs d` 是另一项义务，不能用本篇覆盖结论代替。

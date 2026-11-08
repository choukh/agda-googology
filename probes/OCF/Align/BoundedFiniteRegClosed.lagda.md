# 全有限地板的一棵合法P树

对每个原flL有限分量应用统一down，再取部分和极限。定义保留原地板，
并覆盖全部自然数层；这是与原M direct fold分开的新闭项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegClosed where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedFiniteRegIf
open import OCF.Align.BoundedFiniteRegFold
open import OCF.Align.BoundedFiniteRegUp
open import OCF.Align.BoundedFiniteRegDescent

one-step-good : ∀ n → Good n (down n (floor (suc n)))
one-step-good n = down-good n (floor (suc n)) (floor-good (suc n))

component : ℕ → HB (F zero)
component n = collapse n (floor n)
legal-component : ∀ n → LgB (component n)
legal-component n = collapse-legal n (floor n) (floor-good n)

closed : HB (F zero)
closed = family-sum floor
legal-closed : LgB closed
legal-closed = family-legal floor floor-good
```

合法闭项与全n证明已经给出；其值尚无新定理，不能据类型或层数报强度。
P→可数层仍需折叠与合法性证明，ψ₀Λ终点未完成。OriginalPointwise
也未由本篇填充：逐层迭代不被假定等于旧多层直接fold。

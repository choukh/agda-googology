# 保留P前缀的全有限混合闭项

本轮主族使用bulk：每次把完整旧树up到下一层，再加入该层原地板。
floor-only族仍保留合法性结果，但不因其层数声称有强度提升。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedFiniteRegBulk where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedFiniteRegIf
open import OCF.Align.BoundedFiniteRegClosure
open import OCF.Align.BoundedFiniteRegUp
open import OCF.Align.BoundedFiniteRegDescent

bulk : ∀ n → HB (F n)
bulk zero = floor zero
bulk (suc n) = up (bulk n) ⊞ floor (suc n)

good-bulk : ∀ n → Good n (bulk n)
good-bulk zero = floor-good zero
good-bulk (suc n) = good-add (suc n) (up (bulk n)) (floor (suc n))
  (good-up n (bulk n) (good-bulk n)) (floor-good (suc n))

component : ℕ → HB (F zero)
component n = collapse n (bulk n)
legal-component : ∀ n → LgB (component n)
legal-component n = collapse-legal n (bulk n) (good-bulk n)

closed : HB (F zero)
closed = family-sum bulk
legal-closed : LgB closed
legal-closed = family-legal bulk good-bulk
```

整个原P前缀被带入下一层，未重置为零或纯可数坐标；这仍不自动
给值增长定理。新主族不是原M.direct的替换证明，OriginalPointwise
仍开放。其P→可数折叠、序数值界以及ψ₀Λ验收继续分别是硬义务。

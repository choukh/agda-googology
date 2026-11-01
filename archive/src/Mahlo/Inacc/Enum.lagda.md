# 按大小枚举项

`enumT k` 包含所有 `size ≤ k` 的项（可能重复、含 ∉ OT 的项；完整性另证）。供 [FGH](FGH.lagda.md) 的有界搜索与 [FactsCheck](FactsCheck.lagda.md) 的机器求值测试用。

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Mahlo.Inacc.Enum where

open import Mahlo.Inacc.Syntax
open import Mahlo.Inacc.Closure using (isOT)

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; if_then_else_)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)

mutual
  enumT : ℕ → List Tm
  enumT zero    = []
  enumT (suc k) = zer ∷ concatMap (λ a → map (a ▹_) (enumP k)) (enumT k)

  enumP : ℕ → List PTm
  enumP zero    = []
  enumP (suc k) =
       I
    ∷ (map Om (enumT k)
    ++ concatMap (λ a → map (phi a) (enumT k)) (enumT k)
    ++ concatMap (λ κ → map (psi κ) (enumT k)) (enumR k))

  enumR : ℕ → List Reg
  enumR zero    = []
  enumR (suc k) = IR ∷ map ΩR (enumT k)

filterB : (Tm → Bool) → List Tm → List Tm
filterB p []       = []
filterB p (x ∷ xs) = if p x then x ∷ filterB p xs else filterB p xs

-- size ≤ k 的 OT 项
ots : ℕ → List Tm
ots k = filterB isOT (enumT k)
```

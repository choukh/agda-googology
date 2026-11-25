# 当前逐 fsn 关系没有所需的码侧 ψ 运算

否定范围固定为本轮 `JiaRep` 的 ℕ 子句：与原 EBO 的 fsn 逐项对应。
若当前零层种子是 1，即使只要求在已有 Rep 且码为标准形的输入上保持，
也不存在任何返回原项类型 T 的码侧运算。
这不否定树、折叠或允许不同基本列的关系式方案。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRepNoPreservation where

open import Data.Empty using (⊥)
open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.EboLeanDef using (T; Ωt; Ωs; []<)
open import OCF.Align.EboLeanBase using (NF; n[]; nf-Ω)
open import OCF.Align.EboLean3Omega using (Acc′)
open import OCF.Align.JiaBase using (Seeds; Tree; below; module Layer)
open Seeds using (seed)
open import OCF.Align.JiaFold using (regular; module Fold)
open import OCF.Align.JiaRep using (Rep)
open import OCF.Align.JiaRepOmega using (rep-regular)
open import OCF.Align.JiaRepAuditOne using (no-code-for-regular; one-seeds; one-seeds-zero)

one : T
one = Ωt []

-- 比作者要求更弱：只对标准形码的相关输入量化，不给任意树配码。
record Preservation (seeds : Seeds) (a₁ : Acc′ one) (a₀ : Acc′ []) : Set where
  field
    codeFold : T → T
    maps : ∀ {x c} → NF c → Rep a₁ x c →
      Rep a₀ (Fold.ψ seeds a₁ a₀ (below n[] []<) x) (codeFold c)
open Preservation

regular-normal : NF (Ωs [])
regular-normal = nf-Ω (nf-Ω n[])

no-preservation : ∀ seeds a₁ a₀ → seed seeds [] a₀ ≡ Layer.s Layer.z →
  Preservation seeds a₁ a₀ → ⊥
no-preservation seeds a₁ a₀ e P = no-code-for-regular seeds a₁ a₀ e
  (codeFold P (Ωs [])) (maps P regular-normal (rep-regular a₁ n[]))

-- 条件有实际 Seeds 实例；这里只保证零层条件，不冒称高层 Ω 已正确。
no-preservation-instance : ∀ a₁ a₀ → Preservation one-seeds a₁ a₀ → ⊥
no-preservation-instance a₁ a₀ = no-preservation one-seeds a₁ a₀ (one-seeds-zero a₀)
```

反例的源是原第 1 层的正规 Ω，码的 NF 由 `regular-normal` 给出，
对应由 `rep-regular` 给出，原 Ω 分支域没有改窄。
它不是“选错裸 ψ”的反例：结论覆盖 `codeFold` 的所有选择。
零层种子为 1 是陈述中的条件，不把它省略成对所有种子的结论。

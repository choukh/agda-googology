# 地板移入源前缀：定向下界与待检验的反向律

本篇固定两种实际算法，不把缺失的折叠当作参数。
point 是带显式地板的逐项折叠；unary 把零叶固定为 1，极限取部分和。
两者都保留原底 Ω 种类。它们是原折叠保留片段的代数模型，
不是完整 same/above 运行器，不能据此声称改写了完整 EBO。
比较同一 HB S 的值，不要求下标序或值可判定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.DirectedPrefixIf where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul)

module _ {S : KS} where
  sums : (ℕ → HB S) → ℕ → HB S
  sums f zero = f zero
  sums f (suc n) = sums f n ⊞ f (suc n)

  point : HB S → HB S → HB S
  point η hz = η
  point η (hs a) = hl (mul (point η a))
  point η (hl f) = hl (λ n → point η (f n))
  point η (hΩ κ g) = hΩ κ (λ e → point η (g e))

  unary : HB S → HB S
  unary hz = hs hz
  unary (hs a) = hl (mul (unary a))
  unary (hl f) = hl (sums (λ n → unary (f n)))
  unary (hΩ κ g) = hΩ κ (λ e → unary (g e))

record PrefixLower : Set₁ where
  field
    lower : ∀ {S} (η A a : HB S) → η ≤ᵛ unary A →
      point η a ≤ᵛ unary (A ⊞ a)

record PrefixReverse : Set₁ where
  field
    reverse : ∀ {S} (η A a : HB S) →
      LgB η → LgB A → LgB a →
      η ≤ᵛ unary A → unary A ≤ᵛ η →
      unary (A ⊞ a) ≤ᵛ point η a
```

反向律故意补足合法性与基值相等；若仍有反例，只否定这个精确合同。
共享定义首次编译通过后冻结；后继只在新文件构造实例或证明否定。

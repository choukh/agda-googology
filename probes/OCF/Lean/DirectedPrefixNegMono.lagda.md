# 累计算子不是裸可数序数值上的单调函数

复用同一冻结 unary。这里的比较只有 Cd 的序数值，不涉及下标判等。
两个输入都合法且同值；结论不否定受控生成域或完整路线。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Lean.DirectedPrefixNegMono where
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.DirectedPrefixIf using (unary)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans)
import OCF.Lean.DirectedPrefixNegReverse as N

UnaryMono : Set
UnaryMono = ∀ (a b : Cd) → a ≤ᵛ b → unary a ≤ᵛ unary b

UnaryCongruence : Set
UnaryCongruence = ∀ (a b : Cd) →
  (a ≤ᵛ b) × (b ≤ᵛ a) → (unary a ≤ᵛ unary b) × (unary b ≤ᵛ unary a)

empty-zero : N.a ≤ᵛ hz
empty-zero = l≤ (λ _ → z≤)
zero-empty : hz ≤ᵛ N.a
zero-empty = z≤

legal-pair : LgB N.a × LgB (hz {S⊥})
legal-pair = N.legal-a , tt

two-in-empty : N.two ≤ᵛ unary N.a
two-in-empty = ≤l 1 (≤ᵛ-refl N.two)

no-output-order : ¬ (unary N.a ≤ᵛ unary (hz {S⊥}))
no-output-order p = N.two-not-one (≤ᵛ-trans two-in-empty p)

no-unary-mono : ¬ UnaryMono
no-unary-mono mono = no-output-order (mono N.a hz empty-zero)

no-unary-congruence : ¬ UnaryCongruence
no-unary-congruence congruence = no-output-order
  (proj₁ (congruence N.a hz (empty-zero , zero-empty)))
```

合法性也不能修复这个全域值单调合同。反馈比较可以使用 point 的
值单调性再接定向 PrefixLower，不能把它替换成这里已否定的 unary 单调性。

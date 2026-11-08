# 合法常零极限否定前缀反向律

只导入冻结的两种实际算法。反例的全部合法性和基值双向前提均实填。
这否定 PrefixReverse，不否定定向下界、受控生成族的吸收或完整路线。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Lean.DirectedPrefixNegReverse where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.CRwBase
open import OCF.Lean.DirectedPrefixIf
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans)

one two A a : Cd
one = hs hz
two = hs one
A = hz
a = hl (λ _ → hz)

legal-one : LgB one
legal-one = tt
legal-A : LgB A
legal-A = tt
legal-a : LgB a
legal-a = (λ _ → hself) , (λ _ → tt)

base-lower : one ≤ᵛ unary A
base-lower = ≤ᵛ-refl one
base-upper : unary A ≤ᵛ one
base-upper = ≤ᵛ-refl one

point-upper : point one a ≤ᵛ one
point-upper = l≤ (λ _ → ≤ᵛ-refl one)
unary-lower : two ≤ᵛ unary (A ⊞ a)
unary-lower = ≤l 1 (≤ᵛ-refl two)

two-not-one : ¬ (two ≤ᵛ one)
two-not-one (s≤s ())

no-reverse-instance : ¬ (unary (A ⊞ a) ≤ᵛ point one a)
no-reverse-instance p = two-not-one (≤ᵛ-trans unary-lower (≤ᵛ-trans p point-upper))

no-prefix-reverse : ¬ PrefixReverse
no-prefix-reverse r = no-reverse-instance
  (PrefixReverse.reverse r one A a legal-one legal-A legal-a base-lower base-upper)
```

反例使用整个合法极限，不是有限测试。逐点极限只有常值 1，累计极限
已经包含第 1 个部分和 2；合法性与基值相等不足以给反向值界。

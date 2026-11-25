# 实际块的全合法域可以暴露任意一对（验收定理）
编译定理：两个合法层号能同现于一个合法 Ω 结点并有字面公共上界；全结点比较因此给出全合法域比较。
后者由既有 `YiTBObs.no-total` 反驳，失败字段是双向字面路径，不含折叠或值，也不归类为 LPO 实例。
不否定规范读回域或可缺的表；不从全合法域反例否定写法 A。构造前提先在临时文件实填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTDExpose where

open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (_,_)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWPath
import OCF.Lean.YiTBRow as R
import OCF.Lean.YiTBObs as TB

two-labels : L → L → Tr zero → L
two-labels a b zero = a
two-labels a b (suc _) = b
two-labels a b (lim _ _) = b

two-ok : ∀ a b → Ok a → Ok b → ∀ c → Ok (two-labels a b c)
two-ok a b oa ob zero = oa
two-ok a b oa ob (suc _) = ob
two-ok a b oa ob (lim _ _) = ob

pair : L → L → L
pair a b = nd (sΩ zero) (two-labels a b)

pair-ok : ∀ a b → Ok a → Ok b → Ok (pair a b)
pair-ok a b oa ob = (tt , (λ c → z≤ (two-labels a b c))) , two-ok a b oa ob

pair-left : ∀ a b → a ≤ pair a b
pair-left a b = inc zero self

pair-right : ∀ a b → b ≤ pair a b
pair-right a b = inc (suc zero) self

AllNodePairs : Set
AllNodePairs = (k : L) (h : Tr k → L) → Ok (nd (sΩ k) h) →
  (c c′ : Tr k) → (h c ≤ h c′) ⊎ (h c′ ≤ h c)

LegalTotal : Set
LegalTotal = (a b : L) → Ok a → Ok b → (a ≤ b) ⊎ (b ≤ a)

all→legal-total : AllNodePairs → LegalTotal
all→legal-total C a b oa ob = C zero (two-labels a b) (pair-ok a b oa ob) zero (suc zero)

h₁-ok : ∀ c → Ok (R.h₁ c)
h₁-ok c = Ok⊕ zero (↑ zero c) tt (OkO↑ zero zero tt self c)

no-legal-total : LegalTotal → ⊥
no-legal-total C = TB.no-total (λ c c′ → C (R.h₁ c′) (R.h₁ c) (h₁-ok c′) (h₁-ok c))

no-all-node-pairs : AllNodePairs → ⊥
no-all-node-pairs C = no-legal-total (all→legal-total C)

```

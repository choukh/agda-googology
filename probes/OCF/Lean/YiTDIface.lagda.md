# 派发证据的量化域（验收接口）
编译用接口：`Evidence Q` 对请求域 Q 供给证据，答案须带原层序的三歧证明。
`Notation` 取弱口径：给定层序的可判定全序及一个闭合的一元算子；不含有限编码、良基或折叠方程。
`Scope` 只量化同一允许结点内的两个孩子；`Global` 量化全部层号对。入口见 `YiTDOrder`、`YiTDModels`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTDIface where

open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤)
open import Data.Sum.Base using (_⊎_)
open import Data.Product.Base using (Σ; _×_)
open import Relation.Binary.Definitions using (Transitive)
open import Relation.Binary.Structures using (IsStrictTotalOrder; IsDecTotalOrder)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.Construct.StrictToNonStrict as SN

record Frame : Set₁ where
  field
    A : Set
    _<_ : A → A → Set
    trans : Transitive _<_
    irrefl : ∀ {x} → x < x → ⊥

module On (F : Frame) where
  open Frame F

  Answer : A → A → Set
  Answer x y = (x < y) ⊎ ((x ≡ y) ⊎ (y < x))

  record Evidence (Req : A → A → Set) : Set₁ where
    field
      E : A → A → Set
      answer : ∀ x y → E x y → Answer x y
      provide : ∀ x y → Req x y → E x y

  Global : A → A → Set
  Global _ _ = ⊤

  Closed : (A → A) → (A → A → Set) → Set
  Closed ψ Req = ∀ {x y} → Req x y → Req (ψ x) (ψ y)

  record Notation : Set where
    field
      ψ : A → A
      ordered : IsStrictTotalOrder _≡_ _<_

    decidable-total-order : IsDecTotalOrder _≡_ (SN._≤_ _≡_ _<_)
    decidable-total-order = SN.isDecTotalOrder _≡_ _<_ ordered

  record Nodes : Set₁ where
    field
      Node : Set
      Child : Node → Set
      label : (n : Node) → Child n → A

  Scope : Nodes → A → A → Set
  Scope N x y = Σ Node λ n → Σ (Child n) λ c → Σ (Child n) λ d →
    (label n c ≡ x) × (label n d ≡ y)
    where open Nodes N

  Covers : Nodes → Set
  Covers N = ∀ x y → Scope N x y
```

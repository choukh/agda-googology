# γ 链的相关包随计算生成

相关包只接收已经知道的码及其 Rep，不为任意 raw 树找码。
原 Ω 子句仍只消费相关输入。标准形由现成 EBO γ-链封闭给出；
它要求父折叠码标准形，不能从任意 Rep 输入推出这个前提。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactFeedback where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Data.Product.Base using (proj₁)
open import OCF.Align.EboLeanDef using (T; sucT; cmpᵀ; gt; cof; cΩ; fsT; γT)
open import OCF.Align.EboLeanBase using (NF; gt→≤)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)
open import OCF.Align.EboLeanView using (vΩ; γ-eq)
open import OCF.Align.EboLeanClosure using (tow)
open import OCF.Align.JiaBase
open import OCF.Align.JiaRep
open import OCF.Align.JiaExactSeeds using (SeedSpec; sound)
open import OCF.Align.JiaExactCode using (Ψ)
open import OCF.Align.JiaExactFold using (module Fold)
open import OCF.Align.JiaExactRep using (module Sound)

record Related (ℓ : T) (a : Acc′ ℓ) : Set where
  constructor related
  field
    label : T
    normal-label : NF label
    value : Tree ℓ a
    witness : Rep a value label
open Related public

Trees-at : ∀ {ℓ a} → Related ℓ a → Set
Trees-at x = Tree (label x) (wf (normal-label x))

h-below : ∀ {ℓ j} (aℓ : Acc′ ℓ) → Below j ℓ → Acc′ j
h-below (acc h) q = h (normal q) (smaller q)

module Chain (seeds : Seeds) where
  open Fold seeds using (ψ; gamma)
  open Sound seeds using (ψ-rep)

  gamma-rep : ∀ {ℓ j} (aℓ : Acc′ ℓ) (q : Below j ℓ) → SeedSpec seeds ℓ →
    (f : Low ℓ aℓ j q → Tree ℓ aℓ) → (c : T) →
    (∀ {y d} → RepLow ℓ aℓ j q y d → Rep aℓ (f y) (fsT c d)) →
    ∀ n → RepLow ℓ aℓ j q (gamma aℓ q f n) (γT c j n)
  gamma-rep (acc h) q S f c r zero = sound S q (h (normal q) (smaller q))
  gamma-rep (acc h) q S f c r (suc n) =
    ψ-rep (acc h) (h (normal q) (smaller q)) q S
      (r (gamma-rep (acc h) q S f c r n))

  pack-chain : ∀ {ℓ i j} (aℓ : Acc′ ℓ) (target : Below i ℓ) (q : Below j ℓ) →
    SeedSpec seeds ℓ → (f : Low ℓ aℓ j q → Tree ℓ aℓ) → (c : T) →
    (r : ∀ {y d} → RepLow ℓ aℓ j q y d → Rep aℓ (f y) (fsT c d)) →
    cof c ≡ cΩ j → NF (Ψ i c) → cmpᵀ (sucT j) i ≡ gt →
    (n : ℕ) → Related j (h-below aℓ q)
  pack-chain {i = i} {j} (acc h) target q S f c r ec nc em n =
    related (γT c j n)
      (subst NF (sym (γ-eq (vΩ c ec) n))
        (proj₁ (tow nc (vΩ c ec) (gt→≤ j i em) n)))
      (gamma (acc h) q f n) (gamma-rep (acc h) q S f c r n)
```

`Related` 的码、标准形、原树及对应证据都在构造该链点时给出。
`Trees-at` 展示这个输出包可作下一层号的类型参数；它还不是 Ω 程序
或全反馈闭项，不能以类型存在冒充下一步构造已完成。

# 甲脚手架：真实码上的可及层族

本篇是交接 S1 的探路定义，读记号，不进成品。层号直接取 EBO 的项；
低层结点同时携带标准形与严格小于本层的证据。树族沿现有 `Acc′` 递归，
不假定可及证明相等。这里只固定共享接口与搬运；尚不是 T甲。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; _<ᵀ_; cmpᵀ; lt; eq; gt)
open import OCF.Align.EboLeanBase using (NF; n[]; <ᵀ-trans)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)

record Below (j ℓ : T) : Set where
  constructor below
  field
    normal : NF j
    smaller : j <ᵀ ℓ
open Below public

below-trans : ∀ {j i ℓ} → Below j i → Below i ℓ → Below j ℓ
below-trans (below nj p) (below ni q) = below nj (<ᵀ-trans p q)

module Layer (ℓ : T) (Low : ∀ j → Below j ℓ → Set) where
  data Tree : Set where
    z : Tree
    s : Tree → Tree
    l : (ℕ → Tree) → Tree
    o : ∀ {j} (p : Below j ℓ) → (Low j p → Tree) → Tree

  nat : ℕ → Tree
  nat zero = z
  nat (suc n) = s (nat n)

  omega : Tree
  omega = l nat

  infixl 6 _+_
  _+_ : Tree → Tree → Tree
  x + z = x
  x + s y = s (x + y)
  x + l f = l (λ n → x + f n)
  x + o p f = o p (λ y → x + f y)

iter : ∀ {A : Set} → (A → A) → A → ℕ → A
iter f x zero = x
iter f x (suc n) = f (iter f x n)

lfp : ∀ {ℓ Low} → (Layer.Tree ℓ Low → Layer.Tree ℓ Low) → Layer.Tree ℓ Low
lfp f = Layer.l (iter f Layer.z)

mapTree : ∀ {ℓ Low Low′} →
  (∀ j p → Low′ j p → Low j p) → Layer.Tree ℓ Low → Layer.Tree ℓ Low′
mapTree m Layer.z = Layer.z
mapTree m (Layer.s x) = Layer.s (mapTree m x)
mapTree m (Layer.l f) = Layer.l (λ n → mapTree m (f n))
mapTree m (Layer.o p f) = Layer.o p (λ y → mapTree m (f (m _ p y)))

Tree : ∀ ℓ → Acc′ ℓ → Set
Low : ∀ ℓ → Acc′ ℓ → ∀ j → Below j ℓ → Set
Tree ℓ a = Layer.Tree ℓ (Low ℓ a)
Low ℓ (acc h) j (below nj p) = Tree j (h nj p)

coe : ∀ {ℓ} (a a′ : Acc′ ℓ) → Tree ℓ a → Tree ℓ a′
coe (acc h) (acc h′) =
  mapTree (λ { j (below nj p) → coe (h′ nj p) (h nj p) })

-- 规范的标准形实例：良基性由记号侧提供，不是新假设。
Trees : ∀ {ℓ} → NF ℓ → Set
Trees {ℓ} nℓ = Tree ℓ (wf nℓ)

-- 种子只固定类型，不把其存在说成 Ω 或回灌已经完成。
record Seeds : Set₁ where
  field
    seed : ∀ ℓ (a : Acc′ ℓ) → Tree ℓ a
```

`coe` 的逆变方向与交接骨架相同：目标分支的低层树先搬回源分支的
可及证明，再递归搬运输出；没有比较两个 `Acc′` 证明的相等。
`Seeds` 是后续 Ω 定义的接口，任意填零虽能居留，但不满足 S1 的值目标。

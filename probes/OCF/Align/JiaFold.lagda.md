# 甲脚手架：带本层界的提升与折叠

这是 S1 的参数化构造。`Seeds` 必须由后续 Ω 构造实填；本篇不把它
当作已经存在的正确 Ω。ψ 的零行取目标种子，跨层链经过结点自身的
低层，三路都保留真实 EBO 比较，未用玩具码替代。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef using (T; cmpᵀ; Cmp; lt; eq; gt; sucT)
open import OCF.Align.EboLeanBase using (NF; n[]; lt→<; eq→≡)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)
open import OCF.Align.JiaBase

lift : ∀ {i ℓ} (ai : Acc′ i) (aℓ : Acc′ ℓ) → Below i ℓ → Tree i ai → Tree ℓ aℓ
lift (acc hi) (acc hℓ) p = go where
  go : Tree _ (acc hi) → Tree _ (acc hℓ)
  go Layer.z = Layer.z
  go (Layer.s x) = Layer.s (go x)
  go (Layer.l f) = Layer.l (λ n → go (f n))
  go (Layer.o q f) = Layer.o (below-trans q p)
    (λ y → go (f (coe (hℓ (normal q) (smaller (below-trans q p)))
                       (hi (normal q) (smaller q)) y)))

-- 后继层的 Ω：分支是低层树，按结构提升，不读基本列。
regular : ∀ {i} (a : Acc′ (sucT i)) → NF i → Tree (sucT i) a
regular {i} (acc h) ni = Layer.o p (lift (h ni (<-sucT i)) (acc h) p)
  where p = below ni (<-sucT i)

module Fold (seeds : Seeds) where
  open Seeds seeds

  ψ : ∀ {ℓ i} (aℓ : Acc′ ℓ) (ai : Acc′ i) → Below i ℓ → Tree ℓ aℓ → Tree i ai
  ψ {ℓ} {i} (acc h) (acc hi) target = go where
    open Layer i (Low i (acc hi)) using (_+_)
    go : Tree ℓ (acc h) → Tree i (acc hi)
    go Layer.z = seed i (acc hi)
    go (Layer.s x) = lfp (λ y → go x + y)
    go (Layer.l f) = Layer.l (λ n → go (f n))
    go (Layer.o {j} p f) with cmpᵀ j i in e
    ... | lt = Layer.o (below (normal p) (lt→< j i e))
      (λ y → go (f (coe (hi (normal p) (lt→< j i e))
                       (h (normal p) (smaller p)) y)))
    ... | gt = Layer.l (λ n → go (f
      (iter (λ γ → ψ (acc h) (h (normal p) (smaller p)) p (f γ)) Layer.z n)))
    ... | eq with eq→≡ j i e
    ...   | refl = lfp (λ y → go (f (coe (acc hi) (h (normal p) (smaller p)) y)))
```

## 比较接口：两个码确实都在本层之下

这里仅记录码的界，不宣称它们已经是树上的位置。S2 所要证明的恰是
从这种输入生产合法世界和字面位置，而不是事后补一个值上界。

```agda
record Comparison (ℓ : T) : Set where
  constructor comparison
  field
    node target : T
    node-below : Below node ℓ
    target-below : Below target ℓ
open Comparison public

decision : ∀ {ℓ} → Comparison ℓ → Cmp
decision c = cmpᵀ (node c) (target c)

at-node : ∀ {ℓ i j} → Below j ℓ → Below i ℓ → Comparison ℓ
at-node {i = i} {j} p q = comparison j i p q
```

`Comparison` 是每次 Ω 派发都能直接生成的记录。它不是 T甲 的实际
比较清单，也不填 S2 的位置实现义务；完整闭项尚未接出。

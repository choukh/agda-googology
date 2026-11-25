# 甲的混合分支树族：正规 raw，奇异携码

第五轮的新接口，旧 JiaBase 保留。正规结点 r 的低层域仍是完整 raw 树；
奇异结点 q 的域改为标准形码 d 及 d < Ω_{j+1} 的证据。
这里只有甲脚手架的翻译形状；S3 必须把奇异输入换回低层合法树，
并由树本身给出层号，不能把本篇 CodeArg 搬进乙。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaMixedBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import OCF.Align.EboLeanDef using (T; Ωs; sucT; _<ᵀ_)
open import OCF.Align.EboLeanBase using (NF)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase public using (Below; below; normal; smaller; below-trans)

record CodeArg (j : T) : Set where
  constructor code-arg
  field
    code : T
    code-normal : NF code
    code-bound : code <ᵀ Ωs j
open CodeArg public

data Kind : Set where
  regular-kind singular-kind : Kind

module Layer (ℓ : T) (Low : ∀ j → Below j ℓ → Set) where
  data Tree : Set where
    z : Tree
    s : Tree → Tree
    l : (ℕ → Tree) → Tree
    r : ∀ {j} (p : Below j ℓ) → (Low j p → Tree) → Tree
    q : ∀ {j} (p : Below j ℓ) → (CodeArg j → Tree) → Tree

  infixl 6 _+_
  _+_ : Tree → Tree → Tree
  x + z = x
  x + s y = s (x + y)
  x + l f = l (λ n → x + f n)
  x + r p f = r p (λ y → x + f y)
  x + q p f = q p (λ d → x + f d)

mapTree : ∀ {ℓ Low Low′} →
  (∀ j p → Low′ j p → Low j p) → Layer.Tree ℓ Low → Layer.Tree ℓ Low′
mapTree m Layer.z = Layer.z
mapTree m (Layer.s x) = Layer.s (mapTree m x)
mapTree m (Layer.l f) = Layer.l (λ n → mapTree m (f n))
mapTree m (Layer.r p f) = Layer.r p (λ y → mapTree m (f (m _ p y)))
mapTree m (Layer.q p f) = Layer.q p (λ d → mapTree m (f d))

Tree : ∀ ℓ → Acc′ ℓ → Set
Low : ∀ ℓ → Acc′ ℓ → ∀ j → Below j ℓ → Set
Tree ℓ a = Layer.Tree ℓ (Low ℓ a)
Low ℓ (acc h) j (below nj p) = Tree j (h nj p)

coe : ∀ {ℓ} (a a′ : Acc′ ℓ) → Tree ℓ a → Tree ℓ a′
coe (acc h) (acc h′) =
  mapTree (λ { j (below nj p) → coe (h′ nj p) (h nj p) })

lift : ∀ {i ℓ} (ai : Acc′ i) (aℓ : Acc′ ℓ) → Below i ℓ → Tree i ai → Tree ℓ aℓ
lift (acc hi) (acc hℓ) p = go where
  go : Tree _ (acc hi) → Tree _ (acc hℓ)
  go Layer.z = Layer.z
  go (Layer.s x) = Layer.s (go x)
  go (Layer.l f) = Layer.l (λ n → go (f n))
  go (Layer.r q f) = Layer.r (below-trans q p)
    (λ y → go (f (coe (hℓ (normal q) (smaller (below-trans q p)))
                       (hi (normal q) (smaller q)) y)))
  go (Layer.q q f) = Layer.q (below-trans q p) (λ d → go (f d))

regular : ∀ {i} (a : Acc′ (sucT i)) → NF i → Tree (sucT i) a
regular {i} (acc h) ni = Layer.r p (lift (h ni (<-sucT i)) (acc h) p)
  where p = below ni (<-sucT i)

iter : ∀ {A : Set} → (A → A) → A → ℕ → A
iter f x zero = x
iter f x (suc n) = f (iter f x n)
```

正规分支没有 NF、码或 Rep 的输入前提；低层任意 raw 树都能交给它。
奇异分支的界是原 EBO Ω-基本列的定义域，没有要求两个证据相等。
沿可及证明的搬运仍在正规分支输入处逆变，奇异码域与可及证明无关。

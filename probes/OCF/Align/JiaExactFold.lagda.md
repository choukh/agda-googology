# 甲脚手架：按 EBO 基本列重写 ψ

第四轮的新版本；旧 `JiaFold` 与第三轮结论保留。
原树族、低层 raw 分支域和 Rep 不动。
零行的 Ω 种子仍由参数给出；证明会另外要求其关系证据。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactFold where

open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.EboLeanDef using (T; Cmp; sucT; cmpᵀ; lt; eq; gt; _<ᵀ_)
open import OCF.Align.EboLeanBase using (<ᵀ-trans; lt→<; eq→≡)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase

copies : ∀ {ℓ} {a : Acc′ ℓ} → Tree ℓ a → ℕ → Tree ℓ a
copies {ℓ} {a} x = iter (Layer._+_ ℓ (Low ℓ a) x) Layer.z

-- 后继的显示复制写法与旧 lfp 行相同，不算新增树形变化。
copies-old : ∀ {ℓ} (a : Acc′ ℓ) (x : Tree ℓ a) →
  Layer.l (copies {ℓ = ℓ} {a = a} x) ≡
  lfp {ℓ = ℓ} {Low = Low ℓ a} (λ y → Layer._+_ ℓ (Low ℓ a) x y)
copies-old a x = refl

dispatch : ∀ {ℓ i j} (aℓ : Acc′ ℓ) (ai : Acc′ i) → Below i ℓ →
  (q : Below j ℓ) → (Low ℓ aℓ j q → Tree i ai) →
  (Low ℓ aℓ j q → Low ℓ aℓ j q) → Low ℓ aℓ j q →
  (m : Cmp) → cmpᵀ (sucT j) i ≡ m → Tree i ai
dispatch {i = i} {j} (acc h) (acc hi) target q out step start lt e =
  Layer.o (below (normal q) j<i)
    (λ y → out (coe (hi (normal q) j<i) (h (normal q) (smaller q)) y))
  where j<i = <ᵀ-trans (<-sucT j) (lt→< (sucT j) i e)
dispatch {i = i} {j} (acc h) (acc hi) target q out step start eq e =
  Layer.o (below (normal q) j<i)
    (λ y → out (coe (hi (normal q) j<i) (h (normal q) (smaller q)) y))
  where j<i = subst (j <ᵀ_) (eq→≡ (sucT j) i e) (<-sucT j)
dispatch (acc h) (acc hi) target q out step start gt e =
  Layer.l (λ n → out (iter step start n))

module Fold (seeds : Seeds) where
  open Seeds seeds

  ψ : ∀ {ℓ i} (aℓ : Acc′ ℓ) (ai : Acc′ i) → Below i ℓ → Tree ℓ aℓ → Tree i ai
  ψ {ℓ} {i} (acc h) (acc hi) target = go where
    go : Tree ℓ (acc h) → Tree i (acc hi)
    go Layer.z = seed i (acc hi)
    go (Layer.s x) = Layer.l (copies (go x))
    go (Layer.l f) = Layer.l (λ n → go (f n))
    go (Layer.o {j} p f) = dispatch (acc h) (acc hi) target p
      (λ γ → go (f γ))
      (λ γ → ψ (acc h) (h (normal p) (smaller p)) p (f γ))
      (seed j (h (normal p) (smaller p))) (cmpᵀ (sucT j) i) refl

  -- 与 gt 行中的迭代是同一程序，供链点包的构造使用。
  gamma : ∀ {ℓ j} (aℓ : Acc′ ℓ) (q : Below j ℓ) →
    (Low ℓ aℓ j q → Tree ℓ aℓ) → ℕ → Low ℓ aℓ j q
  gamma {j = j} (acc h) q f =
    iter (λ γ → ψ (acc h) (h (normal q) (smaller q)) q (f γ))
      (seed j (h (normal q) (smaller q)))
```

翻译账：后继的复制数取 n（与旧 lfp 行相同，由 `copies-old` 给出）；
比较左侧取 j+1；lt/eq 都保留 Ω 结点；
gt 取 γ 链，初项为目标共尾层 j 的 Ω 种子，下一项由 ψ_j(f γ) 给出；
输出第 n 支为 ψ_i(f γ_n)。以上形状为逐项对齐 EBO 规则 4、5Ω、6 而写。
它不是乙的最终定义。有界种子合同及保持定理见
[JiaExactSeeds](JiaExactSeeds.lagda.md)、[JiaExactRep](JiaExactRep.lagda.md)；
更高种子与完整闭项仍未完成。

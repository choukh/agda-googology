# 原完成闭项真实采样族的有限前缀规范桥

直接消费LowerFamily里的真实sample；原θ、原θ-path、原末段fold均不变。
规范侧去掉外部共同界与混合组件布局，保留原Native运行器和真实前缀。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionFinitePlaceSample where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Lean.FrozenWorldLift using (Same; same-value; same-sym)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (pure-reflexive)
open import OCF.Align.BoundedCompletionTerminalRel using (terminal-rel)
import OCF.Align.BoundedCompletionFinitePlaceTheta as Θ
import OCF.Align.BoundedCompletionLowerFamily as L
import OCF.Align.BoundedNativeValueFirst as V
import OCF.Align.BoundedNativeFloor as N
import OCF.Align.BoundedNativeTerminalReady as T
import OCF.Align.BoundedNativeCompletionClosed as C

num-agree : ∀ n → L.num n ≡ num n
num-agree zero = refl
num-agree (suc n) = cong hs (num-agree n)

stage : ℕ → ℕ
stage zero = zero
stage (suc n) = L.plus (L.tri n) (suc n)
tri-positive : ∀ n → L.tri n ≡ suc (stage n)
tri-positive zero = refl
tri-positive (suc n) = refl
height-positive : ∀ n → L.height n ≡ num (suc (stage n))
height-positive n = trans (L.height-normal n)
  (trans (num-agree (L.tri n)) (cong num (tri-positive n)))

normalized : ℕ → Cd
normalized n = T.fold V.feedback (Θ.normal (stage n))

actual-normalized : ∀ n → Same (L.sample n) (normalized n)
actual-normalized n = terminal-rel
  (Θ.known-height (L.height n) (stage n) (height-positive n) V.lB V.pt
    (N.θ-path (L.height n) V.B (hsuc (hlim n hself))))
  (pure-reflexive V.feedback)

normalized-below-C : ∀ n → normalized n ≤ᵛ C.tree
normalized-below-C n = ≤-trans (same-value (same-sym (actual-normalized n)))
  (L.sample-below-tree n)

whole-normalized-below-C : hl normalized ≤ᵛ C.tree
whole-normalized-below-C = l≤ normalized-below-C
```

这是全部真实采样与规范前缀族的双向结构桥，并把整族值置于合法C之下。
stage为0、2、5、9……；不能把这些finite层自动称为EBO的Ω迭代塔。
规范侧仍是原Native下降，尚未比较Old.TΩ或EBO参照；也未由本篇声称
normalized各项合法。值桥不依赖这一额外合法性主张。

翻译账：本轮不加记号规则或新运行器；新增的是原source组件布局与共同界
的消去证明。代价为分层结构关系与前缀相容，不是为标签验收定制的分支。

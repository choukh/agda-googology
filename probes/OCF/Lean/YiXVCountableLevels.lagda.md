# YiXVCountableLevels
> 验收文件。档位：编译定理。Strong 沿字面孩子保持；下一阶段所需低层接口有空层、一层完整实例。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableLevels where
open import Data.Product using (proj₁; proj₂)
open import Data.Unit using (tt)
import OCF.Align.Level as L
open import OCF.Lean.YiXVLvlSteps using (Strong)
open import OCF.Lean.YiXVLiteralTri using (Exact; tri)
down : ∀ {i κ} → Strong κ → i L.<ᴵ κ → Strong i
down {κ = L.suc κ} h L.zero = h
down {κ = L.suc κ} h (L.suc q) = down h q
down {κ = L.lim f s} h (L.lim n q) = down (proj₁ h n) q
child : ∀ {i κ} → Strong κ → i L.◃₁ κ → Strong i
child h L.zero = h
child h (L.self n) = proj₁ h n
actual : Strong (L.suc L.zero)
actual = tt

import OCF.Lean.YiXVCountableFoldInput as Q
import OCF.Lean.YiXVCountableGroundFold as G
Lower : L.Ordᴵ → Set₁
Lower κ = ∀ {i} → i L.◃₁ κ → Q.Ops i
one : Lower (L.suc L.zero)
one L.zero = G.ops
empty : Lower L.zero
empty ()
```

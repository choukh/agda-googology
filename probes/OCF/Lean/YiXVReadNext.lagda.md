# YiXVReadNext
> 验收文件。档位：编译定理。实际源层上的 next 模拟保持，复用加法保持与迭代合法性。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadNext where
open import Data.Nat using (zero; suc)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableIter as It
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadBasics as B
import OCF.Lean.YiXVReadPlus as P

model-good : A.Gd (L.suc (L.Ω (L.suc L.zero)))
model-good = A.Layer.gs A.oneΩ
model-read : U.UR (S.suc S.zero) (S.suc S.zero) (L.suc (L.Ω (L.suc L.zero)))
model-read = B.sucU (S.suc S.zero) (B.zero (S.suc S.zero))
model-nz : J.ℓ (S.suc S.zero) S.⊢ S.zero ◃ S.suc S.zero
model-nz = S.◃s

module Power (r : S.Tr S.zero) {x X} (gx : A.Gd X) (hx : U.UR r x X) where
  terms : ∀ k → U.UR r (O.iter (O._+_ x) x k) (iter (L._+_ X) L.zero (suc k))
  terms zero = hx
  terms (suc k) = P.plus r gx hx (It.good X gx (suc k)) (terms k)

next : ∀ r {x X} (nx : J.ℓ r S.⊢ S.zero ◃ x) → A.Gd X → U.UR r x X →
  U.UR r (O.next x nx) (L.lim (iter (L._+_ X) L.zero))
next r {X = X} nx gx hx = B.limU r (λ k → B.weak r (Power.terms r gx hx k)
  (A.Layer.pack (It.good X gx (suc k)) (A.Layer.gl (It.good X gx))
    (A.Layer.lr (suc k) (A.Layer.rfl (T.lvl r) A.Gd< A.Le< (It.good X gx (suc k))))))

actual : U.UR (S.suc S.zero) (O.next (S.suc S.zero) model-nz)
  (L.lim (iter (L._+_ (L.suc (L.Ω (L.suc L.zero)))) L.zero))
actual = next (S.suc S.zero) model-nz model-good model-read
```

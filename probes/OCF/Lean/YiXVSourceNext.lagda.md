# YiXVSourceNext
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceNext where
open import Data.Nat using (ℕ; zero; suc)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePlus as P

module Power (n : ℕ) {x X} (gx : A.Gd n X) (hx : U.U n x X) where
  terms : ∀ k → U.U n (O.iter (O._+_ x) x k) (iter (L._+_ X) L.zero (suc k))
  terms zero = hx
  terms (suc k) = P.plus n gx hx (It.good n X gx (suc k)) (terms k)

next : ∀ n {x X} (nx : J.nat n S.⊢ S.zero ◃ x) → A.Gd n X → U.U n x X →
  U.U n (O.next x nx) (L.lim (iter (L._+_ X) L.zero))
next n {X = X} nx gx hx = UB.limU n (λ k → UB.weakU n (Power.terms n gx hx k)
  (B.lr n F.zero {X = iter (L._+_ X) L.zero (suc k)} {a = iter (L._+_ X) L.zero}
    (It.good n X gx (suc k)) (It.good n X gx) (suc k)
    (B.rfl n F.zero {X = iter (L._+_ X) L.zero (suc k)} (It.good n X gx (suc k)))))
```

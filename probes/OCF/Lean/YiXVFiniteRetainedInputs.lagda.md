# YiXVFiniteRetainedInputs
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteRetainedInputs where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteCanonicalInputs as N
import OCF.Lean.YiXVFiniteTransportShape as S
import OCF.Lean.YiXVFiniteTransportInputs as Q
import OCF.Lean.YiXVFiniteTransport as T

module At (n j m : ℕ) (q : L.natᴵ m L.<ᴵ L.natᴵ (suc n)) (r : L.natᴵ m L.<ᴵ L.natᴵ (suc j)) where
  module D = A.Layer n (A.GoFam n) (A.LeFam n)
  module E = A.Layer j (A.GoFam j) (A.LeFam j)
  module NS = N.At n m q
  module NT = N.At j m r
  pull : L.U (L.natᴵ m) (L.<→◃ r) → L.U (L.natᴵ m) (L.<→◃ q)
  pull u = L.into (L.<→◃ q) (S.τ S.bwd m (L.out (L.<→◃ r) u))
  good : ∀ u → E.GU r u → D.GU q (pull u)
  good u gu = NS.good-in _ (Q.Ops.good (T.ops m) S.bwd F.zero _ (NT.good-out u gu))
  rel : ∀ u v → E.RU r u v → D.RU q (pull u) (pull v)
  rel u v p = NS.rel-in _ _ (Q.Ops.mono (T.ops m) S.bwd F.zero _ _ (NT.rel-out u v p))
  floor : ∀ u → E.Floor r u → D.Floor q (pull u)
  floor u p = NS.floor-in _ (B.trans m F.zero {X = L.Ω (L.natᴵ m)} {Y = S.τ S.bwd m (L.Ω (L.natᴵ m))}
    {Z = S.τ S.bwd m (L.out (L.<→◃ r) u)}
    (proj₁ (Q.Ops.pair (T.ops m) S.bwd F.zero _ (proj₁ (B.Ω-model m F.zero))))
    (Q.Ops.mono (T.ops m) S.bwd F.zero _ _ (NT.floor-out u p)))
  next : ∀ u → pull (C.next r u) ≡ C.next q (pull u)
  next u = trans
    (cong (λ x → L.into (L.<→◃ q) (S.τ S.bwd m x)) (L.out-into (L.<→◃ r) (L.suc (L.out (L.<→◃ r) u))))
    (sym (cong (λ x → L.into (L.<→◃ q) (L.suc x)) (L.out-into (L.<→◃ q) (S.τ S.bwd m (L.out (L.<→◃ r) u)))))
  start-rel : D.RU q (C.start q) (pull (C.start r))
  start-rel = NS.rel-in _ _
    (subst (A.Le m (L.Ω (L.natᴵ m)))
      (sym (cong (S.τ S.bwd m) (L.out-into (L.<→◃ r) (L.Ω (L.natᴵ m)))))
      (proj₁ (Q.Ops.pair (T.ops m) S.bwd F.zero _ (proj₁ (B.Ω-model m F.zero)))))

actual : A.Layer.Floor 2 (A.GoFam 2) (A.LeFam 2) (L.suc L.zero)
  (At.pull 2 1 1 (L.suc L.zero) L.zero (C.start L.zero))
actual = At.floor 2 1 1 (L.suc L.zero) L.zero (C.start L.zero)
  (N.At.floor-in 1 1 L.zero (L.Ω (L.natᴵ 1))
    (B.rfl 1 F.zero {X = L.Ω (L.natᴵ 1)} A.actual₁))
```

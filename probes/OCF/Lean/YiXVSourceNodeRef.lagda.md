# YiXVSourceNodeRef
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceNodeRef where
open import Data.Nat using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong; subst)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.YiLvValBase using (Ψ)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteTransportShape as T
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourcePathInputs as In

module Node {n k} (p : P.Path (suc n) (suc k)) (i : F.Fin (suc k)) (X : I.T (suc n))
  (f : L.U (L.natᴵ (I.rank k i)) (L.<→◃ (J.q k i)) → I.T (suc k)) where
  m = I.rank k i
  idx = P.inc p i
  q = J.q k i
  r = P.σ p q
  qt = J.q n idx
  e = P.level p i
  h = P.bound p i
  inp : L.U (L.natᴵ m) (L.<→◃ r) → L.U (L.natᴵ m) (L.<→◃ q)
  inp u = L.coe (L.<→◃ r) (L.<→◃ q) (L.into (L.<→◃ r) (T.τ T.bwd m (L.out (L.<→◃ r) u)))
  act : L.U (L.natᴵ m) (L.<→◃ r) → I.T (suc n)
  act u = Ψ (suc n) (L.add X (P.σ p) (f (inp u)))
  F′ : L.U (L.natᴵ (I.rank n idx)) (L.<→◃ qt) → I.T (suc n)
  F′ u = act (In.convert e qt r h u)
  ref-shape : Ψ (suc n) (L.add X (P.σ p) (L.limᵢ q f)) ≡ L.limᵢ qt F′
  ref-shape = In.node-convert e qt r h act
  input : ∀ Y → inp (In.convert e qt r h (L.into (L.<→◃ qt) Y)) ≡
    L.into (L.<→◃ q) (T.τ T.bwd m (P.pullR p i Y))
  input Y = trans
    (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ r)
      (T.τ T.bwd m (L.out (L.<→◃ r) (In.convert e qt r h (L.into (L.<→◃ qt) Y))))))
    (cong (λ Z → L.into (L.<→◃ q) (T.τ T.bwd m Z))
      (trans (In.out-convert e qt r h (L.into (L.<→◃ qt) Y))
        (cong (subst I.T e) (L.out-into (L.<→◃ qt) Y))))

```

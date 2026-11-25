# YiXVSourcePathInputs
> 验收文件。档位：编译定理。有限层源模拟的坐标、构造与保持工具；未交读回值界、所有 pre n 或 Goal。
> 从 YiXVCan2Rel/Plus/Lift/Self 按有限层统一，参照侧复用 YiXVFinite*；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourcePathInputs where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteTransportShape as TS
import OCF.Lean.YiXVFiniteTransportInputs as TQ
import OCF.Lean.YiXVFiniteTransport as T
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePath as P

cast-good : ∀ {a b} (e : a ≡ b) (X : I.T a) → A.Gd a X → A.Gd b (subst I.T e X)
cast-good refl X gx = gx
cast-le : ∀ {a b} (e : a ≡ b) (X Y : I.T a) → A.Le a X Y → A.Le b (subst I.T e X) (subst I.T e Y)
cast-le refl X Y t = t
cast-floor : ∀ {a b} (e : a ≡ b) (X : I.T a) → A.Le a (L.Ω (L.natᴵ a)) X → A.Le b (L.Ω (L.natᴵ b)) (subst I.T e X)
cast-floor refl X t = t
cast-margin : ∀ {a b} (e : a ≡ b) (X Y : I.T a) → A.Le a (L.suc X) Y → A.Le b (L.suc (subst I.T e X)) (subst I.T e Y)
cast-margin refl X Y t = t
cast-rel : ∀ {a b} (e : a ≡ b) x X → U.U a x X → U.U b (subst J.Tr e x) (subst I.T e X)
cast-rel refl x X t = t

module Guards {n k} (p : P.Path (suc n) (suc k)) (i : F.Fin (suc k)) where
  m : ℕ
  m = I.rank k i
  idx : F.Fin (suc n)
  idx = P.inc p i
  good : ∀ X → A.Gd (I.rank n idx) X → A.Gd m (P.pullR p i X)
  good X gx = cast-good (P.level p i) X gx
  floor : ∀ X → A.Le (I.rank n idx) (L.Ω (L.natᴵ (I.rank n idx))) X → A.Le m (L.Ω (L.natᴵ m)) (P.pullR p i X)
  floor X t = cast-floor (P.level p i) X t
  margin : ∀ X Y → A.Le (I.rank n idx) (L.suc X) Y → A.Le m (L.suc (P.pullR p i X)) (P.pullR p i Y)
  margin X Y t = cast-margin (P.level p i) X Y t
  rel : ∀ a X → U.UR n idx a X → U.UR k i (P.pullS p i a) (P.pullR p i X)
  rel a X t = subst (λ X → X) (sym (UB.stable k i _ _))
    (cast-rel (P.level p i) a X (subst (λ X → X) (UB.stable n idx a X) t))
  τ-good : ∀ X → A.Gd (I.rank n idx) X → A.Gd m (TS.τ TS.bwd m (P.pullR p i X))
  τ-good X gx = TQ.Ops.good (T.ops m) TS.bwd F.zero _ (good X gx)
  τ-floor : ∀ X → A.Le (I.rank n idx) (L.Ω (L.natᴵ (I.rank n idx))) X →
    A.Le m (L.Ω (L.natᴵ m)) (TS.τ TS.bwd m (P.pullR p i X))
  τ-floor X t = B.trans m F.zero {X = L.Ω (L.natᴵ m)} {Y = TS.τ TS.bwd m (L.Ω (L.natᴵ m))}
    {Z = TS.τ TS.bwd m (P.pullR p i X)}
    (proj₁ (TQ.Ops.pair (T.ops m) TS.bwd F.zero _ (proj₁ (B.Ω-model m F.zero))))
    (TQ.Ops.mono (T.ops m) TS.bwd F.zero _ _ (floor X t))
  τ-margin : ∀ X Y → A.Gd (I.rank n idx) Y → A.Le (I.rank n idx) (L.suc X) Y →
    A.Le m (L.suc (P.pullR p i X)) (TS.τ TS.bwd m (P.pullR p i Y))
  τ-margin X Y gy t = B.trans m F.zero {X = L.suc (P.pullR p i X)} {Y = P.pullR p i Y}
    {Z = TS.τ TS.bwd m (P.pullR p i Y)} (margin X Y t)
    (proj₁ (TQ.Ops.pair (T.ops m) TS.bwd F.zero _ (good Y gy)))

convert : ∀ {a b t} (e : a ≡ b) (q : L.natᴵ a L.<ᴵ L.natᴵ t) (r : L.natᴵ b L.<ᴵ L.natᴵ t) →
  P.cast-q e q ≡ r → L.U (L.natᴵ a) (L.<→◃ q) → L.U (L.natᴵ b) (L.<→◃ r)
convert refl q .q refl u = u
out-convert : ∀ {a b t} (e : a ≡ b) (q : L.natᴵ a L.<ᴵ L.natᴵ t) (r : L.natᴵ b L.<ᴵ L.natᴵ t)
  (h : P.cast-q e q ≡ r) u → L.out (L.<→◃ r) (convert e q r h u) ≡ subst I.T e (L.out (L.<→◃ q) u)
out-convert refl q .q refl u = refl
node-convert : ∀ {a b t} (e : a ≡ b) (q : L.natᴵ a L.<ᴵ L.natᴵ t) (r : L.natᴵ b L.<ᴵ L.natᴵ t)
  (h : P.cast-q e q ≡ r) (f : L.U (L.natᴵ b) (L.<→◃ r) → I.T t) →
  L.limᵢ r f ≡ L.limᵢ q (λ u → f (convert e q r h u))
node-convert refl q .q refl f = refl
source-node : ∀ n {p q : S.Pos (J.nat n)} (e : p ≡ q) (g : S.Br (J.nat n) p → J.Tr n) →
  S.Ω p g ≡ S.Ω q (λ z → g (subst (S.Br (J.nat n)) (sym e) z))
source-node n refl g = refl
```

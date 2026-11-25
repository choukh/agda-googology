# YiXVSourceAffineRef
> 验收文件。档位：编译定理。高参照前缀、源模拟或回灌链的工具；未交正源世界、所有 pre n 或 Goal。
> 从 YiXVSource* 与 YiXVCan2NodeOne 按有限层推广，前提均有完整闭模型；不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceAffineRef where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteVia as V
import OCF.Lean.YiXVFiniteTransportShape as T
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourcePath as P
import OCF.Lean.YiXVSourcePathInputs as In

module Node {n k} (H : ℕ) {ambient : L.Ordᴵ} (pc : L.natᴵ (suc n) L.<ᴵ ambient)
  (ρ : L.Simᴵ (L.natᴵ H) ambient) (ε : L.Simᴵ (L.natᴵ (suc n)) (L.natᴵ H))
  (p : P.Path (suc n) (suc k)) (i : F.Fin (suc k)) (X : I.T H)
  (f : L.U (L.natᴵ (I.rank k i)) (L.<→◃ (J.q k i)) → I.T (suc k)) where
  m = I.rank k i
  idx = P.inc p i
  q = J.q k i
  r = P.σ p q
  qt = J.q n idx
  e = P.level p i
  h = P.bound p i
  σ : L.Simᴵ (L.natᴵ (suc k)) (L.natᴵ H)
  σ q = ε (P.σ p q)
  inp : L.U (L.natᴵ m) (L.<→◃ r) → L.U (L.natᴵ m) (L.<→◃ q)
  inp u = L.coe (L.<→◃ (ε r)) (L.<→◃ q)
    (L.into (L.<→◃ (ε r)) (T.τ T.bwd m (L.out (L.<→◃ r) u)))
  act : L.U (L.natᴵ m) (L.<→◃ r) → I.T (suc n)
  act u = L.ψ pc ρ (L.add X σ (f (inp u)))
  F′ : L.U (L.natᴵ (I.rank n idx)) (L.<→◃ qt) → I.T (suc n)
  F′ u = act (In.convert e qt r h u)
  retain : L.ψ pc ρ (L.add X σ (L.limᵢ q f)) ≡ L.limᵢ r act
  retain with L.<ᴵ-dec (ρ (ε r)) pc
  ... | injᵃ v with V.exact (I.finite m) v
  ... | s , refl rewrite I.q-unique (suc n) s r = refl
  retain | injᵇ w = ⊥-elim (V.strict-both (L.via (L.≅ᴵ-refl _) r) w)
  retain | injᶜ e = ⊥-elim (V.strict-equal (L.via (L.≅ᴵ-refl _) r) e)
  ref-shape : L.ψ pc ρ (L.add X σ (L.limᵢ q f)) ≡ L.limᵢ qt F′
  ref-shape = trans retain (In.node-convert e qt r h act)
  input : ∀ Y → inp (In.convert e qt r h (L.into (L.<→◃ qt) Y)) ≡
    L.into (L.<→◃ q) (T.τ T.bwd m (P.pullR p i Y))
  input Y = trans
    (cong (L.into (L.<→◃ q)) (L.out-into (L.<→◃ (ε r))
      (T.τ T.bwd m (L.out (L.<→◃ r) (In.convert e qt r h (L.into (L.<→◃ qt) Y))))))
    (cong (λ Z → L.into (L.<→◃ q) (T.τ T.bwd m Z))
      (trans (In.out-convert e qt r h (L.into (L.<→◃ qt) Y))
        (cong (subst I.T e) (L.out-into (L.<→◃ qt) Y))))

module Model = Node 3 L.zero (λ q → q) (λ q → L.suc q) (P.down P.top) F.zero (L.Ω (L.natᴵ 3))
  (L.up L.zero)
actual : L.ψ L.zero (λ q → q)
  (L.add (L.Ω (L.natᴵ 3)) (λ q → L.suc (L.suc q)) (L.Ω (L.natᴵ 1))) ≡ L.limᵢ Model.qt Model.F′
actual = Model.ref-shape
```

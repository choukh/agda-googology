# 每座正塔由一个槽启动的不动点值律

第四层，无条件。沿塔的第零个正分支，把一个指定零槽的预算送到实际输出。凡途中使用全孩子或底层路径，返回均覆盖预算之上的下一 h 不动点。任意零路径也统一覆盖 1 之上的下一 h 不动点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4TowerLawSpine where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans)
import W4Block as W
import W4Path as P
import W4Ops as O
import W4Fold as F
import WKGen as Node
open import WVOne using (T₀; read; 𝟏)
import B14Tower as V
import B12Terminal as T
import B12ActualSlots as C
import B15Spine as S
import B19RowSecondParent as Add
import Survey.W4RoomDerivative as D
import Survey.W4TowerLawPoint as Point
import Survey.W4ReturnCarryUnit as Unit
import B27Joint as J
open T.Run

module Root (m : ℕ) (r : T.Run (W.tw (suc m))) where
  k = W.tw m
  top = W.tw (suc m)
  module A = S.Cardinal k (S.branch k) r
  call = λ w z → F.ψ top (ok r) (bs r) W.zero w (β r) (A.b z)
  first = λ w → read (proj₁ (call w W.zero))
  in-node : ∀ w → first w ≼ read (proj₁ (F.node⁺ (F.kp top (ok r) A.p w) (call w) A.step))
  in-node w = Node.node-ge (F.kp top (ok r) A.p w) (call w) A.step zero
  up : ∀ w → first w ≼ V.valueAt r w
  up (W.inc c w) = in-node (W.inc c w)
  up (W.inu ws) = in-node (W.inu ws)
  up (W.ink p) = in-node (W.ink p)

spine : ∀ n → W.zero W.≤ W.tw (suc n) → Set
spine zero w = ⊤
spine (suc n) (W.inu ws) = spine n (ws W.zero)
spine (suc n) (W.ink w) = spine n w
spine (suc n) (W.inc c w) = ⊥

source : ∀ n → W.zero W.≤ W.tw (suc n)
source zero = W.ink W.self
source (suc n) = W.inc W.zero (source n)

paid : ∀ n (r : T.Run (W.tw (suc n))) → ok r ≡ P.Ok-tw (suc n) → C.Covered r →
  ∀ x → x ≼ Point.slot r (source n) → ∀ w → spine n w → D.next x ≼ V.valueAt r w
paid zero r eq cv x f w _ = Point.first r cv x f w
paid (suc n) r@(T.makeRun _ _ _ _ _ _) refl cv x f (W.inu ws) along = ≼-trans
  (paid n (A.child 0) refl (A.cover cv 0) x f (ws W.zero) along) (Root.up (suc n) r (W.inu ws))
  where module A = Root.A (suc n) r
paid (suc n) r@(T.makeRun _ _ _ _ _ _) refl cv x f (W.ink w) along = ≼-trans
  (paid n (A.child 0) refl (A.cover cv 0) x f w along) (Root.up (suc n) r (W.ink w))
  where module A = Root.A (suc n) r
paid (suc n) r eq cv x f (W.inc c w) ()

normal : ∀ n → spine n (P.z≤ (W.tw (suc n)))
normal zero = tt
normal (suc n) = normal n

floor : ∀ n (r : T.Run (W.tw (suc n))) → ok r ≡ P.Ok-tw (suc n) → C.Covered r →
  ∀ w → D.next 𝟏 ≼ V.valueAt r w
floor zero r eq cv w = Point.first r cv 𝟏 (oneB r (source zero)) w
floor (suc n) r@(T.makeRun _ _ _ _ _ _) refl cv (W.inu ws) = ≼-trans
  (floor n (A.child 0) refl (A.cover cv 0) (ws W.zero)) (Root.up (suc n) r (W.inu ws))
  where module A = Root.A (suc n) r
floor (suc n) r@(T.makeRun _ _ _ _ _ _) refl cv (W.ink w) = ≼-trans
  (floor n (A.child 0) refl (A.cover cv 0) w) (Root.up (suc n) r (W.ink w))
  where module A = Root.A (suc n) r
floor (suc n) r@(T.makeRun _ _ _ _ _ _) refl cv (W.inc c w) = ≼-trans
  (paid n reset refl (C.initial k (P.Ok-tw (suc n))) 𝟏 (oneB reset (source n)) (P.z≤ k) (normal n))
  (≼-trans (Add.append (β r) (F.ψ₀ k (P.Ok-tw (suc n)) (proj₁ (O.Ωt k)))) (Root.up (suc n) r (W.inc c w)))
  where
  k = W.tw (suc n)
  reset = T.initial k (P.Ok-tw (suc n))

module Actual (n extra j : ℕ) where
  module Q = Unit.Host n extra j
  all : ∀ w → D.next 𝟏 ≼ V.valueAt Q.r w
  all = floor n Q.r Q.okay Q.cv
  funded : ∀ w → spine n w → D.next Q.x ≼ V.valueAt Q.r w
  funded = paid n Q.r Q.okay Q.cv Q.x (Q.high (source n))
  return : D.next (Point.slot Q.r (source n)) ≼ J.f Q.k j
  return = ≼-trans (paid n Q.r Q.okay Q.cv _ (≼-refl _) (P.z≤ _) (normal n)) Q.into
```

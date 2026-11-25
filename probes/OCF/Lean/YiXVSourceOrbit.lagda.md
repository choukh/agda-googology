# YiXVSourceOrbit
> 验收文件。档位：编译定理。实际节点回灌轨道到规范分支坐标的逐点对齐，不用函数外延。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceOrbit where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans; cong)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLegPath as Path
import OCF.Lean.YiLegFold as Fold
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceSlots as Slots
import OCF.Lean.YiXVSourceSelfInput as Model
import OCF.Lean.YiXVSourceGrowthInput as Growth

module Orbit (n : ℕ) (i : F.Fin (suc n)) (SrcB : Fold.Base (J.nat (suc n)))
  (g : S.Br (J.nat (suc n)) (J.slot n i) → J.Tr (suc n)) where
  m = I.rank n i
  σ = Slots.pth (Slots.slot-path n i)
  fold : S.Br (J.nat (suc n)) (J.slot n i) → J.Tr m
  fold z = Fold.ψs (J.nat (suc n)) (Model.ev (suc n)) (Model.rt (suc n)) SrcB (J.nat m) σ
    (Fold.bs SrcB (J.nat m) σ) (Fold.ns SrcB (J.nat m) σ) (g z)
  step : J.Tr m → J.Tr m
  step a = fold (J.inB n i a)
  actual-step : S.Br (J.nat (suc n)) (J.slot n i) → S.Br (J.nat (suc n)) (J.slot n i)
  actual-step z = S.fromBr (J.nat (suc n)) (J.slot n i)
    (Fold.ψs (J.nat (suc n)) (Model.ev (suc n)) (Model.rt (suc n)) SrcB
      (S.at (J.nat (suc n)) (J.slot n i)) (Path.posW (J.nat (suc n)) (J.slot n i))
      (Fold.bs SrcB (S.at (J.nat (suc n)) (J.slot n i)) (Path.posW (J.nat (suc n)) (J.slot n i)))
      (Fold.ns SrcB (S.at (J.nat (suc n)) (J.slot n i)) (Path.posW (J.nat (suc n)) (J.slot n i))) (g z))
  br : ℕ → S.Br (J.nat (suc n)) (J.slot n i)
  br = O.iter actual-step (S.br0 (J.nat (suc n)) (J.slot n i))
  c : ℕ → J.Tr m
  c k = J.outB n i (br k)
  feed : ∀ z → actual-step z ≡ J.inB n i (fold z)
  feed z = Slots.feed n i (λ j w → Fold.ψs (J.nat (suc n)) (Model.ev (suc n)) (Model.rt (suc n)) SrcB j w
    (Fold.bs SrcB j w) (Fold.ns SrcB j w) (g z))
  orbit : Growth.Orbit m step
  Growth.Orbit.points orbit = c
  Growth.Orbit.start orbit = trans (cong (J.outB n i) (sym (J.first n i))) (J.out-in n i S.zero)
  Growth.Orbit.next orbit k = trans (cong (J.outB n i) (feed (br k)))
    (trans (J.out-in n i (fold (br k))) (cong fold (sym (J.in-out n i (br k)))))
  row : ∀ j (Φ : J.Tr (suc n) → J.Tr j) k → Φ (g (J.inB n i (c k))) ≡ Φ (g (br k))
  row j Φ k = cong (λ z → Φ (g z)) (J.in-out n i (br k))
```

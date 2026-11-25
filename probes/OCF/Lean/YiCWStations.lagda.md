# 新终点的前三站
验收文件，读记号；新终点实际底上第 0、1、2 站的值下界均实填。
来源：YiFRStations，BTBO 入口换 YiCWBTBO，其余参照与语义接线复用原证明。
Kᵗ 的左边沿用原参照 row（仅为记号参照）；右边为新终点的实际 station，未声称全站成立。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWStations where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; cong; sym; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l)
open import OCF.Lean.YiGIInst
open import OCF.Lean.YiExSuff
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiRefTw2 using (tree-≼)
open import OCF.Lean.YiEXRow using (down₁; row₂-btbo)
open import OCF.Lean.YiKCSem using (rr≼)
open import OCF.Lean.YiCWTable using (rbΛ; rbᵗ; EBOᵗ)
import OCF.Lean.YiCWActual as C
open import OCF.Lean.YiCWBTBO using (btbo)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiLBInv using (from⊴)
open import OCF.Lean.YiKQSuff using (read≤)
open import OCF.Lean.YiKSDesc using (rowN)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
Kᵗ : ℕ → Set
Kᵗ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (C.station n)
k0 : Kᵗ 0
k0 h = ≼-trans (tree-back h) (K.lower⁰ (K.G⁰.m-next (O.Ωt B.zero) refl (λ n → refl) (K.m1 refl K.mz)) (back h))
k1 : Kᵗ 1
k1 h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 1)) (≼-trans down₁ (≼-trans row₂-btbo (≼-trans btbo (rr≼ (C.station 1))))))
station-step : ∀ n → K.readRW (C.station n) ≼ K.readRW (C.station (suc n))
station-step n = subst₂ _≼_ (cong K.readRW (sym (C.branch-form n))) (cong K.readRW (sym (C.branch-form (suc n))))
  (K.◃→≼ (TB.mono B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero)
    (O.+-mono (O.cum C.FΛ n) (proj₂ (O.upz (suc n) (O.Ωt (B.tw (suc n))))))))
k2 : Kᵗ 2
k2 h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 2))
  (≼-trans row₂-btbo (≼-trans btbo (≼-trans (rr≼ (C.station 1)) (station-step 1)))))
upper : ∀ n → K.readRW (C.station n) ≼ K.readRW EBOᵗ
upper zero = ≼l zero (≼-refl _)
upper (suc n) = ≼l (suc n) (≼-refl _)
branch-upper : ∀ n q → K.readRW (proj₁ (C.Step.out n (C.Step.chain n q))) ≼ K.readRW (C.station (suc n))
branch-upper n q = ≼-trans (rowN (F.kp (B.tw (suc n)) (P.Ok-tw (suc n)) (inj₁ (inj₁ tt)) (P.z≤ (B.tw (suc n))))
  (C.Step.out n) (C.Step.feed n) q (read≤ (proj₁ (C.Step.out n (C.Step.chain n q))))) (rr≼ (C.station (suc n)))
floor : ∀ q → (h : SI.E.HC (Keel⁻.row keelᴱ 2)) → SI.E.tree h ≼ K.readRW (proj₁ (C.Step.out 2 (C.Step.chain 2 q)))
floor q h = ≼-trans (k2 h) (from⊴ (ψ-⊵ (B.tw 3) (P.Ok-tw 3) (rbᵗ 3) (C.baseᴱ 3)
  B.zero (P.z≤ (B.tw 3)) (C.betaᴱ 3) (C.Step.g 2 (C.Step.chain 2 q))))
```

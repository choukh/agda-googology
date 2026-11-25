# 终点各支的前三站
验收文件；按指定 Kᴱ 陈述证明第 0、1、2 站及相邻站的值单调，未证全塔。
来源：第 0 站用 YiKVRel.m-next/lower⁰；第 1、2 站复用 YiMTValue.btbo-br1ᶻ 与 YiEXRow 的参照界。
branch-form 由实际折叠展开；终点接线复用 YiGIEnd。twc 使用终点继承的基底，不等同于 twᶻ。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFRStations where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.Level as L
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_; ≼-trans; l≼; ≼l; ≼-refl)
open import OCF.Lean.YiGIInst
open import OCF.Lean.YiExSuff
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiRefTw2 using (tree-≼)
open import OCF.Lean.YiEXRow using (down₁; row₂-btbo)
open import OCF.Lean.YiMTValue using (btbo-br1ᶻ; brᶻ)
open import OCF.Lean.YiKCSem using (rr≼)
open import OCF.Lean.YiGIEnd using (reference; hs; upperᴱ)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
Kᴱ : ℕ → Set
Kᴱ n = (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
branch-form : ∀ n → Keel⁻.twc keelᴱ n ≡ proj₁ (TB.ψ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (O.cum FΛ n))
branch-form zero = refl
branch-form (suc n) = refl
k0 : Kᴱ 0
k0 h = ≼-trans (tree-back h) (K.lower⁰ (K.G⁰.m-next (O.Ωt B.zero) refl (λ n → refl) (K.m1 refl K.mz)) (back h))
k1 : Kᴱ 1
k1 h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 1)) (≼-trans down₁ (≼-trans row₂-btbo (≼-trans btbo-br1ᶻ (rr≼ (brᶻ 1))))))

station-step : ∀ n → K.readRW (Keel⁻.twc keelᴱ n) ≼ K.readRW (Keel⁻.twc keelᴱ (suc n))
station-step n = subst₂ _≼_ (cong K.readRW (sym (branch-form n))) (cong K.readRW (sym (branch-form (suc n))))
  (K.◃→≼ (TB.mono B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero)
    (O.+-mono (O.cum FΛ n) (proj₂ (O.upz (suc n) (O.Ωt (B.tw (suc n))))))))

k2 : Kᴱ 2
k2 h = ≼-trans (tree-back h) (≼-trans (tree-≼ refl (back h) (ET.hc-tower 2))
  (≼-trans row₂-btbo (≼-trans btbo-br1ᶻ (≼-trans (rr≼ (brᶻ 1)) (station-step 1)))))

ebo-from-stations : (∀ n → Kᴱ n) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-from-stations k = ≼-trans reference (l≼ (λ n → ≼-trans (k n (hs n)) (upperᴱ n)))
```

# 主线上带条件的 EBO 下界

> 验收文件（读记号）。`Assembly.ebo-end`：`Leaf`、`Lift`、`LowKeep` 与具名出口条件推出 `toL EBO-tree′ ≼ readRW EBOᶻ`。
> 来源：`YiAbsGEbo.ebo-end` 的逐行证明改接 `YiExSuff.TowerE.endpoint`；起点取 0，`row n` 恰为 `EBOψ n`，不另要第 0 行或塔到终点的假设。
> 三条全域律与全塔出口条件仍为假设；规范实例见 `YiGICheck`，不声称无条件达到 EBO。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGIEnd where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
import OCF.Align.Level as L
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_; ≼-refl; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiExSuff
open import OCF.Lean.YiGIInst

open Laws gradedᵍ domsᵍ using (Leaf; Lift; LowKeep)
open ExSuff gradedᵍ domsᵍ

standard-closed : ∀ n → Keel⁻.twc keelᵍ n ≡ MT.twᶻ n
standard-closed n = refl

omega-kt : ∀ n → E.Ωt (Keel⁻.kt keelᴱ n) ≡ E.ΩTower n
omega-kt zero = refl
omega-kt (suc n) = cong E.Ωt (omega-kt n)

row-eq : ∀ n → Keel⁻.row keelᴱ n ≡ E.EBOψ n
row-eq n = cong (λ a → E.ψ [] a ∷ []) (omega-kt n)

upperᴱ : ∀ n → K.readRW (Keel⁻.twc keelᴱ n) ≼ K.readRW MT.EBOᶻ
upperᴱ zero = ≼l zero (≼-refl _)
upperᴱ (suc n) = ≼l (suc n) (≼-refl _)

transport-tree : ∀ {a b} (e : a ≡ b) (h : E.HC a)
  → toL (ET.tree h) ≼ SI.E.tree (subst SI.E.HC e (SI.conv h))
transport-tree refl h = SI.toL-tree h

hs : ∀ n → SI.E.HC (Keel⁻.row keelᴱ n)
hs n = subst SI.E.HC (sym (row-eq n)) (SI.conv (ET.hc-tower n))

reference : toL ET.EBO-tree′ ≼ L.lim (λ n → SI.E.tree (hs n))
reference = l≼ (λ n → ≼l n (transport-tree (sym (row-eq n)) (ET.hc-tower n)))

module Assembly (lf : Leaf) (li : Lift) (lk : LowKeep) where
  module T = TowerE lf li keelᴱ

  ExitCondition : Set
  ExitCondition = ∀ n → H.Exᴴ (T.folded lk n)
    where import OCF.Lean.YiHCRel as H

  module _ (ex : ExitCondition) where
    Kᴱ : ∀ n (h : SI.E.HC (Keel⁻.row keelᴱ n)) → SI.E.tree h ≼ K.readRW (Keel⁻.twc keelᴱ n)
    Kᴱ = T.K lk exitᵍ ex

    endpoint : L.lim (λ n → SI.E.tree (hs n)) ≼ K.readRW MT.EBOᶻ
    endpoint = T.endpoint lk exitᵍ ex (K.readRW MT.EBOᶻ) upperᴱ hs

    ebo-end : toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
    ebo-end = ≼-trans reference endpoint

eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk)
  → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
eboᵍ lf li lk ex = Assembly.ebo-end lf li lk ex
```

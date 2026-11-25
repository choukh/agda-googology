# 仅在规范龙骨上调用三条律
验收文件；条件定理：龙骨 Leaf、Lift 与连同出口返回的逐行低层保持，推出主线终点的 EBO 序数值下界。
来源：按 `YiExSuff.TowerE` 重写调用域，出口按 `YiMXEnd`；参照与终点上界引用 `YiGIEnd`。
`leaf0`、`lift0`、`low0` 实填第 0 站；全塔三条前提仍待实填，不声称无条件达到 EBO。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCNKeel where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIEnd as GE
import OCF.Lean.YiMXEnd as MX
open import OCF.Lean.YiGICheck using (lift-start)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ; exitᵍ; startᴿ)
open import OCF.Lean.YiExSuff using (module ExSuff)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open import OCF.Lean.YiMonoExit using (toL)
open ExSuff gradedᵍ domsᵍ using (Keel⁻; Exit₀)
open Keel⁻ keelᴱ

LeafAt LiftAt LowAt : ℕ → Set
LeafAt n = GR.Rd (tw n) (kt n) → GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n)))
LiftAt n = GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n))) → GR.Rd (B.↑ (tw n) (proj₁ (O.Ωt (tw n)))) (E.Ωt (kt n))
LowAt n = GR.R (tw n) (E.Ωt (kt n)) (proj₁ (O.Ωt (tw n))) → Σ (GR.R B.zero (row n) (twc n)) H.Exᴴ

Leafᵏ Liftᵏ LowKeepᴱᵏ : Set
Leafᵏ = ∀ n → LeafAt n
Liftᵏ = ∀ n → LiftAt n
LowKeepᴱᵏ = ∀ n → LowAt n

record KeelLaws : Set where
  field
    leaf : Leafᵏ
    lift : Liftᵏ
    low : LowKeepᴱᵏ

module Assembly (lf : Leafᵏ) (li : Liftᵏ) (lk : LowKeepᴱᵏ) where
  keel : ∀ n → GR.Rd (tw n) (kt n)
  keel zero = rd-tw0
  keel (suc n) = tw-step n (li n (lf n (keel n)))
  folded : ∀ n → Σ (GR.R B.zero (row n) (twc n)) H.Exᴴ
  folded n = lk n (lf n (keel n))
  Kᴱ : ∀ n (h : SI.E.HC (row n)) → SI.E.tree h ≼ K.readRW (twc n)
  Kᴱ n h = Exit₀.exit exitᵍ (proj₁ (folded n)) (proj₂ (folded n)) h
  eboᶜ : toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
  eboᶜ = ≼-trans GE.reference (l≼ (λ n → ≼-trans (Kᴱ n (GE.hs n)) (GE.upperᴱ n)))

leaf0 : LeafAt 0
leaf0 _ = startᴿ
lift0 : LiftAt 0
lift0 = lift-start
low0 : LowAt 0
low0 _ = MX.low-zeroᴱ (b₀ 0) (β₀ 0) [] (K.m1 {t = E.natT 1} refl K.mz) (K.m1 {t = E.natT 1} refl K.mz)

eboᵏ : Leafᵏ → Liftᵏ → LowKeepᴱᵏ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
eboᵏ = Assembly.eboᶜ
```

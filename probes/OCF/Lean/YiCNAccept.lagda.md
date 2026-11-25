# 规范域与龙骨组装的接合
验收文件；编译定理：旧反例不在 `Cn`，规范域 Leaf 推出龙骨 Leaf；第 0、1 站有 Leaf/Lift，第 2 站有龙骨 Leaf。
`eboᶜ`、`ebo-rest` 均为条件定理；全塔前提的可满足性尚未知，不报告新的无条件强度。
来源：`YiCNKeel` 的组装、`YiCNTw1` 的完整 Leaf；第 1 站 Lift 只取一个指定孩子，并调用 `YiLLCheck.read0`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCNAccept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([])
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiLLLeafNeg as N
import OCF.Lean.YiCNKeel as C
import OCF.Lean.YiCNTw1 as T1
open import OCF.Lean.YiCNDomain
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMonoExit using (toL)

no-cn : Cn N.ℓ → ⊥
no-cn q = bad (cn-mono q {x = suc zero} ◃s)
  where
  bad : nd sS (λ _ → zero) P.⊑ zero → ⊥
  bad ()

not-tw : ∀ n → N.ℓ ≡ tw n → ⊥
not-tw n e = no-cn (subst Cn (sym e) (cn-tw n))

Leafᶜ : Set
Leafᶜ = ∀ {ℓ} → Cn ℓ → ∀ {ν} → GR.Rd ℓ ν → GR.R ℓ (E.Ωt ν) (proj₁ (O.Ωt ℓ))

cn→keel : Leafᶜ → C.Leafᵏ
cn→keel lf n = lf (cn-tw n)

leaf-tw0 : ∀ {ν} → GR.Rd (tw 0) ν → GR.R (tw 0) (E.Ωt ν) (proj₁ (O.Ωt (tw 0)))
leaf-tw0 = LL.leafC zero tt

leaf1 : C.LeafAt 1
leaf1 = T1.leaf-tw1

lift1 : C.LiftAt 1
lift1 _ = GR.rd-child (sΩ zero) _ (suc zero)
  (GR.rd-add zero _ (GR.ca (inj₂ ([] , refl , GR.c0 refl , λ η c r →
    GR.rd-add zero _ (GR.rd-child sS _ tt (LL.read0 r))))))

leaf2 : C.LeafAt 2
leaf2 _ = H.mw (H.mU {t = []} {s = E.Ωt (E.Ωt (E.natT 1))} H.mz LL.leafΩ) ◃w

rd1 : GR.Rd (tw 1) (E.natT 1)
rd1 = GR.tw-step 0 (C.lift0 (C.leaf0 GR.rd-tw0))

rd2 : GR.Rd (tw 2) (E.Ωt (E.natT 1))
rd2 = GR.tw-step 1 (lift1 (leaf1 rd1))

eboᶜ : Leafᶜ → C.Liftᵏ → C.LowKeepᴱᵏ → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
eboᶜ lf = C.eboᵏ (cn→keel lf)

LeafRest LiftRest LowRest : Set
LeafRest = ∀ n → C.LeafAt (suc (suc (suc n)))
LiftRest = ∀ n → C.LiftAt (suc (suc n))
LowRest = ∀ n → C.LowAt (suc n)

fill-leaf : LeafRest → C.Leafᵏ
fill-leaf f zero = C.leaf0
fill-leaf f (suc zero) = leaf1
fill-leaf f (suc (suc zero)) = leaf2
fill-leaf f (suc (suc (suc n))) = f n

fill-lift : LiftRest → C.Liftᵏ
fill-lift f zero = C.lift0
fill-lift f (suc zero) = lift1
fill-lift f (suc (suc n)) = f n

fill-low : LowRest → C.LowKeepᴱᵏ
fill-low f zero = C.low0
fill-low f (suc n) = f n

ebo-rest : LeafRest → LiftRest → LowRest → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ
ebo-rest lf li lo = C.eboᵏ (fill-leaf lf) (fill-lift li) (fill-low lo)
```

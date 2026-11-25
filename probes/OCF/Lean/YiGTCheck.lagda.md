# 一般目标保持的最小前提检查
验收文件（读记号）；零层保持复用 `YiLKIface.self-zero`，底关系的否定复用 `YiLLLeafNeg.Fin.one-ref`。
`PresJ` 按目标读法 ν 参数化；路径取实际折叠的 `≤`，包括槽位使用的 `ink`、`inc`。
编译定理：默认底通过 `OK`，但不能承载任意前缀的 ψ 值；不否定 `OmegaStep` 或规范塔域上的保持。
第 0 步未完成；抽象终止骨架与同源保持到槽位步进的条件归约留在实验目录，不作强度成果。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTCheck where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiKVRel using (⊴r)
open import OCF.Lean.YiLKIface using (OK; self-zero)
open import OCF.Lean.YiLLLeafNeg using (conflict; module Fin)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

PresJ : (ℓ j : L) → j ≤ ℓ → Set
PresJ ℓ j w = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (ν t : E.T) → GR.Rd j ν
  → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))

SlotBase : ∀ k h → Base (nd (sΩ k) h) → E.T → E.T → Set
SlotBase k h B ν t = GR.R k (E.ψ ν t ∷ []) (proj₁ (B k (ink self)))

zero-target : (o : Ok zero) (r : Rb zero) (B : Base zero) → OK B
  → (t : E.T) (β : Tr⁺ zero) → GR.R zero (E.ψ [] t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R zero a x
  → GR.R zero (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ zero o r B zero self β x))
zero-target = self-zero

h₁ : Tr zero → L
h₁ c = zero ⊕ ↑ zero c

rd₀ : GR.Rd zero []
rd₀ = GR.c0 refl

base-ok : OK (B₀ (tw 1))
base-ok i u = ⊴r

base-empty : SlotBase zero h₁ (B₀ (tw 1)) [] []
base-empty = H.m1 refl H.mz

no-base-one : SlotBase zero h₁ (B₀ (tw 1)) [] (E.natT 1) → ⊥
no-base-one m = conflict (E.hd< (E.ar< E.[]<)) (Fin.one-ref m)

no-ok→base : (OK (B₀ (tw 1)) → SlotBase zero h₁ (B₀ (tw 1)) [] (E.natT 1)) → ⊥
no-ok→base f = no-base-one (f base-ok)
```

以下是一个槽位步进样例：源是实际 `tw 1`，目标是零层，分支恒为树 1，空前缀、链的第 0 步。
它实填旧步进的两个关系前提；不代表一切前缀或一切分支的步进。
```agda
sample-child : (η : E.T) → GR.R (tw 1) (E.fsT (E.Ωs []) (E.γT (η ++ E.Ωs []) [] zero)) (suc zero)
sample-child η = H.m1 refl H.mz

sample-low : (η : E.T) → GR.R zero (E.γT (η ++ E.Ωs []) [] zero) (suc zero)
sample-low η = H.m1 refl H.mz

sample-step : (o : Ok (tw 1)) (r : Rb (tw 1))
  → GR.R zero (E.γT (E.Ωs []) [] (suc zero))
      (proj₁ (ψ (tw 1) o r (B₀ (tw 1)) zero (ink self)
        (B₀ (tw 1) zero (ink self)) (suc zero)))
sample-step o r = zero-target tt tt (B₀ zero) (λ i u → ⊴r) [] (Ωt zero)
  (H.m1 refl H.mz) {a = E.natT 1} {x = suc zero}
  (H.m1 {t = E.natT 1} {x = zero} refl H.mz)
```

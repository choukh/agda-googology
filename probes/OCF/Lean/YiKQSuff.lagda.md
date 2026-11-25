# 读回孩子的 Lift₂ 与 K(2) 的条件出口
> 验收文件（读记号）。编译定理：`Lift₁` 与 `Lift₂` 推出主线第 2 项的 `M⁰` 下界；再加该推导的出口条件 `Exᴴ` 得 K(2)。
> 来源：语义孩子接口照 `YiLTKid.Sem`，读回桥照 `YiKCSem.rr≼` 反向写；前提实填 `kid`、零与后继孩子及 `lift-zero`，完整的两个 Lift 与出口条件未实填。
> 第 2 层的定义、折叠与表均未改；不声称已提高无条件下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKQSuff where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
open import OCF.Lean.YiRBFam using (OKB)
open import OCF.Lean.YiHCRel using (M⁰; mz; m1; mw; Exᴴ; exitᴴ; module G⁰)
open import OCF.Lean.YiANFam using (ψᴺ)
open import OCF.Lean.YiKQRel
open import OCF.Lean.YiKQFold using (module Fold)
open import OCF.Lean.YiMTValue using (Kᶻ)
import OCF.Lean.YiKVRel as KV
import OCF.Lean.YiBRValue as BR
open import OCF.Align.Value using (_≼_; z≼; s≼s; l≼; ≼l; ≼-trans)
import OCF.Align.EboLeanDef as E

Kdˢ : (c : Tr (tw 1)) → E.T → Tr (h₂ c) → Set
Kdˢ c s y = ∀ v → Pc c v → (B : Base (h₂ c)) → OKB B
  → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 []) (proj₁ β)
  → M⁰ (ψᴺ 0 s) (proj₁ (ψ (h₂ c) (proj₂ o² c) (rbᶻ (h₂ c)) B zero v β y))

kid : Kid₂
kid = record { Kd = Kdˢ ; foldᶜ = λ c v pc B ok β hβ k → k v pc B ok β hβ }
module S = Top kid

Lift₂ : Set
Lift₂ = ∀ {η c} → A.M¹ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₂ c)))

child-zero : ∀ c → Kdˢ c [] zero
child-zero c v pc B ok β hβ = hβ

child-one : ∀ c → Kdˢ c (E.natT 1) (suc zero)
child-one c v pc B ok β hβ = G⁰.m-next β refl (λ n → refl) hβ

nonempty : S.M² (E.natT 1) (suc zero)
nonempty = m1 refl mz

sample : M⁰ (ψᴺ 0 (E.natT 1))
  (proj₁ (ψ ℓ² o² r² (B₀ ℓ²) zero (z≤ ℓ²) (Ωt zero) (suc zero)))
sample = G⁰.m-next (Ωt zero) refl (λ n → refl) (m1 refl mz)

lift-zero : Kdˢ zero (E.Ωt []) (proj₁ (Ωt (h₂ zero)))
lift-zero v (inj₁ refl) B ok β hβ = mw (G⁰.m-next β refl (λ n → refl) hβ) (◃l 0)
lift-zero v (inj₂ refl) B ok β hβ = mw (G⁰.m-next β refl (λ n → refl) hβ) (◃l 0)

base² : A.Lift₁ → S.GB² (B₀ ℓ²)
base² = S.gb₀

mK2 : (l₁ : A.Lift₁) → (l₂ : Lift₂) → M⁰ (E.EBOψ 3) (twᶻ 2)
mK2 l₁ l₂ = Fold.LF² kid (B₀ ℓ²) (base² l₁) S.wu (Ωt zero) (m1 refl mz) (S.leaf² l₂) (S.leafSp l₂)

read≤ : (x : Tr zero) → KV.readRW x ≼ BR.readRW x
read≤ zero = z≼
read≤ (suc x) = s≼s (read≤ x)
read≤ (lim f _) = l≼ (λ n → ≼l n (read≤ (f n)))

K2 : (l₁ : A.Lift₁) → (l₂ : Lift₂) → Exᴴ (mK2 l₁ l₂) → Kᶻ 2
K2 l₁ l₂ ex h = ≼-trans (exitᴴ {s = E.EBOψ 3} {x = twᶻ 2} (mK2 l₁ l₂) ex h) (read≤ (twᶻ 2))
```

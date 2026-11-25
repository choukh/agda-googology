# Leaf/Lift 最小前提检查
验收文件（读记号）；编译定理：零层的 ω、ω+1 满足 `R`，但均不满足实际 `domsᵍ.Gl`。
`Gl` 字面要求 Ω 树；零层仅接受树 1，`gl-one` 给出非空对照。按简报第 0 步停止。
没有否定 `Leaf` 或 `Lift`，没有修改树、折叠、合法性或共享接口；入口为本文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLLPrem where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiAbsGIface using (Doms)
open import OCF.Lean.YiGIInst using (domsᵍ)
open Doms domsᵍ using (Gl)

nat₀ : ℕ → Tr zero
nat₀ zero = zero
nat₀ (suc n) = suc (nat₀ n)

ω₀ : Tr zero
ω₀ = lim nat₀ (λ n → ◃s)

ω₀+1 : Tr zero
ω₀+1 = suc ω₀

r-ω₀ : GR.R zero (E.natT 1) ω₀
r-ω₀ = H.mw (H.m1 refl H.mz) (◃l 1)

r-ω₀+1 : GR.R zero (E.natT 1) ω₀+1
r-ω₀+1 = H.mw r-ω₀ ◃s

noGl-ω₀ : Gl zero ω₀ → ⊥
noGl-ω₀ ()

noGl-ω₀+1 : Gl zero ω₀+1 → ⊥
noGl-ω₀+1 ()

gl-one : Gl zero (suc zero)
gl-one = refl

gl-exact : ∀ k (x : Tr k) → Gl k x → x ≡ proj₁ (O.Ωt k)
gl-exact k x g = g
```

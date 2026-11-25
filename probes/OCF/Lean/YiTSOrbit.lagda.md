# 本层回灌链的记号出口

验收文件；编译定理。`Atω` 以 `YiSSOmega.Self.PFω` 实填不读记号的 `YiTSMachine`，链归纳只用既有抽象定理。
`orbit-ok` 对 ω 形状层号的一切 `Ok`、表、底与底值成立，底值需对着 Ω_ω；它没有补朝第 0 层的保持。
来源：`YiAbsGSuff.Chain`、`YiSSOmega`、`YiTSNote.fsTΩS`；没有改变树、折叠或合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTSOrbit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Nat.Properties using (≤-refl)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiHCRel using (mw)
open import OCF.Lean.YiLTLift using (module Wω; module Hω)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLLow using (s0; ss)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiSSOmega using (module Omega)
open import OCF.Lean.YiTSMachine using (module Machine)
open import OCF.Lean.YiTSNote using (fsTΩS)
open import OCF.Lean.YiAbsGEbo using (refᴱ)
import OCF.Align.EboLeanDef as E

module Oω = Omega fn (λ n → n) (λ _ → refl) (λ _ → inc tt self) (λ n → ss s0 , refl)

base-ok : Wω.Mω (E.Ωt ωᵀ) (proj₁ (Ωt Wω.Lω))
base-ok = Hω.leafω (λ _ → ≤-refl)

module Atω (o : Ok Wω.Lω) (r : Rb Wω.Lω) (B : Base Wω.Lω) (β : Tr⁺ Wω.Lω) where
  module K = Machine.Keep Wω.Lω o r B refᴱ Wω.Mω Hω.ψω

  self-law : K.SelfKeep
  self-law _ β′ _ hP m = Oω.Self.PFω (proj₁ o) (proj₂ o) r B β′ hP m

  weak-law : K.Weak
  weak-law m d = mw m d

  module C = K.Orbit self-law weak-law β [] (E.Ωt ωᵀ)
  open C public using (z)

  γ-eq : ∀ k → C.γ k ≡ E.γT (E.Ωt (E.sucT ωᵀ)) ωᵀ k
  γ-eq zero = refl
  γ-eq (suc k) = trans (cong Hω.ψω (γ-eq k))
    (cong Hω.ψω (sym (fsTΩS (E.sucT ωᵀ) refl (E.γT (E.Ωt (E.sucT ωᵀ)) ωᵀ k))))

  orbit-ok : Wω.Mω (E.Ωt ωᵀ) (proj₁ β) → ∀ k →
             Wω.Mω (E.γT (E.Ωt (E.sucT ωᵀ)) ωᵀ k) (z k)
  orbit-ok h k = subst (λ t → Wω.Mω t (z k)) (γ-eq k) (C.chain h (mw h (◃l zero)) k)
```

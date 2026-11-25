# 回灌展开的条件出口

验收文件；编译定理。`covered`、`note-covered` 把链的逐项覆盖送到折叠；后者另用只说记号的 `YiTSNote.note`。
覆盖条件仍混合树与记号，未从 `StepS` 的两个归纳前提导出；本文件没有完成 `TreeStep` 到 `StepS` 的桥。
条件在 `ZeroCase` 的 (η = 1, x = 0) 实例可满足；回灌链保持直接调用 `YiLTFold.chain`，未重证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTSExit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow
open import OCF.Lean.YiTSStep using (module Step)
open import OCF.Lean.YiTSNote using (note)
open import OCF.Lean.YiHCRel using (M⁰; m1; mz; mL; mw; mU; module G⁰)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
import OCF.Align.EboLeanDef as E
open E using (cof; cω; c1; fsn; γT; pred; natT)
open import OCF.Lean.YiKVRel using (⊴r)
open import OCF.Lean.YiCLLow using (s0)
open import OCF.Lean.YiHCFold using (GB; mkGB)
open import OCF.Lean.YiLTFold using (chain; Qu)

module Exit (x : Tr zero) (o : Ok (h₁ (suc x))) (r : Rb (h₁ (suc x)))
            (B : Base (h₁ (suc x))) (w : zero ≤ h₁ x) (β : Tr⁺ zero) where
  open Step x o r B w β

  covered : ∀ t → cof t ≡ cω →
            (∀ k → Σ ℕ λ m → M⁰ (fsn t k) (proj₁ (parts m))) →
            M⁰ t (proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x))))))
  covered t e cov = subst (M⁰ t) (sym tree-step)
    (mL e (λ k → G⁰.m-cum parts (proj₁ (cov k)) (proj₂ (cov k))))

  note-covered : ∀ η → cof η ≡ c1 →
                 (∀ k → Σ ℕ λ m → M⁰ (ψᴺ 0 (γT (E.Ωt η) (pred η) k)) (proj₁ (parts m))) →
                 M⁰ (ψᴺ 0 (E.Ωt η))
                   (proj₁ (ψ (h₁ (suc x)) o r B zero (inu (λ _ → w)) β (proj₁ (Ωt (h₁ (suc x))))))
  note-covered η e cov = covered (ψᴺ 0 (E.Ωt η)) (proj₁ (note η e))
    (λ k → proj₁ (cov k) ,
      subst (λ t → M⁰ t (proj₁ (parts (proj₁ (cov k))))) (sym (proj₂ (note η e) k)) (proj₂ (cov k)))

module ZeroCase where
  o : Ok (fn 1)
  o = tt , λ _ → tt
  r : Rb (fn 1)
  r = rb-no (fn 1)
  Bs : Base (fn 1)
  Bs = B₀ (fn 1)
  module Z = Step zero o r Bs self (Ωt zero)
  module X = Exit zero o r Bs self (Ωt zero)

  gb : GB 0 Bs []
  gb = mkGB (λ { s0 → ⊴r }) (λ { s0 → m1 refl mz })

  chain-ok : ∀ k → M⁰ (γT (Ωᴺ 1) [] k) (Z.chain (suc k))
  chain-ok = chain o r s0 [] Bs gb {a = Ωᴺ 1} {ν = []}
    {g = λ z → up zero tt (suc z) (z◃ z ◃s)} refl refl (λ η c l → mU mz (mw l ◃s))

  cover : ∀ k → Σ ℕ λ m → M⁰ (ψᴺ 0 (γT (Ωᴺ 1) [] k)) (proj₁ (Z.parts m))
  cover k = suc k , mw (Qu tt tt (B₀ zero) self (Ωt zero) (m1 refl mz) (chain-ok k)) (◃l zero)

  result : M⁰ (ψᴺ 0 (Ωᴺ 1))
    (proj₁ (ψ (fn 1) o r Bs zero (inu (λ _ → self)) (Ωt zero) (proj₁ (Ωt (fn 1)))))
  result = X.note-covered (natT 1) refl cover
```

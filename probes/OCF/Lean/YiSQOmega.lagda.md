# 有限基本列的极限与 ω+1 的实际前提
验收文件，读记号；编译定理：finite-fsn、omega-all，ω+1 的读回与归纳假设、实际第 0 行。
来源：YiSQNat.nat-all、YiQLRead.limit、YiCLPhi.inv-lim/rep1、YiQLSuccessor.first。
SecondMissing、StepMissing 是未填类型，没有居民；不声称一般 Step、MinimalGoal 或 BranchNeed。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSQOmega where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiCLCrit as Crit
import OCF.Lean.YiCLPhi as Phi
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiQLRead as Q
import OCF.Lean.YiQLSuccessor as C
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiSQNat as N
finite-fsn : ∀ η → E.cof η ≡ E.cω → (f : ℕ → ℕ) → (∀ n → E.fsn η n ≡ E.natT (f n))
  → ∀ {d} → K.M⁰ η d → Q.Need η d
finite-fsn η e f fs {d} m = Q.limit η d e (λ n → subst (λ t → Q.Need t d) (sym (fs n))
  (N.nat-all (f n) (subst (λ t → K.M⁰ t d) (fs n) (Phi.inv-lim e m n))))
omega-all : ∀ {d} → K.M⁰ Phi.ωᵀ d → Q.Need Phi.ωᵀ d
omega-all = finite-fsn Phi.ωᵀ refl (λ n → n) Phi.rep1
ω : B.Tr B.zero
ω = B.lim H.nat (λ n → B.◃s)
read-ω : K.M⁰ Phi.ωᵀ ω
read-ω = K.mL refl (λ n → subst (λ t → K.M⁰ t ω) (sym (Phi.rep1 n))
  (K.mw (Crit.natM n) (B.◃l n)))
need-ω : Q.Need Phi.ωᵀ ω
need-ω = omega-all read-ω
read-next : K.M⁰ (E.pred (E.sucT Phi.ωᵀ)) ω
read-next = read-ω
need-next-input : Q.Need (E.pred (E.sucT Phi.ωᵀ)) ω
need-next-input = need-ω
next-cof : E.cof (E.sucT Phi.ωᵀ) ≡ E.c1
next-cof = refl
module Actual = C.Row ω (proj₂ S.okay (B.suc ω)) (MT.rbᶻ (S.child (B.suc ω)))
  (F.B₀ (S.child (B.suc ω))) (O.Ωt K.one) (λ i u → K.⊴r) (H.Mβ 0)
first-row : H.M 1 (Q.Target Phi.ωᵀ) (proj₁ (Actual.part 1))
first-row = Actual.first Phi.ωᵀ need-ω
SecondMissing : Set
SecondMissing = Actual.SecondRow Phi.ωᵀ
StepMissing : Set
StepMissing = Q.Need (E.sucT Phi.ωᵀ) (B.suc ω)
```

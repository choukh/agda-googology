# 有限 LF 的前提不能直接降读法或覆盖 ω 孩子
验收文件，读记号；编译否定：指定源 Ω 树不能降为 Ω₁；Rows 4 不满足 d = 1 的读回前提。
来源：源树否定调用 YiLRNeg.noN/QΩS；另证实际 ω 孩子的层号不等于任何 fn n。
只排除这三种具体前提，不否定一般 Step、SecondRow、最小实例或实际 BranchNeed。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSQPremise where
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.List using ([])
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiLRNeg as N
import OCF.Align.EboLeanDef as E
no-weaken-seed : H.M 5 (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (H.fn 5))) → ⊥
no-weaken-seed m = N.noN 5 m refl (N.QΩS (λ _ → H.fn 4) tt)
below-one : ∀ {x} → B._⊢_◃_ B.zero x (B.suc B.zero) → x ≡ B.zero
below-one B.◃s = refl
below-one (B.◃t d e) = ⊥-elim (K.¬◃z (subst (λ y → B._⊢_◃_ B.zero _ y) (below-one e) d))
no-positive-zero : ∀ {t} → E.cof t ≡ E.c1 → K.M⁰ t B.zero → ⊥
no-positive-zero () K.mz
no-positive-zero e (K.mL eL h) = N.c1≢cω (trans (sym e) eL)
no-positive-zero e (K.mw m d) = K.¬◃z d
no-domain4 : K.M⁰ (E.natT 4) (B.suc B.zero) → ⊥
no-domain4 (K.m1 e m) = no-positive-zero refl m
no-domain4 (K.mL () h)
no-domain4 (K.mw m e) = no-positive-zero refl (subst (K.M⁰ (E.natT 4)) (below-one e) m)
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiSQOmega as Ω
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong)
childS : B.L → B.L
childS (B.nd B.sS h) = h tt
childS _ = B.zero
no-limit-fin : ∀ n g → B.nd B.sL g ≡ H.fn n → ⊥
no-limit-fin zero g ()
no-limit-fin (suc n) g ()
no-finite-shape : ∀ n → S.child Ω.ω ≡ H.fn n → ⊥
no-finite-shape zero ()
no-finite-shape (suc n) e = no-limit-fin n (λ k → K.two B.⊕ B.↑ B.zero (H.nat k)) (cong childS e)
```

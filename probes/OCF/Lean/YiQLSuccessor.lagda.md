# 后继读回的实际回灌行
验收文件，读记号；编译定理：指定后继行是累计极限，归纳假设给 γ 链第 0 行。
from-rows 仍以 Rows 为前提；SecondRow 是第 1 行的未填义务，不声称 Step 或 BranchNeed。
来源：展开 YiTBRow 的后继行；γ 链与累计极限出口据 YiTBFam.LFΩ，正规叶算式复用 JiaAuditClosure。
层号、表、底与起点取变量；不改变树、折叠或合法性。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQLSuccessor where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiCLLow as L
import OCF.Lean.YiRBFam as RF
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiANFam using (cofG; fsnG)
import OCF.Lean.YiQLRead as Q
module Row (d : B.Tr B.zero)
  (o : P.Ok (S.child (B.suc d))) (r : TB.Rb (S.child (B.suc d)))
  (base : F.Base (S.child (B.suc d))) (beta : O.Tr⁺ K.one)
  (ok : RF.OKB base) (hb : H.M 1 (E.Ωt (E.natT 1)) (proj₁ beta)) where
  a : B.L
  a = S.child d
  cb : F.Base a
  cb i u = base i (P.inc tt u)
  feed : B.Tr a → B.Tr a
  feed x = proj₁ (O.next⁺ (TB.ψ a (proj₂ o tt) (proj₂ r tt) cb a P.self (base a (P.inc tt P.self)) x))
  chain : ℕ → B.Tr a
  chain = O.iter feed B.zero
  part : ℕ → O.Tr⁺ K.one
  part n = O.next⁺ (TB.ψ a (proj₂ o tt) (proj₂ r tt) cb K.one (S.lower d) beta (chain n))
  out : O.Tr⁺ K.one
  out = TB.ψ (S.child (B.suc d)) o r base K.one (S.lower (B.suc d)) beta (proj₁ (O.Ωt (S.child (B.suc d))))
  row : out ≡ O.limc⁺ part
  row = refl
  first : ∀ μ → Q.Need μ d → H.M 1 (E.ψ (E.natT 1) (E.Ωt μ) ∷ []) (proj₁ (part 1))
  first μ ih = H.mwN 1 (H.mwN 1
    (ih (proj₂ o tt) (proj₂ r tt) cb beta (λ i u → ok i (P.inc tt u)) hb)
    (TB.mono a (proj₂ o tt) (proj₂ r tt) cb K.one (S.lower d) beta
      (K.⊴-◃ (ok a (P.inc tt P.self)) (B.◃l zero)))) (B.◃l zero)
  Rows : E.T → Set
  Rows μ = ∀ n → H.M 1 (E.ψ (E.natT 1) (E.γT (E.Ωs μ) μ n) ∷ []) (proj₁ (part (suc n)))
  from-rows : ∀ μ → E.cmpᵀ (E.sucT μ) (E.natT 1) ≡ E.gt → Rows μ
    → H.M 1 (Q.Target (E.sucT μ)) (proj₁ out)
  from-rows μ gt rows = K.mL (cofG (E.natT 1) (E.Ωs μ) gt (cof-regular μ))
    (λ n → subst (λ t → H.M 1 t (proj₁ out))
      (sym (trans (fsnG (E.natT 1) (E.Ωs μ) n gt (cof-regular μ))
        (cong (λ t → E.ψ (E.natT 1) t ∷ []) (fs-regular μ (E.γT (E.Ωs μ) μ n)))))
      (L.cumJ 1 part (suc n) (rows n)))
  SecondRow : E.T → Set
  SecondRow μ = H.M 1 (E.ψ (E.natT 1) (E.γT (E.Ωs μ) μ 1) ∷ []) (proj₁ (part 2))
```

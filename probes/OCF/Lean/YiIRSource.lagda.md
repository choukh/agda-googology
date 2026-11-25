# 目标基本列参数的实际源关系
验收文件；全部Γ参数在每个实际内分支上有源层R证书，包含固定输入零。
证法仅用Ω地板，不给零层折叠值保持，也不说明值随回灌链增长；目标见 YiIRTarget。
来源：沿用 YiLBActual 的地板/raiseR 组合，调用 YiGTGen 公共引理；实例固定原最小表。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiIRSource where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Data.Sum using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import OCF.Lean.YiIRTarget using (Γ)
import OCF.Align.EboLeanDef as E
import OCF.Align.EBO as EB
import OCF.Lean.YiAZStart as A
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as W
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGTGen as GT
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiNLTop2 as NL
import OCF.Lean.YiNLRaise as NR
open import OCF.Lean.YiNLCtx using (prefix)

Γ-bound : ∀ n → Γ n E.<ᵀ E.Ωt (E.Ωt (E.natT 1))
Γ-bound zero = E.hd< (E.lv< (EB.natT<Ωs 1 []))
Γ-bound (suc n) = E.hd< (E.lv< (EB.natT<Ωs 1 []))
leaf-Γ : ∀ n → GR.R (B.tw 2) (Γ n) (proj₁ (O.Ωt (B.tw 2)))
leaf-Γ n = LL.rdown (B.tw 2) (inj₁ (Γ-bound n))
  (NL.leaf-tw2 (GR.rd-child (B.sΩ (B.tw 1)) (A.D.Step.child 1) B.zero LL.rdΩ))

slot-Γ : ∀ n → GR.R (B.tw 2) (Γ n) (proj₁ (A.D.baseᴱ 3 (B.tw 2) (W.ink W.self)))
slot-Γ n = subst (λ f → GR.R (B.tw 2) (Γ n) (proj₁ (f (B.tw 2) (W.ink W.self))))
  (sym (A.D.baseᴱ-eq 3))
  (GT.weakenᴿ (B.tw 2) (leaf-Γ n)
    (TF.ψ-⊵ B.Λ W.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) (B.tw 2)
      (W.inc 3 (W.ink W.self)) (O.Ωt (B.tw 2)) (A.D.pre 3)))

branch-Γ : ∀ n d → GR.R (B.tw 2) (Γ n) (A.N.branch d)
branch-Γ n d = subst (λ f → GR.R (B.tw 2) (Γ n) (f d)) (sym A.N.branch-eq)
  (GT.weakenᴿ (B.tw 2) (slot-Γ n)
    (TF.ψ-⊵ (B.tw 2) (W.Ok-tw 2) (A.D.Step.child-table 2 B.zero) A.N.base₀
      (B.tw 2) W.self (A.D.baseᴱ 3 (B.tw 2) (W.ink W.self)) (A.D.Step.g 1 d)))

child-family : ∀ n d → GR.R (A.N.a d) (E.Ωt (Γ n)) (proj₁ (O.Ωt (A.N.a d)))
child-family n d = NR.raiseR (B.tw 2) (prefix (B.tw 2)) [] (GR.c0 refl)
  (NL.leaf-tw2 (GR.c0 refl)) (branch-Γ n d)
source-family : ∀ n d → GR.R A.N.h (E.Ωt (Γ n)) (A.N.Inner.g d)
source-family n d = subst (λ f → GR.R A.N.h (E.Ωt (Γ n)) (f d))
  (sym A.N.Inner.g-eq) (H.mU H.mz (child-family n d))
```

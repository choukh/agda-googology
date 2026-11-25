# T[0]的必要子列与实际底界
验收文件；S(m)=T[0][0][m]，S(0)、S(1)对实际P₀的全HC值界已证；S(2)及T[0]值界未证。
S-below-T0只给必要子问题，不否定任何M或链点；不代替本批n=0、1的逐项支配。
来源：底界复用YiLBInv.from⊴/beta3、YiTBFam.ψ-⊵，局部值界复用YiFRStations.k1/k2，子列出口复用YiFNTarget.walk-lower，复制列等式复用YiCLPhi.rep1。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAZLocal where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
open import OCF.Lean.YiAZStart
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as W
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiLBInv as LB
import OCF.Lean.YiE4Default as Df
import OCF.Lean.YiFRStations as FS
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiExSuff as EX
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiCLPhi as CP
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiFNTarget as FT
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl)
open EX.ExSuff GI.gradedᵍ GI.domsᵍ using (Keel⁻)
opaque
  β-prior : proj₁ D.β ≡ Keel⁻.twc GI.keelᴱ 2
  β-prior = trans (cong proj₁ D.β-eq) (trans (cong proj₁ (Df.beta-eq 3)) LB.beta3)
out-base : ∀ d → K.readRW (proj₁ D.β) ≼ K.readRW (proj₁ (N.Inner.out d))
out-base d = subst (λ f → K.readRW (proj₁ D.β) ≼ K.readRW (proj₁ (f d)))
  (sym N.Inner.out-eq)
  (LB.from⊴ (TF.ψ-⊵ N.h N.o N.rr N.base₁ B.zero (W.z≤ N.h) D.β (N.Inner.g d)))
S : ℕ → E.T
S m = E.fsn (E.fsn (T 0) 0) m
S-form : ∀ m → S m ≡ E.ψ [] (E.Ωt (E.Ωt (E.natT m))) ∷ []
S-form m = cong (λ t → E.ψ [] (E.Ωt (E.Ωt t)) ∷ []) (CP.rep1 m)
S0 : S 0 ≡ Keel⁻.row GI.keelᴱ 1
S0 = refl
S1 : S 1 ≡ Keel⁻.row GI.keelᴱ 2
S1 = refl
S2 : S 2 ≡ E.ψ [] (E.Ωt (E.Ωt (E.natT 2))) ∷ []
S2 = refl
S0-low : (h : SI.E.HC (S 0)) → SI.E.tree h ≼ K.readRW (P 0)
S0-low h = ≼-trans (FS.k1 h) (≼-trans (FS.station-step 1)
  (≼-trans (subst (λ x → K.readRW (Keel⁻.twc GI.keelᴱ 2) ≼ K.readRW x) (sym β-prior)
    (≼-refl _)) (out-base (N.Inner.chain 0))))
S1-low : (h : SI.E.HC (S 1)) → SI.E.tree h ≼ K.readRW (P 0)
S1-low h = ≼-trans (FS.k2 h)
  (≼-trans (subst (λ x → K.readRW (Keel⁻.twc GI.keelᴱ 2) ≼ K.readRW x) (sym β-prior)
    (≼-refl _)) (out-base (N.Inner.chain 0)))
opaque
  hc-S : ∀ m → SI.E.HC (S m)
  hc-S m = SI.conv (RT.hω-inv (RT.hω-inv (XI.back (hc-T 0)) refl 0) refl m)

S-below-T0 : ∀ m (h : SI.E.HC (S m)) (h₀ : SI.E.HC (T 0)) → SI.E.tree h ≼ SI.E.tree h₀
S-below-T0 m h h₀ = ≼-trans (XI.tree-back h)
  (FT.walk-lower (T 0) (0 ∷ m ∷ []) (refl , refl , tt) refl (XI.back h) h₀)
```

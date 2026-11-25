# 实际链上的 NF/G 验收不变量
验收文件；初项与旧参数区间在实际各链点成立；增长一步 InvStep 尚未实填。
量化仅针对原 Step.chain 2 的输出；条件 step→first 不增加无条件强度。
来源：Buchholz 3.3 的 NF/G 条件、3.6/tow 的参数界；实际底不换成 B₀。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLBInv where
open import OCF.Lean.YiLBStart
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase
import OCF.Align.EboLeanClosure as C
import OCF.Align.EboLeanView as V
import OCF.Align.EboLeanTree as ET
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiFRStations as FS
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiKVRel as K
open import OCF.Lean.YiExInst using (back; tree-back)
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Lean.YiGTGen using (app≤ν)
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl)
open import OCF.Lean.YiTBFam using (ψ-⊵)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiMTTab as MT

open import OCF.Lean.YiExSuff
open ExSuff GI.gradedᵍ GI.domsᵍ using (Keel⁻)

param : ℕ → E.T
param q = V.fΩ w (V.γ w q)
ref : ℕ → E.T
ref q = E.ψ [] (param q) ∷ []
ref-eq : ∀ q → E.fsn (E.EBOψ 3) q ≡ ref q
ref-eq q = V.fω-eq (V.w6 refl refl w) q
ref-NF : ∀ q → NF (ref q)
ref-NF q = subst NF (ref-eq q) (C.cl-fsn-NF (ET.nf-tower 3) refl q)
ref-param-NF : ∀ q → NF (param q)
ref-param-NF q = nfp-a (nf-hd (ref-NF q))
ref-param-G : ∀ q → GB [] (param q) (param q)
ref-param-G q = nfp-g (nf-hd (ref-NF q))
opaque
  ref-HC : ∀ q → SI.E.HC (ref q)
  ref-HC q = SI.conv (ET.hc (ref-NF q) (c∷ c[]))

Inv : ℕ → Set
Inv q = (a : E.T) → NF a → GB [] a a → a ≤ᵀ param q → (h : SI.E.HC (E.ψ [] a ∷ []))
  → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 q)))

beta3 : proj₁ (GI.betaᴱ 3) ≡ Keel⁻.twc GI.keelᴱ 2
beta3 = refl

from⊴ : ∀ {x y : B.Tr B.zero} → x K.⊴ y → K.readRW x ≼ K.readRW y
from⊴ K.⊴r = ≼-refl _
from⊴ (K.⊴◃ d) = K.◃→≼ d

floor : ∀ q → (h : SI.E.HC (ref 0))
  → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 q)))
floor q h = ≼-trans (FS.k2 h)
  (from⊴ (ψ-⊵ (B.tw 3) (P.Ok-tw 3) (MT.rbᶻ (B.tw 3)) (GI.baseᴱ 3)
    B.zero (P.z≤ (B.tw 3)) (GI.betaᴱ 3) (FR.Step.g 2 (FR.Step.chain 2 q))))

old-part : ∀ q → (a : E.T) → NF a → GB [] a a → a ≤ᵀ param 0 → (h : SI.E.HC (E.ψ [] a ∷ []))
  → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 q)))
old-part q a na ga le h = ≼-trans (tree-back h)
  (≼-trans (mono≤ⁿ (nf-ψ n[] na ga) (ET.nf-tower 2) (c∷ c[]) (back h) (back (ref-HC 0)) (app≤ν [] [] le))
    (≼-trans (SI.toL-tree (back (ref-HC 0))) (floor q (SI.conv (back (ref-HC 0))))))

initial : SI.E.HC (ref 0) → Inv 0
initial _ = old-part 0

inv0 : Inv 0
inv0 = initial (ref-HC 0)

sample : NF (param 1) × GB [] (param 1) (param 1) × (param 1 ≤ᵀ param 1) × SI.E.HC (ref 1)
sample = ref-param-NF 1 , ref-param-G 1 , inj₂ refl , ref-HC 1

pointwise : ∀ q → Inv q → (h : SI.E.HC (ref q))
  → SI.E.tree h ≼ K.readRW (proj₁ (FR.Step.out 2 (FR.Step.chain 2 q)))
pointwise q iv = iv (param q) (ref-param-NF q) (ref-param-G q) (inj₂ refl)

sample-band : NF (param 1) × GB [] (param 1) (param 1) × (param 0 E.<ᵀ param 1)
  × (param 1 ≤ᵀ param 1) × SI.E.HC (ref 1)
sample-band = ref-param-NF 1 , ref-param-G 1 , V.val-mono w 0 , inj₂ refl , ref-HC 1

InvStep : Set
InvStep = ∀ q → Inv q → Inv (suc q)

step→first : InvStep → FR.FirstMissing
step→first st = 1 , pointwise 1 (st 0 inv0)
```

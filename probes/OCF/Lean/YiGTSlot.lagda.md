# 路径证据树给出补前缀的槽位步进
验收文件（读记号）；`IndexTree` 经一般保持给 SlotPres，再给 YiSU 的 StepU′。
不假定 Leaf，不声称每层都有 IndexTree；原 StepU 与新增前缀条件不同。
入口：`slot-pres`、`step′`、`kit`；前提实例见 YiGTInst。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTSlot where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK)
open import OCF.Lean.YiLKSlot using (low-from)
open import OCF.Lean.YiSUIface using (PrefixU; StepU′)
open import OCF.Lean.YiMWPre using (fsT++)
open import OCF.Lean.YiGTIndex using (SlotPres; Kit)
open import OCF.Lean.YiGTDirect
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

slot-pres : ∀ ℓ → IndexTree ℓ → SlotPres ℓ
slot-pres ℓ it o r B gb t pref p ν nu m = direct ℓ it o r B gb t pref
  (at ℓ p) (posW ℓ p) ν (slot-index ℓ it o r p ν nu)
  (B (at ℓ p) (posW ℓ p)) (pref p ν nu) m

step-from-slot : ∀ ℓ → SlotPres ℓ → StepU′ ℓ
step-from-slot ℓ sp o r B gb t pref a p ν nu e g n c lc m = low-from ℓ p
  (subst (λ z → GR.R (at ℓ p) (E.ψ ν z ∷ [])
    (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c))))
    (sym (fsT++ t a (E.γT (t ++ a) ν n) e)) (sp o r B gb t pref p ν nu m))

step′ : ∀ ℓ → IndexTree ℓ → StepU′ ℓ
step′ ℓ it = step-from-slot ℓ (slot-pres ℓ it)

kit : ∀ ℓ → IndexTree ℓ → Kit ℓ
kit zero it = tt
kit (nd s h) it = slot-pres (nd s h) it , step′ (nd s h) it , λ c → kit (h c) (proj₂ it c)

layer-index : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → LayerIndex ℓ o r → SlotIndex ℓ o r
layer-index zero o r li ()
layer-index (nd s h) o r li = proj₁ li

step-layer : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → LayerIndex ℓ o r
  → (B : Base ℓ) → OK B → (t : E.T) → PrefixU B t
  → (a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (OCF.Lean.YiLKIface.feed ℓ o r B p g c)
step-layer ℓ o r li B gb t pref a p ν nu e g n c lc m = low-from ℓ p
  (subst (λ z → GR.R (at ℓ p) (E.ψ ν z ∷ [])
    (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c))))
    (sym (fsT++ t a (E.γT (t ++ a) ν n) e))
    (layer-at ℓ o r li B gb t pref (at ℓ p) (posW ℓ p) ν (layer-index ℓ o r li p ν nu)
      (B (at ℓ p) (posW ℓ p)) (pref p ν nu) m))

OmegaStepAt : (k : L) (h : Tr k → L) → Ok (nd (sΩ k) h) → Rb (nd (sΩ k) h) → Set
OmegaStepAt k h o r = (B : Base (nd (sΩ k) h)) → OK B
  → (t : E.T) → PrefixU B t → (a ν : E.T) → GR.Rd k ν → E.cof a ≡ E.cΩ ν
  → (g : Tr k → Tr (nd (sΩ k) h)) (n : ℕ) (c : Tr k)
  → GR.R k (E.γT (t ++ a) ν n) c
  → GR.R (nd (sΩ k) h) (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.R k (E.γT (t ++ a) ν (suc n))
      (proj₁ (ψ (nd (sΩ k) h) o r B k (ink self) (B k (ink self)) (g c)))

omega-step-at : ∀ k h (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h))
  → LayerIndex (nd (sΩ k) h) o r → OmegaStepAt k h o r
omega-step-at k h o r li B gb t pref a ν nu e g n c lc m =
  step-layer (nd (sΩ k) h) o r li B gb t pref a (inj₁ (inj₁ tt)) ν nu e g n c lc m
```

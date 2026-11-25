# 由叶律消去槽位起点，留下分级步进
验收文件；编译条件定理：`Leaf` 加全层 `StepU` 推出 `LowKeep`。
`nu-to`、`low-from` 按 `YiGIRel` 与 `YiGIBlock` 的槽位换型递归；弱化复用 `YiGICheck.rw-weak`。
`omega-step` 展开 Ω 形状的第一个槽位；未证明它能由较低源层的零目标保持得到。
入口：`steps→lowKeep`、`OmegaStep`、`omega-step`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLKSlot where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (_++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ⊴◃)
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiGICheck using (rw-weak)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ)
open import OCF.Lean.YiAbsGIface using (module Laws)
open import OCF.Lean.YiLKIface
open import OCF.Lean.YiLKFold using (slots→lowKeep; fromSlots)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

mutual
  nu-to : ∀ ℓ (p : Pos ℓ) {ν} → GR.Nu ℓ p ν → GR.Rd (at ℓ p) ν
  nu-to (nd s h) (inj₂ (c , q)) nu = nu-to⁼ (h c) q nu
  nu-to (nd (sΩ k) h) (inj₁ q) nu = nu-to⁼ k q nu

  nu-to⁼ : ∀ a (q : Pos⁼ a) {ν} → GR.Nu⁼ a q ν → GR.Rd (proj₁ (sl⁼ a q)) ν
  nu-to⁼ a (inj₁ _) nu = nu
  nu-to⁼ a (inj₂ p) nu = nu-to a p nu

mutual
  low-from : ∀ ℓ (p : Pos ℓ) {η} {x : Tr (at ℓ p)}
    → GR.R (at ℓ p) η x → GR.Low ℓ p η (fromBr ℓ p x)
  low-from (nd s h) (inj₂ (c , q)) m = low-from⁼ (h c) q m
  low-from (nd (sΩ k) h) (inj₁ q) m = low-from⁼ k q m

  low-from⁼ : ∀ a (q : Pos⁼ a) {η} {x : Tr (proj₁ (sl⁼ a q))}
    → GR.R (proj₁ (sl⁼ a q)) η x → GR.Low⁼ a q η (proj₂ (sl⁼ a q) x)
  low-from⁼ a (inj₁ _) m = m
  low-from⁼ a (inj₂ p) m = low-from a p m

r⊴ : ∀ ℓ {η x y} → GR.R ℓ η x → x ⊴ y → GR.R ℓ η y
r⊴ ℓ m ⊴r = m
r⊴ ℓ m (⊴◃ d) = rw-weak ℓ m d

start-from-leaf : Laws.Leaf gradedᵍ domsᵍ → ∀ ℓ → StartU ℓ
start-from-leaf lf ℓ o r B gb t a p ν nu e g = low-from ℓ p
  (r⊴ (at ℓ p) (lf (nu-to ℓ p nu))
    (⊴-trans (gb (at ℓ p) (posW ℓ p))
      (ψ-⊵ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g (fromBr ℓ p zero)))))

step-zero : StepU zero
step-zero = SlotU.step (KidU.slot kid-zero)

steps→pres : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → ∀ ℓ → PresU ℓ
steps→pres lf st = fromSlots (λ ℓ → record { start = start-from-leaf lf ℓ ; step = st ℓ })

steps→lowKeep : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → StepU ℓ) → Laws.LowKeep gradedᵍ domsᵍ
steps→lowKeep lf st = slots→lowKeep (λ ℓ → record { start = start-from-leaf lf ℓ ; step = st ℓ })

OmegaStep : (k : L) → (Tr k → L) → Set
OmegaStep k h = (o : Ok (nd (sΩ k) h)) (r : Rb (nd (sΩ k) h)) (B : Base (nd (sΩ k) h)) → OK B
  → (t a ν : E.T) → GR.Rd k ν → E.cof a ≡ E.cΩ ν
  → (g : Tr k → Tr (nd (sΩ k) h)) (n : ℕ) (c : Tr k)
  → GR.R k (E.γT (t ++ a) ν n) c
  → GR.R (nd (sΩ k) h) (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.R k (E.γT (t ++ a) ν (suc n))
      (proj₁ (ψ (nd (sΩ k) h) o r B k (ink self) (B k (ink self)) (g c)))

omega-step : ∀ k h → StepU (nd (sΩ k) h) → OmegaStep k h
omega-step k h st o r B gb t a ν rd e g n c lc m = st o r B gb t a (inj₁ (inj₁ tt)) ν rd e g n c lc m
```

`OmegaStep` 的目标为 k，源仍为 `nd (sΩ k) h`；`PresU k` 与各 `PresU (h c)` 的源均不同。
据此尚未得到对较低源层同形命题的递归，不把这一未完成前提解释为否定定理。

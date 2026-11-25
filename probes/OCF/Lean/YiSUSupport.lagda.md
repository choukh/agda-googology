# 根底与递归更新底的显式供给
验收文件；`Support` 在当前底上给 `PrefixU`，对嵌入行的每个实际更新底递归给同一证据。
`Rows` 逐层给起点与修正步进，不要求已知为假的全域 `Leaf`；没有替原 `Bdᵍ` 增加字段。
最小层有非空实例；根与孩子的供给分开命名，供实际折叠归约使用。
入口：`RootPrefix`、`Updated`、`Support`、`Rows`、`support-one`、`rows-one`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUSupport where
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ; rb-no)
open import OCF.Lean.YiLKIface using (StartU; OK)
open import OCF.Lean.YiLKSlot using (low-from; r⊴)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiSUIface using (PrefixU; StepU′)
open import OCF.Lean.YiSUMin using (step′-one; prefix-zero; rd-zero)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiKVRel using (⊴r)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

RootPrefix : ∀ ℓ → Base ℓ → E.T → Set
RootPrefix ℓ B t = PrefixU B t

Updated : ∀ s h → Ok (nd s h) → Rb (nd s h) → Base (nd s h)
  → Tr (nd s h) → (c : Ch s) → Base (h c)
Updated s h o r B x c i u = ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x

Support : ∀ ℓ → Ok ℓ → Rb ℓ → Base ℓ → E.T → Set
Support zero o r B t = ⊤
Support (nd s h) o r B t = RootPrefix (nd s h) B t ×
  (∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
    → Support (h c) (proj₂ o c) (proj₂ r c) (Updated s h o r B x c) (t ++ a))

UpdateSupply : ∀ s h (o : Ok (nd s h)) (r : Rb (nd s h)) → Base (nd s h) → E.T → Set
UpdateSupply s h o r B t = ∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
  → Support (h c) (proj₂ o c) (proj₂ r c) (Updated s h o r B x c) (t ++ a)

root : ∀ s h o r B t → Support (nd s h) o r B t → RootPrefix (nd s h) B t
root s h o r B t = proj₁

update : ∀ s h o r B t → Support (nd s h) o r B t → UpdateSupply s h o r B t
update s h o r B t = proj₂

Rows : L → Set
Rows zero = ⊤
Rows (nd s h) = (StartU (nd s h) × StepU′ (nd s h)) × ((c : Ch s) → Rows (h c))

start-one : StartU (fn 1)
start-one o r B gb t a (inj₂ (tt , inj₁ tt)) ν nu e g with rd-zero nu
... | refl = low-from (fn 1) (inj₂ (tt , inj₁ tt))
  (r⊴ zero (H.m1 refl H.mz)
    (⊴-trans (gb zero (inc tt self))
      (ψ-⊵ (fn 1) o r B zero (inc tt self) (B zero (inc tt self)) (g zero))))
start-one o r B gb t a (inj₂ (tt , inj₂ ())) ν nu e g

support-one : ∀ o r → Support (fn 1) o r (B₀ (fn 1)) []
support-one o r = prefix-zero , λ m c → tt

rows-one : Rows (fn 1)
rows-one = (start-one , step′-one) , λ c → tt
```

# 实际内层部分和上的 NF/G 不变量
验收文件；初项、旧区间保持与非空新区间拆分为编译定理；新区间步进尚未实填。
Inv₂ 仅对 YiAZStart.P；step→rows/first 保留未填步进前提，不增加无条件强度。
来源：Buchholz 3.3 的 NF/G 形状；初项复用 YiCFMono.mono≤ⁿ 与 YiAZLocal.S1-low，累计保持复用 YiKVRel.+⊴。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGBInv where
open import OCF.Lean.YiGBStart
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong; cong₂)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiOLMilestone as OM
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWBlock as B
open import OCF.Lean.YiCFMono using (mono≤ⁿ)
open import OCF.Lean.YiGTGen using (app≤ν)
open import OCF.Lean.YiLBInv using (from⊴)
open import OCF.Align.Value using (_≼_; ≼-trans)

P1-form : AZ.P 1 ≡ (proj₁ (AZ.N.Inner.out B.zero) O.+
  proj₁ (AZ.N.Inner.out (AZ.N.Inner.feed B.zero)))
P1-form = trans AZ.P1 (cong₂ O._+_
  (cong (λ d → proj₁ (AZ.N.Inner.out d)) AZ.inner0)
  (cong (λ d → proj₁ (AZ.N.Inner.out d)) AZ.inner1))

Inv₂ : ℕ → Set
Inv₂ q = (a : E.T) → NF a → GB [] a a → a ≤ᵀ param q
  → (h : SI.E.HC (E.ψ [] a ∷ [])) → SI.E.tree h ≼ K.readRW (AZ.P q)

partial-step : ∀ q → K.readRW (AZ.P q) ≼ K.readRW (AZ.P (suc q))
partial-step q = from⊴ (K.+⊴ (AZ.P q) (proj₁ (AZ.G (suc q))))

old-part : ∀ q → (a : E.T) → NF a → GB [] a a → a ≤ᵀ param 0
  → (h : SI.E.HC (E.ψ [] a ∷ [])) → SI.E.tree h ≼ K.readRW (AZ.P q)
old-part zero a na ga le h = ≼-trans (XI.tree-back h)
  (≼-trans (mono≤ⁿ (nf-ψ n[] na ga) (ref-NF 0) (c∷ c[]) (XI.back h) (XI.back (ref-HC 0)) (app≤ν [] [] le))
    (≼-trans (SI.toL-tree (XI.back (ref-HC 0))) (AL.S1-low (SI.conv (XI.back (ref-HC 0))))))
old-part (suc q) a na ga le h = ≼-trans (old-part q a na ga le h) (partial-step q)

inv0 : Inv₂ 0
inv0 = old-part 0

carry : ∀ q → Inv₂ q → (a : E.T) → NF a → GB [] a a → a ≤ᵀ param q
  → (h : SI.E.HC (E.ψ [] a ∷ [])) → SI.E.tree h ≼ K.readRW (AZ.P (suc q))
carry q iv a na ga le h = ≼-trans (iv a na ga le h) (partial-step q)

New₂ : ℕ → Set
New₂ q = (a : E.T) → NF a → GB [] a a → param q E.<ᵀ a → a ≤ᵀ param (suc q)
  → (h : SI.E.HC (E.ψ [] a ∷ [])) → SI.E.tree h ≼ K.readRW (AZ.P (suc q))

step-at : ∀ q → New₂ q → Inv₂ q → Inv₂ (suc q)
step-at q new iv a na ga le h with dec≤ a (param q)
... | inj₁ old = carry q iv a na ga old h
... | inj₂ fresh = new a na ga fresh le h

pointwise : ∀ q → Inv₂ q → (h : SI.E.HC (ref q)) → SI.E.tree h ≼ K.readRW (AZ.P q)
pointwise q iv = iv (param q) (param-NF q) (param-G q) (inj₂ refl)

InvStep : Set
InvStep = ∀ q → Inv₂ q → Inv₂ (suc q)

iterate-inv : InvStep → ∀ q → Inv₂ q
iterate-inv st zero = inv0
iterate-inv st (suc q) = st q (iterate-inv st q)

step→rows : InvStep → OM.Rows2
step→rows st n = n , subst (λ t → K.M⁰ t (AZ.P n)) (sym (ref-eq n))
  (CS.sem→M⁰ (XI.back (ref-HC n)) (AZ.P n)
    (≼-trans (SI.toL-tree (XI.back (ref-HC n)))
      (pointwise n (iterate-inv st n) (SI.conv (XI.back (ref-HC n))))))

step→first : InvStep → OM.FirstRow
step→first st = step→rows st 1

new0→first : New₂ 0 → OM.FirstRow
new0→first new = 1 , CS.sem→M⁰ (XI.back (ref-HC 1)) (AZ.P 1)
  (≼-trans (SI.toL-tree (XI.back (ref-HC 1)))
    (pointwise 1 (step-at 0 new inv0) (SI.conv (XI.back (ref-HC 1)))))

step→milestone : InvStep → (h : SI.E.HC (AL.S 2))
  → SI.E.tree h ≼ K.readRW (proj₁ AZ.D.output)
step→milestone st = OM.assemble2 (step→rows st)
```

# StepU 在最小层号上的反例
验收文件；编译否定：`StepU (fn 1)` 不成立，规范底 `B₀` 下的全部前提均实填。
反例甚至满足 g 的整条分支律；缺的是底与非空前缀的联系，不能归因于单支前提。
这是否定充分接口的全域量化，不否定规范塔的强度，不使用全域 `Leaf`。
入口：`no-step`、`no-steps`、`whole-branch`、`small-step`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUNeg where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (rb-no)
open import OCF.Lean.YiLKIface using (feed; OK; StepU)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiKVRel using (⊴r)
open import OCF.Lean.YiSUBound using (fin-bound; fz; no-ω²; ωᶜ)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

ℓ : L
ℓ = fn 1

o : Ok ℓ
o = tt , λ _ → tt

p : Pos ℓ
p = inj₂ (tt , inj₁ tt)

a : E.T
a = E.Ωt (E.natT 1)

t : E.T
t = E.natT 1

ν : E.T
ν = []

g : Br ℓ p → Tr ℓ
g c with zl c
... | inj₁ eq = zero
... | inj₂ d = up zero tt c d

c : Br ℓ p
c = suc zero

okB : OK (B₀ ℓ)
okB _ _ = ⊴r

nu : GR.Nu ℓ p ν
nu = GR.c0 refl

cof-a : E.cof a ≡ E.cΩ ν
cof-a = refl

low : GR.Low ℓ p (E.γT (t ++ a) ν 0) c
low = H.m1 refl H.mz

zero-ref : ∀ {η} → H.M⁰ η zero → η ≡ []
zero-ref m with fin-bound m fz
... | inj₂ refl = refl

whole-branch : ∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c)
whole-branch η c m with zl c
... | inj₁ refl = subst (λ s → GR.R ℓ s zero) (sym (zero-ref m)) H.mz
... | inj₂ d = H.mU H.mz m

branch : GR.R ℓ (E.fsT a (E.γT (t ++ a) ν 0)) (g c)
branch = whole-branch _ c low

gamma1 : E.γT (t ++ a) ν 1 ≡ (E.ψ [] (E.natT 2) ∷ [])
gamma1 = refl

out : feed ℓ o (rb-no ℓ) (B₀ ℓ) p g c ≡ ωᶜ
out = refl

small-step : GR.Low ℓ p (E.γT a ν 1) (feed ℓ o (rb-no ℓ) (B₀ ℓ) p g c)
small-step = H.G⁰.m-next (Ωt zero) refl (λ n → refl) (H.m1 refl H.mz)

no-step : StepU ℓ → ⊥
no-step st = no-ω² (st o (rb-no ℓ) (B₀ ℓ) okB t a p ν nu cof-a g 0 c low branch)

no-steps : (∀ ℓ → StepU ℓ) → ⊥
no-steps st = no-step (st ℓ)
```

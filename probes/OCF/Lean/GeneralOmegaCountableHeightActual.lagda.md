# 原完成生成域的遗传前沿步进

Lead只记录原树每个极限的相邻Leading路径，不要求任意两输入可比。
原leg的全部输出都满足它；其原合法性步进与下方构造逐点相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableHeightActual where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg; Σ₀)
open import OCF.Lean.GeneralOmegaCountableHeightIf
open import OCF.Lean.GeneralOmegaCountableHeightLeading
open import OCF.Lean.GeneralOmegaCountableObserveClosed using (Γ; rawΓ; stage)

Lead : Cd → Set
Lead hz = ⊤
Lead (hs a) = Lead a
Lead (hl f) = (∀ n → Leading (f n) (f (suc n))) × (∀ n → Lead (f n))
Lead (hΩ () f)
add-leading : ∀ a {b c} → Leading b c → Leading (a ⊞ b) (a ⊞ c)
add-leading a here = here
add-leading a (next p) = next (add-leading a p)
add-leading a (first p) = first (add-leading a p)
lead-add : ∀ {a b} → Lead a → Lead b → Lead (a ⊞ b)
lead-add {b = hz} la lb = la
lead-add {b = hs b} la lb = lead-add la lb
lead-add {a} {hl f} la (step , branches) = (λ n → add-leading a (step n)) , (λ n → lead-add la (branches n))
lead-sum : ∀ (f : ℕ → Cd) → (∀ n → Lead (f n)) → ∀ n → Lead (Σ₀ f n)
lead-sum f l zero = l zero
lead-sum f l (suc n) = lead-add (lead-sum f l n) (l (suc n))
leg-all : ∀ a → Lead (leg a)
leg-all hz = tt
leg-all (hs a) = leg-all a
leg-all (hl f) = (λ n → prefix-leading (Σ₀ (λ k → leg (f k)) n) (leg (f (suc n)))) ,
  lead-sum (λ n → leg (f n)) (λ n → leg-all (f n))
leg-all (hΩ () f)
prefix-path : ∀ a b → path (prefix-leading a b) ≡ ⊞-fst a b
prefix-path a hz = refl
prefix-path a (hs b) = cong hsuc (prefix-path a b)
prefix-path a (hl f) = cong (hlim zero) (prefix-path a (f zero))
prefix-path a (hΩ () f)
actual-leg-step : ∀ (f : ℕ → Cd) n →
  path (proj₁ (leg-all (hl f)) n) ≡ proj₁ (Lg-leg (hl f)) n
actual-leg-step f n = prefix-path _ _
Γ-leading-steps : ∀ c → Lead (Γ c)
Γ-leading-steps c = leg-all (rawΓ c)
stage-leading : ∀ n → Lead (stage n)
stage-leading zero = tt
stage-leading (suc n) = Γ-leading-steps (stage n)
height-leading : ∀ n → Lead (leg (stage n))
height-leading n = leg-all (stage n)
```

这些证书是原闭项既有结构的定理，不加入它的定义。Lead不蕴含
所有位置为Leading，也不把第n累计右分量变为左前缀；一般高度
吸收字段仍未完成。

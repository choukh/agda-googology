# 原动态跨底运行器在相干证书域上的保持

先给实际repeat和diagonal的Good闭包；后者的所有反馈坐标均递归携带Good。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeReadyFold where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.BoundedFoldRun using (chain; diagonal)
open import OCF.Align.BoundedDescentValueBridge
open import OCF.Align.BoundedNativeReadyGood
open import OCF.Align.BoundedNativeZeroWorld using (seed)

partial-good : ∀ t f → (∀ n → Good t (f n)) → ∀ n → Good t (Ops.partial (Native t) f n)
partial-good t f lf zero = lf zero
partial-good t f lf (suc n) = add-good t _ _ (partial-good t f lf n) (lf (suc n))
repeat-good : ∀ t x → Good t x → Good t (Ops.repeat (Native t) x)
repeat-good t x lx = (λ lv n → ⊞-fst _ _) , partial-good t (λ _ → x) (λ _ → lx)
chain-good : ∀ i (f : HB (Native i) → HB (Native i)) →
  (∀ e → Good i e → Good i (f e)) → ∀ n → Good i (chain f n)
chain-good i f lf zero = tt
chain-good i f lf (suc n) = add-good i _ _ (chain-good i f lf n) (lf _ (chain-good i f lf n))
diagonal-good : ∀ i t (f : HB (Native i) → HB (Native i)) (g : HB (Native i) → HB (Native t)) →
  (∀ e → Good i e → Good i (f e)) → (∀ e → Good i e → Good t (g e)) → Good t (diagonal f g)
diagonal-good i t f g lf lg = (λ lv n → ⊞-fst _ _) ,
  partial-good t _ (λ n → lg _ (chain-good i f lf n))
```

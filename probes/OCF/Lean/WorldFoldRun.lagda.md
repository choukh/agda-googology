# 可数折叠的运行与合法性

`CountableFold` 的无前提实例。递归只下降输入树，回灌选出的分支仍是
原节点的直接子树；由 Agda 验证终止。输出合法不要求原始输入合法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.WorldFoldRun where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl; LgB; ⊞-fst; Lg-⊞)
open import OCF.Lean.NegFab6Idx using (W; wz; ws; wl; wn)
open import OCF.Lean.WorldFoldIf

run : ∀ {B} → W B → Cd
run wz = hz
run (ws a) = hs (run a)
run (wl f) = series (λ n → run (f n))
run {B} (wn g) = feedback B (λ e p → run (g e p))

partial-legal : ∀ f → (∀ n → LgB (f n)) → ∀ n → LgB (partial f n)
partial-legal f l zero = l zero
partial-legal f l (suc n) = Lg-⊞ (partial f n) (f (suc n)) (partial-legal f l n) (l (suc n))

series-legal : ∀ f → (∀ n → LgB (f n)) → LgB (series f)
series-legal f l = (λ n → ⊞-fst (partial f n) (f (suc n))) , partial-legal f l

run-legal : ∀ {B} (a : W B) → LgB (run a)
run-legal wz = tt
run-legal (ws a) = run-legal a
run-legal (wl f) = series-legal (λ n → run (f n)) (λ n → run-legal (f n))
run-legal {B} (wn g) = series-legal _ (λ n →
  let s = orbit B (λ e p → run (g e p)) n in run-legal (g (proj₁ s) (proj₂ s)))

instance-fold : CountableFold
instance-fold = record
  { fold = run ; legal = run-legal
  ; zero-law = refl ; suc-law = λ a → refl
  ; lim-law = λ f → refl ; node-law = λ g → refl }
```

# B7 候选与现主线块的兼容
> 原型。旧层号与孩子坐标保持不动；每层将旧树及其第一位置嵌入新的一层块。
> 编译定理：所有旧树均可嵌入，且该候选每层的新关系良基；尚未把新树读回成新层号。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFWCompat where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as O
open import OCF.Lean.YiFWBlock
open import OCF.Lean.YiFWWf

mutual
  unBr : (ℓ : O.L) (p : O.Pos ℓ) → O.Br ℓ p → O.Tr (O.at ℓ p)
  unBr (O.nd s h) (inj₂ (c , t)) = unBr⁼ (h c) t
  unBr (O.nd (O.sΩ k) h) (inj₁ t) = unBr⁼ k t

  unBr⁼ : (a : O.L) (p : O.Pos⁼ a) → O.Br⁼ a p → O.Tr (proj₁ (O.sl⁼ a p))
  unBr⁼ a (inj₁ _) x = x
  unBr⁼ a (inj₂ p) x = unBr a p x

Sig : O.L → Sg
Sig ℓ = sg (O.Pos ℓ) (O.Br ℓ) (O.CH ℓ) (O.ChT ℓ)
  (λ p → O.fromBr ℓ p O.zero) (O.chZ ℓ) (O.RCh ℓ)
  O.L (O.at ℓ) (λ p a b → O.Lt (O.Sig (O.at ℓ p)) (unBr ℓ p a) (unBr ℓ p b))

mutual
  embed : (ℓ : O.L) → O.Tr ℓ → T (Sig ℓ)
  embed ℓ O.zero = zero
  embed ℓ (O.suc x) = suc (embed ℓ x)
  embed ℓ (O.lim f a) = lim (λ n → embed ℓ (f n)) (λ n → embed-mono ℓ (a n))
  embed ℓ (O.Ω p g) = Ω p (λ z → embed ℓ (g z))
  embed ℓ (O.up x c y e) = up (embed ℓ x) c y e

  embed-mono : (ℓ : O.L) {x y : O.Tr ℓ} → O.Lt (O.Sig ℓ) x y → Lt (Sig ℓ) (embed ℓ x) (embed ℓ y)
  embed-mono ℓ O.◃s = ◃s
  embed-mono ℓ (O.◃l n) = ◃l n
  embed-mono ℓ O.◃w = ◃w
  embed-mono ℓ (O.◃u x c y e) = ◃u (embed ℓ x) c y e
  embed-mono ℓ (O.◃c x c d) = ◃c (embed ℓ x) c d
  embed-mono ℓ (O.◃t d e) = ◃t (embed-mono ℓ d) (embed-mono ℓ e)

pullAcc : {A B : Set} {R : A → A → Set} {S : B → B → Set}
  (f : A → B) (mono : ∀ {x y} → R x y → S (f x) (f y))
  {x : A} → Acc S (f x) → Acc R x
pullAcc f mono (acc ax) = acc λ d → pullAcc f mono (ax (mono d))

mutual
  old-wf : (ℓ : O.L) (x : O.Tr ℓ) → Acc (O.Lt (O.Sig ℓ)) x
  old-wf ℓ x = pullAcc (embed ℓ) (embed-mono ℓ) (wf (child-wf ℓ) (embed ℓ x))

  child-wf : (ℓ : O.L) (c : O.CH ℓ) (y : O.ChT ℓ c) → Acc (O.RCh ℓ c) y
  child-wf (O.nd s h) c y = old-wf (h c) y

new-wf : (ℓ : O.L) (x : T (Sig ℓ)) → Acc (Lt (Sig ℓ)) x
new-wf ℓ = wf (child-wf ℓ)

new-irrefl : (ℓ : O.L) {x : T (Sig ℓ)} → Lt (Sig ℓ) x x → ⊥
new-irrefl ℓ = irrefl (child-wf ℓ)

-- 不同的字面槽位，同一个下层，等价证据不需要判等算法。
flat : O.L
flat = O.nd O.sL (λ _ → O.zero)

p₀ p₁ : O.Pos flat
p₀ = inj₂ (0 , inj₁ tt)
p₁ = inj₂ (1 , inj₁ tt)

slots-differ : p₀ ≡ p₁ → ⊥
slots-differ ()

same-branches : E (Sig flat) p₀ p₁
same-branches = refl , record
  { cv = λ x → x ; back = λ x → x
  ; cv-back = λ _ → refl ; back-cv = λ _ → refl
  ; first = refl ; forward = λ d → d ; backward = λ d → d }

cross-slot : Lt (Sig flat) (Ω p₀ (λ _ → zero)) (Ω p₁ (λ _ → suc zero))
cross-slot = ◃σ same-branches (λ _ → ◃s)

cross-nat : ℕ → T (Sig flat)
cross-nat zero = zero
cross-nat (suc n) = suc (cross-nat n)

cross-slotAt : ℕ → O.Pos flat
cross-slotAt zero = p₀
cross-slotAt (suc n) = p₁

cross-eqslot : ∀ n → E (Sig flat) (cross-slotAt n) (cross-slotAt (suc n))
cross-eqslot zero = same-branches
cross-eqslot (suc n) = reflE (Sig flat) p₁

cross-node : ℕ → T (Sig flat)
cross-node n = Ω (cross-slotAt n) (λ _ → cross-nat n)

cross-step : ∀ n → Lt (Sig flat) (cross-node n) (cross-node (suc n))
cross-step n = ◃σ (cross-eqslot n) (λ _ → ◃s)

cross-limit : T (Sig flat)
cross-limit = lim cross-node cross-step
```

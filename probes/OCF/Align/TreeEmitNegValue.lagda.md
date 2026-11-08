# 同一裸标记反例的值否定

两端使用真实旧解释与下降解释，沿自然数基本列给出完整 Goodᴺ。
本篇加强结构反例为值不等，不涉及 Ω̇ 实际生成域。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeEmitNegValue where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import Relation.Nullary using (¬_)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ; Ordˢ; Ord₊ˢ; _+ˢ_)
open import OCF.Free.Force
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.ValueJudgeBase
import OCF.Align.TreeEmitNegRaw as N
open N.T

nat : ℕ → Ordˢ zero
nat zero = Ord₊ˢ.zero
nat (suc n) = Ord₊ˢ.suc (nat n)

one-add : ∀ n → nat 1 +ˢ nat n ≡ nat (suc n)
one-add zero = refl
one-add (suc n) = cong Ord₊ˢ.suc (one-add n)

terms : ℕ → Ordˢ zero
terms = iter (nat 1 +ˢ_) Ord₊ˢ.zero

terms-nat : ∀ n → terms n ≡ nat n
terms-nat zero = refl
terms-nat (suc n) rewrite terms-nat n = one-add n

good-nat : ∀ n → Goodᴺ (toZ (nat n))
good-nat zero = gz
good-nat (suc n) = gs (good-nat n)

num : ℕ → Ordᶜ zero
num zero = zero
num (suc n) = suc (num n)

force-nat : ∀ n → forceᴺ _ (good-nat n) ≡ num n
force-nat zero = refl
force-nat (suc n) = cong suc (force-nat n)

good-term : ∀ n → Goodᴺ (toZ (terms n))
good-term n rewrite terms-nat n = good-nat n

force-term : ∀ n → forceᴺ _ (good-term n) ≡ num n
force-term n rewrite terms-nat n = force-nat n

num-step : ∀ n → num n ⊑⁰ num (suc n)
num-step n p = ≺s p

old : Z
old = toZ (ψ̄ᵠ N.ok N.e₀ N.x N.ev zero)
down : Z
down = toZ (ψ̄ᵠ N.ok N.e₁ (ι↓ {α = zero} _ N.x) N.ev zero)

old-good : Goodᴺ old
old-good = gl good-term step where
  step : ∀ n → forceᴺ _ (good-term n) ⊑⁰ forceᴺ _ (good-term (suc n))
  step n rewrite force-term n | force-term (suc n) = num-step n

down-good : Goodᴺ down
down-good = gs gz

two-below : num 2 ≼ forceᴺ old old-good
two-below = ≼l 2 (s≼s (s≼s z≼))

no-value-upper : ¬ (forceᴺ old old-good ≼ forceᴺ down down-good)
no-value-upper p with ≼-trans two-below p
... | s≼s ()
```

# 累计解释的全裸程序比较不能成立

固定共享算法。第一例是合法常一极限，第二例是旧轨道恒一、
但观察分支在层号一和二处不同的真实闭包程序。所有旧 Goodᴺ 实填。
只否定全裸 Z 合同，不否定原 Ω̇ 生成域中的下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RadicalNegTotal where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalOrbitCompareIf
import OCF.Free.TotalOrbitBuild as A

one : Z
one = Z.suc Z.zero

run-zero : A.run Z.zero ≡ zero
run-zero = refl
run-one : A.run one ≡ suc zero
run-one = refl

flat : Z
flat = Z.lim (λ _ → one)
flat-good : Goodᴺ flat
flat-good = gl (λ _ → gs gz) (λ _ → ≅→⊑ (s≅ z≅))

two-flat : suc (suc (zero {zero})) ≼ A.tree flat
two-flat = ≼l 1 (s≼s (s≼s z≼))
flat-upper : forceᴺ flat flat-good ≼ suc (zero {zero})
flat-upper = l≼ (λ _ → s≼s z≼)

no-same-value : ¬ SameValue
no-same-value law with ≼-trans two-flat
  (≼-trans (proj₂ (SameValue.same law flat flat-good)) flat-upper)
... | s≼s ()

observeBranch : (η : Ordᴵ) → suc zero ⊑ᴵ η → Z
observeBranch zero d = Z.zero
observeBranch (suc zero) d = one
observeBranch (suc (suc a)) d = Z.zero
observeBranch (suc (lim f s)) d = Z.zero
observeBranch (lim f s) d = Z.zero

bad : Z
bad = Z.ĉᴸ (suc zero) one (λ _ _ → one) Z.zero observeBranch

bad-good : Goodᴺ bad
bad-good = gc (λ _ → suc zero) (λ _ → hs hz)
  (λ _ → s⊑ z≅ zero)
  (gs gz) (s≅ z≅) (λ _ → gs gz) (λ _ → s≅ z≅)
  gz (λ _ → gs gz) (λ ()) (λ _ → ≅→⊑ (s≅ z≅))

one-old : suc (zero {zero}) ≼ forceᴺ bad bad-good
one-old = ≼l 1 (s≼s z≼)

item : Ordᴵ → ℕ → Ordᴵ
item zero n = zero
item (suc a) n = zero
item (lim f st) n = f n

new-item-zero : ∀ n → item (A.run bad) n ≡ zero
new-item-zero zero = refl
new-item-zero (suc zero) = refl
new-item-zero (suc (suc n)) rewrite new-item-zero (suc n) = refl

new-upper : A.tree bad ≼ zero {zero}
new-upper = l≼ (λ n → subst (λ a → A.read a ≼ zero {zero})
  (Relation.Binary.PropositionalEquality.sym (new-item-zero n)) z≼)

no-old-lower : ¬ OldLower
no-old-lower law with ≼-trans one-old
  (≼-trans (OldLower.lower law bad bad-good) new-upper)
... | ()
```

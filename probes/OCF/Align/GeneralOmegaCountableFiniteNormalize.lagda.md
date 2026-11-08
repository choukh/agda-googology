# rawΓ数值输入的真实证据规范化

只规范原num n共同高度中的证据，不给一般Cd路径无关性。
leg-num处理高度本身，合法证据按有限高度递归，路径使用已证的
固定数值右端唯一性；最终观察的源地板仍是原累计floor。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableFiniteNormalize where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
import OCF.Lean.GeneralOmegaCountableObserveIf as C
import OCF.Lean.GeneralOmegaCountableObserveRun as R
import OCF.Lean.GeneralOmegaCountableObserveClosed as Closed
open import OCF.Lean.GeneralOmegaCountableObserveClass using (num; num-legal)
open import OCF.Lean.GeneralOmegaCountableNumber using (leg-num; path-unique)

legal-unique : ∀ n (p q : LgB (num n)) → p ≡ q
legal-unique zero tt tt = refl
legal-unique (suc n) p q = legal-unique n p q

normalize : ∀ n {B} → B ≡ num n → (lB : LgB B) (pt : hz ⊲ B) →
  R.observe B lB hz pt (C.floor B) ≡
  R.observe (num n) (num-legal n) hz (z⊲ᴮ (num n)) (C.floor (num n))
normalize n refl lB pt rewrite legal-unique n lB (num-legal n) |
  path-unique n pt (z⊲ᴮ (num n)) = refl

raw-normal : ∀ n → Closed.rawΓ (num n) ≡
  R.observe (num n) (num-legal n) hz (z⊲ᴮ (num n)) (C.floor (num n))
raw-normal n = normalize n (leg-num n) (Lg-leg (num n)) (z⊲ᴮ (leg (num n)))
```

raw-normal全n是观察整个输入的命题等式；无需假设observer对高层
Same单调。它不负责原两分类器的配对，更不是Γ一般值单调性。

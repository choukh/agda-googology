# 合法正则输入的完成不保持旧前驱包含

验收专用。实际输入为ω+1，完成后为legω+1。否定的仅是旧⊑⁰
提升字段；输入的普通值膨胀仍成立，不能据此否定ψΩ值比较或γ₁专用桥。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedValueNegCompletion where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.CountableCompletionUpperOmega using (num; ω; legal-ω; leg-ω≤ω)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaCountableRegularIf using (Reg)
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.NegFold1If using (¬s≤ᵛ)
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.LambdaOrderBridge as Order

input : Cd
input = hs ω
legal-input : LgB input
legal-input = legal-ω
regular-num : ∀ n → Reg (num n)
regular-num zero = tt
regular-num (suc n) = regular-num n
regular-input : Reg input
regular-input = (λ n → ≤-refl _) , regular-num
hs-num : ∀ n → L.HS (B.read (num n))
hs-num zero = L.hz
hs-num (suc n) = L.hs (hs-num n)
hs-input : L.HS (B.read input)
hs-input = L.hs (L.hl hs-num (λ n p → L.≺s p))

-- 原ω第2分量为2，legω第2部分和为3。
two-not-three : B.read (num 2) L.≅ B.read (num 3) → ⊥
two-not-three (L.s≅ (L.s≅ ()))
not-same-omega : B.read ω L.≅ B.read (leg ω) → ⊥
not-same-omega (L.l≅ p) = two-not-three (p 2)
not-below-completed : B.read ω L.≺ B.read (leg ω) → ⊥
not-below-completed p = ¬s≤ᵛ ω (≤-trans
  (B.read-reflect (Order.backward (V.≺→s≼ p))) leg-ω≤ω)
not-predecessor : B.read ω L.≺ B.read (leg input) → ⊥
not-predecessor (L.≺z e) = not-same-omega e
not-predecessor (L.≺s p) = not-below-completed p
no-input-inclusion : B.read input L.⊑⁰ B.read (leg input) → ⊥
no-input-inclusion p = not-predecessor (p (L.≺z (L.≅-refl⁰ (B.read ω))))

no-regular-completion-rule :
  (∀ a → LgB a → Reg a → L.HS (B.read a) → B.read a L.⊑⁰ B.read (leg a)) → ⊥
no-regular-completion-rule rule = no-input-inclusion
  (rule input legal-input regular-input hs-input)

value-inflation-survives : input ≤ᵛ leg input
value-inflation-survives = inflation input
legal-completed : LgB (leg input)
legal-completed = Lg-leg input
```

反例带原LgB、正则Reg及旧HS三项真实证书；它不依靠非法高度。
未声称完成后无字面公共界，也未声称当前实际γ₁违反专用包含关系。
更高层的有向值比较需要另证，不能从本否定得到其真假。

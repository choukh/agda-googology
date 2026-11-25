# 换基折叠沿首孩子下降
验收文件；对任意读回证据沿字面首孩子路径下降，不涉及记号。
来源：YiMTKeel.step¹ᶻ/descᶻ 原证明，折叠换成 YiBSFold，读回证据作为变量递归。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBTDesc where
open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiBSBase using (Rb)
import OCF.Lean.YiBSFold as F
import OCF.Lean.YiBTLocal as C
open import OCF.Lean.YiKSDesc using (_⊑¹_; r¹; n¹; ok¹; ◃≼ᴿ; plusᴿ)
import OCF.Lean.YiBRValue as BR
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
open import OCF.Align.Value using (_≼_; ≼l; ≼-trans; ≼-refl; z≼; s≼s; l≼)
F₀ : (ℓ : L) → Ok ℓ → Rb ℓ → Tr zero
F₀ ℓ o r = proj₁ (F.ψ₀ ℓ o r (proj₁ (Ωt ℓ)))
step¹ : (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h))
  → BR.readRW (F₀ (h (c₀ s)) (proj₂ o (c₀ s)) (proj₂ r (c₀ s))) ≼ BR.readRW (F₀ (nd s h) o r)
step¹ sS h o r = ≼l 1 (plusᴿ _ _ (◃≼ᴿ (◃t (◃l zero) (◃l zero))))
step¹ sL h o r = ◃≼ᴿ (◃l zero)
step¹ (sΩ k) h o r = ◃≼ᴿ (F.mono (nd (sΩ k) h) o r (B₀ (nd (sΩ k) h)) zero
  (z≤ (nd (sΩ k) h)) (Ωt zero) (◃w {p = inj₁ (inj₁ tt)}))
desc : ∀ {j ℓ} (p : j ⊑¹ ℓ) (o : Ok ℓ) (r : Rb ℓ)
  → BR.readRW (F₀ j (ok¹ p o) (C.rb¹ p r)) ≼ BR.readRW (F₀ ℓ o r)
desc {j} r¹ o r = ≼-refl (BR.readRW (F₀ j o r))
desc (n¹ {s} {h} p) o r = ≼-trans (desc p (proj₂ o (c₀ s)) (proj₂ r (c₀ s))) (step¹ s h o r)
read-back : (x : Tr zero) → K.readRW x ≼ BR.readRW x
read-back zero = z≼
read-back (suc x) = s≼s (read-back x)
read-back (lim f a) = l≼ (λ n → ≼l n (read-back (f n)))
read-desc : ∀ {j ℓ} (p : j ⊑¹ ℓ) (o : Ok ℓ) (r : Rb ℓ)
  → K.readRW (F₀ j (ok¹ p o) (C.rb¹ p r)) ≼ K.readRW (F₀ ℓ o r)
read-desc {j} {ℓ} p o r = ≼-trans (read-back (F₀ j (ok¹ p o) (C.rb¹ p r)))
  (≼-trans (desc p o r) (CS.rr≼ (F₀ ℓ o r)))
```

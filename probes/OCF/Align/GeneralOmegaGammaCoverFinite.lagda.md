# γ₂首个完整回调的有限下标共尾族

验收专用。这一回调不是ψ₀(Ω₁)，而是全部ψ₀(Ω_n)的极限。
下面保留原γ₂的HS证书，证明整个自然数族的双向值界；没有把原
callback替换成手选低项，也不声称候选已覆盖这个极限。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaGammaCoverFinite where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; subst)
open import OCF.Lean.CRwBase using (Cd; hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Align.Level as L
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.GeneralOmegaGammaActual as A

nat-tree : ℕ → L.Ordᶜ L.zero
nat-tree zero = L.zero
nat-tree (suc n) = L.suc (nat-tree n)
nat-level : ℕ → L.Ordᴵ
nat-level zero = L.zero
nat-level (suc n) = L.suc (nat-level n)

count : ℕ → L.Ordᶜ L.zero
count = iter (L.suc L.zero L.+_) L.zero
one-plus : ∀ n → L.suc L.zero L.+ nat-tree n ≡ nat-tree (suc n)
one-plus zero = refl
one-plus (suc n) = cong L.suc (one-plus n)
count-shape : ∀ n → count n ≡ nat-tree n
count-shape zero = refl
count-shape (suc n) = trans (cong (L.suc L.zero L.+_) (count-shape n)) (one-plus n)
nat-toLevel : ∀ n (h : L.HS (nat-tree n)) → L.toLevel (nat-tree n) h ≡ nat-level n
nat-toLevel zero h = refl
nat-toLevel (suc n) h = cong L.suc (nat-toLevel n (L.hs⁻ h))
count-toLevel : ∀ n (h : L.HS (count n)) → L.toLevel (count n) h ≡ nat-level n
count-toLevel n h rewrite count-shape n = nat-toLevel n h

finite : ℕ → Cd
finite n = B.forget (L.ψ⁰ (L.Ω (nat-level n)))
original : ℕ → Cd
original n = B.forget (L.ψ⁰ (L.Ω (L.toLevel (count n) (L.hl₁ (A.component-HS zero) n))))
original-finite : ∀ n → original n ≡ finite n
original-finite n = cong (λ j → B.forget (L.ψ⁰ (L.Ω j)))
  (count-toLevel n (L.hl₁ (A.component-HS zero) n))
first-callback-shape : A.reference-branch zero ≡ hl original
first-callback-shape = refl

first≤finite : A.reference-branch zero ≤ᵛ hl finite
first≤finite = l≤ (λ n → ≤l n (subst (λ z → original n ≤ᵛ z) (original-finite n) (≤-refl _)))
finite≤first : hl finite ≤ᵛ A.reference-branch zero
finite≤first = l≤ (λ n → ≤l n (subst (λ z → z ≤ᵛ original n) (original-finite n) (≤-refl _)))
```

这是原第一回调的完整值校准：有限族全部保留，且原累计候选分量
没有改变。要把它送入候选，仍需同时覆盖所有finite n；只证n=1
不能完成本回调。也未给出该回调对候选的上界或否定。

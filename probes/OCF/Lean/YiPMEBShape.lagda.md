# 按表参数化: EBShape

参数化（工程），数学内容与 `YiVTEBShape` 的保持及下降证明相同；验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMEBShape where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Unit using (tt)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Product using (_,_; proj₁; proj₂; _×_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)

  open import OCF.Lean.YiLegBlock renaming (L to LF)
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  open import OCF.Lean.YiLSRead
  import OCF.Lean.YiPMLSFold
  open OCF.Lean.YiPMLSFold.F tb using (OKB; ok-B₀; ok-dL)
  import OCF.Lean.YiPMLSTw1
  open OCF.Lean.YiPMLSTw1.F tb using (h₁)

  import OCF.Align.Level as L
  open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼)

  pre : ℕ → Tr Λ
  pre zero    = zero
  pre (suc n) = cumΩ tw n

  dB : (n : ℕ) → Base (tw n)
  dB n = dL tw Ev-Λ Rt-Λ (B₀ Λ) n (pre n)

  Fn : (n : ℕ) → Base (tw n) → Tr zero
  Fn n B = ψ⊥ (tw n) (Ev-tw n) (Rt-tw n) B (Ωt (tw n))

  br : ℕ → Tr zero
  br n = Fn n (dB n)

  EBO-lim : EBOᶜ ≡ lim (λ n → ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n))
                       (λ n → mono⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (◃u (cumΩ tw n) (suc n) (Ωt (tw (suc n))) (Ωt-nz (tw (suc n)))))
  EBO-lim = refl

  branch-eq : (n : ℕ) → ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n) ≡ br n
  branch-eq zero    = refl
  branch-eq (suc n) = refl

  br≼ : (n : ℕ) → read (br n) ≼ read EBOᶜ
  br≼ zero    = ≼l zero (≼-refl _)
  br≼ (suc n) = ≼l (suc n) (≼-refl _)

  sup≼ : (Y : T₀) → ((n : ℕ) → read (br n) ≼ Y) → read EBOᶜ ≼ Y
  sup≼ Y h = l≼ go
    where
    go : (n : ℕ) → read (ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n)) ≼ Y
    go zero    = h zero
    go (suc n) = h (suc n)

  EBO≅sup : read EBOᶜ L.≅ L.lim (λ n → read (br n))
  EBO≅sup = L.l≅ go
    where
    go : (n : ℕ) → read (ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n)) L.≅ read (br n)
    go zero    = L.≅-refl⁰ _
    go (suc n) = L.≅-refl⁰ _

  ok-dB : (n : ℕ) → OKB (tw n) (dB n)
  ok-dB n = ok-dL tw Ev-Λ Rt-Λ (B₀ Λ) (ok-B₀ Λ) n (pre n)

  b⊥-dB : (n : ℕ) → b⊥ (dB (suc n)) ≡ br n
  b⊥-dB zero    = refl
  b⊥-dB (suc n) = refl

  transfer : (X : T₀) (n : ℕ) → ((B : Base (tw n)) → OKB (tw n) B → X ≼ read (Fn n B)) → X ≼ read EBOᶜ
  transfer X n h = ≼-trans (h (dB n) (ok-dB n)) (br≼ n)

  transferP : (X : T₀) (n : ℕ) (P : Base (tw n) → Set) → P (dB n)
    → ((B : Base (tw n)) → OKB (tw n) B → P B → X ≼ read (Fn n B)) → X ≼ read EBOᶜ
  transferP X n P pd h = ≼-trans (h (dB n) (ok-dB n) pd) (br≼ n)

  start-dB2 : bs (dB 2) (tw 1) (ink self)
            ≡ Ω (inj₁ (inj₁ tt)) (λ c → Up (h₁ c) (down stop c) (next (Ωt (tw 1)) (Ωt-nz (tw 1))) _ (Ωt (h₁ c)))
  start-dB2 = refl

  start-B₀2 : bs (B₀ (tw 2)) (tw 1) (ink self) ≡ Ω (inj₁ (inj₁ tt)) (λ c → up zero c (Ωt (h₁ c)) (Ωt-nz (h₁ c)))
  start-B₀2 = refl
```

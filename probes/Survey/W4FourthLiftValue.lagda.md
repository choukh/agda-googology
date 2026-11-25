# 第四层新下界在 H 不动点列中的位置

第四层，无条件。D 是 H 的首个正不动点。连续枚举 H 的正不动点 h，旧界 B(D) 在 h(ω)，四级运行中取得的新界在 h(ω²)。枚举以零编号。
 
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FourthLiftValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; s≼s; l≼; ≼l; ≅→≼)
open import WVOne using (T₀; 𝟏)
open import W4Block using (iter)
import B18Product as Mul
import B24ROrbit as O
import B24RKernel as H
import Survey.W4PTOSeededQuery as N
import Survey.W4ThreeReturn as R
import Survey.W4FourthLift as V

iteration : ∀ n → O.orbit n ≡ N.orbit L.zero n
iteration zero = refl
iteration (suc n) = cong H.H (iteration n)

start : O.D ≈ᵛ N.next L.zero
start = ≼-trans {b = L.lim (λ n → O.orbit (suc n))} (≅→≼ O.shape)
          (l≼ λ n → ≼l n (subst (O.orbit (suc n) ≼_) (iteration (suc n)) (≼-refl _))) ,
        ≼-trans {b = L.lim (λ n → O.orbit (suc n))}
          (l≼ λ n → ≼l n (subst (_≼ O.orbit (suc n)) (iteration (suc n)) (≼-refl _))) (≅→≼ (L.≅-sym O.shape))

h : T₀ → T₀
h L.zero = N.next L.zero
h (L.suc a) = N.next (h a)
h (L.lim f) = L.lim (λ j → h (f j))

mono : ∀ {a b} → a ≼ b → N.next a ≼ N.next b
mono {a} {b} p = N.least a (N.next b) (≼-trans {b = L.suc b} (s≼s p) (N.above b)) (proj₁ (N.fixed b))

walk : ∀ a b → a ≼ b → ∀ n → iter N.next a n ≼ iter N.next b n
walk a b p zero = p
walk a b p (suc n) = mono {iter N.next a n} {iter N.next b n} (walk a b p n)

shift : ∀ x n → iter N.next (N.next x) n ≡ iter N.next x (suc n)
shift x zero = refl
shift x (suc n) = cong N.next (shift x n)

series-mono : ∀ {a b} → a ≼ b → R.series a ≼ R.series b
series-mono {a} {b} p = l≼ (λ n → ≼l n (walk a b p (suc n)))

skip : ∀ x → R.series (L.suc x) ≼ R.series x
skip x = l≼ λ n → ≼l (suc n) (subst (iter N.next (L.suc x) (suc n) ≼_) (shift x (suc n))
  (walk (L.suc x) (N.next x) (N.above x) (suc n)))

finite : ∀ a n → h (a L.+ L.natᶜ n) ≡ iter N.next (h a) n
finite a zero = refl
finite a (suc n) = cong N.next (finite a n)

block : ∀ a → h (a L.+ L.ωᶜ) ≈ᵛ R.series (h a)
block a = l≼ (λ n → ≼l n (subst (_≼ iter N.next (h a) (suc n)) (sym (finite a n))
  (≼-trans (≼-suc (≼-refl _)) (N.above (iter N.next (h a) n))))) ,
  l≼ (λ n → ≼l (suc n) (subst (iter N.next (h a) (suc n) ≼_) (sym (finite a (suc n))) (≼-refl _)))

index = λ n → L.ωᶜ Mul.· L.natᶜ n
stage = iter V.gain O.D
bracket : ∀ n → (h (index n) ≼ stage n) × (stage n ≼ L.suc (h (index n)))
bracket zero = proj₂ start , ≼-suc (proj₁ start)
bracket (suc n) = ≼-suc (≼-trans {b = R.series (h a)} (proj₁ (block a))
                      (series-mono {h a} {stage n} (proj₁ (bracket n)))) ,
                  s≼s (≼-trans {b = R.series (L.suc (h a))} (series-mono {stage n} {L.suc (h a)} (proj₂ (bracket n)))
                    (≼-trans {b = R.series (h a)} (skip (h a)) (proj₂ (block a))))
  where a = index n

margin : ∀ a → L.suc (h a) ≼ h (a L.+ L.ωᶜ)
margin a = ≼-trans {b = R.series (h a)} (≼l 0 (N.above (h a))) (proj₂ (block a))

old : R.series O.D ≈ᵛ h L.ωᶜ
old = ≼-trans {b = R.series (h L.zero)} (series-mono {O.D} {h L.zero} (proj₁ start)) (proj₂ zero-block) ,
      ≼-trans {b = R.series (h L.zero)} (proj₁ zero-block) (series-mono {h L.zero} {O.D} (proj₂ start))
  where
  nat : ∀ n → h (L.natᶜ n) ≡ iter N.next (h L.zero) n
  nat zero = refl
  nat (suc n) = cong N.next (nat n)
  zero-block : h L.ωᶜ ≈ᵛ R.series (h L.zero)
  zero-block = l≼ (λ n → ≼l n (subst (h (L.natᶜ n) ≼_) (nat (suc n))
                  (≼-trans {b = L.suc (h (L.natᶜ n))} (≼-suc (≼-refl _)) (N.above (h (L.natᶜ n)))))) ,
               l≼ (λ n → ≼l (suc n) (subst (_≼ h (L.natᶜ (suc n))) (nat (suc n)) (≼-refl _)))

square : V.limit₄ ≈ᵛ h (L.ωᶜ Mul.· L.ωᶜ)
square = l≼ (λ n → ≼l (suc (suc n)) (≼-trans {b = L.suc (h (index (suc n)))} (proj₂ (bracket (suc n))) (margin (index (suc n))))) ,
         l≼ (λ n → ≼l n (≼-trans {b = stage n} (proj₁ (bracket n)) (≼-suc (≼l 0 (≼-trans (≼-suc (≼-refl _)) (N.above (stage n)))))))
```

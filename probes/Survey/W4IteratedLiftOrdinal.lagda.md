# 把一个升层律的反复使用换算成 g 的下标增量

第四层。若变换可从任意 g(a) 以上的预算启动，有限次迭代的上确界把下标增量右乘 ω；所有有限次如此升层的上确界把它右乘 ω^ω。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftOrdinal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import W4Block as W
open import WVOne using (T₀; 𝟏)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; l≼; ≼l; +-mono; ≼-+ʳ)
import B18Product as M
import B19IdealProduct as Ar
import Survey.W4RoomDerivative as D
import Survey.W4RoomHeight as H
import Survey.W4NextLiftValue as Prior
import Survey.W4TowerLawStandard as First
import Survey.W4IteratedLiftSeries as S

Acts : (T₀ → T₀) → T₀ → Set
Acts f t = ∀ a x → D.g a ≼ x → D.g (a L.+ t) ≼ f x
narrow : ∀ f u v → u ≼ v → Acts f v → Acts f u
narrow f u v d r a x q = ≼-trans (Prior.monotone {x = a L.+ u} {y = a L.+ v} (+-mono (≼-refl a) d)) (r a x q)

omega : ∀ f t → Acts f t → Acts (H.repeat f) (t M.· L.ωᶜ)
omega f t r a x q = l≼ λ { zero → ≼l 0 (≼-trans (Prior.monotone {x = a} {y = a L.+ t} (≼-+ʳ a t)) (r a x q));
                              (suc n) → ≼l n (finite (suc n)) }
  where
  finite : ∀ n → D.g (a L.+ (t M.· L.natᶜ n)) ≼ W.iter f x n
  finite zero = q
  finite (suc n) = ≼-trans {b = D.g ((a L.+ (t M.· L.natᶜ n)) L.+ t)}
    (Prior.monotone {x = a L.+ ((t M.· L.natᶜ n) L.+ t)} {y = (a L.+ (t M.· L.natᶜ n)) L.+ t}
      (proj₂ (Ar.assoc+ a (t M.· L.natᶜ n) t))) (r (a L.+ (t M.· L.natᶜ n)) _ (finite n))

finite : ∀ f t → Acts f t → ∀ n → Acts (S.ops f n) (t M.· Prior.stride n)
finite f t r zero = narrow f _ t (proj₁ (Ar.one t)) r
finite f t r (suc n) = narrow (S.ops f (suc n)) _ ((t M.· Prior.stride n) M.· L.ωᶜ)
  (proj₂ (Ar.assoc t (Prior.stride n) L.ωᶜ)) (omega (S.ops f n) (t M.· Prior.stride n) (finite f t r n))

jump : ∀ f t → Acts f t → Acts (S.jump f) (t M.· Prior.exponent)
jump f t r a x q = l≼ λ n → ≼l n (≼l 0 (finite f t r n a x q))

stages = W.iter S.jump D.next
stride = λ n → Ar.power Prior.exponent (L.natᶜ n)
width = Ar.power Prior.exponent L.ωᶜ
stair : ∀ n → Acts (stages n) (stride n)
stair zero a x q = First.next-mono q
stair (suc n) = jump (stages n) (stride n) (stair n)

weak : ∀ n x → stages n x ≼ stages (suc n) x
weak n x = ≼l 0 (≼l 0 (≼-refl _))
```

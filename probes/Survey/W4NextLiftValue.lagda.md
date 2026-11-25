# 第二座标准塔越过 g(ω²)

第四层。实际首个正询问含任意有限组重复块，整座第二塔达到 g(ω^ω)。结合相邻标准塔的迭代，得到高于 g(ω²) 的整树下界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4NextLiftValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
import W4Block as W
import W4Path as P
open import WVOne using (T₀; read; 𝟏)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼-suc; s≼s; l≼; ≼l; z≼)
import B12Terminal as T
import B12ActualSlots as C
import B15ReadPaths as R
import B15TowerIteration as Iter
import B18Product as M
import B19IdealProduct as Ar
import B20Room as Room
import B20StandardInside as Std
import B21StandardShape as Rise
import B22TowerCut as K
import Survey.W4NextLiftBlock as B
import Survey.W4NextLiftStandard as Standard
import Survey.W4RoomDerivative as D
import Survey.W4TowerLawStandard as Prior
import Survey.W4RouteTests as Old
open T.Run

stride = λ n → Ar.power L.ωᶜ (L.natᶜ n)
start : ∀ y → D.g L.zero ≼ D.g y
start L.zero = ≼-refl _
start (L.suc y) = ≼-trans (start y) (≼-trans (≼-suc (≼-refl _)) (D.above (D.g y)))
start (L.lim s) = ≼l 0 (start (s 0))
monotone : ∀ {x y} → x ≼ y → D.g x ≼ D.g y
monotone {y = y} z≼ = start y
monotone (s≼s q) = Prior.next-mono (monotone q)
monotone (≼l n q) = ≼l n (monotone q)
monotone (l≼ q) = l≼ λ n → monotone (q n)

inflation : ∀ n x → x ≼ B.op n x
inflation zero x = ≼-trans (≼-suc (≼-refl _)) (D.above x)
inflation (suc n) x = ≼l 0 (inflation n x)

step : ∀ n a x → D.g a ≼ x → D.g (a L.+ stride n) ≼ B.op n x
step zero a x q = Prior.next-mono q
step (suc n) a x high = l≼ λ { zero → ≼l 0 (≼-trans high (inflation n x)); (suc j) → ≼l j (finite (suc j)) }
  where
  t = stride n
  finite : ∀ j → D.g (a L.+ (t M.· L.natᶜ j)) ≼ W.iter (B.op n) x j
  finite zero = high
  finite (suc j) = ≼-trans {b = D.g ((a L.+ (t M.· L.natᶜ j)) L.+ t)}
    (monotone {x = a L.+ ((t M.· L.natᶜ j) L.+ t)} {y = (a L.+ (t M.· L.natᶜ j)) L.+ t}
      (proj₂ (Ar.assoc+ a (t M.· L.natᶜ j) t)))
    (step n (a L.+ (t M.· L.natᶜ j)) (W.iter (B.op n) x j) (finite j))

seed : ∀ n → D.g L.zero ≼ B.op n 𝟏
seed zero = Prior.next-mono {L.zero} {𝟏} z≼
seed (suc n) = ≼l 0 (seed n)

strides : ∀ n → D.g (stride n) ≼ B.op (suc n) 𝟏
strides n = ≼-trans {b = D.g (L.zero L.+ stride n)} (monotone {x = stride n} {y = L.zero L.+ stride n} (proj₂ (Ar.plus-id (stride n))))
  (≼-trans {b = B.op n (B.op n 𝟏)} (step n L.zero (B.op n 𝟏) (seed n)) (≼l 1 (≼-refl _)))

exponent = Ar.power L.ωᶜ L.ωᶜ
second : D.g exponent ≼ Std.std 2
second = l≼ go where
  go : ∀ n → D.g (stride n) ≼ Std.std 2
  go zero = ≼-trans {b = B.op 1 𝟏} (strides 0) (≼-trans {b = B.op 2 𝟏} (≼l 0 (≼-refl _)) (Standard.paid 0))
  go (suc n) = ≼-trans {b = B.op (suc (suc n)) 𝟏} (strides (suc n)) (Standard.paid n)

after : ∀ n → D.g (exponent L.+ D.index n) ≼ Std.std (suc (suc (suc n)))
after zero = ≼-trans second (≼-trans (≼-suc (≼-refl _)) (Rise.rise 2))
after (suc n) = ≼-trans {b = D.g ((exponent L.+ D.index n) L.+ L.ωᶜ)}
  (monotone {x = exponent L.+ (D.index n L.+ L.ωᶜ)} {y = (exponent L.+ D.index n) L.+ L.ωᶜ} (proj₂ (Ar.assoc+ exponent (D.index n) L.ωᶜ)))
  (≼-trans {b = D.block (D.g (exponent L.+ D.index n))} (D.limit-block (exponent L.+ D.index n)) (Prior.Step.from n _ (after n)))

bound = D.g (exponent L.+ (L.ωᶜ M.· L.ωᶜ))
cut : bound ≼ K.cut
cut = l≼ λ n → ≼l (suc (suc (suc n))) (after n)
whole : bound ≼ Old.Y
whole = ≼-trans cut K.terminal

past : L.suc (D.g (L.ωᶜ M.· L.ωᶜ)) ≼ bound
past = ≼-trans {b = L.suc (D.g exponent)} (s≼s (monotone {x = L.ωᶜ M.· L.ωᶜ} {y = exponent}
  (≼l 2 (M.mono (M.one-left L.ωᶜ) (≼-refl L.ωᶜ)))))
  (≼-trans {b = D.g (L.suc exponent)} (D.above (D.g exponent))
    (≼l 1 (≼l 1 (≼-refl _))))
```

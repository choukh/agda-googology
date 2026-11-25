# 实际首塔的整值是 h 的不动点

第四层，无条件。h 枚举已标定函数 H 的正不动点。对首塔的第 j 个实际下标施 h 后，三个反馈步后的真实单位覆盖它。因此整座首塔本身是 h 的不动点，所有严格内点的 h 值仍严格在内。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4NextBoundFirst where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; ≼lim⁻)
open import WVOne using (T₀; read; h₁; 𝟏; ≼-+ˡ)
import W4Path as Path
import B12Strict as Strict
import B12Terminal as T
import B27UArbitrary as U
import B29SFirst as F
import B29SCases as Full
import B29SLimit as Orbit
import B29SUnit as Unit
import B26Names as N
import Survey.W4PTODescent as Descent
import Survey.W4RoomDerivative as Fixed
import Survey.W4RoomDiagonal as D
open import Survey.W4FourthLiftValue using (h)

later : ℕ → ℕ
later j = suc (suc (suc j))

advance : ∀ j → L.suc (F.x j) ≼ F.x (suc j)
advance j = Strict.strict {U.index j} {U.index (suc j)} (Orbit.edge j)

three-steps : ∀ (x : ℕ → T₀) → (∀ j → L.suc (x j) ≼ x (suc j)) → ∀ j → D.H.cut (x j) ≼ x (later j)
three-steps x grow j = ≼-trans {b = L.suc (L.suc (L.suc (x j)))} (D.pad 3 (x j))
  (≼-trans {b = L.suc (L.suc (x (suc j)))} (s≼s (s≼s (grow j)))
    (≼-trans {b = L.suc (x (suc (suc j)))} (s≼s (grow (suc j))) (grow (suc (suc j)))))

free-at : ∀ u z → D.H.cut u ≼ read z → h u ≼ U.free z
free-at u z paid = ≼-trans {b = D.three L.+ h u}
  (≼-+ˡ D.three (h u)) (≼-trans {b = D.H.at u 𝟏} (D.buffer u 𝟏)
    (D.H.apply u z paid (U.run z) (U.all z) 𝟏 (T.Run.oneB (U.run z)) (Path.z≤ (h₁ z))))

step : ∀ j → h (F.x j) ≼ F.f (later j)
step j = subst (h (F.x j) ≼_) (U.real (later j))
  (free-at (F.x j) (U.index (later j)) (three-steps F.x advance j))

indices : Full.Y₁ ≼ F.I
indices = ≼-trans {b = F.S} Full.upper (proj₂ F.exact)

inside : ∀ j → F.f j ≼ Full.Y₁
inside j = ≼-trans {b = F.S} (≼l {f = F.f} j (≼-refl _)) Full.lower

fixed : h Full.Y₁ ≈ᵛ Full.Y₁
fixed = ≼-trans {b = h F.I} (D.monotone {Full.Y₁} {F.I} indices)
  (l≼ λ j → ≼-trans {b = F.f (later j)} (step j) (inside (later j))) , Fixed.inflation Full.Y₁

strict-limit : ∀ (t : T₀) (x : ℕ → T₀) → t ≼ L.lim x → (∀ j → L.suc (h (x j)) ≼ t) →
  ∀ q → L.suc q ≼ t → L.suc (h q) ≼ t
strict-limit t x co within q low with ≼lim⁻ {a = q} {f = x} (≼-trans {b = t} low co)
... | j , e = ≼-trans {b = L.suc (h (x j))}
  (s≼s (D.monotone {q} {x j} (≼-trans {b = L.suc q} (≼-suc (≼-refl q)) e))) (within j)

interior : ∀ q → L.suc q ≼ Full.Y₁ → L.suc (h q) ≼ Full.Y₁
interior = strict-limit Full.Y₁ F.x indices λ j → ≼-trans {b = L.suc (F.f (later j))} (s≼s (step j))
  (≼-trans {b = F.f (suc (later j))} (Unit.unit (later j)) (inside (suc (later j))))

above-any : ∀ q → L.suc q ≼ Full.Y₁ → Fixed.next q ≼ Full.Y₁
above-any q low = Fixed.least q Full.Y₁ low (proj₁ fixed)

above-original : Fixed.next (N.value Descent.DepthTwo.beta) ≼ Full.Y₁
above-original = above-any (N.value Descent.DepthTwo.beta) Descent.DepthTwo.strict
```

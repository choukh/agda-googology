# 二层闭项的对角上界

第四层。所取闭项固定 g，严格初段对 g 封闭。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedCapDiagonal where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; s≼s; l≼; ≼l; z≼; ≅→≼)
open import OCF.Align.BTBOValBase using (tr₀)
open import WVOne using (T₀; 𝟏)
import B12Omega3Ref as R
import B13Target as P
import Survey.W4IteratedCap as C
import Survey.W4RoomDerivative as G
import Survey.W4IteratedCapCube as Cube
import B22MovingIndex as E
import Survey.W4FourthLiftValue as Index
import Survey.W4RoomDiagonal as H
import Survey.W4NextLiftValue as Scale
import Survey.W4ReflectionFixed as Fixed

open import Survey.W4IteratedCapShape using (value; wall; bridge)

wall-fixed : G.g wall ≼ wall
wall-fixed = l≼ λ n → ≼l (suc n) (C.indexed (R.S.iter value 𝟏 (suc n)))

grows : ∀ x → x ≼ G.g x
grows L.zero = z≼
grows (L.suc x) = ≼-trans {b = L.suc (G.g x)} (s≼s (grows x)) (G.above (G.g x))
grows (L.lim f) = l≼ λ n → ≼l n (grows (f n))

source-fixed : G.g (tr₀ Cube.source) ≈ᵛ tr₀ Cube.source
source-fixed = ≼-trans {b = G.g wall} (Scale.monotone {x = tr₀ Cube.source} {y = wall} (proj₁ bridge))
  (≼-trans {b = wall} wall-fixed (proj₂ bridge)) , grows (tr₀ Cube.source)

inside : ∀ x → L.suc x ≼ wall → L.suc (G.g x) ≼ tr₀ Cube.source
inside x d = ≼-trans {b = G.g (L.suc x)} (G.above (G.g x))
  (≼-trans {b = G.g wall} (Scale.monotone {x = L.suc x} {y = wall} d)
    (≼-trans {b = wall} wall-fixed (proj₂ bridge)))

closed : ∀ x → L.suc x ≼ tr₀ Cube.source → L.suc (G.g x) ≼ tr₀ Cube.source
closed x d = inside x (≼-trans {b = tr₀ Cube.source} d (proj₁ bridge))

first : G.g L.zero ≼ wall
first = ≼-trans {b = G.g wall} (Scale.start wall) wall-fixed
eps : E.above L.zero ≼ G.g L.zero
eps = ≼-trans {b = Index.h L.zero} (Fixed.above≤next L.zero)
  (≼-trans {b = Index.h (G.g L.zero)} (H.monotone {L.zero} {G.g L.zero} z≼) (proj₁ (G.enumerated L.zero)))
small : ∀ x → L.suc x ≼ E.above L.zero → L.suc (G.g x) ≼ tr₀ Cube.source
small x lo = inside x (≼-trans {b = E.above L.zero} lo (≼-trans {b = G.g L.zero} eps first))

```

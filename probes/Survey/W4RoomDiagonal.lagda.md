# 首座正塔达到 H 的不动点枚举的首个不动点

第四层，无条件。h 连续枚举 H 的正不动点。任一带槽覆盖证据的第一座正塔的运行都达到 h 的首个不动点。证明把每次输出送回这座塔实际选取的下一个层号。[按可数高度升层](W4RoomHeight.lagda.md) · [枚举的起点](W4FourthLiftValue.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4RoomDiagonal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-trans; ≼-suc; ≼l; l≼; s≼s; z≼)
open import WVOne using (T₀; read; 𝟏)
import W4Block as W
import W4Path as P
import B12Terminal as T
import B12ActualSlots as C
import B14Tower as V
import B15TowerSeed as Seed
import B12EboRows as Rows
import Survey.W4RouteTests as A
import Survey.W4PTOSeededQuery as N
import Survey.W4RoomHeight as Height
import Survey.W4FourthLift as G
import Survey.W4FourthLiftValue as Index
open Index using (h)
module H = Height.Climb G.gain G.third-step

three = L.natᶜ 3
pad : ∀ n x → L.natᶜ n L.+ x ≼ W.iter L.suc x n
pad zero L.zero = ≼-refl _
pad (suc n) L.zero = s≼s (pad n L.zero)
pad n (L.suc x) = subst (λ v → L.suc (L.natᶜ n L.+ x) ≼ v) (succ-iter x n) (s≼s (pad n x))
  where
  open import Relation.Binary.PropositionalEquality using (subst; _≡_; refl; cong)
  succ-iter : ∀ x n → L.suc (W.iter L.suc x n) ≡ W.iter L.suc (L.suc x) n
  succ-iter x zero = refl
  succ-iter x (suc n) = cong L.suc (succ-iter x n)
pad n (L.lim a) = l≼ λ i → ≼-trans (pad n (a i)) (lift n (≼l i (≼-refl _)))
  where
  lift : ∀ k {a b : T₀} → a ≼ b → W.iter L.suc a k ≼ W.iter L.suc b k
  lift zero p = p
  lift (suc k) p = s≼s (lift k p)

one-step : ∀ u x → N.next x ≼ H.at u x
one-step L.zero x = ≼-suc (≼l 0 (≼-refl _))
one-step (L.suc u) x = ≼l 0 (one-step u x)
one-step (L.lim a) x = ≼l 0 (one-step (a 0) x)

successors : ∀ u x n → W.iter L.suc x n ≼ W.iter (H.at u) x n
successors u x zero = ≼-refl _
successors u x (suc n) = ≼-trans (s≼s (successors u x n)) (≼-trans (N.above _) (one-step u _))

buffer : ∀ u x → three L.+ h u ≼ H.at u x
buffer L.zero x = ≼-suc (≼l 3 (≼-trans (pad 3 (h L.zero)) (four x)))
  where
  four : ∀ x → W.iter L.suc (h L.zero) 3 ≼ W.iter N.next x 4
  four x = past 3
    where
    past : ∀ n → W.iter L.suc (h L.zero) n ≼ W.iter N.next x (suc n)
    past zero = Index.mono {L.zero} {x} z≼
    past (suc n) = ≼-trans (s≼s (past n)) (N.above _)
buffer (L.suc u) x = ≼l 4 (≼-trans (pad 3 (h (L.suc u))) three-more)
  where
  y = H.at u x
  at-two : h (L.suc u) ≼ H.at u y
  at-two = ≼-trans (Index.mono {h u} {y} (≼-trans (WVOne.≼-+ˡ three (h u)) (buffer u x))) (one-step u y)
  three-more : L.suc (L.suc (L.suc (h (L.suc u)))) ≼ W.iter (H.at u) x 5
  three-more = ≼-trans (s≼s (s≼s (s≼s at-two))) (successors u (H.at u y) 3)
buffer (L.lim a) x = l≼ λ i → ≼l i (buffer (a i) x)

bottom : ∀ u → h L.zero ≼ h u
bottom L.zero = ≼-refl _
bottom (L.suc u) = ≼-trans (bottom u) (≼-trans (≼-suc (≼-refl _)) (N.above _))
bottom (L.lim a) = ≼l 0 (bottom (a 0))

monotone : ∀ {x y} → x ≼ y → h x ≼ h y
monotone {y = y} z≼ = bottom y
monotone (s≼s {a = x} {b = y} p) = Index.mono {h x} {h y} (monotone p)
monotone (≼l n d) = ≼l n (monotone d)
monotone (l≼ f) = l≼ λ n → monotone (f n)

stages : ℕ → T₀
stages = W.iter h L.zero
fixedPoint : T₀
fixedPoint = L.lim stages

fixed : h fixedPoint ≈ᵛ fixedPoint
fixed = l≼ (λ n → ≼l (suc n) (≼-refl _)) , l≼ (λ { zero → z≼ ; (suc n) → ≼l n (≼-refl _) })

least : ∀ q → h q ≼ q → fixedPoint ≼ q
least q close = l≼ each
  where
  each : ∀ n → stages n ≼ q
  each zero = z≼
  each (suc n) = ≼-trans (monotone (each n)) close

module Tower (r : T.Run (W.tw 1)) (cv : C.Covered r) where
  module X = V.At r
  budget : ∀ n → H.cut (stages n) ≼ read (X.idx (suc n))
  budget zero = Seed.First.finite r cv 3
  budget (suc n) = ≼-trans (buffer (stages n) 𝟏)
    (H.apply (stages n) z (budget n) (X.chain z) (V.chain-covered r cv z) 𝟏 (T.Run.oneB (X.chain z)) (X.path z))
    where z = X.idx (suc n)

  whole : fixedPoint ≼ read (T.value r)
  whole = l≼ λ n → ≼-trans (WVOne.≼-+ˡ three (stages n)) (≼-trans (budget n) (into n))
    where
    into : ∀ n → read (X.idx (suc n)) ≼ read (T.value r)
    into n = B16ReadIndex.FirstTower.indices r cv (suc n)
      where import B16ReadIndex

actual : fixedPoint ≼ Rows.child 1
actual = Tower.whole T.tower1 (C.enter W.sL W.tw T.terminal 1 (T.prefix W.tw 1) (C.initial _ P.Ok-Λ))

strict : L.suc fixedPoint ≼ A.c 1
strict = ≼-trans (s≼s actual) (B17CellNext.strict 1 0)
  where import B17CellNext
```

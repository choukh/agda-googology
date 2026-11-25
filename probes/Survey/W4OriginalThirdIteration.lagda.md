# 按指标比较原名中的第三层 Veblen 迭代

第四层，无条件。以每个 g(a) 已固定 ζ 枚举为依据，从任意 d≤g(0) 开始，按 a 次迭代取其上方首个 ζ 枚举不动点，所得值不超过 g(a)。[原名的整行计算](W4OriginalVeblenRows.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4OriginalThirdIteration where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-suc; ≼-refl; s≼s; l≼; ≼l)
open import WVOne using (T₀)
import W4Block as W
import Survey.W4ReflectionFixed as Z
import Survey.W4RoomDiagonal as H
import Survey.W4RoomDerivative as G
open import Survey.W4FourthLiftValue using (h)
open import OCF.Lean.YiRefTw2 using (Rt)
import Survey.W4OriginalVeblenRows as R

third : T₀ → T₀
third x = L.lim (W.iter Z.zeta (L.suc x))

closed : ∀ x y → L.suc x ≼ y → h y ≼ y → third x ≼ y
closed x y low fixed = l≼ steps
  where
  seq = W.iter Z.zeta (L.suc x)
  steps : ∀ n → seq n ≼ y
  steps zero = low
  steps (suc n) = ≼-trans {b = h (seq n)} (Z.zeta≤h (seq n))
    (≼-trans {b = h y} (H.monotone {seq n} {y} (steps n)) fixed)

walk : T₀ → T₀ → T₀
walk d L.zero = d
walk d (L.suc a) = third (walk d a)
walk d (L.lim f) = L.lim (λ n → walk d (f n))

paid : ∀ d → d ≼ G.g L.zero → ∀ a → walk d a ≼ G.g a
paid d low L.zero = low
paid d low (L.suc a) = closed (walk d a) (G.g (L.suc a))
  (≼-trans {b = L.suc (G.g a)} (s≼s (paid d low a)) (G.above (G.g a))) (proj₁ (G.enumerated (L.suc a)))
paid d low (L.lim f) = l≼ λ n → ≼l n (paid d low (f n))

original : ∀ a → walk (Rt R.d-h) a ≼ G.g a
original = paid (Rt R.d-h) (≼-trans (≼-suc (≼-refl _)) R.base-strict)
```

经典读值时，`third x` 从 x+1 开始反复施递增连续的 ζ 枚举，故其值恰为严格大于 x 的首个该枚举的不动点。于是 `walk` 给出整行值公式中的 I₃，`original` 实现了公式 (2) 的树值比较。[ζ 枚举的标定](W4ReflectionFixed.lagda.md)

# 一次 H 不动点容纳整个 ζ 枚举

第四层，无条件。把任一起点上的 ω 次时钟更新装入 H 的一段长度 ω 的下标，由此支配任意可数下标的 ζ 枚举。h 逐项支配 φ₃，g 支付从 D 出发的第四行迭代。[此前的第三行](W4OriginalThirdIteration.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadVeblen where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import WVOne using (T₀)
import W4Block as W
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; ≼l; l≼; s≼s; z≼)
import B18Product as M
import B19IdealProduct as Ar
import B22MovingIndex as E
import B24RKernel as K
import B27UEpsilon as Small
import Survey.W4PTOSeededQuery as N
import Survey.W4ThreeTower as Gap
import Survey.W4FourthLiftValue as I
import Survey.W4RoomDiagonal as HM
import Survey.W4RoomDerivative as G
import Survey.W4ClockClosure as C
import Survey.W4ReflectionFixed as Z
import Survey.W4OriginalThirdIteration as Third

block : ∀ u x → x ≼ K.H u → C.hull x ≼ K.H (u L.+ L.ωᶜ)
block u x start = l≼ λ n → ≼l n (step n)
  where
  step : ∀ n → C.stages-from x n ≼ K.H (u L.+ L.natᶜ n)
  step zero = start
  step (suc n) = Gap.jump-step (u L.+ L.natᶜ n) (C.stages-from x n) (step n)

clock = λ (x : T₀) → L.ωᶜ L.+ (L.ωᶜ M.· x)

zeta-bound : ∀ x → Z.zeta x ≼ K.H (clock x)
zeta-bound L.zero = ≼-trans {b = K.H (L.zero L.+ L.ωᶜ)} (block L.zero L.zero z≼)
  (K.monotone {L.zero L.+ L.ωᶜ} {L.ωᶜ} (proj₁ (Ar.plus-id L.ωᶜ)))
zeta-bound (L.suc x) = ≼-trans {b = K.H (clock x L.+ L.ωᶜ)} (block (clock x) (Z.zeta x) (zeta-bound x))
  (K.monotone {clock x L.+ L.ωᶜ} {clock (L.suc x)} (proj₁ (Ar.assoc+ L.ωᶜ (L.ωᶜ M.· x) L.ωᶜ)))
zeta-bound (L.lim f) = l≼ λ n → ≼l n (zeta-bound (f n))

clock-room : ∀ x → L.suc (clock x) ≼ N.next x
clock-room x = ≼-trans {b = E.above x}
  (S.finite {clock x} (S.sumC {L.ωᶜ} {L.ωᶜ M.· x} om (S.mulC {L.ωᶜ} {x} om S.seed))) (Z.above≤next x)
  where
  module S = Small.At x
  om = Gap.Gap.omega-in x

zeta-room : ∀ x t → L.suc t ≼ N.next x → L.suc (Z.zeta t) ≼ N.next x
zeta-room x t p = ≼-trans {b = L.suc (K.H (clock t))} (s≼s (zeta-bound t))
  (≼-trans {b = K.H (L.suc (clock t))} (K.grow (clock t))
    (≼-trans {b = K.H (N.next x)} (K.monotone {L.suc (clock t)} {N.next x}
      (≼-trans {b = N.next t} (clock-room t) (N.least t (N.next x) p (proj₁ (N.fixed x)))))
      (proj₁ (N.fixed x))))

seed : ∀ x → L.suc (L.suc x) ≼ N.next x
seed x = ≼-trans {b = L.suc (C.hull x)} (s≼s (≼l 1 (C.rises x))) (Gap.Gap.strict x)

third-bound : ∀ x → Third.third x ≼ N.next x
third-bound x = l≼ λ n → ≼-trans (≼-suc (≼-refl _)) (each n)
  where
  seq = W.iter Z.zeta (L.suc x)
  each : ∀ n → L.suc (seq n) ≼ N.next x
  each zero = seed x
  each (suc n) = zeta-room x (seq n) (each n)

phi₃ : T₀ → T₀
phi₃ L.zero = Third.third L.zero
phi₃ (L.suc x) = Third.third (phi₃ x)
phi₃ (L.lim f) = L.lim (λ n → phi₃ (f n))

enum-bound : ∀ x → phi₃ x ≼ I.h x
enum-bound L.zero = third-bound L.zero
enum-bound (L.suc x) = ≼-trans {b = N.next (phi₃ x)} (third-bound (phi₃ x))
  (I.mono {phi₃ x} {I.h x} (enum-bound x))
enum-bound (L.lim f) = l≼ λ n → ≼l n (enum-bound (f n))

index≤phi₃ : ∀ x → x ≼ phi₃ x
index≤phi₃ L.zero = z≼
index≤phi₃ (L.suc x) = ≼l {f = W.iter Z.zeta (L.suc (phi₃ x))} 0 (s≼s (index≤phi₃ x))
index≤phi₃ (L.lim f) = l≼ λ n → ≼l n (index≤phi₃ (f n))

fixed-at-g : ∀ a → phi₃ (G.g a) ≈ᵛ G.g a
fixed-at-g a = ≼-trans {b = I.h (G.g a)} (enum-bound (G.g a)) (proj₁ (G.enumerated a)) , index≤phi₃ (G.g a)

fourth : T₀ → T₀
fourth x = L.lim (W.iter phi₃ (L.suc x))
fourth-at : ∀ x y → L.suc x ≼ y → I.h y ≼ y → fourth x ≼ y
fourth-at x y low fixed = l≼ steps
  where
  seq = W.iter phi₃ (L.suc x)
  steps : ∀ n → seq n ≼ y
  steps zero = low
  steps (suc n) = ≼-trans {b = I.h (seq n)} (enum-bound (seq n))
    (≼-trans {b = I.h y} (HM.monotone {seq n} {y} (steps n)) fixed)

walk : T₀ → T₀ → T₀
walk d L.zero = d
walk d (L.suc a) = fourth (walk d a)
walk d (L.lim f) = L.lim (λ n → walk d (f n))

paid : ∀ d → d ≼ G.g L.zero → ∀ a → walk d a ≼ G.g a
paid d low L.zero = low
paid d low (L.suc a) = fourth-at (walk d a) (G.g (L.suc a))
  (≼-trans {b = L.suc (G.g a)} (s≼s (paid d low a)) (G.above (G.g a))) (proj₁ (G.enumerated (L.suc a)))
paid d low (L.lim f) = l≼ λ n → ≼l n (paid d low (f n))
```

经典读值时，clock(α)=ω+ω·α。若 λ 是 x 上方首个 H 不动点而 t<λ，则 clock(t) 严格低于 t 上方首个 ε 数，后者不超过 t 上方首个 H 不动点，故 clock(t)<λ。H 严格递增，给出 ζ(t)≤H(clock(t))<H(λ)=λ。由 `seed` 还有 x+1<λ，从 x+1 反复施 ζ 并取上确界，便得到严格高于 x 的首个 ζ 不动点，值 ≤λ。按 φ₀(α)=ω^α 的下标约定，ζ=φ₂，它的不动点由 φ₃ 枚举。`enum-bound` 给 φ₃(α)≤h(α)，`fixed-at-g` 给 φ₃(g(α))=g(α)。再从任一起点取上方首个 φ₃ 不动点，便是 `walk` 使用的第四行后继步。[ζ 的经典标定](W4ClockClosure.lagda.md) · [原记号的行指标](W4OriginalVeblenRows.lagda.md)

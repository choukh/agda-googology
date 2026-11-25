# ε、ζ 的枚举与参照函数 h

第四层，无条件。对任意指标 x，两种枚举的第 x 项均不超过 h(x)。因而每个 h 不动点也固定这两种枚举。ζ 的经典命名沿用已证的上方首个不动点公式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReflectionFixed where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import WVOne using (T₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-refl; ≼-suc; ≼-trans; s≼s; l≼; ≼l; z≼)
import B19IdealArithmetic as Ar
import B22TowerCut as Mon
import B22MovingIndex as E
import Survey.W4ClockClosure as Clock
import Survey.W4RouteTests as Tests
import Survey.W4PTOSeededQuery as H
import Survey.W4ThreeTower as Gap
import Survey.W4FourthLiftValue as Index
import Survey.W4RoomDerivative as D

loosen : ∀ {a b : T₀} → L.suc a ≼ b → a ≼ b
loosen {a} d = ≼-trans {b = L.suc a} (≼-suc (≼-refl a)) d

above≤next : ∀ x → E.above x ≼ H.next x
above≤next x = ≼-trans {b = Clock.jump x} (Tests.clock-below x (E.above x))
  (≼-trans {b = Clock.hull x} (≼l {f = Clock.stages-from x} 1 (≼-refl (Clock.jump x))) (loosen {a = Clock.hull x} {b = H.next x} (Gap.Gap.strict x)))

enum≤h : ∀ x → Clock.enum x ≼ Index.h x
enum≤h L.zero = above≤next L.zero
enum≤h (L.suc x) = ≼-trans {b = E.above (Index.h x)} (Mon.advance {Clock.enum x} {Index.h x} (enum≤h x)) (above≤next (Index.h x))
enum≤h (L.lim f) = l≼ λ n → ≼l n (enum≤h (f n))

epsilon-index : ∀ a → Clock.enum (D.g a) ≈ᵛ D.g a
epsilon-index a = ≼-trans {b = Index.h (D.g a)} (enum≤h (D.g a)) (proj₁ (D.enumerated a)) , Clock.index-below (D.g a)

-- 由 ζ⁺(x) 的已证经典最小性，下面的递归连续枚举 ζ 数。
zeta : T₀ → T₀
zeta L.zero = Clock.hull L.zero
zeta (L.suc x) = Clock.hull (zeta x)
zeta (L.lim f) = L.lim (λ n → zeta (f n))

zeta≤h : ∀ x → zeta x ≼ Index.h x
zeta≤h L.zero = loosen {a = Clock.hull L.zero} {b = H.next L.zero} (Gap.Gap.strict L.zero)
zeta≤h (L.suc x) = ≼-trans {b = H.next (zeta x)} (loosen {a = Clock.hull (zeta x)} {b = H.next (zeta x)} (Gap.Gap.strict (zeta x)))
  (Index.mono {zeta x} {Index.h x} (zeta≤h x))
zeta≤h (L.lim f) = l≼ λ n → ≼l n (zeta≤h (f n))

index≤zeta : ∀ x → x ≼ zeta x
index≤zeta L.zero = z≼
index≤zeta (L.suc x) = ≼-trans {b = L.suc (zeta x)} (s≼s (index≤zeta x))
  (≼l {f = Clock.stages-from (zeta x)} 1 (Clock.rises (zeta x)))
index≤zeta (L.lim f) = l≼ λ n → ≼l n (index≤zeta (f n))

zeta-index : ∀ a → zeta (D.g a) ≈ᵛ D.g a
zeta-index a = ≼-trans {b = Index.h (D.g a)} (zeta≤h (D.g a)) (proj₁ (D.enumerated a)) , index≤zeta (D.g a)

-- 地址序的序型是 ω^x。这里将其与反射迭代的指标逐字校准。
enum-fixed : ∀ x → E.step (Clock.enum x) ≼ Clock.enum x
enum-fixed L.zero = proj₁ (E.fix L.zero)
enum-fixed (L.suc x) = proj₁ (E.fix (Clock.enum x))
enum-fixed (L.lim f) = l≼ λ n → ≼l n (enum-fixed (f n))

import B19IdealPowers as Pow
address-index : ∀ a → E.step (D.g a) ≈ᵛ D.g a
address-index a = ≼-trans {b = E.step (Clock.enum (D.g a))}
  (Pow.expo Pow.omega-pos (proj₂ (epsilon-index a)))
  (≼-trans {b = Clock.enum (D.g a)} (enum-fixed (D.g a)) (proj₁ (epsilon-index a))) , Ar.up (D.g a)
```

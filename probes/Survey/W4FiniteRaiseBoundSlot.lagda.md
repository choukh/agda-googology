# 接收旧折叠所需的输入与任意合法槽的反例

第四层，无条件。每个 n 的旧层前缀均有越过 ε⁺(bₙ) 的实例。若允许任取合法下标，则第一座真实塔的槽表可给出超出 bₙ₊₁ 的覆盖证书，但存在这样的见证严格超过闭项 Y，因而其下标与每个真实反馈地址都不同。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FiniteRaiseBoundSlot where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; subst)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-+ʳ; s≼s)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import WVOne using (read; ≼-+ˡ)
import W4Block as W
import B12ActualSlots as Slots
import B12BtboCut as C
import W4Ops as O
import B20StandardGoal as Real
import B22MovingIndex as E
import B26PActual as A
import B27UArbitrary as U
import Survey.W4FixedDepth as Fixed
import Survey.W4FiniteRaiseBound as Bound
import Survey.W4LegacyOmega as Old

head-separate : (k : ℕ) (x : W.Tr W.zero) → O.ι (W.tw (suc k)) x ≡ proj₁ (O.Ωt (W.tw (suc k))) → ⊥
head-separate k W.zero ()
head-separate k (W.suc x) ()
head-separate k (W.lim f steps) ()
head-separate k (W.Ω () _)
head-separate k (W.up _ () _ _)
head-separate k (W.ex _ _ _ _ ())

module At (i : ℕ) where
  module S = Bound.At i
  old-above : L.suc (E.above (Fixed.sample i)) ≼ Old.p (suc i)
  old-above = ≼-trans {b = C.finite (suc (suc i))} S.below-next-cut (Old.lower (suc i))

  no-scalar-simulation : (f : ℕ → W.Tr W.zero) → (∀ j → S.Built (f j)) → Old.p (suc i) ≼ L.lim (λ j → read (f j)) → ⊥
  no-scalar-simulation f h p = s≼-irrefl (E.above S.b) (≼-trans {b = Old.p (suc i)} old-above
    (≼-trans {b = L.lim (λ j → read (f j))} p (S.limit f h)))

  goal = Fixed.sample (suc i)
  joint = A.Y L.+ goal
  z = proj₁ (U.exceeds joint)

  covered : Slots.Covered (U.run z)
  covered = U.all z

  crosses : L.suc goal ≼ U.free z
  crosses = ≼-trans {b = L.suc joint} (s≼s (≼-+ˡ A.Y goal)) (proj₂ (U.exceeds joint))

  outside : L.suc A.Y ≼ U.free z
  outside = ≼-trans {b = L.suc joint} (s≼s (≼-+ʳ A.Y goal)) (proj₂ (U.exceeds joint))

  absent : ∀ j → z ≡ U.index j → ⊥
  absent j e = s≼-irrefl A.Y (≼-trans {b = U.free (U.index j)} (subst (λ x → L.suc A.Y ≼ U.free x) e outside)
    (subst (_≼ A.Y) (sym (U.real j)) (Real.into 0 j)))
```

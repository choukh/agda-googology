# 反复使用首塔正询问共有的一级子运行

第四层，无条件。从任一正的零树 β 开始，回灌这个真实子调用的完整返回，全部有限轮次的上确界恰为 |β|·ε₀^ω。每一轮的子调用可在首塔任一正询问中定位。起点低于 ψ₀(Ω₂) 时，上确界仍严格低于 ψ₀(Ω₂)。
 
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4ReturnBoundFirst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import WVOne using (T₀; 𝟏; read; lvl1)
import W4Block as W
import W4Fold as F
import W4Path as P
import W4Ops as O
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; l≼; ≼l; ≼-refl; ≼-trans; s≼s; ≼-suc)
open import OCF.Align.TightValBase using (s≼-irrefl)
import B12XRef as Ref
import B18Product as M
import B19IdealProduct as Law
open Law using (_∙_)
import B27UArbitrary as Actual
import B29SUnit as Query
import B30UOrbit as Shared
import B12BtboCut as C
import Survey.W4FiniteOmegaCut as Fin
import Survey.W4LegacyFeedback as Cut
import Survey.W4Rule48 as Rule

ε = Ref.row 1
module K = Fin.At 0

step : O.Tr⁺ W.zero → O.Tr⁺ W.zero
step β = F.ψ lvl1 Shared.o Shared.B W.zero (P.z≤ lvl1) β (proj₁ (O.Ωt lvl1))

module Run (β : O.Tr⁺ W.zero) where
  state = W.iter step β
  x = read (proj₁ β)
  val = λ n → read (proj₁ (state n))

  located : ∀ n j → W.zero W.⊢ proj₁ (state (suc n)) ◃ Query.output (state n) (Actual.index (suc j))
  located n j = Shared.place (state n) j

  formula : ∀ n → val n ≈ᵛ (x M.· Law.power ε (L.natᶜ n))
  formula zero = Law.flip (Law.one x)
  formula (suc n) = Shared.general (state n) ∙ Law.mul (formula n) (Law.id ε) ∙ Law.assoc x (Law.power ε (L.natᶜ n)) ε

  total : T₀
  total = L.lim val
  exact : total ≈ᵛ (x M.· Law.power ε L.ωᶜ)
  exact = Law.lim formula

  short : K.small x → L.suc total ≼ C.finite 2
  short p = ≼-trans {b = L.suc (x M.· Law.power ε L.ωᶜ)} (s≼s (proj₁ exact))
    (K.product x (Law.power ε L.ωᶜ) p (K.power ε L.ωᶜ ε-small K.omega))
    where
    ε-small : K.small ε
    ε-small = ≼-trans {b = L.suc (C.finite 1)} (s≼s Ref.epsilon) (Cut.step 1)

  misses-first : K.small x → Rule.Start.H.middle ≼ total → ⊥
  misses-first p reach = s≼-irrefl total (≼-trans {b = C.finite 2} (short p)
    (≼-trans {b = C.finite 3} (≼-trans {b = L.suc (C.finite 2)} (≼-suc (≼-refl _)) (Cut.step 2))
      (≼-trans {b = L.suc (C.finite 3)} (≼-suc (≼-refl _)) (≼-trans {b = Rule.Start.H.middle} Rule.finite-three-short reach))))

module FromOne = Run (O.Ωt W.zero)
value : FromOne.total ≈ᵛ Law.power ε L.ωᶜ
value = FromOne.exact ∙ Law.left-one (Law.power ε L.ωᶜ)

no-first : Rule.Start.H.middle ≼ FromOne.total → ⊥
no-first = FromOne.misses-first K.one
```

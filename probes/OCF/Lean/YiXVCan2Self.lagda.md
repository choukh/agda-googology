# YiXV: 二层自身折叠的模拟保持
> 验收文件。档位：编译定理。由 YiXVSlotSrc.Fold 推广；种子有指定前缀的模拟后，二层自身折叠保持模拟，不改源折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Self where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVCanTau as T
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Add as A
import OCF.Lean.YiXVCan2Psi as P
import OCF.Lean.YiXVCanTauPair as TP
import OCF.Lean.YiXVCan2Rel as S
import OCF.Lean.YiXVCan2Plus as Cl
import OCF.Lean.YiXVCan2Lift as K
import OCF.Lean.YiXVCan2Assoc as AS

module Fold (B : Base (suc zero)) (SrcB : Base (suc (suc zero))) (Z : F.T₂) (gz : C.Gd Z)
  (γ : Tr (suc (suc zero))) (nγ : suc (suc zero) ⊢ zero ◃ γ)
  (seed : S.Rel.U B γ (P.Ψ (Z L.+ F.Ω₂))) where
  module U = S.Rel B
  module Q = Cl.Closure B
  χ = ψs (suc (suc zero)) tt tt SrcB (suc (suc zero)) self γ nγ
  nχ = nzs (suc (suc zero)) tt tt SrcB (suc (suc zero)) self γ nγ

  result : ∀ {x X} → C.Gd X → U.U x X → U.U (χ x) (P.Ψ (Z L.+ X))
  result gx U.uz = seed
  result (C.gs gx) (U.us {x = x} h) = Q.next (nχ x) (P.good (A.good gz gx)) (result gx h)
  result gx (U.uw h q) = U.uw (result (C.left q) h) (P.mono (A.plus (C.refl gz) q))
  result gx (U.ul h) = U.ul (λ n → result gx (h n))
  result (C.gn₀ law gb) (U.un₀ h) = U.un₀ (λ a y q →
    let y′ = L.tr⁻ L.z≅ y; q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
    in result (gb y′ (O.s→1 q′)) (h a y′ q′))
  result (C.gn₁ law gb) (U.un₁ h) = U.un₁ (λ a X Y gX gY o ha ca q →
    result (gb (T.τ Y) (T.good gY) (T.floor o))
      (h a X (T.τ Y) gX (T.good gY) (T.floor o) ha ca (R.trans q (proj₁ (TP.pair gY)))))
  result gx (U.uu {x = x} {y = y} {ny = ny} gy h gz₁ hz cz) = U.uw
    (K.Lift.upc B (nχ x) (A.good gz gy) (result gy h) gz₁ hz cz)
    (P.mono (AS.mixed gz gy gz₁))
```

# YiXV: 二层模拟的上折保持
> 验收文件。档位：编译定理。由 YiXVCarry.Lift 推广；从第 0 层和第 1 层上折时，保留同一二层前缀的模拟。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Lift where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegFold using (Base)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl; ≼-trans)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2Add as A
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2Psi as P
import OCF.Lean.YiXVCan2Add as CA
import OCF.Lean.YiXVCan2Rel as S
import OCF.Lean.YiXVCan2Plus as Cl
import OCF.Lean.YiXVCan2AffRef as AR

module Lift (B : Base (suc zero)) where
  module U = S.Rel B
  module Q = Cl.Closure B
  module Low = U.Low
  module HC = U.HC

  ground : ∀ {x X} (d : Dn (suc (suc zero)) zero) (nx : suc (suc zero) ⊢ zero ◃ x) → C.Gd X → U.U x (P.Ψ X) →
    (z : Tr zero) → U.U (Up zero d x nx z) (P.Ψ (L.add X A.σ₀ (read z)))
  ground d nx gx hx zero = hx
  ground {X = X} d nx gx hx (suc z) = Q.next (Up-nz zero d _ nx z)
    (P.good (M.good₀ gx (read z))) (ground d nx gx hx z)
  ground {X = X} d nx gx hx (lim f a) = U.ul (λ n → U.uw (ground d nx gx hx (f n))
    (C.pack (P.good (M.good₀ gx (read (f n)))) (C.gl (λ m → P.good (M.good₀ gx (read (f m)))))
      (C.lr n (C.refl (P.good (M.good₀ gx (read (f n))))))))
  ground d nx gx hx (Ω () g)
  ground d nx gx hx (up y () z e)

  upc : ∀ {x X y Y} (nx : suc (suc zero) ⊢ zero ◃ x) → C.Gd X → U.U x (P.Ψ X) → O.Gd Y →
    (h : Low.U y Y) → HC.Closed h → U.U (Upc (suc (suc zero)) tt x nx y) (P.Ψ (L.add X A.σ₁ Y))
  upc nx gx hx gy (Low.uz p q) refl = U.uw hx
    (P.mono (CA.rightE (C.refl gx) (C.gu O.Gd-Ω) (M.good₁ gx O.Gd-Ω)))
  upc {y = suc y} nx gx hx (O.gs gy) (Low.us h) c = Q.next (Upc-nz (suc (suc zero)) tt _ nx y)
    (P.good (M.good₁ gx gy)) (upc nx gx hx gy h c)
  upc nx gx hx gy (Low.uw gy₀ h q) c = U.uw (upc nx gx hx gy₀ h c) (P.mono (M.tail (C.refl gx) gy₀ gy q))
  upc nx gx hx gy (Low.ul h) c = U.ul (λ n → upc nx gx hx gy (h n) (c n))
  upc nx gx hx (O.gi law gb) (Low.un h) c = U.un₀ (λ a y q →
    let y′ = L.tr⁻ L.z≅ y; q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
    in upc nx gx hx (gb y′ (O.s→1 q′)) (h a y′ q′) (c a y′ q′))
  upc {x = x} {X = X} nx gx hx gy (Low.uu {x = y} {y = z} {ny = nz} {X = Y} {Y = Z} {σ′ = σ} gy₀ h q) c =
    U.uw (ground (down (down stop tt) tt) (Upc-nz (suc (suc zero)) tt x nx y) (M.good₁ gx gy₀) (upc nx gx hx gy₀ h c) z)
      (P.mono (C.trans (M.ground (C.refl (M.good₁ gx gy₀)) q) (AR.assoc gx gy₀ σ Z)))
```

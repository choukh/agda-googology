# YiXV: 更新孩子底的非零目标保持
> 验收文件。档位：编译定理。由 YiXVSlotSrc.Fold 改写；任意带好树证据的二层前缀，保持目标 1 的模拟与字面起点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2SlotOne where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (T₀; read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVPlus as P
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as A
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2One as I
import OCF.Lean.YiXVCan2Add as CA
import OCF.Lean.YiXVCan2AffRef as AR

module Lift (B : Base (suc zero)) where
  module U = S.Sim B
  module Cl = P.Closure B
  module HC = H.Anchor B

  upc : ∀ {x X} (nx : suc zero ⊢ zero ◃ x) → C.Gd X → U.U x (F.ψ₁ X) → (z : Tr zero) →
    U.U (Upc (suc zero) tt x nx z) (F.ψ₁ (L.add X A.σ₀ (read z)))
  upc nx gx hx zero = hx
  upc {X = X} nx gx hx (suc z) = Cl.next-comp (Upc-nz (suc zero) tt _ nx z)
    (I.good₁ (M.good₀ gx (read z))) (upc nx gx hx z)
  upc {X = X} nx gx hx (lim f a) = U.ul (λ n → U.uw (I.good₁ (M.good₀ gx (read (f n))))
    (upc nx gx hx (f n)) (R.≤l n (O.reflₚ (I.good₁ (M.good₀ gx (read (f n)))))))
  upc nx gx hx (Ω () g)
  upc nx gx hx (up y () z e)

  closed : ∀ {x X} (nx : suc zero ⊢ zero ◃ x) (gx : C.Gd X) (hx : U.U x (F.ψ₁ X)) → HC.Closed hx →
    (z : Tr zero) → HC.Closed (upc nx gx hx z)
  closed nx gx hx c zero = c
  closed nx gx hx c (suc z) = HC.next-closed (Upc-nz (suc zero) tt _ nx z)
    (I.good₁ (M.good₀ gx (read z))) (upc nx gx hx z) (closed nx gx hx c z)
  closed nx gx hx c (lim f a) = λ n → closed nx gx hx c (f n)
  closed nx gx hx c (Ω () g)
  closed nx gx hx c (up y () z e)

module Fold (B SrcB : Base (suc zero)) (X : F.T₂) (gx : C.Gd X)
  (γ : Tr (suc zero)) (nγ : suc zero ⊢ zero ◃ γ)
  (seed : S.Sim.U B γ (F.ψ₁ X)) (seedC : H.Anchor.Closed B seed) where
  module U = S.Sim B
  module Cl = P.Closure B
  module HC = H.Anchor B
  χ = ψs (suc zero) tt tt SrcB (suc zero) self γ nγ
  nχ = nzs (suc zero) tt tt SrcB (suc zero) self γ nγ
  Φ : R.T₁ → R.T₁
  Φ Y = F.ψ₁ (L.add X A.σ₁ Y)
  GΦ : ∀ {Y} → O.Gd Y → O.Gd (Φ Y)
  GΦ gy = I.good₁ (M.good₁ gx gy)
  hγ : U.U γ (Φ O.Ω₁)
  hγ = U.uw (I.good₁ gx) seed (I.mono₁ (CA.rightE (C.refl gx) (C.gu O.Gd-Ω) (M.good₁ gx O.Gd-Ω)))

  Out : Tr (suc zero) → R.T₁ → Set
  Out y Y = Σ (U.U (χ y) (Φ Y)) HC.Closed

  up-case : ∀ {x Y} (y : Tr zero) (ny : zero ⊢ zero ◃ y) (Z : T₀)
    (σ : L.Simᴵ L.zero (L.suc L.zero)) → O.Gd Y → read y ≼ Z → Out x Y → Out (up x tt y ny) (L.add Y σ Z)
  up-case {x} {Y} y ny Z σ gy q (h , c) =
    U.uw (I.good₁ (M.good₀ (M.good₁ gx gy) (read y)))
      (Lift.upc B (nχ x) (M.good₁ gx gy) h y)
      (I.mono₁ (C.trans (M.ground (C.refl (M.good₁ gx gy)) q) (AR.assoc gx gy σ Z))) ,
    Lift.closed B (nχ x) (M.good₁ gx gy) h c y

  result : ∀ {y Y} (gy : O.Gd Y) (h : U.U y Y) → HC.Closed h → Out y Y
  result gy (U.uz p q) refl = hγ , seedC
  result (O.gs gy) (U.us {x = y} h) c =
    Cl.next-comp (nχ y) (GΦ gy) (proj₁ (result gy h c)) ,
    HC.next-closed (nχ y) (GΦ gy) (proj₁ (result gy h c)) (proj₂ (result gy h c))
  result gy (U.uw gy₀ h q) c = U.uw (GΦ gy₀) (proj₁ (result gy₀ h c))
    (I.mono₁ (M.tail (C.refl gx) gy₀ gy q)) , proj₂ (result gy₀ h c)
  result gy (U.ul h) c = U.ul (λ n → proj₁ (result gy (h n) (c n))) , λ n → proj₂ (result gy (h n) (c n))
  result (O.gi law gb) (U.un h) c = U.un (λ a y q →
    let y′ = L.tr⁻ L.z≅ y; q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
    in proj₁ (result (gb y′ (O.s→1 q′)) (h a y′ q′) (c a y′ q′))) ,
    (λ a y q → let y′ = L.tr⁻ L.z≅ y; q′ = ≼-trans q (proj₂ (O.tr⁻≈ y))
    in proj₂ (result (gb y′ (O.s→1 q′)) (h a y′ q′) (c a y′ q′)))
  result gy (U.uu {y = y} {ny = ny} {Y = Z} {σ′ = σ} gy₀ h q) c = up-case y ny Z σ gy₀ q (result gy₀ h c)
```

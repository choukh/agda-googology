# YiXV: 二层模拟对加法与 next 封闭
> 验收文件。档位：编译定理。由 YiXVPlus 推广到 YiXVCan2Rel；每个孩子输入携带已有低层模拟与字面起点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Plus where
open import Data.Nat using (zero; suc)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps hiding (next)
open import OCF.Lean.YiLegFold using (Base)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Add as A
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2Psi as P
import OCF.Lean.YiXVCan2Assoc as Assoc
import OCF.Lean.YiXVCan2Rel as S
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)

module Closure (B : Base (suc zero)) where
  module U = S.Rel B
  plus : ∀ {x X y Y} → C.Gd X → U.U x X → C.Gd Y → U.U y Y → U.U (x + y) (X L.+ Y)
  plus gx hx gy U.uz = U.uw hx (A.plus (C.refl gx) (C.z≤ C.Gd-Ω₂))
  plus gx hx (C.gs gy) (U.us hy) = U.us (plus gx hx gy hy)
  plus gx hx gy (U.uw hy q) = U.uw (plus gx hx (C.left q) hy) (A.plus (C.refl gx) q)
  plus gx hx gy (U.ul h) = U.ul (λ n → plus gx hx gy (h n))
  plus gx hx (C.gn₀ law gb) (U.un₀ h) = U.un₀ (λ a y q → plus gx hx (gb y (O.s→1 q)) (h a y q))
  plus gx hx (C.gn₁ law gb) (U.un₁ h) = U.un₁ (λ a X Y gX gY o ha ca q → plus gx hx (gb Y gY o) (h a X Y gX gY o ha ca q))
  plus gx hx gy (U.uu gy₀ hy gZ hz cz) = U.uw (U.uu (A.good gx gy₀) (plus gx hx gy₀ hy) gZ hz cz) (Assoc.mixed gx gy₀ gZ)

  module Power {x X} (gx : C.Gd X) (hx : U.U x X) where
    terms : ∀ n → U.U (iter (x +_) x n) (iterᴸ (X L.+_) L.zero (suc n))
    terms zero = hx
    terms (suc n) = plus gx hx (P.good-iter gx (suc n)) (terms n)

  next : ∀ {x X} → (nx : suc (suc zero) ⊢ zero ◃ x) → C.Gd X → U.U x X →
    U.U (OCF.Lean.YiLegOps.next x nx) (L.lim (iterᴸ (X L.+_) L.zero))
  next nx gx hx = U.ul (λ n → U.uw (Power.terms gx hx n)
    (C.pack (P.good-iter gx (suc n)) (C.gl (P.good-iter gx)) (C.lr (suc n) (C.refl (P.good-iter gx (suc n))))))
```

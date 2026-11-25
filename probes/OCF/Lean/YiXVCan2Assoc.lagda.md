# YiXV: 二层加法的结合方向
> 验收文件。档位：编译定理。沿右端的好树证据递归；同层与低层尾部给出左结合到右结合的比较，所有层号字面固定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Assoc where
open import Data.Nat using (zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-trans)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2Add as OldA
open import OCF.Lean.YiXVCan2Core
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2Add as A

σ₀ = OldA.σ₀
σ₁ = OldA.σ₁

ground : ∀ {X Y} → Gd X → Gd Y → (z : R.T₀) →
  Le (L.add (X L.+ Y) σ₀ z) (X L.+ L.add Y σ₀ z)
ground gx gy L.zero = refl (A.good gx gy)
ground gx gy (L.suc z) = s≤ (ground gx gy z)
ground gx gy (L.lim f) = pack (gl (λ n → M.good₀ (A.good gx gy) (f n)))
  (gl (λ n → A.good gx (M.good₀ gy (f n))))
  (ll (λ n → pack (M.good₀ (A.good gx gy) (f n)) (gl (λ m → A.good gx (M.good₀ gy (f m)))) (lr n (ground gx gy (f n)))))
ground gx gy (L.limᵢ () f)
ground gx gy (L.up () y)

mixed : ∀ {X Y Z} → Gd X → Gd Y → O.Gd Z → Le (L.add (X L.+ Y) σ₁ Z) (X L.+ L.add Y σ₁ Z)
mixed gx gy O.gz = refl (A.good gx gy)
mixed gx gy (O.gs gZ) = s≤ (mixed gx gy gZ)
mixed gx gy (O.gl gZ) = pack (gl (λ n → M.good₁ (A.good gx gy) (gZ n)))
  (gl (λ n → A.good gx (M.good₁ gy (gZ n))))
  (ll (λ n → pack (M.good₁ (A.good gx gy) (gZ n)) (gl (λ m → A.good gx (M.good₁ gy (gZ m)))) (lr n (mixed gx gy (gZ n)))))
mixed gx gy (O.gi law gb) = pack (M.good₁ (A.good gx gy) (O.gi law gb)) (A.good gx (M.good₁ gy (O.gi law gb)))
  (nn₀ (λ x y o q → trans (mixed gx gy (gb x o))
    (A.plus (refl gx) (M.tail (refl gy) (gb x o) (gb y (≼-trans o q)) (O.SC.mo law x y o q)))))
mixed gx gy O.gu = ground gx gy _

same : ∀ {X Y Z} → Gd X → Gd Y → Gd Z → Le ((X L.+ Y) L.+ Z) (X L.+ (Y L.+ Z))
same {X} {Y} gx gy OCF.Lean.YiXVCan2Core.gz = refl {X = X L.+ Y} (A.good {X = X} {Y = Y} gx gy)
same gx gy (gs gZ) = s≤ (same gx gy gZ)
same gx gy (gl gZ) = pack (gl (λ n → A.good (A.good gx gy) (gZ n)))
  (gl (λ n → A.good gx (A.good gy (gZ n))))
  (ll (λ n → pack (A.good (A.good gx gy) (gZ n)) (gl (λ m → A.good gx (A.good gy (gZ m)))) (lr n (same gx gy (gZ n)))))
same gx gy (gn₀ law gb) = pack (A.good (A.good gx gy) (gn₀ law gb)) (A.good gx (A.good gy (gn₀ law gb)))
  (nn₀ (λ x y o q → trans (same gx gy (gb x o)) (A.plus (refl gx) (A.plus (refl gy) (SC₀.mo₀ law x y o q)))))
same gx gy (gn₁ law gb) = pack (A.good (A.good gx gy) (gn₁ law gb)) (A.good gx (A.good gy (gn₁ law gb)))
  (nn₁ (λ x y hx hy o q → trans (same gx gy (gb x hx o)) (A.plus (refl gx) (A.plus (refl gy) (SC₁.mo₁ law x y hx hy o q)))))
same gx gy (gu gZ) = mixed gx gy gZ
```

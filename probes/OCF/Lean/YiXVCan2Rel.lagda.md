# YiXV: 实际源树的二层模拟域
> 验收文件。档位：编译定理。零行的参照固定为 Ω₂，两个结点行显式带后继余量；这是模拟文法，值定理在 YiXVCan2Sem。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Rel where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegFold using (Base)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as A
import OCF.Lean.YiXVSim as S
import OCF.Lean.YiXVAnchor as H
import OCF.Lean.YiXVCan2Core as C

module Rel (B : Base (suc zero)) where
  module Low = S.Sim B
  module HC = H.Anchor B
  data U : Tr (suc (suc zero)) → F.T₂ → Set where
    uz : U zero F.Ω₂
    us : ∀ {x X} → U x X → U (suc x) (L.suc X)
    uw : ∀ {x X Y} → U x X → C.Le X Y → U x Y
    ul : ∀ {g a X} → (∀ n → U (g n) X) → U (lim g a) X
    un₀ : ∀ {g f} → (∀ a y → L.suc (read a) ≼ y → U (g a) (f y)) →
      U (Ω (inj₂ (inj₁ tt)) g) (L.limᵢ (L.suc L.zero) f)
    un₁ : ∀ {g f} → (∀ a X Y → O.Gd X → O.Gd Y → O.Ω₁ R.≤ₚ Y →
      (h : Low.U a X) → HC.Closed h → L.suc X R.≤ₚ Y → U (g a) (f Y)) →
      U (Ω (inj₁ tt) g) (L.limᵢ L.zero f)
    uu : ∀ {x y ny X Y} → C.Gd X → U x X → O.Gd Y → (h : Low.U y Y) → HC.Closed h →
      U (up x tt y ny) (L.add X A.σ₁ Y)
```

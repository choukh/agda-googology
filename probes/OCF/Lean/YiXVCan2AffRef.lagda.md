# YiXV: 低层尾部节点的五字段供给
> 验收文件。档位：编译定理。由 YiXVAffRef 改写到带好树证据的比较；Norm 的五字段全称成立，Ω₂ 的完整实例已填。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2AffRef where
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l; 1≼ψ⁰; s≼s; z≼) renaming (+-mono to +ᵛ)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVRef2Add as OldA
import OCF.Lean.YiXVCan2Core as C
import OCF.Lean.YiXVCan2Mix as M
import OCF.Lean.YiXVCan2Zero as Z
import OCF.Lean.YiXVNum as N

σ₀ = OldA.σ₀
σ₁ = OldA.σ₁

assoc : ∀ {X Y} → C.Gd X → O.Gd Y → (σ : L.Simᴵ L.zero (L.suc L.zero)) → (z : R.T₀) →
  C.Le (L.add (L.add X σ₁ Y) σ₀ z) (L.add X σ₁ (L.add Y σ z))
assoc gx gy σ L.zero = C.refl (M.good₁ gx gy)
assoc gx gy σ (L.suc z) = C.s≤ (assoc gx gy σ z)
assoc gx gy σ (L.lim f) = C.pack (C.gl (λ n → M.good₀ (M.good₁ gx gy) (f n)))
  (C.gl (λ n → M.good₁ gx (O.Gd-add⁰ gy (f n))))
  (C.ll (λ n → C.pack (M.good₀ (M.good₁ gx gy) (f n)) (C.gl (λ m → M.good₁ gx (O.Gd-add⁰ gy (f m))))
    (C.lr n (assoc gx gy σ (f n)))))
assoc gx gy σ (L.limᵢ () f)
assoc gx gy σ (L.up () y)

module Aff (X : F.T₂) (gx : C.Gd X) (f : R.T₀ → R.T₁) (sc : O.SC f)
  (gb : ∀ y → R.𝟙 ≼ y → O.Gd (f y)) where
  S : R.T₀ → F.T₂
  S y = L.add X σ₁ (f y)
  P ν : R.T₀ → R.T₀
  P y = L.ψ (L.suc L.zero) (λ r → r) (S y)
  ν y = L.ψ⁰ (S y)
  norm : N.Norm P ν
  N.Norm.same norm y = F.ψ₀≈ (S y)
  N.Norm.pos norm y = ≼-trans (1≼ψ⁰ (S y)) (proj₂ (F.ψ₀≈ (S y)))
  N.Norm.mo norm x y o q = Z.mono₀ (M.tail (C.refl gx) (gb x o) (gb y (≼-trans o q)) (O.SC.mo sc x y o q))
  N.Norm.db norm y o = Z.mono₀ (M.tail (C.refl gx) (O.gs (gb y o)) (gb (L.suc y) (s≼s z≼)) (O.SC.db sc y o))
  N.Norm.two norm = ≼-trans (≼l 2 (+ᵛ (1≼ψ⁰ X) (1≼ψ⁰ X)))
    (≼-trans (Z.mono₀ (M.tail (C.refl gx) (O.gs O.gz) (gb R.𝟙 (≼-refl _)) (O.SC.po sc))) (proj₂ (F.ψ₀≈ (S R.𝟙))))

module Sample = Aff F.Ω₂ C.Gd-Ω₂ (L.up L.zero) O.SC-up (λ y o → O.gu)
sample : N.Norm Sample.P Sample.ν
sample = Sample.norm
```

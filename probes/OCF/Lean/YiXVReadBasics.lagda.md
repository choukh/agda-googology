# YiXVReadBasics
> 验收文件。档位：编译定理。源模拟的坐标稳定与基础保持；每个实际后继层的 Ω 以两份参照 Ω 模拟。
> 复用原 h₁/lvl 与 YiXVLvlLiteral，源模拟从 YiXVSourceFamily/Basics 推广；未交一般源世界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadBasics where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (z≼; s≼s; l≼; ≼-trans)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as Ω
import OCF.Lean.YiXVCountableGroundValue as G
import OCF.Lean.YiXVCountableAddFrame as Add
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
stable : ∀ x p a X → U.Fam x p a X ≡ U.UR (J.slot x p) (J.outB x p a) X
stable S.zero ()
stable (S.suc x) (inj₁ t) a X = refl
stable (S.suc x) (inj₂ p) a X = stable x p a X
stable (S.lim f d) (n , inj₁ t) a X = refl
stable (S.lim f d) (n , inj₂ p) a X = stable (f n) p a X
stable (S.Ω () g) p a X
stable (S.up x () y e) p a X
zero : ∀ x → U.UR x S.zero (L.Ω (T.lvl x))
zero S.zero = z≼
zero (S.suc x) = U.Layer.uz
zero (S.lim f d) = U.Layer.uz
zero (S.Ω () g)
zero (S.up x () y e)
sucU : ∀ x {a X} → U.UR x a X → U.UR x (S.suc a) (L.suc X)
sucU S.zero h = s≼s h
sucU (S.suc x) h = U.Layer.us h
sucU (S.lim f d) h = U.Layer.us h
sucU (S.Ω () g) h
sucU (S.up x () y e) h
weak : ∀ x {a X Y} → U.UR x a X → A.Le X Y → U.UR x a Y
weak S.zero h p = ≼-trans h (G.value p)
weak (S.suc x) h p = U.Layer.uw h p
weak (S.lim f d) h p = U.Layer.uw h p
weak (S.Ω () g) h p
weak (S.up x () y e) h p
limU : ∀ x {f d X} → (∀ n → U.UR x (f n) X) → U.UR x (S.lim f d) X
limU S.zero h = l≼ h
limU (S.suc x) h = U.Layer.ul h
limU (S.lim f d) h = U.Layer.ul h
limU (S.Ω () g) h
limU (S.up x () y e) h

Ωsuc : ∀ x → U.UR (S.suc x) (O.Ωt (J.ℓ (S.suc x)))
  (L.Ω (T.lvl (S.suc x)) L.+ L.Ω (T.lvl (S.suc x)))
Ωsuc x = D.un (inj₁ tt) (λ a X Y gx gy o ha t → D.uw
  (D.uu tt gΩ D.uz (A.Layer.gs gx) (sucU x ha))
  (Add.mixed {σ = λ q → L.suc q} {τ = λ q → L.suc q}
    (A.Layer.rfl (T.lvl (S.suc x)) A.Gd< A.Le< gΩ) t))
  where
  module D = U.Layer (S.suc x) (U.Fam (S.suc x))
  gΩ = proj₁ (Ω.model (T.lvl (S.suc x)))
actual : U.UR (S.suc S.zero) (O.Ωt (J.ℓ (S.suc S.zero)))
  (L.Ω (L.suc L.zero) L.+ L.Ω (L.suc L.zero))
actual = Ωsuc S.zero
```

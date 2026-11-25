# YiXVReadFamily
> 验收文件。档位：编译定理。源模拟按实际读回层号分级，量化域为原 h₁ 的源层及其带证据位置。
> 复用原 h₁/lvl 与 YiXVLvlLiteral，源模拟从 YiXVSourceFamily/Basics 推广；未交一般源世界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadFamily where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
open import OCF.Lean.YiLSRead using (read)
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadIndex as J

module Layer (x : S.Tr S.zero)
  (Lo : ∀ (p : S.Pos (J.ℓ x)) → S.Br (J.ℓ x) p → L.Ordᶜ (T.lvl (J.slot x p)) → Set) where
  data U : S.Tr (J.ℓ x) → L.Ordᶜ (T.lvl x) → Set where
    uz : U S.zero (L.Ω (T.lvl x))
    us : ∀ {a X} → U a X → U (S.suc a) (L.suc X)
    uw : ∀ {a X Y} → U a X → A.Le X Y → U a Y
    ul : ∀ {f d X} → (∀ n → U (f n) X) → U (S.lim f d) X
    un : ∀ (p : S.Pos (J.ℓ x)) {g f} →
      (∀ (a : S.Br (J.ℓ x) p) X Y → A.Gd X → A.Gd Y →
        A.Le (L.Ω (T.lvl (J.slot x p))) Y → Lo p a X → A.Le (L.suc X) Y →
        U (g a) (f (L.into (L.<→◃ (J.q x p)) Y))) →
      U (S.Ω p g) (L.limᵢ (J.q x p) f)
    uu : ∀ (c : S.Ch (J.ℓ x)) {a b nb X Y} →
      A.Gd X → U a X → A.Gd Y → Lo (J.child-slot x c) (J.ctoB x c b) Y →
      U (S.up a c b nb) (L.add X (J.σchild x c) Y)
mutual
  UR : ∀ x → S.Tr (J.ℓ x) → L.Ordᶜ (T.lvl x) → Set
  UR S.zero a X = read a ≼ X
  UR x@(S.suc y) a X = Layer.U x (Fam x) a X
  UR x@(S.lim f d) a X = Layer.U x (Fam x) a X
  UR (S.Ω () g) a X
  UR (S.up x () y e) a X
  Fam : ∀ x (p : S.Pos (J.ℓ x)) → S.Br (J.ℓ x) p → L.Ordᶜ (T.lvl (J.slot x p)) → Set
  Fam S.zero ()
  Fam (S.suc x) (inj₁ t) a X = UR x a X
  Fam (S.suc x) (inj₂ p) a X = Fam x p a X
  Fam (S.lim f d) (n , inj₁ t) a X = UR (f n) a X
  Fam (S.lim f d) (n , inj₂ p) a X = Fam (f n) p a X
  Fam (S.Ω () g) p a X
  Fam (S.up x () y e) p a X
```

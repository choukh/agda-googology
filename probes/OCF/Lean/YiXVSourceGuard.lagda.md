# YiXVSourceGuard
> 验收文件。档位：编译定理。保留分支的反向守卫搬运；实填正层前提。
> 按 YiXVCan2Sem、YiXVSourceAffine* 与 YiXVSourceGrowth 统一；未交实际全基底、所有 pre n、Need1 或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVSourceGuard where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import Data.Fin as F
import OCF.Lean.YiLegBlock as S
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteTransportShape as T
import OCF.Lean.YiXVFiniteTransportInputs as Q
import OCF.Lean.YiXVFiniteTransport as Trans
import OCF.Lean.YiXVSourceIndex as J
import OCF.Lean.YiXVSourceFamily as U
import OCF.Lean.YiXVSourceBasics as UB
import OCF.Lean.YiXVSourcePathInputs as Cast

module Bridge (n k : ℕ) (source : F.Fin (suc n)) (target : F.Fin (suc k)) (e : I.rank k target ≡ I.rank n source) where
  m = I.rank n source
  pullS : J.Tr (I.rank k target) → J.Tr m
  pullS a = subst J.Tr e a
  pullR : I.T (I.rank k target) → I.T m
  pullR X = subst I.T e X
  good : ∀ X → A.Gd (I.rank k target) X → A.Gd m (pullR X)
  good X gx = Cast.cast-good e X gx
  floor : ∀ X → A.Le (I.rank k target) (L.Ω (L.natᴵ (I.rank k target))) X → A.Le m (L.Ω (L.natᴵ m)) (pullR X)
  floor X t = Cast.cast-floor e X t
  rel : ∀ a X → U.UR k target a X → U.UR n source (pullS a) (pullR X)
  rel a X h = subst (λ X → X) (sym (UB.stable n source _ _))
    (Cast.cast-rel e a X (subst (λ X → X) (UB.stable k target a X) h))
  τ-good : ∀ X → A.Gd (I.rank k target) X → A.Gd m (T.τ T.bwd m (pullR X))
  τ-good X gx = Q.Ops.good (Trans.ops m) T.bwd F.zero _ (good X gx)
  τ-floor : ∀ X → A.Le (I.rank k target) (L.Ω (L.natᴵ (I.rank k target))) X → A.Le m (L.Ω (L.natᴵ m)) (T.τ T.bwd m (pullR X))
  τ-floor X t = B.trans m F.zero {X = L.Ω (L.natᴵ m)} {Y = T.τ T.bwd m (L.Ω (L.natᴵ m))} {Z = T.τ T.bwd m (pullR X)}
    (proj₁ (Q.Ops.pair (Trans.ops m) T.bwd F.zero _ (proj₁ (B.Ω-model m F.zero))))
    (Q.Ops.mono (Trans.ops m) T.bwd F.zero _ _ (floor X t))
  τ-margin : ∀ X Y → A.Gd (I.rank k target) Y → A.Le (I.rank k target) (L.suc X) Y →
    A.Le m (L.suc (pullR X)) (T.τ T.bwd m (pullR Y))
  τ-margin X Y gy t = B.trans m F.zero {X = L.suc (pullR X)} {Y = pullR Y} {Z = T.τ T.bwd m (pullR Y)}
    (Cast.cast-margin e X Y t) (proj₁ (Q.Ops.pair (Trans.ops m) T.bwd F.zero _ (good Y gy)))

module Model = Bridge 2 4 F.zero (F.suc (F.suc F.zero)) refl
actual : U.UR 2 F.zero S.zero (L.Ω (L.natᴵ 2))
actual = Model.rel S.zero (L.Ω (L.natᴵ 2)) (UB.zeroU 2)
```

# 在已进入的语境中比较指数 1 和完整 Ω

第四层，无条件。在任意折叠语境，孩子的完整 Ω 指数严格超过指数 1 的零层返回。适用于 Ω₃ 反馈调用中实际进入的 Ω₂ 语境。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchRunFrame where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import W4Block as W
import W4Ops as O
import W4Path as P
import W4Fold as F
import B12Strict as Strict
import B13FiniteLift as Lift
open import WVOne using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; s≼s)

module In {ℓ : W.L} {X : F.Cx ℓ} (j : W.L) (o : P.Ok ℓ) (T : F.TD X (Lift.sc j)) (K : F.Op X) where
  m = F.chMT T tt
  push : F.St X → F.St (F.cons (O.down (F.fr T) tt) X)
  push S i t = S i (proj₂ t)
  pull : F.St (F.cons (O.down (F.fr T) tt) X) → F.St X
  pull S i t = S i (F.σ m t)
  states : ∀ n S → pull (F.itS (F.enterO m K) n (push S)) ≡ F.itS K n S
  states zero S = refl
  states (suc n) S = cong (F.stepS K) (states n S)

  values : ∀ n S i (t : F.⟦ X ⟧ i) v →
    F.itV (F.enterO m K) n (push S) i (F.σ m t) v ≡ F.itV K n S i t v
  values zero S i t v = refl
  values (suc n) S i t v rewrite states n S | values n S i t v = refl

  first = W.up {S = W.Sig (Lift.sc j)} W.zero tt (W.suc W.zero) W.◃s
  module At (S : F.St X) (t : F.⟦ X ⟧ W.zero) (v : O.Tr⁺ W.zero) where
    see = λ x → read (proj₁ (F.E o T x K S W.zero t v))
    terms = λ k → read (proj₁ (F.itV (F.enterO m K) (suc k) (push S) W.zero (F.σ m t) v))
    same : see (W.suc W.zero) ≼ see first
    same = l≼ λ k → ≼l {f = terms} k (subst (λ a → read (proj₁ a) ≼ terms k) (values (suc k) S W.zero t v) (≼-refl _))

    gain : L.suc (see (W.suc W.zero)) ≼ see (proj₁ (O.Ωt (Lift.sc j)))
    gain = ≼-trans {b = L.suc (see first)} (s≼s same)
      (Strict.strict (F.Emono o T K S W.zero t v {x = first} {y = proj₁ (O.Ωt (Lift.sc j))} W.◃w))
```

# 每一份实际正槽自身就容纳无限列升层

第四层。一次累计槽的第 n 个前缀含 n+1 个标准正块。前缀数任意大，在极限的每条零路径可选取任意足够靠后的前缀，因此整个正槽支付所有有限次升层的上确界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedLiftSeries where

open import Data.Nat.Base as N using (ℕ; zero; suc; _≤_)
import Data.Nat.Properties as NP
open import Data.List.Base using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import W4Block as W
import W4Ops as O
open import WVOne using (T₀)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≼l; l≼)
import Survey.W4RoomHeight as H
import Survey.W4NextLiftIndex as I
import Survey.W4IteratedLiftBlock as B
import Survey.W4IteratedLiftRun as R
import Survey.W4IteratedLiftSlot as S

ops = W.iter H.repeat
jump : R.Op → R.Op
jump f x = L.lim (λ n → ops f (suc n) x)

later : ∀ f i m x → i ≤ m → ops f i x ≼ ops f m x
later f i m x d = grow (NP.≤⇒≤′ d)
  where
  grow : ∀ {k} → i N.≤′ k → ops f i x ≼ ops f k x
  grow N.≤′-refl = ≼-refl _
  grow (N.≤′-step h) = ≼l 0 (grow h)

module Lift (g : S.Family) where
  seq = λ n → proj₁ (O.Ωt B.k O.⊞ g n)
  module At (p : Data.List.Base.List W.L) (nz : B.Nonzero (I.plug p W.zero)) (f : R.Op) (low : H.Law (I.plug p W.zero) f) where
    row = λ n → B.readL (O.cum seq n)
    prefix : ∀ n → H.Law (I.plug p (row n)) (ops f (suc n))
    prefix zero = B.raise (B.append B.seed (proj₁ (g 0))) [] p nz low
    prefix (suc n) = B.raise (B.append B.seed (proj₁ (g (suc n)))) (O.cum seq n ∷ []) p nz (prefix n)
    subs : ∀ i m → i ≤ m → H.Law (I.plug p (row m)) (ops f (suc i))
    subs i m d r cv x hi w = ≼-trans (later f (suc i) (suc m) x (N.s≤s d)) (prefix m r cv x hi w)
    full : H.Law (W.nd W.sL (λ n → I.plug p (row n))) (jump f)
    full r cv x hi w = l≼ λ i → H.Limit.all (λ n → I.plug p (row n)) i (ops f (suc i)) (subs i) r cv x hi w
    paid : H.Law (I.plug p (B.readL (S.tree g))) (jump f)
    paid = subst (λ l → H.Law l (jump f)) (sym (I.node p W.sL row)) full

transfer : ∀ {t} → S.Series t → R.Transfer t jump
transfer (S.witness g) = Lift.At.paid g
```

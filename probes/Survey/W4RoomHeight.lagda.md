# 沿实际层号迭代有零槽下界的变换

第四层。后继层同时更新全部零槽与显式返回。极限层沿指定零路径可以选取任意足够靠后的孩子，因而同一个变换可以按可数树高度迭代。[继承槽的运行](W4FourthLift.lagda.md)

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4RoomHeight where

import Data.Nat.Base as N
open N using (ℕ; zero; suc; _⊔_)
import Data.Nat.Properties as NP
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import W4Block as W
import W4Fold as F
import W4Path as P
import W4Ops as O
open import WVOne using (T₀; read; h₁; 𝟏)
open import WVTwo using (◃→≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼-suc; s≼s; ≼l; l≼)
import B12Terminal as T
import B12ActualSlots as C
import B14Tower as V
import B14Floor as Floor
import B20OldStage as St
import B20Room as Room
import B31PPrefix as Prefix
open T.Run

Law : W.L → (T₀ → T₀) → Set
Law j f = (r : T.Run j) → C.Covered r → ∀ x → Room.Room r x → ∀ w → f x ≼ V.valueAt r w

repeat : (T₀ → T₀) → T₀ → T₀
repeat f x = L.lim (λ n → W.iter f x (suc n))

module Successor (s : W.Sh) (h : W.Ch s → W.L) (f : T₀ → T₀) (pay : Law (W.nd s h) f)
  (r : T.Run (W.nd W.sS (λ _ → W.nd s h))) (cv : C.Covered r) (x : T₀) (high : Room.Room r x) where
  module A = St.At s h r cv
  room : ∀ n w → W.iter f x n ≼ read (proj₁ (A.S n W.zero w))
  room zero w = ≼-trans (high (W.inc tt w)) (◃→≼ (F.inf A.K (bs A.r₀) W.zero w (bs A.r₀ W.zero w)))
  room (suc n) w = ≼-trans (pay (V.reset a (bs a W.zero w) (oneB a w)) (A.cover n) _ (room n) w)
    (A.weaken _ w _)
    where a = A.setup w (β r) (oneβ r) n

  emit : ∀ w n → W.iter f x (suc n) ≼ read (proj₁ (A.v w (β r) (suc n)))
  emit w n = ≼-trans (pay (A.setup w (β r) (oneβ r) n) (A.cover n) _ (room n) w) (A.weaken _ w _)

  all : ∀ w → repeat f x ≼ V.valueAt r w
  all (W.inc tt w) = l≼ λ n → ≼-trans (emit w n) (A.send A.select (β r) n)
  all (W.inu ws) = l≼ λ n → ≼-trans (emit (ws tt) n) (A.send (A.every refl) (β r) n)

later : ∀ (g : ℕ → W.L) (o : ∀ n → g n W.≤ g (suc n)) m k → k N.≤ m →
  Σ (g k W.≤ g m) (λ p → P.way g o m k ≡ inj₂ p)
later g o m zero d = _ , refl
later g o (suc m) (suc k) (N.s≤s d) = later (λ n → g (suc n)) (λ n → o (suc n)) m k d

module Limit (g : ℕ → W.L) (j : ℕ) (f : T₀ → T₀) (pay : ∀ m → j N.≤ m → Law (g m) f)
  (r : T.Run (W.nd W.sL g)) (cv : C.Covered r) (x : T₀) (high : Room.Room r x) where
  root = W.nd W.sL g
  child : ∀ m → W.zero W.≤ root → T.Run (g m)
  child m w = V.reset (T.limRun g r m) b (≼-trans (oneβ r) (T.inflate0 root (ok r) (bs r) w (β r) (T.prefix g m)))
    where b = F.ψ root (ok r) (bs r) W.zero w (β r) (T.prefix g m)

  term = λ w m → read (proj₁ (F.ψ root (ok r) (bs r) W.zero w (β r) (T.prefix g (suc m))))
  part : ∀ w m → term w m ≼ V.valueAt r w
  part (W.inc k v) zero = ≼l 0 (≼-refl _)
  part (W.inc k v) (suc m) = ≼l (suc m) (≼-refl _)
  part (W.inu ws) zero = ≼l 0 (≼-refl _)
  part (W.inu ws) (suc m) = ≼l (suc m) (≼-refl _)

  picked : ∀ k m (v : W.zero W.≤ g k) → k N.≤ m → j N.≤ m → f x ≼ term (W.inc k v) m
  picked k m v d jm rewrite Prefix.At.segment g r m with later g (proj₁ (ok r)) m k d
  ... | p , eq rewrite eq = pay m jm (child m (W.inc k v)) (C.enter W.sL g r m (T.prefix g m) cv) x
    (λ t → ≼-trans (high (W.inc m t)) (T.inflate0 root (ok r) (bs r) (W.inc m t) (bs r W.zero _) (T.prefix g m))) (v W.∙ p)

  all : ∀ w → f x ≼ V.valueAt r w
  all (W.inc k v) = ≼-trans (picked k (k ⊔ j) v (NP.m≤m⊔n k j) (NP.m≤n⊔m k j)) (part (W.inc k v) (k ⊔ j))
  all (W.inu ws) = ≼-trans
    (pay j NP.≤-refl (M.sub j) (M.covered cv j) x
      (λ t → ≼-trans (high (W.inc j t)) (T.inflate0 root (ok r) (bs r) (W.inc j t) (bs r W.zero _) (T.prefix g j))) (ws j))
    (M.part j)
    where module M = V.Lim g r ws

increasing : ∀ {g : ℕ → W.Tr W.zero} → (∀ n → W.zero W.⊢ g n ◃ g (suc n)) →
  ∀ j m → j N.≤ m → read (g j) ≼ read (g m)
increasing {g} step j m jm = walk (NP.≤⇒≤′ jm)
  where
  walk : ∀ {k} → j N.≤′ k → read (g j) ≼ read (g k)
  walk N.≤′-refl = ≼-refl _
  walk {suc k} (N.≤′-step p) = ≼-trans (walk p) (◃→≼ (step k))

up : ∀ z → L.natᶜ 3 ≼ read z → ∀ f → Law (h₁ z) f → Law (h₁ (W.suc z)) (repeat f)
up W.zero ()
up (W.suc z) p = Successor.all W.sS (λ _ → h₁ z)
up (W.lim g d) p = Successor.all W.sL (λ n → h₁ (g n))

module Climb (f : T₀ → T₀) (seed : Law (h₁ (Floor.num 3)) f) where
  base : ∀ z → L.natᶜ 3 ≼ read z → Law (h₁ z) f
  base W.zero ()
  base (W.suc z) (s≼s d) with Floor.split 2 z d
  ... | Data.Sum.Base.inj₁ refl = seed
  ... | inj₂ ge = λ r cv x hi w → ≼-trans (≼l 0 (≼-refl _)) (up z ge f (base z ge) r cv x hi w)
  base (W.lim g e) (≼l j d) = Limit.all (λ m → h₁ (g m)) j f
    (λ m jm → base (g m) (≼-trans d (increasing e j m jm)))

  at : T₀ → T₀ → T₀
  at L.zero = f
  at (L.suc u) = repeat (at u)
  at (L.lim a) x = L.lim (λ n → at (a n) x)

  cut = λ u → L.natᶜ 3 L.+ u
  three : ∀ u → L.natᶜ 3 ≼ cut u
  three L.zero = ≼-refl _
  three (L.suc u) = ≼-suc (three u)
  three (L.lim a) = ≼l 0 (three (a 0))

  apply : ∀ u z → cut u ≼ read z → Law (h₁ z) (at u)
  apply L.zero = base
  apply (L.suc u) (W.suc z) (s≼s d) = up z (≼-trans (three u) d) (at u) (apply u z d)
  apply (L.suc u) (W.lim g e) (≼l j d) = Limit.all (λ m → h₁ (g m)) j (at (L.suc u))
    (λ m jm → apply (L.suc u) (g m) (≼-trans d (increasing e j m jm)))
  apply (L.lim a) z d r cv x hi w = l≼ λ n → apply (a n) z (≼-trans (≼l n (≼-refl _)) d) r cv x hi w
```

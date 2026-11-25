# 首枝目标在第 4 层的有限迭代检验

第四层。要让 ψ₀ψ₃(Ω₂) 进入指定读值，充分条件是它的每个基本列值皆被一次实际有限迭代严格超过。反向可在排中律下抽取两个自然数地址；无条件已可排除所有有限迭代共受任何一个基本列值约束。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchCapTest where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
open import WVOne using (read; T₀; cum-≥)
import W4Ops as O
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; s≼s; ≼-+ʳ; +-mono)
open import OCF.Align.TightValBase using (s≼-irrefl)
open import OCF.Lean.YiRVLevel using (LEM)
import B12Strict as Strict
import B17ValueDich as Compare
import B18Product as M
import B19IdealArithmetic as Ar
import B19IdealProduct as Alg
import B26PSuffix as Ref
import B28BValues as Values
import Survey.W4FiniteOmegaCut as Cut
import Survey.W4FirstBranchCap as Rows
import Survey.W4FiniteRaiseWindow as Window
import Survey.W4FirstBranchRoom as Room

module Test {small full} (parts : Rows.Parts small full) where
  open Rows.Parts parts
  raw = λ k → proj₁ (term k)
  amount = λ n → read (raw n)
  module S = Values.Series raw amount (λ _ → refl)
  module W = S.Whole full outer
  module T = Values.Series (λ j → raw (suc j)) (λ j → amount (suc j)) (λ _ → refl)
  module R = T.Whole (L.lim T.pre) refl

  split : ∀ n → S.sum (suc n) ≈ᵛ (small L.+ T.sum n)
  split zero = Alg.add (Alg.flip first) (Alg.id (amount 1))
  split (suc n) = Alg.add (split n) (Alg.id (amount (suc (suc n)))) Alg.∙ Alg.assoc+ small (T.sum n) (amount (suc (suc n)))

  after-first : full ≈ᵛ (small L.+ L.lim T.sum)
  after-first = W.exact Alg.∙ (l≼ point , l≼ (λ n → ≼l {f = S.sum} (suc n) (proj₂ (split n))))
    where
    point : ∀ n → S.sum n ≼ small L.+ L.lim T.sum
    point zero = ≼l {f = λ n → small L.+ T.sum n} 0
      (≼-trans {b = S.sum 1} (≼-+ʳ (amount 0) (amount 1)) (proj₁ (split 0)))
    point (suc n) = ≼l {f = λ m → small L.+ T.sum m} n (proj₁ (split n))

  tail-bound : ∀ x → (∀ j m → finite (suc j) m ≼ x) → full ≼ (small L.+ (x M.· L.ωᶜ))
  tail-bound x cap = ≼-trans {b = small L.+ L.lim T.sum} (proj₁ after-first)
    (+-mono (≼-refl small) (≼-trans {b = L.lim T.pre} (proj₂ R.exact) (R.cap x
      (λ j → subst (_≼ x) (sym (inner (suc j))) (l≼ (cap j))))))

  row-in : ∀ k → L.suc (amount k) ≼ full
  row-in k = subst (L.suc (amount k) ≼_) (sym outer) (≼l {f = S.pre} (suc k)
    (≼-trans {b = L.suc (S.pre k)} (s≼s (cum-≥ raw k)) (Strict.strict (O.+-mono (O.cum raw k) (proj₂ (term (suc k)))))))

  item-in : ∀ k n → finite k n ≼ full
  item-in k n = ≼-trans {b = amount k} (subst (finite k n ≼_) (sym (inner k)) (≼l {f = finite k} n (≼-refl _)))
    (≼-trans {b = L.suc (amount k)} (≼-suc (≼-refl _)) (row-in k))

  bounded : (x : T₀) → (∀ k n → finite k n ≼ x) → full ≼ (x M.· L.ωᶜ)
  bounded x cap = W.cap x (λ k → subst (_≼ x) (sym (inner k)) (l≼ (cap k)))

  module At (n : ℕ) where
    module Q = Cut.At n
    sum : ∀ a b → Q.small a → Q.small b → Q.small (a L.+ b)
    sum a b pa pb = ≼-trans {b = L.suc (Ar.norm a M.· Ar.norm b)} (s≼s
      (≼-trans {b = Ar.norm (a L.+ b)} (Ar.up (a L.+ b)) (proj₁ (Alg.power-sum L.ωᶜ a b))))
      (Q.product _ _ (Q.omega-power a pa) (Q.omega-power b pb))

    caps = ∀ k → Σ T₀ (λ y → Q.small y × (∀ m → finite k m ≼ y))

    bounded-row : caps → ∀ k → Q.small (amount k)
    bounded-row c k = let y , py , p = c k in ≼-trans {b = L.suc y}
      (s≼s (subst (_≼ y) (sym (inner k)) (l≼ p))) py

    sufficient : caps → full ≼ Q.q
    sufficient c = ≼-trans {b = L.lim S.sum} (proj₁ W.exact)
      (l≼ (λ k → ≼-trans {b = L.suc (S.sum k)} (≼-suc (≼-refl _)) (pre k)))
      where
      pre : ∀ k → Q.small (S.sum k)
      pre zero = bounded-row c 0
      pre (suc k) = sum (S.sum k) (amount (suc k)) (pre k) (bounded-row c (suc k))

    necessary : full ≼ Q.q → caps
    necessary p k = amount k , ≼-trans {b = full} (row-in k) p ,
      λ m → subst (finite k m ≼_) (sym (inner k)) (≼l {f = finite k} m (≼-refl _))

module Live = Test Rows.fourth
module ThirdCut = Live.At 1
open Rows.Parts Rows.fourth using (finite)

hits : Set
hits = ∀ k → Σ ℕ (λ j → Σ ℕ (λ m → L.suc (Room.child k) ≼ finite j m))

sufficient : hits → Room.target ≼ Window.Live.full 2
sufficient h = ≼-trans {b = L.lim Room.child} (proj₁ (Ref.limit Room.h refl Room.child (λ _ → Alg.id _))) (l≼ λ k →
  let j , m , paid = h k in ≼-trans {b = L.suc (Room.child k)} (≼-suc (≼-refl _))
    (≼-trans {b = finite j m} paid (Live.item-in j m)))

no-cap : Room.target ≼ Window.Live.full 2 → (k : ℕ) → (∀ j m → finite j m ≼ Room.child k) → ⊥
no-cap pay k cap = s≼-irrefl (Room.child k M.· L.ωᶜ) (≼-trans {b = Room.target} (Room.room k)
  (≼-trans {b = Window.Live.full 2} pay (Live.bounded (Room.child k) cap)))

module Classical (lem : LEM) where
  necessary : Room.target ≼ Window.Live.full 2 → hits
  necessary pay k with lem (Σ ℕ (λ j → Σ ℕ (λ m → L.suc (Room.child k) ≼ finite j m)))
  ... | inj₁ ok = ok
  ... | inj₂ no = ⊥-elim (no-cap pay k all)
    where
    all : ∀ j m → finite j m ≼ Room.child k
    all j m with Compare.Classical.compare lem (finite j m) (Room.child k)
    ... | inj₁ low = low
    ... | inj₂ past = ⊥-elim (no (j , m , past))
```

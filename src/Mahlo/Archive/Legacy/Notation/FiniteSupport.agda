{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Notation.FiniteSupport where

-- Executable finite support families, following [Se98] 5.1--5.2.
-- Lists may contain duplicates: no quotient or decidable equality is needed.
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Unit using (⊤; tt)
open import Mahlo.Archive.Legacy.Universe.External using (Sum; inl; inr)

data Empty : Set where

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : (P → Empty) → Dec P

infix 4 _∈_
data _∈_ {X : Set} (x : X) : List X → Set where
  first : {xs : List X} → x ∈ (x ∷ xs)
  later : {y : X} {xs : List X} → x ∈ xs → x ∈ (y ∷ xs)

infixr 5 _++_
_++_ : {X : Set} → List X → List X → List X
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Any {X : Set} (P : X → Set) : List X → Set where
  here : {x : X} {xs : List X} → P x → Any P (x ∷ xs)
  there : {x : X} {xs : List X} → Any P xs → Any P (x ∷ xs)

All : {X : Set} → (X → Set) → List X → Set
All P [] = ⊤
All P (x ∷ xs) = Σ (P x) (λ _ → All P xs)

module On (X : Set) where
  Family = List (List X)

  Holds : (X → Set) → Family → Set
  Holds A = Any (All A)

  -- Tensor concatenates each pair of supports; ++ is extensional union.
  prefix : List X → Family → Family
  prefix xs [] = []
  prefix xs (ys ∷ yss) = (xs ++ ys) ∷ prefix xs yss

  tensor : Family → Family → Family
  tensor [] yss = []
  tensor (xs ∷ xss) yss = prefix xs yss ++ tensor xss yss

  all-join : {A : X → Set} (xs ys : List X)
    → All A xs → All A ys → All A (xs ++ ys)
  all-join [] ys px py = py
  all-join (x ∷ xs) ys (px , pxs) py = px , all-join xs ys pxs py

  all-split : {A : X → Set} (xs ys : List X)
    → All A (xs ++ ys) → Σ (All A xs) (λ _ → All A ys)
  all-split [] ys p = tt , p
  all-split (x ∷ xs) ys (px , p) with all-split xs ys p
  ... | q , r = (px , q) , r

  left : {A : X → Set} {xss yss : Family}
    → Holds A xss → Holds A (xss ++ yss)
  left (here p) = here p
  left (there p) = there (left p)

  right : {A : X → Set} (xss : Family) {yss : Family}
    → Holds A yss → Holds A (xss ++ yss)
  right [] p = p
  right (_ ∷ xss) p = there (right xss p)

  split : {A : X → Set} (xss yss : Family)
    → Holds A (xss ++ yss) → Sum (Holds A xss) (Holds A yss)
  split [] yss p = inr p
  split (_ ∷ xss) yss (here p) = inl (here p)
  split (_ ∷ xss) yss (there p) with split xss yss p
  ... | inl q = inl (there q)
  ... | inr q = inr q

  prefix-in : {A : X → Set} (xs : List X) {yss : Family}
    → All A xs → Holds A yss → Holds A (prefix xs yss)
  prefix-in xs px (here {x = ys} py) = here (all-join xs ys px py)
  prefix-in xs px (there py) = there (prefix-in xs px py)

  prefix-out : {A : X → Set} (xs : List X) (yss : Family)
    → Holds A (prefix xs yss) → Σ (All A xs) (λ _ → Holds A yss)
  prefix-out xs (ys ∷ yss) (here p) with all-split xs ys p
  ... | q , r = q , here r
  prefix-out xs (ys ∷ yss) (there p) with prefix-out xs yss p
  ... | q , r = q , there r

  tensor-in : {A : X → Set} {xss yss : Family}
    → Holds A xss → Holds A yss → Holds A (tensor xss yss)
  tensor-in (here {x = xs} px) py = left (prefix-in xs px py)
  tensor-in {yss = yss} (there {x = xs} px) py =
    right (prefix xs yss) (tensor-in px py)

  tensor-out : {A : X → Set} (xss yss : Family)
    → Holds A (tensor xss yss) → Σ (Holds A xss) (λ _ → Holds A yss)
  tensor-out (xs ∷ xss) yss p with split (prefix xs yss) (tensor xss yss) p
  ... | inl q with prefix-out xs yss q
  ...   | r , s = here r , s
  tensor-out (xs ∷ xss) yss p | inr q with tensor-out xss yss q
  ... | r , s = there r , s

  all-map : {A B : X → Set} → ((x : X) → A x → B x)
    → (xs : List X) → All A xs → All B xs
  all-map f [] p = tt
  all-map f (x ∷ xs) (p , ps) = f x p , all-map f xs ps

  monotone : {A B : X → Set} → ((x : X) → A x → B x)
    → {xss : Family} → Holds A xss → Holds B xss
  monotone f (here {x = xs} p) = here (all-map f xs p)
  monotone f (there p) = there (monotone f p)

  all-self : (xs : List X) → All (λ x → x ∈ xs) xs
  all-self [] = tt
  all-self (x ∷ xs) = first , all-map (λ y → later) xs (all-self xs)

  all-member : {A : X → Set} {x : X} {xs : List X}
    → All A xs → x ∈ xs → A x
  all-member (p , ps) first = p
  all-member (p , ps) (later q) = all-member ps q

  -- Extract an actual list of seeds, its inclusion in A, and a certificate
  -- that the same support family is satisfied by this finite predicate alone.
  finite-witness : {A : X → Set} {xss : Family} → Holds A xss
    → Σ (List X) (λ xs → Σ (All A xs) (λ _ → Holds (λ x → x ∈ xs) xss))
  finite-witness (here {x = xs} p) = xs , p , here (all-self xs)
  finite-witness (there p) with finite-witness p
  ... | xs , q , r = xs , q , there r

  decide-all : {A : X → Set} → ((x : X) → Dec (A x))
    → (xs : List X) → Dec (All A xs)
  decide-all dec [] = yes tt
  decide-all dec (x ∷ xs) with dec x
  ... | no p = no (λ q → p (fst q))
  ... | yes p with decide-all dec xs
  ...   | no q = no (λ r → q (snd r))
  ...   | yes q = yes (p , q)

  decide : {A : X → Set} → ((x : X) → Dec (A x))
    → (xss : Family) → Dec (Holds A xss)
  decide dec [] = no (λ ())
  decide dec (xs ∷ xss) with decide-all dec xs
  ... | yes p = yes (here p)
  ... | no p with decide dec xss
  ...   | yes q = yes (there q)
  ...   | no q = no λ { (here r) → p r ; (there r) → q r }

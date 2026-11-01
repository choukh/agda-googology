{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.WellOrder.SmallCover where

-- Constructive witness collection. This does NOT assert that the resulting
-- cover is distinguished without the explicitly required union theorem.
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Mahlo.Archive.Legacy.Universe.Predicates using (SmallPred)
import Mahlo.Archive.Legacy.WellOrder.Segments as Segments

module Collect (D : SmallPred → Set) where
  record Global (x : Nat) : Set₁ where
    constructor witness
    field
      carrier : SmallPred
      certified : D carrier
      contains : carrier x
  open Global

  module Cover (B : SmallPred) (included : (x : Nat) → B x → Global x) where
    Index : Set
    Index = Σ Nat B

    chosen : Index → SmallPred
    chosen (x , bx) = carrier (included x bx)

    chosen-certified : (i : Index) → D (chosen i)
    chosen-certified (x , bx) = certified (included x bx)

    C : SmallPred
    C y = Σ Index (λ i → chosen i y)

    covers : (x : Nat) → B x → C x
    covers x bx = (x , bx) , contains (included x bx)

    remains-global : (y : Nat) → C y → Global y
    remains-global y (i , yi) = witness (chosen i) (chosen-certified i) yi

    -- Exactly the two directions of the still-unproved ordinal-specific
    -- [Se98] Lemma 4.26. Segment union itself is proved in Segments.agda.
    module FromSegments (Valid : Nat → Set) (_<_ : Nat → Nat → Set) where
      module S = Segments.On Valid _<_

      certified-cover :
        ((A : SmallPred) → D A → S.Segment A Global)
        → ((A : SmallPred) → S.Segment A Global → D A)
        → D C
      certified-cover to-segment from-segment = from-segment C
        (S.union Index chosen Global (λ i → to-segment (chosen i) (chosen-certified i)))

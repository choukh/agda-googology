{-# OPTIONS --safe --without-K #-}
module Mahlo.WellOrder.Distinguished where

-- The segment formulation of Ag(A), followed by the induction consequence.
-- The actual Mahlo Valid, order, M(A), and tau_A are NOT instantiated here.
open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
import Mahlo.WellOrder.Accessible as Accessible
import Mahlo.WellOrder.Segments as Segments

module On (Valid : Nat → Set) (_<_ : Nat → Nat → Set) where
  module S = Segments.On Valid _<_

  module For {a m p : Level}
    (A : Nat → Set a) (M : Nat → Set m) (Pred : Nat → Nat → Set p) where
    module G = Accessible.Generate M Pred

    -- Segment already contains A subset Valid, so it includes that part
    -- of [Se98] Definition 4.18 without an extra duplicate conjunction.
    Distinguished : Set (a ⊔ m ⊔ p)
    Distinguished = S.Segment A G.Generated

    -- This is the direction of Remark 4.20 needed by the induction proof.
    -- It must be proved from the reference closure system, not assumed as
    -- an automatic consequence of Distinguished for arbitrary M and Pred.
    PredecessorComplete : Set (a ⊔ p)
    PredecessorComplete = (x : Nat) → A x → (y : Nat) → A y → y < x → Pred x y

    induction : Distinguished → PredecessorComplete
      → {q : Level} (Q : Nat → Set q)
      → ((x : Nat) → A x → ((y : Nat) → A y → y < x → Q y) → Q x)
      → (x : Nat) → A x → Q x
    induction distinguished pred-complete Q progressive x ax =
      G.least (λ y → A y → Q y)
        (λ y my ih ay → progressive y ay
          (λ z az lt → ih z (pred-complete y ay z az lt) az))
        x (S.Segment.included distinguished x ax) ax

    -- Accessibility of the order restricted to members of A. This does
    -- not assert that every natural-number code lies in A or is accessible.
    module Restricted = Accessible.Generate (λ _ → ⊤)
      (λ x y → Σ (A y) (λ _ → y < x))

    accessible : Distinguished → PredecessorComplete
      → (x : Nat) → A x → Restricted.Generated x
    accessible distinguished pred-complete =
      induction distinguished pred-complete Restricted.Generated
        (λ x ax ih → Restricted.step tt (λ y edge → ih y (fst edge) (snd edge)))

  -- Instantiate M and tau by [Se98] Definition 4.5. Closure x y stands
  -- for y in C^x(A); the actual finite closure algorithm remains to be built.
  module FromClosure {a c : Level} (A : Nat → Set a)
    (Closure : Nat → Nat → Set c)
    (seed : (x y : Nat) → A y → y < x → Closure x y) where

    M : Nat → Set c
    M x = Σ (Valid x) (λ _ → Closure x x)

    Tau : Nat → Nat → Set c
    Tau x y = Σ (Closure x y) (λ _ → y < x)

    module D = For A M Tau
    open D using (Distinguished)

    predecessor-complete : D.PredecessorComplete
    predecessor-complete x ax y ay lt = seed x y ay lt , lt

    -- Together with predecessor-complete, this proves the two membership
    -- implications in tau_A(x) = A intersect x, for x in distinguished A.
    predecessor-contained : Distinguished → (x : Nat) → A x
      → (y : Nat) → Tau x y → A y
    predecessor-contained distinguished x ax y edge =
      S.Segment.initial distinguished x ax y
        (D.G.predecessor (S.Segment.included distinguished x ax) edge) (snd edge)

    induction : Distinguished → {q : Level} (Q : Nat → Set q)
      → ((x : Nat) → A x → ((y : Nat) → A y → y < x → Q y) → Q x)
      → (x : Nat) → A x → Q x
    induction distinguished = D.induction distinguished predecessor-complete

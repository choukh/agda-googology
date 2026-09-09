{-# OPTIONS --safe --without-K #-}
module Mahlo.Notation.Reference where

-- Executable candidate based on Setzer 3.3, 3.5, 3.6. Resource-bounded for
-- now: nothing means exhaustion, NEVER false or equality. Adequacy of the
-- automatic budget and correspondence to the reference remain unproved.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.List using (List; []; _∷_)
open import Mahlo.Notation.Syntax
open import Mahlo.Notation.FiniteSupport using (Dec; yes; no; _++_)

infixr 5 _and_
infixr 4 _or_
_and_ : Maybe Bool → Maybe Bool → Maybe Bool
just false and _ = just false
just true and y = y
nothing and just false = just false
nothing and _ = nothing

_or_ : Maybe Bool → Maybe Bool → Maybe Bool
just true or _ = just true
just false or y = y
nothing or just true = just true
nothing or _ = nothing

neg : Maybe Bool → Maybe Bool
neg (just true) = just false
neg (just false) = just true
neg nothing = nothing

accepted : {P : Set} → Dec P → Bool
accepted (yes _) = true
accepted (no _) = false

equal : Term → Term → Bool
equal a b = accepted (term≟ a b)

join : Maybe (List Term) → Maybe (List Term) → Maybe (List Term)
join (just xs) (just ys) = just (xs ++ ys)
join _ _ = nothing

all : (Term → Maybe Bool) → List Term → Maybe Bool
all f [] = just true
all f (x ∷ xs) = f x and all f xs

any : (Term → Maybe Bool) → List Term → Maybe Bool
any f [] = just false
any f (x ∷ xs) = f x or any f xs

all? : (Term → Maybe Bool) → Maybe (List Term) → Maybe Bool
all? f nothing = nothing
all? f (just xs) = all f xs

any? : (Term → Maybe Bool) → Maybe (List Term) → Maybe Bool
any? f nothing = nothing
any? f (just xs) = any f xs

mutual
  lt : Nat → Term → Term → Maybe Bool
  lt zero a b = nothing
  lt (suc n) a b with equal a b
  ... | true = just false
  ... | false = ltBody n a b

  ltBody : Nat → Term → Term → Maybe Bool
  ltBody zero a b = nothing
  ltBody (suc n) nil nil = just false
  ltBody (suc n) nil (cons q qs) = just true
  ltBody (suc n) (cons p ps) nil = just false
  ltBody (suc n) (cons p nil) (cons q nil) = ltP n p q
  ltBody (suc n) (cons p nil) (cons q (cons r rs)) with accepted (principal≟ p q)
  ... | true = just true
  ... | false = ltP n p q
  ltBody (suc n) (cons p (cons r rs)) (cons q nil) with accepted (principal≟ p q)
  ... | true = just false
  ... | false = ltP n p q
  ltBody (suc n) (cons p (cons r rs)) (cons q (cons s ss)) with accepted (principal≟ p q)
  ... | true = lt n (cons r rs) (cons s ss)
  ... | false = ltP n p q

  le : Nat → Term → Term → Maybe Bool
  le n a b with equal a b
  ... | true = just true
  ... | false = lt n a b

  ltP : Nat → Principal → Principal → Maybe Bool
  ltP zero p q = nothing
  ltP (suc n) (phi a b) (phi c d) =
    (lt n a c and lt n b (single (phi c d))) or
    (just (equal a c) and lt n b d) or
    (lt n c a and lt n (single (phi a b)) d)
  ltP (suc n) (phi a b) q = lt n a (single q) and lt n b (single q)
  ltP (suc n) p (phi a b) = neg (lt n a (single p) and lt n b (single p))
  ltP (suc n) (psi k a) (psi l b) =
    le n k (single (psi l b)) or
    any? (le n (single (psi k a))) (sc n l b) or
    (just (equal k l) and lt n a b and all? (λ x → lt n x (single (psi l b))) (sc n k a)) or
    (lt n (single (psi k a)) l and lt n l k and
      all? (λ x → lt n x (single (psi l b))) (sc n k a))
  ltP (suc n) (psi k a) (omega b) with isI k
  ... | true = le n (single (psi k a)) b
  ... | false = le n k (single (omega b))
  ltP (suc n) (psi k a) mahlo with isI k
  ... | true = just true
  ... | false = le n k (single mahlo)
  ltP (suc n) (omega a) (psi k b) = neg (ltP n (psi k b) (omega a))
  ltP (suc n) mahlo (psi k b) = neg (ltP n (psi k b) mahlo)
  ltP (suc n) (omega a) (omega b) = lt n a b
  ltP (suc n) (omega a) mahlo = lt n a (single mahlo)
  ltP (suc n) mahlo (omega a) = neg (lt n a (single mahlo))
  ltP (suc n) mahlo mahlo = just false

  SC : Nat → Term → Term → Maybe (List Term)
  SC zero k a = nothing
  SC (suc n) k nil = just []
  SC (suc n) k (cons p ps) = join (SCP n k p) (SC n k ps)

  SCP : Nat → Term → Principal → Maybe (List Term)
  SCP zero k p = nothing
  SCP (suc n) k mahlo = just []
  SCP (suc n) k (phi a b) = join (SC n k a) (SC n k b)
  SCP (suc n) k (omega a) = SC n k a
  SCP (suc n) k (psi l b) with lt n (single (psi l b)) k
  ... | nothing = nothing
  ... | just true = just (single (psi l b) ∷ [])
  ... | just false = join (SC n k l) (SC n k b)

  sc : Nat → Term → Term → Maybe (List Term)
  sc n k a with equal k (single mahlo)
  ... | true = SC n k a
  ... | false = just []

  G : Nat → Term → Term → Maybe (List Term)
  G zero k a = nothing
  G (suc n) k nil = just []
  G (suc n) k (cons p ps) = join (GP n k p) (G n k ps)

  GP : Nat → Term → Principal → Maybe (List Term)
  GP zero k p = nothing
  GP (suc n) k mahlo = just []
  GP (suc n) k (phi a b) = join (G n k a) (G n k b)
  GP (suc n) k (omega a) = G n k a
  -- Convention under audit: the non-below branch includes equality.
  -- The scanned Mahlo paper prints a strict condition in the final G case,
  -- leaving equality uncovered, although aux k b k needs it for psi indices.
  -- See UNIVERSE-AND-SEQUENCES.md; this is not certified source equivalence.
  GP (suc n) k (psi l b) with lt n (single (psi l b)) k
  ... | nothing = nothing
  ... | just true = just []
  ... | just false = join (join (G n k l) (G n k b)) (just (b ∷ []))

cr : Nat → Term → Term → Maybe Bool
cr n a (cons (phi b c) nil) = lt n a b
cr n a (cons (psi k b) nil) = lt n a (single (psi k b))
cr n a (cons (omega b) nil) = lt n a (single (omega b))
cr n a (cons mahlo nil) = lt n a (single mahlo)
cr n a _ = just false

aux : Nat → Term → Term → Term → Maybe Bool
aux n k b c = all? (λ x → lt n x (single (psi k b))) (SC n k c)
  and all? (λ x → lt n x b) (G n k c)

mutual
  ot : Nat → Term → Maybe Bool
  ot zero a = nothing
  ot (suc n) nil = just true
  ot (suc n) (cons p nil) = otP n p
  ot (suc n) (cons p (cons q qs)) = otP n p and ot n (cons q qs)
    and le n (single q) (single p)

  otP : Nat → Principal → Maybe Bool
  otP zero p = nothing
  otP (suc n) mahlo = just true
  otP (suc n) (phi a b) = ot n a and ot n b and neg (cr n a b)
    and neg (just (equal b nil) and just (isG a))
  otP (suc n) (omega a) = ot n a and neg (just (isFi a)) and neg (just (equal a nil))
  otP (suc n) (psi k b) = ot n k and ot n b and just (isRegular k)
    and aux n k b k and aux n k b b

mutual
  size : Term → Nat
  size nil = 1
  size (cons p ps) = suc (sizeP p + size ps)

  sizeP : Principal → Nat
  sizeP mahlo = 1
  sizeP (phi a b) = suc (size a + size b)
  sizeP (psi a b) = suc (size a + size b)
  sizeP (omega a) = suc (size a)

-- A practical initial budget, NOT a proved recursion-depth bound.
budget : Term → Term → Nat
budget a b = 32 * (size a + size b)

less : Term → Term → Maybe Bool
less a b with accepted (raw? a) | accepted (raw? b)
... | true | true with equal a b
...   | true = just false
...   | false = lt (budget a b) a b
less a b | _ | _ = just false

validOT : Term → Maybe Bool
validOT a = ot (budget a a) a

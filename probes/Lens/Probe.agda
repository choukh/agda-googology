{-# OPTIONS --cubical --no-import-sorts #-}
module Probe where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; lzero; lsuc; Set; Setω)
open import Agda.Builtin.Cubical.Path using (_≡_)

refl : {a : Level} {A : Set a} {x : A} → x ≡ x
refl {x = x} = λ _ → x

-- function extensionality is a *theorem* in cubical, not a postulate
funExt : {a b : Level} {A : Set a} {B : A → Set b} {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g
funExt p i x = p x i

----------------------------------------------------------------------
-- 1. Church-encoded Brouwer ordinals
----------------------------------------------------------------------

Ord : Set₁
Ord = (X : Set) → X → (X → X) → ((Nat → X) → X) → X

iter : {X : Set} → (X → X) → Nat → X → X
iter f zero    x = x
iter f (suc n) x = f (iter f n x)

o0 : Ord
o0 X z s l = z

osuc : Ord → Ord
osuc a X z s l = s (a X z s l)

-- t_n
onat : Nat → Ord
onat zero    = o0
onat (suc n) = osuc (onat n)

-- t_omega  =  l (n |-> I s n z)
oomega : Ord
oomega X z s l = l (λ n → iter s n z)

----------------------------------------------------------------------
-- 2. THE FGH ALGEBRA:  Omega-algebra structure on  F = Nat -> Nat
----------------------------------------------------------------------

Fn : Set
Fn = Nat → Nat

zF : Fn
zF = suc

sF : Fn → Fn
sF g n = iter g n n

lF : (Nat → Fn) → Fn
lF G n = G n n

F[_] : Ord → Fn
F[ a ] = a Fn zF sF lF

----------------------------------------------------------------------
-- 2a. sanity: the fast-growing hierarchy comes out right
----------------------------------------------------------------------

_ : F[ o0 ] ≡ suc
_ = refl

_ : F[ onat 1 ] 3 ≡ 6            -- F_1 n = 2n
_ = refl

_ : F[ onat 1 ] 5 ≡ 10
_ = refl

_ : F[ onat 2 ] 3 ≡ 24           -- F_2 n = 2^n * n
_ = refl

_ : F[ onat 2 ] 2 ≡ 8
_ = refl

_ : F[ oomega ] 2 ≡ 8            -- F_omega n = F_n n
_ = refl

_ : F[ oomega ] 1 ≡ 2
_ = refl

-- F_1 = \n. n+n  pointwise, then upgraded to a function equality by funExt
lem-iter-suc : (n m : Nat) → iter suc n m ≡ n + m
lem-iter-suc zero    m = refl
lem-iter-suc (suc n) m i = suc (lem-iter-suc n m i)

F1-pointwise : (n : Nat) → F[ onat 1 ] n ≡ n + n
F1-pointwise n = lem-iter-suc n n

F1-funext : F[ onat 1 ] ≡ (λ n → n + n)
F1-funext = funExt F1-pointwise

----------------------------------------------------------------------
-- 3. Lenses
----------------------------------------------------------------------

record Lens : Set₁ where
  field
    Fm : Set → Set
    Zt : {X : Set} → X → (X → X) → ((Nat → X) → X) → Fm X
    St : {X : Set} → X → (X → X) → ((Nat → X) → X) → Fm X → Fm X
    Lt : {X : Set} → X → (X → X) → ((Nat → X) → X) → (Nat → Fm X) → Fm X
    Dn : {X : Set} → X → (X → X) → ((Nat → X) → X) → Fm X → X
open Lens

-- the implementation relation, as a definition
app : Lens → Ord → Ord
app t a X z s l = Dn t z s l (a (Fm t X) (Zt t z s l) (St t z s l) (Lt t z s l))

-- identity lens
idLens : Lens
Fm idLens X     = X
Zt idLens z s l = z
St idLens z s l = λ x → s x
Lt idLens z s l = λ g → l g
Dn idLens z s l = λ x → x

-- Gentzen / Archimedes lens :  a |-> omega^a
gentzen : Lens
Fm gentzen X       = X → X
Zt gentzen z s l   = s
St gentzen z s l f = λ x → l (λ n → iter f n x)
Lt gentzen z s l g = λ x → l (λ n → g n x)
Dn gentzen z s l f = f z

-- composition of lenses (MGS'08 Example 3)
comp : Lens → Lens → Lens
Fm (comp t1 t2) X       = Fm t1 (Fm t2 X)
Zt (comp t1 t2) z s l   = Zt t1 (Zt t2 z s l) (St t2 z s l) (Lt t2 z s l)
St (comp t1 t2) z s l   = St t1 (Zt t2 z s l) (St t2 z s l) (Lt t2 z s l)
Lt (comp t1 t2) z s l   = Lt t1 (Zt t2 z s l) (St t2 z s l) (Lt t2 z s l)
Dn (comp t1 t2) z s l   = λ u → Dn t2 z s l (Dn t1 (Zt t2 z s l) (St t2 z s l) (Lt t2 z s l) u)

----------------------------------------------------------------------
-- 4. THE CRUCIAL TESTS:  does the Gentzen lens implement  a |-> omega^a
--    up to DEFINITIONAL equality (refl), or do we need paths?
----------------------------------------------------------------------

pow : Ord → Ord
pow = app gentzen

-- omega^0 = 1 , as Church terms, definitionally
test-pow0 : pow o0 ≡ onat 1
test-pow0 = refl

-- omega^1 = omega , as Church terms, definitionally
test-pow1 : pow (onat 1) ≡ oomega
test-pow1 = refl

-- and hence on the FGH side, for free
test-fgh-pow1 : F[ pow (onat 1) ] ≡ F[ oomega ]
test-fgh-pow1 = refl

_ : F[ pow (onat 1) ] 2 ≡ 8
_ = refl

-- PROP 2 : composition of lenses implements composition of functions
test-prop2 : (a : Ord) → app (comp gentzen gentzen) a ≡ pow (pow a)
test-prop2 a = refl

-- identity lens is the identity
test-id : (a : Ord) → app idLens a ≡ a
test-id a = refl

----------------------------------------------------------------------
-- 5. THE OPEN PROBLEM: limit of a sequence of lenses.
--    Candidate:  Fm X = (n : Nat) -> Fm (t n) X ,  Dn takes a sup via l.
----------------------------------------------------------------------

limLens : (Nat → Lens) → Lens
Fm (limLens t) X     = (n : Nat) → Fm (t n) X
Zt (limLens t) z s l = λ n → Zt (t n) z s l
St (limLens t) z s l = λ u n → St (t n) z s l (u n)
Lt (limLens t) z s l = λ G n → Lt (t n) z s l (λ k → G k n)
Dn (limLens t) z s l = λ u → l (λ n → Dn (t n) z s l (u n))

-- the n-fold Gentzen lens implements  a |-> omega^omega^...^a  (n times)
powN : Nat → Lens
powN zero    = idLens
powN (suc n) = comp gentzen (powN n)

-- tower n = omega^omega^...^0
tower : Nat → Ord
tower n = app (powN n) o0

-- the sup of the towers, written by hand
eps0-byhand : Ord
eps0-byhand X z s l = l (λ n → tower n X z s l)

-- the limit lens applied to 0
eps0-bylens : Ord
eps0-bylens = app (limLens powN) o0

-- DOES THE CANDIDATE LIMIT LENS PRODUCE EPSILON_0 DEFINITIONALLY?
test-limit : eps0-bylens ≡ eps0-byhand
test-limit = refl

-- and it lands in FGH
Feps0 : Fn
Feps0 = F[ eps0-bylens ]

_ : Feps0 0 ≡ 1
_ = refl

_ : Feps0 1 ≡ 2
_ = refl

_ : Feps0 2 ≡ 8
_ = refl

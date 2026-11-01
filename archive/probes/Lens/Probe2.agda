{-# OPTIONS --cubical --no-import-sorts #-}
module Probe2 where

open import Probe
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; lzero; lsuc; Set)
open import Agda.Builtin.Cubical.Path using (_≡_)
open Lens

----------------------------------------------------------------------
-- 6. limits of Church ordinals, and NORMALITY of a lens
----------------------------------------------------------------------

olim : (Nat → Ord) → Ord
olim f X z s l = l (λ n → f n X z s l)

-- Is the Gentzen lens continuous at limits, definitionally?
gentzen-normal : (f : Nat → Ord)
               → app gentzen (olim f) ≡ olim (λ n → app gentzen (f n))
gentzen-normal f = refl

-- Does that hold for *every* lens, definitionally?  (expected: NO)
-- any-lens-normal : (t : Lens) (f : Nat → Ord)
--                 → app t (olim f) ≡ olim (λ n → app t (f n))
-- any-lens-normal t f = refl

----------------------------------------------------------------------
-- 7. THE DERIVATIVE OPERATOR ON LENSES
--    deriv t = limit of the sequence  id, t, t.t, t.t.t, ...
--    i.e. b |-> sup_n (phi^n b)  =  enumerate fixed points of phi
----------------------------------------------------------------------

powLens : Lens → Nat → Lens
powLens t zero    = idLens
powLens t (suc n) = comp t (powLens t n)

deriv : Lens → Lens
deriv t = limLens (powLens t)

-- deriv gentzen should be exactly the epsilon-lens we built by hand
tower' : Nat → Ord
tower' n = app (powLens gentzen n) o0

eps0-byhand' : Ord
eps0-byhand' = olim tower'

test-deriv-is-eps : app (deriv gentzen) o0 ≡ eps0-byhand'
test-deriv-is-eps = refl

-- NOTE: the same statement against Probe.powN (an extensionally identical
-- but syntactically distinct sequence) is NOT refl.  Recorded as a finding.

----------------------------------------------------------------------
-- 8. THE VEBLEN LADDER, built entirely from Gentzen + deriv
----------------------------------------------------------------------

veblen : Nat → Lens
veblen zero    = gentzen              -- phi_0 : a |-> omega^a
veblen (suc n) = deriv (veblen n)     -- phi_{n+1} = derivative of phi_n

-- phi_n(0)
phi : Nat → Ord
phi n = app (veblen n) o0

eps0 : Ord
eps0 = phi 1

zeta0 : Ord
zeta0 = phi 2

-- Gamma_0 = sup_n phi_n(0) : the ceiling of the no-W-type universe ladder
Gamma0 : Ord
Gamma0 = olim phi

-- ... and as a *lens*, so it can be iterated further
GammaLens : Lens
GammaLens = limLens veblen

test-Gamma-agrees : app GammaLens o0 ≡ Gamma0
test-Gamma-agrees = refl

----------------------------------------------------------------------
-- 9. FEEDING THEM TO THE FAST-GROWING HIERARCHY
----------------------------------------------------------------------

Feps0b : Nat → Nat
Feps0b = F[ eps0 ]

Fzeta0 : Nat → Nat
Fzeta0 = F[ zeta0 ]

FGamma0 : Nat → Nat
FGamma0 = F[ Gamma0 ]

-- these must all COMPUTE.  Small inputs only; they explode instantly.
_ : Feps0b 1 ≡ 2
_ = refl

_ : Feps0b 2 ≡ 8
_ = refl

_ : Fzeta0 1 ≡ 2
_ = refl

_ : FGamma0 1 ≡ 2
_ = refl

_ : FGamma0 0 ≡ 0
_ = refl

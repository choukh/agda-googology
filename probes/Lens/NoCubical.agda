{-# OPTIONS --safe --without-K --no-import-sorts #-}
-- Universe-polymorphic rebuild.
-- The point: the type of LENSES itself carries an Omega-algebra
-- (gentzen , deriv , limLens), so a Church ordinal can be run over it.
-- Running a Church ordinal over  Lens l  costs exactly one universe level.
module NoCubical where

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_; Set)
open import Agda.Builtin.Equality using (_≡_) renaming (refl to rfl)

refl : {a : Level} {A : Set a} {x : A} → x ≡ x
refl = rfl


iter : {a : Level} {X : Set a} → (X → X) → Nat → X → X
iter f zero    x = x
iter f (suc n) x = f (iter f n x)

----------------------------------------------------------------------
-- Church ordinals at every universe level
----------------------------------------------------------------------

Ord : (ℓ : Level) → Set (lsuc ℓ)
Ord ℓ = (X : Set ℓ) → X → (X → X) → ((Nat → X) → X) → X

o0 : {ℓ : Level} → Ord ℓ
o0 X z s l = z

osuc : {ℓ : Level} → Ord ℓ → Ord ℓ
osuc a X z s l = s (a X z s l)

onat : {ℓ : Level} → Nat → Ord ℓ
onat zero    = o0
onat (suc n) = osuc (onat n)

olim : {ℓ : Level} → (Nat → Ord ℓ) → Ord ℓ
olim f X z s l = l (λ n → f n X z s l)

oomega : {ℓ : Level} → Ord ℓ
oomega = olim onat

----------------------------------------------------------------------
-- The FGH algebra, at level 0
----------------------------------------------------------------------

Fn : Set
Fn = Nat → Nat

zF : Fn
zF = suc

sF : Fn → Fn
sF g n = iter g n n

lF : (Nat → Fn) → Fn
lF G n = G n n

F[_] : Ord lzero → Fn
F[ a ] = a Fn zF sF lF

----------------------------------------------------------------------
-- Lenses, level-polymorphically
----------------------------------------------------------------------

record Lens (ℓ : Level) : Set (lsuc ℓ) where
  field
    Fm : Set ℓ → Set ℓ
    Zt : {X : Set ℓ} → X → (X → X) → ((Nat → X) → X) → Fm X
    St : {X : Set ℓ} → X → (X → X) → ((Nat → X) → X) → Fm X → Fm X
    Lt : {X : Set ℓ} → X → (X → X) → ((Nat → X) → X) → (Nat → Fm X) → Fm X
    Dn : {X : Set ℓ} → X → (X → X) → ((Nat → X) → X) → Fm X → X
open Lens

app : {ℓ : Level} → Lens ℓ → Ord ℓ → Ord ℓ
app t a X z s l = Dn t z s l (a (Fm t X) (Zt t z s l) (St t z s l) (Lt t z s l))

idLens : {ℓ : Level} → Lens ℓ
Fm idLens X     = X
Zt idLens z s l = z
St idLens z s l = λ x → s x
Lt idLens z s l = λ g → l g
Dn idLens z s l = λ x → x

gentzen : {ℓ : Level} → Lens ℓ                       -- a |-> omega^a
Fm gentzen X       = X → X
Zt gentzen z s l   = s
St gentzen z s l f = λ x → l (λ n → iter f n x)
Lt gentzen z s l g = λ x → l (λ n → g n x)
Dn gentzen z s l f = f z

comp : {ℓ : Level} → Lens ℓ → Lens ℓ → Lens ℓ
Fm (comp t u) X     = Fm t (Fm u X)
Zt (comp t u) z s l = Zt t (Zt u z s l) (St u z s l) (Lt u z s l)
St (comp t u) z s l = St t (Zt u z s l) (St u z s l) (Lt u z s l)
Lt (comp t u) z s l = Lt t (Zt u z s l) (St u z s l) (Lt u z s l)
Dn (comp t u) z s l = λ v → Dn u z s l (Dn t (Zt u z s l) (St u z s l) (Lt u z s l) v)

-- the candidate limit construction.  Fm needs  Nat -> Lens  to be a
-- genuine function into Set: that is large elimination, i.e. a universe.
limLens : {ℓ : Level} → (Nat → Lens ℓ) → Lens ℓ
Fm (limLens t) X     = (n : Nat) → Fm (t n) X
Zt (limLens t) z s l = λ n → Zt (t n) z s l
St (limLens t) z s l = λ u n → St (t n) z s l (u n)
Lt (limLens t) z s l = λ G n → Lt (t n) z s l (λ k → G k n)
Dn (limLens t) z s l = λ u → l (λ n → Dn (t n) z s l (u n))

powLens : {ℓ : Level} → Lens ℓ → Nat → Lens ℓ
powLens t zero    = idLens
powLens t (suc n) = comp t (powLens t n)

deriv : {ℓ : Level} → Lens ℓ → Lens ℓ
deriv t = limLens (powLens t)

----------------------------------------------------------------------
-- *** THE OMEGA-ALGEBRA ON THE TYPE OF LENSES ***
--   zero      = gentzen    (phi_0 = omega^.)
--   successor = deriv      (phi_{a+1} = derivative of phi_a)
--   limit     = limLens    (phi_lambda = limit)
-- Running a Church ordinal over it is EXACTLY one universe step.
----------------------------------------------------------------------

veblenLens : {ℓ : Level} → Ord (lsuc ℓ) → Lens ℓ
veblenLens a = a (Lens _) gentzen deriv limLens

-- Theta a = phi_a (0)
Θ : {ℓ : Level} → Ord (lsuc ℓ) → Ord ℓ
Θ a = app (veblenLens a) o0

----------------------------------------------------------------------
-- checks
----------------------------------------------------------------------

eps0 : {ℓ : Level} → Ord ℓ
eps0 = app (deriv gentzen) o0

-- phi_0(0) = omega^0 = 1
_ : Θ {lzero} o0 ≡ onat 1
_ = refl

-- phi_1(0) = epsilon_0
_ : Θ {lzero} (onat 1) ≡ eps0
_ = refl

-- phi_omega(0) = Gamma_0
Gamma0 : {ℓ : Level} → Ord ℓ
Gamma0 = Θ oomega

_ : Θ {lzero} oomega ≡ olim (λ n → Θ (onat n))
_ = refl

----------------------------------------------------------------------
-- *** HANCOCK'S UNIVERSE LADDER ***
--   Theta_0 = eps0 ,  Theta_{n+1} = Theta(Theta_n) = phi_{Theta_n}(0)
-- Each nesting of Theta consumes one universe level.
----------------------------------------------------------------------

Θ₀ : {ℓ : Level} → Ord ℓ
Θ₀ = eps0

Θ₁ : {ℓ : Level} → Ord ℓ                -- MLTT + 1 universe
Θ₁ = Θ Θ₀

Θ₂ : {ℓ : Level} → Ord ℓ                -- MLTT + 2 universes
Θ₂ = Θ Θ₁

Θ₃ : {ℓ : Level} → Ord ℓ
Θ₃ = Θ Θ₂

----------------------------------------------------------------------
-- and finally: the numbers
----------------------------------------------------------------------

FΘ₀ FΘ₁ FΘ₂ FΓ : Fn
FΘ₀ = F[ Θ₀ ]
FΘ₁ = F[ Θ₁ ]
FΘ₂ = F[ Θ₂ ]
FΓ  = F[ Gamma0 ]

_ : FΘ₀ 1 ≡ 2
_ = refl

_ : FΘ₀ 2 ≡ 8
_ = refl

_ : FΘ₁ 1 ≡ 2
_ = refl

_ : FΘ₂ 1 ≡ 2
_ = refl

_ : FΓ 1 ≡ 2
_ = refl

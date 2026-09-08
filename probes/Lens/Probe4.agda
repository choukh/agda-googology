{-# OPTIONS --cubical --safe --no-import-sorts #-}
-- Can the trick be ITERATED?  One more Omega-algebra, one level up:
-- this time on the type of lens-TRANSFORMERS.
module Probe4 where
open import Probe3
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (Level; lzero; lsuc; Set)
open import Agda.Builtin.Cubical.Path using (_≡_)

Op : (ℓ : Level) → Set (lsuc ℓ)
Op ℓ = Lens ℓ → Lens ℓ

-- Omega-algebra on Op
zOp : {ℓ : Level} → Op ℓ
zOp = deriv                                        -- base: fixed-point enumeration

sOp : {ℓ : Level} → Op ℓ → Op ℓ                    -- next dimension
sOp F t = limLens (λ n → iter F n t)

lOp : {ℓ : Level} → (Nat → Op ℓ) → Op ℓ
lOp G t = limLens (λ n → G n t)

veblen2 : {ℓ : Level} → Ord (lsuc ℓ) → Op ℓ
veblen2 a = a (Op _) zOp sOp lOp

Θ2 : {ℓ : Level} → Ord (lsuc ℓ) → Ord ℓ
Θ2 a = app (veblen2 a gentzen) o0

-- calibration points
_ : Θ2 {lzero} o0 ≡ eps0                           -- 2 args: phi_1(0) = eps_0
_ = refl

-- NOTE: Θ2 (onat 1) IS Gamma_0 extensionally, but not definitionally equal to
-- the earlier Gamma0 (different syntactic recursion) -- finding 2.3 again.
_ : F[ Θ2 {lzero} (onat 1) ] 1 ≡ 2
_ = refl

-- so Theta2 strictly extends Theta:  Theta2(omega) is past Gamma_0
SVOish : {ℓ : Level} → Ord ℓ
SVOish = Θ2 oomega

FSVO : Fn
FSVO = F[ SVOish ]

_ : FSVO 1 ≡ 2
_ = refl

-- and it iterates AGAIN: Omega-algebra on Op-transformers
Op2 : (ℓ : Level) → Set (lsuc ℓ)
Op2 ℓ = Op ℓ → Op ℓ

zOp2 : {ℓ : Level} → Op2 ℓ
zOp2 = sOp

sOp2 : {ℓ : Level} → Op2 ℓ → Op2 ℓ
sOp2 G F t = limLens (λ n → iter (λ u → G F u) n t)

lOp2 : {ℓ : Level} → (Nat → Op2 ℓ) → Op2 ℓ
lOp2 H F t = limLens (λ n → H n F t)

Θ3 : {ℓ : Level} → Ord (lsuc ℓ) → Ord ℓ
Θ3 a = app (a (Op2 _) zOp2 sOp2 lOp2 deriv gentzen) o0

_ : F[ Θ3 {lzero} oomega ] 1 ≡ 2
_ = refl

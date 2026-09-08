{-# OPTIONS --cubical --safe --no-import-sorts #-}
module Bad where
open import Probe3
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Primitive using (lzero)
open import Agda.Builtin.Cubical.Path using (_≡_)

-- a perfectly legal Brouwer tree whose "fundamental sequence" is constant 0
bad1 : Ord lzero
bad1 = olim (λ n → o0)

-- another: constant 1
bad2 : Ord lzero
bad2 = olim (λ n → onat 1)

-- both are limit-shaped terms.  Both type-check.  Both terminate.
_ : F[ bad1 ] 5 ≡ 6          -- ... and grow exactly like F_0
_ = refl

_ : F[ bad1 ] 100 ≡ 101
_ = refl

_ : F[ bad2 ] 5 ≡ 10         -- ... and like F_1
_ = refl

-- non-monotone: alternates between 0 and 2
alt : Nat → Ord lzero
alt zero          = onat 2
alt (suc zero)    = o0
alt (suc (suc n)) = alt n

bad3 : Ord lzero
bad3 = olim alt

_ : F[ bad3 ] 7 ≡ 8          -- odd input -> falls to F_0
_ = refl

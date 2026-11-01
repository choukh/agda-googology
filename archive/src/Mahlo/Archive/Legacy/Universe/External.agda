{-# OPTIONS --safe --without-K #-}
-- Archived probe; not an implementation of universe-to-fundamental-sequence extraction.
module Mahlo.Archive.Legacy.Universe.External where

-- Research checkpoint U1: external closure and a candidate host realization.
-- This is not a full interpretation of MLM or a Mahlo well-ordering proof.
-- Independently written from the parameterized induction-recursion construction:
-- https://csetzer.github.io/articles/mahlo.pdf (section 4; Definition 5.9)
-- https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf (section 2)
-- No import of the older MonomorphicSets helper, which defines K.

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.Equality using (_≡_; refl)

data Fin : Nat → Set where
  fzero : {n : Nat} → Fin (suc n)
  fsuc : {n : Nat} → Fin n → Fin (suc n)

data Sum (A B : Set) : Set where
  inl : A → Sum A B
  inr : B → Sum A B

data W (A : Set) (B : A → Set) : Set where
  sup : (a : A) → (B a → W A B) → W A B

Fam : Set₁
Fam = Σ Set (λ A → A → Set)

module Close (F : Fam → Fam) where
  mutual
    data U : Set where
      nat : U
      fin : Nat → U
      sum : U → U → U
      pi sigma w : (a : U) → (El a → U) → U
      eq : (a : U) → El a → El a → U
      res₀ : (a : U) → (El a → U) → U
      res₁ : (a : U) → (b : El a → U) → El (res₀ a b) → U

    El : U → Set
    El nat = Nat
    El (fin n) = Fin n
    El (sum a b) = Sum (El a) (El b)
    El (pi a b) = (x : El a) → El (b x)
    El (sigma a b) = Σ (El a) (λ x → El (b x))
    El (w a b) = W (El a) (λ x → El (b x))
    El (eq a x y) = x ≡ y
    El (res₀ a b) = fst (F (El a , λ x → El (b x)))
    El (res₁ a b x) = snd (F (El a , λ y → El (b y))) x

  SmallFam : Set
  SmallFam = Σ U (λ a → El a → U)

  decode : SmallFam → Fam
  decode (a , b) = El a , λ x → El (b x)

  restrict : SmallFam → SmallFam
  restrict (a , b) = res₀ a b , res₁ a b

  commute : (c : SmallFam) → decode (restrict c) ≡ F (decode c)
  commute (a , b) = refl

-- Russell realization of the Mahlo code sort, in the next host universe.
V : Set₁
V = Set
T : V → Set
T A = A
u : (F : Fam → Fam) → V
u F = Close.U F
s : (F : Fam → Fam) → T (u F) → V
s F = Close.El F
u-decode : (F : Fam → Fam) → T (u F) ≡ Close.U F
u-decode F = refl

-- Nonconstant operator; both components depend on the input family.
exampleOp : Fam → Fam
exampleOp (A , B) = Σ A B , λ p → B (fst p) → Nat

module Example where
  open Close exampleOp
  input : SmallFam
  input = nat , λ _ → fin (suc zero)
  index-equation : El (fst (restrict input)) ≡ Σ Nat (λ _ → Fin 1)
  index-equation = refl
  member-equation : (p : Σ Nat (λ _ → Fin 1)) →
    El (snd (restrict input) p) ≡ (Fin 1 → Nat)
  member-equation p = refl

-- Setzer Definition 5.9: recode a specified family using a constant operator.
-- This is a small instance of the closure rule, not Lemma 5.10.
module Recode (A : Set) (B : A → Set) where
  constantOp : Fam → Fam
  constantOp _ = A , B

  open Close constantOp

  codeA : U
  codeA = res₀ nat (λ _ → fin zero)

  codeB : A → U
  codeB = res₁ nat (λ _ → fin zero)

  decodeA : El codeA ≡ A
  decodeA = refl

  decodeB : (x : A) → El (codeB x) ≡ B x
  decodeB x = refl

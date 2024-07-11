module OCF.Strong where
open import Base public

data O (ℓ : Ord) (El : Ord → Set) : Set where
  zero : O ℓ El
  suc  : O ℓ El → O ℓ El
  lim  : (ℕ → O ℓ El) → O ℓ El
  Lim  : (ℓ′ : Ord) → (El ℓ′ → O ℓ El) → O ℓ El

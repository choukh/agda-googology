module OCF.Base where

open import Data.Unit
open import Data.Nat
open import Function using (_∘_)

data Ord : Set where
  zero : Ord
  suc : Ord → Ord
  lim : (ℕ → Ord) → Ord

ord : ℕ → Ord
ord zero = zero
ord (suc n) = suc (ord n)

ω = lim ord

module _ {X : Set} (cf : X → Set) where
  data Ordₓ : Set where
    zero : Ordₓ
    suc : Ordₓ → Ordₓ
    limω : (f : ℕ → Ordₓ) → Ordₓ
    limX : (x : X) (f : cf x → Ordₓ) → Ordₓ
    limΩ : (f : X → Ordₓ) → Ordₓ

  cfₓ : Ordₓ → Set
  cfₓ (limΩ _) = X
  cfₓ (limX x _) = cf x
  cfₓ _ = ⊤

mutual
  Ordω : ℕ → Set
  Ordω zero = Ord
  Ordω (suc n) = Ordₓ (cfω n)

  cfω : (n : ℕ) → Ordω n → Set
  cfω zero _ = ⊤
  cfω (suc n) = cfₓ (cfω n)

ord₁ : Ordω 0 → Ordω 1
ord₁ zero = zero
ord₁ (suc α) = suc (ord₁ α)
ord₁ (lim f) = limω (ord₁ ∘ f)

ord₊ : {n : ℕ} → Ordω (suc n) → Ordω (suc (suc n))
ord₊ zero = zero
ord₊ (suc a) = suc (ord₊ a)
ord₊ (limω f) = limω (ord₊ ∘ f)
ord₊ a@(limX _ f) = limX a (ord₊ ∘ f)
ord₊ a@(limΩ f) = limX a (ord₊ ∘ f)

Ω₁ : Ordω 1
Ω₁ = limΩ ord₁

mutual
  OrdΩ : Ord → Set
  OrdΩ zero = Ord
  OrdΩ (suc α) = Ordₓ (cfΩ α)
  OrdΩ (lim f) = ∀ n → OrdΩ (f n)

  cfΩ : (α : Ord) → OrdΩ α → Set
  cfΩ zero _ = ⊤
  cfΩ (suc α) = cfₓ (cfΩ α)
  cfΩ (lim _) _ = ⊤

ψ : (α : Ord) → OrdΩ α → Ord
ψ zero a = a
ψ (suc α) a = ψ α {!   !}
ψ (lim f) a = lim (λ n → ψ (f n) {! a n  !})

module ConstructorAnalysis where
  o₁ : Ordω 1 → Set
  o₁ (limX _ f) = ⊤                       -- dummy f : ⊤ → Ordω 1
  o₁ (limΩ f) = ⊤                         -- f : Ordω 0 → Ordω 1
  o₁ _ = ⊤

  o₂ : Ordω 2 → Set
  o₂ (limX zero f) = ⊤                    -- dummy f : ⊤ → Ordω 2
  o₂ (limX (suc _) f) = ⊤                 -- dummy f : ⊤ → Ordω 2
  o₂ (limX (limω _) f) = ⊤                -- dummy f : ⊤ → Ordω 2
  o₂ (limX (limX x _) f) = ⊤              -- dummy f : ⊤ → Ordω 2
  o₂ (limX (limΩ _) f) = ⊤                -- f : Ordω 0 → Ordω 2
  o₂ (limΩ f) = ⊤                         -- f : Ordω 1 → Ordω 2
  o₂ _ = ⊤

  o₃ : Ordω 3 → Set
  o₃ (limX zero f) = ⊤                    -- dummy f : ⊤ → Ordω 3
  o₃ (limX (suc _) f) = ⊤                 -- dummy f : ⊤ → Ordω 3
  o₃ (limX (limω _) f) = ⊤                -- dummy f : ⊤ → Ordω 3
  o₃ (limX (limX zero _) f) = ⊤           -- dummy f : ⊤ → Ordω 3
  o₃ (limX (limX (suc _) _) f) = ⊤        -- dummy f : ⊤ → Ordω 3
  o₃ (limX (limX (limω _) _) f) = ⊤       -- dummy f : ⊤ → Ordω 3
  o₃ (limX (limX (limX _ _) _) f) = ⊤     -- dummy f : ⊤ → Ordω 3
  o₃ (limX (limX (limΩ _) _) f) = ⊤       -- f : Ordω 0 → Ordω 3
  o₃ (limX (limΩ _) f) = ⊤                -- f : Ordω 1 → Ordω 3
  o₃ (limΩ f) = ⊤                         -- f : Ordω 2 → Ordω 3
  o₃ _ = ⊤

  o_ω+1 : OrdΩ (suc ω) → Set
  o_ω+1 (limX _ f) = ⊤                    -- dummy f : ⊤ → OrdΩ (suc ω)
  o_ω+1 (limΩ f) = ⊤                      -- f : OrdΩ ω → OrdΩ (suc ω)
  o_ω+1 _ = ⊤

  o_ω+2 : OrdΩ (suc (suc ω)) → Set
  o_ω+2 (limX zero f) = ⊤                 -- dummy f : ⊤ → OrdΩ (suc (suc ω))
  o_ω+2 (limX (suc _) f) = ⊤              -- dummy f : ⊤ → OrdΩ (suc (suc ω))
  o_ω+2 (limX (limω _) f) = ⊤             -- dummy f : ⊤ → OrdΩ (suc (suc ω))
  o_ω+2 (limX (limX _ _) f) = ⊤           -- dummy f : ⊤ → OrdΩ (suc (suc ω))
  o_ω+2 (limX (limΩ _) f) = ⊤             -- f : OrdΩ ω → OrdΩ (suc (suc ω))
  o_ω+2 (limΩ f) = ⊤                      -- f : OrdΩ (suc ω) → OrdΩ (suc (suc ω))
  o_ω+2 _ = ⊤

  o_ω+3 : OrdΩ (suc (suc (suc ω))) → Set
  o_ω+3 (limX zero f) = ⊤                 -- dummy f : ⊤ → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (suc _) f) = ⊤              -- dummy f : ⊤ → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (limω _) f) = ⊤             -- dummy f : ⊤ → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (limX zero _) f) = ⊤        -- dummy f : ⊤ → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (limX (suc _) _) f) = ⊤     -- dummy f : ⊤ → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (limX (limω _) _) f) = ⊤    -- dummy f : ⊤ → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (limX (limX _ _) _) f) = ⊤  -- dummy f : ⊤ → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (limX (limΩ _) _) f) = ⊤    -- f : OrdΩ ω → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limX (limΩ _) f) = ⊤             -- f : OrdΩ (suc ω) → OrdΩ (suc (suc (suc ω)))
  o_ω+3 (limΩ f) = ⊤                      -- f : OrdΩ (suc (suc ω)) → OrdΩ (suc (suc (suc ω)))
  o_ω+3 _ = ⊤

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module WellFormed.Madore where
```

```agda
import Cubical.Foundations.Prelude as 🧊
open import WellFormed.Base as Level public
  hiding (Level; Lift; wf; f; g; zero₁; suc₁; lim₁; isPropWf; limExtPath; limExt)
  renaming (Ord to Level; Road to _⊏_; _<_ to _⊏₁_)
```

```agda
data U (a : Level) (E : ∀ x → x ⊏ a → Type) : Type
data _<_ {a : Level} {E : ∀ x → x ⊏ a → Type} : U a E → U a E → Type; infix 6 _<_
```

```agda
variable
  x y : Level
  E : ∀ x → x ⊏ a → Type
  α β γ : U a E
  f g : ℕ → U a E
```

```agda
_<₁_ : U a E → U a E → Type; infix 6 _<₁_
a <₁ b = ∥ a < b ∥₁
```

```agda
wf : (ℕ → U a E) → Type
wf f = ∀ {n} → f n <₁ f (suc n)
```

```agda
data U a E where
  zero : U a E
  suc  : U a E → U a E
  lim  : (f : ℕ → U a E) → ⦃ wf f ⦄ → U a E
  Lim : (⊏a : x ⊏ a) → (E x ⊏a → U a E) → U a E
```

```agda
data _<_ {a} {E} where
  zero : α < suc α
  suc  : α < β → α < suc β
  lim  : ⦃ _ : wf f ⦄ → α < f n → α < lim f
  Lim  : {⊏a : x ⊏ a} {F : E x ⊏a → U a E} (ι : E x ⊏a) → α < F ι → α < Lim ⊏a F
```

```agda
pattern zero₁  = ∣ zero ∣₁
pattern suc₁ r = ∣ suc r ∣₁
pattern lim₁ r = ∣ lim r ∣₁
pattern Lim₁ r = ∣ Lim r ∣₁
```

```agda
Elm : ∀ x → x ⊏ a → Type
Elm x zero = U x Elm
Elm x (suc r) = Elm x r
Elm x (lim r) = Elm x r
```

```agda
Ord : Level → Type
Ord a = U a Elm
```

```agda
isPropWf : isProp (wf f)
isPropWf = isPropImplicitΠ λ _ → squash₁
  where open import Cubical.Foundations.HLevels
```

```agda
limExtPath : {wff : wf f} {wfg : wf g} → (∀ n → Path _ (f n) (g n)) → Path (U a E) (lim f ⦃ wff ⦄) (lim g ⦃ wfg ⦄)
limExtPath p = 🧊.cong₂ (λ f (wff : wf f) → U.lim f ⦃ wff ⦄) (funExt p) (toPathP $ isPropWf _ _)

limExt : {wff : wf f} {wfg : wf g} → (∀ n → f n ≡ g n) → lim f ⦃ wff ⦄ ≡ lim g ⦃ wfg ⦄
limExt p = pathToEq $ limExtPath $ eqToPath ∘ p
```

```agda
open import Lower public using (_∘ⁿ_)
finLvl : ℕ → Level
finLvl n = (suc ∘ⁿ n) zero
finOrd : ℕ → Ord a
finOrd n = (suc ∘ⁿ n) zero
```

```agda
open import Agda.Builtin.FromNat public
instance
  nNat : Number ℕ
  nNat = record { Constraint = λ _ → ⊤ ; fromNat = λ n → n }
  nLvl : Number Level
  nLvl = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finLvl n }
  nOrd : Number (Ord a)
  nOrd = record { Constraint = λ _ → ⊤ ; fromNat = λ n → finOrd n }
```

```agda
module OrdIso where
  open import Cubical.Foundations.Isomorphism
```

```agda
  to : Ord 0 → Level
  from< : α < β → to α ⊏ to β

  to zero = zero
  to (suc α) = suc (to α)
  to (lim f) = lim (to ∘ f) ⦃ map from< it ⦄
  
  from< zero = zero
  from< (suc r) = suc (from< r)
  from< (lim r) = lim ⦃ map from< it ⦄ (from< r)
```

```agda
  from : Level → Ord 0
  from⊏ : a ⊏ b → from a < from b

  from zero = zero
  from (suc a) = suc (from a)
  from (lim f) = lim (from ∘ f) ⦃ map from⊏ it ⦄

  from⊏ zero = zero
  from⊏ (suc r) = suc (from⊏ r)
  from⊏ (lim r) = lim ⦃ map from⊏ it ⦄ (from⊏ r)
```

```agda
  sec : section to from
  sec zero = 🧊.refl
  sec (suc a) = 🧊.cong suc (sec a)
  sec (lim f) = Level.limExtPath λ n → sec (f n)

  ret : retract to from
  ret zero = 🧊.refl
  ret (suc α) = 🧊.cong suc (ret α)
  ret (lim f) = limExtPath λ n → ret (f n)
```

```agda
  Ord0≡Level : Ord 0 ≡ Level
  Ord0≡Level = pathToEq $ isoToPath $ iso to from sec ret
```

```agda
Elm≡Ord : {⊏x : a ⊏ x} → Elm a ⊏x ≡ Ord a
Elm≡Ord {⊏x = zero} = refl
Elm≡Ord {⊏x = suc ⊏x} = Elm≡Ord {⊏x = ⊏x}
Elm≡Ord {⊏x = lim ⊏x} = Elm≡Ord {⊏x = ⊏x}
```

```agda
ord : {⊏x : a ⊏ x} → Elm a ⊏x → Ord a
ord {⊏x} α = subst id Elm≡Ord α

elm : {⊏x : a ⊏ x} → Ord a → Elm a ⊏x
elm α = subst id (sym Elm≡Ord) α
```

```agda
open import Relation.Binary.PropositionalEquality using (subst-sym-subst; subst-subst-sym)
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public

elm-ord : {⊏x : a ⊏ x} {α : Elm a ⊏x} → subst id (sym Elm≡Ord) (ord α) ≡ α
elm-ord = subst-sym-subst Elm≡Ord
{-# REWRITE elm-ord #-}

ord-elm : {⊏x : a ⊏ x} {α : Ord a} → subst id Elm≡Ord (elm {⊏x = ⊏x} α) ≡ α
ord-elm = subst-subst-sym Elm≡Ord
{-# REWRITE ord-elm #-}
```

```agda
swap : {⊏x : a ⊏ x} {⊏y : a ⊏ y} → Elm a ⊏x → Elm a ⊏y
swap α = elm (ord α)
```

```agda
Lift : a ⊏ b → Ord a → Ord b
Lift-pres : {p : a ⊏ b} → α < β → Lift p α < Lift p β

Lift ab zero = zero
Lift ab (suc α) = suc (Lift ab α)
Lift ab (lim f) = lim (Lift ab ∘ f) ⦃ map Lift-pres it ⦄
Lift ab (Lim xa F) = Lim (rd-trans xa ab) λ ι → Lift ab (F (swap ι))

Lift-pres zero = zero
Lift-pres (suc r) = suc (Lift-pres r)
Lift-pres (lim r) = lim ⦃ map Lift-pres it ⦄ (Lift-pres r)
Lift-pres (Lim {F} ι r) = Lim (swap ι) (Lift-pres (subst (_ <_) refl r))
```

```agda
Lift-trans : {p : a ⊏ b} {q : b ⊏ c} {r : a ⊏ c} → Lift q (Lift p α) ≡ Lift r α
Lift-trans {α = zero} = refl
Lift-trans {α = suc α} = cong suc Lift-trans
Lift-trans {α = lim f} = limExt λ _ → Lift-trans
Lift-trans {α = Lim ⊏a F} = {!   !}
```

```agda
ω : Ord 0
ω = lim finOrd ⦃ zero₁ ⦄

Ω : ∀ a → Ord a
Ω-pres : {ac : a ⊏ c} {bc : b ⊏ c} → a ⊏ b → Lift ac (Ω a) < Lift bc (Ω b)

Ω zero = ω
Ω (suc a) = Lim zero (Lift zero)
Ω (lim f) = lim (λ n → Lift f<l-rd (Ω (f n))) ⦃ map Ω-pres it ⦄

Ω-pres {a} {ac} zero = Lim (elm (suc (Ω a))) (subst (Lift ac (Ω a) <_) (sym Lift-trans) (Lift-pres zero))
Ω-pres (suc r) = {!   !}
Ω-pres (lim r) = lim ⦃ {!   !} ⦄ {!   !}
```

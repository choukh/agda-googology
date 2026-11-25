# YiXV YiXVCan2Core
> 验收文件。二层参照的带证据比较，每条比较携带两端好树； Ω₂ 的全部结点律已填。
> 按 YiOverOps/YiXVRef2Add 的证明扩展，仅二层参照域；源树γ₂与整链上界仍未证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVCan2Core where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRef2 as F
import OCF.Lean.YiXVCanTau as T

T₂ = F.T₂
one : T₂
one = L.suc L.zero

mutual
  data Gd : T₂ → Set
  data Le : T₂ → T₂ → Set
  data Step : T₂ → T₂ → Set

  record SC₀ (f : R.T₀ → T₂) : Set where
    inductive
    constructor sc₀
    field
      mo₀ : ∀ x y → R.𝟙 ≼ x → x ≼ y → Le (f x) (f y)
      db₀ : ∀ x → R.𝟙 ≼ x → Le (L.suc (f x)) (f (L.suc x))
      po₀ : Le one (f R.𝟙)

  record SC₁ (f : R.T₁ → T₂) : Set where
    inductive
    constructor sc₁
    field
      mo₁ : ∀ x y → O.Gd x → O.Gd y → O.Ω₁ R.≤ₚ x → x R.≤ₚ y → Le (f x) (f y)
      db₁ : ∀ x → O.Gd x → O.Ω₁ R.≤ₚ x → Le (L.suc (f x)) (f (L.suc x))
      po₁ : Le one (f O.Ω₁)

  data Gd where
    gz : Gd L.zero
    gs : ∀ {X} → Gd X → Gd (L.suc X)
    gl : ∀ {f} → (∀ n → Gd (f n)) → Gd (L.lim f)
    gn₀ : ∀ {f : R.T₀ → T₂} → SC₀ f → (∀ x → R.𝟙 ≼ x → Gd (f x)) → Gd (L.limᵢ (L.suc L.zero) f)
    gn₁ : ∀ {f : R.T₁ → T₂} → SC₁ f → (∀ x → O.Gd x → O.Ω₁ R.≤ₚ x → Gd (f x)) → Gd (L.limᵢ L.zero f)
    gu : ∀ {X : R.T₁} → O.Gd X → Gd (L.up L.zero X)

  data Le where
    pack : ∀ {X Y} → Gd X → Gd Y → Step X Y → Le X Y

  data Step where
    rr : ∀ {X} → Step X X
    zz : ∀ {Y} → Step L.zero Y
    ss : ∀ {X Y} → Le X Y → Step (L.suc X) (L.suc Y)
    ws : ∀ {X Y} → Le X Y → Step X (L.suc Y)
    ll : ∀ {f Y} → (∀ n → Le (f n) Y) → Step (L.lim f) Y
    lr : ∀ {X f} n → Le X (f n) → Step X (L.lim f)
    nn₀ : ∀ {f g : R.T₀ → T₂} → (∀ x y → R.𝟙 ≼ x → x ≼ y → Le (f x) (g y)) →
      Step (L.limᵢ (L.suc L.zero) f) (L.limᵢ (L.suc L.zero) g)
    nn₁ : ∀ {f g : R.T₁ → T₂} →
      (∀ x y → O.Gd x → O.Gd y → O.Ω₁ R.≤ₚ x → x R.≤ₚ y → Le (f x) (g y)) →
      Step (L.limᵢ L.zero f) (L.limᵢ L.zero g)
    aa₀ : ∀ {X} {g : R.T₀ → T₂} → Le X (g R.𝟙) → Step X (L.limᵢ (L.suc L.zero) g)
    aa₁ : ∀ {X} {g : R.T₁ → T₂} → (∀ z → T.Start z → Le X (g z)) → Step X (L.limᵢ L.zero g)
    uu : ∀ {X Y : R.T₁} → X R.≤ₚ Y → Step (L.up L.zero X) (L.up L.zero Y)
    uS : ∀ {X : R.T₁} → O.Gd X → Step (L.suc (L.up L.zero X)) (L.up L.zero (L.suc X))
    uS⁻ : ∀ {X : R.T₁} → O.Gd X → Step (L.up L.zero (L.suc X)) (L.suc (L.up L.zero X))
    uZ : Step (L.up L.zero (L.zero {ℓ = L.suc L.zero})) L.zero
    uZ⁻ : Step L.zero (L.up L.zero (L.zero {ℓ = L.suc L.zero}))
    uL : ∀ {f : ℕ → R.T₁} → (∀ n → O.Gd (f n)) → Step (L.up L.zero (L.lim f)) (L.lim (λ n → L.up L.zero (f n)))
    uL⁻ : ∀ {f : ℕ → R.T₁} → (∀ n → O.Gd (f n)) → Step (L.lim (λ n → L.up L.zero (f n))) (L.up L.zero (L.lim f))
    uN : ∀ {f : R.T₀ → R.T₁} → O.Gd (L.limᵢ L.zero f) →
      Step (L.up L.zero (L.limᵢ L.zero f)) (L.limᵢ (L.suc L.zero) (λ x → L.up L.zero (f x)))
    uN⁻ : ∀ {f : R.T₀ → R.T₁} → O.Gd (L.limᵢ L.zero f) →
      Step (L.limᵢ (L.suc L.zero) (λ x → L.up L.zero (f x))) (L.up L.zero (L.limᵢ L.zero f))
    tr : ∀ {X Y Z} → Le X Y → Le Y Z → Step X Z

left : ∀ {X Y} → Le X Y → Gd X
left (pack x y p) = x
right : ∀ {X Y} → Le X Y → Gd Y
right (pack x y p) = y
refl : ∀ {X} → Gd X → Le X X
refl g = pack g g rr
trans : ∀ {X Y Z} → Le X Y → Le Y Z → Le X Z
trans p q = pack (left p) (right q) (tr p q)
z≤ : ∀ {Y} → Gd Y → Le L.zero Y
z≤ g = pack gz g zz
s≤ : ∀ {X Y} → Le X Y → Le (L.suc X) (L.suc Y)
s≤ p = pack (gs (left p)) (gs (right p)) (ss p)
u≤ : ∀ {X Y} → O.Gd X → O.Gd Y → X R.≤ₚ Y → Le (L.up L.zero X) (L.up L.zero Y)
u≤ gx gy p = pack (gu gx) (gu gy) (uu p)
uS≤ : ∀ {X} → O.Gd X → Le (L.suc (L.up L.zero X)) (L.up L.zero (L.suc X))
uS≤ g = pack (gs (gu g)) (gu (O.gs g)) (uS g)

one-up-Ω : Le one (L.up L.zero O.Ω₁)
one-up-Ω = trans (trans (s≤ (z≤ (gu O.gz))) (uS≤ O.gz))
  (u≤ (O.gs O.gz) O.Gd-Ω O.pos-Ω)

Gd-Ω₂ : Gd F.Ω₂
Gd-Ω₂ = gn₁ (sc₁ (λ x y gx gy o p → u≤ gx gy p)
  (λ x gx o → uS≤ gx) one-up-Ω) (λ x gx o → gu gx)
Ω₂-refl : Le F.Ω₂ F.Ω₂
Ω₂-refl = refl Gd-Ω₂
```

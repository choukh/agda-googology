# YiZero 塔：层号的合法性对 Ω̂ 封闭，塔与 Λ 合法

**判决：编译定理，无前提。** `Legal-Ω̂ : ∀ x → Legal x → Legal (upT x)`，推论 `Legal-tw : ∀ n → Legal (tw n)`, `Legal-Λ : Legal Λ`。证法照 [YiLeanTower](YiLeanTower.lagda.md)；
块的改动 (`zero` 在 `top` 之下) 只多一条：层号上 `zero` 是一切层号的第一位置 (`CP-zero`)。不在闭项的切片里。块在 [YiZeroCore](YiZeroCore.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZeroTower where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiZeroCore

data CP : LF → LF → Set where
  self : ∀ {a} → CP a a
  suc  : ∀ {a b} → CP a b → CP a (suc b)
  lim  : ∀ {a f} n → CP a (f n) → CP a (lim f)
  fst  : ∀ {a k g} → CP a (g G.top) → CP a (lc k g)

Legal : LF → Set
Legal zero = ⊤
Legal (suc k) = Legal k
Legal (lim f) = (∀ n → CP (f n) (f (suc n))) × (∀ n → Legal (f n))
Legal (lc k g) = Legal k × (∀ η → Lgl k η → Legal (g η)) ×
  (∀ η η′ → Lgl k η → Cp k η η′ → Lgl k η′ → CP (g η) (g η′))

CP-zero : ∀ x → CP zero x
CP-zero zero = self
CP-zero (suc x) = suc (CP-zero x)
CP-zero (lim f) = lim 0 (CP-zero (f 0))
CP-zero (lc k g) = fst (CP-zero (g G.top))
```

```agda
fstN : ∀ y r (h : Lay.A (Lo y r) → LF) {a} → CP a (h (Lay.tp (Lo y r))) → CP a (upN y r h)
fstN (suc k) (inj₁ _) h p = fst p
fstN (suc k) (inj₂ r) = fstN k r
fstN (lim f) (n , r) = fstN (f n) r
fstN (lc k g) (η , _ , r) = fstN (g η) r

cp→CP : ∀ y {a b} → Cp y a b → CP (up y a) (up y b)
dn→CP : ∀ y {a} b → Dn y a b → CP (up y a) (up y b)
cp→CP y (inj₁ refl) = self
cp→CP y (inj₂ p) = dn→CP y _ p
dn→CP y (G.suc b) p = suc (cp→CP y p)
dn→CP y (G.lim f) (n , p) = lim n (cp→CP y p)
dn→CP y (G.lc r g) p = fstN y r _ (cp→CP y p)
dn→CP (suc k) {G.em _ a} (G.em _ d) (refl , p) = dn→CP k d p
dn→CP (lim f) {G.em n a} (G.em _ d) (refl , p) = dn→CP (f n) d p
dn→CP (lc k g) {G.em (η , l) a} (G.em _ d) (refl , p) = dn→CP (g η) d p
dn→CP y G.top refl = CP-zero (upT y)

legalN : ∀ y r (h : Lay.A (Lo y r) → LF) → Legal y →
  (∀ η → Lay.lg (Lo y r) η → Legal (h η)) →
  (∀ η η′ → Lay.lg (Lo y r) η → Le (Lo y r) η η′ → Lay.lg (Lo y r) η′ → CP (h η) (h η′)) →
  Legal (upN y r h)
legalN (suc k) (inj₁ _) h L a b = L , a , b
legalN (suc k) (inj₂ r) h L = legalN k r h L
legalN (lim f) (n , r) h (st , L) = legalN (f n) r h (L n)
legalN (lc k g) (η , l , r) h (Lk , lg , mo) = legalN (g η) r h (lg η l)
```

## 闭包定理与推论

```agda
Ω̂-CP : ∀ {a b} → CP a b → CP (upT a) (upT b)
Ω̂-CP self = self
Ω̂-CP (suc p) = fst (Ω̂-CP p)
Ω̂-CP (lim n p) = lim n (Ω̂-CP p)
Ω̂-CP (fst p) = fst (Ω̂-CP p)

Legal-Ω̂ : ∀ x → Legal x → Legal (upT x)
lgl→Legal : ∀ y → Legal y → ∀ a → Lgl y a → Legal (up y a)

Legal-Ω̂ zero L = tt
Legal-Ω̂ (suc k) L = L , (λ η l → lgl→Legal k L η l) , (λ η η′ l e l′ → cp→CP k e)
Legal-Ω̂ (lim f) (st , L) = (λ n → Ω̂-CP (st n)) , (λ n → Legal-Ω̂ (f n) (L n))
Legal-Ω̂ (lc k g) (Lk , lg , mo) =
  Lk , (λ η l → Legal-Ω̂ (g η) (lg η l)) , (λ η η′ l e l′ → Ω̂-CP (mo η η′ l e l′))

lgl→Legal y L G.zero l = tt
lgl→Legal y L (G.suc a) l = lgl→Legal y L a l
lgl→Legal y L (G.lim f) (st , lf) = (λ n → cp→CP y (st n)) , (λ n → lgl→Legal y L (f n) (lf n))
lgl→Legal y L (G.lc r g) (lg , mo) =
  legalN y r _ L (λ η l → lgl→Legal y L (g η) (lg η l)) (λ η η′ l e l′ → cp→CP y (mo η η′ l e l′))
lgl→Legal (suc k) L (G.em _ a) l = lgl→Legal k L a l
lgl→Legal (lim f) (st , L) (G.em n a) l = lgl→Legal (f n) (L n) a l
lgl→Legal (lc k g) (Lk , lg , mo) (G.em (η , lη) a) l = lgl→Legal (g η) (lg η lη) a l
lgl→Legal y L G.top l = Legal-Ω̂ y L

tw-step : ∀ n → CP (tw n) (tw (suc n))
tw-step zero = suc self
tw-step (suc n) = Ω̂-CP (tw-step n)

Legal-tw : ∀ n → Legal (tw n)
Legal-tw zero = tt
Legal-tw (suc n) = Legal-Ω̂ (tw n) (Legal-tw n)

Legal-Λ : Legal Λ
Legal-Λ = tw-step , Legal-tw

Legal-ΩΛ : Legal (upT Λ)
Legal-ΩΛ = Legal-Ω̂ Λ Legal-Λ
```

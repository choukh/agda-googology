---
title: 形式化大数数学 (3.0 - 高阶递归序数层级)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.0 - 高阶递归序数层级)

> 交流Q群: 893531731  
> 本文源码: [HigherOrd.lagda.md](httrsps://github.com/choukh/agda-googology/blob/main/src/OCF/HigherOrd.lagda.md)  
> 高亮渲染: [HigherOrd.html](httrsps://choukh.github.io/agda-googology/OCF.HigherOrd.html)  

## 工作环境

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module OCF.HigherOrd where
open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
```

```agda
open import WellFormed.Base as Level public
  using (a; b; c; n; m; zero; suc; lim)
  renaming (Ord to Level; Road to _⊏_; _<_ to _⊏₁_; rd-trans to ⊏-trans; f<l-rd to f⊏l)

open Level.Foundations public
open Level.CanonicalRoad using (cano; cano-2const)
import Cubical.Foundations.Prelude as 🧊
```

## 高阶递归序数层级

```agda
data U (ℓ : Level) (E : ∀ a → a ⊏ ℓ → Type) : Type
data _<_ {ℓ : Level} {E : ∀ a → a ⊏ ℓ → Type} : U ℓ E → U ℓ E → Type; infix 6 _<_
```

```agda
variable
  ℓ ℓ′ : Level
  aℓ : a ⊏ ℓ
  E : ∀ a → a ⊏ ℓ → Type
  α β γ : U ℓ E
  f g : ℕ → U ℓ E
```

```agda
_<₁_ : U ℓ E → U ℓ E → Type; infix 6 _<₁_
α <₁ β = ∥ α < β ∥₁
```

```agda
wf : (ℕ → U ℓ E) → Type
wf f = ∀ {n} → f n <₁ f (suc n)
```

```agda
data U ℓ E where
  zero : U ℓ E
  suc  : U ℓ E → U ℓ E
  lim  : (f : ℕ → U ℓ E) → ⦃ wf f ⦄ → U ℓ E
  Lim : (aℓ : a ⊏ ℓ) (F : E a aℓ → U ℓ E) → U ℓ E
```

```agda
data _<_ {ℓ} {E} where
  zero : α < suc α
  suc  : α < β → α < suc β
  f<l  : {w : wf f} → f n < lim f ⦃ w ⦄
  lim  : {w : wf f} → α < f n → α < lim f ⦃ w ⦄
  Lim  : {aℓ : a ⊏ ℓ} {F : E a aℓ → U ℓ E} {ι : E a aℓ} → α < F ι → α < Lim aℓ F
```

## 层级的表示

```agda
Elm : ∀ a → a ⊏ ℓ → Type
Elm a zero = U a Elm
Elm a (suc r) = Elm a r
Elm a (lim r) = Elm a r
```

```agda
Ord : Level → Type
Ord a = U a Elm
```

```agda
Elm≡Ord : Elm a aℓ ≡ Ord a
Elm≡Ord {aℓ = zero} = refl
Elm≡Ord {aℓ = suc aℓ} = Elm≡Ord {aℓ = aℓ}
Elm≡Ord {aℓ = lim aℓ} = Elm≡Ord {aℓ = aℓ}
```

```agda
ord : Elm a aℓ → Ord a
ord {aℓ} α = subst id Elm≡Ord α

elm : Ord a → Elm a aℓ
elm α = subst id (sym Elm≡Ord) α
```

```agda
open import Relation.Binary.PropositionalEquality using (subst-sym-subst; subst-subst-sym)

elm-ord : {α : Elm a aℓ} → subst id (sym Elm≡Ord) (ord α) ≡ α
elm-ord = subst-sym-subst Elm≡Ord
{-# REWRITE elm-ord #-}

ord-elm : {aℓ : a ⊏ ℓ} {α : Ord a} → subst id Elm≡Ord (elm {aℓ = aℓ} α) ≡ α
ord-elm = subst-subst-sym Elm≡Ord
{-# REWRITE ord-elm #-}
```

```agda
trsp : {aℓ : a ⊏ ℓ} {aℓ′ : a ⊏ ℓ′} → Elm a aℓ → Elm a aℓ′
trsp α = elm (ord α)
```

```agda
lim- : (f : ℕ → Ord a) {w : wf f} → Ord a
lim- f {w} = lim f ⦃ w ⦄
```

## 数字字面量

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

## 极限的外延性

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
module _ {aℓ₁ : a ⊏ ℓ} {F₁ : Elm a (cano aℓ₁) → U ℓ Elm}
         {aℓ₂ : a ⊏ ℓ} {F₂ : Elm a (cano aℓ₂) → U ℓ Elm}
         (p : {aℓ : a ⊏ ℓ} (ι : Elm a aℓ) → F₁ (trsp ι) ≡ F₂ (trsp ι))
         where

  LimExtPath : Path (U ℓ Elm) (Lim (cano aℓ₁) F₁) (Lim (cano aℓ₂) F₂)
  LimExtPath i = Lim (cano-2const aℓ₁ aℓ₂ i) λ ι → eqToPath (p ι) i

  LimExt : U.Lim (cano aℓ₁) F₁ ≡ Lim (cano aℓ₂) F₂
  LimExt = pathToEq LimExtPath
```

## 第零层与层级序数同构

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
  from< (lim r) = lim ⦃ _ ⦄ (from< r)
  from< f<l = f⊏l
```

```agda
  from : Level → Ord 0
  from⊏ : a ⊏ b → from a < from b

  from zero = zero
  from (suc a) = suc (from a)
  from (lim f) = lim (from ∘ f) ⦃ map from⊏ it ⦄

  from⊏ zero = zero
  from⊏ (suc r) = suc (from⊏ r)
  from⊏ (lim r) = lim (from⊏ r)
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
level : Ord 0 → Level
level = subst id OrdIso.Ord0≡Level
```

## 高阶路径关系

```agda
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Induction.WellFounded
```

```agda
module Order (a : Level) where
  open import Relation.Binary.Structures {A = Ord a} _≡_
  _<ₐ_ : Ord a → Ord a → Type
  _<ₐ_ = _<_
```

### 严格序

```agda
  <-resp-≡ : _<ₐ_ Respects₂ _≡_
  <-resp-≡ = (λ { refl → id }) , (λ { refl → id })
```

```agda
  <-trans : Transitive _<ₐ_
  <-trans r zero = suc r
  <-trans r (suc s) = suc (<-trans r s)
  <-trans r (lim s) = lim (<-trans r s)
  <-trans r (Lim s) = Lim (<-trans r s)
  <-trans r f<l = lim r
```

```agda
  <-acc : α <ₐ β → Acc _<ₐ_ α
  <-acc zero    = acc λ s → <-acc s
  <-acc (suc r) = acc λ s → <-acc (<-trans s r)
  <-acc (lim r) = acc λ s → <-acc (<-trans s r)
  <-acc (Lim r) = acc λ s → <-acc (<-trans s r)
  <-acc f<l     = acc λ s → <-acc s

  <-wfnd : WellFounded _<ₐ_
  <-wfnd _ = <-acc zero
```

```agda
  <-asym : Asymmetric _<ₐ_
  <-asym = wf⇒asym <-wfnd

  <-irrefl : Irreflexive _≡_ _<ₐ_
  <-irrefl = wf⇒irrefl <-resp-≡ sym <-wfnd
```

```agda
  <-isStrictPartialOrder : IsStrictPartialOrder _<_
  <-isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl = <-irrefl
    ; trans = <-trans
    ; <-resp-≈ = <-resp-≡ }
```

### 非严格序

```agda
  open import Relation.Binary.Construct.StrictToNonStrict _≡_ _<ₐ_
    as NonStrict public using () renaming (_≤_ to infix 6 _≤_; <⇒≤ to <→≤)
```

```agda
  <s→≤ : α < suc β → α ≤ β
  <s→≤ zero    = inr refl
  <s→≤ (suc r) = inl r

  ≤→<s : α ≤ β → α < suc β
  ≤→<s (inl r)    = suc r
  ≤→<s (inr refl) = zero
```

```agda
  ≤-refl : Reflexive _≤_
  ≤-refl = NonStrict.reflexive refl

  ≤-antisym : Antisymmetric _≡_ _≤_
  ≤-antisym = NonStrict.antisym isEquivalence <-trans <-irrefl

  ≤-trans : Transitive _≤_
  ≤-trans = NonStrict.trans isEquivalence <-resp-≡ <-trans

  <-≤-trans : Trans _<ₐ_ _≤_ _<ₐ_
  <-≤-trans = NonStrict.<-≤-trans <-trans (fst <-resp-≡)

  ≤-<-trans : Trans _≤_ _<ₐ_ _<ₐ_
  ≤-<-trans = NonStrict.≤-<-trans sym <-trans (snd <-resp-≡)
```

```agda
  ≤-isPreorder : IsPreorder _≤_
  ≤-isPreorder = record
    { isEquivalence = isEquivalence
    ; reflexive = inr
    ; trans = ≤-trans
    }

  ≤-isPartialOrder : IsPartialOrder _≤_
  ≤-isPartialOrder = record { isPreorder = ≤-isPreorder ; antisym = ≤-antisym }
```

```agda
module _ {a : Level} where
  open Order a hiding (_<ₐ_; _≤_)
  open Order a using (_<ₐ_; _≤_) public
  module HigherRoadReasoning where
    open import Relation.Binary.Reasoning.Base.Triple
      {_≈_ = _≡_} {_≤_ = _≤_} {_<_ = _<ₐ_}
      ≤-isPreorder <-asym <-trans <-resp-≡ <→≤ <-≤-trans ≤-<-trans
      public
```

## 层级的提升

```agda
lift : a ⊏ b → Ord a → Ord b
lift-pres : {ab : a ⊏ b} → α < β → lift ab α < lift ab β

lift ab zero = zero
lift ab (suc α) = suc (lift ab α)
lift ab (lim f) = lim (lift ab ∘ f) ⦃ map lift-pres it ⦄
lift ab (Lim xa F) = Lim (cano $ ⊏-trans xa ab) λ ι → lift ab (F $ trsp ι)

lift-pres zero = zero
lift-pres (suc r) = suc (lift-pres r)
lift-pres (lim r) = lim (lift-pres r)
lift-pres (Lim {ι} r) = Lim {ι = trsp ι} (lift-pres $ subst (_ <_) refl r)
lift-pres f<l = f<l
```

提升的复合

```agda
lift-comp : {ab : a ⊏ b} {bc : b ⊏ c} {ac : a ⊏ c} → lift ac α ≡ lift bc (lift ab α)
lift-comp {α = zero} = refl
lift-comp {α = suc α} = cong suc lift-comp
lift-comp {α = lim f} = limExt λ _ → lift-comp
lift-comp {α = Lim xa F} = LimExt λ _ → lift-comp
```

```agda
lift-trans : {ab : a ⊏ b} {bc : b ⊏ c} → lift (⊏-trans ab bc) α ≡ lift bc (lift ab α)
lift-trans = lift-comp
```

## 高阶 ω

```agda
instance
  finOrd-wf : wf (finOrd {a})
  finOrd-wf = ∣ zero ∣₁

ω : Ord a
ω = lim finOrd

Ω : ∀ a → Ord a
Ω-pres : {ac : a ⊏ c} {bc : b ⊏ c} → a ⊏ b → lift ac (Ω a) < lift bc (Ω b)

Ω zero = ω
Ω (suc a) = Lim zero (lift zero)
Ω (lim f) = lim (λ n → lift f⊏l (Ω $ f n)) ⦃ map Ω-pres it ⦄

Ω-pres {a} {c} {ac} {bc} zero = Lim {ι = elm $ suc (Ω a)} (begin-strict
  lift ac (Ω a)                       <⟨ lift-pres zero ⟩
  lift ac (suc (Ω a))                 ≈⟨ lift-comp ⟩
  lift bc (lift zero (suc (Ω a)))     ∎) where open HigherRoadReasoning
Ω-pres {a} {c} {ac} {bc} (suc {b} r) = Lim {ι = elm $ Ω b} $ begin-strict
  lift ac (Ω a)                       <⟨ Ω-pres r ⟩
  lift _ (Ω b)                        ≈⟨ lift-trans ⟩
  lift bc (lift zero (Ω b))           ∎ where open HigherRoadReasoning
Ω-pres {a} {c} {ac} {bc} (lim {f} {n} r) = lim $ begin-strict
  lift ac (Ω a)                       <⟨ Ω-pres r ⟩
  lift _ (Ω (f n))                    ≈⟨ lift-trans ⟩
  lift bc (lift f⊏l (Ω (f n)))        ∎ where open HigherRoadReasoning
```

## 高阶良构性

```agda
Pres : (aℓ : a ⊏ ℓ) → (Elm a aℓ → Ord ℓ) → Type
Pres aℓ F = ∀ {β γ} → β < γ → F (elm β) < F (elm γ)
```

```agda
data Wf {ℓ : Level} : Ord ℓ → Type where
  zero : Wf zero
  suc  : Wf α → Wf (suc α)
  lim  : {w : wf f} (ḟ : ∀ {n} → Wf (f n)) → Wf (lim f ⦃ w ⦄)
  Lim  : {aℓ : a ⊏ ℓ} {F : Elm a aℓ → Ord ℓ}
         (Ḟ : ∀ {n} → Wf (F $ elm $ finOrd n)) (F-pres : Pres aℓ F) → Wf (Lim aℓ F)
```

```agda
finOrd-Wf : Wf {ℓ} (finOrd n)
finOrd-Wf {n = zero} = zero
finOrd-Wf {n = suc n} = suc finOrd-Wf
```

```agda
lift-Wf : {ab : a ⊏ b} {α : Ord a} → Wf α → Wf (lift ab α)
lift-Wf zero = zero
lift-Wf (suc α̇) = suc (lift-Wf α̇)
lift-Wf (lim ḟ) = lim (lift-Wf ḟ)
lift-Wf (Lim Ḟ F-pres) = Lim (lift-Wf Ḟ) (lift-pres ∘ F-pres)
```

```agda
Ω-Wf : Wf (Ω a)
Ω-Wf {(zero)} = lim finOrd-Wf
Ω-Wf {suc a} = Lim (lift-Wf finOrd-Wf) lift-pres
Ω-Wf {lim f} = lim (lift-Wf Ω-Wf)
```

---
title: 形式化大数数学 (3.0 - 序数崩塌函数)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (3.0 - 序数崩塌函数)

> 交流Q群: 893531731  
> 本文源码: [Base.lagda.md](httrsps://github.com/choukh/agda-googology/blob/main/src/Madore/Base.lagda.md)  
> 高亮渲染: [Base.html](httrsps://choukh.github.io/agda-googology/Madore.Base.html)  

## 工作环境

```agda
{-# OPTIONS --rewriting --cubical --lossy-unification #-}
module Madore.Base where
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

## 高阶递归层级

```agda
data U (ℓ : Level) (E : ∀ a → a ⊏ ℓ → Type) : Type
data _<_ {ℓ : Level} {E : ∀ a → a ⊏ ℓ → Type} : U ℓ E → U ℓ E → Type; infix 6 _<_
```

```agda
variable
  ℓ ℓ′ : Level
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
  lim  : ⦃ _ : wf f ⦄ → α < f n → α < lim f
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
Elm≡Ord : {aℓ : a ⊏ ℓ} → Elm a aℓ ≡ Ord a
Elm≡Ord {aℓ = zero} = refl
Elm≡Ord {aℓ = suc aℓ} = Elm≡Ord {aℓ = aℓ}
Elm≡Ord {aℓ = lim aℓ} = Elm≡Ord {aℓ = aℓ}
```

```agda
ord : {aℓ : a ⊏ ℓ} → Elm a aℓ → Ord a
ord {aℓ} α = subst id Elm≡Ord α

elm : {aℓ : a ⊏ ℓ} → Ord a → Elm a aℓ
elm α = subst id (sym Elm≡Ord) α
```

```agda
open import Relation.Binary.PropositionalEquality using (subst-sym-subst; subst-subst-sym)

elm-ord : {aℓ : a ⊏ ℓ} {α : Elm a aℓ} → subst id (sym Elm≡Ord) (ord α) ≡ α
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
lift-pres (lim r) = lim ⦃ map lift-pres it ⦄ (lift-pres r)
lift-pres (Lim {ι} r) = Lim {ι = trsp ι} (lift-pres $ subst (_ <_) refl r)
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

Ω-pres {a} {ac} zero        = Lim {ι = elm $ suc (Ω a)} (subst (lift ac (Ω a) <_) lift-comp (lift-pres zero))
Ω-pres {bc}     (suc {b} r) = Lim {ι = elm $ Ω b}       (subst (_ <_) lift-trans (Ω-pres r))
Ω-pres {bc}     (lim r)     = lim ⦃ _ ⦄                 (subst (_ <_) lift-trans (Ω-pres r))
```

## 路径关系

```agda
open import Relation.Binary.Definitions
open import Induction.WellFounded
```

### 严格序

```agda
<-trans : Transitive (_<_ {ℓ} {E = Elm})
<-trans r zero = suc r
<-trans r (suc s) = suc (<-trans r s)
<-trans r (lim s) = lim (<-trans r s)
<-trans r (Lim s) = Lim (<-trans r s)

<-acc : {α β : Ord a} → α < β → Acc _<_ α
<-acc zero    = acc λ s → <-acc s
<-acc (suc r) = acc λ s → <-acc (<-trans s r)
<-acc (lim r) = acc λ s → <-acc (<-trans s r)
<-acc (Lim r) = acc λ s → <-acc (<-trans s r)
```

## 高阶算术

```agda
_+_ : Ord a → Ord a → Ord a; infixl 7 _+_
+-pres : β < γ → α + β < α + γ

α + zero = α
α + suc β = suc (α + β)
α + lim f = lim (λ n → α + f n) ⦃ map +-pres it ⦄
α + Lim aℓ F = Lim aℓ (λ ι → α + F ι)

+-pres zero = zero
+-pres (suc r) = suc (+-pres r)
+-pres (lim r) = lim ⦃ _ ⦄ (+-pres r)
+-pres (Lim r) = Lim (+-pres r)
```

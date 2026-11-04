# 表的路线: 位置, 键的判定 (由 [GuardTightTab](GuardTightTab.lagda.md) 用脚本改写)

> 不含记号. 结论写在 [LevelNoK](LevelNoK.lagda.md). 只差 `kdec` 的 `bra` 对 `bra`: 走 `cmpBr`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LevelNoKLv using (Dom; module Lv)

module OCF.Align.LevelNoKTab (𝔻 : Dom) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open Lv 𝔻
```

## §1 位置的接上与严格子项

```agda
infixr 9 _⊙_
_⊙_ : ∀ {k a b} → Cp a b → Cp k a → Cp k b
self      ⊙ q = q
suc p     ⊙ q = suc (p ⊙ q)
lim n p   ⊙ q = lim n (p ⊙ q)
fst p     ⊙ q = fst (p ⊙ q)
bra η e p ⊙ q = bra η e (p ⊙ q)

adm⊙ : ∀ {E k a b} (p : Cp a b) {q : Cp k a} → AdmC E p → AdmC E q → AdmC E (p ⊙ q)
adm⊙ self        _ y = y
adm⊙ (suc p)     x y = adm⊙ p x y
adm⊙ (lim n p)   x y = adm⊙ p x y
adm⊙ (fst p)     x y = adm⊙ p x y
adm⊙ (bra η e p) (u , x) y = u , adm⊙ p x y

toCp : ∀ {k c} → k < c → Cp k c
toCp zero        = suc self
toCp (suc r)     = suc (toCp r)
toCp (lim n r)   = lim n (toCp r)
toCp (fst r)     = fst (toCp r)
toCp (bra η e r) = bra η e (toCp r)

admTo : ∀ {E k c} (r : k < c) → Adm E r → AdmC E (toCp r)
admTo zero        _ = tt
admTo (suc r)     a = admTo r a
admTo (lim n r)   a = admTo r a
admTo (fst r)     a = admTo r a
admTo (bra η e r) (u , a) = u , admTo r a

data Strict (k : LG) : LG → Set where
  st-suc : ∀ {b} → Cp k b → Strict k (suc b)
  st-lim : ∀ {f} n → Cp k (f n) → Strict k (lim f)
  st-fst : ∀ {c t g} → Cp k t → Strict k (lc c t g)
  st-bra : ∀ {c t g} η e → Cp k (g η e) → Strict k (lc c t g)

stCp : ∀ {k a} → Strict k a → Cp k a
stCp (st-suc r)     = suc r
stCp (st-lim n r)   = lim n r
stCp (st-fst r)     = fst r
stCp (st-bra η e r) = bra η e r

st⊙ : ∀ {k a b} → Cp a b → Strict k a → Strict k b
st⊙ self s = s
st⊙ (suc p) s = st-suc (p ⊙ stCp s)
st⊙ (lim n p) s = st-lim n (p ⊙ stCp s)
st⊙ (fst p) s = st-fst (p ⊙ stCp s)
st⊙ (bra η e p) s = st-bra η e (p ⊙ stCp s)

irr : ∀ a {k} → Strict k a → a ≈ k → ⊥
irr (suc a) (st-suc r) (s≈ e) = irr a (st⊙ r (st-suc self)) e
irr (lim f) (st-lim n r) (l≈ h) = irr (f n) (st⊙ r (st-lim n self)) (h n)
irr (lc c t g) (st-fst r) (o≈ d e h h⁻ hˡ hʳ) = irr t (st⊙ r (st-fst self)) e
irr (lc c t g) (st-bra η e₁ r) (o≈ d e h h⁻ hˡ hʳ) = irr (g η e₁) (st⊙ r (st-bra η (conv d e₁) self)) (h η e₁)
```

## §2 键的判定

对 $c$ 结构递归, 与 `<-dec` 同一个骨架.

```agda
Dec′ : Set → Set
Dec′ A = A ⊎ (A → ⊥)

decL : ∀ {a a′ b} → a ≈ a′ → Dec′ (a′ ≈ b) → Dec′ (a ≈ b)
decL e (inj₁ d) = inj₁ (≈-trans e d)
decL e (inj₂ n) = inj₂ (λ d → n (≈-trans (≈-sym e) d))

decR : ∀ {a b b′} → b ≈ b′ → Dec′ (a ≈ b′) → Dec′ (a ≈ b)
decR e (inj₁ d) = inj₁ (≈-trans d (≈-sym e))
decR e (inj₂ n) = inj₂ (λ d → n (≈-trans d e))

kdec : ∀ {c} → WFˢ c → c ≈ c → ∀ {c₁ t₁ g₁ c₂ t₂ g₂} (p : Cp (lc c₁ t₁ g₁) c) (q : Cp (lc c₂ t₂ g₂) c) (E : Ents) → AdmC (tab E) p → AdmC (tab E) q → Dec′ (lc c₁ t₁ g₁ ≈ lc c₂ t₂ g₂)
kdec {suc k} w (s≈ e) (suc p) (suc q) E ap aq = kdec w e p q E ap aq
kdec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) E ap aq with <ᴺ-dec n m
... | injᵃ n<m with ⊴K (stepsˢ st n<m) p
...   | viaᴷ d p′ t = decL d (kdec (w m) (e m) p′ q E (t (tab E) ap) aq)
kdec {lim f} (st , w) (l≈ e) (lim n p) (lim m q) E ap aq | injᵇ m<n with ⊴K (stepsˢ st m<n) q
...   | viaᴷ d q′ t = decR d (kdec (w n) (e n) p q′ E ap (t (tab E) aq))
kdec {lim f} (st , w) (l≈ e) (lim n p) (lim _ q) E ap aq | injᶜ refl = kdec (w n) (e n) p q E ap aq
kdec {lc c t g} wf sf self self E _ _ = inj₁ sf
kdec {lc c t g} wf sf self (fst q) E _ _ = inj₂ (irr (lc c t g) (st-fst q))
kdec {lc c t g} wf sf self (bra η e q) E _ _ = inj₂ (irr (lc c t g) (st-bra η e q))
kdec {lc c t g} wf sf (fst p) self E _ _ = inj₂ (λ d → irr (lc c t g) (st-fst p) (≈-sym d))
kdec {lc c t g} wf sf (bra η e p) self E _ _ = inj₂ (λ d → irr (lc c t g) (st-bra η e p) (≈-sym d))
kdec {lc c t g} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst p) (fst q) E ap aq = kdec wt se p q E ap aq
kdec {lc c t g} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (fst p) (bra η e q) E ap (ly , aq) with ⊴K (tg η e) p
... | viaᴷ d′ p′ u = decL d′ (kdec (wg η e) (shˡ η e) p′ q E (u (tab E) ap) aq)
kdec {lc c t g} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra η e p) (fst q) E (lx , ap) aq with ⊴K (tg η e) q
... | viaᴷ d′ q′ u = decR d′ (kdec (wg η e) (shˡ η e) p q′ E ap (u (tab E) aq))
kdec {lc c t g} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ p) (bra y e₂ q) E ((ℓ , a , o₁ , lx) , ap) ((ℓ′ , b , o₂ , ly) , aq) with at-uq {E} (o≈ d se sh sh⁻ shˡ shʳ) a b
... | refl with cmpBr {u = ℓ} dir o₁ o₂ e₁ e₂ lx ly
...   | inj₁ r with ⊴K r p
...     | viaᴷ d′ p′ u = decL d′ (kdec (wg y e₂) (shˡ y e₂) p′ q E (u (tab E) ap) aq)
kdec {lc c t g} (tg , dir , wt , wg) (o≈ d se sh sh⁻ shˡ shʳ) (bra x e₁ p) (bra y e₂ q) E ((ℓ , a , o₁ , lx) , ap) ((ℓ′ , b , o₂ , ly) , aq) | refl | inj₂ r with ⊴K r q
...     | viaᴷ d′ q′ u = decR d′ (kdec (wg x e₁) (shˡ x e₁) p q′ E ap (u (tab E) aq))
```

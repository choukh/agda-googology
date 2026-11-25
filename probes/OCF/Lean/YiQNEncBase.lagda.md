# 不单射的孩子编码: 通用引理

> 判决: 编译定理, 无前提 (排中律, 函数外延只作参数). 排中律给一切类型的 UIP (`lem→uip`, Hedberg); 单射加排中律给满射 (`inj→surj`); 带全空间相等的 ℕ 极限相等 (`limEq`, 用函数外延与 UIP).
> `Emb a b`: `Tr a` 到 `Tr b` 的保零, 保第一位置序的映射, 在树上与 "相邻证明的全空间" 上单射. 用法在 `YiQNEncStep`.
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQNEncBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Tr⁺; T⁺)
open import OCF.Lean.YiRVLevel using (LEM)
open import OCF.Lean.YiQNReg using (Surj)
```

## 函数外延, UIP (Hedberg)

```agda
Funext : Set₁
Funext = ∀ {A : Set} {B : A → Set} {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g

UIP : Set → Set
UIP A = {x y : A} (p q : x ≡ y) → p ≡ q

tsr : {A : Set} {x y : A} (r : x ≡ y) → trans (sym r) r ≡ refl
tsr refl = refl

module Hedberg {A : Set} (d : (x y : A) → (x ≡ y) ⊎ (x ≡ y → ⊥)) where
  pick : {x y : A} → (x ≡ y) ⊎ (x ≡ y → ⊥) → x ≡ y → x ≡ y
  pick (inj₁ q) p = q
  pick (inj₂ n) p = ⊥-elim (n p)

  pick-c : {x y : A} (e : (x ≡ y) ⊎ (x ≡ y → ⊥)) (p q : x ≡ y) → pick e p ≡ pick e q
  pick-c (inj₁ r) p q = refl
  pick-c (inj₂ n) p q = ⊥-elim (n p)

  nf : {x y : A} → x ≡ y → x ≡ y
  nf {x} {y} p = pick (d x y) p

  canon : {x y : A} (p : x ≡ y) → trans (sym (nf (refl {x = x}))) (nf p) ≡ p
  canon {x} refl = tsr (nf (refl {x = x}))

  uip : UIP A
  uip {x} {y} p q =
    trans (sym (canon p)) (trans (cong (trans (sym (nf (refl {x = x})))) (pick-c (d x y) p q)) (canon q))

lem→uip : LEM → (A : Set) → UIP A
lem→uip lem A = Hedberg.uip (λ x y → lem (x ≡ y))
```

## Σ 的纤维, 单射到满射

```agda
Σ≡ : {A : Set} {B : A → Set} {a a′ : A} {b : B a} {b′ : B a′}
   → _≡_ {A = Σ A B} (a , b) (a′ , b′) → Σ (a ≡ a′) λ p → subst B p b ≡ b′
Σ≡ refl = refl , refl

fib : {A : Set} (B : A → Set) → UIP A → {a : A} {b b′ : B a} → _≡_ {A = Σ A B} (a , b) (a , b′) → b ≡ b′
fib B u {b = b} {b′} e = subst (λ q → subst B q b ≡ b′) (u (proj₁ (Σ≡ e)) refl) (proj₂ (Σ≡ e))

Inj : Set → Set → Set
Inj A B = Σ (A → B) λ f → {x y : A} → f x ≡ f y → x ≡ y

module _ (lem : LEM) where
  inj→surj : {A B : Set} → A → Inj A B → Surj B A
  inj→surj {A} {B} a₀ (f , fi) = ρ , λ z → f z , back z (lem (Σ A λ x → f x ≡ f z))
    where
    pk : (u : B) → (Σ A λ x → f x ≡ u) ⊎ ((Σ A λ x → f x ≡ u) → ⊥) → A
    pk u (inj₁ w) = proj₁ w
    pk u (inj₂ _) = a₀
    ρ : B → A
    ρ u = pk u (lem (Σ A λ x → f x ≡ u))
    back : (z : A) (w : (Σ A λ x → f x ≡ f z) ⊎ ((Σ A λ x → f x ≡ f z) → ⊥)) → pk (f z) w ≡ z
    back z (inj₁ (x , e)) = fi e
    back z (inj₂ n)       = ⊥-elim (n (z , refl))
```

## 有限标签

```agda
natT : {S : Sg} → ℕ → T S
natT zero    = zero
natT (suc n) = suc (natT n)

cntT : {S : Sg} → T S → ℕ
cntT (suc x) = suc (cntT x)
cntT _       = zero

natT-inj : {S : Sg} {n m : ℕ} → natT {S} n ≡ natT m → n ≡ m
natT-inj {S} {n} {m} e = trans (sym (cn n)) (trans (cong cntT e) (cn m))
  where
  cn : (k : ℕ) → cntT (natT {S} k) ≡ k
  cn zero    = refl
  cn (suc k) = cong suc (cn k)
```

## 相邻证明的全空间, ℕ 极限的相等

`TL S`: 一层之内带两端的第一位置序证明. 指标不固定, 所以在它上面按构造子投影不需要合一指标.

```agda
TL : Sg → Set
TL S = Σ (T S) λ x → Σ (T S) λ y → Lt S x y

module _ {S : Sg} (u : UIP (T S)) where
  tEq : {x y z x′ y′ z′ : T S} {d : Lt S x y} {e : Lt S y z} {d′ : Lt S x′ y′} {e′ : Lt S y′ z′}
      → _≡_ {A = TL S} (x , y , d) (x′ , y′ , d′) → _≡_ {A = TL S} (y , z , e) (y′ , z′ , e′)
      → _≡_ {A = TL S} (x , z , ◃t d e) (x′ , z′ , ◃t d′ e′)
  tEq {x = x} {d = d} refl Q = cong (λ w → x , proj₁ w , ◃t d (proj₂ w)) (fib (λ y → Σ (T S) (Lt S y)) u Q)

  fix2 : {x y : T S} {d d′ : Lt S x y} → _≡_ {A = TL S} (x , y , d) (x , y , d′) → d ≡ d′
  fix2 {x} {y} e = fib (Lt S x) u (fib (λ x → Σ (T S) (Lt S x)) u e)

  limEq : Funext → {f f′ : ℕ → T S} {a : (n : ℕ) → Lt S (f n) (f (suc n))} {a′ : (n : ℕ) → Lt S (f′ n) (f′ (suc n))}
        → f ≡ f′ → ((n : ℕ) → _≡_ {A = TL S} (f n , f (suc n) , a n) (f′ n , f′ (suc n) , a′ n)) → lim f a ≡ lim f′ a′
  limEq fe {f} refl h = cong (lim f) (fe (λ n → fix2 (h n)))
```

## 嵌入 `Emb`

`injL` 带两端相等作前提 (由调用者给出), 所以对 ℕ 极限等强制指标不必再递归.

```agda
record Emb (a b : L) : Set where
  field
    σ    : Tr a → Tr b
    σm   : ∀ {x y} → a ⊢ x ◃ y → b ⊢ σ x ◃ σ y
    σz   : σ zero ≡ zero
    inj  : ∀ {x x′} → σ x ≡ σ x′ → x ≡ x′
    injL : ∀ {x y x′ y′} (d : a ⊢ x ◃ y) (d′ : a ⊢ x′ ◃ y′) → x ≡ x′ → y ≡ y′
         → _≡_ {A = TL (Sig b)} (σ x , σ y , σm d) (σ x′ , σ y′ , σm d′)
         → _≡_ {A = TL (Sig a)} (x , y , d) (x′ , y′ , d′)

  σ⁺ : Tr⁺ a → Tr⁺ b
  σ⁺ (y , e) = σ y , subst (λ t → b ⊢ t ◃ σ y) σz (σm e)

open Emb public

private
  unz : ∀ {b} {w : Tr b} (p : w ≡ zero) {Y Y′ : Tr b} {D : b ⊢ w ◃ Y} {D′ : b ⊢ w ◃ Y′}
      → _≡_ {A = Tr⁺ b} (Y , subst (λ t → b ⊢ t ◃ Y) p D) (Y′ , subst (λ t → b ⊢ t ◃ Y′) p D′)
      → _≡_ {A = TL (Sig b)} (w , Y , D) (w , Y′ , D′)
  unz refl E = cong (λ t → zero , proj₁ t , proj₂ t) E

inj⁺ : ∀ {a b} → UIP (Tr a) → (E : Emb a b) {t t′ : Tr⁺ a} → σ⁺ E t ≡ σ⁺ E t′ → t ≡ t′
inj⁺ {a} u E {y , e} {y′ , e′} P =
  fib (λ x → Σ (Tr a) (Lt (Sig a) x)) u
      (injL E e e′ refl (inj E (cong proj₁ P)) (unz (σz E) P))

idE : (a : L) → Emb a a
idE a = record { σ = λ x → x ; σm = λ d → d ; σz = refl ; inj = λ e → e ; injL = λ d d′ _ _ e → e }
```

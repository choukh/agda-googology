# 经典值工具：块上值的严格序、上确界、良基与最小元

> 验收文件，档位：编译定理（无前提）与条件定理（条件：排中律，模块参数 `lem`）。对象是 `YiVWVal` 的值 `V` 与跨层的 `≼`；不改块、折叠或合法性。
> 无前提：严格序 `a ≺ b = suc a ≼ b` 无自反（`irr`）、与 `≼` 相容；ℕ 族与 Ω 族的极限是 `≼` 下的最小上界，严格在它之下就严格在某一项之下（`lim-below`、`Ω-below`）；`≺` 跨层良基（`wf`）。
> 条件（排中律）：二分 `dich`（a ≼ b 或 b ≺ a），全序 `tri`（探针 P1 的 `P1Tri.tri`，这里由 `dich` 推出），`⋠→≻`，三歧 `trich`，外延 `ext≼`，上确界的分裂与刻画（`lim-split`、`lim-sup`、`Ω-split`、`Ω-sup`），非空谓词有 `≼` 最小元（`least`）。
> 不否定什么。入口 `Classical`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCIOrder where

open import Data.Nat using (ℕ)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Induction.WellFounded using (Acc; acc)

open import OCF.Lean.YiRWBlock using (L; Pos; Br)
open import OCF.Lean.YiVWVal using (V; zero; suc; lim; Ω; _≼_; _≈_; z≼; s≼s; ≼l; l≼; ≼Ω; Ω≼; ≼-refl; ≼-trans; ≼-suc; lim⁻; Ω⁻)
```

## 1 严格序（无前提）

```agda
infix 4 _≺_
_≺_ : ∀ {ℓ₁ ℓ₂} → V ℓ₁ → V ℓ₂ → Set
a ≺ b = suc a ≼ b

s≼s⁻ : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → suc a ≼ suc b → a ≼ b
s≼s⁻ (s≼s d) = d

≺0 : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} → ¬ (a ≺ zero {ℓ₂})
≺0 ()

lim-below : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {f : ℕ → V ℓ₂} → a ≺ lim f → Σ ℕ λ n → a ≺ f n
lim-below (≼l n d) = n , d

Ω-below : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {p : Pos ℓ₂} {g : Br ℓ₂ p → V ℓ₂} → a ≺ Ω p g → Σ (Br ℓ₂ p) λ z → a ≺ g z
Ω-below (≼Ω z d) = z , d

≺→≼ : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → a ≺ b → a ≼ b
≺→≼ {a = a} d = ≼-trans (≼-suc (≼-refl a)) d

≼-≺ : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≼ b → b ≺ c → a ≺ c
≼-≺ d e = ≼-trans (s≼s d) e

≺-≼ : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≺ b → b ≼ c → a ≺ c
≺-≼ d e = ≼-trans d e

irr : ∀ {ℓ} (a : V ℓ) → ¬ (a ≺ a)
irr zero ()
irr (suc a) d = irr a (s≼s⁻ d)
irr (lim f) d with lim-below d
... | n , e = irr (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) e)
irr (Ω p g) d with Ω-below d
... | z , e = irr (g z) (≼-trans (s≼s (≼Ω z (≼-refl (g z)))) e)

≺→⋠ : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → a ≺ b → ¬ (b ≼ a)
≺→⋠ {a = a} d e = irr a (≼-trans d e)
```

## 2 ℕ 族与 Ω 族的上确界（无前提）

```agda
lim-ub : ∀ {ℓ} (f : ℕ → V ℓ) (n : ℕ) → f n ≼ lim f
lim-ub f n = ≼l n (≼-refl (f n))

lim-lub : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {b : V ℓ₂} → ((n : ℕ) → f n ≼ b) → lim f ≼ b
lim-lub = l≼

lim-lub⁻ : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {b : V ℓ₂} → lim f ≼ b → (n : ℕ) → f n ≼ b
lim-lub⁻ d n = lim⁻ n d

Ω-ub : ∀ {ℓ} {p : Pos ℓ} (g : Br ℓ p → V ℓ) (z : Br ℓ p) → g z ≼ Ω p g
Ω-ub g z = ≼Ω z (≼-refl (g z))

Ω-lub : ∀ {ℓ₁ ℓ₂} {p : Pos ℓ₁} {g : Br ℓ₁ p → V ℓ₁} {b : V ℓ₂} → ((z : Br ℓ₁ p) → g z ≼ b) → Ω p g ≼ b
Ω-lub = Ω≼

Ω-lub⁻ : ∀ {ℓ₁ ℓ₂} {p : Pos ℓ₁} {g : Br ℓ₁ p → V ℓ₁} {b : V ℓ₂} → Ω p g ≼ b → (z : Br ℓ₁ p) → g z ≼ b
Ω-lub⁻ d z = Ω⁻ z d
```

## 3 良基（无前提）

跨层：载体是 `Σ L V`，`x ⊏ y` 即 `proj₂ x ≺ proj₂ y`。

```agda
VΣ : Set
VΣ = Σ L V

infix 4 _⊏_
_⊏_ : VΣ → VΣ → Set
x ⊏ y = proj₂ x ≺ proj₂ y

acc-≼ : ∀ {x y : VΣ} → proj₂ x ≼ proj₂ y → Acc _⊏_ y → Acc _⊏_ x
acc-≼ d (acc r) = acc (λ lt → r (≼-trans lt d))

acc-inv : ∀ {x y : VΣ} → Acc _⊏_ y → x ⊏ y → Acc _⊏_ x
acc-inv (acc r) e = r e

mutual
  wf : ∀ {ℓ} (a : V ℓ) → Acc _⊏_ (ℓ , a)
  wf a = acc (wf< a)

  wf< : ∀ {ℓ} (a : V ℓ) {y : VΣ} → y ⊏ (ℓ , a) → Acc _⊏_ y
  wf< zero ()
  wf< (suc a) lt = acc-≼ (s≼s⁻ lt) (wf a)
  wf< (lim f) lt with lim-below lt
  ... | n , e = acc-inv (wf (f n)) e
  wf< (Ω p g) lt with Ω-below lt
  ... | z , e = acc-inv (wf (g z)) e
```

## 4 经典部分（条件：排中律）

```agda
LEM : Set₁
LEM = (A : Set) → A ⊎ ¬ A

module Classical (lem : LEM) where

  notAll : {I : Set} {P : I → Set} → ¬ ((i : I) → P i) → Σ I (λ i → ¬ P i)
  notAll {I} {P} na with lem (Σ I (λ i → ¬ P i))
  ... | inj₁ e  = e
  ... | inj₂ ne = ⊥-elim (na dn)
    where
    dn : (i : I) → P i
    dn i with lem (P i)
    ... | inj₁ p  = p
    ... | inj₂ np = ⊥-elim (ne (i , np))

  dich : ∀ {ℓ₁ ℓ₂} (a : V ℓ₁) (b : V ℓ₂) → a ≼ b ⊎ b ≺ a
  dich zero b = inj₁ z≼
  dich (lim f) b with lem ((n : ℕ) → f n ≼ b)
  ... | inj₁ h  = inj₁ (l≼ h)
  ... | inj₂ nh with notAll nh
  ...   | n , nf with dich (f n) b
  ...     | inj₁ x = ⊥-elim (nf x)
  ...     | inj₂ y = inj₂ (≼l n y)
  dich (Ω p g) b with lem ((z : Br _ p) → g z ≼ b)
  ... | inj₁ h  = inj₁ (Ω≼ h)
  ... | inj₂ nh with notAll nh
  ...   | z , nz with dich (g z) b
  ...     | inj₁ x = ⊥-elim (nz x)
  ...     | inj₂ y = inj₂ (≼Ω z y)
  dich (suc a) zero = inj₂ (s≼s z≼)
  dich (suc a) (suc b) with dich a b
  ... | inj₁ x = inj₁ (s≼s x)
  ... | inj₂ y = inj₂ (s≼s y)
  dich (suc a) (lim g) with lem ((n : ℕ) → g n ≼ a)
  ... | inj₁ h  = inj₂ (s≼s (l≼ h))
  ... | inj₂ nh with notAll nh
  ...   | n , ng with dich (suc a) (g n)
  ...     | inj₁ x = inj₁ (≼l n x)
  ...     | inj₂ y = ⊥-elim (ng (s≼s⁻ y))
  dich (suc a) (Ω p g) with lem ((z : Br _ p) → g z ≼ a)
  ... | inj₁ h  = inj₂ (s≼s (Ω≼ h))
  ... | inj₂ nh with notAll nh
  ...   | z , nz with dich (suc a) (g z)
  ...     | inj₁ x = inj₁ (≼Ω z x)
  ...     | inj₂ y = ⊥-elim (nz (s≼s⁻ y))

  tri : ∀ {ℓ₁ ℓ₂} (a : V ℓ₁) (b : V ℓ₂) → a ≼ b ⊎ b ≼ a
  tri a b with dich a b
  ... | inj₁ d = inj₁ d
  ... | inj₂ e = inj₂ (≺→≼ e)

  ⋠→≻ : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → ¬ (a ≼ b) → b ≺ a
  ⋠→≻ {a = a} {b} n with dich a b
  ... | inj₁ d = ⊥-elim (n d)
  ... | inj₂ e = e

  trich : ∀ {ℓ₁ ℓ₂} (a : V ℓ₁) (b : V ℓ₂) → a ≺ b ⊎ (a ≈ b) ⊎ b ≺ a
  trich a b with dich a b
  ... | inj₂ e = inj₂ (inj₂ e)
  ... | inj₁ d with dich b a
  ...   | inj₁ d′ = inj₂ (inj₁ (d , d′))
  ...   | inj₂ e′ = inj₁ e′

  ext≼ : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → ((c : V ℓ₂) → c ≺ a → c ≺ b) → a ≼ b
  ext≼ {a = a} {b} h with dich a b
  ... | inj₁ d = d
  ... | inj₂ e = ⊥-elim (irr b (h b e))

  lim-split : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {b : V ℓ₂} → lim f ≼ b ⊎ Σ ℕ (λ n → b ≺ f n)
  lim-split {f = f} {b} with lem ((n : ℕ) → f n ≼ b)
  ... | inj₁ h = inj₁ (l≼ h)
  ... | inj₂ nh with notAll nh
  ...   | n , nf = inj₂ (n , ⋠→≻ nf)

  Ω-split : ∀ {ℓ₁ ℓ₂} {p : Pos ℓ₁} {g : Br ℓ₁ p → V ℓ₁} {b : V ℓ₂} → Ω p g ≼ b ⊎ Σ (Br ℓ₁ p) (λ z → b ≺ g z)
  Ω-split {p = p} {g} {b} with lem ((z : Br _ p) → g z ≼ b)
  ... | inj₁ h = inj₁ (Ω≼ h)
  ... | inj₂ nh with notAll nh
  ...   | z , nz = inj₂ (z , ⋠→≻ nz)
```

上确界的刻画：上界，且严格在 `b` 之下的值严格在某一项之下，则 `b` 与极限值相等。

```agda
  lim-sup : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {b : V ℓ₂} → ((n : ℕ) → f n ≼ b) →
    ((c : V ℓ₁) → c ≺ b → Σ ℕ λ n → c ≺ f n) → lim f ≈ b
  lim-sup ub ap = l≼ ub , ext≼ (λ c lt → ≼l (proj₁ (ap c lt)) (proj₂ (ap c lt)))

  Ω-sup : ∀ {ℓ₁ ℓ₂} {p : Pos ℓ₁} {g : Br ℓ₁ p → V ℓ₁} {b : V ℓ₂} → ((z : Br ℓ₁ p) → g z ≼ b) →
    ((c : V ℓ₁) → c ≺ b → Σ (Br ℓ₁ p) λ z → c ≺ g z) → Ω p g ≈ b
  Ω-sup ub ap = Ω≼ ub , ext≼ (λ c lt → ≼Ω (proj₁ (ap c lt)) (proj₂ (ap c lt)))
```

最小元：沿 `wf` 下降，每一步用排中律问 "有没有更小的见证"。

```agda
  Least : (P : VΣ → Set) → Set
  Least P = Σ VΣ λ m → P m × ((y : VΣ) → P y → proj₂ m ≼ proj₂ y)

  least-acc : (P : VΣ → Set) (x : VΣ) → Acc _⊏_ x → P x → Least P
  least-acc P x (acc r) px with lem (Σ VΣ λ y → P y × (y ⊏ x))
  ... | inj₁ (y , py , lt) = least-acc P y (r lt) py
  ... | inj₂ no = x , px , below
    where
    below : (y : VΣ) → P y → proj₂ x ≼ proj₂ y
    below y py with dich (proj₂ x) (proj₂ y)
    ... | inj₁ d  = d
    ... | inj₂ lt = ⊥-elim (no (y , py , lt))

  least : (P : VΣ → Set) {x : VΣ} → P x → Least P
  least P {x} px = least-acc P x (wf (proj₂ x)) px
```

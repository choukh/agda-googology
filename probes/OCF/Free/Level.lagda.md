# 无记号主线 (一): 层号与值层树

> **下标类型 `Ordᴵ`, 累积树族 `Ordᶜ`, 互模拟 $\cong$, 结构序, `HS`, `toLevel`, `FGH`.** 主线的最底层; 从 `src` 的 `OCF.BTBO` 只取 `Trich`, `Ord-Ord.iter`, `injᵃ` 三件.
> 脚本从 [Level](../Align/Level.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
> 唯一改写的代码: 原文 `ωᴵ ω′ : Ordᴵ` 的 `ω′` 没有用处, 只有它需要 `_+ᴺ_`, 删掉. 不再导入 `OCF.Barrier`, `OCF.Align.Cumsum`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Level where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Trich; module Ord-Ord; injᵃ; injᵇ; injᶜ)
```

```agda
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open Ord-Ord using (iter)

```

## §1 下标类型 `Ordᴵ`

```agda
infix 4 _<ᴵ_ _≅ᴵ_ _⊑ᴵ_ _≺ᴵ_
data Ordᴵ : Set
data _<ᴵ_ : Ordᴵ → Ordᴵ → Set
data _≅ᴵ_ : Ordᴵ → Ordᴵ → Set
data _⊑ᴵ_ : Ordᴵ → Ordᴵ → Set

data Ordᴵ where
  zero : Ordᴵ
  suc  : Ordᴵ → Ordᴵ
  lim  : (f : ℕ → Ordᴵ) (s : ∀ n → f n ⊑ᴵ f (suc n)) → Ordᴵ

data _<ᴵ_ where
  zero : ∀ {a} → a <ᴵ suc a
  suc  : ∀ {a b} → a <ᴵ b → a <ᴵ suc b
  lim  : ∀ {a} {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → a <ᴵ f n → a <ᴵ lim f s

data _≅ᴵ_ where
  z≅ : zero ≅ᴵ zero
  s≅ : ∀ {a b} → a ≅ᴵ b → suc a ≅ᴵ suc b
  l≅ : ∀ {f g : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} {t : ∀ n → g n ⊑ᴵ g (suc n)} →
       (∀ n → f n ≅ᴵ g n) → lim f s ≅ᴵ lim g t

data _⊑ᴵ_ where
  z⊑ : ∀ {b} → zero ⊑ᴵ b
  s⊑ : ∀ {a a′ b} → a ≅ᴵ a′ → a′ <ᴵ b → suc a ⊑ᴵ b
  l⊑ : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} {b} → (∀ n → f n ⊑ᴵ b) → lim f s ⊑ᴵ b

data _≺ᴵ_ (a b : Ordᴵ) : Set where
  via : ∀ {a′} → a ≅ᴵ a′ → a′ <ᴵ b → a ≺ᴵ b
```

```agda
≅ᴵ-refl : ∀ a → a ≅ᴵ a
≅ᴵ-refl zero      = z≅
≅ᴵ-refl (suc a)   = s≅ (≅ᴵ-refl a)
≅ᴵ-refl (lim f s) = l≅ (λ n → ≅ᴵ-refl (f n))

≅ᴵ-sym : ∀ {a b} → a ≅ᴵ b → b ≅ᴵ a
≅ᴵ-sym z≅     = z≅
≅ᴵ-sym (s≅ e) = s≅ (≅ᴵ-sym e)
≅ᴵ-sym (l≅ h) = l≅ (λ n → ≅ᴵ-sym (h n))

≅ᴵ-trans : ∀ {a b c} → a ≅ᴵ b → b ≅ᴵ c → a ≅ᴵ c
≅ᴵ-trans z≅     z≅      = z≅
≅ᴵ-trans (s≅ e) (s≅ e′) = s≅ (≅ᴵ-trans e e′)
≅ᴵ-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅ᴵ-trans (h n) (h′ n))

<ᴵ-trans : ∀ {a b c} → a <ᴵ b → b <ᴵ c → a <ᴵ c
<ᴵ-trans p zero      = suc p
<ᴵ-trans p (suc q)   = suc (<ᴵ-trans p q)
<ᴵ-trans p (lim n q) = lim n (<ᴵ-trans p q)
```

```agda
<-≅ : ∀ {c a a′} → c <ᴵ a → a ≅ᴵ a′ → c ≺ᴵ a′
<-≅ zero      (s≅ e) = via e zero
<-≅ (suc p)   (s≅ e) with <-≅ p e
... | via e′ q = via e′ (suc q)
<-≅ (lim n p) (l≅ h) with <-≅ p (h n)
... | via e′ q = via e′ (lim n q)

≺ᴵ-respˡ : ∀ {a a′ b} → a′ ≅ᴵ a → a ≺ᴵ b → a′ ≺ᴵ b
≺ᴵ-respˡ e (via e′ q) = via (≅ᴵ-trans e e′) q

≺ᴵ-respʳ : ∀ {a b b′} → a ≺ᴵ b → b ≅ᴵ b′ → a ≺ᴵ b′
≺ᴵ-respʳ (via e q) e′ = ≺ᴵ-respˡ e (<-≅ q e′)

≺ᴵ-trans : ∀ {a b c} → a ≺ᴵ b → b ≺ᴵ c → a ≺ᴵ c
≺ᴵ-trans (via e q) (via e′ r) with <-≅ q e′
... | via e″ q′ = via (≅ᴵ-trans e e″) (<ᴵ-trans q′ r)

sim : ∀ {a b c} → a ⊑ᴵ b → c <ᴵ a → c ≺ᴵ b
sim (s⊑ e q) zero      = via e q
sim (s⊑ e q) (suc p)   = ≺ᴵ-trans (<-≅ p e) (via (≅ᴵ-refl _) q)
sim (l⊑ h)   (lim n p) = sim (h n) p

⊑ᴵ-trans : ∀ {a b c} → a ⊑ᴵ b → b ⊑ᴵ c → a ⊑ᴵ c
⊑ᴵ-trans z⊑       r = z⊑
⊑ᴵ-trans (s⊑ e q) r with sim r q
... | via e′ q′ = s⊑ (≅ᴵ-trans e e′) q′
⊑ᴵ-trans (l⊑ h)   r = l⊑ (λ n → ⊑ᴵ-trans (h n) r)

steps : ∀ {f : ℕ → Ordᴵ} → (∀ n → f n ⊑ᴵ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊑ᴵ f m
steps s zero    = s _
steps s (suc p) = ⊑ᴵ-trans (steps s p) (s _)

Sim→⊑ᴵ : ∀ {a b} → (∀ {c} → c <ᴵ a → c <ᴵ b) → a ⊑ᴵ b
Sim→⊑ᴵ {a = zero}    σ = z⊑
Sim→⊑ᴵ {a = suc a}   σ = s⊑ (≅ᴵ-refl a) (σ zero)
Sim→⊑ᴵ {a = lim f s} σ = l⊑ (λ n → Sim→⊑ᴵ (λ q → σ (lim n q)))

⊑ᴵ-refl : ∀ {a} → a ⊑ᴵ a
⊑ᴵ-refl = Sim→⊑ᴵ (λ q → q)
```

```agda
<ᴵ-dec : ∀ {a b c} → a <ᴵ c → b <ᴵ c → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
<ᴵ-dec zero    zero    = injᶜ (≅ᴵ-refl _)
<ᴵ-dec zero    (suc q) = injᵇ (via (≅ᴵ-refl _) q)
<ᴵ-dec (suc p) zero    = injᵃ (via (≅ᴵ-refl _) p)
<ᴵ-dec (suc p) (suc q) = <ᴵ-dec p q
<ᴵ-dec (lim {s = s} n p) (lim m q) with <ᴺ-dec n m
... | injᵃ n<m with sim (steps s n<m) p
...   | via e p′ = shift e (<ᴵ-dec p′ q) where
  shift : ∀ {a a′ b} → a ≅ᴵ a′ → a′ ≺ᴵ b ⊎ b ≺ᴵ a′ ⊎ a′ ≅ᴵ b → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
  shift e (injᵃ r) = injᵃ (≺ᴵ-respˡ e r)
  shift e (injᵇ r) = injᵇ (≺ᴵ-respʳ r (≅ᴵ-sym e))
  shift e (injᶜ r) = injᶜ (≅ᴵ-trans e r)
<ᴵ-dec (lim {s = s} n p) (lim m q) | injᵇ m<n with sim (steps s m<n) q
...   | via e q′ = shift e (<ᴵ-dec p q′) where
  shift : ∀ {a b b′} → b ≅ᴵ b′ → a ≺ᴵ b′ ⊎ b′ ≺ᴵ a ⊎ a ≅ᴵ b′ → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
  shift e (injᵃ r) = injᵃ (≺ᴵ-respʳ r (≅ᴵ-sym e))
  shift e (injᵇ r) = injᵇ (≺ᴵ-respˡ e r)
  shift e (injᶜ r) = injᶜ (≅ᴵ-trans r (≅ᴵ-sym e))
<ᴵ-dec (lim n p) (lim m q) | injᶜ refl = <ᴵ-dec p q

data Accᴵ (a : Ordᴵ) : Set where
  acc : (∀ {b} → b <ᴵ a → Accᴵ b) → Accᴵ a

accᴵ : ∀ a {b} → b <ᴵ a → Accᴵ b
accᴵ (suc a)   zero      = acc (accᴵ a)
accᴵ (suc a)   (suc p)   = accᴵ a p
accᴵ (lim f s) (lim n p) = accᴵ (f n) p

≺ᴵ-irrefl : ∀ {a} → ¬ (a ≺ᴵ a)
≺ᴵ-irrefl {a} = go (acc (accᴵ a)) where
  go : ∀ {a} → Accᴵ a → ¬ (a ≺ᴵ a)
  go (acc h) (via e q) = go (h q) (<-≅ q e)
```

## §2 第一种情况不能是字面的

```agda
natᴵ : ℕ → Ordᴵ
natᴵ zero    = zero
natᴵ (suc n) = suc (natᴵ n)

natᴵ-step : ∀ m → natᴵ m ⊑ᴵ natᴵ (suc m)
natᴵ-step m = Sim→⊑ᴵ suc

ωᴵ : Ordᴵ
ωᴵ = lim natᴵ natᴵ-step
```

## §4 树族、层间搬运与折叠

```agda
infix 4 _◃_ _◃₁_

data _◃_ : Ordᴵ → Ordᴵ → Set where
  zero : ∀ {a} → a ◃ suc a
  suc  : ∀ {a b} → a ◃ b → a ◃ suc b
  self : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → f n ◃ lim f s
  lim  : ∀ {a} {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → a ◃ f n → a ◃ lim f s

data _◃₁_ : Ordᴵ → Ordᴵ → Set where
  zero : ∀ {a} → a ◃₁ suc a
  self : ∀ {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → f n ◃₁ lim f s

<→◃ : ∀ {a b} → a <ᴵ b → a ◃ b
<→◃ zero      = zero
<→◃ (suc p)   = suc (<→◃ p)
<→◃ (lim n p) = lim n (<→◃ p)

◃₁→◃ : ∀ {a b} → a ◃₁ b → a ◃ b
◃₁→◃ zero     = zero
◃₁→◃ (self n) = self n

Simᴵ : Ordᴵ → Ordᴵ → Set
Simᴵ a b = ∀ {c} → c <ᴵ a → c <ᴵ b

module _ (ℓ : Ordᴵ) (U : (i : Ordᴵ) → i ◃ ℓ → Set) where
  data Ord₊ : Set where
    zero : Ord₊
    suc  : Ord₊ → Ord₊
    lim  : (f : ℕ → Ord₊) → Ord₊
    limᵢ : ∀ {i} (p : i <ᴵ ℓ) (f : U i (<→◃ p) → Ord₊) → Ord₊
    up   : ∀ {k} (r : k ◃₁ ℓ) (x : U k (◃₁→◃ r)) → Ord₊

U : ∀ {ℓ} (i : Ordᴵ) → i ◃ ℓ → Set
U i zero         = Ord₊ i U
U i (suc r)      = U i r
U _ (self {f} n) = Ord₊ (f n) U
U i (lim n r)    = U i r

Ordᶜ : Ordᴵ → Set
Ordᶜ ℓ = Ord₊ ℓ U

out : ∀ {i ℓ} (r : i ◃ ℓ) → U i r → Ordᶜ i
out zero      x = x
out (suc r)   x = out r x
out (self n)  x = x
out (lim n r) x = out r x

into : ∀ {i ℓ} (r : i ◃ ℓ) → Ordᶜ i → U i r
into zero      x = x
into (suc r)   x = into r x
into (self n)  x = x
into (lim n r) x = into r x

out-into : ∀ {i ℓ} (r : i ◃ ℓ) (x : Ordᶜ i) → out r (into r x) ≡ x
out-into zero      x = refl
out-into (suc r)   x = out-into r x
out-into (self n)  x = refl
out-into (lim n r) x = out-into r x
```

```agda
record Restr (j b : Ordᴵ) : Set where
  constructor restr
  field
    {rep} : Ordᴵ
    eq    : j ≅ᴵ rep
    lt    : rep <ᴵ b
    back  : Ordᶜ rep → Ordᶜ j
open Restr

tr   : ∀ {a b} → a ≅ᴵ b → Ordᶜ a → Ordᶜ b
tr⁻  : ∀ {a b} → a ≅ᴵ b → Ordᶜ b → Ordᶜ a
res  : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → Restr j b
res⁻ : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → Restr j a

tr e zero    = zero
tr e (suc x) = suc (tr e x)
tr e (lim f) = lim (λ n → tr e (f n))
tr e (limᵢ q f) = limᵢ (lt (res q e)) (λ y → tr e (f (into (<→◃ q) (back (res q e) (out (<→◃ (lt (res q e))) y)))))
tr (s≅ e) (up zero x)     = up zero (tr e x)
tr (l≅ h) (up (self n) x) = up (self n) (tr (h n) x)

tr⁻ e zero    = zero
tr⁻ e (suc x) = suc (tr⁻ e x)
tr⁻ e (lim f) = lim (λ n → tr⁻ e (f n))
tr⁻ e (limᵢ q f) = limᵢ (lt (res⁻ q e)) (λ y → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) (out (<→◃ (lt (res⁻ q e))) y)))))
tr⁻ (s≅ e) (up zero x)     = up zero (tr⁻ e x)
tr⁻ (l≅ h) (up (self n) x) = up (self n) (tr⁻ (h n) x)

res zero      (s≅ e) = restr e zero (tr⁻ e)
res (suc q)   (s≅ e) = restr (eq (res q e)) (suc (lt (res q e))) (back (res q e))
res (lim n q) (l≅ h) = restr (eq (res q (h n))) (lim n (lt (res q (h n)))) (back (res q (h n)))

res⁻ zero      (s≅ e) = restr (≅ᴵ-sym e) zero (tr e)
res⁻ (suc q)   (s≅ e) = restr (eq (res⁻ q e)) (suc (lt (res⁻ q e))) (back (res⁻ q e))
res⁻ (lim n q) (l≅ h) = restr (eq (res⁻ q (h n))) (lim n (lt (res⁻ q (h n)))) (back (res⁻ q (h n)))
```

```agda

FGH : Ordᶜ zero → ℕ → ℕ
FGH zero        n = suc n
FGH (suc a)     n = iter (FGH a) n n
FGH (lim f)     n = FGH (f n) n
FGH (limᵢ () f) n
FGH (up () x)   n
```

## §5 跨层结构互模拟 $\cong$

```agda
module _ (ℓ : Ordᴵ) (R : (i : Ordᴵ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set) where
  data Eq₊ : ∀ {ℓ′} → Ordᶜ ℓ → Ordᶜ ℓ′ → Set where
    z≅  : ∀ {ℓ′} → Eq₊ {ℓ′} zero zero
    s≅  : ∀ {ℓ′} {a : Ordᶜ ℓ} {b : Ordᶜ ℓ′} → Eq₊ a b → Eq₊ (suc a) (suc b)
    l≅  : ∀ {ℓ′} {f : ℕ → Ordᶜ ℓ} {g : ℕ → Ordᶜ ℓ′} → (∀ n → Eq₊ (f n) (g n)) → Eq₊ (lim f) (lim g)
    lᵢ≅ : ∀ {ℓ′ j j′} {p : j <ᴵ ℓ} {q : j′ <ᴵ ℓ′} {f : U j (<→◃ p) → Ordᶜ ℓ} {g : U j′ (<→◃ q) → Ordᶜ ℓ′} →
          j ≅ᴵ j′ →
          (∀ (x : Ordᶜ j) (y : Ordᶜ j′) → R j (<→◃ p) (into (<→◃ p) x) y → Eq₊ (f (into (<→◃ p) x)) (g (into (<→◃ q) y))) →
          Eq₊ (limᵢ p f) (limᵢ q g)
    upˡ : ∀ {ℓ′ k} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} {b : Ordᶜ ℓ′} → R k (◃₁→◃ r) x b → Eq₊ (up r x) b
    upʳ : ∀ {ℓ′ k} {r : k ◃₁ ℓ′} {y : U k (◃₁→◃ r)} {a : Ordᶜ ℓ} → Eq₊ a (out (◃₁→◃ r) y) → Eq₊ a (up r y)

R : ∀ {ℓ} (i : Ordᴵ) (r : i ◃ ℓ) → U i r → ∀ {ℓ′} → Ordᶜ ℓ′ → Set
R i zero         x b = Eq₊ i R x b
R i (suc r)      x b = R i r x b
R _ (self {f} n) x b = Eq₊ (f n) R x b
R i (lim n r)    x b = R i r x b

infix 4 _≅_
_≅_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
_≅_ {ℓ₁} = Eq₊ ℓ₁ R

R→≅ : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → R i r (into r x) b → x ≅ b
R→≅ zero      e = e
R→≅ (suc r)   e = R→≅ r e
R→≅ (self n)  e = e
R→≅ (lim n r) e = R→≅ r e

≅→R : ∀ {i ℓ ℓ′} (r : i ◃ ℓ) {x : Ordᶜ i} {b : Ordᶜ ℓ′} → x ≅ b → R i r (into r x) b
≅→R zero      e = e
≅→R (suc r)   e = ≅→R r e
≅→R (self n)  e = e
≅→R (lim n r) e = ≅→R r e
```

```agda
≅-sym   : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → b ≅ a
R-flip  : ∀ {j j′ ℓ₁ ℓ₂} (r : j ◃ ℓ₁) (r′ : j′ ◃ ℓ₂) {x : Ordᶜ j} {y : Ordᶜ j′} → R j r (into r x) y → R j′ r′ (into r′ y) x
flipR   : ∀ {j j′ ℓ₂} (r′ : j′ ◃ ℓ₂) {x : Ordᶜ j} {y : Ordᶜ j′} → x ≅ y → R j′ r′ (into r′ y) x
≅-sym z≅      = z≅
≅-sym (s≅ e)  = s≅ (≅-sym e)
≅-sym (l≅ h)  = l≅ (λ n → ≅-sym (h n))
≅-sym (lᵢ≅ {p = p} {q = q} e h) = lᵢ≅ (≅ᴵ-sym e) (λ y x d → ≅-sym (h x y (R-flip (<→◃ q) (<→◃ p) d)))
≅-sym (upˡ {r = zero} e)    = upʳ (≅-sym e)
≅-sym (upˡ {r = self n} e)  = upʳ (≅-sym e)
≅-sym (upʳ {r = zero} e)    = upˡ (≅-sym e)
≅-sym (upʳ {r = self n} e)  = upˡ (≅-sym e)
R-flip zero      r′ e = flipR r′ e
R-flip (suc r)   r′ e = R-flip r r′ e
R-flip (self n)  r′ e = flipR r′ e
R-flip (lim n r) r′ e = R-flip r r′ e
flipR zero       e = ≅-sym e
flipR (suc r′)   e = flipR r′ e
flipR (self n)   e = ≅-sym e
flipR (lim n r′) e = flipR r′ e
```

```agda
tr-≅    : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordᶜ a} {y : Ordᶜ ℓ′} → x ≅ y → tr e x ≅ y
tr⁻-≅   : ∀ {a b ℓ′} (e : a ≅ᴵ b) {x : Ordᶜ b} {y : Ordᶜ ℓ′} → x ≅ y → tr⁻ e x ≅ y
back-≅  : ∀ {j a b ℓ′} (q : j <ᴵ a) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res q e))} {v : Ordᶜ ℓ′} → u ≅ v → back (res q e) u ≅ v
back⁻-≅ : ∀ {j a b ℓ′} (q : j <ᴵ b) (e : a ≅ᴵ b) {u : Ordᶜ (rep (res⁻ q e))} {v : Ordᶜ ℓ′} → u ≅ v → back (res⁻ q e) u ≅ v

tr-≅ e z≅      = z≅
tr-≅ e (s≅ d)  = s≅ (tr-≅ e d)
tr-≅ e (l≅ h)  = l≅ (λ n → tr-≅ e (h n))
tr-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eq (res q e))) ej) λ u v d →
    subst (λ w → tr e (f (into (<→◃ q) (back (res q e) w))) ≅ g (into (<→◃ q₂) v))
          (sym (out-into (<→◃ (lt (res q e))) u))
          (tr-≅ e (h _ v (≅→R (<→◃ q) (back-≅ q e (R→≅ (<→◃ (lt (res q e))) d)))))
tr-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr-≅ e d)
tr-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (tr-≅ (h n) d)
tr-≅ e (upʳ d) = upʳ (tr-≅ e d)

tr⁻-≅ e z≅      = z≅
tr⁻-≅ e (s≅ d)  = s≅ (tr⁻-≅ e d)
tr⁻-≅ e (l≅ h)  = l≅ (λ n → tr⁻-≅ e (h n))
tr⁻-≅ e (lᵢ≅ {p = q} {q = q₂} {f = f} {g = g} ej h) =
  lᵢ≅ (≅ᴵ-trans (≅ᴵ-sym (eq (res⁻ q e))) ej) λ u v d →
    subst (λ w → tr⁻ e (f (into (<→◃ q) (back (res⁻ q e) w))) ≅ g (into (<→◃ q₂) v))
          (sym (out-into (<→◃ (lt (res⁻ q e))) u))
          (tr⁻-≅ e (h _ v (≅→R (<→◃ q) (back⁻-≅ q e (R→≅ (<→◃ (lt (res⁻ q e))) d)))))
tr⁻-≅ (s≅ e) (upˡ {r = zero} d)   = upˡ (tr⁻-≅ e d)
tr⁻-≅ (l≅ h) (upˡ {r = self n} d) = upˡ (tr⁻-≅ (h n) d)
tr⁻-≅ e (upʳ d) = upʳ (tr⁻-≅ e d)

back-≅ zero      (s≅ e) d = tr⁻-≅ e d
back-≅ (suc q)   (s≅ e) d = back-≅ q e d
back-≅ (lim n q) (l≅ h) d = back-≅ q (h n) d

back⁻-≅ zero      (s≅ e) d = tr-≅ e d
back⁻-≅ (suc q)   (s≅ e) d = back⁻-≅ q e d
back⁻-≅ (lim n q) (l≅ h) d = back⁻-≅ q (h n) d
```

```agda
≅-trans  : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ≅ b → b ≅ c → a ≅ c
R-reflˡ  : ∀ {j ℓ ℓ′} (r : j ◃ ℓ) {x : Ordᶜ j} {z : Ordᶜ ℓ′} → R j r (into r x) z → x ≅ x
≅-trans (upˡ {r = zero} e)   d = upˡ (≅-trans e d)
≅-trans (upˡ {r = self n} e) d = upˡ (≅-trans e d)
≅-trans d (upʳ {r = zero} e)   = upʳ (≅-trans d e)
≅-trans d (upʳ {r = self n} e) = upʳ (≅-trans d e)
≅-trans (upʳ {r = zero} e)   (upˡ e′) = ≅-trans e e′
≅-trans (upʳ {r = self n} e) (upˡ e′) = ≅-trans e e′
≅-trans z≅     z≅      = z≅
≅-trans (s≅ e) (s≅ e′) = s≅ (≅-trans e e′)
≅-trans (l≅ h) (l≅ h′) = l≅ (λ n → ≅-trans (h n) (h′ n))
≅-trans (lᵢ≅ {p = p} {q = q} e h) (lᵢ≅ e′ h′) =
  lᵢ≅ (≅ᴵ-trans e e′) λ x z d →
    ≅-trans (h x (tr e x) (≅→R (<→◃ p) (≅-sym (tr-≅ e (R-reflˡ (<→◃ p) d)))))
            (h′ (tr e x) z (≅→R (<→◃ q) (tr-≅ e (R→≅ (<→◃ p) d))))
R-reflˡ zero      e = ≅-trans e (≅-sym e)
R-reflˡ (suc r)   e = R-reflˡ r e
R-reflˡ (self n)  e = ≅-trans e (≅-sym e)
R-reflˡ (lim n r) e = R-reflˡ r e

≅-tr : ∀ {a b ℓ′} (e : a ≅ᴵ b) {y : Ordᶜ ℓ′} {x : Ordᶜ a} → y ≅ x → y ≅ tr e x
≅-tr e d = ≅-sym (tr-≅ e (≅-sym d))
```

## §6 折叠尊重 $\cong$

```agda
iter-R : ∀ {A B : Set} (Rel : A → B → Set) {G : A → A} {G′ : B → B} →
         (∀ {x y} → Rel x y → Rel (G x) (G′ y)) → ∀ {x y} → Rel x y → ∀ n → Rel (iter G x n) (iter G′ y n)
iter-R Rel h e zero    = e
iter-R Rel h e (suc n) = h (iter-R Rel h e n)

clash₁ : ∀ {j j′ i i′} → j ≅ᴵ j′ → i ≅ᴵ i′ → j ≺ᴵ i → i′ ≺ᴵ j′ → ⊥
clash₁ e ei r s = ≺ᴵ-irrefl (≺ᴵ-respʳ (≺ᴵ-trans (≺ᴵ-respʳ r ei) s) (≅ᴵ-sym e))

clash₂ : ∀ {j j′ i i′} → j ≅ᴵ j′ → i ≅ᴵ i′ → j ≺ᴵ i → j′ ≅ᴵ i′ → ⊥
clash₂ e ei r c = ≺ᴵ-irrefl (≺ᴵ-respʳ r (≅ᴵ-trans ei (≅ᴵ-trans (≅ᴵ-sym c) (≅ᴵ-sym e))))
```

```agda
iter-ext : ∀ {f g : ℕ → ℕ} → (∀ m → f m ≡ g m) → ∀ a n → iter f a n ≡ iter g a n
iter-ext h a zero    = refl
iter-ext {g = g} h a (suc n) = trans (h _) (cong g (iter-ext h a n))

FGH-≅ : ∀ {x y : Ordᶜ zero} → x ≅ y → ∀ n → FGH x n ≡ FGH y n
FGH-≅ z≅     n = refl
FGH-≅ (s≅ e) n = iter-ext (FGH-≅ e) n n
FGH-≅ (l≅ h) n = FGH-≅ (h n) n
FGH-≅ (lᵢ≅ {p = ()} e h) n
FGH-≅ (upˡ {r = ()} e) n
FGH-≅ (upʳ {r = ()} e) n
```

## §7 叶子为 $\cong$ 的结构序

```agda
infix 4 _≺_ _⊑_
data _≺_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set where
  ≺z : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≅ b → c ≺ suc b
  ≺s : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → c ≺ b → c ≺ suc b
  ≺l : ∀ {ℓ₁ ℓ₂} {c : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → c ≺ f n → c ≺ lim f
  ≺i : ∀ {ℓ₁ ℓ₂ j} {c : Ordᶜ ℓ₁} {p : j <ᴵ ℓ₂} {f : U j (<→◃ p) → Ordᶜ ℓ₂}
       (x : Ordᶜ j) → x ≅ x → c ≺ f (into (<→◃ p) x) → c ≺ limᵢ p f
  ≺u : ∀ {ℓ₁ ℓ₂ k} {c : Ordᶜ ℓ₁} {r : k ◃₁ ℓ₂} {y : U k (◃₁→◃ r)} → c ≺ out (◃₁→◃ r) y → c ≺ up r y

_⊑_ : ∀ {ℓ₁ ℓ₂} → Ordᶜ ℓ₁ → Ordᶜ ℓ₂ → Set
a ⊑ b = ∀ {ℓ} {c : Ordᶜ ℓ} → c ≺ a → c ≺ b

≺-respʳ : ∀ {ℓ₁ ℓ₂ ℓ₃} {c : Ordᶜ ℓ₁} {a : Ordᶜ ℓ₂} {b : Ordᶜ ℓ₃} → c ≺ a → a ≅ b → c ≺ b
≺-respʳ h (upʳ {r = zero} e)   = ≺u (≺-respʳ h e)
≺-respʳ h (upʳ {r = self n} e) = ≺u (≺-respʳ h e)
≺-respʳ (≺u {r = zero} h)   (upˡ e) = ≺-respʳ h e
≺-respʳ (≺u {r = self n} h) (upˡ e) = ≺-respʳ h e
≺-respʳ (≺z e₀)   (s≅ e) = ≺z (≅-trans e₀ e)
≺-respʳ (≺s h)    (s≅ e) = ≺s (≺-respʳ h e)
≺-respʳ (≺l n h)  (l≅ e) = ≺l n (≺-respʳ h (e n))
≺-respʳ (≺i {p = p} x ex h) (lᵢ≅ e h′) =
  ≺i (tr e x) (tr-≅ e (≅-tr e ex)) (≺-respʳ h (h′ x (tr e x) (≅→R (<→◃ p) (≅-tr e ex))))

≅→⊑ : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → a ≅ b → a ⊑ b
≅→⊑ e h = ≺-respʳ h e

⊑-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} {c : Ordᶜ ℓ₃} → a ⊑ b → b ⊑ c → a ⊑ c
⊑-trans p q h = q (p h)

⊑-lim : ∀ {ℓ₁ ℓ₂} {a : Ordᶜ ℓ₁} {f : ℕ → Ordᶜ ℓ₂} n → a ⊑ f n → a ⊑ lim f
⊑-lim n p h = ≺l n (p h)

lim-⊑ : ∀ {ℓ₁ ℓ₂} {f : ℕ → Ordᶜ ℓ₁} {b : Ordᶜ ℓ₂} → (∀ n → f n ⊑ b) → lim f ⊑ b
lim-⊑ k (≺l n h) = k n h
```

## §9 遗传步进 `HS` 与证书 `toLevel`

```agda
infix 4 _⊑⁰_
_⊑⁰_ : Ordᶜ zero → Ordᶜ zero → Set
a ⊑⁰ b = a ⊑ b

data HS : Ordᶜ zero → Set where
  hz : HS zero
  hs : ∀ {a} → HS a → HS (suc a)
  hl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → HS (f n)) → (∀ n → f n ⊑⁰ f (suc n)) → HS (lim f)

hs⁻ : ∀ {a} → HS (suc a) → HS a
hs⁻ (hs h) = h

hl₁ : ∀ {f : ℕ → Ordᶜ zero} → HS (lim f) → ∀ n → HS (f n)
hl₁ (hl h st) = h

hl₂ : ∀ {f : ℕ → Ordᶜ zero} → HS (lim f) → ∀ n → f n ⊑⁰ f (suc n)
hl₂ (hl h st) = st

≅-refl⁰ : (x : Ordᶜ zero) → x ≅ x
≅-refl⁰ zero        = z≅
≅-refl⁰ (suc x)     = s≅ (≅-refl⁰ x)
≅-refl⁰ (lim f)     = l≅ (λ n → ≅-refl⁰ (f n))
≅-refl⁰ (limᵢ () f)
≅-refl⁰ (up () x)
```

```agda
s⊑′ : ∀ {a b} → a ≺ᴵ b → suc a ⊑ᴵ b
s⊑′ (via e q) = s⊑ e q

≺-suc : ∀ {a b} → a ≺ᴵ b → a ≺ᴵ suc b
≺-suc (via e q) = via e (suc q)

≺-lim : ∀ {a} {f : ℕ → Ordᴵ} {s : ∀ n → f n ⊑ᴵ f (suc n)} n → a ≺ᴵ f n → a ≺ᴵ lim f s
≺-lim n (via e q) = via e (lim n q)

toLevel   : (x : Ordᶜ zero) → HS x → Ordᴵ
toLevel-⊑ : ∀ {a b} (ha : HS a) (hb : HS b) → a ⊑⁰ b → toLevel a ha ⊑ᴵ toLevel b hb
toLevel-≺ : ∀ {c b} (hc : HS c) (hb : HS b) → c ≺ b → toLevel c hc ≺ᴵ toLevel b hb
toLevel-≅ : ∀ {a b} (ha : HS a) (hb : HS b) → a ≅ b → toLevel a ha ≅ᴵ toLevel b hb

toLevel zero        h = zero
toLevel (suc a)     h = suc (toLevel a (hs⁻ h))
toLevel (lim f)     h = lim (λ n → toLevel (f n) (hl₁ h n)) (λ n → toLevel-⊑ (hl₁ h n) (hl₁ h (suc n)) (hl₂ h n))
toLevel (limᵢ () f) h
toLevel (up () x)   h

toLevel-⊑ {a = zero}      ha hb k = z⊑
toLevel-⊑ {a = suc a}     ha hb k = s⊑′ (toLevel-≺ (hs⁻ ha) hb (k (≺z (≅-refl⁰ a))))
toLevel-⊑ {a = lim f}     ha hb k = l⊑ (λ n → toLevel-⊑ (hl₁ ha n) hb (λ d → k (≺l n d)))
toLevel-⊑ {a = limᵢ () f} ha hb k
toLevel-⊑ {a = up () x}   ha hb k

toLevel-≺ hc hb (≺z e)   = via (toLevel-≅ hc (hs⁻ hb) e) zero
toLevel-≺ hc hb (≺s d)   = ≺-suc (toLevel-≺ hc (hs⁻ hb) d)
toLevel-≺ hc hb (≺l n d) = ≺-lim n (toLevel-≺ hc (hl₁ hb n) d)
toLevel-≺ hc hb (≺i {p = ()} x ex d)
toLevel-≺ hc hb (≺u {r = ()} d)

toLevel-≅ ha hb z≅     = z≅
toLevel-≅ ha hb (s≅ e) = s≅ (toLevel-≅ (hs⁻ ha) (hs⁻ hb) e)
toLevel-≅ ha hb (l≅ k) = l≅ (λ n → toLevel-≅ (hl₁ ha n) (hl₁ hb n) (k n))
toLevel-≅ ha hb (lᵢ≅ {p = ()} e k)
toLevel-≅ ha hb (upˡ {r = ()} e)
toLevel-≅ ha hb (upʳ {r = ()} e)
```

## §12 结论与边界

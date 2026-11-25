# 新块的 View：值
> 成品候选。来源：`YiLPVal` 的定义与证明；旧层号的三种分支合并为 `nd s h`。
> 编译定理：跨层值前序自反传递、抬升保值、第一位置单调、值合法与加法保值；不改块、折叠或合法性。
> View 在 `YiVWView`，部分良基在 `YiVWWf`；不作强度验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVWVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (_+_)

chL : (ℓ : L) → CH ℓ → L
chL (nd s h) c = h c

chP : (ℓ : L) (c : CH ℓ) → Pos (chL ℓ c) → Pos ℓ
chP (nd s h) c p = inj₂ (c , inj₂ p)

chBr : (ℓ : L) (c : CH ℓ) (p : Pos (chL ℓ c)) → Br ℓ (chP ℓ c p) → Br (chL ℓ c) p
chBr (nd s h) c p z = z

br0 : (ℓ : L) (p : Pos ℓ) → Br ℓ p
br0 ℓ p = fromBr ℓ p zero

data V (ℓ : L) : Set where
  zero : V ℓ
  suc  : V ℓ → V ℓ
  lim  : (ℕ → V ℓ) → V ℓ
  Ω    : (p : Pos ℓ) → (Br ℓ p → V ℓ) → V ℓ

infixl 6 _⊹_
_⊹_ : ∀ {ℓ} → V ℓ → V ℓ → V ℓ
a ⊹ zero  = a
a ⊹ suc b = suc (a ⊹ b)
a ⊹ lim f = lim (λ n → a ⊹ f n)
a ⊹ Ω p g = Ω p (λ z → a ⊹ g z)

emb : (ℓ : L) (c : CH ℓ) → V (chL ℓ c) → V ℓ
emb ℓ c zero    = zero
emb ℓ c (suc v) = suc (emb ℓ c v)
emb ℓ c (lim f) = lim (λ n → emb ℓ c (f n))
emb ℓ c (Ω p g) = Ω (chP ℓ c p) (λ z → emb ℓ c (g (chBr ℓ c p z)))

chT : (ℓ : L) (c : CH ℓ) → ChT ℓ c → Tr (chL ℓ c)
chT zero     () y
chT (nd s h) c y = y

mutual
  val : (ℓ : L) → Tr ℓ → V ℓ
  val ℓ zero         = zero
  val ℓ (suc x)      = suc (val ℓ x)
  val ℓ (lim f _)    = lim (λ n → val ℓ (f n))
  val ℓ (Ω p g)      = Ω p (λ z → val ℓ (g z))
  val ℓ (up x c y _) = val ℓ x ⊹ valCh ℓ c y

  valCh : (ℓ : L) (c : CH ℓ) → ChT ℓ c → V ℓ
  valCh zero     () y
  valCh (nd s h) c y = emb (nd s h) c (val (h c) y)

infix 4 _≼_ _≈_
data _≼_ : {ℓ₁ ℓ₂ : L} → V ℓ₁ → V ℓ₂ → Set where
  z≼  : ∀ {ℓ₁ ℓ₂} {b : V ℓ₂} → zero {ℓ₁} ≼ b
  s≼s : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → a ≼ b → suc a ≼ suc b
  ≼l  : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {f : ℕ → V ℓ₂} (n : ℕ) → a ≼ f n → a ≼ lim f
  l≼  : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {b : V ℓ₂} → ((n : ℕ) → f n ≼ b) → lim f ≼ b
  ≼Ω  : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {p : Pos ℓ₂} {g : Br ℓ₂ p → V ℓ₂} (z : Br ℓ₂ p) → a ≼ g z → a ≼ Ω p g
  Ω≼  : ∀ {ℓ₁ ℓ₂} {p : Pos ℓ₁} {g : Br ℓ₁ p → V ℓ₁} {b : V ℓ₂} → ((z : Br ℓ₁ p) → g z ≼ b) → Ω p g ≼ b

_≈_ : ∀ {ℓ₁ ℓ₂} → V ℓ₁ → V ℓ₂ → Set
a ≈ b = (a ≼ b) × (b ≼ a)

≼-refl : ∀ {ℓ} (a : V ℓ) → a ≼ a
≼-refl zero    = z≼
≼-refl (suc a) = s≼s (≼-refl a)
≼-refl (lim f) = l≼ (λ n → ≼l n (≼-refl (f n)))
≼-refl (Ω p g) = Ω≼ (λ z → ≼Ω z (≼-refl (g z)))

lim⁻ : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {c : V ℓ₂} (n : ℕ) → lim f ≼ c → f n ≼ c
lim⁻ n (≼l m e)  = ≼l m (lim⁻ n e)
lim⁻ n (l≼ h)    = h n
lim⁻ n (≼Ω z e)  = ≼Ω z (lim⁻ n e)

Ω⁻ : ∀ {ℓ₁ ℓ₂ p} {g : Br ℓ₁ p → V ℓ₁} {c : V ℓ₂} (z : Br ℓ₁ p) → Ω p g ≼ c → g z ≼ c
Ω⁻ z (≼l m e)   = ≼l m (Ω⁻ z e)
Ω⁻ z (≼Ω z′ e)  = ≼Ω z′ (Ω⁻ z e)
Ω⁻ z (Ω≼ h)     = h z

mutual
  ≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≼ b → b ≼ c → a ≼ c
  ≼-trans z≼        e = z≼
  ≼-trans (s≼s d)   e = sucT d e
  ≼-trans (≼l n d)  e = ≼-trans d (lim⁻ n e)
  ≼-trans (l≼ h)    e = l≼ (λ n → ≼-trans (h n) e)
  ≼-trans (≼Ω z d)  e = ≼-trans d (Ω⁻ z e)
  ≼-trans (Ω≼ h)    e = Ω≼ (λ z → ≼-trans (h z) e)

  sucT : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≼ b → suc b ≼ c → suc a ≼ c
  sucT d (s≼s e)   = s≼s (≼-trans d e)
  sucT d (≼l n e)  = ≼l n (sucT d e)
  sucT d (≼Ω z e)  = ≼Ω z (sucT d e)

≈-refl : ∀ {ℓ} (a : V ℓ) → a ≈ a
≈-refl a = ≼-refl a , ≼-refl a

≈-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≈ b → b ≈ c → a ≈ c
≈-trans (d , d′) (e , e′) = ≼-trans d e , ≼-trans e′ d′

≼-suc : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → a ≼ b → a ≼ suc b
≼-suc z≼        = z≼
≼-suc (s≼s d)   = s≼s (≼-suc d)
≼-suc (≼l n d)  = ≼-trans (≼-suc d) (s≼s (≼l n (≼-refl _)))
≼-suc (l≼ h)    = l≼ (λ n → ≼-suc (h n))
≼-suc (≼Ω z d)  = ≼-trans (≼-suc d) (s≼s (≼Ω z (≼-refl _)))
≼-suc (Ω≼ h)    = Ω≼ (λ z → ≼-suc (h z))

≼⊹ : ∀ {ℓ} (a b : V ℓ) → a ≼ a ⊹ b
≼⊹ a zero    = ≼-refl a
≼⊹ a (suc b) = ≼-suc (≼⊹ a b)
≼⊹ a (lim f) = ≼l 0 (≼⊹ a (f 0))
≼⊹ {ℓ} a (Ω p g) = ≼Ω (br0 ℓ p) (≼⊹ a (g _))

⊹-mono : ∀ {ℓ} (a : V ℓ) {b b′ : V ℓ} → b ≼ b′ → a ⊹ b ≼ a ⊹ b′
⊹-mono a {b′ = b′} z≼ = ≼⊹ a b′
⊹-mono a (s≼s d)   = s≼s (⊹-mono a d)
⊹-mono a (≼l n d)  = ≼l n (⊹-mono a d)
⊹-mono a (l≼ h)    = l≼ (λ n → ⊹-mono a (h n))
⊹-mono a (≼Ω z d)  = ≼Ω z (⊹-mono a d)
⊹-mono a (Ω≼ h)    = Ω≼ (λ z → ⊹-mono a (h z))

⊹-monoˡ : ∀ {ℓ} {a a′ : V ℓ} → a ≼ a′ → (b : V ℓ) → a ⊹ b ≼ a′ ⊹ b
⊹-monoˡ d zero    = d
⊹-monoˡ d (suc b) = s≼s (⊹-monoˡ d b)
⊹-monoˡ d (lim f) = l≼ (λ n → ≼l n (⊹-monoˡ d (f n)))
⊹-monoˡ d (Ω p g) = Ω≼ (λ z → ≼Ω z (⊹-monoˡ d (g z)))

emb-mono : (ℓ : L) (c : CH ℓ) {v w : V (chL ℓ c)} → v ≼ w → emb ℓ c v ≼ emb ℓ c w
emb-mono zero     ()
emb-mono ℓ        c z≼        = z≼
emb-mono ℓ        c (s≼s d)   = s≼s (emb-mono ℓ c d)
emb-mono ℓ        c (≼l n d)  = ≼l n (emb-mono ℓ c d)
emb-mono ℓ        c (l≼ h)    = l≼ (λ n → emb-mono ℓ c (h n))
emb-mono (nd s h) c (≼Ω z d) = ≼Ω z (emb-mono (nd s h) c d)
emb-mono (nd s h) c (Ω≼ e) = Ω≼ (λ z → emb-mono (nd s h) c (e z))

F≈ : (ℓ : L) (c : CH ℓ) (a : V ℓ) {v w : V (chL ℓ c)} → v ≈ w → a ⊹ emb ℓ c v ≈ a ⊹ emb ℓ c w
F≈ ℓ c a (d , e) = ⊹-mono a (emb-mono ℓ c d) , ⊹-mono a (emb-mono ℓ c e)

emb-≼ : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → emb ℓ c v ≼ v
emb-≼ ℓ c zero    = z≼
emb-≼ ℓ c (suc v) = s≼s (emb-≼ ℓ c v)
emb-≼ ℓ c (lim f) = l≼ (λ n → ≼l n (emb-≼ ℓ c (f n)))
emb-≼ ℓ c (Ω p g) = Ω≼ (λ z → ≼Ω (chBr ℓ c p z) (emb-≼ ℓ c (g (chBr ℓ c p z))))

≼-emb : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → v ≼ emb ℓ c v
≼-emb zero     () v
≼-emb ℓ        c zero    = z≼
≼-emb ℓ        c (suc v) = s≼s (≼-emb ℓ c v)
≼-emb ℓ        c (lim f) = l≼ (λ n → ≼l n (≼-emb ℓ c (f n)))
≼-emb (nd s h) c (Ω p g) = Ω≼ (λ z → ≼Ω z (≼-emb (nd s h) c (g z)))

emb-≈ : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → emb ℓ c v ≈ v
emb-≈ ℓ c v = emb-≼ ℓ c v , ≼-emb ℓ c v

valCh-≈ : (ℓ : L) (c : CH ℓ) (y : ChT ℓ c) → valCh ℓ c y ≈ val (chL ℓ c) (chT ℓ c y)
valCh-≈ zero     () y
valCh-≈ (nd s h) c y = emb-≈ (nd s h) c (val (h c) y)

infix 4 _◁_
data _◁_ {ℓ : L} : V ℓ → V ℓ → Set where
  ◁s : ∀ {x} → x ◁ suc x
  ◁l : ∀ {f} (n : ℕ) → f n ◁ lim f
  ◁w : ∀ {p g} → g (br0 ℓ p) ◁ Ω p g
  ◁t : ∀ {x y z} → x ◁ y → y ◁ z → x ◁ z

◁→≼ : ∀ {ℓ} {x y : V ℓ} → x ◁ y → x ≼ y
◁→≼ ◁s       = ≼-suc (≼-refl _)
◁→≼ (◁l n)   = ≼l n (≼-refl _)
◁→≼ ◁w       = ≼Ω _ (≼-refl _)
◁→≼ (◁t d e) = ≼-trans (◁→≼ d) (◁→≼ e)

⊹-mono◁ : ∀ {ℓ} (a : V ℓ) {b b′ : V ℓ} → b ◁ b′ → a ⊹ b ◁ a ⊹ b′
⊹-mono◁ a ◁s       = ◁s
⊹-mono◁ a (◁l n)   = ◁l n
⊹-mono◁ a ◁w       = ◁w
⊹-mono◁ a (◁t d e) = ◁t (⊹-mono◁ a d) (⊹-mono◁ a e)

emb-mono◁ : (ℓ : L) (c : CH ℓ) {v w : V (chL ℓ c)} → v ◁ w → emb ℓ c v ◁ emb ℓ c w
emb-mono◁ zero     ()
emb-mono◁ ℓ        c ◁s       = ◁s
emb-mono◁ ℓ        c (◁l n)   = ◁l n
emb-mono◁ (nd s h) c ◁w = ◁w
emb-mono◁ ℓ        c (◁t d e) = ◁t (emb-mono◁ ℓ c d) (emb-mono◁ ℓ c e)

mutual
  val-mono : (ℓ : L) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → val ℓ x ◁ val ℓ y
  val-mono ℓ ◃s             = ◁s
  val-mono ℓ (◃l n)         = ◁l n
  val-mono ℓ ◃w             = ◁w
  val-mono ℓ (◃u x c y e)   = ⊹-mono◁ (val ℓ x) (valCh-mono₀ ℓ c y e)
  val-mono ℓ (◃c x c d)     = ⊹-mono◁ (val ℓ x) (valCh-mono ℓ c d)
  val-mono ℓ (◃t d e)       = ◁t (val-mono ℓ d) (val-mono ℓ e)

  valCh-mono₀ : (ℓ : L) (c : CH ℓ) (y : ChT ℓ c) → RCh ℓ c (chZ ℓ c) y → zero ◁ valCh ℓ c y
  valCh-mono₀ zero     () y d
  valCh-mono₀ (nd s h) c y d = emb-mono◁ (nd s h) c (val-mono (h c) d)

  valCh-mono : (ℓ : L) (c : CH ℓ) {y′ y : ChT ℓ c} → RCh ℓ c y′ y → valCh ℓ c y′ ◁ valCh ℓ c y
  valCh-mono zero     () d
  valCh-mono (nd s h) c d = emb-mono◁ (nd s h) c (val-mono (h c) d)

LegV : (ℓ : L) → V ℓ → Set
LegV ℓ zero    = ⊤
LegV ℓ (suc a) = LegV ℓ a
LegV ℓ (lim f) = ((n : ℕ) → LegV ℓ (f n)) × ((n : ℕ) → f n ◁ f (suc n))
LegV ℓ (Ω p g) = (z : Br ℓ p) → LegV ℓ (g z)

⊹-leg : ∀ {ℓ} (a b : V ℓ) → LegV ℓ a → LegV ℓ b → LegV ℓ (a ⊹ b)
⊹-leg a zero    ha hb = ha
⊹-leg a (suc b) ha hb = ⊹-leg a b ha hb
⊹-leg a (lim f) ha (hf , adj) = (λ n → ⊹-leg a (f n) ha (hf n)) , (λ n → ⊹-mono◁ a (adj n))
⊹-leg a (Ω p g) ha hb = λ z → ⊹-leg a (g z) ha (hb z)

emb-leg : (ℓ : L) (c : CH ℓ) (v : V (chL ℓ c)) → LegV (chL ℓ c) v → LegV ℓ (emb ℓ c v)
emb-leg zero     () v
emb-leg ℓ        c zero    h = tt
emb-leg ℓ        c (suc v) h = emb-leg ℓ c v h
emb-leg ℓ        c (lim f) (hf , adj) = (λ n → emb-leg ℓ c (f n) (hf n)) , (λ n → emb-mono◁ ℓ c (adj n))
emb-leg (nd s h) c (Ω p g) e = λ z → emb-leg (nd s h) c (g z) (e z)

mutual
  val-leg : (ℓ : L) (x : Tr ℓ) → LegV ℓ (val ℓ x)
  val-leg ℓ zero         = tt
  val-leg ℓ (suc x)      = val-leg ℓ x
  val-leg ℓ (lim f a)    = (λ n → val-leg ℓ (f n)) , (λ n → val-mono ℓ (a n))
  val-leg ℓ (Ω p g)      = λ z → val-leg ℓ (g z)
  val-leg ℓ (up x c y _) = ⊹-leg (val ℓ x) (valCh ℓ c y) (val-leg ℓ x) (valCh-leg ℓ c y)

  valCh-leg : (ℓ : L) (c : CH ℓ) (y : ChT ℓ c) → LegV ℓ (valCh ℓ c y)
  valCh-leg zero     () y
  valCh-leg (nd s h) c y = emb-leg (nd s h) c (val (h c) y) (val-leg (h c) y)

s≈ : ∀ {ℓ₁ ℓ₂} {a : V ℓ₁} {b : V ℓ₂} → a ≈ b → suc a ≈ suc b
s≈ (d , e) = s≼s d , s≼s e

l≈ : ∀ {ℓ₁ ℓ₂} {f : ℕ → V ℓ₁} {g : ℕ → V ℓ₂} → ((n : ℕ) → f n ≈ g n) → lim f ≈ lim g
l≈ e = l≼ (λ n → ≼l n (proj₁ (e n))) , l≼ (λ n → ≼l n (proj₂ (e n)))

Ω≈ : ∀ {ℓ} {p : Pos ℓ} {f g : Br ℓ p → V ℓ} → ((z : Br ℓ p) → f z ≈ g z) → Ω p f ≈ Ω p g
Ω≈ e = Ω≼ (λ z → ≼Ω z (proj₁ (e z))) , Ω≼ (λ z → ≼Ω z (proj₂ (e z)))

⊹-assoc : ∀ {ℓ} (a b c : V ℓ) → (a ⊹ b) ⊹ c ≈ a ⊹ (b ⊹ c)
⊹-assoc a b zero    = ≈-refl (a ⊹ b)
⊹-assoc a b (suc c) = s≈ (⊹-assoc a b c)
⊹-assoc a b (lim f) = l≈ (λ n → ⊹-assoc a b (f n))
⊹-assoc a b (Ω p g) = Ω≈ (λ z → ⊹-assoc a b (g z))

val-+ : ∀ {ℓ} (x y : Tr ℓ) → val ℓ (x + y) ≈ val ℓ x ⊹ val ℓ y
val-+ {ℓ} x zero         = ≈-refl (val ℓ x)
val-+ x (suc y)          = s≈ (val-+ x y)
val-+ x (lim f a)        = l≈ (λ n → val-+ x (f n))
val-+ x (Ω p g)          = Ω≈ (λ z → val-+ x (g z))
val-+ {ℓ} x (up y c w e) =
  ≈-trans (⊹-monoˡ (proj₁ (val-+ x y)) (valCh ℓ c w) , ⊹-monoˡ (proj₂ (val-+ x y)) (valCh ℓ c w))
          (⊹-assoc (val ℓ x) (val ℓ y) (valCh ℓ c w))
```

# 合法块的 View: 值

> 判决: 成品候选 (值). 与 `YiViewVal` 同文, 搬到合法块: 值类型 `V ℓ` 只有零, 后继, ℕ 极限, Ω 结点; Ω 结点的坐标是 `Br ℓ p`, 即低层的树, 在合法块里都合法, 所以值前序的 Ω 两条不再带 `LegBr`. `up x c y e` 读成 x 的值加上 y 的值抬进本层.
> 编译定理, 无前提: 值前序 `_≼_` (跨层) 自反传递; 抬升不改值 (`emb-≈`, `valCh-≈`); 加法与抬升对 `≼`, 对值的第一位置序 `_◁_` 单调; 树的第一位置序推出值的第一位置序 (`val-mono`), 所以值合法 (`val-leg`); 块的加法的值是值的加法 (`val-+`).
> 不否定什么. 没有搬 `YiViewVal.incl` (见文末). View 在 [YiLPView](YiLPView.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (_+_; chP; chBr)
```

## 值类型与值

```agda
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

emb : (ℓ : L) (c : Ch ℓ) → V (chL ℓ c) → V ℓ
emb ℓ c zero    = zero
emb ℓ c (suc v) = suc (emb ℓ c v)
emb ℓ c (lim f) = lim (λ n → emb ℓ c (f n))
emb ℓ c (Ω p g) = Ω (chP ℓ c p) (λ z → emb ℓ c (g (chBr ℓ c p z)))

chT : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → Tr (chL ℓ c)
chT zero     () y
chT (suc a)  _ y = y
chT (lim g)  n y = y
chT (Ωₗ k h) c y = y

mutual
  val : (ℓ : L) → Tr ℓ → V ℓ
  val ℓ zero         = zero
  val ℓ (suc x)      = suc (val ℓ x)
  val ℓ (lim f _)    = lim (λ n → val ℓ (f n))
  val ℓ (Ω p g)      = Ω p (λ z → val ℓ (g z))
  val ℓ (up x c y _) = val ℓ x ⊹ valCh ℓ c y

  valCh : (ℓ : L) (c : Ch ℓ) → ChT ℓ c → V ℓ
  valCh zero     () y
  valCh (suc a)  c y = emb (suc a) c (val a y)
  valCh (lim g)  n y = emb (lim g) n (val (g n) y)
  valCh (Ωₗ k h) c y = emb (Ωₗ k h) c (val (h c) y)
```

## 值前序

Ω 结点是一切低层树分支上的上确界.

```agda
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
```

## 加法与抬升对值前序单调; 抬升不改值

```agda
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

emb-mono : (ℓ : L) (c : Ch ℓ) {v w : V (chL ℓ c)} → v ≼ w → emb ℓ c v ≼ emb ℓ c w
emb-mono zero     ()
emb-mono ℓ        c z≼        = z≼
emb-mono ℓ        c (s≼s d)   = s≼s (emb-mono ℓ c d)
emb-mono ℓ        c (≼l n d)  = ≼l n (emb-mono ℓ c d)
emb-mono ℓ        c (l≼ h)    = l≼ (λ n → emb-mono ℓ c (h n))
emb-mono (suc a)  c (≼Ω z d)  = ≼Ω z (emb-mono (suc a) c d)
emb-mono (lim g)  n (≼Ω z d)  = ≼Ω z (emb-mono (lim g) n d)
emb-mono (Ωₗ k h) c (≼Ω z d)  = ≼Ω z (emb-mono (Ωₗ k h) c d)
emb-mono (suc a)  c (Ω≼ e)    = Ω≼ (λ z → emb-mono (suc a) c (e z))
emb-mono (lim g)  n (Ω≼ e)    = Ω≼ (λ z → emb-mono (lim g) n (e z))
emb-mono (Ωₗ k h) c (Ω≼ e)    = Ω≼ (λ z → emb-mono (Ωₗ k h) c (e z))

F≈ : (ℓ : L) (c : Ch ℓ) (a : V ℓ) {v w : V (chL ℓ c)} → v ≈ w → a ⊹ emb ℓ c v ≈ a ⊹ emb ℓ c w
F≈ ℓ c a (d , e) = ⊹-mono a (emb-mono ℓ c d) , ⊹-mono a (emb-mono ℓ c e)

emb-≼ : (ℓ : L) (c : Ch ℓ) (v : V (chL ℓ c)) → emb ℓ c v ≼ v
emb-≼ ℓ c zero    = z≼
emb-≼ ℓ c (suc v) = s≼s (emb-≼ ℓ c v)
emb-≼ ℓ c (lim f) = l≼ (λ n → ≼l n (emb-≼ ℓ c (f n)))
emb-≼ ℓ c (Ω p g) = Ω≼ (λ z → ≼Ω (chBr ℓ c p z) (emb-≼ ℓ c (g (chBr ℓ c p z))))

≼-emb : (ℓ : L) (c : Ch ℓ) (v : V (chL ℓ c)) → v ≼ emb ℓ c v
≼-emb zero     () v
≼-emb ℓ        c zero    = z≼
≼-emb ℓ        c (suc v) = s≼s (≼-emb ℓ c v)
≼-emb ℓ        c (lim f) = l≼ (λ n → ≼l n (≼-emb ℓ c (f n)))
≼-emb (suc a)  c (Ω p g) = Ω≼ (λ z → ≼Ω z (≼-emb (suc a) c (g z)))
≼-emb (lim g)  n (Ω p f) = Ω≼ (λ z → ≼Ω z (≼-emb (lim g) n (f z)))
≼-emb (Ωₗ k h) c (Ω p g) = Ω≼ (λ z → ≼Ω z (≼-emb (Ωₗ k h) c (g z)))

emb-≈ : (ℓ : L) (c : Ch ℓ) (v : V (chL ℓ c)) → emb ℓ c v ≈ v
emb-≈ ℓ c v = emb-≼ ℓ c v , ≼-emb ℓ c v

valCh-≈ : (ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → valCh ℓ c y ≈ val (chL ℓ c) (chT ℓ c y)
valCh-≈ zero     () y
valCh-≈ (suc a)  c y = emb-≈ (suc a) c (val a y)
valCh-≈ (lim g)  n y = emb-≈ (lim g) n (val (g n) y)
valCh-≈ (Ωₗ k h) c y = emb-≈ (Ωₗ k h) c (val (h c) y)
```

## 值的第一位置序

与树的第一位置序同形, 没有 `up` 的两条; 结点一条取第一分支 `br0`.

```agda
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

emb-mono◁ : (ℓ : L) (c : Ch ℓ) {v w : V (chL ℓ c)} → v ◁ w → emb ℓ c v ◁ emb ℓ c w
emb-mono◁ zero     ()
emb-mono◁ ℓ        c ◁s       = ◁s
emb-mono◁ ℓ        c (◁l n)   = ◁l n
emb-mono◁ (suc a)  c ◁w       = ◁w
emb-mono◁ (lim g)  n ◁w       = ◁w
emb-mono◁ (Ωₗ k h) c ◁w       = ◁w
emb-mono◁ ℓ        c (◁t d e) = ◁t (emb-mono◁ ℓ c d) (emb-mono◁ ℓ c e)

mutual
  val-mono : (ℓ : L) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → val ℓ x ◁ val ℓ y
  val-mono ℓ ◃s             = ◁s
  val-mono ℓ (◃l n)         = ◁l n
  val-mono ℓ ◃w             = ◁w
  val-mono ℓ (◃u x c y e)   = ⊹-mono◁ (val ℓ x) (valCh-mono₀ ℓ c y e)
  val-mono ℓ (◃c x c d)     = ⊹-mono◁ (val ℓ x) (valCh-mono ℓ c d)
  val-mono ℓ (◃t d e)       = ◁t (val-mono ℓ d) (val-mono ℓ e)

  valCh-mono₀ : (ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → RCh ℓ c (chZ ℓ c) y → zero ◁ valCh ℓ c y
  valCh-mono₀ zero     () y d
  valCh-mono₀ (suc a)  c y d = emb-mono◁ (suc a) c (val-mono a d)
  valCh-mono₀ (lim g)  n y d = emb-mono◁ (lim g) n (val-mono (g n) d)
  valCh-mono₀ (Ωₗ k h) c y d = emb-mono◁ (Ωₗ k h) c (val-mono (h c) d)

  valCh-mono : (ℓ : L) (c : Ch ℓ) {y′ y : ChT ℓ c} → RCh ℓ c y′ y → valCh ℓ c y′ ◁ valCh ℓ c y
  valCh-mono zero     () d
  valCh-mono (suc a)  c d = emb-mono◁ (suc a) c (val-mono a d)
  valCh-mono (lim g)  n d = emb-mono◁ (lim g) n (val-mono (g n) d)
  valCh-mono (Ωₗ k h) c d = emb-mono◁ (Ωₗ k h) c (val-mono (h c) d)
```

## 值合法; 块的加法就是值的加法

值的合法性: ℕ 极限的相邻项按 `_◁_` 步进. 合法块的每棵树都合法, 所以每个值合法 (`val-leg`, 没有前提).

```agda
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

emb-leg : (ℓ : L) (c : Ch ℓ) (v : V (chL ℓ c)) → LegV (chL ℓ c) v → LegV ℓ (emb ℓ c v)
emb-leg zero     () v
emb-leg ℓ        c zero    h = tt
emb-leg ℓ        c (suc v) h = emb-leg ℓ c v h
emb-leg ℓ        c (lim f) (hf , adj) = (λ n → emb-leg ℓ c (f n) (hf n)) , (λ n → emb-mono◁ ℓ c (adj n))
emb-leg (suc a)  c (Ω p g) h = λ z → emb-leg (suc a) c (g z) (h z)
emb-leg (lim g)  n (Ω p f) h = λ z → emb-leg (lim g) n (f z) (h z)
emb-leg (Ωₗ k h) c (Ω p g) e = λ z → emb-leg (Ωₗ k h) c (g z) (e z)

mutual
  val-leg : (ℓ : L) (x : Tr ℓ) → LegV ℓ (val ℓ x)
  val-leg ℓ zero         = tt
  val-leg ℓ (suc x)      = val-leg ℓ x
  val-leg ℓ (lim f a)    = (λ n → val-leg ℓ (f n)) , (λ n → val-mono ℓ (a n))
  val-leg ℓ (Ω p g)      = λ z → val-leg ℓ (g z)
  val-leg ℓ (up x c y _) = ⊹-leg (val ℓ x) (valCh ℓ c y) (val-leg ℓ x) (valCh-leg ℓ c y)

  valCh-leg : (ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → LegV ℓ (valCh ℓ c y)
  valCh-leg zero     () y
  valCh-leg (suc a)  c y = emb-leg (suc a) c (val a y) (val-leg a y)
  valCh-leg (lim g)  n y = emb-leg (lim g) n (val (g n) y) (val-leg (g n) y)
  valCh-leg (Ωₗ k h) c y = emb-leg (Ωₗ k h) c (val (h c) y) (val-leg (h c) y)

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

`YiViewVal.incl` (值放回块里) 没有搬: 合法块的 ℕ 极限要交相邻项的树序步进, 而值的合法性证明不唯一, 逐项放回的树依赖各自的证明, 相邻两项对不上 (判断, 未编译否定).

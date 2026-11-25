# 上折: Ω₂ 这一步的值

> 验收文件. 编译定理, 无前提: `bho-lower : ψ⁰(Ω₂) ≼ read (ψ₀ 2 (Ωt 2))`, 参照的 ψ₀(Ω₂) 不高于新折叠在层号 2 上的 Ω 树的折叠值 (只有下界); 对满足四条下界条件的任意底 B₂ 也成立 (`At.lower2`).
> 证法: 第 1 层上参照树与块里的树之间的模拟 `S` (结点对结点, 右边可沿第一位置序放宽); 三条保持: 折到自身 (`P`), 折到第 0 层的树 (`Q`), 折到第 0 层的值 (`V`).
> 不涉及上界; 不是 `LOWER` 在 m = 1 的全部 (那里的层号是 ℕ 极限, 要一切有限层, 见 `YiUpValTw1`). 原折叠在同一处没有对应定理 (`YiFreshValGap` 的判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUpVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock renaming (L to LF)
open import OCF.Lean.YiFreshFold using (_+_; iter; next; cum; Ωt; ι)
open import OCF.Lean.YiFreshLegal using (_⊢_◃_; ◃s; ◃l; ◃w; ◃u; ◃c; ◃t; +-mono; Ωt-nz)
open import OCF.Lean.YiFreshValRead using (T₀; read; ◃⊑; next≽; next≼; limcum≽)
open import OCF.Lean.YiPhiBlock
open import OCF.Lean.YiUpBlock
open import OCF.Lean.YiUpFold
open import OCF.Lean.YiUpLegal using (mono⊥; monos; Up-mono; dS)
open import OCF.Lean.YiUpCheck using (one; two; d₁)

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-refl; ≼-trans; ⊑→≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 第一位置序的自反闭包

```agda
infix 4 _⊢_⊴_
data _⊢_⊴_ (ℓ : LF) (t : Tr ℓ) : Tr ℓ → Set where
  ⊴r : ℓ ⊢ t ⊴ t
  ⊴◃ : ∀ {t′} → ℓ ⊢ t ◃ t′ → ℓ ⊢ t ⊴ t′

⊴-◃ : ∀ {ℓ} {a b c : Tr ℓ} → ℓ ⊢ a ⊴ b → ℓ ⊢ b ◃ c → ℓ ⊢ a ◃ c
⊴-◃ ⊴r     e = e
⊴-◃ (⊴◃ d) e = ◃t d e

◃-⊴ : ∀ {ℓ} {a b c : Tr ℓ} → ℓ ⊢ a ◃ b → ℓ ⊢ b ⊴ c → ℓ ⊢ a ◃ c
◃-⊴ d ⊴r     = d
◃-⊴ d (⊴◃ e) = ◃t d e

⊴-trans : ∀ {ℓ} {a b c : Tr ℓ} → ℓ ⊢ a ⊴ b → ℓ ⊢ b ⊴ c → ℓ ⊢ a ⊴ c
⊴-trans d ⊴r     = d
⊴-trans d (⊴◃ e) = ⊴◃ (⊴-◃ d e)
```

底在折叠值之下 (无前提, 不要合法性): 上折与第 0 层的两种折叠 (第 1 层的在 `At` 里).

```agda
Up-⊵ : ∀ {ℓ} (j : LF) (d : Dn ℓ j) (b : Tr ℓ) (y : Tr j) → ℓ ⊢ b ⊴ Up j d b y
Up-⊵ j d b zero    = ⊴r
Up-⊵ j d b (suc y) = ⊴◃ (⊴-◃ (Up-⊵ j d b y) (◃l zero))
Up-⊵ j d b (lim f) = ⊴◃ (⊴-◃ (Up-⊵ j d b (f zero)) (◃l zero))
Up-⊵ {ℓ} j d b (Ω p g) = ⊴◃ (⊴-◃ (Up-⊵ j d b (g (mvBr d p (fromBr ℓ (mv d p) zero)))) ◃w)
Up-⊵ (suc a)  d b (up y _ y′) = ⊴-trans (Up-⊵ (suc a) d b y) (Up-⊵ a (down d tt) _ y′)
Up-⊵ (lim g)  d b (up y n y′) = ⊴-trans (Up-⊵ (lim g) d b y) (Up-⊵ (g n) (down d n) _ y′)
Up-⊵ (Ωₗ k h) d b (up y c y′) = ⊴-trans (Up-⊵ (Ωₗ k h) d b y) (Up-⊵ (h c) (down d c) _ y′)
Up-⊵ zero     d b (up y () _)

s0-⊵ : (B : Base zero) (b c : Tr zero) → zero ⊢ b ⊴ ψs zero tt B zero self b c
s0-⊵ B b zero    = ⊴r
s0-⊵ B b (suc c) = ⊴◃ (⊴-◃ (s0-⊵ B b c) (◃l zero))
s0-⊵ B b (lim f) = ⊴◃ (⊴-◃ (s0-⊵ B b (f zero)) (◃l zero))
s0-⊵ B b (Ω () _)
s0-⊵ B b (up _ () _)

⊥0-⊵ : (B : Base zero) (c : Tr zero) → zero ⊢ b⊥ B ⊴ ψ⊥ zero tt B c
⊥0-⊵ B zero    = ⊴r
⊥0-⊵ B (suc c) = ⊴◃ (⊴-◃ (⊥0-⊵ B c) (◃l zero))
⊥0-⊵ B (lim f) = ⊴◃ (⊴-◃ (⊥0-⊵ B (f zero)) (◃l zero))
⊥0-⊵ B (Ω () _)
⊥0-⊵ B (up _ () _)
```

## 模拟

`R⁰ y c`: 参照的第 0 层树 y 被块的第 0 层树 c 模拟. `S x t`: 第 1 层. 右边可沿第一位置序放宽 (`rw`, `S-w`); 结点对结点, 分支对一切被模拟的输入 (`S-n`); 参照里摊平的加法对着 `up` 的孩子 (`S-u0`, `S-us`), 参照的提升 `up` 对着底为零的 `up` (`S-u`).

```agda
I1 I2 : L.Ordᴵ
I1 = L.suc L.zero
I2 = L.suc I1

T₁ : Set
T₁ = L.Ordᶜ I1

data R⁰ : T₀ → Tr zero → Set where
  rz : ∀ {c} → R⁰ L.zero c
  rs : ∀ {y c} → R⁰ y c → R⁰ (L.suc y) (suc c)
  rL : ∀ {f c} → (∀ n → R⁰ (f n) c) → R⁰ (L.lim f) c
  rw : ∀ {y c c′} → R⁰ y c → zero ⊢ c ◃ c′ → R⁰ y c′

data S : T₁ → Tr one → Set where
  S-z  : S L.zero zero
  S-s  : ∀ {x t} → S x t → S (L.suc x) (suc t)
  S-L  : ∀ {f t} → (∀ n → S (f n) t) → S (L.lim f) t
  S-w  : ∀ {x t t′} → S x t → one ⊢ t ◃ t′ → S x t′
  S-n  : ∀ {f : T₀ → T₁} {g : Tr zero → Tr one} → (∀ y c → R⁰ y c → S (f y) (g c))
       → S (L.limᵢ L.zero f) (Ω (inj₁ tt) g)
  S-u0 : ∀ {x t} → S x t → (c : Tr zero) → S x (up t tt c)
  S-us : ∀ {x t c} → S x (up t tt c) → S (L.suc x) (up t tt (suc c))
  S-u  : ∀ {y c} → R⁰ y c → S (L.up L.zero y) (up zero tt c)

r-⊴ : ∀ {y c c′} → R⁰ y c → zero ⊢ c ⊴ c′ → R⁰ y c′
r-⊴ r ⊴r     = r
r-⊴ r (⊴◃ d) = rw r d

s-⊴ : ∀ {x t t′} → S x t → one ⊢ t ⊴ t′ → S x t′
s-⊴ s ⊴r     = s
s-⊴ s (⊴◃ d) = S-w s d
```

第 0 层: 加法, `next`, 部分和, 搬运, 读成值序.

```agda
+⊴ : (b b′ : Tr zero) → zero ⊢ b ⊴ b + b′
+⊴ b zero    = ⊴r
+⊴ b (suc c) = ⊴◃ (⊴-◃ (+⊴ b c) ◃s)
+⊴ b (lim f) = ⊴◃ (⊴-◃ (+⊴ b (f zero)) (◃l zero))
+⊴ b (Ω () _)
+⊴ b (up _ () _)

r-add : ∀ {a b a′ b′} → R⁰ a b → R⁰ a′ b′ → R⁰ (a L.+ a′) (b + b′)
r-add {b = b} ra (rz {c})  = r-⊴ ra (+⊴ b c)
r-add ra (rs r)    = rs (r-add ra r)
r-add ra (rL h)    = rL (λ n → r-add ra (h n))
r-add {b = b} ra (rw r d)  = rw (r-add ra r) (+-mono b d)

r-right : ∀ {y b′} → R⁰ y b′ → (a : Tr zero) → R⁰ y (a + b′)
r-right rz       a = rz
r-right (rs r)   a = rs (r-right r a)
r-right (rL h)   a = rL (λ n → r-right (h n) a)
r-right (rw r d) a = rw (r-right r a) (+-mono a d)

r-next : ∀ {a b} → R⁰ a b → R⁰ (L.lim (iterᴸ (a L.+_) L.zero)) (next b)
r-next {a} {b} ra = rL λ where
    zero    → rz
    (suc n) → rw (go n) (◃l n)
  where
  go : ∀ n → R⁰ (iterᴸ (a L.+_) L.zero (suc n)) (iter (b +_) b n)
  go zero    = ra
  go (suc n) = r-add ra (go n)

r-cum : (G : ℕ → Tr zero) (n : ℕ) {y : T₀} → R⁰ y (G n) → R⁰ y (lim (cum G))
r-cum G n r = rw (go n r) (◃l n)
  where
  go : ∀ n {y} → R⁰ y (G n) → R⁰ y (cum G n)
  go zero    r = r
  go (suc n) r = r-right r (cum G n)

r-tr : ∀ {y c} (e : L.zero L.≅ᴵ L.zero) → R⁰ y c → R⁰ (L.tr⁻ e y) c
r-tr e rz       = rz
r-tr e (rs r)   = rs (r-tr e r)
r-tr e (rL h)   = rL (λ n → r-tr e (h n))
r-tr e (rw r d) = rw (r-tr e r) d

r→≼ : ∀ {y c} → R⁰ y c → y ≼ read c
r→≼ rz       = z≼
r→≼ (rs r)   = s≼s (r→≼ r)
r→≼ (rL h)   = l≼ (λ n → r→≼ (h n))
r→≼ (rw {c = c} r d) = ≼-trans (r→≼ r) (⊑→≼ (read c) (◃⊑ d))

⊴→≼ : ∀ {c c′ : Tr zero} → zero ⊢ c ⊴ c′ → read c ≼ read c′
⊴→≼ {c} ⊴r     = ≼-refl (read c)
⊴→≼ {c} (⊴◃ d) = ⊑→≼ (read c) (◃⊑ d)
```

第 1 层: 参照里的加法把右边的提升摊平, 块里的加法把 `up` 留着 (`flat`); 加法与 `next`.

```agda
flat : ∀ {a b y c} (σ : L.Simᴵ L.zero I1) → S a b → R⁰ y c → S (L.add a σ y) (up b tt c)
flat σ sa (rz {c}) = S-u0 sa c
flat σ sa (rs r)   = S-us (flat σ sa r)
flat σ sa (rL h)   = S-L (λ n → flat σ sa (h n))
flat σ sa (rw r d) = S-w (flat σ sa r) (◃c d)

s-add : ∀ {a b a′ b′} → S a b → S a′ b′ → S (a L.+ a′) (b + b′)
s-add sa S-z        = sa
s-add sa (S-s s)    = S-s (s-add sa s)
s-add sa (S-L h)    = S-L (λ n → s-add sa (h n))
s-add {b = b} sa (S-w s d) = S-w (s-add sa s) (+-mono b d)
s-add sa (S-n h)    = S-n (λ y c r → s-add sa (h y c r))
s-add sa (S-u0 s c) = S-u0 (s-add sa s) c
s-add sa (S-us s)   = S-us (s-add sa s)
s-add sa (S-u r)    = flat (λ q → L.suc q) sa r

s-next : ∀ {a b} → S a b → one ⊢ zero ◃ b → S (L.lim (iterᴸ (a L.+_) L.zero)) (next b)
s-next {a} {b} sa zb = S-L λ where
    zero    → S-w S-z (◃t zb (◃l zero))
    (suc n) → S-w (go n) (◃l n)
  where
  go : ∀ n → S (iterᴸ (a L.+_) L.zero (suc n)) (iter (b +_) b n)
  go zero    = sa
  go (suc n) = s-add sa (go n)
```

## 参照的 ψ₁ 与上折

`ψ₁`: 第 1 层的树折到第 1 层 (上界是第 2 层). 提升的第 0 层树 y 的像是 Ω₁·ω^y, 对着上折 (`Pu`); 这一行用到上折的三条: 零到底, 后继到 `next`, 极限逐项.

```agda
ψ₁ : T₁ → T₁
ψ₁ x = L.ψ {i = I1} {k = I1} {ℓ = I2} L.zero (λ q → L.suc q) x

Sβ₀ : S (L.Ω I1) (Ωt one)
Sβ₀ = S-n (λ y c r → S-w (S-u r) (◃c ◃s))

Pu : ∀ {y c} (σ : L.Simᴵ L.zero I2) (b : Tr one) → S (L.Ω I1) b → one ⊢ zero ◃ b → R⁰ y c
   → S (L.ψ {i = I1} {k = L.zero} {ℓ = I2} L.zero σ y) (Up zero d₁ b c)
Pu σ b sb zb (rz {c}) = s-⊴ sb (Up-⊵ zero d₁ b c)
Pu σ b sb zb (rs {c = c} r) = s-next (Pu σ b sb zb r) (◃-⊴ zb (Up-⊵ zero d₁ b c))
Pu σ b sb zb (rL h)   = S-L (λ n → Pu σ b sb zb (h n))
Pu σ b sb zb (rw r d) = S-w (Pu σ b sb zb r) (Up-mono zero d₁ b d)
```

## 取定底

`At B₂`: 第 2 层的底 B₂ 任意, 只要四条: 第 1 层目标的底模拟 Ω₁ 且非零, 第 0 层目标的底不低于 1, `b⊥` 的值不低于 1. `B₀` 满足 (`bho-lower`); 塔第 1 项的链里出现的底也满足 (`YiUpValTw1`).
以下三条保持: 参照的 ψ₁ 对着折到自身的 `F` (`P`); 参照折到第 0 层的 ψ 对着 `H` (`Q`; 结点处两边都是链, 参照从 Ω₀ = 1 起, 块从 0 起, 差一步, `chain`); ψ⁰ 的值对着 `ψ⊥` 的读回 (`V`).

```agda
𝟏 : T₀
𝟏 = L.suc L.zero

ψ₁₀ : T₁ → T₀
ψ₁₀ x = L.ψ {i = L.zero} {k = I1} {ℓ = I1} L.zero (λ q → q) x

Qu : ∀ {y c} (σ : L.Simᴵ L.zero I1) (B : Base zero) (b : Tr zero) → zero ⊢ suc zero ⊴ b → R⁰ y c
   → R⁰ (L.ψ {i = L.zero} {k = L.zero} {ℓ = I1} L.zero σ y) (ψs zero tt B zero self b c)
Qu σ B b ob (rz {c}) = r-⊴ (rs rz) (⊴-trans ob (s0-⊵ B b c))
Qu σ B b ob (rs r)   = r-next (Qu σ B b ob r)
Qu σ B b ob (rL h)   = rL (λ n → Qu σ B b ob (h n))
Qu σ B b ob (rw r d) = rw (Qu σ B b ob r) (monos zero tt B zero self b d)

Vu : ∀ {y c} (B : Base zero) → 𝟏 ≼ read (b⊥ B) → R⁰ y c → L.ψ⁰ y ≼ read (ψ⊥ zero tt B c)
Vu B ob (rz {c}) = ≼-trans ob (⊴→≼ (⊥0-⊵ B c))
Vu B ob (rs {c = c} r) = next≽ (ψ⊥ zero tt B c) (Vu B ob r)
Vu B ob (rL h)   = l≼ (λ n → Vu B ob (h n))
Vu B ob (rw {c = c} r d) = ≼-trans (Vu B ob r) (⊑→≼ (read (ψ⊥ zero tt B c)) (◃⊑ (mono⊥ zero tt B d)))

module At (B₂ : Base two)
  (hβ : S (L.Ω I1) (bs B₂ one (ins self)))
  (zβ : one ⊢ zero ◃ bs B₂ one (ins self))
  (h0 : zero ⊢ suc zero ⊴ bs B₂ zero (ins (ins self)))
  (h⊥ : 𝟏 ≼ read (b⊥ B₂)) where

  Bᵃ : Base one
  Bᵃ = dS one tt B₂ zero

  β₁ : Tr one
  β₁ = bs B₂ one (ins self)

  β₀ : Tr zero
  β₀ = bs B₂ zero (ins (ins self))

  F : Tr one → Tr one
  F t = ψs one tt Bᵃ one self β₁ t

  H : Tr one → Tr zero
  H t = ψs one tt Bᵃ zero (ins self) β₀ t

  F-⊵ : (t : Tr one) → one ⊢ β₁ ⊴ F t
  F-⊵ zero       = ⊴r
  F-⊵ (suc t)    = ⊴◃ (⊴-◃ (F-⊵ t) (◃l zero))
  F-⊵ (lim f)    = ⊴◃ (⊴-◃ (F-⊵ (f zero)) (◃l zero))
  F-⊵ (Ω p g)    = ⊴◃ (⊴-◃ (F-⊵ (g (fromBr one p zero))) ◃w)
  F-⊵ (up t _ c) = ⊴-trans (F-⊵ t) (Up-⊵ zero d₁ (F t) c)

  H-⊵ : (t : Tr one) → zero ⊢ β₀ ⊴ H t
  H-⊵ zero       = ⊴r
  H-⊵ (suc t)    = ⊴◃ (⊴-◃ (H-⊵ t) (◃l zero))
  H-⊵ (lim f)    = ⊴◃ (⊴-◃ (H-⊵ (f zero)) (◃l zero))
  H-⊵ (Ω (inj₁ tt) g) = ⊴◃ (⊴-◃ (H-⊵ (g zero)) (◃l zero))
  H-⊵ (Ω (inj₂ ()) g)
  H-⊵ (up t _ c) = ⊴-trans (H-⊵ t) (s0-⊵ (dS zero tt Bᵃ t) (H t) c)

  nzF : (t : Tr one) → one ⊢ zero ◃ F t
  nzF t = ◃-⊴ zβ (F-⊵ t)

  P : ∀ {x t} → S x t → S (ψ₁ x) (F t)
  P S-z        = hβ
  P (S-s {t = t} s) = s-next (P s) (nzF t)
  P (S-L h)    = S-L (λ n → P (h n))
  P (S-w s d)  = S-w (P s) (monos one tt Bᵃ one self β₁ d)
  P (S-n h)    = S-n (λ y c r → P (h (L.tr⁻ _ y) c (r-tr _ r)))
  P (S-u0 {t = t} s c) = s-⊴ (P s) (Up-⊵ zero d₁ (F t) c)
  P (S-us {t = t} {c = c} s) = s-next (P s) (◃-⊴ (nzF t) (Up-⊵ zero d₁ (F t) c))
  P (S-u r)    = Pu _ β₁ hβ zβ r

  wch : (T₀ → T₁) → ℕ → T₀
  wch f = iterᴸ (λ x → ψ₁₀ (f x)) (L.suc L.zero)

  vch : (Tr zero → Tr one) → ℕ → Tr zero
  vch g = iter (λ z → H (g z)) zero

  mutual
    Q : ∀ {x t} → S x t → R⁰ (ψ₁₀ x) (H t)
    Q S-z        = r-⊴ (rs rz) h0
    Q (S-s s)    = r-next (Q s)
    Q (S-L h)    = rL (λ n → Q (h n))
    Q (S-w s d)  = rw (Q s) (monos one tt Bᵃ zero (ins self) β₀ d)
    Q (S-n {f} {g} h) =
      rL (λ n → r-cum (λ m → H (g (vch g m))) (suc n) (Q (h (wch f n) (vch g (suc n)) (chain h n))))
    Q (S-u0 {t = t} s c) = r-⊴ (Q s) (s0-⊵ (dS zero tt Bᵃ t) (H t) c)
    Q (S-us s)   = r-next (Q s)
    Q (S-u r)    = Qu _ (dS zero tt Bᵃ zero) β₀ h0 r

    chain : ∀ {f : T₀ → T₁} {g : Tr zero → Tr one} → (∀ y c → R⁰ y c → S (f y) (g c))
          → ∀ n → R⁰ (wch f n) (vch g (suc n))
    chain {g = g} h zero    = r-⊴ (rs rz) (⊴-trans h0 (H-⊵ (g zero)))
    chain h (suc n) = Q (h _ _ (chain h n))
  V : ∀ {x t} → S x t → L.ψ⁰ x ≼ read (ψ⊥ one tt Bᵃ t)
  V S-z        = h⊥
  V (S-s {t = t} s) = next≽ (ψ⊥ one tt Bᵃ t) (V s)
  V (S-L h)    = l≼ (λ n → V (h n))
  V (S-w {t = t} s d) = ≼-trans (V s) (⊑→≼ (read (ψ⊥ one tt Bᵃ t)) (◃⊑ (mono⊥ one tt Bᵃ d)))
  V (S-n {f} {g} h) =
    l≼ (λ n → limcum≽ (λ m → ψ⊥ one tt Bᵃ (g (vch g m))) (suc n) (V (h (wch f n) (vch g (suc n)) (chain h n))))
  V (S-u0 {t = t} s c) = ≼-trans (V s) (⊴→≼ (⊥0-⊵ (dS zero tt Bᵃ t) c))
  V (S-us {t = t} {c = c} s) = next≽ (ψ⊥ one tt Bᵃ (up t tt c)) (V s)
  V (S-u r)    = Vu (dS zero tt Bᵃ zero) h⊥ r

  γ : ℕ → T₁
  γ = iterᴸ ψ₁ (L.Ω I1)

  z : ℕ → Tr one
  z = iter (λ c → next (F c)) zero

  form : ψ⊥ two tt B₂ (Ωt two) ≡ lim (cum (λ k → next (ψ⊥ one tt Bᵃ (z k))))
  form = refl

  sγ : ∀ n → S (γ n) (z (suc n))
  sγ zero    = S-w hβ (◃l zero)
  sγ (suc n) = S-w (P (sγ n)) (◃l zero)

  lower2 : L.ψ⁰ (L.Ω I2) ≼ read (ψ⊥ two tt B₂ (Ωt two))
  lower2 = l≼ (λ n → limcum≽ (λ k → next (ψ⊥ one tt Bᵃ (z k))) (suc n)
    (next≼ (ψ⊥ one tt Bᵃ (z (suc n))) (V (sγ n))))
```

## Ω₂ 的下界

参照的链 γ₀ = Ω₁, γₙ₊₁ = ψ₁(γₙ) 对着块里的链 `z` (底取 `B₀` 时是 `YiUpCheck.z₂`) 的第 n+1 项. `P` 的各行里, `S-u0`, `S-us`, `S-u` 三行用到自身行的上折; 其余是 `YiPhiFold` 已有的行.

```agda
bho-lower : L.ψ⁰ (L.Ω I2) ≼ read (ψ₀ two tt (Ωt two))
bho-lower = At.lower2 (B₀ two) Sβ₀ (Ωt-nz one) ⊴r (≼-refl 𝟏)
```

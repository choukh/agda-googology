# 从头重写: 块

> 判决: 成品候选 (块). 树 `T` 与第一位置序 `Lt` 归纳-归纳 (ℕ 极限带相邻步进, 嵌入带孩子非零); 层号 `L` 统一成 `nd s h` (形状 `s`, 孩子 `h`), 与各层的树归纳-递归.
> 与 F2 (`YiLegBlock`) 的层号一一对应 (`suc a` 即 `nd sS (λ _ → a)`, `lim g` 即 `nd sL g`, `Ωₗ k h` 即 `nd (sΩ k) h`), 槽位多一层 `⊥ ⊎`; 第一分支直接定义为 `fromBr ℓ p zero`.
> 不否定什么. 运算与证据在 `YiRWOps`, 折叠在 `YiRWFold`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRWBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
```

## 一层的树与它的序

```agda
record Sg : Set₁ where
  constructor sg
  field
    P  : Set
    B  : P → Set
    C  : Set
    D  : C → Set
    b₀ : (p : P) → B p
    z₀ : (c : C) → D c
    R  : (c : C) → D c → D c → Set
open Sg public

mutual
  data T (S : Sg) : Set where
    zero : T S
    suc  : T S → T S
    lim  : (f : ℕ → T S) → ((n : ℕ) → Lt S (f n) (f (suc n))) → T S
    Ω    : (p : P S) → (B S p → T S) → T S
    up   : T S → (c : C S) (y : D S c) → R S c (z₀ S c) y → T S

  data Lt (S : Sg) : T S → T S → Set where
    ◃s : ∀ {x} → Lt S x (suc x)
    ◃l : ∀ {f a} (n : ℕ) → Lt S (f n) (lim f a)
    ◃w : ∀ {p g} → Lt S (g (b₀ S p)) (Ω p g)
    ◃u : (x : T S) (c : C S) (y : D S c) (e : R S c (z₀ S c) y) → Lt S x (up x c y e)
    ◃c : (x : T S) (c : C S) {y′ y : D S c} {e′ : R S c (z₀ S c) y′} {e : R S c (z₀ S c) y}
       → R S c y′ y → Lt S (up x c y′ e′) (up x c y e)
    ◃t : ∀ {x y z} → Lt S x y → Lt S y z → Lt S x z
```

## 层号与各层的树

槽位: 经孩子 c 到 `h c` 本身或更深 (`inj₂`), 或 (只在 Ω 形状) 到下标层 k 本身或更深 (`inj₁`). `sl` 同时给槽位所在的层号与换型.

```agda
mutual
  data L : Set
  data Sh : Set
  Ch : Sh → Set
  Sig : L → Sg
  Tr : L → Set
  Tr ℓ = T (Sig ℓ)

  data L where
    zero : L
    nd   : (s : Sh) → (Ch s → L) → L

  data Sh where
    sS sL : Sh
    sΩ    : L → Sh

  Ch sS     = ⊤
  Ch sL     = ℕ
  Ch (sΩ k) = Tr k

  PK : Sh → Set
  PK (sΩ k) = Pos⁼ k
  PK _      = ⊥

  Pos : L → Set
  Pos zero     = ⊥
  Pos (nd s h) = PK s ⊎ Σ (Ch s) λ c → Pos⁼ (h c)

  Pos⁼ : L → Set
  Pos⁼ a = ⊤ ⊎ Pos a

  Br : (ℓ : L) → Pos ℓ → Set
  Br (nd s h)      (inj₂ (c , t)) = Br⁼ (h c) t
  Br (nd (sΩ k) h) (inj₁ t)       = Br⁼ k t

  Br⁼ : (a : L) → Pos⁼ a → Set
  Br⁼ a (inj₁ _) = Tr a
  Br⁼ a (inj₂ p) = Br a p

  sl : (ℓ : L) (p : Pos ℓ) → Σ L λ a → Tr a → Br ℓ p
  sl (nd s h)      (inj₂ (c , t)) = sl⁼ (h c) t
  sl (nd (sΩ k) h) (inj₁ t)       = sl⁼ k t

  sl⁼ : (a : L) (t : Pos⁼ a) → Σ L λ b → Tr b → Br⁼ a t
  sl⁼ a (inj₁ _) = a , λ x → x
  sl⁼ a (inj₂ p) = sl a p

  CH : L → Set
  CH zero     = ⊥
  CH (nd s h) = Ch s

  ChT : (ℓ : L) → CH ℓ → Set
  ChT (nd s h) c = Tr (h c)

  chZ : (ℓ : L) (c : CH ℓ) → ChT ℓ c
  chZ (nd s h) c = zero

  RCh : (ℓ : L) (c : CH ℓ) → ChT ℓ c → ChT ℓ c → Set
  RCh (nd s h) c = Lt (Sig (h c))

  Sig ℓ = sg (Pos ℓ) (Br ℓ) (CH ℓ) (ChT ℓ) (λ p → proj₂ (sl ℓ p) zero) (chZ ℓ) (RCh ℓ)

infix 4 _⊢_◃_
_⊢_◃_ : (ℓ : L) → Tr ℓ → Tr ℓ → Set
ℓ ⊢ x ◃ y = Lt (Sig ℓ) x y

at : (ℓ : L) → Pos ℓ → L
at ℓ p = proj₁ (sl ℓ p)

fromBr : (ℓ : L) (p : Pos ℓ) → Tr (at ℓ p) → Br ℓ p
fromBr ℓ p = proj₂ (sl ℓ p)
```

## 读回, 塔, Λ

```agda
infixl 6 _⊕_
_⊕_ : L → L → L
a ⊕ zero   = a
a ⊕ nd s h = nd s λ c → a ⊕ h c

↑ : (k : L) → Tr k → L
↑ k        zero         = zero
↑ k        (suc x)      = nd sS λ _ → ↑ k x
↑ k        (lim f _)    = nd sL λ n → ↑ k (f n)
↑ k        (Ω p g)      = nd (sΩ (at k p)) λ c → ↑ k (g (fromBr k p c))
↑ (nd s h) (up x c y _) = ↑ (nd s h) x ⊕ ↑ (h c) y

tw : ℕ → L
tw zero    = zero
tw (suc n) = nd (sΩ (tw n)) λ c → tw n ⊕ ↑ (tw n) c

Λ : L
Λ = nd sL tw
```

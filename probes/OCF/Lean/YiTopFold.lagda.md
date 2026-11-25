# 顶槽位的块: 折叠

> 判决: 成品候选 (折叠). 空白页的折叠 (`YiFreshFold`) 去掉保留判定 `kp` 与 `posW`: Ω 结点在目标是 `self` 时保留, 其余沿下标层做链 (`stp`, 起点 `z₀`); 其余各行照空白页.
> 目标仍是 "层号 j 连同 j ≤ ℓ 的路径"; 嵌入分支 `up` 的各行, 加法, 底与空白页逐行相同, Ω 树只把槽位 `inj₁ tt`, `inj₁ (inj₁ tt)` 换成证据 `tt`.
> 不否定什么. 与空白页折叠的对应在 `YiTopCheck`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTopFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiTopBlock
```

## 运算

```agda
infixl 6 _+_
_+_ : ∀ {S B C D} → T S B C D → T S B C D → T S B C D
x + zero     = x
x + suc y    = suc (x + y)
x + lim f    = lim (λ n → x + f n)
x + Ω s g    = Ω s (λ z → x + g z)
x + up y c w = up (x + y) c w

iter : {A : Set} → (A → A) → A → ℕ → A
iter f a zero    = a
iter f a (suc n) = f (iter f a n)

next : ∀ {S B C D} → T S B C D → T S B C D
next b = lim (iter (b +_) b)

cum : ∀ {S B C D} → (ℕ → T S B C D) → ℕ → T S B C D
cum f zero    = f zero
cum f (suc n) = cum f n + f (suc n)

Ωt : (ℓ : L) → Tr ℓ
Ωt zero     = suc zero
Ωt (suc a)  = Ω tt (λ c → up zero tt (suc c))
Ωt (lim g)  = lim cumΩ
  where
  cumΩ : ℕ → Tr (lim g)
  cumΩ zero    = up zero zero (Ωt (g zero))
  cumΩ (suc n) = up (cumΩ n) (suc n) (Ωt (g (suc n)))
Ωt (Ωₗ k h) = Ω tt (λ c → up zero c (Ωt (h c)))

ι : (j : L) → Tr zero → Tr j
ι j zero       = zero
ι j (suc x)    = suc (ι j x)
ι j (lim f)    = lim (λ n → ι j (f n))
ι j (Ω () _)
ι j (up _ () _)

z₀ : (ℓ : L) → Hd ℓ → Bt ℓ
z₀ (suc a)  _ = zero
z₀ (Ωₗ k h) _ = zero
z₀ zero     ()
z₀ (lim _)  ()
```

## 目标

```agda
infix 4 _≤_
data _≤_ : L → L → Set where
  self : ∀ {ℓ} → ℓ ≤ ℓ
  ins  : ∀ {j a} → j ≤ a → j ≤ suc a
  inl  : ∀ {j g} (n : ℕ) → j ≤ g n → j ≤ lim g
  ink  : ∀ {j k h} → j ≤ k → j ≤ Ωₗ k h
  inb  : ∀ {j k h} (c : Tr k) → j ≤ h c → j ≤ Ωₗ k h

eqℕ : (n m : ℕ) → Maybe (n ≡ m)
eqℕ zero    zero    = just refl
eqℕ (suc n) (suc m) with eqℕ n m
... | just refl = just refl
... | nothing   = nothing
eqℕ _       _       = nothing

eqℕ-refl : (n : ℕ) → eqℕ n n ≡ just refl
eqℕ-refl zero = refl
eqℕ-refl (suc n) rewrite eqℕ-refl n = refl
```

## 折叠

结点: 目标是 `self` 时保留; 否则沿结点的下标层做链 γ₀ = 0, γₙ₊₁ = ψ_k(g γₙ) (`stp`), 取部分和的极限.

```agda
record Base (ℓ : L) : Set where
  constructor base
  field
    b⊥ : Tr zero
    bs : (j : L) → j ≤ ℓ → Tr j
open Base public

B₀ : (ℓ : L) → Base ℓ
B₀ ℓ = base (Ωt zero) (λ j _ → Ωt j)

mutual
  ψ⊥ : (ℓ : L) → Base ℓ → Tr ℓ → Tr zero
  ψ⊥ ℓ B zero    = b⊥ B
  ψ⊥ ℓ B (suc x) = next (ψ⊥ ℓ B x)
  ψ⊥ ℓ B (lim f) = lim (λ n → ψ⊥ ℓ B (f n))
  ψ⊥ ℓ B (Ω s g) = lim (cum (λ n → ψ⊥ ℓ B (g (iter (stp ℓ B s g) (z₀ ℓ s) n))))
  ψ⊥ (suc a)  B (up x _ y) =
    ψ⊥ a (base (ψ⊥ (suc a) B x) (λ j w → ψs (suc a) B j (ins w) x)) y
  ψ⊥ (lim g)  B (up x n y) =
    ψ⊥ (g n) (base (ψ⊥ (lim g) B x) (λ j w → ψs (lim g) B j (inl n w) x)) y
  ψ⊥ (Ωₗ k h) B (up x c y) =
    ψ⊥ (h c) (base (ψ⊥ (Ωₗ k h) B x) (λ j w → ψs (Ωₗ k h) B j (inb c w) x)) y
  ψ⊥ zero     B (up x () y)

  ψs : (ℓ : L) → Base ℓ → (j : L) → j ≤ ℓ → Tr ℓ → Tr j
  ψs ℓ B j w zero    = bs B j w
  ψs ℓ B j w (suc x) = next (ψs ℓ B j w x)
  ψs ℓ B j w (lim f) = lim (λ n → ψs ℓ B j w (f n))
  ψs ℓ B _ self (Ω s g) = Ω s (λ z → ψs ℓ B ℓ self (g z))
  ψs ℓ B j w    (Ω s g) = lim (cum (λ n → ψs ℓ B j w (g (iter (stp ℓ B s g) (z₀ ℓ s) n))))
  ψs ℓ B _ self (up x c y) = up (ψs ℓ B ℓ self x) c y
  ψs (suc a) B j (ins w) (up x _ y) =
    ψs a (base (ψ⊥ (suc a) B x) (λ j′ w′ → ψs (suc a) B j′ (ins w′) x)) j w y
  ψs (lim g) B j (inl n w) (up x m y) with eqℕ m n
  ... | just refl =
    ψs (g m) (base (ψ⊥ (lim g) B x) (λ j′ w′ → ψs (lim g) B j′ (inl m w′) x)) j w y
  ... | nothing   = ψs (lim g) B j (inl n w) x + ι j (ψ⊥ (g m) (B₀ (g m)) y)
  ψs (Ωₗ k h) B j (ink w)    (up x c y) = ψs (Ωₗ k h) B j (ink w) x    + ι j (ψ⊥ (h c) (B₀ (h c)) y)
  ψs (Ωₗ k h) B j (inb c′ w) (up x c y) = ψs (Ωₗ k h) B j (inb c′ w) x + ι j (ψ⊥ (h c) (B₀ (h c)) y)

  stp : (ℓ : L) → Base ℓ → Hd ℓ → (Bt ℓ → Tr ℓ) → Bt ℓ → Bt ℓ
  stp (suc a)  B _ g z = ψs (suc a) B a (ins self) (g z)
  stp (Ωₗ k h) B _ g z = ψs (Ωₗ k h) B k (ink self) (g z)
  stp zero     B () g z
  stp (lim _)  B () g z

ψ₀ : (ℓ : L) → Tr ℓ → Tr zero
ψ₀ ℓ = ψ⊥ ℓ (B₀ ℓ)
```

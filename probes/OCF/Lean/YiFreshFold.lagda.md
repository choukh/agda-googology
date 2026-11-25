# 空白页样本: 折叠

> 判决: 成品候选 (折叠). 目标是第 0 层 (`ψ⊥`) 或 "层号 j 连同 j ≤ ℓ 的路径" (`ψs`); 结点保留与否只比路径, 两条路径都在同一个 ℓ 里 (字面公共上界).
> 嵌入分支 `up x c y` 交给孩子层的折叠, 底是 x 的折叠 (J2); 加法不打开 `up`.
> 不否定什么. 已知退让 (判断, 不是否定): `Ωₗ` 层分支侧的两条路径无从比较, 按 "不保留" 处理; 目标不在孩子里时 `up` 按 "x 的折叠 + 孩子的 ψ⊥" 处理.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFreshFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiFreshBlock
```

## 运算

加法按右边结构递归, `up` 原样保留 (约束 5). `next b` 是 b, b+b, … 的极限; `cum` 是部分和.

```agda
infixl 6 _+_
_+_ : ∀ {P B C D} → T P B C D → T P B C D → T P B C D
x + zero     = x
x + suc y    = suc (x + y)
x + lim f    = lim (λ n → x + f n)
x + Ω p g    = Ω p (λ z → x + g z)
x + up y c w = up (x + y) c w

iter : {A : Set} → (A → A) → A → ℕ → A
iter f a zero    = a
iter f a (suc n) = f (iter f a n)

next : ∀ {P B C D} → T P B C D → T P B C D
next b = lim (iter (b +_) b)

cum : ∀ {P B C D} → (ℕ → T P B C D) → ℕ → T P B C D
cum f zero    = f zero
cum f (suc n) = cum f n + f (suc n)
```

每一层的 Ω 树. 后继层取 sup (↑(c+1)); ℕ 极限层取孩子的 Ω 树的部分和.

```agda
Ωt : (ℓ : L) → Tr ℓ
Ωt zero     = suc zero
Ωt (suc a)  = Ω (inj₁ tt) (λ c → up zero tt (suc c))
Ωt (lim g)  = lim cumΩ
  where
  cumΩ : ℕ → Tr (lim g)
  cumΩ zero    = up zero zero (Ωt (g zero))
  cumΩ (suc n) = up (cumΩ n) (suc n) (Ωt (g (suc n)))
Ωt (Ωₗ k h) = Ω (inj₁ (inj₁ tt)) (λ c → up zero c (Ωt (h c)))

ι : (j : L) → Tr zero → Tr j
ι j zero       = zero
ι j (suc x)    = suc (ι j x)
ι j (lim f)    = lim (λ n → ι j (f n))
ι j (Ω () _)
ι j (up _ () _)
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

mutual
  posW : (ℓ : L) (p : Pos ℓ) → at ℓ p ≤ ℓ
  posW (suc a)  t              = ins (posW⁼ a t)
  posW (lim g)  (n , t)        = inl n (posW⁼ (g n) t)
  posW (Ωₗ k h) (inj₁ t)       = ink (posW⁼ k t)
  posW (Ωₗ k h) (inj₂ (c , t)) = inb c (posW⁼ (h c) t)

  posW⁼ : (a : L) (t : Pos⁼ a) → at⁼ a t ≤ a
  posW⁼ a (inj₁ _) = self
  posW⁼ a (inj₂ p) = posW a p
```

孩子编号只在 ℕ 上比较 (ℓ = lim g 时), 不比较层号.

```agda
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

## 保留判定

结点槽位 p 与目标路径 w 同在 ℓ 里. 若 p 沿 w 落进目标层, 交出它在目标层里的槽位与分支换型 (都是恒等), 否则走默认.

```agda
mutual
  kp : (ℓ : L) (p : Pos ℓ) {j : L} (w : j ≤ ℓ) {X : Set}
     → ((q : Pos j) → (Br j q → Br ℓ p) → X) → X → X
  kp ℓ         p        self      k d = k p (λ z → z)
  kp (suc a)   p        (ins w)   k d = kp⁼ a p w k d
  kp (lim g)   (m , p)  (inl n w) k d with eqℕ m n
  ... | just refl = kp⁼ (g m) p w k d
  ... | nothing   = d
  kp (Ωₗ k′ h) (inj₁ p) (ink w)   k d = kp⁼ k′ p w k d
  kp (Ωₗ k′ h) (inj₂ _) (ink w)   k d = d
  kp (Ωₗ k′ h) _        (inb c w) k d = d

  kp⁼ : (a : L) (p : Pos⁼ a) {j : L} (w : j ≤ a) {X : Set}
      → ((q : Pos j) → (Br j q → Br⁼ a p) → X) → X → X
  kp⁼ a (inj₁ _) w k d = d
  kp⁼ a (inj₂ p) w k d = kp a p w k d
```

## 折叠

`Base ℓ` 是 "偏移" 对每个目标的折叠 (记录, 有 η). 结点: 保留, 或沿结点自己的层做链 γ₀ = 0, γₙ₊₁ = ψ_p(g γₙ), 取部分和的极限;
目标等于结点层时也用这一式, 不另判相等. `up`: 目标在孩子里则交孩子层折叠; 目标是 ℓ 自身则原样保留嵌入; 其余按 x 的折叠加孩子的 ψ⊥.

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
  ψ⊥ ℓ B (Ω p g) = lim (cum (λ n → ψ⊥ ℓ B (g (iter step (fromBr ℓ p zero) n))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ B (at ℓ p) (posW ℓ p) (g z))
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
  ψs ℓ B j w (Ω p g) =
    kp ℓ p w (λ q cv → Ω q (λ z → ψs ℓ B j w (g (cv z))))
             (lim (cum (λ n → ψs ℓ B j w (g (iter step (fromBr ℓ p zero) n)))))
    where
    step : Br ℓ p → Br ℓ p
    step z = fromBr ℓ p (ψs ℓ B (at ℓ p) (posW ℓ p) (g z))
  ψs ℓ B _ self (up x c y) = up (ψs ℓ B ℓ self x) c y
  ψs (suc a) B j (ins w) (up x _ y) =
    ψs a (base (ψ⊥ (suc a) B x) (λ j′ w′ → ψs (suc a) B j′ (ins w′) x)) j w y
  ψs (lim g) B j (inl n w) (up x m y) with eqℕ m n
  ... | just refl =
    ψs (g m) (base (ψ⊥ (lim g) B x) (λ j′ w′ → ψs (lim g) B j′ (inl m w′) x)) j w y
  ... | nothing   = ψs (lim g) B j (inl n w) x + ι j (ψ⊥ (g m) (B₀ (g m)) y)
  ψs (Ωₗ k h) B j (ink w)    (up x c y) = ψs (Ωₗ k h) B j (ink w) x    + ι j (ψ⊥ (h c) (B₀ (h c)) y)
  ψs (Ωₗ k h) B j (inb c′ w) (up x c y) = ψs (Ωₗ k h) B j (inb c′ w) x + ι j (ψ⊥ (h c) (B₀ (h c)) y)

ψ₀ : (ℓ : L) → Tr ℓ → Tr zero
ψ₀ ℓ = ψ⊥ ℓ (B₀ ℓ)
```

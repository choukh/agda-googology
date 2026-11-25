# 空白页候选 B 的块: 层号是树, 孩子层是 "基底 + 1 + 孩子树", 孩子的树经结点 `ex` 嵌入

> 块 (不读记号). 层号 `Lv`: 零 `z`, 可数加法 `μ ⊞ c` (读作 μ+1+c, c 是层 μ 的树; 后继是 `μ ⊞ zero`), ℕ 极限 `l`, Ω 结点 `Ωₗ μ` (按层 μ 的树 c 分支, 孩子层是 μ ⊞ c). 树 `Tr ℓ`: 零, 后继, ℕ 极限, 位置 p 上的 Ω 极限, 以及 `ex x a y` (读作 x + y, y 是孩子层 a 的树, 保留自己的相对位置).
> 孩子层的位置分成基底部分 `Pos⁺ μ` (每个孩子里字面相同) 与增量部分; 孩子地址 `Ch` 只在 `ex` 结点里出现. 增量里 `ex` 的右边不贡献位置 (只取左边). 塔 `tw`, `Λ = l tw`, 各层的 Ω 树 `top`. 折叠在 [YiBPFold](YiBPFold.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBPBlock where

open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
```

## 树的形状

位置集 P 与分支类型 B, 孩子地址集 C 与孩子层的树 D.

```agda
data Br (P : Set) (B : P → Set) (C : Set) (D : C → Set) : Set where
  zero : Br P B C D
  suc  : Br P B C D → Br P B C D
  lim  : (ℕ → Br P B C D) → Br P B C D
  Ω    : (p : P) → (B p → Br P B C D) → Br P B C D
  ex   : Br P B C D → (a : C) → D a → Br P B C D

mapBr : ∀ {P P′ : Set} {B : P → Set} {B′ : P′ → Set} {C C′ : Set} {D : C → Set} {D′ : C′ → Set}
        (h : P → P′) → (∀ p → B′ (h p) → B p) → (h′ : C → C′) → (∀ a → D a → D′ (h′ a)) →
        Br P B C D → Br P′ B′ C′ D′
mapBr h k h′ k′ zero       = zero
mapBr h k h′ k′ (suc x)    = suc (mapBr h k h′ k′ x)
mapBr h k h′ k′ (lim f)    = lim (λ n → mapBr h k h′ k′ (f n))
mapBr h k h′ k′ (Ω p f)    = Ω (h p) (λ e → mapBr h k h′ k′ (f (k p e)))
mapBr h k h′ k′ (ex x a y) = ex (mapBr h k h′ k′ x) (h′ a) (k′ a y)

_+_ : ∀ {P B C D} → Br P B C D → Br P B C D → Br P B C D
x + zero     = x
x + suc y    = suc (x + y)
x + lim f    = lim (λ n → x + f n)
x + Ω p f    = Ω p (λ e → x + f e)
x + ex y a w = ex (x + y) a w
```

## 层号与各层的树 (归纳-递归)

`Pos ℓ`: ℓ 之下的层的位置 (含孩子内部的位置, 供 Ω 极限用); `Ch ℓ`: 孩子地址 (供 `ex` 用). `TrP μ c` 是层 μ ⊞ c 的树, 单独写出让检查器看出对 (μ, c) 的下降.

```agda
mutual
  data Lv : Set where
    z   : Lv
    _⊞_ : (μ : Lv) → Tr μ → Lv
    l   : (ℕ → Lv) → Lv
    Ωₗ  : Lv → Lv

  Tr : Lv → Set
  Tr ℓ = Br (Pos ℓ) (λ p → TrAt ℓ p) (Ch ℓ) (λ a → TrCh ℓ a)

  Pos⁺ : Lv → Set
  Pos⁺ μ = ⊤ ⊎ Pos μ

  Pos : Lv → Set
  Pos z       = ⊥
  Pos (μ ⊞ c) = Pos⁺ μ ⊎ IPos μ c
  Pos (l f)   = Σ ℕ (λ n → Pos⁺ (f n))
  Pos (Ωₗ μ)  = Pos⁺ μ ⊎ Σ (Tr μ) (λ c → ⊤ ⊎ IPos μ c)

  IPos : (μ : Lv) → Tr μ → Set
  IPos μ zero       = ⊥
  IPos μ (suc c)    = ⊤ ⊎ IPos μ c
  IPos μ (lim f)    = Σ ℕ (λ n → ⊤ ⊎ IPos μ (f n))
  IPos μ (Ω q f)    = Σ (TrAt μ q) (λ e → ⊤ ⊎ IPos μ (f e))
  IPos μ (ex x a y) = IPos μ x

  Ch : Lv → Set
  Ch z       = ⊥
  Ch (μ ⊞ c) = Ch μ ⊎ ChI μ c
  Ch (l f)   = Σ ℕ (λ n → Ch (f n))
  Ch (Ωₗ μ)  = Ch μ ⊎ Σ (Tr μ) (λ c → ⊤ ⊎ ChI μ c)

  ChI : (μ : Lv) → Tr μ → Set
  ChI μ zero       = ⊥
  ChI μ (suc c)    = ChI μ c
  ChI μ (lim f)    = Σ ℕ (λ n → ChI μ (f n))
  ChI μ (Ω q f)    = Σ (TrAt μ q) (λ e → ⊤ ⊎ ChI μ (f e))
  ChI μ (ex x a y) = ChI μ x

  TrAt⁺ : (μ : Lv) → Pos⁺ μ → Set
  TrAt⁺ μ (inj₁ _) = Tr μ
  TrAt⁺ μ (inj₂ q) = TrAt μ q

  TrAt : (ℓ : Lv) → Pos ℓ → Set
  TrAt z ()
  TrAt (μ ⊞ c) p                    = TrPAt μ c p
  TrAt (l f) (n , b)                = TrAt⁺ (f n) b
  TrAt (Ωₗ μ) (inj₁ b)              = TrAt⁺ μ b
  TrAt (Ωₗ μ) (inj₂ (c , inj₁ _))   = TrP μ c
  TrAt (Ωₗ μ) (inj₂ (c , inj₂ ip))  = TrI μ c ip

  TrCh : (ℓ : Lv) → Ch ℓ → Set
  TrCh ℓ a = Br (PCh ℓ a) (λ p → BCh ℓ a p) (CCh ℓ a) (λ b → DCh ℓ a b)

  TrP : (μ : Lv) → Tr μ → Set
  TrP μ c = Br (Pos⁺ μ ⊎ IPos μ c) (λ p → TrPAt μ c p) (Ch μ ⊎ ChI μ c) (λ a → TrChP μ c a)

  TrPAt : (μ : Lv) (c : Tr μ) → Pos⁺ μ ⊎ IPos μ c → Set
  TrPAt μ c (inj₁ b)  = TrAt⁺ μ b
  TrPAt μ c (inj₂ ip) = TrI μ c ip

  TrChP : (μ : Lv) (c : Tr μ) → Ch μ ⊎ ChI μ c → Set
  TrChP μ c a = Br (PChP μ c a) (λ p → BChP μ c a p) (CChP μ c a) (λ b → DChP μ c a b)

  TrI : (μ : Lv) (c : Tr μ) → IPos μ c → Set
  TrI μ (suc c) (inj₁ _)        = TrP μ c
  TrI μ (suc c) (inj₂ ip)       = TrI μ c ip
  TrI μ (lim f) (n , inj₁ _)    = TrP μ (f n)
  TrI μ (lim f) (n , inj₂ ip)   = TrI μ (f n) ip
  TrI μ (Ω q f) (e , inj₁ _)    = TrP μ (f e)
  TrI μ (Ω q f) (e , inj₂ ip)   = TrI μ (f e) ip
  TrI μ (ex x a y) ip           = TrI μ x ip

  TrChI : (μ : Lv) (c : Tr μ) → ChI μ c → Set
  TrChI μ c ia = Br (PChI μ c ia) (λ p → BChI μ c ia p) (CChI μ c ia) (λ b → DChI μ c ia b)

  PCh : (ℓ : Lv) (a : Ch ℓ) → Set
  PCh z ()
  PCh (μ ⊞ c) a = PChP μ c a
  PCh (l f) (n , a) = PCh (f n) a
  PCh (Ωₗ μ) (inj₁ a) = PCh μ a
  PCh (Ωₗ μ) (inj₂ (c , inj₁ _)) = Pos⁺ μ ⊎ IPos μ c
  PCh (Ωₗ μ) (inj₂ (c , inj₂ ia)) = PChI μ c ia

  PChP : (μ : Lv) (c : Tr μ) (a : Ch μ ⊎ ChI μ c) → Set
  PChP μ c (inj₁ a) = PCh μ a
  PChP μ c (inj₂ ia) = PChI μ c ia

  PChI : (μ : Lv) (c : Tr μ) (ia : ChI μ c) → Set
  PChI μ (suc c) ia = PChI μ c ia
  PChI μ (lim f) (n , ia) = PChI μ (f n) ia
  PChI μ (Ω q f) (e , inj₁ _) = Pos⁺ μ ⊎ IPos μ (f e)
  PChI μ (Ω q f) (e , inj₂ ia) = PChI μ (f e) ia
  PChI μ (ex x a′ y) ia = PChI μ x ia

  BCh : (ℓ : Lv) (a : Ch ℓ) → PCh ℓ a → Set
  BCh z ()
  BCh (μ ⊞ c) a p = BChP μ c a p
  BCh (l f) (n , a) p = BCh (f n) a p
  BCh (Ωₗ μ) (inj₁ a) p = BCh μ a p
  BCh (Ωₗ μ) (inj₂ (c , inj₁ _)) p = TrPAt μ c p
  BCh (Ωₗ μ) (inj₂ (c , inj₂ ia)) p = BChI μ c ia p

  BChP : (μ : Lv) (c : Tr μ) (a : Ch μ ⊎ ChI μ c) → PChP μ c a → Set
  BChP μ c (inj₁ a) p = BCh μ a p
  BChP μ c (inj₂ ia) p = BChI μ c ia p

  BChI : (μ : Lv) (c : Tr μ) (ia : ChI μ c) → PChI μ c ia → Set
  BChI μ (suc c) ia p = BChI μ c ia p
  BChI μ (lim f) (n , ia) p = BChI μ (f n) ia p
  BChI μ (Ω q f) (e , inj₁ _) p = TrPAt μ (f e) p
  BChI μ (Ω q f) (e , inj₂ ia) p = BChI μ (f e) ia p
  BChI μ (ex x a′ y) ia p = BChI μ x ia p

  CCh : (ℓ : Lv) (a : Ch ℓ) → Set
  CCh z ()
  CCh (μ ⊞ c) a = CChP μ c a
  CCh (l f) (n , a) = CCh (f n) a
  CCh (Ωₗ μ) (inj₁ a) = CCh μ a
  CCh (Ωₗ μ) (inj₂ (c , inj₁ _)) = Ch μ ⊎ ChI μ c
  CCh (Ωₗ μ) (inj₂ (c , inj₂ ia)) = CChI μ c ia

  CChP : (μ : Lv) (c : Tr μ) (a : Ch μ ⊎ ChI μ c) → Set
  CChP μ c (inj₁ a) = CCh μ a
  CChP μ c (inj₂ ia) = CChI μ c ia

  CChI : (μ : Lv) (c : Tr μ) (ia : ChI μ c) → Set
  CChI μ (suc c) ia = CChI μ c ia
  CChI μ (lim f) (n , ia) = CChI μ (f n) ia
  CChI μ (Ω q f) (e , inj₁ _) = Ch μ ⊎ ChI μ (f e)
  CChI μ (Ω q f) (e , inj₂ ia) = CChI μ (f e) ia
  CChI μ (ex x a′ y) ia = CChI μ x ia

  DCh : (ℓ : Lv) (a : Ch ℓ) → CCh ℓ a → Set
  DCh z ()
  DCh (μ ⊞ c) a b = DChP μ c a b
  DCh (l f) (n , a) b = DCh (f n) a b
  DCh (Ωₗ μ) (inj₁ a) b = DCh μ a b
  DCh (Ωₗ μ) (inj₂ (c , inj₁ _)) b = TrChP μ c b
  DCh (Ωₗ μ) (inj₂ (c , inj₂ ia)) b = DChI μ c ia b

  DChP : (μ : Lv) (c : Tr μ) (a : Ch μ ⊎ ChI μ c) → CChP μ c a → Set
  DChP μ c (inj₁ a) b = DCh μ a b
  DChP μ c (inj₂ ia) b = DChI μ c ia b

  DChI : (μ : Lv) (c : Tr μ) (ia : ChI μ c) → CChI μ c ia → Set
  DChI μ (suc c) ia b = DChI μ c ia b
  DChI μ (lim f) (n , ia) b = DChI μ (f n) ia b
  DChI μ (Ω q f) (e , inj₁ _) b = TrChP μ (f e) b
  DChI μ (Ω q f) (e , inj₂ ia) b = DChI μ (f e) ia b
  DChI μ (ex x a′ y) ia b = DChI μ x ia b
```

## 位置与地址上的层

```agda
sub : (μ : Lv) (c : Tr μ) → IPos μ c → Tr μ
sub μ (suc c) (inj₁ _)      = c
sub μ (suc c) (inj₂ ip)     = sub μ c ip
sub μ (lim f) (n , inj₁ _)  = f n
sub μ (lim f) (n , inj₂ ip) = sub μ (f n) ip
sub μ (Ω q f) (e , inj₁ _)  = f e
sub μ (Ω q f) (e , inj₂ ip) = sub μ (f e) ip
sub μ (ex x a y) ip         = sub μ x ip

subC : (μ : Lv) (c : Tr μ) → ChI μ c → Tr μ
subC μ (suc c) ia            = subC μ c ia
subC μ (lim f) (n , ia)      = subC μ (f n) ia
subC μ (Ω q f) (e , inj₁ _)  = f e
subC μ (Ω q f) (e , inj₂ ia) = subC μ (f e) ia
subC μ (ex x a y) ia         = subC μ x ia

mutual
  at⁺ : (μ : Lv) → Pos⁺ μ → Lv
  at⁺ μ (inj₁ _) = μ
  at⁺ μ (inj₂ q) = at μ q

  at : (ℓ : Lv) → Pos ℓ → Lv
  at z ()
  at (μ ⊞ c) (inj₁ b)             = at⁺ μ b
  at (μ ⊞ c) (inj₂ ip)            = μ ⊞ sub μ c ip
  at (l f) (n , b)                = at⁺ (f n) b
  at (Ωₗ μ) (inj₁ b)              = at⁺ μ b
  at (Ωₗ μ) (inj₂ (c , inj₁ _))   = μ ⊞ c
  at (Ωₗ μ) (inj₂ (c , inj₂ ip))  = μ ⊞ sub μ c ip

chAt : (ℓ : Lv) → Ch ℓ → Lv
chAt z ()
chAt (μ ⊞ c) (inj₁ a)             = chAt μ a
chAt (μ ⊞ c) (inj₂ ia)            = μ ⊞ subC μ c ia
chAt (l f) (n , a)                = chAt (f n) a
chAt (Ωₗ μ) (inj₁ a)              = chAt μ a
chAt (Ωₗ μ) (inj₂ (c , inj₁ _))   = μ ⊞ c
chAt (Ωₗ μ) (inj₂ (c , inj₂ ia))  = μ ⊞ subC μ c ia
```

`TrAt ℓ p` 与 `Tr (at ℓ p)` 逐情形相同, 换算在每个叶子上是恒等.

```agda
outI : ∀ μ c ip → TrI μ c ip → Tr (μ ⊞ sub μ c ip)
outI μ (suc c) (inj₁ _)      x = x
outI μ (suc c) (inj₂ ip)     x = outI μ c ip x
outI μ (lim f) (n , inj₁ _)  x = x
outI μ (lim f) (n , inj₂ ip) x = outI μ (f n) ip x
outI μ (Ω q f) (e , inj₁ _)  x = x
outI μ (Ω q f) (e , inj₂ ip) x = outI μ (f e) ip x
outI μ (ex y a w) ip         x = outI μ y ip x

inI : ∀ μ c ip → Tr (μ ⊞ sub μ c ip) → TrI μ c ip
inI μ (suc c) (inj₁ _)      x = x
inI μ (suc c) (inj₂ ip)     x = inI μ c ip x
inI μ (lim f) (n , inj₁ _)  x = x
inI μ (lim f) (n , inj₂ ip) x = inI μ (f n) ip x
inI μ (Ω q f) (e , inj₁ _)  x = x
inI μ (Ω q f) (e , inj₂ ip) x = inI μ (f e) ip x
inI μ (ex y a w) ip         x = inI μ y ip x

mutual
  out⁺ : ∀ μ b → TrAt⁺ μ b → Tr (at⁺ μ b)
  out⁺ μ (inj₁ _) x = x
  out⁺ μ (inj₂ q) x = out μ q x

  out : ∀ ℓ p → TrAt ℓ p → Tr (at ℓ p)
  out z ()
  out (μ ⊞ c) (inj₁ b)            x = out⁺ μ b x
  out (μ ⊞ c) (inj₂ ip)           x = outI μ c ip x
  out (l f) (n , b)               x = out⁺ (f n) b x
  out (Ωₗ μ) (inj₁ b)             x = out⁺ μ b x
  out (Ωₗ μ) (inj₂ (c , inj₁ _))  x = x
  out (Ωₗ μ) (inj₂ (c , inj₂ ip)) x = outI μ c ip x

mutual
  into⁺ : ∀ μ b → Tr (at⁺ μ b) → TrAt⁺ μ b
  into⁺ μ (inj₁ _) x = x
  into⁺ μ (inj₂ q) x = into μ q x

  into : ∀ ℓ p → Tr (at ℓ p) → TrAt ℓ p
  into z ()
  into (μ ⊞ c) (inj₁ b)            x = into⁺ μ b x
  into (μ ⊞ c) (inj₂ ip)           x = inI μ c ip x
  into (l f) (n , b)               x = into⁺ (f n) b x
  into (Ωₗ μ) (inj₁ b)             x = into⁺ μ b x
  into (Ωₗ μ) (inj₂ (c , inj₁ _))  x = x
  into (Ωₗ μ) (inj₂ (c , inj₂ ip)) x = inI μ c ip x
```

## 嵌入: 低层的树经位置加深进入高层

只改位置与地址, 分支类型与孩子的树逐字相同.

```agda
emb⊞ : ∀ μ c → Tr μ → Tr (μ ⊞ c)
emb⊞ μ c = mapBr (λ q → inj₁ (inj₂ q)) (λ q e → e) inj₁ (λ a y → y)

embS : ∀ μ c → Tr (μ ⊞ c) → Tr (μ ⊞ suc c)
embS μ c = mapBr h k (λ a → a) k′
  where
  h : Pos⁺ μ ⊎ IPos μ c → Pos⁺ μ ⊎ IPos μ (suc c)
  h (inj₁ b)  = inj₁ b
  h (inj₂ ip) = inj₂ (inj₂ ip)
  k : ∀ p → TrPAt μ (suc c) (h p) → TrPAt μ c p
  k (inj₁ b)  e = e
  k (inj₂ ip) e = e
  k′ : ∀ a → TrChP μ c a → TrChP μ (suc c) a
  k′ (inj₁ a)  y = y
  k′ (inj₂ ia) y = y

embL : ∀ μ (f : ℕ → Tr μ) n → Tr (μ ⊞ f n) → Tr (μ ⊞ lim f)
embL μ f n = mapBr h k h′ k′
  where
  h : Pos⁺ μ ⊎ IPos μ (f n) → Pos⁺ μ ⊎ IPos μ (lim f)
  h (inj₁ b)  = inj₁ b
  h (inj₂ ip) = inj₂ (n , inj₂ ip)
  k : ∀ p → TrPAt μ (lim f) (h p) → TrPAt μ (f n) p
  k (inj₁ b)  e = e
  k (inj₂ ip) e = e
  h′ : Ch μ ⊎ ChI μ (f n) → Ch μ ⊎ ChI μ (lim f)
  h′ (inj₁ a)  = inj₁ a
  h′ (inj₂ ia) = inj₂ (n , ia)
  k′ : ∀ a → TrChP μ (f n) a → TrChP μ (lim f) (h′ a)
  k′ (inj₁ a)  y = y
  k′ (inj₂ ia) y = y

embX : ∀ μ x a y → Tr (μ ⊞ x) → Tr (μ ⊞ ex x a y)
embX μ x a y = mapBr (λ p → p) k (λ c → c) k′
  where
  k : ∀ p → TrPAt μ (ex x a y) p → TrPAt μ x p
  k (inj₁ b)  e = e
  k (inj₂ ip) e = e
  k′ : ∀ c → TrChP μ x c → TrChP μ (ex x a y) c
  k′ (inj₁ c)  w = w
  k′ (inj₂ ia) w = w

embN : ∀ (f : ℕ → Lv) n → Tr (f n) → Tr (l f)
embN f n = mapBr (λ q → n , inj₂ q) (λ q x → x) (λ a → n , a) (λ a y → y)

embB : ∀ μ → Tr μ → Tr (Ωₗ μ)
embB μ = mapBr (λ q → inj₁ (inj₂ q)) (λ q x → x) inj₁ (λ a y → y)
```

## 各层的 Ω 树

`top ℓ` 读作 Ω_ℓ (读法是判断). 后继层: 对下一层全分支的 Ω 极限; 增量里的 Ω 极限与 Ω 结点: 对基底分支, 第 e 支是孩子层的 Ω 树, 经 `ex` 放进去 (左边是 0). 层 0 的 Ω 树是 1.

```agda
topP : ∀ μ c → Tr (μ ⊞ c)
topP μ zero       = Ω (inj₁ (inj₁ tt)) (λ e → emb⊞ μ zero e)
topP μ (suc c)    = Ω (inj₂ (inj₁ tt)) (λ e → embS μ c e)
topP μ (lim f)    = lim (λ n → embL μ f n (topP μ (f n)))
topP μ (Ω q f)    = Ω (inj₁ (inj₂ q)) (λ e → ex zero (inj₂ (e , inj₁ tt)) (topP μ (f e)))
topP μ (ex x a y) = embX μ x a y (topP μ x)

top : ∀ ℓ → Tr ℓ
top z       = suc zero
top (μ ⊞ c) = topP μ c
top (l f)   = lim (λ n → embN f n (top (f n)))
top (Ωₗ μ)  = Ω (inj₁ (inj₁ tt)) (λ c → ex zero (inj₂ (c , inj₁ tt)) (topP μ c))
```

## 塔与 Λ

```agda
tw : ℕ → Lv
tw zero    = z
tw (suc n) = Ωₗ (tw n)

Λ : Lv
Λ = l tw
```

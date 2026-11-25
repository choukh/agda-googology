# 上界工具 (二): 见证树 N₂ 的回灌只落在 Ω₁ 的线性类里

> 诊断：上界. 不进成品. 档: 编译定理 (形状), 无前提. `N₂` 的折叠沿链 `e₂ (n+1) = Gw (br₂ (e₂ n))` 取行; `feed-Lin`: 对第 1 层的**一切**树 z, `Gw (br₂ z)` 在类 `Lin` 里; 所以链的每一项都在 (`chain-Lin`).
> `Lin`: 由 `Ωt 1` 出发, 对三种运算封闭: 接一个分支为 `x + ι 1 (y c)` 的结点 (分支只经嵌入的可数树依赖下标), ℕ 极限, 加法. 类里没有 "分支上再长结点" 的树.
> 不给出什么: 没有 `read (ψ₀ … N₂)` 的值上界, 没有与记号参照的比较. `Lin` 的值上界 (Ω₁·d, d 可数) 在 [YiCeilSmall](YiCeilSmall.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCeilWit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inb)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSTw1 using (h₁; G)
open import OCF.Lean.YiT2Frame using (ε¹; ρ¹; β; two)
open import OCF.Lean.YiDecFlat using (mvC)
open import OCF.Lean.YiDecWit using (nb; d₂; N₂; br₂; Gw; e₂)
```

## 输入一侧的类

`node x` 就是 `x + β` (`node-form`). `Src`: 由 β 出发, 对 "右加 β", ℕ 极限, 孩子一侧槽位的结点封闭. 它对左加封闭 (`Src-+`), 所以对 `next` 封闭; 上折的像 (链不是 `stop`, 底在类里) 都在类里 (`Src-Up`).

```agda
node : Tr (tw 1) → Tr (tw 1)
node x = Ω (inj₁ (inj₁ tt)) (λ c → up x c (Ωt (h₁ c)) (Ωt-nz (h₁ c)))

node-form : (x : Tr (tw 1)) → x + β ≡ node x
node-form x = refl

IsCh : Pos (tw 1) → Set
IsCh q = Σ (Tr zero) λ c₀ → Σ (Pos⁼ (h₁ c₀)) λ t → q ≡ inj₂ (c₀ , t)

data Src : Tr (tw 1) → Set where
  sβ : Src (node zero)
  sn : ∀ {x} → Src x → Src (node x)
  sl : ∀ {f a} → ((n : ℕ) → Src (f n)) → Src (lim f a)
  sΩ : ∀ {q g} → IsCh q → ((z : Br (tw 1) q) → Src (g z)) → Src (Ω q g)

Src-+ : {x w : Tr (tw 1)} → Src x → Src w → Src (x + w)
Src-+ sx sβ        = sn sx
Src-+ sx (sn s)    = sn (Src-+ sx s)
Src-+ sx (sl h)    = sl (λ n → Src-+ sx (h n))
Src-+ sx (sΩ ic h) = sΩ ic (λ z → Src-+ sx (h z))

Src-iter : {b : Tr (tw 1)} → Src b → (n : ℕ) → Src (iter (b +_) b n)
Src-iter sb zero    = sb
Src-iter sb (suc n) = Src-+ sb (Src-iter sb n)

Src-next : {b : Tr (tw 1)} {nz : tw 1 ⊢ zero ◃ b} → Src b → Src (next b nz)
Src-next sb = sl (Src-iter sb)

NS : ∀ {ℓ j} → Dn ℓ j → Set
NS stop       = ⊥
NS (down _ _) = ⊤

isCh : ∀ {j} (d : Dn (tw 1) j) → NS d → (p : Pos j) → IsCh (mv d p)
isCh (down d c) _ p = mvC zero h₁ d c p

Src-Up : (j : LF) (d : Dn (tw 1) j) → NS d → (b : Tr (tw 1)) (nb′ : tw 1 ⊢ zero ◃ b) → Src b
  → (y : Tr j) → Src (Up j d b nb′ y)
Src-Up j d ns b nb′ sb zero      = sb
Src-Up j d ns b nb′ sb (suc y)   = Src-next (Src-Up j d ns b nb′ sb y)
Src-Up j d ns b nb′ sb (lim f a) = sl (λ n → Src-Up j d ns b nb′ sb (f n))
Src-Up j d ns b nb′ sb (Ω p g)   = sΩ (isCh d ns p) (λ z → Src-Up j d ns b nb′ sb (g (mvBr d p z)))
Src-Up (suc a)  d ns b nb′ sb (up y _ y′ _) =
  Src-Up a (down d tt) tt (Up (suc a) d b nb′ y) (Up-nz (suc a) d b nb′ y) (Src-Up (suc a) d ns b nb′ sb y) y′
Src-Up (lim g)  d ns b nb′ sb (up y n y′ _) =
  Src-Up (g n) (down d n) tt (Up (lim g) d b nb′ y) (Up-nz (lim g) d b nb′ y) (Src-Up (lim g) d ns b nb′ sb y) y′
Src-Up (Ωₗ k h) d ns b nb′ sb (up y c y′ _) =
  Src-Up (h c) (down d c) tt (Up (Ωₗ k h) d b nb′ y) (Up-nz (Ωₗ k h) d b nb′ y) (Src-Up (Ωₗ k h) d ns b nb′ sb y) y′
Src-Up zero     d ns b nb′ sb (up y () _ _)
```

## 输出一侧的类

`ext x y`: 分支 c 上是 `x + ι 1 (y c)` 的结点. 回退行造的结点都是这种 (y 取 `G`, 即分支层号上 Ω 树的标准折叠).

```agda
ext : Tr (suc zero) → (Tr zero → Tr zero) → Tr (suc zero)
ext x y = Ω (inj₁ tt) (λ c → x + ι (suc zero) (y c))

data Lin : Tr (suc zero) → Set where
  l0 : Lin (Ωt (suc zero))
  lx : ∀ {x} → Lin x → (y : Tr zero → Tr zero) → Lin (ext x y)
  ll : ∀ {f a} → ((n : ℕ) → Lin (f n)) → Lin (lim f a)
  l+ : ∀ {x y} → Lin x → Lin y → Lin (x + y)

Lin-cum : (F : ℕ → Tr (suc zero)) → ((n : ℕ) → Lin (F n)) → (n : ℕ) → Lin (cum F n)
Lin-cum F h zero    = h zero
Lin-cum F h (suc n) = l+ (Lin-cum F h n) (h (suc n))
```

## 朝第 1 层的折叠把 `Src` 送进 `Lin`

四行: β 与 "右加 β" 走保留一行, 分支上是回退行 (`Gw x + ι 1 (G c)`); ℕ 极限逐项; 孩子一侧槽位的结点走摊平式, 成为部分和的极限.

```agda
Gw-Src : {x : Tr (tw 1)} → Src x → Lin (Gw x)
Gw-Src sβ        = lx l0 G
Gw-Src (sn s)    = lx (Gw-Src s) G
Gw-Src (sl h)    = ll (λ n → Gw-Src (h n))
Gw-Src (sΩ {g = g} (c₀ , t , refl) h) =
  ll (Lin-cum (λ n → Gw (g (stp n))) (λ n → Gw-Src (h (stp n))))
  where
  stp : ℕ → Br (tw 1) (inj₂ (c₀ , t))
  stp = iter (λ z → fromBr (tw 1) (inj₂ (c₀ , t))
          (ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (at (tw 1) (inj₂ (c₀ , t))) (OCF.Lean.YiLegPath.posW (tw 1) (inj₂ (c₀ , t)))
            (bs (B₀ (tw 1)) (at (tw 1) (inj₂ (c₀ , t))) (OCF.Lean.YiLegPath.posW (tw 1) (inj₂ (c₀ , t))))
            (ns (B₀ (tw 1)) (at (tw 1) (inj₂ (c₀ , t))) (OCF.Lean.YiLegPath.posW (tw 1) (inj₂ (c₀ , t))))
            (g z))) (br0 (tw 1) (inj₂ (c₀ , t)))
```

## N₂ 的回灌

`br₂ z` 是 `next (Up … β z)`, 在 `Src` 里; 所以对一切 z, `Gw (br₂ z)` 在 `Lin` 里. z 里的结点 (不论分支的形状) 不进入输出的结点.

```agda
br₂-Src : (z : Tr (suc zero)) → Src (br₂ z)
br₂-Src z = Src-next (Src-Up (suc zero) d₂ tt β nb sβ z)

feed-Lin : (z : Tr (suc zero)) → Lin (Gw (br₂ z))
feed-Lin z = Gw-Src (br₂-Src z)

chain-Lin : (n : ℕ) → Lin (e₂ (suc n))
chain-Lin n = feed-Lin (e₂ n)
```

## 自身行的全部输出

不限于 N₂: 对一切分支 c 与孩子层 `h₁ c` 的一切树 y, 自身行的输出 `Upc (tw 1) c β nb y` 朝第 1 层折叠后都在 `Lin` 里. N₂ 是 c 取 `two`, y 取 `Ωt (h₁ two)` 的一例.

```agda
self-Lin : (c : Tr zero) (y : Tr (h₁ c)) → Lin (Gw (Upc (tw 1) c β nb y))
self-Lin c y = Gw-Src (Src-Up (h₁ c) (down stop c) tt β nb sβ y)

N₂-Lin : Lin (Gw N₂)
N₂-Lin = self-Lin two (Ωt (h₁ two))
```

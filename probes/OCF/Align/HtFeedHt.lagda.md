# 高度是树 (三): 高度的生成

> 不含记号. 入口 [HtFeed](HtFeed.lagda.md). 高度 `H` 的元素怎么来. **不加坐标**: 一切高度都是同一个类型 `H` 的树, 生成它们的是三条对一切级成立的规则, 合法性 (`LgH`) 都由形状给出 (第一位置只走 $\Omega$-分支的坐标 $0$, 所以在世界 $0$ 上成立, 搬到一切世界).
>
> - `emb`: 可数的高度就是 `A` 的树换构造子. `Ωᴴ = hΩ emb`: 一切可数高度之上的高度, 读 $\Omega$. 这正是 `HtGen.no-top` 说 `A` 里没有的那个顶; 在 `H` 里它是一个合法的元素 (`Lg-Ωᴴ`), 但它的第一位置要带世界 (`below-Ω`).
> - **一阶: 算子.** `Fn = H → H`, `Good`: 保合法, 往上走. `it F x c`: 沿可数的 $c$ 迭代 $F$. `Ωit F x = hΩ (λ c → F^c (F x))`: $\Omega$-迭代. 折叠到第 0 层时, 这个 $\Omega$-极限的分支 $c$ 由回灌给出, 所以 **"迭代几次" 是折叠的输出**.
> - **二阶: 算子的变换.** `Tr`: 把好算子变成好算子, 往上走. `Hier T F c`: 沿可数的 $c$ 迭代变换 $T$. `ΩD G = λ x → hΩ (λ c → G c x)`: 算子族的 $\Omega$-对角. `upT T F = ΩD (Hier T (T F))`.
> - **ℕ-对角**: `Upω`, `Tω`.
>
> 读法 (都是判断, 按通常的布劳威尔树算术): `Up k x` 读 $x+\Omega^k$, `Upω hz` 读 $\Omega^\omega$, `Tk 1` 作用于后继读 $x+\Omega^\Omega$, `Tk k` 读 $x+\Omega^{\Omega^k}$, `Tω` 读 $x+\Omega^{\Omega^\omega}$.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtFeedHt where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree using (H; hz; hs; hl; hΩ; _⊲[_]_; hself; hsuc; hlim; hLim; ⊲ᴴ-tr; ⊲ᴴ↑; ⊲ᴴ0; LgH)
```

## §1 可数的高度, $\Omega$

```agda
emb : A → H
emb azero = hz
emb (asuc a) = hs (emb a)
emb (alim f) = hl (λ n → emb (f n))

emb⊲ : ∀ {a b} → a ⊲ b → emb a ⊲[ azero ] emb b
emb⊲ C.self = hself
emb⊲ (C.suc p) = hsuc (emb⊲ p)
emb⊲ (C.lim n p) = hlim n (emb⊲ p)

Lg-emb : ∀ a → Lg a → LgH (emb a)
Lg-emb azero _ = tt
Lg-emb (asuc a) l = Lg-emb a l
Lg-emb (alim f) (st , l) = (λ n → emb⊲ (st n)) , (λ n → Lg-emb (f n) (l n))

Ωᴴ : H
Ωᴴ = hΩ emb

Lg-Ωᴴ : LgH Ωᴴ
Lg-Ωᴴ = (λ _ p → ⊲ᴴ0 (emb⊲ p)) , Lg-emb

-- 可数高度在 Ω 之下, 只在含它的世界里
below-Ω : ∀ {W} c → c ⊲ W → emb c ⊲[ W ] Ωᴴ
below-Ω c e = hLim e hself
```

## §2 一阶: 算子与 $\Omega$-迭代

```agda
Fn : Set
Fn = H → H

record Good (F : Fn) : Set where
  constructor gd
  field
    lf  : ∀ h → LgH h → LgH (F h)
    fst : ∀ h → h ⊲[ azero ] F h
open Good public

it : Fn → H → A → H
it F x azero = x
it F x (asuc c) = F (it F x c)
it F x (alim g) = hl (λ n → it F x (g n))

it⊲ : ∀ {F} → Good F → ∀ x {c c′} → c ⊲ c′ → it F x c ⊲[ azero ] it F x c′
it⊲ gF x C.self = hself
it⊲ gF x (C.suc p) = ⊲ᴴ-tr (it⊲ gF x p) (fst gF _)
it⊲ gF x (C.lim n p) = hlim n (it⊲ gF x p)

Lg-it : ∀ {F} → Good F → ∀ x → LgH x → ∀ c → Lg c → LgH (it F x c)
Lg-it gF x lx azero _ = lx
Lg-it gF x lx (asuc c) l = lf gF _ (Lg-it gF x lx c l)
Lg-it gF x lx (alim g) (st , l) = (λ n → it⊲ gF x (st n)) , (λ n → Lg-it gF x lx (g n) (l n))

-- Ω-迭代: 第 c 支是 F^c (F x)
Ωit : Fn → Fn
Ωit F x = hΩ (it F (F x))

Good-Ωit : ∀ {F} → Good F → Good (Ωit F)
Good-Ωit {F} gF = gd (λ x lx → (λ _ p → ⊲ᴴ0 (it⊲ gF (F x) p)) , Lg-it gF (F x) (lf gF x lx)) (λ h → hLim C.self (fst gF h))

-- 第 0 支就是 F x
Ωit-inf : ∀ F x → F x ⊲[ azero ] Ωit F x
Ωit-inf F x = hLim C.self hself

Good-hs : Good hs
Good-hs = gd (λ h l → l) (λ h → hsuc hself)

Up : ℕ → Fn
Up zero = hs
Up (suc k) = Ωit (Up k)

Good-Up : ∀ k → Good (Up k)
Good-Up zero = Good-hs
Good-Up (suc k) = Good-Ωit (Good-Up k)

Upω : Fn
Upω x = hl (λ k → Up k x)

Good-Upω : Good Upω
Good-Upω = gd (λ x lx → (λ k → Ωit-inf (Up k) x) , (λ k → lf (Good-Up k) x lx)) (λ h → hlim 0 (fst Good-hs h))
```

## §3 二阶: 变换, 沿可数的迭代, $\Omega$-对角

```agda
record Tr : Set where
  constructor tr
  field
    T    : Fn → Fn
    Tgd  : ∀ {F} → Good F → Good (T F)
    Tinf : ∀ F x → F x ⊲[ azero ] T F x
open Tr public

Hier : (Fn → Fn) → Fn → A → Fn
Hier T F azero = F
Hier T F (asuc c) = T (Hier T F c)
Hier T F (alim g) x = hl (λ n → Hier T F (g n) x)

Hier⊲ : ∀ (𝒯 : Tr) F {c c′} → c ⊲ c′ → ∀ x → Hier (T 𝒯) F c x ⊲[ azero ] Hier (T 𝒯) F c′ x
Hier⊲ 𝒯 F C.self x = hself
Hier⊲ 𝒯 F (C.suc p) x = ⊲ᴴ-tr (Hier⊲ 𝒯 F p x) (Tinf 𝒯 _ x)
Hier⊲ 𝒯 F (C.lim n p) x = hlim n (Hier⊲ 𝒯 F p x)

Good-Hier : ∀ (𝒯 : Tr) {F} → Good F → ∀ c → Lg c → Good (Hier (T 𝒯) F c)
Good-Hier 𝒯 gF azero _ = gF
Good-Hier 𝒯 gF (asuc c) l = Tgd 𝒯 (Good-Hier 𝒯 gF c l)
Good-Hier 𝒯 {F} gF (alim g) (st , l) =
  gd (λ x lx → (λ n → Hier⊲ 𝒯 F (st n) x) , (λ n → lf (Good-Hier 𝒯 gF (g n) (l n)) x lx))
     (λ h → hlim 0 (fst (Good-Hier 𝒯 gF (g 0) (l 0)) h))

-- 算子族的 Ω-对角
ΩD : (A → Fn) → Fn
ΩD G x = hΩ (λ c → G c x)

upT : Tr → Tr
upT 𝒯 = tr (λ F → ΩD (Hier (T 𝒯) (T 𝒯 F)))
  (λ {F} gF → gd (λ x lx → (λ _ p → ⊲ᴴ0 (Hier⊲ 𝒯 (T 𝒯 F) p x)) , (λ c lc → lf (Good-Hier 𝒯 (Tgd 𝒯 gF) c lc) x lx))
                 (λ h → hLim C.self (⊲ᴴ-tr (fst gF h) (Tinf 𝒯 F h))))
  (λ F x → hLim C.self (Tinf 𝒯 F x))

T₀ : Tr
T₀ = tr Ωit Good-Ωit Ωit-inf

Tk : ℕ → Tr
Tk zero = T₀
Tk (suc k) = upT (Tk k)

-- 第 k+1 级的第 0 支就是第 k 级
Tk⊲ : ∀ k F x → T (Tk k) F x ⊲[ azero ] T (Tk (suc k)) F x
Tk⊲ k F x = hLim C.self hself

Tω : Fn → Fn
Tω F x = hl (λ k → T (Tk k) F x)

Good-Tω : ∀ {F} → Good F → Good (Tω F)
Good-Tω {F} gF = gd (λ x lx → (λ k → Tk⊲ k F x) , (λ k → lf (Tgd (Tk k) gF) x lx))
                    (λ h → hlim 0 (⊲ᴴ-tr (fst gF h) (Tinf (Tk 0) F h)))
```

## §4 高度的闭项

都从 $0$ 出发, 合法性都是上面的一般定理的实例. 读法是判断.

```agda
lz : LgH hz
lz = tt

-- Ω, Ω+1, Ω·2, Ω^k, Ω^ω, Ω^Ω, Ω^{Ω^k}, Ω^{Ω^ω}
h-Ω h-Ω+1 h-Ω·2 h-Ωω h-ΩΩ h-ΩΩω : H
h-Ω = Ωᴴ
h-Ω+1 = hs Ωᴴ
h-Ω·2 = Ωit hs Ωᴴ
h-Ωω = Upω hz
h-ΩΩ = T (Tk 1) hs hz
h-ΩΩω = Tω hs hz

h-Ωk : ℕ → H
h-Ωk k = Up k hz

h-ΩΩk : ℕ → H
h-ΩΩk k = T (Tk k) hs hz

l-Ω : LgH h-Ω
l-Ω = Lg-Ωᴴ

l-Ω+1 : LgH h-Ω+1
l-Ω+1 = Lg-Ωᴴ

l-Ω·2 : LgH h-Ω·2
l-Ω·2 = lf (Good-Ωit Good-hs) Ωᴴ Lg-Ωᴴ

l-Ωk : ∀ k → LgH (h-Ωk k)
l-Ωk k = lf (Good-Up k) hz lz

l-Ωω : LgH h-Ωω
l-Ωω = lf Good-Upω hz lz

l-ΩΩk : ∀ k → LgH (h-ΩΩk k)
l-ΩΩk k = lf (Tgd (Tk k) Good-hs) hz lz

l-ΩΩ : LgH h-ΩΩ
l-ΩΩ = l-ΩΩk 1

l-ΩΩω : LgH h-ΩΩω
l-ΩΩω = lf (Good-Tω Good-hs) hz lz
```

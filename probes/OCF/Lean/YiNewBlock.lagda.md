# YiNew 块: 层号是树, 各层的树是同一个泛型树

判决 (编译定理): 层号 `Lv` 与各层的树 `T` 归纳-递归地写出; 塔 `tw` 与 `Λ` 对字面层序合法 (`tw-legal`, `Λ-legal`).
做了什么: 泛型树 `Tr` (零, 后继, ℕ 极限, 按码分支, 嵌入 `up`), 层号四种构造子, 读回 `inj`, 塔.
不否定什么: `Legal` 不含 "Ω 结点的各分支合法", 这一条没有做.
入口: 折叠在 `OCF.Lean.YiNewFold`, 验收在 `OCF.Lean.YiNewKey`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNewBlock where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
```

## 泛型树

`U` 是分支码, `B u` 是分支类型; `E` 是嵌入码, `M e` 是被嵌入的低层树.
`up x e y` 读作 x 再加上嵌入的 y. 分支只出现在 `Lm`, `up` 不带函数.

```agda
data Tr (U : Set) (B : U → Set) (E : Set) (M : E → Set) : Set where
  zr : Tr U B E M
  sc : Tr U B E M → Tr U B E M
  lm : (ℕ → Tr U B E M) → Tr U B E M
  Lm : (u : U) → (B u → Tr U B E M) → Tr U B E M
  up : Tr U B E M → (e : E) → M e → Tr U B E M
```

## 层号与各层的树

层号 `Om a f` 按 a 层的树分支. 码与分支类型对层号递归, 所以 `T a` 可以出现在 `Om` 的定义域里.
Ω 结点层 `Om a f` 的分支码是 "孩子 c 连同孩子层里的码", 嵌入码是孩子 c 本身.

```agda
data Lv : Set
U  : Lv → Set
Br : (ℓ : Lv) → U ℓ → Set
E  : Lv → Set
Em : (ℓ : Lv) → E ℓ → Set
T  : Lv → Set

data Lv where
  ze : Lv
  su : Lv → Lv
  li : (ℕ → Lv) → Lv
  Om : (a : Lv) → (T a → Lv) → Lv

T ℓ = Tr (U ℓ) (Br ℓ) (E ℓ) (Em ℓ)

U ze       = ⊥
U (su ℓ)   = ⊤ ⊎ U ℓ
U (li f)   = Σ ℕ (λ n → U (f n))
U (Om a f) = Σ (T a) (λ c → U (f c))

Br (su ℓ)   (inj₁ _) = T ℓ
Br (su ℓ)   (inj₂ u) = Br ℓ u
Br (li f)   (n , u)  = Br (f n) u
Br (Om a f) (c , u)  = Br (f c) u

E ze       = ⊥
E (su ℓ)   = ⊤
E (li f)   = ℕ
E (Om a f) = T a

Em (su ℓ)   _ = T ℓ
Em (li f)   n = T (f n)
Em (Om a f) c = T (f c)
```

有限层与每个分支类型里的零 (第一位置).

```agda
fin : ℕ → Lv
fin zero    = ze
fin (suc k) = su (fin k)

F : ℕ → Set
F k = T (fin k)

z0 : (ℓ : Lv) (u : U ℓ) → Br ℓ u
z0 (su ℓ)   (inj₁ _) = zr
z0 (su ℓ)   (inj₂ u) = z0 ℓ u
z0 (li f)   (n , u)  = z0 (f n) u
z0 (Om a f) (c , u)  = z0 (f c) u
```

## 读回: 树当层号

`inj ℓ x` 把 ℓ 层的树 x 读成层号. 分支结点读成 Ω 结点层号, 嵌入读成层号的加法.

```agda
lvU : (ℓ : Lv) → U ℓ → Lv
lvU (su ℓ)   (inj₁ _) = ℓ
lvU (su ℓ)   (inj₂ u) = lvU ℓ u
lvU (li f)   (n , u)  = lvU (f n) u
lvU (Om a f) (c , u)  = lvU (f c) u

cvt : (ℓ : Lv) (u : U ℓ) → T (lvU ℓ u) → Br ℓ u
cvt (su ℓ)   (inj₁ _) x = x
cvt (su ℓ)   (inj₂ u) x = cvt ℓ u x
cvt (li f)   (n , u)  x = cvt (f n) u x
cvt (Om a f) (c , u)  x = cvt (f c) u x

infixl 6 _⊕_
_⊕_ : Lv → Lv → Lv
a ⊕ ze     = a
a ⊕ su b   = su (a ⊕ b)
a ⊕ li f   = li (λ n → a ⊕ f n)
a ⊕ Om b f = Om b (λ c → a ⊕ f c)

inj  : (ℓ : Lv) → T ℓ → Lv
injE : (ℓ : Lv) (e : E ℓ) → Em ℓ e → Lv
inj ℓ zr         = ze
inj ℓ (sc x)     = su (inj ℓ x)
inj ℓ (lm g)     = li (λ n → inj ℓ (g n))
inj ℓ (Lm u g)   = Om (lvU ℓ u) (λ z → inj ℓ (g (cvt ℓ u z)))
inj ℓ (up x e y) = inj ℓ x ⊕ injE ℓ e y
injE (su ℓ)   _ y = inj ℓ y
injE (li f)   n y = inj (f n) y
injE (Om a f) c y = inj (f c) y
```

## 塔与 Λ

`tw (n+1)` 是以 `tw n` 为下标层的 Ω 结点层号; 孩子 c 的层是 `tw n` 之上再加 c 读回的层号, 再加一.
孩子层字面地高于下标层, 所以相邻两项的次序有字面证据 (孩子取零).

```agda
tw : ℕ → Lv
tw zero    = ze
tw (suc n) = Om (tw n) (λ c → su (tw n ⊕ inj (tw n) c))

Λ : Lv
Λ = li tw
```

## 字面层序与合法性

`⊑` 只沿后继, ℕ 极限的某一项, Ω 结点的某个指定孩子上升; 不比较两个孩子.
`Legal` 要求 ℕ 极限相邻项严格上升. Ω 结点只要求下标层合法 (分支的合法性没有纳入).

```agda
infix 4 _⊑_ _⊏_
data _⊑_ : Lv → Lv → Set where
  rf  : ∀ {ℓ} → ℓ ⊑ ℓ
  ⊑su : ∀ {ℓ m} → ℓ ⊑ m → ℓ ⊑ su m
  ⊑li : ∀ {ℓ f} n → ℓ ⊑ f n → ℓ ⊑ li f
  ⊑ch : ∀ {ℓ a f} c → ℓ ⊑ f c → ℓ ⊑ Om a f

_⊏_ : Lv → Lv → Set
ℓ ⊏ m = su ℓ ⊑ m

Legal : Lv → Set
Legal ze       = ⊤
Legal (su ℓ)   = Legal ℓ
Legal (li f)   = ∀ n → Legal (f n) × (f n ⊏ f (suc n))
Legal (Om a f) = Legal a

tw-step : ∀ n → tw n ⊏ tw (suc n)
tw-step n = ⊑ch zr rf

tw-legal : ∀ n → Legal (tw n)
tw-legal zero    = tt
tw-legal (suc n) = tw-legal n

Λ-legal : Legal Λ
Λ-legal n = tw-legal n , tw-step n
```

# 没有闭包的世界: 字面的层, 字面的折叠

> 不含记号. 结论写在 [CumRead](CumRead.lagda.md). 这一篇是 $\psi_0(\Omega_\eta)$ 对 **任意** 字面合法的可数层 $\eta$ 的折叠, 不带地板, 不带帧, 不带 `≈` 上的搬运: 比较只在同一棵合法层的两个第一位置之间 (`cmpN`, `cmpF`), 答案里的层就是字面的那一层.
>
> - `A`: 层, 只有 $0$, 后继, $\omega$-极限. `a ⊲ b`: $a$ 字面地是 $b$ 的第一位置. `k ≪ L`: 节点的路径. `Lg`: 极限的相邻项是字面第一位置.
> - `O L`: 数据树. `oi r h`: 第 $r$ 个节点 ($\Omega_{k+1}$ 的分支), `oe R x`: 低层元素的 **懒嵌入**, 折叠时直接走进去, 所以不需要 $\iota$ 的算律.
> - `_⊕⟨_⟩_`: 右边可以是低一层的元素. `rep`: $y\cdot n$.
> - `ψ`: 折叠, 目标 $t$ 与当前层字面可比 (`Tg`). 节点低于目标就保留, 否则上升: $\lim_n\psi_t(h(z_n))$, $z_0=\Omega_k$, $z_{n+1}=\psi_k(h(z_n))$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumReadCF where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
```

## §1 层

```agda
data A : Set where
  azero : A
  asuc  : A → A
  alim  : (ℕ → A) → A

infix 4 _⊲_ _≪_
data _⊲_ : A → A → Set where
  self : ∀ {a} → a ⊲ a
  suc  : ∀ {a b} → a ⊲ b → a ⊲ asuc b
  lim  : ∀ {a f} n → a ⊲ f n → a ⊲ alim f

data _≪_ : A → A → Set where
  zero : ∀ {a} → a ≪ asuc a
  suc  : ∀ {a b} → a ≪ b → a ≪ asuc b
  lim  : ∀ {a f} n → a ≪ f n → a ≪ alim f

data Strict (a : A) : A → Set where
  ss : ∀ {b} → a ⊲ b → Strict a (asuc b)
  sl : ∀ {f} n → a ⊲ f n → Strict a (alim f)

Lg : A → Set
Lg azero = ⊤
Lg (asuc a) = Lg a
Lg (alim f) = (∀ n → f n ⊲ f (suc n)) × (∀ n → Lg (f n))

⊲-tr : ∀ {a b c} → a ⊲ b → b ⊲ c → a ⊲ c
⊲-tr p self = p
⊲-tr p (suc q) = suc (⊲-tr p q)
⊲-tr p (lim n q) = lim n (⊲-tr p q)

≪⊲ : ∀ {a b} → a ≪ b → a ⊲ b
≪⊲ zero = suc self
≪⊲ (suc r) = suc (≪⊲ r)
≪⊲ (lim n r) = lim n (≪⊲ r)

≪∘ : ∀ {k a b} → k ≪ a → a ⊲ b → k ≪ b
≪∘ r self = r
≪∘ r (suc q) = suc (≪∘ r q)
≪∘ r (lim n q) = lim n (≪∘ r q)

S→⊲ : ∀ {a b} → Strict a b → a ⊲ b
S→⊲ (ss P) = suc P
S→⊲ (sl n P) = lim n P

≪S : ∀ {a b} → a ≪ b → Strict a b
≪S zero = ss self
≪S (suc r) = ss (≪⊲ r)
≪S (lim n r) = sl n (≪⊲ r)

S∘ : ∀ {a b c} → Strict a b → b ⊲ c → a ⊲ c
S∘ R q = ⊲-tr (S→⊲ R) q

lg⊲ : ∀ {a b} → a ⊲ b → Lg b → Lg a
lg⊲ self w = w
lg⊲ (suc p) w = lg⊲ p w
lg⊲ (lim n p) w = lg⊲ p (proj₂ w n)

lgS : ∀ {a b} → Strict a b → Lg b → Lg a
lgS R w = lg⊲ (S→⊲ R) w

z⊲ : ∀ a → azero ⊲ a
z⊲ azero = self
z⊲ (asuc a) = suc (z⊲ a)
z⊲ (alim f) = lim 0 (z⊲ (f 0))

steps : ∀ {f : ℕ → A} → (∀ n → f n ⊲ f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊲ f m
steps s zero = s _
steps s (suc q) = ⊲-tr (steps s q) (s _)
```

**比较.** 同一棵合法层的两个第一位置可比. 对上界结构递归, 极限处用字面的步进把两边搬到同一项. 这就是 `cmpC` 在这里的形状. 没有比较两个任意的层.

```agda
data Rk (k t : A) : Set where
  keep : k ≪ t → Rk k t
  rise : t ⊲ k → Rk k t

cmpN : ∀ {k t L} → k ≪ L → t ⊲ L → Lg L → Rk k t
cmpN r self w = keep r
cmpN zero (suc q) w = rise q
cmpN (suc r) (suc q) w = cmpN r q w
cmpN (lim n r) (lim m q) (st , w) with <ᴺ-dec n m
... | injᵃ n<m = cmpN (≪∘ r (steps st n<m)) q (w m)
... | injᵇ m<n = cmpN r (⊲-tr q (steps st m<n)) (w n)
... | injᶜ refl = cmpN r q (w n)

cmpF : ∀ {a t L} → a ⊲ L → t ⊲ L → Lg L → (t ⊲ a) ⊎ (a ⊲ t)
cmpF self q w = inj₁ q
cmpF p self w = inj₂ p
cmpF (suc p) (suc q) w = cmpF p q w
cmpF (lim n p) (lim m q) (st , w) with <ᴺ-dec n m
... | injᵃ n<m = cmpF (⊲-tr p (steps st n<m)) q (w m)
... | injᵇ m<n = cmpF p (⊲-tr q (steps st m<n)) (w n)
... | injᶜ refl = cmpF p q (w n)
```

## §2 数据树

```agda
module _ (L : A) (V : ∀ {a} → Strict a L → Set) where
  data O₊ : Set where
    o0 : O₊
    os : O₊ → O₊
    ol : (ℕ → O₊) → O₊
    oi : ∀ {k} (r : k ≪ L) → (V (≪S r) → O₊) → O₊
    oe : ∀ {a} (R : Strict a L) → V R → O₊

O  : A → Set
Vs : ∀ L {a} → Strict a L → Set
Vc : ∀ b {a} → a ⊲ b → Set
O L = O₊ L (Vs L)
Vs (asuc b) (ss P) = Vc b P
Vs (alim f) (sl n P) = Vc (f n) P
Vc a self = O a
Vc (asuc b) (suc P) = Vc b P
Vc (alim f) (lim n P) = Vc (f n) P

outC : ∀ {b a} (P : a ⊲ b) → Vc b P → O a
outC self x = x
outC (suc P) x = outC P x
outC (lim n P) x = outC P x

inC : ∀ {b a} (P : a ⊲ b) → O a → Vc b P
inC self x = x
inC (suc P) x = inC P x
inC (lim n P) x = inC P x

outS : ∀ {b a} (R : Strict a b) → Vs b R → O a
outS (ss P) x = outC P x
outS (sl n P) x = outC P x

inS : ∀ {b a} (R : Strict a b) → O a → Vs b R
inS (ss P) x = inC P x
inS (sl n P) x = inC P x

out-inC : ∀ {b a} (P : a ⊲ b) (x : O a) → outC P (inC P x) ≡ x
out-inC self x = refl
out-inC (suc P) x = out-inC P x
out-inC (lim n P) x = out-inC P x

out-inS : ∀ {b a} (R : Strict a b) (x : O a) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x
```

## §3 $\Omega$, 加法, $y\cdot n$

```agda
Ω̇ : ∀ L → O L
Ω̇ azero = os o0
Ω̇ (asuc a) = oi zero (λ z → oe (ss self) z)
Ω̇ (alim f) = ol (λ n → oe (sl n self) (Ω̇ (f n)))

-- 右边是低层的元素, P 是它的层到 L 的第一位置
add  : ∀ {L a} → O L → a ⊲ L → O a → O L
addC : ∀ {L b a} → O L → b ⊲ L → (P : a ⊲ b) → Vc b P → O L
addS : ∀ {L b a} → O L → b ⊲ L → (R : Strict a b) → Vs b R → O L

add W P o0 = W
add W P (os x) = os (add W P x)
add W P (ol F) = ol (λ n → add W P (F n))
add W P (oi r h) = oi (≪∘ r P) (λ z → add W P (h (inS (≪S r) (outS (≪S (≪∘ r P)) z))))
add W P (oe R x) = addS W P R x

addS W Q (ss P) x = addC W (⊲-tr (suc self) Q) P x
addS W Q (sl n P) x = addC W (⊲-tr (lim n self) Q) P x

addC W Q self x = add W Q x
addC W Q (suc P) x = addC W (⊲-tr (suc self) Q) P x
addC W Q (lim n P) x = addC W (⊲-tr (lim n self) Q) P x

infixl 6 _⊕_
_⊕_ : ∀ {L} → O L → O L → O L
W ⊕ y = add W self y

rep : ∀ {L} → O L → ℕ → O L
rep y zero = o0
rep y (suc zero) = y
rep y (suc (suc m)) = rep y (suc m) ⊕ y

chainᵒ : ∀ {k} → (O k → O k) → ℕ → O k
chainᵒ {k} f zero = Ω̇ k
chainᵒ f (suc n) = f (chainᵒ f n)
```

## §4 折叠

`Tg t L`: 目标与当前层字面可比. 层高于目标时, 节点可能上升; 层不高于目标时, 节点都保留. 懒嵌入 `oe` 把层换成低的那一层, 关系由 `cmpF` 给.

```agda
Tg : A → A → Set
Tg t L = (t ⊲ L) ⊎ (L ⊲ t)

rkT : ∀ {k t L} → k ≪ L → Tg t L → Lg L → Rk k t
rkT r (inj₁ q) w = cmpN r q w
rkT r (inj₂ q) w = keep (≪∘ r q)

tgS : ∀ {t a L} → Strict a L → Tg t L → Lg L → Tg t a
tgS R (inj₁ q) w = cmpF (S→⊲ R) q w
tgS R (inj₂ q) w = inj₂ (⊲-tr (S→⊲ R) q)

ψ  : ∀ {L} t → Tg t L → Lg L → O L → O t
ψS : ∀ {L a} t → (R : Strict a L) → Tg t a → Lg a → Vs L R → O t
ψC : ∀ {b a} t → (P : a ⊲ b) → Tg t a → Lg a → Vc b P → O t

ψ t T w o0 = Ω̇ t
ψ t T w (os a) = ol (rep (ψ t T w a))
ψ t T w (ol F) = ol (λ n → ψ t T w (F n))
ψ {L} t T w (oi {k} r h) with rkT r T w
... | keep s = oi s (λ y → ψ t T w (h (inS (≪S r) (outS (≪S s) y))))
... | rise _ = ol (λ n → ψ t T w (h (inS (≪S r) (chainᵒ (λ z → ψ k (inj₁ (≪⊲ r)) w (h (inS (≪S r) z))) n))))
ψ t T w (oe R x) = ψS t R (tgS R T w) (lgS R w) x

ψS t (ss P) T w x = ψC t P T w x
ψS t (sl n P) T w x = ψC t P T w x

ψC t self T w x = ψ t T w x
ψC t (suc P) T w x = ψC t P T w x
ψC t (lim n P) T w x = ψC t P T w x

-- O 0 只有 o0, os, ol
ψ₀Ω : ∀ η → Lg η → O azero
ψ₀Ω η w = ψ azero (inj₁ (z⊲ η)) w (Ω̇ η)
```

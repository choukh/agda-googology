# 序数高度的世界: 下标, 世界, 高度

> 不含记号, 不含累加. 结论写在 [CumHt](CumHt.lagda.md). 层是三元组 $(r,p,a)$, 这一篇给前两位 (高度 `Ht`) 与它们的比较.
>
> - **高度的 $p$ 也活在世界里.** `CumUp` 的 $p$ 是 $\mathbb N$, 全局可比. 这里 $p:A$, 比较 `cmpH` 要一个字面的世界 $m$, $p,q\lhd m$, `Lg m`. 没有全局三歧. $r$ 还是 $\mathbb N$.
> - **路径 `<ᴴ`** 对 $p$ 位走 `A` 的结构 (`hs0`, `hl0`, `hsS`, `hlS`), 对 $r$ 位走 $\mathbb N$ (`hr0`, `hrS`), 这时 $p$ 位是自由的. 自由的那一位由 `fd` 读出, 节点要带它在世界之下的证据.
> - `Nx`: 第 0 层闭包的链怎么走. 只有这一个接口, 闭包定理对任何实例成立, 累加是 [CumHtCum](CumHtCum.lagda.md) 里的一个实例. 这个文件和后面的 `CumHtTree`, `Eq`, `W`, `Psi`, `Le`, `Main` 的导入闭包都不含 `CumReadBase`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHtBase where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Level using (Ordᶜ; _≅_)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Lg; ⊲-tr; lg⊲; z⊲; ≪⊲; cmpF)
import OCF.Align.CumReadCF as C

Ord₀ : Set
Ord₀ = Ordᶜ FL.zero
```

## §1 下标的结构等价

与 `CumUpEq` 相同.

```agda
infix 4 _≈ᴬ_ _⊏_
data _≈ᴬ_ : A → A → Set where
  z≈ : azero ≈ᴬ azero
  s≈ : ∀ {a b} → a ≈ᴬ b → asuc a ≈ᴬ asuc b
  l≈ : ∀ {f g} → (∀ n → f n ≈ᴬ g n) → alim f ≈ᴬ alim g

≈ᴬ-refl : ∀ a → a ≈ᴬ a
≈ᴬ-refl azero = z≈
≈ᴬ-refl (asuc a) = s≈ (≈ᴬ-refl a)
≈ᴬ-refl (alim f) = l≈ (λ n → ≈ᴬ-refl (f n))

≈ᴬ-sym : ∀ {a b} → a ≈ᴬ b → b ≈ᴬ a
≈ᴬ-sym z≈ = z≈
≈ᴬ-sym (s≈ e) = s≈ (≈ᴬ-sym e)
≈ᴬ-sym (l≈ h) = l≈ (λ n → ≈ᴬ-sym (h n))

≈ᴬ-trans : ∀ {a b c} → a ≈ᴬ b → b ≈ᴬ c → a ≈ᴬ c
≈ᴬ-trans z≈ z≈ = z≈
≈ᴬ-trans (s≈ e) (s≈ d) = s≈ (≈ᴬ-trans e d)
≈ᴬ-trans (l≈ h) (l≈ k) = l≈ (λ n → ≈ᴬ-trans (h n) (k n))

-- 真的第一位置
data _⊏_ : A → A → Set where
  sf : ∀ {a b} → a ⊲ b → a ⊏ asuc b
  lf : ∀ {a f} n → a ⊲ f n → a ⊏ alim f

⊏→⊲ : ∀ {a b} → a ⊏ b → a ⊲ b
⊏→⊲ (sf p) = C.suc p
⊏→⊲ (lf n p) = C.lim n p

≪→⊏ : ∀ {a b} → a ≪ b → a ⊏ b
≪→⊏ C.zero = sf C.self
≪→⊏ (C.suc r) = sf (⊏→⊲ (≪→⊏ r))
≪→⊏ (C.lim n r) = lf n (⊏→⊲ (≪→⊏ r))

⊏⊲ : ∀ {a b c} → a ⊏ b → b ⊲ c → a ⊏ c
⊏⊲ r C.self = r
⊏⊲ r (C.suc q) = sf (⊏→⊲ (⊏⊲ r q))
⊏⊲ r (C.lim n q) = lf n (⊏→⊲ (⊏⊲ r q))

⊲or : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (a ⊏ b)
⊲or C.self = inj₁ refl
⊲or (C.suc p) = inj₂ (sf p)
⊲or (C.lim n p) = inj₂ (lf n p)

⊲-mv : ∀ {a b b′} → a ⊲ b → b ≈ᴬ b′ → Σ A (λ a′ → (a′ ⊲ b′) × (a ≈ᴬ a′))
⊲-mv {b′ = b′} C.self e = b′ , C.self , e
⊲-mv (C.suc p) (s≈ e) with ⊲-mv p e
... | a′ , q , d = a′ , C.suc q , d
⊲-mv (C.lim n p) (l≈ h) with ⊲-mv p (h n)
... | a′ , q , d = a′ , C.lim n q , d

⊏-mv : ∀ {a b b′} → a ⊏ b → b ≈ᴬ b′ → Σ A (λ a′ → (a′ ⊏ b′) × (a ≈ᴬ a′))
⊏-mv (sf p) (s≈ e) with ⊲-mv p e
... | a′ , q , d = a′ , sf q , d
⊏-mv (lf n p) (l≈ h) with ⊲-mv p (h n)
... | a′ , q , d = a′ , lf n q , d

data Acc⊏ (a : A) : Set where
  acc : (∀ {b} → b ⊏ a → Acc⊏ b) → Acc⊏ a

acc⊲ : ∀ a {b} → b ⊲ a → Acc⊏ b
acc⊏ : ∀ a {b} → b ⊏ a → Acc⊏ b
acc⊲ a C.self = acc (acc⊏ a)
acc⊲ (asuc a) (C.suc p) = acc⊲ a p
acc⊲ (alim f) (C.lim n p) = acc⊲ (f n) p
acc⊏ (asuc a) (sf p) = acc⊲ a p
acc⊏ (alim f) (lf n p) = acc⊲ (f n) p

irr′ : ∀ {a b} → Acc⊏ a → b ⊏ a → b ≈ᴬ a → ⊥
irr′ (acc h) r e with ⊏-mv r (≈ᴬ-sym e)
... | b₂ , r₂ , d = irr′ (h r) r₂ (≈ᴬ-sym d)

irr : ∀ {a b} → b ⊏ a → b ≈ᴬ a → ⊥
irr {a} = irr′ (acc (acc⊏ a))

-- k ⊏ t, t ≈ t′, t′ ⊲ k′, k′ ≈ k 相撞
clash⊏ : ∀ {k t k′ t′} → k ⊏ t → t′ ⊲ k′ → k ≈ᴬ k′ → t ≈ᴬ t′ → ⊥
clash⊏ s q ek et with ⊲-mv q (≈ᴬ-sym ek)
... | t″ , q″ , d with ⊏-mv s (≈ᴬ-trans et d)
...   | k₂ , r₂ , d₂ = irr (⊏⊲ r₂ q″) (≈ᴬ-sym d₂)

clash : ∀ {k t k′ t′} → k ≪ t → t′ ⊲ k′ → k ≈ᴬ k′ → t ≈ᴬ t′ → ⊥
clash s = clash⊏ (≪→⊏ s)

-- 反对称, 模 ≈ᴬ
anti : ∀ {a b a′ b′} → a ⊲ b → b′ ⊲ a′ → a ≈ᴬ a′ → b ≈ᴬ b′ → a ≈ᴬ b
anti {a} p q ea eb with ⊲or p
... | inj₁ refl = ≈ᴬ-refl a
... | inj₂ r = ⊥-elim (clash⊏ r q ea eb)
```

## §2 世界

`Gw v`: 世界合法且不低于 $1$. 与 `CumReadW` 的同形, 重写一份是为了导入闭包里没有累加.

```agda
one : A
one = asuc azero

record Gw (v : A) : Set where
  constructor gw
  field
    lgw : Lg v
    pos : one ⊲ v
open Gw public

g₀ : Gw one
g₀ = gw tt C.self
```

## §3 两位的证据

`D⊲ x y v`: 两个下标都在世界 $v$ 之下. `Rd x k v`: 同样, 第二个严格, 走节点路径.

```agda
record D⊲ (x y v : A) : Set where
  constructor _,ᵈ_
  field
    d₁ : x ⊲ v
    d₂ : y ⊲ v
open D⊲ public

record Rd (x k v : A) : Set where
  constructor rd
  field
    r₁ : x ⊲ v
    r₂ : k ≪ v
open Rd public

D-tr : ∀ {x y u v} → D⊲ x y u → u ⊲ v → D⊲ x y v
D-tr e q = ⊲-tr (d₁ e) q ,ᵈ ⊲-tr (d₂ e) q

Rd-tr : ∀ {x k u v} → Rd x k u → u ⊲ v → Rd x k v
Rd-tr e q = rd (⊲-tr (r₁ e) q) (C.≪∘ (r₂ e) q)

Dr : ∀ {x y′ y v} → y′ ⊲ y → D⊲ x y v → D⊲ x y′ v
Dr q e = d₁ e ,ᵈ ⊲-tr q (d₂ e)

Dz : ∀ v → D⊲ azero azero v
Dz v = z⊲ v ,ᵈ z⊲ v

Dzr : ∀ {y v} → y ⊲ v → D⊲ azero y v
Dzr {v = v} e = z⊲ v ,ᵈ e

record D≈ (x y x′ y′ : A) : Set where
  constructor _,≈_
  field
    e₁ : x ≈ᴬ x′
    e₂ : y ≈ᴬ y′
open D≈ public

D≈-z : D≈ azero azero azero azero
D≈-z = z≈ ,≈ z≈

D≈-sym : ∀ {x y x′ y′} → D≈ x y x′ y′ → D≈ x′ y′ x y
D≈-sym e = ≈ᴬ-sym (e₁ e) ,≈ ≈ᴬ-sym (e₂ e)
```

## §4 高度

```agda
record Ht : Set where
  constructor ⟨_,_⟩
  field
    rr : ℕ
    pp : A
open Ht public

infix 4 _<ᴴ_
data _<ᴴ_ : Ht → Ht → Set where
  hs0 : ∀ {r b} → ⟨ r , b ⟩ <ᴴ ⟨ r , asuc b ⟩
  hl0 : ∀ {r f} n → ⟨ r , f n ⟩ <ᴴ ⟨ r , alim f ⟩
  hr0 : ∀ {s p′ p} → ⟨ s , p′ ⟩ <ᴴ ⟨ suc s , p ⟩
  hsS : ∀ {H r b} → H <ᴴ ⟨ r , b ⟩ → H <ᴴ ⟨ r , asuc b ⟩
  hlS : ∀ {H r f} n → H <ᴴ ⟨ r , f n ⟩ → H <ᴴ ⟨ r , alim f ⟩
  hrS : ∀ {H s p} → H <ᴴ ⟨ s , azero ⟩ → H <ᴴ ⟨ suc s , p ⟩

-- 路径里自由的那一位
fd : ∀ {H H′} → H <ᴴ H′ → A
fd hs0 = azero
fd (hl0 n) = azero
fd (hr0 {p′ = p′}) = p′
fd (hsS i) = fd i
fd (hlS n i) = fd i
fd (hrS i) = fd i

fd⊲ : ∀ {H H′ m} (i : H <ᴴ H′) → pp H ⊲ m → fd i ⊲ m
fd⊲ {m = m} hs0 e = z⊲ m
fd⊲ {m = m} (hl0 n) e = z⊲ m
fd⊲ hr0 e = e
fd⊲ (hsS i) e = fd⊲ i e
fd⊲ (hlS n i) e = fd⊲ i e
fd⊲ (hrS i) e = fd⊲ i e

pp⊲ : ∀ {H H′ m} (i : H <ᴴ H′) → pp H′ ⊲ m → fd i ⊲ m → pp H ⊲ m
pp⊲ hs0 e f = ⊲-tr (C.suc C.self) e
pp⊲ (hl0 n) e f = ⊲-tr (C.lim n C.self) e
pp⊲ hr0 e f = f
pp⊲ (hsS i) e f = pp⊲ i (⊲-tr (C.suc C.self) e) f
pp⊲ (hlS n i) e f = pp⊲ i (⊲-tr (C.lim n C.self) e) f
pp⊲ {m = m} (hrS i) e f = pp⊲ i (z⊲ m) f

-- r 位上升时, p 位换成自由的
rt : ∀ {H s p′ p} → H <ᴴ ⟨ s , p′ ⟩ → H <ᴴ ⟨ suc s , p ⟩
rt hs0 = hr0
rt (hl0 n) = hr0
rt hr0 = hrS hr0
rt (hsS j) = rt j
rt (hlS n j) = rt j
rt (hrS j) = hrS (hrS j)

<tr : ∀ {H₀ H₁ H₂} → H₀ <ᴴ H₁ → H₁ <ᴴ H₂ → H₀ <ᴴ H₂
<tr j hs0 = hsS j
<tr j (hl0 n) = hlS n j
<tr j hr0 = rt j
<tr j (hsS i) = hsS (<tr j i)
<tr j (hlS n i) = hlS n (<tr j i)
<tr j (hrS i) = hrS (<tr j i)

fd-rt : ∀ {H s p′ p m} (j : H <ᴴ ⟨ s , p′ ⟩) → fd j ⊲ m → p′ ⊲ m → fd (rt {p = p} j) ⊲ m
fd-rt hs0 f e = ⊲-tr (C.suc C.self) e
fd-rt (hl0 n) f e = ⊲-tr (C.lim n C.self) e
fd-rt hr0 f e = f
fd-rt (hsS j) f e = fd-rt j f (⊲-tr (C.suc C.self) e)
fd-rt (hlS n j) f e = fd-rt j f (⊲-tr (C.lim n C.self) e)
fd-rt (hrS j) f e = f

fd-tr : ∀ {H₀ H₁ H₂ m} (j : H₀ <ᴴ H₁) (i : H₁ <ᴴ H₂) → fd j ⊲ m → fd i ⊲ m → fd (<tr j i) ⊲ m
fd-tr j hs0 f e = f
fd-tr j (hl0 n) f e = f
fd-tr j hr0 f e = fd-rt j f e
fd-tr j (hsS i) f e = fd-tr j i f e
fd-tr j (hlS n i) f e = fd-tr j i f e
fd-tr j (hrS i) f e = fd-tr j i f e
```

## §5 高度的比较

**只在世界之下.** 前一位比 $\mathbb N$, 后一位比同一个合法世界 $m$ 的两个第一位置 (`cmpF`). 相等是字面的: 两个第一位置落在同一处就是同一个子项.

```agda
<ᴺ-tr : ∀ {a b c} → a <ᴺ b → b <ᴺ c → a <ᴺ c
<ᴺ-tr p zero = suc p
<ᴺ-tr p (suc q) = suc (<ᴺ-tr p q)

<ᴺ-irr : ∀ {n} → n <ᴺ n → ⊥
<ᴺ-irr {suc n} (suc q) = <ᴺ-irr (<shrink q)
  where
  <shrink : ∀ {a b} → suc a <ᴺ b → a <ᴺ b
  <shrink zero = suc zero
  <shrink (suc q′) = suc (<shrink q′)

hrOf : ∀ {r s p q} → r <ᴺ s → ⟨ r , p ⟩ <ᴴ ⟨ s , q ⟩
hrOf zero = hr0
hrOf (suc i) = hrS (hrOf i)

data Child : A → A → Set where
  chs : ∀ {b} → Child b (asuc b)
  chl : ∀ {f} n → Child (f n) (alim f)

hb : ∀ {r y z} → Child y z → ⟨ r , y ⟩ <ᴴ ⟨ r , z ⟩
hb chs = hs0
hb (chl n) = hl0 n

hu : ∀ {H r y z} → Child y z → H <ᴴ ⟨ r , y ⟩ → H <ᴴ ⟨ r , z ⟩
hu chs j = hsS j
hu (chl n) j = hlS n j

pA : ∀ {r a y z} → a ⊲ y → Child y z → ⟨ r , a ⟩ <ᴴ ⟨ r , z ⟩
pA C.self c = hb c
pA (C.suc P) c = hu c (pA P chs)
pA (C.lim n P) c = hu c (pA P (chl n))

pth : ∀ {r a b} → a ⊏ b → ⟨ r , a ⟩ <ᴴ ⟨ r , b ⟩
pth (sf P) = pA P chs
pth (lf n P) = pA P (chl n)

cmpH : ∀ H q {m} → pp H ⊲ m → pp q ⊲ m → Lg m → (H <ᴴ q) ⊎ (q <ᴴ H) ⊎ (H ≡ q)
cmpH ⟨ r , p ⟩ ⟨ s , q ⟩ e₁ e₂ w with <ᴺ-dec r s
... | injᵃ i = injᵃ (hrOf i)
... | injᵇ i = injᵇ (hrOf i)
... | injᶜ refl with cmpF e₁ e₂ w
...   | inj₁ q⊲p with ⊲or q⊲p
...     | inj₁ refl = injᶜ refl
...     | inj₂ d = injᵇ (pth d)
cmpH ⟨ r , p ⟩ ⟨ s , q ⟩ e₁ e₂ w | injᶜ refl | inj₂ p⊲q with ⊲or p⊲q
...     | inj₁ refl = injᶜ refl
...     | inj₂ d = injᵃ (pth d)
```

## §6 高度的等价, 路径与等价相撞

```agda
infix 4 _≈ᴴ_
_≈ᴴ_ : Ht → Ht → Set
H ≈ᴴ H′ = (rr H ≡ rr H′) × (pp H ≈ᴬ pp H′)

≈ᴴ-refl : ∀ H → H ≈ᴴ H
≈ᴴ-refl H = refl , ≈ᴬ-refl (pp H)

≈ᴴ-sym : ∀ {H H′} → H ≈ᴴ H′ → H′ ≈ᴴ H
≈ᴴ-sym (e , d) = sym e , ≈ᴬ-sym d

≈ᴴ-trans : ∀ {H H′ H″} → H ≈ᴴ H′ → H′ ≈ᴴ H″ → H ≈ᴴ H″
≈ᴴ-trans (e , d) (e′ , d′) = trans e e′ , ≈ᴬ-trans d d′

Hd : ∀ {H H′ t t′} → H ≈ᴴ H′ → t ≈ᴬ t′ → D≈ (pp H) t (pp H′) t′
Hd e d = proj₂ e ,≈ d

<v : ∀ {H H′} → H <ᴴ H′ → (rr H <ᴺ rr H′) ⊎ ((rr H ≡ rr H′) × (pp H ⊏ pp H′))
<v hs0 = inj₂ (refl , sf C.self)
<v (hl0 n) = inj₂ (refl , lf n C.self)
<v hr0 = inj₁ zero
<v (hsS i) with <v i
... | inj₁ x = inj₁ x
... | inj₂ (e , d) = inj₂ (e , sf (⊏→⊲ d))
<v (hlS n i) with <v i
... | inj₁ x = inj₁ x
... | inj₂ (e , d) = inj₂ (e , lf n (⊏→⊲ d))
<v (hrS i) with <v i
... | inj₁ x = inj₁ (<ᴺ-tr x zero)
... | inj₂ (e , ())

≤ᴺ-cross : ∀ {a b c d} → a <ᴺ b → c <ᴺ d → a ≡ d → b ≡ c → ⊥
≤ᴺ-cross x y refl refl = <ᴺ-irr (<ᴺ-tr x y)

no-<≈ : ∀ {H q} → H <ᴴ q → H ≈ᴴ q → ⊥
no-<≈ {⟨ r , p ⟩} {⟨ s , q ⟩} i (refl , d) with <v i
... | inj₁ x = <ᴺ-irr x
... | inj₂ (_ , f) = irr f d

clashᴴ : ∀ {H q q′ H′} → H <ᴴ q → q′ <ᴴ H′ → H ≈ᴴ H′ → q ≈ᴴ q′ → ⊥
clashᴴ {⟨ r , p ⟩} {⟨ s , q ⟩} {⟨ s′ , q′ ⟩} {⟨ r′ , p′ ⟩} i i′ (refl , ea) (refl , eb) with <v i | <v i′
... | inj₁ x | inj₁ y = <ᴺ-irr (<ᴺ-tr x y)
... | inj₁ x | inj₂ (refl , _) = <ᴺ-irr x
... | inj₂ (refl , _) | inj₁ y = <ᴺ-irr y
... | inj₂ (refl , f) | inj₂ (_ , g) = clash⊏ f (⊏→⊲ g) ea eb
```

## §7 第 0 层闭包的接口

`Nx`: 第 0 层的闭包走链时, 下一个下标怎么由上一个下标和上一个输出得到. 只要求: 字面在上, 保合法, 保等价. **这是闭包定理对第 0 层闭包的全部要求.** 实例在 [CumHtCum](CumHtCum.lagda.md) (累加), [CumHt](CumHt.lagda.md) (不读输出的对照).

```agda
record Nx : Set where
  field
    nxt   : A → Ord₀ → A
    nxt-⊲ : ∀ η y → η ⊲ nxt η y
    nxt-L : ∀ η y → Lg η → Lg (nxt η y)
    nxt-≈ : ∀ {η η′} {y y′ : Ord₀} → η ≈ᴬ η′ → y ≅ y′ → nxt η y ≈ᴬ nxt η′ y′
```

# 带高度的世界: 折叠

> 不含记号. 结论写在 [CumUp](CumUp.lagda.md). 取代 [CumReadW](CumReadW.lagda.md) 的路径写法: 层是一对 $(p,a)$, 读作 $\Omega_{\Omega\cdot p+a}$. 比较只有两件: 高度比 $\mathbb N$, 同高度比 `A`, 在一个字面的世界之下.
>
> - **目标的世界就是目标本身.** 上一轮的障碍: 目标路径上的下标 $\tau$ 随路径变, 同一个闭包在两处算出的链字面不可比 (`no-⊞-left`). 这里没有目标路径, 目标 $(q,t)$ 的 $t$ 自己就是世界的下界, 输出闭包的世界是 $\max(u,t,a)$, 只看项与目标.
> - **低高度的节点 `od`, 嵌入 `oL`** 不要路径, 只要下标在世界之下: 第 $h<p$ 高度的 `A` 下标都合法. 这就是 `Lo` 的那个家族在类型里的位置.
> - 其余与 [CumReadCF](CumReadCF.lagda.md) 相同. 第 0 层的闭包直接计值, 链点累加 (`next`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpW where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲; Rk; keep; rise; cmpN; cmpF; steps)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next; next-⊲; Lg-next)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀; gnext)
```

## §1 高度上的序

```agda
<tr : ∀ {a b c} → a <ᴺ b → b <ᴺ c → a <ᴺ c
<tr p zero = suc p
<tr p (suc q) = suc (<tr p q)

-- 第 k 个: 世界之下的下标是否严格低于世界
≪⊲′ : ∀ {k a b} → k ≪ a → a ⊲ b → k ≪ b
≪⊲′ = ≪∘
```

## §2 数据树

`𝓞 p a u`: 高度 $p$, 层 $a$, 世界 $u$. `V`: 同高度低层的元素, 走路径 (`≪`). `L`: 低高度的元素, 对一切 `A` 下标.

```agda
data Stp : ∀ {a L} → Strict a L → Set where
  es : ∀ {b} → Stp {b} {asuc b} (ss C.self)
  el : ∀ {f} n → Stp {f n} {alim f} (sl n C.self)

module _ (p : ℕ) (a : A) (V : ∀ {b} → Strict b a → A → Set) (Lw : ∀ {h} → h <ᴺ p → A → A → Set) where
  data O₊ : A → Set where
    o0 : ∀ {u} → O₊ u
    os : ∀ {u} → O₊ u → O₊ u
    ol : ∀ {u} → (ℕ → O₊ u) → O₊ u
    oi : ∀ {u k} (r : k ≪ a) → (∀ {v} → u ⊲ v → Gw v → V (≪S r) v → O₊ v) → O₊ u
    od : ∀ {u h} (i : h <ᴺ p) (k : A) → k ≪ u → (∀ {v} → u ⊲ v → Gw v → Lw i k v → O₊ v) → O₊ u
    oc : ∀ {u} → O₊ u → (∀ {v} → u ⊲ v → Gw v → O₊ v) → O₊ u
    oe : ∀ {u b} {R : Strict b a} → Stp R → V R u → O₊ u
    oL : ∀ {u h} (i : h <ᴺ p) (k : A) → k ⊲ u → Lw i k u → O₊ u
    ow : ∀ {u v} → u ⊲ v → Gw u → O₊ u → O₊ v

𝓞  : ℕ → A → A → Set
Vs : ∀ p a {b} → Strict b a → A → Set
Vc : ∀ p a {b} → b ⊲ a → A → Set
Low : ∀ p {h} → h <ᴺ p → A → A → Set
𝓞 p a = O₊ p a (Vs p a) (Low p)
Vs p (asuc b) (ss P) u = Vc p b P u
Vs p (alim f) (sl n P) u = Vc p (f n) P u
Vc p a C.self u = 𝓞 p a u
Vc p (asuc b) (C.suc P) u = Vc p b P u
Vc p (alim f) (C.lim n P) u = Vc p (f n) P u
Low (suc q) zero k u = 𝓞 q k u
Low (suc q) (suc i) k u = Low q i k u

outC : ∀ {p a b u} (P : b ⊲ a) → Vc p a P u → 𝓞 p b u
outC C.self x = x
outC (C.suc P) x = outC P x
outC (C.lim n P) x = outC P x

inC : ∀ {p a b u} (P : b ⊲ a) → 𝓞 p b u → Vc p a P u
inC C.self x = x
inC (C.suc P) x = inC P x
inC (C.lim n P) x = inC P x

outS : ∀ {p a b u} (R : Strict b a) → Vs p a R u → 𝓞 p b u
outS (ss P) x = outC P x
outS (sl n P) x = outC P x

inS : ∀ {p a b u} (R : Strict b a) → 𝓞 p b u → Vs p a R u
inS (ss P) x = inC P x
inS (sl n P) x = inC P x

outL : ∀ {p h k u} (i : h <ᴺ p) → Low p i k u → 𝓞 h k u
outL zero x = x
outL (suc i) x = outL i x

inL : ∀ {p h k u} (i : h <ᴺ p) → 𝓞 h k u → Low p i k u
inL zero x = x
inL (suc i) x = inL i x

out-inC : ∀ {p a b u} (P : b ⊲ a) (x : 𝓞 p b u) → outC P (inC P x) ≡ x
out-inC C.self x = refl
out-inC (C.suc P) x = out-inC P x
out-inC (C.lim n P) x = out-inC P x

out-inS : ∀ {p a b u} (R : Strict b a) (x : 𝓞 p b u) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x

out-inL : ∀ {p h k u} (i : h <ᴺ p) (x : 𝓞 h k u) → outL i (inL i x) ≡ x
out-inL zero x = refl
out-inL (suc i) x = out-inL i x
```

## §3 $\Omega$, 加法

`Ω̇ p a`: 闭的元素, 世界是 $1$. $(p+1,0)$ 是闭包: 第一支 $(p,1)$, 分支 $(p,v)$. 世界 $v$ 就是下标.

```agda
Ω̇ : ∀ p a → 𝓞 p a one
Ω̇ p (asuc c) = oi C.zero (λ q g z → oe es z)
Ω̇ p (alim f) = ol (λ n → oe (el n) (Ω̇ p (f n)))
Ω̇ zero azero = os o0
Ω̇ (suc p) azero = oc (oL zero one C.self (Ω̇ p one)) (λ {v} q g → oL zero v C.self (ow (pos g) g₀ (Ω̇ p v)))

Ω̇at : ∀ p a {v} → Gw v → 𝓞 p a v
Ω̇at p a g = ow (pos g) g₀ (Ω̇ p a)

record Mx (u t a v : A) : Set where
  constructor mx′
  field
    m   : A
    gm  : Gw m
    um  : u ⊲ m
    tm  : t ⊲ m
    am  : a ⊲ m
    mv  : m ⊲ v

mx : ∀ {u t a v} → Gw u → Gw v → u ⊲ v → t ⊲ v → a ⊲ v → Mx u t a v
mx {u} {t} {a} gu gv uv tv av with cmpF uv tv (lgw gv)
... | inj₁ t⊲u with cmpF uv av (lgw gv)
...   | inj₁ a⊲u = mx′ u gu C.self t⊲u a⊲u uv
...   | inj₂ u⊲a = mx′ a (gw (lg⊲ av (lgw gv)) (⊲-tr (pos gu) u⊲a)) u⊲a (⊲-tr t⊲u u⊲a) C.self av
mx {u} {t} {a} gu gv uv tv av | inj₂ u⊲t with cmpF tv av (lgw gv)
...   | inj₁ a⊲t = mx′ t (gw (lg⊲ tv (lgw gv)) (⊲-tr (pos gu) u⊲t)) u⊲t C.self a⊲t tv
...   | inj₂ t⊲a = mx′ a (gw (lg⊲ av (lgw gv)) (⊲-tr (pos gu) (⊲-tr u⊲t t⊲a))) (⊲-tr u⊲t t⊲a) t⊲a C.self av

-- 右边元素的层 (p′, b) 怎么放进左边的层 (p, a): 同高度走第一位置, 低高度只要下标在世界之下
data Rel : ℕ → A → ℕ → A → Set where
  sa : ∀ {p a b} → b ⊲ a → Rel p b p a
  lw : ∀ {h p b a} → h <ᴺ p → Rel h b p a

bw : ∀ {p′ b p a} → Rel p′ b p a → A
bw (sa P) = azero
bw {b = b} (lw i) = b

bw↑ : ∀ {p′ b p a v} (R : Rel p′ b p a) → (b ⊲ v) → bw R ⊲ v
bw↑ {v = v} (sa P) e = z⊲ v
bw↑ (lw i) e = e

-- W + x: 左边不动, 世界是 max(u₀, u′, 层). 与运行世界无关
add  : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′ → Gw u′ → ∀ v → Gw v → u₀ ⊲ v → u′ ⊲ v → bw R ⊲ v → 𝓞 p a v
add⁰ : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → bw R ⊲ m → 𝓞 p a m
addL : ∀ {p a p′ h k u₀ u′} → 𝓞 p a u₀ → Gw u₀ → h <ᴺ p → (j : h <ᴺ p′) → Low p′ j k u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → k ⊲ m → 𝓞 p a m

add W gu₀ R x gx v gv u₀v xv bv with mx gu₀ gv u₀v xv bv
... | mx′ m gm um tm am mv = ow mv gm (add⁰ W gu₀ R x gx m gm um tm am)

add⁰ W gu₀ R o0 gx m gm um tm am = ow um gu₀ W
add⁰ W gu₀ R (os x) gx m gm um tm am = os (add W gu₀ R x gx m gm um tm am)
add⁰ W gu₀ R (ol F) gx m gm um tm am = ol (λ n → add W gu₀ R (F n) gx m gm um tm am)
add⁰ W gu₀ (sa P) (oi r h) gx m gm um tm am =
  oi (≪∘ r P) (λ {v} q g y → add W gu₀ (sa P) (h (⊲-tr tm q) g (inS (≪S r) (outS (≪S (≪∘ r P)) y))) g v g (⊲-tr um q) C.self (z⊲ v))
add⁰ W gu₀ (lw i) (oi {k = k} r h) gx m gm um tm am =
  od i k (≪∘ r am) (λ {v} q g y → add W gu₀ (lw i) (h (⊲-tr tm q) g (inS (≪S r) (outL i y))) g v g (⊲-tr um q) C.self (⊲-tr am q))
add⁰ W gu₀ (sa P) (od j k r h) gx m gm um tm am =
  od j k (≪∘ r tm) (λ {v} q g y → add W gu₀ (sa P) (h (⊲-tr tm q) g (inL j (outL j y))) g v g (⊲-tr um q) C.self (z⊲ v))
add⁰ W gu₀ (lw i) (od j k r h) gx m gm um tm am =
  od (<tr j i) k (≪∘ r tm) (λ {v} q g y → add W gu₀ (lw i) (h (⊲-tr tm q) g (inL j (outL (<tr j i) y))) g v g (⊲-tr um q) C.self (⊲-tr am q))
add⁰ W gu₀ R (oc x h) gx m gm um tm am =
  oc (add W gu₀ R x gx m gm um tm am) (λ {v} q g → add W gu₀ R (h (⊲-tr tm q) g) g v g (⊲-tr um q) C.self (⊲-tr am q))
add⁰ W gu₀ (sa P) (oe es x) gx m gm um tm am = add W gu₀ (sa (⊲-tr (C.suc C.self) P)) x gx m gm um tm am
add⁰ W gu₀ (lw i) (oe es x) gx m gm um tm am = add W gu₀ (lw i) x gx m gm um tm (⊲-tr (C.suc C.self) am)
add⁰ W gu₀ (sa P) (oe (el n) x) gx m gm um tm am = add W gu₀ (sa (⊲-tr (C.lim n C.self) P)) x gx m gm um tm am
add⁰ W gu₀ (lw i) (oe (el n) x) gx m gm um tm am = add W gu₀ (lw i) x gx m gm um tm (⊲-tr (C.lim n C.self) am)
add⁰ W gu₀ (sa P) (oL j k e x) gx m gm um tm am = addL W gu₀ j j x gx m gm um tm (⊲-tr e tm)
add⁰ W gu₀ (lw i) (oL j k e x) gx m gm um tm am = addL W gu₀ (<tr j i) j x gx m gm um tm (⊲-tr e tm)
add⁰ W gu₀ R (ow p′ g′ x) gx m gm um tm am = add W gu₀ R x g′ m gm um (⊲-tr p′ tm) am

addL W gu₀ t zero x gx m gm um tm km = add W gu₀ (lw t) x gx m gm um tm km
addL W gu₀ t (suc j) x gx m gm um tm km = addL W gu₀ t j x gx m gm um tm km

rep : ∀ {p a u} → 𝓞 p a u → Gw u → ℕ → 𝓞 p a u
rep y g zero = o0
rep y g (suc zero) = y
rep {u = u} y g (suc (suc m)) = add (rep y g (suc m)) g (sa C.self) y g u g C.self C.self (z⊲ u)

chainᵒ : ∀ {p k u} → Gw u → (𝓞 p k u → 𝓞 p k u) → ℕ → 𝓞 p k u
chainᵒ {p} {k} g f zero = Ω̇at p k g
chainᵒ g f (suc n) = f (chainᵒ g f n)
```

## §4 第 0 层

```agda
ord : ∀ {u} → 𝓞 zero azero u → Ord₀
ord o0 = FL.zero
ord (os x) = FL.suc (ord x)
ord (ol F) = FL.lim (λ n → ord (F n))
ord (oi () _)
ord (od () _ _ _)
ord (oc x h) = ord x
ord (oe () _)
ord (oL () _ _ _)
ord (ow p g x) = ord x

em : ∀ {u} → Ord₀ → 𝓞 zero azero u
em FL.zero = o0
em (FL.suc a) = os (em a)
em (FL.lim f) = ol (λ n → em (f n))
em (FL.limᵢ () f)
em (FL.up () x)
```

## §5 折叠

`mx`: $\max(u,t,a)$, 字面比较, 运行世界 $v$ 只作证据. 输出的世界是它, 不是 $v$.

```agda
record Ix (b : A) : Set where
  constructor ix
  field
    η  : A
    gη : Gw η
    up : b ⊲ η

step : ∀ {b} → Ix b → Ord₀ → Ix b
step (ix η g u) y = ix (next η y) (gnext y g) (⊲-tr u (next-⊲ η y))

ixs : ∀ {m} → Gw m → Ord₀ → (Ix m → Ord₀) → ℕ → Ix m
ixs {m} gm y₀ val zero = step (ix m gm C.self) y₀
ixs gm y₀ val (suc n) = step (ixs gm y₀ val n) (val (ixs gm y₀ val n))

yss : ∀ {m} → Gw m → Ord₀ → (Ix m → Ord₀) → ℕ → Ord₀
yss gm y₀ val zero = y₀
yss gm y₀ val (suc n) = val (ixs gm y₀ val n)

-- 第 0 层: 直接算到序数
infixl 6 _+₀_
_+₀_ : Ord₀ → Ord₀ → Ord₀
a +₀ FL.zero = a
a +₀ FL.suc b = FL.suc (a +₀ b)
a +₀ FL.lim f = FL.lim (λ n → a +₀ f n)
a +₀ FL.limᵢ () f
a +₀ FL.up () x

rep₀ : Ord₀ → ℕ → Ord₀
rep₀ y zero = FL.zero
rep₀ y (suc zero) = y
rep₀ y (suc (suc m)) = rep₀ y (suc m) +₀ y

ψ  : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → t ⊲ v → a ⊲ v → 𝓞 q t v
ψᵐ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → t ⊲ v → a ⊲ v → 𝓞 q t v
ψ⁰ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → t ⊲ m → a ⊲ m → 𝓞 q t m
ψL : ∀ {p h k u} q t (j : h <ᴺ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → t ⊲ m → k ⊲ m → 𝓞 q t m
ψ₀  : ∀ {p a u} → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → a ⊲ v → Ord₀
ψ₀⁰ : ∀ {p a u} → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → a ⊲ m → Ord₀
ψ₀L : ∀ {p h k u} (j : h <ᴺ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → k ⊲ m → Ord₀

ψ zero azero x gu v gv uv tv av = ow (pos gv) g₀ (em (ψ₀ x gu v gv uv av))
ψ zero (asuc t) x gu v gv uv tv av = ψᵐ zero (asuc t) x gu v gv uv tv av
ψ zero (alim f) x gu v gv uv tv av = ψᵐ zero (alim f) x gu v gv uv tv av
ψ (suc q) t x gu v gv uv tv av = ψᵐ (suc q) t x gu v gv uv tv av

ψᵐ q t x gu v gv uv tv av with mx gu gv uv tv av
... | mx′ m gm um tm am mv = ow mv gm (ψ⁰ q t x gu m gm um tm am)

ψ⁰ q t o0 gu m gm um tm am = Ω̇at q t gm
ψ⁰ q t (os x) gu m gm um tm am = ol (rep (ψ q t x gu m gm um tm am) gm)
ψ⁰ q t (ol F) gu m gm um tm am = ol (λ n → ψ q t (F n) gu m gm um tm am)
ψ⁰ {p} {a} q t (oi {k = k} r h) gu m gm um tm am with <ᴺ-dec p q
... | injᵃ i = od i k (≪∘ r am) (λ w g y → ψ q t (h (⊲-tr um w) g (inS (≪S r) (outL i y))) g _ g C.self (⊲-tr tm w) (⊲-tr am w))
... | injᵇ _ = ol (λ n → ψ q t (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n))) gm m gm C.self tm am)
... | injᶜ refl with cmpN (≪∘ r am) tm (lgw gm)
...   | keep s = oi s (λ w g y → ψ q t (h (⊲-tr um w) g (inS (≪S r) (outS (≪S s) y))) g _ g C.self (⊲-tr tm w) (⊲-tr am w))
...   | rise _ = ol (λ n → ψ q t (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n))) gm m gm C.self tm am)
ψ⁰ {p} {a} q t (od {h = h₀} j k r h) gu m gm um tm am with <ᴺ-dec h₀ q
... | injᵃ i = od i k (≪∘ r um) (λ w g y → ψ q t (h (⊲-tr um w) g (inL j (outL i y))) g _ g C.self (⊲-tr tm w) (⊲-tr am w))
... | injᵇ _ = ol (λ n → ψ q t (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n))) gm m gm C.self tm am)
... | injᶜ refl with cmpN (≪∘ r um) tm (lgw gm)
...   | keep s = oi s (λ w g y → ψ q t (h (⊲-tr um w) g (inL j (outS (≪S s) y))) g _ g C.self (⊲-tr tm w) (⊲-tr am w))
...   | rise _ = ol (λ n → ψ q t (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n))) gm m gm C.self tm am)
ψ⁰ q t (oc x h) gu m gm um tm am =
  oc (ψ q t x gu m gm um tm am) (λ {v} w g → ψ q t (h (⊲-tr um w) g) g v g C.self (⊲-tr tm w) (⊲-tr am w))
ψ⁰ q t (oe es x) gu m gm um tm am = ψ q t x gu m gm um tm (⊲-tr (C.suc C.self) am)
ψ⁰ q t (oe (el n) x) gu m gm um tm am = ψ q t x gu m gm um tm (⊲-tr (C.lim n C.self) am)
ψ⁰ q t (oL j k e x) gu m gm um tm am = ψL q t j x gu m gm um tm (⊲-tr e um)
ψ⁰ q t (ow p g′ x) gu m gm um tm am = ψ q t x g′ m gm (⊲-tr p um) tm am

ψL q t zero x gu m gm um tm km = ψ q t x gu m gm um tm km
ψL q t (suc j) x gu m gm um tm km = ψL q t j x gu m gm um tm km

ψ₀ x gu v gv uv av with mx gu gv uv (z⊲ v) av
... | mx′ m gm um tm am mv = ψ₀⁰ x gu m gm um am

ψ₀⁰ o0 gu m gm um am = FL.suc FL.zero
ψ₀⁰ (os x) gu m gm um am = FL.lim (rep₀ (ψ₀ x gu m gm um am))
ψ₀⁰ (ol F) gu m gm um am = FL.lim (λ n → ψ₀ (F n) gu m gm um am)
ψ₀⁰ {p} {a} (oi {k = k} r h) gu m gm um am =
  FL.lim (λ n → ψ₀ (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n))) gm m gm C.self am)
ψ₀⁰ {a = a} (od {h = h₀} j k r h) gu m gm um am =
  FL.lim (λ n → ψ₀ (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n))) gm m gm C.self am)
ψ₀⁰ (oc x h) gu m gm um am =
  FL.lim (yss gm (ψ₀ x gu m gm um am) (λ i → ψ₀ (h (⊲-tr um (Ix.up i)) (Ix.gη i)) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (⊲-tr am (Ix.up i))))
ψ₀⁰ (oe es x) gu m gm um am = ψ₀ x gu m gm um (⊲-tr (C.suc C.self) am)
ψ₀⁰ (oe (el n) x) gu m gm um am = ψ₀ x gu m gm um (⊲-tr (C.lim n C.self) am)
ψ₀⁰ (oL j k e x) gu m gm um am = ψ₀L j x gu m gm um (⊲-tr e um)
ψ₀⁰ (ow p g′ x) gu m gm um am = ψ₀ x g′ m gm (⊲-tr p um) am

ψ₀L zero x gu m gm um km = ψ₀ x gu m gm um km
ψ₀L (suc j) x gu m gm um km = ψ₀L j x gu m gm um km
```

## §6 闭项

$\psi_0(\Omega_{\Omega\cdot p+a})$. 世界 $u_0$ 要在 $a$ 之上.

```agda
Tψ : ∀ p a u₀ → Gw u₀ → a ⊲ u₀ → Ord₀
Tψ p a u₀ g e = ψ₀ (Ω̇ p a) g₀ u₀ g (pos g) e
```

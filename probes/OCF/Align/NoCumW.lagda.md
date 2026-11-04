# 不累加的世界: 折叠

> 不含记号. 结论写在 [NoCum](NoCum.lagda.md). 层是 $(p,a)$, 目标 $(q,t)$ 的 $t$ 自己是世界的下界, 与 [CumUpW](CumUpW.lagda.md) 同形. **没有链, 没有 `next`, 没有 `⊞`:** 目标 $(0,0)$ 不再特殊, 闭包 `oc` 留在第 $(0,0)$ 层的数据里, 只有计值 ([NoCumForce](NoCumForce.lagda.md)) 才走链. 本文件的导入闭包不含 `CumReadBase`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.NoCumW where

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
```

## §0 世界

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

## §5 折叠

`mx`: $\max(u,t,a)$, 字面比较, 运行世界 $v$ 只作证据. 输出的世界是它, 不是 $v$.

```agda
ψ  : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → t ⊲ v → a ⊲ v → 𝓞 q t v
ψᵐ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → t ⊲ v → a ⊲ v → 𝓞 q t v
ψ⁰ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → t ⊲ m → a ⊲ m → 𝓞 q t m
ψL : ∀ {p h k u} q t (j : h <ᴺ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → t ⊲ m → k ⊲ m → 𝓞 q t m

ψ q t x gu v gv uv tv av = ψᵐ q t x gu v gv uv tv av

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

```

## §6 闭项

$\psi_0(\Omega_{\Omega\cdot p+a})$ 的**数据**. 它还不是树: 闭包的链要证书 ([NoCumForce](NoCumForce.lagda.md)).

```agda
Tᴰ : ∀ p a u₀ → Gw u₀ → a ⊲ u₀ → 𝓞 zero azero u₀
Tᴰ p a u₀ g e = ψ zero azero (Ω̇ p a) g₀ u₀ g (pos g) (z⊲ u₀) e
```

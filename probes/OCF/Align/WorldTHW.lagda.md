# 带高度世界, 高度是世界里的下标 (一): 折叠

> 入口 [WorldTH](WorldTH.lagda.md). 不含记号. 由 [CumUpW](CumUpW.lagda.md) 改写. 差别: 高度从 $\mathbb N$ 换成 `Hg`: 一个层号 `ht a` 或者顶 `top`. 高度上的序 `_<ᴴ_` 是路径; 高度的比较和下标的比较一样, 在字面的世界之下做 (`hcmp`). 顶的第 0 行是 `oc`, 第 $v$ 支的高度是 $v$ 本身. 世界 $m$ 现在是 $\max(u,t,a,p,q)$.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WorldTHW where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; ≪∘; ≪S; ≪⊲; S→⊲; Rk; keep; rise; cmpN; cmpF; steps)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next; next-⊲; Lg-next)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀; gnext)
```

## §1 高度

`tφ f` 是对 $A$ 分支的高度, 第 $a$ 支的高度是 `f a`. 我们只用 `tφ ht`, 读作 $\Omega^2$ 这个高度; 其他的 `f` 过不了证据 `HO`. 让 $f$ 是变元只为一件事: $f\,a$ 是 `tφ f` 的结构子项, 递归与停机不用另加秩.

```agda
data Hg : Set where
  ht : A → Hg
  tφ : (A → Hg) → Hg

top : Hg
top = tφ ht

hA : Hg → A
hA (ht a) = a
hA (tφ f) = azero

infix 4 _<ᴴ_
data _<ᴴ_ : Hg → Hg → Set where
  here : ∀ {a} → ht a <ᴴ ht (asuc a)
  st   : ∀ {h b} → h <ᴴ ht b → h <ᴴ ht (asuc b)
  lh   : ∀ {f} n → ht (f n) <ᴴ ht (alim f)
  ll   : ∀ {h f} n → h <ᴴ ht (f n) → h <ᴴ ht (alim f)
  tp   : ∀ {f} a → f a <ᴴ tφ f
  tq   : ∀ {h f} a → h <ᴴ f a → h <ᴴ tφ f

-- 高度在世界之下; 顶只能是 tφ ht
HO : Hg → A → Set
HO (ht a) v = a ⊲ v
HO (tφ f) v = f ≡ ht

HO↑ : ∀ {h u v} → HO h u → u ⊲ v → HO h v
HO↑ {ht _} b w = ⊲-tr b w
HO↑ {tφ _} b w = b

hw : ∀ {h v} → HO h v → hA h ⊲ v
hw {ht _} b = b
hw {tφ _} {v} b = z⊲ v

HO⇓ : ∀ {h v m} → HO h v → hA h ⊲ m → HO h m
HO⇓ {ht _} b x = x
HO⇓ {tφ _} b x = b

-- 顶上的节点要自己说高度在世界之下. 只有 tφ ht 才要, 所以 f ≡ ht 是前提: 这样 Ω̇ 对一切 f 全
Hb : Hg → Hg → A → Set
Hb (ht _) h u = ⊤
Hb (tφ f) h u = f ≡ ht → hA h ⊲ u

HT : Hg → Set
HT (ht _) = ⊤
HT (tφ f) = f ≡ ht

ho→ht : ∀ {p v} → HO p v → HT p
ho→ht {ht _} b = tt
ho→ht {tφ _} b = b

<HO : ∀ {h p} → h <ᴴ ht p → HO h p
<HO here = C.suc C.self
<HO (st j) = HO↑ (<HO j) (C.suc C.self)
<HO (lh n) = C.lim n C.self
<HO (ll n j) = HO↑ (<HO j) (C.lim n C.self)

<tr : ∀ {a b c} → a <ᴴ b → b <ᴴ c → a <ᴴ c
<tr j here = st j
<tr j (st i) = st (<tr j i)
<tr j (lh n) = ll n j
<tr j (ll n i) = ll n (<tr j i)
<tr j (tp a) = tq a j
<tr j (tq a i) = tq a (<tr j i)

hoL : ∀ {h a m} → h <ᴴ ht a → hA h ⊲ m → HO h m
hoL here x = x
hoL (st j) x = hoL j x
hoL (lh n) x = x
hoL (ll n j) x = hoL j x

<⊲ : ∀ {h a} → h <ᴴ ht a → hA h ⊲ a
<⊲ here = C.suc C.self
<⊲ (st j) = C.suc (<⊲ j)
<⊲ (lh n) = C.lim n C.self
<⊲ (ll n j) = C.lim n (<⊲ j)

-- 世界之下的高度
hmm : ∀ {h p u m} (i : h <ᴴ p) → Hb p h u → u ⊲ m → HO p m → HO h m
hmm here hb um pm = HO↑ (<HO here) pm
hmm (st j) hb um pm = HO↑ (<HO (st j)) pm
hmm (lh n) hb um pm = HO↑ (<HO (lh n)) pm
hmm (ll n j) hb um pm = HO↑ (<HO (ll n j)) pm
hmm (tp a) hb um refl = ⊲-tr (hb refl) um
hmm (tq a j) hb um refl = hoL j (⊲-tr (hb refl) um)

hb↑ : ∀ {p h u v} → Hb p h u → u ⊲ v → Hb p h v
hb↑ {p = ht _} b w = tt
hb↑ {p = tφ _} b w = λ e → ⊲-tr (b e) w

no-tφ : ∀ {x a} → tφ x <ᴴ ht a → ⊥
no-tφ (st j) = no-tφ j
no-tφ (ll n j) = no-tφ j

-- 高度差一层: 下面一层总在上面一层的 hA 之下
hA< : ∀ {h p′} → h <ᴴ p′ → p′ <ᴴ top → hA h ⊲ hA p′
hA< j (tp a) = <⊲ j
hA< {p′ = ht _} j (tq a i) = <⊲ j
hA< {p′ = tφ _} j (tq a i) = ⊥-elim (no-tφ i)

-- 层在世界之下
LB : Hg → A → A → Set
LB p a v = (a ⊲ v) × HO p v

lb↑ : ∀ {p a v w} → LB p a v → v ⊲ w → LB p a w
lb↑ (x , y) w = ⊲-tr x w , HO↑ y w

lb0 : ∀ v → LB (ht azero) azero v
lb0 v = z⊲ v , z⊲ v

lb≪ : ∀ {p k a v} → k ≪ a → LB p a v → LB p k v
lb≪ r (x , y) = ⊲-tr (≪⊲ r) x , y

lbS : ∀ {p k a v} → k ⊲ a → LB p a v → LB p k v
lbS r (x , y) = ⊲-tr r x , y
```

## §2 高度的比较

```agda
lt⊲ : ∀ {a b} → a ⊲ b → (a ≡ b) ⊎ (ht a <ᴴ ht b)
lt⊲ C.self = inj₁ refl
lt⊲ (C.suc p) with lt⊲ p
... | inj₁ refl = inj₂ here
... | inj₂ l = inj₂ (st l)
lt⊲ (C.lim n p) with lt⊲ p
... | inj₁ refl = inj₂ (lh n)
... | inj₂ l = inj₂ (ll n l)

data HC (p q : Hg) (m : A) : Set where
  hlt : (i : p <ᴴ q) → Hb q p m → HC p q m
  hgt : q <ᴴ p → HC p q m
  heq : p ≡ q → HC p q m

hbHt : ∀ {h b m} → Hb (ht b) h m
hbHt = tt

hcmp : ∀ p q {m} → HO p m → HO q m → Lg m → HC p q m
hcmp (tφ f) (tφ g) refl refl w = heq refl
hcmp (ht a) (tφ g) pm refl w = hlt (tp a) (λ _ → pm)
hcmp (tφ f) (ht b) refl qm w = hgt (tp b)
hcmp (ht a) (ht b) pm qm w with cmpF pm qm w
... | inj₁ b⊲a with lt⊲ b⊲a
...   | inj₁ refl = heq refl
...   | inj₂ l = hgt l
hcmp (ht a) (ht b) pm qm w | inj₂ a⊲b with lt⊲ a⊲b
...   | inj₁ refl = heq refl
...   | inj₂ l = hlt l tt
```

## §3 数据树

`𝓞 p a u`: 高度 $p$, 层 $a$, 世界 $u$.

```agda
data Stp : ∀ {a L} → Strict a L → Set where
  es : ∀ {b} → Stp {b} {asuc b} (ss C.self)
  el : ∀ {f} n → Stp {f n} {alim f} (sl n C.self)

module _ (p : Hg) (a : A) (V : ∀ {b} → Strict b a → A → Set) (Lw : ∀ {h} → h <ᴴ p → A → A → Set) where
  data O₊ : A → Set where
    o0 : ∀ {u} → O₊ u
    os : ∀ {u} → O₊ u → O₊ u
    ol : ∀ {u} → (ℕ → O₊ u) → O₊ u
    oi : ∀ {u k} (r : k ≪ a) → (∀ {v} → u ⊲ v → Gw v → V (≪S r) v → O₊ v) → O₊ u
    od : ∀ {u h} (i : h <ᴴ p) (k : A) → (k ≪ u) × Hb p h u → (∀ {v} → u ⊲ v → Gw v → Lw i k v → O₊ v) → O₊ u
    oc : ∀ {u} → O₊ u → (∀ {v} → u ⊲ v → Gw v → O₊ v) → O₊ u
    oe : ∀ {u b} {R : Strict b a} → Stp R → V R u → O₊ u
    oL : ∀ {u h} (i : h <ᴴ p) (k : A) → (k ⊲ u) × Hb p h u → Lw i k u → O₊ u
    ow : ∀ {u v} → u ⊲ v → Gw u → O₊ u → O₊ v

𝓞  : Hg → A → A → Set
Vs : ∀ p a {b} → Strict b a → A → Set
Vc : ∀ p a {b} → b ⊲ a → A → Set
Low : ∀ p {h} → h <ᴴ p → A → A → Set
𝓞 p a = O₊ p a (Vs p a) (Low p)
Vs p (asuc b) (ss P) u = Vc p b P u
Vs p (alim f) (sl n P) u = Vc p (f n) P u
Vc p a C.self u = 𝓞 p a u
Vc p (asuc b) (C.suc P) u = Vc p b P u
Vc p (alim f) (C.lim n P) u = Vc p (f n) P u
Low _ (here {a}) k u = 𝓞 (ht a) k u
Low _ (st {b = b} j) k u = Low (ht b) j k u
Low _ (lh {f} n) k u = 𝓞 (ht (f n)) k u
Low _ (ll {f = f} n j) k u = Low (ht (f n)) j k u
Low _ (tp {f} a) k u = 𝓞 (f a) k u
Low _ (tq {f = f} a j) k u = Low (f a) j k u

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

outL : ∀ {p h k u} (i : h <ᴴ p) → Low p i k u → 𝓞 h k u
outL here x = x
outL (st i) x = outL i x
outL (lh n) x = x
outL (ll n i) x = outL i x
outL (tp a) x = x
outL (tq a i) x = outL i x

inL : ∀ {p h k u} (i : h <ᴴ p) → 𝓞 h k u → Low p i k u
inL here x = x
inL (st i) x = inL i x
inL (lh n) x = x
inL (ll n i) x = inL i x
inL (tp a) x = x
inL (tq a i) x = inL i x

out-inC : ∀ {p a b u} (P : b ⊲ a) (x : 𝓞 p b u) → outC P (inC P x) ≡ x
out-inC C.self x = refl
out-inC (C.suc P) x = out-inC P x
out-inC (C.lim n P) x = out-inC P x

out-inS : ∀ {p a b u} (R : Strict b a) (x : 𝓞 p b u) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x

out-inL : ∀ {p h k u} (i : h <ᴴ p) (x : 𝓞 h k u) → outL i (inL i x) ≡ x
out-inL here x = refl
out-inL (st i) x = out-inL i x
out-inL (lh n) x = refl
out-inL (ll n i) x = out-inL i x
out-inL (tp a) x = refl
out-inL (tq a i) x = out-inL i x
```

## §4 $\Omega$, 加法

`Ω̇ p a`: 闭的元素, 世界是 $1$. 高度 $0$ 第 0 行是 $1$. 高度 $b+1$ 第 0 行是闭包: 第一支 $(b,1)$, 分支 $(b,v)$. 高度 $\lim f$ 是链. **顶的第 0 行也是闭包: 第 $v$ 支是高度 $v$ 的第 0 行.** 这就是 $\Omega_{\Omega^2}$.

```agda
hb₀ : ∀ f → Hb (tφ f) (f azero) one
hb₀ f refl = z⊲ one

hbv : ∀ f v → Hb (tφ f) (f v) v
hbv f v refl = C.self

Ω̇ : ∀ p a → 𝓞 p a one
Ω̇ p (asuc c) = oi C.zero (λ q g z → oe es z)
Ω̇ p (alim f) = ol (λ n → oe (el n) (Ω̇ p (f n)))
Ω̇ (ht azero) azero = os o0
Ω̇ (ht (asuc p)) azero = oc (oL here one (C.self , tt) (Ω̇ (ht p) one)) (λ {v} q g → oL here v (C.self , tt) (ow (pos g) g₀ (Ω̇ (ht p) v)))
Ω̇ (ht (alim f)) azero = ol (λ n → oL (lh n) azero (z⊲ one , tt) (Ω̇ (ht (f n)) azero))
Ω̇ (tφ f) azero = oc (oL (tp azero) azero (z⊲ one , hb₀ f) (Ω̇ (f azero) azero)) (λ {v} q g → oL (tp v) azero (z⊲ v , hbv f v) (ow (pos g) g₀ (Ω̇ (f v) azero)))

Ω̇at : ∀ p a {v} → Gw v → 𝓞 p a v
Ω̇at p a g = ow (pos g) g₀ (Ω̇ p a)

record Mx (u : A) (q : Hg) (t : A) (p : Hg) (a v : A) : Set where
  constructor mx′
  field
    m   : A
    gm  : Gw m
    um  : u ⊲ m
    tm  : LB q t m
    am  : LB p a m
    mv  : m ⊲ v

-- 五个数的 max, 一个一个并
record Jn (u v : A) : Set where
  constructor jn
  field
    j   : A
    gj  : Gw j
    uj  : u ⊲ j
    jv  : j ⊲ v
open Jn

join : ∀ {u x v} → Gw u → Gw v → u ⊲ v → x ⊲ v → Σ (Jn u v) (λ J → x ⊲ j J)
join {u} {x} gu gv uv xv with cmpF uv xv (lgw gv)
... | inj₁ x⊲u = jn u gu C.self uv , x⊲u
... | inj₂ u⊲x = jn x (gw (lg⊲ xv (lgw gv)) (⊲-tr (pos gu) u⊲x)) u⊲x xv , C.self

mx : ∀ {u q t p a v} → Gw u → Gw v → u ⊲ v → LB q t v → LB p a v → Mx u q t p a v
mx {u} {q} {t} {p} {a} {v} gu gv uv (tv , qv) (av , pv)
  with join gu gv uv tv
... | jn j₁ g₁ u₁ v₁ , t₁ with join g₁ gv v₁ av
... | jn j₂ g₂ u₂ v₂ , a₂ with join g₂ gv v₂ (hw qv)
... | jn j₃ g₃ u₃ v₃ , q₃ with join g₃ gv v₃ (hw pv)
... | jn j₄ g₄ u₄ v₄ , p₄ =
  mx′ j₄ g₄ (⊲-tr u₁ (⊲-tr u₂ (⊲-tr u₃ u₄)))
      (⊲-tr t₁ (⊲-tr u₂ (⊲-tr u₃ u₄)) , HO⇓ qv (⊲-tr q₃ u₄))
      (⊲-tr a₂ (⊲-tr u₃ u₄) , HO⇓ pv p₄)
      v₄

-- 右边元素的层 (p′, b) 怎么放进左边的层 (p, a): 同高度走第一位置, 低高度只要下标在世界之下
data Rel : Hg → A → Hg → A → Set where
  sa : ∀ {p a b} → b ⊲ a → Rel p b p a
  lw : ∀ {h p b a} → h <ᴴ p → Rel h b p a

bw : ∀ {p′ b p a} → Rel p′ b p a → A
bw (sa P) = azero
bw {b = b} (lw i) = b

-- 世界要盖住的高度: 只有顶上才要
bB : ∀ {p′ b p a} → Rel p′ b p a → A
bB (sa P) = azero
bB {p = ht _} (lw i) = azero
bB {p′ = p′} {p = tφ _} (lw i) = hA p′

BW : ∀ {p′ b p a} → Rel p′ b p a → A → Set
BW {p = p} R v = LB (ht (bB R)) (bw R) v × HT p

bw↓ : ∀ {k b p′ p a v} (i : p′ <ᴴ p) → k ⊲ b → BW {b = b} {a = a} (lw i) v → BW {b = k} {a = a} (lw i) v
bw↓ {p = ht _} i s ((x , y) , h) = (⊲-tr s x , y) , h
bw↓ {p = tφ _} i s ((x , y) , h) = (⊲-tr s x , y) , h

bw↑ : ∀ {p′ b p a v w} (R : Rel p′ b p a) → BW R v → v ⊲ w → BW R w
bw↑ R (l , h) w = lb↑ l w , h

hbW : ∀ {p′ b p a v} (i : p′ <ᴴ p) → BW {b = b} {a = a} (lw i) v → Hb p p′ v
hbW {p = ht _} i b = tt
hbW {p = tφ _} i ((x , y) , h) = λ _ → y

hbTr : ∀ {h p′ p m b a} (j : h <ᴴ p′) (i : p′ <ᴴ p) → BW {b = b} {a = a} (lw i) m → Hb p h m
hbTr {p = ht _} j i b = tt
hbTr {p = tφ _} j i ((x , y) , refl) = λ _ → ⊲-tr (hA< j i) y

-- 同层 oL: 证据由节点给. 对 p 分情况
bwEe : ∀ {h p k u′ m a} (j : h <ᴴ p) → (k ⊲ u′) × Hb p h u′ → u′ ⊲ m → HT p → BW {b = k} {a = a} (lw j) m
bwEe {p = ht _} {m = m} j e tm h = (⊲-tr (proj₁ e) tm , z⊲ m) , h
bwEe {p = tφ _} j e tm refl = (⊲-tr (proj₁ e) tm , ⊲-tr (proj₂ e refl) tm) , refl

bwTr : ∀ {h p′ p k u′ m a b a₂} (j : h <ᴴ p′) (i : p′ <ᴴ p) → (k ⊲ u′) × Hb p′ h u′ → u′ ⊲ m → BW {b = b} {a = a₂} (lw i) m → BW {b = k} {a = a} (lw (<tr j i)) m
bwTr {p = ht _} {m = m} j i e tm ((x , y) , h) = (⊲-tr (proj₁ e) tm , z⊲ m) , h
bwTr {p = tφ _} j i e tm ((x , y) , refl) = (⊲-tr (proj₁ e) tm , ⊲-tr (hA< j i) y) , refl

subst′ : ∀ {x y v} → x ≡ y → y ⊲ v → x ⊲ v
subst′ refl q = q

lbu : ∀ {x v} → x ⊲ v → LB (ht azero) x v
lbu {v = v} e = e , z⊲ v

-- W + x: 左边不动, 世界是 max(u₀, u′, 层). 与运行世界无关
add  : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′ → Gw u′ → ∀ v → Gw v → u₀ ⊲ v → u′ ⊲ v → BW R v → 𝓞 p a v
add⁰ : ∀ {p a p′ b u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (R : Rel p′ b p a) → 𝓞 p′ b u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → BW R m → 𝓞 p a m
addL : ∀ {p a p′ h k u₀ u′} → 𝓞 p a u₀ → Gw u₀ → (t : h <ᴴ p) → (j : h <ᴴ p′) → Low p′ j k u′ → Gw u′ → ∀ m → Gw m → u₀ ⊲ m → u′ ⊲ m → BW {b = k} {a = a} (lw t) m → 𝓞 p a m

add W gu₀ R x gx v gv u₀v xv bv with mx gu₀ gv u₀v (lbu xv) (proj₁ bv)
... | mx′ m gm um tm am mv = ow mv gm (add⁰ W gu₀ R x gx m gm um (proj₁ tm) (am , proj₂ bv))

add⁰ W gu₀ R o0 gx m gm um tm am = ow um gu₀ W
add⁰ W gu₀ R (os x) gx m gm um tm am = os (add W gu₀ R x gx m gm um tm am)
add⁰ W gu₀ R (ol F) gx m gm um tm am = ol (λ n → add W gu₀ R (F n) gx m gm um tm am)
add⁰ W gu₀ (sa P) (oi r h) gx m gm um tm am =
  oi (≪∘ r P) (λ {v} q g y → add W gu₀ (sa P) (h (⊲-tr tm q) g (inS (≪S r) (outS (≪S (≪∘ r P)) y))) g v g (⊲-tr um q) C.self (lb0 v , proj₂ am))
add⁰ W gu₀ (lw i) (oi {k = k} r h) gx m gm um tm am =
  od i k (≪∘ r (proj₁ (proj₁ am)) , hbW i am) (λ {v} q g y → add W gu₀ (lw i) (h (⊲-tr tm q) g (inS (≪S r) (outL i y))) g v g (⊲-tr um q) C.self (bw↑ _ am q))
add⁰ W gu₀ (sa P) (od j k r h) gx m gm um tm am =
  od j k (≪∘ (proj₁ r) tm , hb↑ (proj₂ r) tm) (λ {v} q g y → add W gu₀ (sa P) (h (⊲-tr tm q) g (inL j (outL j y))) g v g (⊲-tr um q) C.self (lb0 v , proj₂ am))
add⁰ W gu₀ (lw i) (od j k r h) gx m gm um tm am =
  od (<tr j i) k (≪∘ (proj₁ r) tm , hbTr j i am) (λ {v} q g y → add W gu₀ (lw i) (h (⊲-tr tm q) g (inL j (outL (<tr j i) y))) g v g (⊲-tr um q) C.self (bw↑ _ am q))
add⁰ W gu₀ R (oc x h) gx m gm um tm am =
  oc (add W gu₀ R x gx m gm um tm am) (λ {v} q g → add W gu₀ R (h (⊲-tr tm q) g) g v g (⊲-tr um q) C.self (bw↑ _ am q))
add⁰ W gu₀ (sa P) (oe es x) gx m gm um tm am = add W gu₀ (sa (⊲-tr (C.suc C.self) P)) x gx m gm um tm am
add⁰ W gu₀ (lw i) (oe es x) gx m gm um tm am = add W gu₀ (lw i) x gx m gm um tm (bw↓ i (C.suc C.self) am)
add⁰ W gu₀ (sa P) (oe (el n) x) gx m gm um tm am = add W gu₀ (sa (⊲-tr (C.lim n C.self) P)) x gx m gm um tm am
add⁰ W gu₀ (lw i) (oe (el n) x) gx m gm um tm am = add W gu₀ (lw i) x gx m gm um tm (bw↓ i (C.lim n C.self) am)
add⁰ W gu₀ (sa P) (oL j k e x) gx m gm um tm am = addL W gu₀ j j x gx m gm um tm (bwEe j e tm (proj₂ am))
add⁰ W gu₀ (lw i) (oL j k e x) gx m gm um tm am = addL W gu₀ (<tr j i) j x gx m gm um tm (bwTr j i e tm am)
add⁰ W gu₀ R (ow p′ g′ x) gx m gm um tm am = add W gu₀ R x g′ m gm um (⊲-tr p′ tm) am

addL W gu₀ t here x gx m gm um tm km = add W gu₀ (lw t) x gx m gm um tm km
addL W gu₀ t (st j) x gx m gm um tm km = addL W gu₀ t j x gx m gm um tm km
addL W gu₀ t (lh n) x gx m gm um tm km = add W gu₀ (lw t) x gx m gm um tm km
addL W gu₀ t (ll n j) x gx m gm um tm km = addL W gu₀ t j x gx m gm um tm km
addL W gu₀ t (tp a) x gx m gm um tm km = add W gu₀ (lw t) x gx m gm um tm km
addL W gu₀ t (tq a j) x gx m gm um tm km = addL W gu₀ t j x gx m gm um tm km

rep : ∀ {p a u} → HT p → 𝓞 p a u → Gw u → ℕ → 𝓞 p a u
rep H y g zero = o0
rep H y g (suc zero) = y
rep {u = u} H y g (suc (suc m)) = add (rep H y g (suc m)) g (sa C.self) y g u g C.self C.self (lb0 u , H)

chainᵒ : ∀ {p k u} → Gw u → (𝓞 p k u → 𝓞 p k u) → ℕ → 𝓞 p k u
chainᵒ {p} {k} g f zero = Ω̇at p k g
chainᵒ g f (suc n) = f (chainᵒ g f n)
```

## §4 第 0 层

```agda
ord : ∀ {u} → 𝓞 (ht azero) azero u → Ord₀
ord o0 = FL.zero
ord (os x) = FL.suc (ord x)
ord (ol F) = FL.lim (λ n → ord (F n))
ord (oi () _)
ord (od () _ _ _)
ord (oc x h) = ord x
ord (oe () _)
ord (oL () _ _ _)
ord (ow p g x) = ord x

em : ∀ {u} → Ord₀ → 𝓞 (ht azero) azero u
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

-- 世界之下的层: 节点的高度和下标
lbd : ∀ {p h k u m a} (j : h <ᴴ p) → (k ≪ u) × Hb p h u → u ⊲ m → LB p a m → LB h k m
lbd j r um am = ⊲-tr (≪⊲ (proj₁ r)) um , hmm j (proj₂ r) um (proj₂ am)

lbe : ∀ {p h k u m a} (j : h <ᴴ p) → (k ⊲ u) × Hb p h u → u ⊲ m → LB p a m → LB h k m
lbe j e um am = ⊲-tr (proj₁ e) um , hmm j (proj₂ e) um (proj₂ am)

ψ  : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → LB q t v → LB p a v → 𝓞 q t v
ψᵐ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → LB q t v → LB p a v → 𝓞 q t v
ψ⁰ : ∀ {p a u} q t → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → LB q t m → LB p a m → 𝓞 q t m
ψL : ∀ {p h k u} q t (j : h <ᴴ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → LB q t m → LB h k m → 𝓞 q t m
ψ₀  : ∀ {p a u} → 𝓞 p a u → Gw u → ∀ v → Gw v → u ⊲ v → LB p a v → Ord₀
ψ₀⁰ : ∀ {p a u} → 𝓞 p a u → Gw u → ∀ m → Gw m → u ⊲ m → LB p a m → Ord₀
ψ₀L : ∀ {p h k u} (j : h <ᴴ p) → Low p j k u → Gw u → ∀ m → Gw m → u ⊲ m → LB h k m → Ord₀

ψ (ht azero) azero x gu v gv uv tv av = ow (pos gv) g₀ (em (ψ₀ x gu v gv uv av))
ψ (ht azero) (asuc t) x gu v gv uv tv av = ψᵐ (ht azero) (asuc t) x gu v gv uv tv av
ψ (ht azero) (alim f) x gu v gv uv tv av = ψᵐ (ht azero) (alim f) x gu v gv uv tv av
ψ (ht (asuc q)) t x gu v gv uv tv av = ψᵐ (ht (asuc q)) t x gu v gv uv tv av
ψ (ht (alim f)) t x gu v gv uv tv av = ψᵐ (ht (alim f)) t x gu v gv uv tv av
ψ (tφ f) t x gu v gv uv tv av = ψᵐ (tφ f) t x gu v gv uv tv av

ψᵐ q t x gu v gv uv tv av with mx gu gv uv tv av
... | mx′ m gm um tm am mv = ow mv gm (ψ⁰ q t x gu m gm um tm am)

ψ⁰ q t o0 gu m gm um tm am = Ω̇at q t gm
ψ⁰ q t (os x) gu m gm um tm am = ol (rep (ho→ht (proj₂ tm)) (ψ q t x gu m gm um tm am) gm)
ψ⁰ q t (ol F) gu m gm um tm am = ol (λ n → ψ q t (F n) gu m gm um tm am)
ψ⁰ {p} {a} q t (oi {k = k} r h) gu m gm um tm am with hcmp p q (proj₂ am) (proj₂ tm) (lgw gm)
... | hlt i b = od i k (≪∘ r (proj₁ am) , b) (λ w g y → ψ q t (h (⊲-tr um w) g (inS (≪S r) (outL i y))) g _ g C.self (lb↑ tm w) (lb↑ am w))
... | hgt _ = ol (λ n → ψ q t (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am) n))) gm m gm C.self tm am)
... | heq refl with cmpN (≪∘ r (proj₁ am)) (proj₁ tm) (lgw gm)
...   | keep s = oi s (λ w g y → ψ q t (h (⊲-tr um w) g (inS (≪S r) (outS (≪S s) y))) g _ g C.self (lb↑ tm w) (lb↑ am w))
...   | rise _ = ol (λ n → ψ q t (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am) n))) gm m gm C.self tm am)
ψ⁰ {p} {a} q t (od {h = h₀} j k r h) gu m gm um tm am with hcmp h₀ q (hmm j (proj₂ r) um (proj₂ am)) (proj₂ tm) (lgw gm)
... | hlt i b = od i k (≪∘ (proj₁ r) um , b) (λ w g y → ψ q t (h (⊲-tr um w) g (inL j (outL i y))) g _ g C.self (lb↑ tm w) (lb↑ am w))
... | hgt _ = ol (λ n → ψ q t (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am) n))) gm m gm C.self tm am)
... | heq refl with cmpN (≪∘ (proj₁ r) um) (proj₁ tm) (lgw gm)
...   | keep s = oi s (λ w g y → ψ q t (h (⊲-tr um w) g (inL j (outS (≪S s) y))) g _ g C.self (lb↑ tm w) (lb↑ am w))
...   | rise _ = ol (λ n → ψ q t (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am) n))) gm m gm C.self tm am)
ψ⁰ q t (oc x h) gu m gm um tm am =
  oc (ψ q t x gu m gm um tm am) (λ {v} w g → ψ q t (h (⊲-tr um w) g) g v g C.self (lb↑ tm w) (lb↑ am w))
ψ⁰ q t (oe es x) gu m gm um tm am = ψ q t x gu m gm um tm (lbS (C.suc C.self) am)
ψ⁰ q t (oe (el n) x) gu m gm um tm am = ψ q t x gu m gm um tm (lbS (C.lim n C.self) am)
ψ⁰ q t (oL j k e x) gu m gm um tm am = ψL q t j x gu m gm um tm (lbe j e um am)
ψ⁰ q t (ow p g′ x) gu m gm um tm am = ψ q t x g′ m gm (⊲-tr p um) tm am

ψL q t here x gu m gm um tm km = ψ q t x gu m gm um tm km
ψL q t (st j) x gu m gm um tm km = ψL q t j x gu m gm um tm km
ψL q t (lh n) x gu m gm um tm km = ψ q t x gu m gm um tm km
ψL q t (ll n j) x gu m gm um tm km = ψL q t j x gu m gm um tm km
ψL q t (tp a) x gu m gm um tm km = ψ q t x gu m gm um tm km
ψL q t (tq a j) x gu m gm um tm km = ψL q t j x gu m gm um tm km

ψ₀ x gu v gv uv av with mx gu gv uv (lb0 v) av
... | mx′ m gm um tm am mv = ψ₀⁰ x gu m gm um am

ψ₀⁰ o0 gu m gm um am = FL.suc FL.zero
ψ₀⁰ (os x) gu m gm um am = FL.lim (rep₀ (ψ₀ x gu m gm um am))
ψ₀⁰ (ol F) gu m gm um am = FL.lim (λ n → ψ₀ (F n) gu m gm um am)
ψ₀⁰ {p} {a} (oi {k = k} r h) gu m gm um am =
  FL.lim (λ n → ψ₀ (h um gm (inS (≪S r) (chainᵒ gm (λ z₁ → ψ p k (h um gm (inS (≪S r) z₁)) gm m gm C.self (lb≪ r am) am) n))) gm m gm C.self am)
ψ₀⁰ {a = a} (od {h = h₀} j k r h) gu m gm um am =
  FL.lim (λ n → ψ₀ (h um gm (inL j (chainᵒ gm (λ z₁ → ψ h₀ k (h um gm (inL j z₁)) gm m gm C.self (lbd j r um am) am) n))) gm m gm C.self am)
ψ₀⁰ (oc x h) gu m gm um am =
  FL.lim (yss gm (ψ₀ x gu m gm um am) (λ i → ψ₀ (h (⊲-tr um (Ix.up i)) (Ix.gη i)) (Ix.gη i) (Ix.η i) (Ix.gη i) C.self (lb↑ am (Ix.up i))))
ψ₀⁰ (oe es x) gu m gm um am = ψ₀ x gu m gm um (lbS (C.suc C.self) am)
ψ₀⁰ (oe (el n) x) gu m gm um am = ψ₀ x gu m gm um (lbS (C.lim n C.self) am)
ψ₀⁰ (oL j k e x) gu m gm um am = ψ₀L j x gu m gm um (lbe j e um am)
ψ₀⁰ (ow p g′ x) gu m gm um am = ψ₀ x g′ m gm (⊲-tr p um) am

ψ₀L here x gu m gm um km = ψ₀ x gu m gm um km
ψ₀L (st j) x gu m gm um km = ψ₀L j x gu m gm um km
ψ₀L (lh n) x gu m gm um km = ψ₀ x gu m gm um km
ψ₀L (ll n j) x gu m gm um km = ψ₀L j x gu m gm um km
ψ₀L (tp a) x gu m gm um km = ψ₀ x gu m gm um km
ψ₀L (tq a j) x gu m gm um km = ψ₀L j x gu m gm um km
```

## §6 闭项

$\psi_0(\Omega_{\Omega\cdot p+a})$, $p$ 是 `ht`; 顶是 $\psi_0(\Omega_{\Omega^2+a})$. 世界 $u_0$ 要在 $a$, $p$ 之上.

```agda
Tψ : ∀ p a u₀ → Gw u₀ → LB p a u₀ → Ord₀
Tψ p a u₀ g e = ψ₀ (Ω̇ p a) g₀ u₀ g (pos g) e
```

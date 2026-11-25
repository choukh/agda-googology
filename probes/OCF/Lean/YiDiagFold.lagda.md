# YiDiag 折叠：链不累加，目标层 0 逐项

**判决：定义与 `refl` 的行 (第 2 层)。** 从 [YiLeanFold](YiLeanFold.lagda.md) 改四处：结点折叠的链下一点就是这一点上的折叠值 (`chain j gk = iter gk top`)；
ω 倍从零起 (`mult`)；目标层 0 上极限层号的 `top` 逐项 (`ltop`)，别的目标层仍取部分和；目标层 0 的派发是 `⊤` (`Way zero j = ⊤`)，层号 `Lv` 不带位置搬运，
极限层号上不同支的位置一律折叠 (`cmp`)。没有合法性的证明。合法性在 [YiDiagLegal](YiDiagLegal.lagda.md)，闭项在 [YiDiagTw3](YiDiagTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDiagFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Nat.Properties using (_≟_)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiDiagCore
```

## 1 位置、派发、比较

`W m j`：保留 (槽位) 或折叠。`Way zero j = ⊤`：目标层 0 没有槽位，派发只有一种取值，并且对派发函数有 η 规则，
所以目标层 0 的折叠定义性地不依赖派发 (逐项的那一行合法要用到)。`wv` 把 `Way` 读成 `W`，`wk`, `wf` 造保留与折叠。

```agda
lev : (k : LF) → Pre k → LF
lev (suc k) (inj₁ _) = k
lev (suc k) (inj₂ r) = lev k r
lev (lim f) (n , r) = lev (f n) r
lev (lc k g) (η , _ , r) = lev (g η) r

data W (m j : LF) : Set where
  keep : (s : Pre m) → lev m s ≡ j → W m j
  fold : W m j

Way : LF → LF → Set
Way zero j = ⊤
Way (suc m) j = W (suc m) j
Way (lim f) j = W (lim f) j
Way (lc k g) j = W (lc k g) j

wv : ∀ m j → Way m j → W m j
wv zero j w = fold
wv (suc m) j w = w
wv (lim f) j w = w
wv (lc k g) j w = w

wk : ∀ m (s : Pre m) → Way m (lev m s)
wk zero ()
wk (suc m) s = keep s refl
wk (lim f) s = keep s refl
wk (lc k g) s = keep s refl

wf : ∀ m j → Way m j
wf zero j = tt
wf (suc m) j = fold
wf (lim f) j = fold
wf (lc k g) j = fold

Ext : LF → LF → Set
Ext m k = (r : Pre k) → Way m (lev k r)

self : ∀ k → Ext k k
self k = wk k
```

`Lv k`：`k` 由零、后继、ℕ 极限组成；不带任何证明或搬运，所以链点读成的 `Lv` 只依赖链点本身。
`cmp V q r`：目标在位置 `q`，结点在位置 `r`，结点层在目标层之下才保留；极限层号上两个位置在同一支才往下比，不同支折叠。

```agda
data Lv : LF → Set where
  v0 : Lv zero
  vs : ∀ {k} → Lv k → Lv (suc k)
  vl : ∀ {f} → (∀ n → Lv (f n)) → Lv (lim f)

cmp : ∀ {k} → Lv k → (q r : Pre k) → Way (lev k q) (lev k r)
cmpL : ∀ {f : ℕ → LF} (V : ∀ n → Lv (f n)) n (q : Pre (f n)) m (r : Pre (f m)) → Dec (n ≡ m) →
  Way (lev (f n) q) (lev (f m) r)

cmp v0 () r
cmp (vs {k} V) (inj₁ _) (inj₂ r) = wk k r
cmp (vs V) (inj₂ q) (inj₂ r) = cmp V q r
cmp (vs {k} V) (inj₁ _) (inj₁ _) = wf k k
cmp (vs {k} V) (inj₂ q) (inj₁ _) = wf (lev k q) k
cmp (vl V) (n , q) (m , r) = cmpL V n q m r (n ≟ m)

cmpL V n q .n r (yes refl) = cmp (V n) q r
cmpL {f} V n q m r (no _) = wf (lev (f n) q) (lev (f m) r)
```

## 2 结点的两行

保留：按槽位造结点，分支是目标层的折叠 `gm`。折叠：链在结点自己的第 `j` 层，从 `top` 起，下一点是这一点上结点层的折叠 `gk` (不累加)，观察 `gm`。

```agda
iter : ∀ {T : Set} → (T → T) → T → ℕ → T
iter h x zero = x
iter h x (suc n) = h (iter h x n)

nodeAt : ∀ {M} m (s : Pre m) → Bld M m → (Raw (lev m s) → Raw M) → Raw M
nodeAt (suc k) (inj₁ _) B = B (inj₁ tt)
nodeAt (suc k) (inj₂ p) B = nodeAt k p (λ r → B (inj₂ r))
nodeAt (lim f) (n , p) B = nodeAt (f n) p (λ r → B (n , r))
nodeAt (lc j g) (η , l , p) B = nodeAt (g η) p (λ r → B (η , l , r))

chain : ∀ j → (Raw j → Raw j) → ℕ → Raw j
chain j gk = iter gk G.top

Ψw : ∀ m j → W m j → (Raw j → Raw m) → (Raw j → Raw j) → Raw m
Ψw m .(lev m p) (keep p refl) gm gk = nodeAt m p G.lc gm
Ψw m j fold gm gk = G.lim (λ n → gm (chain j gk n))

Ψn : ∀ m j → Way m j → (Raw j → Raw m) → (Raw j → Raw j) → Raw m
Ψn m j w = Ψw m j (wv m j w)

ΨN : ∀ m k (r : Pre k) → Way m (lev k r) →
  (Lay.A (Lo k r) → Raw m) → (Lay.A (Lo k r) → Raw (lev k r)) → Raw m
ΨN m (suc k) (inj₁ _) = Ψn m k
ΨN m (suc k) (inj₂ r) = ΨN m k r
ΨN m (lim f) (n , r) = ΨN m (f n) r
ΨN m (lc j g) (η , _ , r) = ΨN m (g η) r
```

## 3 折叠

零给 `top`；后继给 ω 倍 `mult`，从零起；极限层号上的 `top` 在目标层 0 逐项，在别的目标层取部分和
(那里各支保留的结点挂在不同支的槽位上，互不为第一位置)。

```agda
mult : ∀ m → Raw m → Raw m
mult m y = G.lim (iter (plus m y) G.zero)

psum : ∀ m → (ℕ → Raw m) → ℕ → Raw m
psum m h = acc (λ n z → plus m z (h (suc n))) (h zero)

ltop : ∀ m → (ℕ → Raw m) → Raw m
ltop zero h = G.lim h
ltop (suc m) h = G.lim (psum (suc m) h)
ltop (lim f) h = G.lim (psum (lim f) h)
ltop (lc k g) h = G.lim (psum (lc k g) h)

Ψ : ∀ m {k} → Lv k → Ext m k → Raw k → Raw m
Ψ m V x G.zero = G.top
Ψ m V x (G.suc a) = mult m (Ψ m V x a)
Ψ m V x (G.lim f) = G.lim (λ n → Ψ m V x (f n))
Ψ m {k} V x (G.lc r g) =
  ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
Ψ m (vs V) x (G.em _ a) = Ψ m V (λ r → x (inj₂ r)) a
Ψ m (vl V) x (G.em n a) = Ψ m (V n) (λ r → x (n , r)) a
Ψ m v0 x G.top = mult m G.top
Ψ m {suc k} (vs V) x G.top =
  Ψn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
Ψ m (vl V) x G.top = ltop m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top)
```

## 4 行

都是 `refl`。

```agda
zero-row : ∀ m {k} (V : Lv k) x → Ψ m V x G.zero ≡ G.top
zero-row m V x = refl

suc-row : ∀ m {k} (V : Lv k) x a → Ψ m V x (G.suc a) ≡ G.lim (iter (plus m (Ψ m V x a)) G.zero)
suc-row m V x a = refl

lim-row : ∀ m {k} (V : Lv k) x f → Ψ m V x (G.lim f) ≡ G.lim (λ n → Ψ m V x (f n))
lim-row m V x f = refl

node-row : ∀ m {k} (V : Lv k) x r g → Ψ m V x (G.lc r g) ≡
  ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
node-row m V x r g = refl

keep-row : ∀ m p gm gk → Ψw m (lev m p) (keep p refl) gm gk ≡ nodeAt m p G.lc gm
keep-row m p gm gk = refl

fold-row : ∀ m j gm gk → Ψw m j fold gm gk ≡ G.lim (λ n → gm (chain j gk n))
fold-row m j gm gk = refl

fold-row⁰ : ∀ j (w : Way zero j) gm gk → Ψn zero j w gm gk ≡ G.lim (λ n → gm (chain j gk n))
fold-row⁰ j w gm gk = refl

chain-row : ∀ j gk n → chain j gk (suc n) ≡ gk (chain j gk n)
chain-row j gk n = refl

top-row⁰ : ∀ m x → Ψ m v0 x G.top ≡ mult m G.top
top-row⁰ m x = refl

top-rowˢ : ∀ m {k} (V : Lv k) x → Ψ m (vs V) x G.top ≡
  Ψn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
top-rowˢ m V x = refl

top-row-lim⁰ : ∀ {f} (V : ∀ n → Lv (f n)) (x : Ext zero (lim f)) →
  Ψ zero (vl V) x G.top ≡ G.lim (λ n → Ψ zero (V n) (λ r → x (n , r)) G.top)
top-row-lim⁰ V x = refl

top-row-limˢ : ∀ m {f} (V : ∀ n → Lv (f n)) (x : Ext (suc m) (lim f)) →
  Ψ (suc m) (vl V) x G.top ≡ G.lim (psum (suc m) (λ n → Ψ (suc m) (V n) (λ r → x (n , r)) G.top))
top-row-limˢ m V x = refl

-- 目标层 0 的折叠与派发无关 (派发的类型是到 ⊤ 的函数)。
dispatch-free : ∀ {k} (V : Lv k) (x y : Ext zero k) ξ → Ψ zero V x ξ ≡ Ψ zero V y ξ
dispatch-free V x y ξ = refl
```

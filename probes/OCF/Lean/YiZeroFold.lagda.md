# YiZero 折叠：ω 倍从零起

**判决：定义与 `refl` 的行 (第 2 层)。** 与 [YiLeanFold](YiLeanFold.lagda.md) 只差后继一行：`succ m y` 的基本列是 0, y, y+y, … (从零起，同参照 `ψ⁰ (suc a)`)，主线是 y, y+y, …。
链 (从 `top` 起，下一点是这一点加上折叠值) 与极限层号上 `top` 的部分和照抄主线。没有合法性的证明，没有值。
块在 [YiZeroCore](YiZeroCore.lagda.md)，合法性在 [YiZeroLegal](YiZeroLegal.lagda.md)，闭项在 [YiZeroTw3](YiZeroTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZeroFold where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst₂)
open import OCF.Lean.YiZeroCore
```

## 1 位置、派发、比较

```agda
lev : (k : LF) → Pre k → LF
lev (suc k) (inj₁ _) = k
lev (suc k) (inj₂ r) = lev k r
lev (lim f) (n , r) = lev (f n) r
lev (lc k g) (η , _ , r) = lev (g η) r

data Way (m j : LF) : Set where
  keep : (s : Pre m) → lev m s ≡ j → Way m j
  fold : Way m j

Ext : LF → LF → Set
Ext m k = (r : Pre k) → Way m (lev k r)

Shift : LF → LF → Set
Shift a b = (q : Pre a) → Σ (Pre b) λ q′ → lev b q′ ≡ lev a q

data Lv : LF → Set where
  v0 : Lv zero
  vs : ∀ {k} → Lv k → Lv (suc k)
  vl : ∀ {f} → (∀ n → Lv (f n)) → (∀ n → Shift (f n) (f (suc n))) → Lv (lim f)

shift : ∀ {f : ℕ → LF} → (∀ n → Shift (f n) (f (suc n))) → ∀ {n m} → n ≤′ m → Shift (f n) (f m)
shift st ≤′-refl q = q , refl
shift st (≤′-step p) q =
  proj₁ (st _ (proj₁ (shift st p q))) , trans (proj₂ (st _ _)) (proj₂ (shift st p q))

cmp : ∀ {k} → Lv k → (q r : Pre k) → Way (lev k q) (lev k r)
cmp v0 () r
cmp (vs V) (inj₁ _) (inj₂ r) = keep r refl
cmp (vs V) (inj₂ q) (inj₂ r) = cmp V q r
cmp (vs V) q r = fold
cmp (vl V st) (n , q) (m , r) =
  subst₂ Way (proj₂ (shift st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (shift st (≤⇒≤′ (m≤n⊔m n m)) r))
    (cmp (V (n ⊔ m)) (proj₁ (shift st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₁ (shift st (≤⇒≤′ (m≤n⊔m n m)) r)))
```

## 2 结点的两行

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
chain j gk = iter (λ η → plus j η (gk η)) G.top

Ψn : ∀ m j → Way m j → (Raw j → Raw m) → (Raw j → Raw j) → Raw m
Ψn m .(lev m p) (keep p refl) gm gk = nodeAt m p G.lc gm
Ψn m j fold gm gk = G.lim (λ n → gm (chain j gk n))

ΨN : ∀ m k (r : Pre k) → Way m (lev k r) →
  (Lay.A (Lo k r) → Raw m) → (Lay.A (Lo k r) → Raw (lev k r)) → Raw m
ΨN m (suc k) (inj₁ _) = Ψn m k
ΨN m (suc k) (inj₂ r) = ΨN m k r
ΨN m (lim f) (n , r) = ΨN m (f n) r
ΨN m (lc j g) (η , _ , r) = ΨN m (g η) r
```

## 3 折叠

`succ` 是这里唯一改动的定义。

```agda
succ : ∀ m → Raw m → Raw m
succ m y = G.lim (acc (λ _ z → plus m y z) G.zero)

psum : ∀ m → (ℕ → Raw m) → ℕ → Raw m
psum m h = acc (λ n z → plus m z (h (suc n))) (h zero)

self : ∀ k → Ext k k
self k r = keep r refl

Ψ : ∀ m {k} → Lv k → Ext m k → Raw k → Raw m
Ψ m V x G.zero = G.top
Ψ m V x (G.suc a) = succ m (Ψ m V x a)
Ψ m V x (G.lim f) = G.lim (λ n → Ψ m V x (f n))
Ψ m {k} V x (G.lc r g) =
  ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
Ψ m (vs V) x (G.em _ a) = Ψ m V (λ r → x (inj₂ r)) a
Ψ m (vl V st) x (G.em n a) = Ψ m (V n) (λ r → x (n , r)) a
Ψ m v0 x G.top = succ m G.top
Ψ m {suc k} (vs V) x G.top =
  Ψn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
Ψ m (vl V st) x G.top = G.lim (psum m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top))
```

## 4 行

都是 `refl`。

```agda
zero-row : ∀ m {k} (V : Lv k) x → Ψ m V x G.zero ≡ G.top
zero-row m V x = refl

suc-row : ∀ m {k} (V : Lv k) x a → Ψ m V x (G.suc a) ≡ succ m (Ψ m V x a)
suc-row m V x a = refl

succ-row₀ : ∀ m y → succ m y ≡ G.lim (acc (λ _ z → plus m y z) G.zero)
succ-row₀ m y = refl

succ-row₁ : ∀ m y n → acc (λ _ z → plus m y z) G.zero (suc n) ≡ plus m y (acc (λ _ z → plus m y z) G.zero n)
succ-row₁ m y n = refl

lim-row : ∀ m {k} (V : Lv k) x f → Ψ m V x (G.lim f) ≡ G.lim (λ n → Ψ m V x (f n))
lim-row m V x f = refl

node-row : ∀ m {k} (V : Lv k) x r g → Ψ m V x (G.lc r g) ≡
  ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
node-row m V x r g = refl

root-row : ∀ m j (w : Way m j) gm gk → ΨN m (suc j) (inj₁ tt) w gm gk ≡ Ψn m j w gm gk
root-row m j w gm gk = refl

keep-row : ∀ m p gm gk → Ψn m (lev m p) (keep p refl) gm gk ≡ nodeAt m p G.lc gm
keep-row m p gm gk = refl

fold-row : ∀ m j gm gk → Ψn m j fold gm gk ≡ G.lim (λ n → gm (chain j gk n))
fold-row m j gm gk = refl

chain-row : ∀ j gk n → chain j gk (suc n) ≡ plus j (chain j gk n) (gk (chain j gk n))
chain-row j gk n = refl

em-rowˢ : ∀ m {k} (V : Lv k) x a → Ψ m (vs V) x (G.em tt a) ≡ Ψ m V (λ r → x (inj₂ r)) a
em-rowˢ m V x a = refl

em-rowˡ : ∀ m {f} (V : ∀ n → Lv (f n)) (st : ∀ n → Shift (f n) (f (suc n))) (x : Ext m (lim f)) n a →
  Ψ m (vl V st) x (G.em n a) ≡ Ψ m (V n) (λ r → x (n , r)) a
em-rowˡ m V st x n a = refl

top-row⁰ : ∀ m x → Ψ m v0 x G.top ≡ succ m G.top
top-row⁰ m x = refl

top-rowˢ : ∀ m {k} (V : Lv k) x → Ψ m (vs V) x G.top ≡
  Ψn m k (x (inj₁ tt)) (λ η → Ψ m V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
top-rowˢ m V x = refl

top-rowˡ : ∀ m {f} (V : ∀ n → Lv (f n)) (st : ∀ n → Shift (f n) (f (suc n))) (x : Ext m (lim f)) →
  Ψ m (vl V st) x G.top ≡
  G.lim (psum m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top))
top-rowˡ m V st x = refl
```

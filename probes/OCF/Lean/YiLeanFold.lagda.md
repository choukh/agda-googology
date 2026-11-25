# YiLean 折叠：写在第 k 层的树上，派发读位置

**判决：定义与 `refl` 的行 (第 2 层)。** 折叠 `Ψ m V x ξ` 把第 `k` 层的树 `ξ` 折到目标层 `m`；`k` 是只含零、后继、ℕ 极限的层号，`V : Lv k` 带着极限处
相邻两支之间的位置搬运，比较两个位置用它 (`cmp`)。外部派发 `x` 对每个位置给出保留 (带槽位) 或折叠。没有合法性的证明，没有值。
不否定别的写法。块在 [YiLeanCore](YiLeanCore.lagda.md)，合法性在 [YiLeanLegal](YiLeanLegal.lagda.md)，塔的第 3 项在 [YiLeanTw3](YiLeanTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLeanFold where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst₂)
open import OCF.Lean.YiLeanCore
```

## 1 位置、派发、比较

`lev k r` 是位置 `r` 上的层号。`Way m j`：层号 `j` 的结点在目标层 `m` 上保留 (槽位 `s`，`lev m s ≡ j`) 或折叠。
`Lv k`：`k` 由零、后继、ℕ 极限组成，极限处带相邻两支之间保持层号的位置搬运。`cmp V q r`：目标在位置 `q`，结点在位置 `r`，
结点层在目标层之下才保留；极限处把两个位置都搬到编号较大的那一支再比。

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

`ΨN` 沿位置走到根，那里 `Lo` 是 `layer j`，分支域就是 `Raw j`；`Ψn` 里层号 `j` 是变量，所以 `keep s refl` 之后分支域是槽位那一层，
`nodeAt` 沿槽位走到根造结点。保留：按槽位造结点，分支是目标层的折叠 `gm`。折叠：链在第 `j` 层，从 `top` 起，
下一点是这一点加上结点自己那一层的折叠 `gk`，观察 `gm`。

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

零给 `top`；后继给 ω 倍 `succ`；ℕ 极限逐项；结点按派发走 `ΨN`，结点自己那一层的折叠用目标为这个位置的 `cmp`；
嵌入进孩子层，派发限制到孩子；`top` 在后继层号上是根位置的结点 (分支是孩子层的树，推进用目标为孩子层自己的派发 `self`)，
在极限层号上取各支的部分和 (各支的 `top` 互不为第一位置，同 `add` 的 `x + top`)。

```agda
succ : ∀ m → Raw m → Raw m
succ m y = G.lim (acc (λ _ z → plus m y z) y)

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

-- top 与根位置上分支为嵌入的结点折叠相同.
top-as-node : ∀ m {k} (V : Lv k) x →
  Ψ m (vs V) x G.top ≡ Ψ m (vs V) x (G.lc (inj₁ tt) (λ η → G.em tt η))
top-as-node m V x = refl

top-rowˡ : ∀ m {f} (V : ∀ n → Lv (f n)) (st : ∀ n → Shift (f n) (f (suc n))) (x : Ext m (lim f)) →
  Ψ m (vl V st) x G.top ≡
  G.lim (psum m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top))
top-rowˡ m V st x = refl
```

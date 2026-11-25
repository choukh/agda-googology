# YiNext 折叠的部件：加法的合法性，公共上界 `Lv`，各行的合法性

**判决：定义与编译定理 (第 2、3 层的部件)，无前提。** 加法的三条 (照主线)；公共上界 `Lv` 在零、后继、ℕ 极限之外加 Ω 结点层号 `tw 2` 的情形 `vΩ`；
`vΩ` 带分支的公共上界 `V`，以及沿 "加上一段" 的下行路径 `Up` (链的观察单调要用)。Ω 结点层号上的两个位置一律折叠 (`cmp`)。
`top` 在 `tw 2` 上的两行的部件：保留时的分支族 `Kf` (沿分支下标的结构累加，坐标取归一 `nrm`，对一切下标有定义且单调)，折叠时的链 `pts`。
不否定别的写法。折叠本身在 [YiNextFold](YiNextFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextBase where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst₂)
open import OCF.Lean.YiNextCore
```

## 1 加法的合法性

与主线 [YiLeanLegal](YiLeanLegal.lagda.md) §1, §2 相同；放在 `Lv` 之前，因为 `vΩ` 的字段要用 `plus-lgl`。

```agda
Br : (X : Lay) (M : LF) → (Lay.A X → Raw M) → Set
Br X M g = (∀ η → Lay.lg X η → Lgl M (g η)) ×
  (∀ η η′ → Lay.lg X η → Le X η η′ → Lay.lg X η′ → Cp M (g η) (g η′))

DnB : ∀ {M k} → Bld M k → Set
DnB {M} {k} B = ∀ r g {z} → Cp M z (g (Lay.tp (Lo k r))) → Dn M z (B r g)

LgB : ∀ {M k} → Bld M k → Set
LgB {M} {k} B = ∀ r g → Br (Lo k r) M g → Lgl M (B r g)

dnLc : ∀ {M} → DnB {M} {M} G.lc
dnLc r g p = p

lgLc : ∀ {M} → LgB {M} {M} G.lc
lgLc r g h = h

acc-ind : ∀ {T : Set} (P : T → Set) (s : ℕ → T → T) →
  (∀ n y → P y → P (s n y)) → ∀ x → P x → ∀ n → P (acc s x n)
acc-ind P s h x px zero = px
acc-ind P s h x px (suc n) = h n _ (acc-ind P s h x px n)

add-cp : ∀ {M} k (B : Bld M k) → DnB B → ∀ x {a b} → Cp k a b → Cp M (add k B x a) (add k B x b)
add-dn : ∀ {M} k (B : Bld M k) → DnB B → ∀ x {a} b → Dn k a b → Dn M (add k B x a) (add k B x b)

add-cp k B h x (inj₁ refl) = inj₁ refl
add-cp k B h x (inj₂ p) = inj₂ (add-dn k B h x _ p)

add-dn k B h x (G.suc b) p = add-cp k B h x p
add-dn k B h x (G.lim f) (n , p) = n , add-cp k B h x p
add-dn k B h x (G.lc r g) p = h r _ (add-cp k B h x p)
add-dn (suc k) B h x {G.em _ a} (G.em _ d) (refl , p) = add-dn k _ (λ r → h (inj₂ r)) x d p
add-dn (lim f) B h x {G.em n a} (G.em _ d) (refl , p) = add-dn (f n) _ (λ r → h (n , r)) x d p
add-dn (lc j g) B h x {G.em (η , l) a} (G.em _ d) (refl , p) =
  add-dn (g η) _ (λ r → h (η , l , r)) x d p

add-weak : ∀ {M} k (B : Bld M k) → DnB B → ∀ x a → Cp M x (add k B x a)
add-weak k B h x G.zero = inj₁ refl
add-weak k B h x (G.suc a) = inj₂ (add-weak k B h x a)
add-weak k B h x (G.lim f) = inj₂ (0 , add-weak k B h x (f 0))
add-weak k B h x (G.lc r g) = inj₂ (h r _ (add-weak k B h x (g _)))
add-weak zero B h x (G.em () a)
add-weak (suc k) B h x (G.em _ a) = add-weak k _ (λ r → h (inj₂ r)) x a
add-weak (lim f) B h x (G.em n a) = add-weak (f n) _ (λ r → h (n , r)) x a
add-weak (lc j g) B h x (G.em (η , l) a) = add-weak (g η) _ (λ r → h (η , l , r)) x a
add-weak zero B h x G.top = inj₂ (inj₁ refl)
add-weak (suc k) B h x G.top = inj₂ (h (inj₁ tt) _ (add-weak k _ (λ r → h (inj₂ r)) x G.top))
add-weak (lim f) B h x G.top = inj₂ (0 , add-weak (f 0) _ (λ r → h (0 , r)) x G.top)
add-weak (lc j g) B h x G.top = inj₂ (inj₁ refl)

add-lgl : ∀ {M} k (B : Bld M k) → DnB B → LgB B → ∀ x a → Lgl M x → Lgl k a → Lgl M (add k B x a)
add-lgl k B h b x G.zero lx la = lx
add-lgl k B h b x (G.suc a) lx la = add-lgl k B h b x a lx la
add-lgl k B h b x (G.lim f) lx (st , lf) =
  (λ n → add-cp k B h x (st n)) , (λ n → add-lgl k B h b x (f n) lx (lf n))
add-lgl k B h b x (G.lc r g) lx (lg , mo) = b r _
  ((λ η l → add-lgl k B h b x (g η) lx (lg η l)) ,
   (λ η η′ l e l′ → add-cp k B h x (mo η η′ l e l′)))
add-lgl zero B h b x (G.em () a) lx la
add-lgl (suc k) B h b x (G.em _ a) lx la =
  add-lgl k _ (λ r → h (inj₂ r)) (λ r → b (inj₂ r)) x a lx la
add-lgl (lim f) B h b x (G.em n a) lx la =
  add-lgl (f n) _ (λ r → h (n , r)) (λ r → b (n , r)) x a lx la
add-lgl (lc j g) B h b x (G.em (η , l) a) lx la =
  add-lgl (g η) _ (λ r → h (η , l , r)) (λ r → b (η , l , r)) x a lx la
add-lgl zero B h b x G.top lx la = lx
add-lgl (suc k) B h b x G.top lx la = b (inj₁ tt) _
  ((λ η l → add-lgl k _ (λ r → h (inj₂ r)) (λ r → b (inj₂ r)) x η lx l) ,
   (λ η η′ l e l′ → add-cp k _ (λ r → h (inj₂ r)) x e))
add-lgl (lim f) B h b x G.top lx la =
  (λ n → add-weak (f (suc n)) _ (λ r → h (suc n , r)) _ G.top) ,
  (λ n → acc-ind (Lgl _) _ (λ i y ly →
    add-lgl (f i) _ (λ r → h (i , r)) (λ r → b (i , r)) y G.top ly tt) x lx (suc n))
add-lgl (lc j g) B h b x G.top lx la = lx

plus-weak : ∀ m x a → Cp m x (plus m x a)
plus-weak m = add-weak m G.lc dnLc

plus-lgl : ∀ m x a → Lgl m x → Lgl m a → Lgl m (plus m x a)
plus-lgl m = add-lgl m G.lc dnLc lgLc
```

## 2 位置、派发、公共上界

`lev`, `Way`, `Ext`, `Shift` 照主线。`Lv` 多一个构造子 `vΩ`：层号 `tw 2 = lc zero ⌜_⌝`，带各支的公共上界 `V` 与字段 `up`：
第 `η + y` 支的公共上界沿 `Up` (后继、ℕ 极限的第 0 支) 走下去到第 `η` 支。`cmp` 在 `vΩ` 上一律折叠：两个位置的分支下标
是两棵可数树，它们之间没有现成的公共上界 (不要求全分支的比较)。

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

R : Set
R = Raw zero

⌜_⌝ : R → LF
⌜ η ⌝ = up zero η

data Lv : LF → Set
data Up {a} (A : Lv a) : ∀ {b} → Lv b → Set

data Lv where
  v0 : Lv zero
  vs : ∀ {k} → Lv k → Lv (suc k)
  vl : ∀ {f} → (∀ n → Lv (f n)) → (∀ n → Shift (f n) (f (suc n))) → Lv (lim f)
  vΩ : (V : ∀ η → Lgl zero η → Lv ⌜ η ⌝) →
    (∀ η l y ly → Up (V η l) (V (plus zero η y) (plus-lgl zero η y l ly))) → Lv (lc zero ⌜_⌝)

data Up {a} A where
  ur : Up A A
  us : ∀ {b} {B : Lv b} → Up A B → Up A (vs B)
  ul : ∀ {f : ℕ → LF} {B : ∀ n → Lv (f n)} {st : ∀ n → Shift (f n) (f (suc n))} →
    Up A (B 0) → Up A (vl B st)

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
cmp (vΩ V u) q r = fold
```

## 3 结点的两行与它们的合法性

照主线 [YiLeanFold](YiLeanFold.lagda.md) §2, §3 与 [YiLeanLegal](YiLeanLegal.lagda.md) §2, §3。

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

succ : ∀ m → Raw m → Raw m
succ m y = G.lim (acc (λ _ z → plus m y z) y)

psum : ∀ m → (ℕ → Raw m) → ℕ → Raw m
psum m h = acc (λ n z → plus m z (h (suc n))) (h zero)

self : ∀ k → Ext k k
self k r = keep r refl

succ-step : ∀ m y n → Cp m (acc (λ _ z → plus m y z) y n) (acc (λ _ z → plus m y z) y (suc n))
succ-step m y zero = plus-weak m y y
succ-step m y (suc n) = add-cp m G.lc dnLc y (succ-step m y n)

succ-lgl : ∀ m y → Lgl m y → Lgl m (succ m y)
succ-lgl m y ly = succ-step m y , acc-ind (Lgl m) _ (λ _ z lz → plus-lgl m y z ly lz) y ly

psum-lgl : ∀ m h → (∀ n → Lgl m (h n)) → Lgl m (G.lim (psum m h))
psum-lgl m h lh = (λ n → plus-weak m _ (h (suc n))) ,
  acc-ind (Lgl m) _ (λ n z lz → plus-lgl m z (h (suc n)) lz (lh (suc n))) (h zero) (lh zero)

nodeAt-dn : ∀ {M} m p (B : Bld M m) → DnB B → ∀ g {z} → Cp M z (g G.top) → Dn M z (nodeAt m p B g)
nodeAt-dn (suc k) (inj₁ _) B h g q = h (inj₁ tt) g q
nodeAt-dn (suc k) (inj₂ p) B h = nodeAt-dn k p _ (λ r → h (inj₂ r))
nodeAt-dn (lim f) (n , p) B h = nodeAt-dn (f n) p _ (λ r → h (n , r))
nodeAt-dn (lc j g) (η , l , p) B h = nodeAt-dn (g η) p _ (λ r → h (η , l , r))

nodeAt-lgl : ∀ {M} m p (B : Bld M m) → LgB B → ∀ g → Br (layer (lev m p)) M g → Lgl M (nodeAt m p B g)
nodeAt-lgl (suc k) (inj₁ _) B b = b (inj₁ tt)
nodeAt-lgl (suc k) (inj₂ p) B b = nodeAt-lgl k p _ (λ r → b (inj₂ r))
nodeAt-lgl (lim f) (n , p) B b = nodeAt-lgl (f n) p _ (λ r → b (n , r))
nodeAt-lgl (lc j g) (η , l , p) B b = nodeAt-lgl (g η) p _ (λ r → b (η , l , r))

chain-lgl : ∀ j gk → (∀ η → Lgl j η → Lgl j (gk η)) → ∀ n → Lgl j (chain j gk n)
chain-lgl j gk h zero = tt
chain-lgl j gk h (suc n) = plus-lgl j _ _ (chain-lgl j gk h n) (h _ (chain-lgl j gk h n))

Ψn-dn : ∀ m j (w : Way m j) gm gk {z} → Cp m z (gm G.top) → Dn m z (Ψn m j w gm gk)
Ψn-dn m .(lev m p) (keep p refl) gm gk q = nodeAt-dn m p G.lc dnLc gm q
Ψn-dn m j fold gm gk q = 0 , q

Ψn-lgl : ∀ m j (w : Way m j) gm gk → Br (layer j) m gm → (∀ η → Lgl j η → Lgl j (gk η)) →
  Lgl m (Ψn m j w gm gk)
Ψn-lgl m .(lev m p) (keep p refl) gm gk hm hk = nodeAt-lgl m p G.lc lgLc gm hm
Ψn-lgl m j fold gm gk (lg , mo) hk =
  (λ n → mo _ _ (chain-lgl j gk hk n) (plus-weak j _ _) (chain-lgl j gk hk (suc n))) ,
  (λ n → lg _ (chain-lgl j gk hk n))

ΨN-dn : ∀ m k r (w : Way m (lev k r)) gm gk {z} → Cp m z (gm (Lay.tp (Lo k r))) →
  Dn m z (ΨN m k r w gm gk)
ΨN-dn m (suc k) (inj₁ _) = Ψn-dn m k
ΨN-dn m (suc k) (inj₂ r) = ΨN-dn m k r
ΨN-dn m (lim f) (n , r) = ΨN-dn m (f n) r
ΨN-dn m (lc j g) (η , _ , r) = ΨN-dn m (g η) r

ΨN-lgl : ∀ m k r (w : Way m (lev k r)) gm gk → Br (Lo k r) m gm →
  (∀ η → Lay.lg (Lo k r) η → Lgl (lev k r) (gk η)) → Lgl m (ΨN m k r w gm gk)
ΨN-lgl m (suc k) (inj₁ _) = Ψn-lgl m k
ΨN-lgl m (suc k) (inj₂ r) = ΨN-lgl m k r
ΨN-lgl m (lim f) (n , r) = ΨN-lgl m (f n) r
ΨN-lgl m (lc j g) (η , _ , r) = ΨN-lgl m (g η) r
```

## 4 `top` 在 `tw 2` 上的两行的部件

`tw 2` 的 `top` 读成 Ω_Ω，是层号 0 的 Ω 结点 (分支 η 是第 `⌜ η ⌝` 层的 `top`)，但 `Pre (tw 2)` 里没有层号 0 的根位置；
这个结点保留与否看第 `top` 支里层号 0 的位置 `p₀` 的派发。保留时结点的分支必须对一切下标有定义并单调，
而各支的 `top` 互不为第一位置，所以分支取沿下标结构的累加 `Kf T`：后继一步加上 ω 份 `T`，`T η` 是坐标 `nrm η`
(ℕ 极限处取部分和，总是合法) 那一支的 `top` 的像。折叠时照主线 `T₃`：链点带坐标与合法性，下一点是 `η + F η`。

```agda
nrm : R → R
nrm G.zero = G.zero
nrm (G.suc a) = G.suc (nrm a)
nrm (G.lim f) = G.lim (psum zero (λ n → nrm (f n)))
nrm G.top = G.top

nrm-lgl : ∀ η → Lgl zero (nrm η)
nrm-lgl G.zero = tt
nrm-lgl (G.suc a) = nrm-lgl a
nrm-lgl (G.lim f) = psum-lgl zero _ (λ n → nrm-lgl (f n))
nrm-lgl G.top = tt

Kf : ∀ m → (R → Raw m) → R → Raw m
Kf m T G.zero = T G.zero
Kf m T (G.suc a) = G.lim (acc (λ _ z → plus m z (T (G.suc a))) (Kf m T a))
Kf m T (G.lim f) = G.lim (λ n → Kf m T (f n))
Kf m T G.top = T G.top

Kf-cp : ∀ m T {a b} → Cp zero a b → Cp m (Kf m T a) (Kf m T b)
Kf-dn : ∀ m T {a} b → Dn zero a b → Dn m (Kf m T a) (Kf m T b)
Kf-cp m T (inj₁ refl) = inj₁ refl
Kf-cp m T (inj₂ p) = inj₂ (Kf-dn m T _ p)
Kf-dn m T (G.suc b) p = 0 , Kf-cp m T p
Kf-dn m T (G.lim f) (n , p) = n , Kf-cp m T p

Kf-br : ∀ m T → (∀ η → Lgl m (T η)) → Br (layer zero) m (Kf m T)
Kf-lgl : ∀ m T → (∀ η → Lgl m (T η)) → ∀ η → Lgl zero η → Lgl m (Kf m T η)
Kf-br m T h = Kf-lgl m T h , λ η η′ l e l′ → Kf-cp m T e
Kf-lgl m T h G.zero l = h G.zero
Kf-lgl m T h (G.suc a) l = (λ n → plus-weak m _ _) ,
  acc-ind (Lgl m) _ (λ _ z lz → plus-lgl m z _ lz (h _)) _ (Kf-lgl m T h a l)
Kf-lgl m T h (G.lim f) (st , lf) = (λ n → Kf-cp m T (st n)) , (λ n → Kf-lgl m T h (f n) (lf n))
Kf-lgl m T h G.top l = h G.top

ΩT : ∀ m j → Way m j → (Raw j → Raw m) → (ℕ → Raw m) → Raw m
ΩT m .(lev m p) (keep p refl) K o = nodeAt m p G.lc K
ΩT m j fold K o = G.lim o

ΩT-lgl : ∀ m j (w : Way m j) K o → Br (layer j) m K → Lgl m (G.lim o) → Lgl m (ΩT m j w K o)
ΩT-lgl m .(lev m p) (keep p refl) K o b l = nodeAt-lgl m p G.lc lgLc K b
ΩT-lgl m j fold K o b l = l

record Pt : Set where
  constructor pt
  field
    co : R
    lw : Lgl zero co
open Pt public

nx : (F : (η : R) → Lgl zero η → R) → (∀ η l → Lgl zero (F η l)) → Pt → Pt
nx F FL (pt η l) = pt (plus zero η (F η l)) (plus-lgl zero η (F η l) l (FL η l))

pts : (F : (η : R) → Lgl zero η → R) → (∀ η l → Lgl zero (F η l)) → ℕ → Pt
pts F FL = iter (nx F FL) (pt G.top tt)
```

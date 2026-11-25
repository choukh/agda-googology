# YiRawFold 底座：结点的数据、外部派发、合法性的限制

**档位：定义与编译定理，没有折叠。** `Nd` 把一个 Ω 结点折叠时要用的数据收成记录，层号是变量；`ΨN` 对 (公共上界, 位置) 递归，
走到根位置时 `Low` 就是 `Raw`，所以下界与分支域不搬运。`Ext` 是折叠带着走的外部派发，进孩子时用复合限制。
`CohP` 是 `Legal` 沿自己的路径一致。入口 [YiRawFold](YiRawFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawFoldBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiIrrIf using (CP; self; suc; lim; fst; Legal; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt)
open import OCF.Align.YiLvIf using (Plain; lev; Kept)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase
  using (Way; keep; fold; nodeAt; node-dn; node-lgl; node-ns; node-ps; startᴸ;
         module Chain; module ChainLegal)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiLvNegRestrict using (restrictL)
open import OCF.Align.YiRawIf using (IsLim)
```

## 1 外部派发

折叠在 `Raw k` 上走，目标层 `m`。`low`：一律折叠 (目标层在 `k` 的一切位置之下或与之相等，例如第 0 层)。
`mix w`：位置 `r` 上的结点按 `w r` 办。进孩子时位置前面添一个 `inj₂` 或 `(n , _)`，层号定义性不变。

```agda
data Ext (m k : LF) : Set where
  low : Ext m k
  mix : ((r : Pre k) → Way m (lev k r)) → Ext m k

wayOf : ∀ {m k} → Ext m k → (r : Pre k) → Way m (lev k r)
wayOf low r = fold
wayOf (mix w) r = w r

inS : ∀ {m k} → Ext m (suc k) → Ext m k
inS low = low
inS (mix w) = mix (λ r → w (inj₂ r))

inL : ∀ {m f} → Ext m (lim f) → ∀ n → Ext m (f n)
inL low n = low
inL (mix w) n = mix (λ r → w (n , r))
```

## 2 结点的数据

`A`, `Gd′`, `Lg′`, `Ns′` 是下界所在的类型与它上面的守卫、合法性、嵌套证据。取 `Raw k`, `Gd k`, … 是 `NdR`；
取 `Low K r`, `GdL K r`, … 是 `NdL`。在根位置这两个记录类型定义性相等。
`t`, `gm` 是折到目标层 `m` 的第一支与分支；`gk` 是折到结点自己那一层的分支，链用它推进。

```agda
record Nd (m k : LF) (A : Set) (Gd′ : A → A → Set) (Lg′ Ns′ : A → Set) : Set where
  constructor nd
  field
    c : A
    .lw : Lg′ c
    .nw : Ns′ c
    t : Raw m
    gm : (η : A) → .(Gd′ c η) → Raw m
    gk : (η : A) → .(Gd′ c η) → Raw k
    .lk : ∀ η (e : Gd′ c η) → Lgl k (gk η e)
    .nk : ∀ η (e : Gd′ c η) → Nested k (gk η e)
    pk : ∀ η .(e : Gd′ c η) → Pos k (gk η e)

NdR : LF → LF → Set
NdR m k = Nd m k (Raw k) (Gd k) (Lgl k) (Nested k)

NdL : ∀ m k → Pre k → Set
NdL m k r = Nd m (lev k r) (Low k r) (GdL k r) (LglLow k r) (NestedLow k r)

-- 证明用的相关数据. seed 是下界自身的守卫.
record NdLgl {m k A Gd′ Lg′ Ns′} (N : Nd m k A Gd′ Lg′ Ns′) : Set where
  open Nd N using (c; t; gm; gk)
  field
    seed : Gd′ c c
    tg : ∀ η (e : Gd′ c η) → Cp m t (gm η e)
    dir : ∀ η (e : Gd′ c η) η′ (e′ : Gd′ c η′) → Gd′ η η′ → Cp m (gm η e) (gm η′ e′)
    lt : Lgl m t
    lg : ∀ η (e : Gd′ c η) → Lgl m (gm η e)
    lkʳ : ∀ η (e : Gd′ c η) → Lgl k (gk η e)
    nkʳ : ∀ η (e : Gd′ c η) → Nested k (gk η e)

record NdNs {m k A Gd′ Lg′ Ns′} (N : Nd m k A Gd′ Lg′ Ns′) : Set where
  open Nd N using (c; t; gm; gk)
  field
    seed : Gd′ c c
    lcʳ : Lg′ c
    ncʳ : Ns′ c
    nt : Nested m t
    ng : ∀ η (e : Gd′ c η) → Nested m (gm η e)
    lkʳ : ∀ η (e : Gd′ c η) → Lgl k (gk η e)
    nkʳ : ∀ η (e : Gd′ c η) → Nested k (gk η e)

seedL : ∀ k r c → LglLow k r c → NestedLow k r c → GdL k r c c
seedL (suc k) (inj₁ _) c l n = inj₁ refl , l , n
seedL (suc k) (inj₂ r) c l n = seedL k r c l n
seedL (lim f) (n′ , r) c l n = seedL (f n′) r c l n
seedL (lc k c₀ w b t g) (inj₁ (inj₁ _)) c l n = inj₁ refl , l , n
seedL (lc k c₀ w b t g) (inj₁ (inj₂ r)) c l n = seedL k r c l n
seedL (lc k c₀ w b t g) (inj₂ (inj₁ r)) c l n = seedL t r c l n
seedL (lc k c₀ w b t g) (inj₂ (inj₂ (η , e , r))) c l n = seedL (g η e) r c l n
```

## 3 结点处的两行

层号 `k` 是变量，所以 `keep s refl` 之后下界就在 `Raw (lev m s)` 里。保留：按槽位造结点。折叠：链在 `Raw k` 里由 `gk` 推进，观察 `gm`。

```agda
Ψn : ∀ m k → .(Plain k) → Way m k → NdR m k → Raw m
Ψn m .(lev m s) pl (keep s refl) (nd c lw nw t gm gk lk nk pk) =
  nodeAt m s (rawAlg m) c t gm
Ψn m k pl fold (nd c lw nw t gm gk lk nk pk) =
  Chain.collapse k pl c gk lk nk pk m gm (startᴸ k c lw nw)

ΨN : ∀ m k → Plain k → (r : Pre k) → Way m (lev k r) → NdL m k r → Raw m
ΨN m (suc k) pl (inj₁ _) y N = Ψn m k pl y N
ΨN m (suc k) pl (inj₂ r) y N = ΨN m k pl r y N
ΨN m (lim f) pl (n , r) y N = ΨN m (f n) (pl n) r y N
```

引理各两条：`Ψn` 上按派发分情况，`ΨN` 上照定义的三个子句传下去。

```agda
Ψn-pos : ∀ m k .(pl : Plain k) (y : Way m k) (N : NdR m k) → Pos m (Ψn m k pl y N)
Ψn-pos m .(lev m s) pl (keep s refl) (nd c lw nw t gm gk lk nk pk) =
  node-ps m s (rawAlg m) c t gm
Ψn-pos m k pl fold (nd c lw nw t gm gk lk nk pk) = tt

ΨN-pos : ∀ m k (pl : Plain k) r (y : Way m (lev k r)) (N : NdL m k r) →
  Pos m (ΨN m k pl r y N)
ΨN-pos m (suc k) pl (inj₁ _) y N = Ψn-pos m k pl y N
ΨN-pos m (suc k) pl (inj₂ r) y N = ΨN-pos m k pl r y N
ΨN-pos m (lim f) pl (n , r) y N = ΨN-pos m (f n) (pl n) r y N

Ψn-legal : ∀ m k (pl : Plain k) (y : Way m k) (N : NdR m k) → NdLgl N →
  Lgl m (Ψn m k pl y N)
Ψn-legal m .(lev m s) pl (keep s refl) (nd c lw nw t gm gk lk nk pk) H =
  node-lgl m s (rawAlg m) c t gm (NdLgl.tg H) (NdLgl.dir H) (NdLgl.lt H) (NdLgl.lg H)
Ψn-legal m k pl fold (nd c lw nw t gm gk lk nk pk) H =
  ChainLegal.collapse-legal k pl c gk (NdLgl.lkʳ H) (NdLgl.nkʳ H) pk
    (startᴸ k c lw nw) (NdLgl.seed H) m gm (NdLgl.lg H) (NdLgl.dir H)

ΨN-legal : ∀ m k (pl : Plain k) r (y : Way m (lev k r)) (N : NdL m k r) → NdLgl N →
  Lgl m (ΨN m k pl r y N)
ΨN-legal m (suc k) pl (inj₁ _) y N H = Ψn-legal m k pl y N H
ΨN-legal m (suc k) pl (inj₂ r) y N H = ΨN-legal m k pl r y N H
ΨN-legal m (lim f) pl (n , r) y N H = ΨN-legal m (f n) (pl n) r y N H

Ψn-nested : ∀ m k (pl : Plain k) (y : Way m k) (N : NdR m k) → NdNs N →
  Nested m (Ψn m k pl y N)
Ψn-nested m .(lev m s) pl (keep s refl) (nd c lw nw t gm gk lk nk pk) H =
  node-ns m s (rawAlg m) c t gm (NdNs.lcʳ H) (NdNs.ncʳ H) (NdNs.nt H) (NdNs.ng H)
Ψn-nested m k pl fold (nd c lw nw t gm gk lk nk pk) H =
  ChainLegal.collapse-nested k pl c gk (NdNs.lkʳ H) (NdNs.nkʳ H) pk
    (startᴸ k c lw nw) (NdNs.seed H) m gm (NdNs.ng H)

ΨN-nested : ∀ m k (pl : Plain k) r (y : Way m (lev k r)) (N : NdL m k r) → NdNs N →
  Nested m (ΨN m k pl r y N)
ΨN-nested m (suc k) pl (inj₁ _) y N H = Ψn-nested m k pl y N H
ΨN-nested m (suc k) pl (inj₂ r) y N H = ΨN-nested m k pl r y N H
ΨN-nested m (lim f) pl (n , r) y N H = ΨN-nested m (f n) (pl n) r y N H

-- 第一位置: 保留时经第一支, 折叠时经下界自身那一支 (链的第 0 项).
Ψn-dn : ∀ m k .(pl : Plain k) (y : Way m k) (N : NdR m k) {X : Raw m} →
  Cp m X (Nd.t N) → (e₀ : Gd k (Nd.c N) (Nd.c N)) → Cp m X (Nd.gm N (Nd.c N) e₀) →
  Dn m X (Ψn m k pl y N)
Ψn-dn m .(lev m s) pl (keep s refl) (nd c lw nw t gm gk lk nk pk) p e₀ q =
  node-dn m s (rawAlg m) c t gm p
Ψn-dn m k pl fold (nd c lw nw t gm gk lk nk pk) p e₀ q = zero , q

ΨN-dn : ∀ m k (pl : Plain k) r (y : Way m (lev k r)) (N : NdL m k r) {X : Raw m} →
  Cp m X (Nd.t N) → (e₀ : GdL k r (Nd.c N) (Nd.c N)) → Cp m X (Nd.gm N (Nd.c N) e₀) →
  Dn m X (ΨN m k pl r y N)
ΨN-dn m (suc k) pl (inj₁ _) y N p e₀ q = Ψn-dn m k pl y N p e₀ q
ΨN-dn m (suc k) pl (inj₂ r) y N p e₀ q = ΨN-dn m k pl r y N p e₀ q
ΨN-dn m (lim f) pl (n , r) y N p e₀ q = ΨN-dn m (f n) (pl n) r y N p e₀ q
```

## 4 携带强度的两条：保留时输出是结点，否则是 ℕ 极限

```agda
KeptA : ∀ {m} (A : Alg m) → LF → Alg.T A → Set
KeptA {m} A k y =
  Σ (Pre m) λ r → (lev m r ≡ k) ×
  Σ (Low m r) λ c → Σ (Alg.T A) λ t →
  Σ ((η : Low m r) → .(GdL m r c η) → Alg.T A) λ g → y ≡ Alg.nT A r c t g

nodeAt-kept : ∀ m → Plain m → ∀ s (A : Alg m) c t g → KeptA A (lev m s) (nodeAt m s A c t g)
nodeAt-kept (suc k) pm (inj₁ _) A c t g = inj₁ tt , refl , c , t , g , refl
nodeAt-kept (suc k) pm (inj₂ r) A c t g with nodeAt-kept k pm r (shS A) c t g
... | r′ , e , c′ , t′ , g′ , q = inj₂ r′ , e , c′ , t′ , g′ , q
nodeAt-kept (lim f) pm (n , r) A c t g with nodeAt-kept (f n) (pm n) r (shL A n) c t g
... | r′ , e , c′ , t′ , g′ , q = (n , r′) , e , c′ , t′ , g′ , q

Ψn-kept : ∀ m → Plain m → ∀ k .(pl : Plain k) (y : Way m k) (N : NdR m k) →
  IsKeep y → Kept m k (Ψn m k pl y N)
Ψn-kept m pm .(lev m s) pl (keep s refl) (nd c lw nw t gm gk lk nk pk) h =
  nodeAt-kept m pm s (rawAlg m) c t gm

ΨN-kept : ∀ m → Plain m → ∀ k (pl : Plain k) r (y : Way m (lev k r)) (N : NdL m k r) →
  IsKeep y → Kept m (lev k r) (ΨN m k pl r y N)
ΨN-kept m pm (suc k) pl (inj₁ _) y N h = Ψn-kept m pm k pl y N h
ΨN-kept m pm (suc k) pl (inj₂ r) y N h = ΨN-kept m pm k pl r y N h
ΨN-kept m pm (lim f) pl (n , r) y N h = ΨN-kept m pm (f n) (pl n) r y N h

Ψn-lim : ∀ m k .(pl : Plain k) (y : Way m k) (N : NdR m k) →
  (IsKeep y → ⊥) → IsLim (Ψn m k pl y N)
Ψn-lim m .(lev m s) pl (keep s refl) N h = ⊥-elim (h tt)
Ψn-lim m k pl fold (nd c lw nw t gm gk lk nk pk) h = tt

ΨN-lim : ∀ m k (pl : Plain k) r (y : Way m (lev k r)) (N : NdL m k r) →
  (IsKeep y → ⊥) → IsLim (ΨN m k pl r y N)
ΨN-lim m (suc k) pl (inj₁ _) y N h = Ψn-lim m k pl y N h
ΨN-lim m (suc k) pl (inj₂ r) y N h = ΨN-lim m k pl r y N h
ΨN-lim m (lim f) pl (n , r) y N h = ΨN-lim m (f n) (pl n) r y N h
```

## 5 部分和

极限层号上 `top` 在 `mix` 之下取各支折叠的部分和，理由与 `YiLvFoldAdd.add` 在 `x + top` 处相同：
保留结点的槽位取自位置，同一个层号在不同分支里是不同的位置。`self` 派发在 ω 上各支排成的极限不合法 (`YiRawFoldNoLim.side-lim-illegal`)；
规范槽位的派发下各支的输出是否互为第一位置没有证 (要派发沿路径的限制作为函数相等)。

```agda
psum : ∀ m → (ℕ → Raw m) → ℕ → Raw m
psum m g zero = g zero
psum m g (suc n) = plus m (psum m g n) (g (suc n))

psum-step : ∀ m g n → Cp m (psum m g n) (psum m g (suc n))
psum-step m g n = add-weak m (rawAlg m) (psum m g n) (g (suc n))

psum-legal : ∀ m → Plain m → ∀ g → (∀ n → Lgl m (g n)) → ∀ n → Lgl m (psum m g n)
psum-legal m pm g lg zero = lg zero
psum-legal m pm g lg (suc n) =
  add-lgl m pm (rawAlg m) (psum m g n) (g (suc n)) (psum-legal m pm g lg n) (lg (suc n))

psum-nested : ∀ m g → (∀ n → Nested m (g n)) → ∀ n → Nested m (psum m g n)
psum-nested m g ng zero = ng zero
psum-nested m g ng (suc n) =
  add-ns m (rawAlg m) (psum m g n) (g (suc n)) (psum-nested m g ng n) (ng (suc n))
```

## 6 合法性沿路径的限制与一致

`CohP K pl L`：极限处第 `n+1` 支的 (`Plain`, `Legal`) 沿第 `n` 步限制下来等于第 `n` 支的；各支遗传。是逐项的相等。
`Plain` 也在里面：比较把它当数据传，含极限的层号上两份 `Plain` 的相等不用函数外延证不出。

```agda
plainR : ∀ {a} b → CP a b → Plain b → Plain a
plainR b self pl = pl
plainR (suc b) (suc p) pl = plainR b p pl
plainR (lim f) (lim n p) pl = plainR (f n) p (pl n)

CohP : ∀ K → Plain K → Legal K → Set
CohP zero pl L = ⊤
CohP (suc k) pl L = CohP k pl L
CohP (lim f) pl (st , lg) =
  (∀ n → _≡_ {A = Plain (f n) × Legal (f n)}
     (plainR (f (suc n)) (st n) (pl (suc n)) , restrictL (f (suc n)) (st n) (lg (suc n)))
     (pl n , lg n)) ×
  (∀ n → CohP (f n) (pl n) (lg n))
CohP (lc k c w b t g) pl L = ⊥

Good : ∀ {m} k → Plain k → Legal k → Ext m k → Set
Good k pl L low = CohP k pl L
Good k pl L (mix w) = ⊤

good-S : ∀ {m} k pl L (x : Ext m (suc k)) → Good (suc k) pl L x → Good k pl L (inS x)
good-S k pl L low h = h
good-S k pl L (mix w) h = tt

good-L : ∀ {m} f pl L (x : Ext m (lim f)) → Good (lim f) pl L x →
  ∀ n → Good (f n) (pl n) (proj₂ L n) (inL x n)
good-L f pl L low h n = proj₂ h n
good-L f pl L (mix w) h n = tt
```

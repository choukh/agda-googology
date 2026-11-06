# 和形式, 层取可变位数 (一): 定义

> 不含记号. 入口 [SumVar](SumVar.lagda.md). 由 [SumClimbTree](SumClimbTree.lagda.md) 改写. **差别只在层: 层是一个有限列表** `a₀ ∷ a₁ ∷ … ∷ aₙ₋₁` (低位在前), 读作 $\Omega_{\Omega^{n-1}a_{n-1}+\dots+\Omega a_1+a_0}$, 位数不固定; 列表末尾补零不改读法 (`EqP`). 顶层的节点各位都在世界之下, 读作 $\Omega_{\Omega^\omega}$.
>
> **停机怎么过.** 三位时分支类型 `D r p a` 三个参数分开写, 停机检查看得见字典序. 位数可变时看不见, 所以分两步:
>
> 1. `D′ L ac`: 对层的**可达性证明** `ac : AccY (lay L)` 结构递归定义; 节点的分支类型是 `D′ L′ (f x)`, `f x` 是 `ac = acc f` 里取出的那一份.
> 2. `D L`: 规范的那一个, 分支类型取 `accY L` 里的那一份. 类型依赖证明, 所以有**换证明的搬运** `fw`, `bw` (对第一个证明结构递归, 第二个随之下降) 与 `toD`, `ofD`; 它们就是 `outV`, `inV`. 三位时 `outV`, `inV` 是沿 `◁` 的浅搬运, 这里是对整棵树的深搬运.
>
> 节点种类 `KL W L L′` 只有三个构造子, **对一切位数一个定义**: `hd` (这一位严格低, 以上补零相等), `tl` (更高位已经低了, 这一位只要在世界之下), `tz` (节点是空列表, 层非零). 合法性仍只有 §3 讲和的 `sum-fst`, `Lg-sum`, 无前提. **没有 `HS`, `Goodᴺ`, `WF`, `ψW`.**
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumVarTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲; cmpF)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLOpsW using (_◁_; ◁-tr; ◁⊲; ⊲◁; ◁∘⊲)
import OCF.Align.TLOpsW as H
open import OCF.Align.SumHtTree using (NZ; NZ◁; tailP; ⊲-idl; ⊲-as) public
```

## §1 树

同 `SumClimbTree`, 节点的层是列表.

```agda
Lay : Set
Lay = List A

module _ (Kd : A → Lay → Set) (V : ∀ {W L} → Kd W L → A → Set) (Zz : Set) where
  infixl 6 _⨾_
  data D₊ : A → Set where
    n0  : ∀ {W} → D₊ W
    n1  : ∀ {W} → D₊ W
    _⨾_ : ∀ {W} → D₊ W → D₊ W → D₊ W
    nl  : ∀ {W} → (ℕ → D₊ W) → D₊ W
    ni  : ∀ {W L} (r : Kd W L) → (∀ {W′} → W ⊲ W′ → Lg W′ → V r W′ → D₊ W′) → D₊ W
    nκ  : ∀ {W} → Zz → (∀ {c} → W ⊲ c → Lg c → D₊ c) → D₊ W
    nw  : ∀ {W₀ W} → W₀ ⊲ W → D₊ W₀ → D₊ W
```

## §2 层与节点种类

`Zs L`: 各位为零. `EqP L L′`: 末尾补零后相等. `NZL L`: 有一位非零 (字面的非零, 即构造子不是 `azero`).

```agda
data Zs : Lay → Set where
  z[] : Zs []
  z∷  : ∀ {L} → Zs L → Zs (azero ∷ L)

data EqP : Lay → Lay → Set where
  zl : ∀ {L} → Zs L → EqP [] L
  zr : ∀ {L} → Zs L → EqP L []
  cs : ∀ {a L L′} → EqP L L′ → EqP (a ∷ L) (a ∷ L′)

NZL : Lay → Set
NZL [] = ⊥
NZL (a ∷ L) = NZ a ⊎ NZL L

AllB : Lay → A → Set
AllB [] W = ⊤
AllB (a ∷ L) W = (a ⊲ W) × AllB L W
```

**节点种类.** `KL W L L′`: 层 $L$ 里, 世界 $W$ 上, 可以有层 $L′$ 的节点. 从最高的不同位往下读: 那一位严格低 (`hd`), 更低的位只要在世界之下 (`tl`). 一个定义对一切位数.

```agda
data KL (W : A) : Lay → Lay → Set where
  hd : ∀ {p h L L′} → EqP L L′ → h ◁ p → KL W (p ∷ L) (h ∷ L′)
  tl : ∀ {p h L L′} → KL W L L′ → h ⊲ W → KL W (p ∷ L) (h ∷ L′)
  tz : ∀ {L} → NZL L → KL W L []
```

### 补零相等的小算律

```agda
eqr : ∀ L → EqP L L
eqr [] = zl z[]
eqr (a ∷ L) = cs (eqr L)

zsE : ∀ {L L′} → Zs L → EqP L L′ → Zs L′
zsE z (zl z′) = z′
zsE z (zr _) = z[]
zsE (z∷ z) (cs e) = z∷ (zsE z e)

zsE′ : ∀ {L L′} → Zs L′ → EqP L L′ → Zs L
zsE′ z (zl _) = z[]
zsE′ z (zr z′) = z′
zsE′ (z∷ z) (cs e) = z∷ (zsE′ z e)

zzE : ∀ {L L′} → Zs L → Zs L′ → EqP L L′
zzE z[] z′ = zl z′
zzE (z∷ z) z[] = zr (z∷ z)
zzE (z∷ z) (z∷ z′) = cs (zzE z z′)

eqtr : ∀ {L₁ L₂ L₃} → EqP L₁ L₂ → EqP L₂ L₃ → EqP L₁ L₃
eqtr (zl z) e = zl (zsE z e)
eqtr (zr z) e = zzE z (zsE z[] e)
eqtr (cs e) (zr (z∷ z)) = zr (z∷ (zsE′ z e))
eqtr (cs e) (cs e′) = cs (eqtr e e′)

zsNZ : ∀ {L} → Zs L → NZL L → ⊥
zsNZ (z∷ z) (inj₁ ())
zsNZ (z∷ z) (inj₂ y) = zsNZ z y

nzE : ∀ {L L₁} → EqP L L₁ → NZL L₁ → NZL L
nzE (zl z) nz with zsNZ z nz
... | ()
nzE (cs e) (inj₁ x) = inj₁ x
nzE (cs e) (inj₂ y) = inj₂ (nzE e y)

nzR0 : ∀ {p L} → NZL (azero ∷ L) → NZL (p ∷ L)
nzR0 (inj₂ y) = inj₂ y

zdec : ∀ L → Zs L ⊎ NZL L
zdec [] = inj₁ z[]
zdec (azero ∷ L) with zdec L
... | inj₁ z = inj₁ (z∷ z)
... | inj₂ nz = inj₂ (inj₂ nz)
zdec (asuc a ∷ L) = inj₂ (inj₁ tt)
zdec (alim f ∷ L) = inj₂ (inj₁ tt)

zsAll : ∀ {L W} → Zs L → AllB L W
zsAll z[] = tt
zsAll {W = W} (z∷ z) = z⊲ W , zsAll z

eqAll : ∀ {L L′ W} → EqP L L′ → AllB L W → AllB L′ W
eqAll (zl z) _ = zsAll z
eqAll (zr z) _ = tt
eqAll (cs e) (aW , LW) = aW , eqAll e LW

hk↑ : ∀ {L W W′} → AllB L W → W ⊲ W′ → AllB L W′
hk↑ {L = []} _ q = tt
hk↑ {L = a ∷ L} (aW , LW) q = ⊲-tr aW q , hk↑ LW q
```

### 节点种类的算律

```agda
nzK : ∀ {W L L′} → KL W L L′ → NZL L
nzK (hd e i) = inj₁ (NZ◁ i)
nzK (tl t f) = inj₂ (nzK t)
nzK (tz nz) = nz

kzs : ∀ {W L L′} → Zs L → KL W L L′ → ⊥
kzs (z∷ z) (hd e ())
kzs (z∷ z) (tl t f) = kzs z t
kzs z (tz nz) = zsNZ z nz

z◁ : ∀ {p} → NZ p → azero ◁ p
z◁ {asuc a} _ with ⊲◁ (z⊲ (asuc a))
... | inj₁ ()
... | inj₂ i = i
z◁ {alim f} _ with ⊲◁ (z⊲ (alim f))
... | inj₁ ()
... | inj₂ i = i

-- 层非零, 节点各位为零: 节点在层之下
kzz : ∀ {W L L₂} → NZL L → Zs L₂ → KL W L L₂
kzz nz z[] = tz nz
kzz {W} {p ∷ T} nz (z∷ z₂) with zdec T
kzz {W} {p ∷ T} (inj₁ np) (z∷ z₂) | inj₁ zT = hd (zzE zT z₂) (z◁ np)
kzz {W} {p ∷ T} (inj₂ nT) (z∷ z₂) | inj₁ zT with zsNZ zT nT
... | ()
kzz {W} {p ∷ T} nz (z∷ z₂) | inj₂ nT = tl (kzz nT z₂) (z⊲ W)

-- 层换成补零相等的
congL : ∀ {W L L₁ L₂} → EqP L L₁ → KL W L₁ L₂ → KL W L L₂
congL (zl (z∷ z)) (hd e ())
congL (zl (z∷ z)) (tl t f) with kzs z t
... | ()
congL (zr z) (tz nz) = tz (nzE (zr z) nz)
congL (zl z) (tz nz) with zsNZ z nz
... | ()
congL (cs e) (hd e′ i) = hd (eqtr e e′) i
congL (cs e) (tl t f) = tl (congL e t) f
congL (cs e) (tz nz) = tz (nzE (cs e) nz)

-- 节点换成补零相等的
congR : ∀ {W L L₁ L₂} → KL W L L₁ → EqP L₁ L₂ → KL W L L₂
congR (hd e i) (zr (z∷ z)) = tz (inj₁ (NZ◁ i))
congR (hd e i) (cs e′) = hd (eqtr e e′) i
congR (tl t f) (zr (z∷ z)) = tz (inj₂ (nzK t))
congR (tl t f) (cs e′) = tl (congR t e′) f
congR (tz nz) (zl z) = kzz nz z
congR (tz nz) (zr z) = tz nz

-- 世界的界从节点的各位重新取
rebound : ∀ {W₀ W₁ L L₁} → KL W₀ L L₁ → AllB L₁ W₁ → KL W₁ L L₁
rebound (hd e i) _ = hd e i
rebound (tl t f) (hW , TW) = tl (rebound t TW) hW
rebound (tz nz) _ = tz nz

kkL : ∀ {W₀ W L L′} → KL W₀ L L′ → W₀ ⊲ W → AllB L W → AllB L′ W
kkL (hd e i) q (pW , TW) = ⊲-tr (◁⊲ i) pW , eqAll e TW
kkL (tl t f) q (pW , TW) = ⊲-tr f q , kkL t q TW
kkL (tz _) q _ = tt

KLup : ∀ {W W′ L L′} → W ⊲ W′ → KL W L L′ → KL W′ L L′
KLup q (hd e i) = hd e i
KLup q (tl t f) = tl (KLup q t) (⊲-tr f q)
KLup q (tz nz) = tz nz

-- 传递: 层 L 的节点 L₁ 里的节点 L₂ 是层 L 的节点
ktr : ∀ {W₀ W₁ L L₁ L₂} → KL W₀ L L₁ → AllB L₁ W₁ → KL W₁ L₁ L₂ → KL W₁ L L₂
ktr (hd e i) hk (hd e′ i′) = hd (eqtr e e′) (◁-tr i′ i)
ktr (hd e i) hk (tl t′ f′) = tl (congL e t′) f′
ktr (hd e i) hk (tz nz) = tz (inj₁ (NZ◁ i))
ktr (tl t f) (hW , TW) (hd e′ i′) = tl (congR (rebound t TW) e′) (⊲-tr (◁⊲ i′) hW)
ktr (tl t f) (hW , TW) (tl t′ f′) = tl (ktr t TW t′) f′
ktr (tl t f) hk (tz nz) = tz (inj₂ (nzK t))
ktr (tz nz) hk (tz ())

-- 第 0 位为零的层的节点, 换到第 0 位任意的层 (第 0 位没有可低的)
rehd : ∀ {W p L L′} → KL W (azero ∷ L) L′ → KL W (p ∷ L) L′
rehd (hd e ())
rehd (tl t f) = tl t f
rehd (tz nz) = tz (nzR0 nz)
```

### 层的良基

`AccY`: 节点种类的可达性, 同 `SumClimbTree`. 证明对列表结构递归, 每个列表里对首位结构递归; 补零相等的层可达性相同 (`accE`). 没有字典序的停机问题: 这里递归的是**证明**, 下降在 `acc f` 到 `f t` 上.

```agda
data Ly : Set where
  lay : Lay → Ly
  top : Ly

K : Ly → A → Lay → Set
K (lay L) W L′ = KL W L L′
K top W L′ = AllB L′ W

data AccY (ly : Ly) : Set where
  acc : (∀ {W L′} → K ly W L′ → AccY (lay L′)) → AccY ly

acc[] : AccY (lay [])
acc[] = acc (λ { (tz ()) })

accE : ∀ {L L′} → EqP L L′ → AccY (lay L) → AccY (lay L′)
accE e (acc f) = acc (λ x → f (congL e x))

accC : ∀ {L} → AccY (lay L) → ∀ a → AccY (lay (a ∷ L))
accK : ∀ {L} → AccY (lay L) → ∀ a {W N} → KL W (a ∷ L) N → AccY (lay N)
accS : ∀ {L} → AccY (lay L) → ∀ a {h} → h ◁ a → AccY (lay (h ∷ L))
accC ac a = acc (accK ac a)
accK ac a (hd e i) = accE (cs e) (accS ac a i)
accK (acc f) a (tl t _) = accC (f t) _
accK ac a (tz _) = acc[]
accS ac (asuc b) H.zero = accC ac b
accS ac (asuc b) (H.suc i) = accS ac b i
accS ac (alim g) (H.self n) = accC ac (g n)
accS ac (alim g) (H.lim n i) = accS ac (g n) i

accY : ∀ L → AccY (lay L)
accY [] = acc[]
accY (a ∷ L) = accC (accY L) a

accTop : AccY top
accTop = acc (λ {_} {L} _ → accY L)

subA : ∀ {ly W L′} → AccY ly → K ly W L′ → AccY (lay L′)
subA (acc f) x = f x
```

### 分支类型: 对可达性证明递归

```agda
D′ : (L : Lay) → AccY (lay L) → A → Set
D′ L (acc f) = D₊ (λ W L′ → KL W L L′) (λ {W} {L′} x W′ → D′ L′ (f x) W′) (NZL L)

VL : ∀ L {W L′} → KL W L L′ → A → Set
VL L {L′ = L′} x W′ = D′ L′ (subA (accY L) x) W′

D : Lay → A → Set
D L = D₊ (λ W L′ → KL W L L′) (VL L) (NZL L)
```

**换证明的搬运.** 同一层的两份可达性证明给两个类型, 它们之间来回搬. `mapD`: 只换分支的定义域, 对树结构递归; `fw`, `bw` 对证明结构递归 (`acc f` 到 `f x`).

```agda
mapD : ∀ {Kd : A → Lay → Set} {V₁ V₂ : ∀ {W L} → Kd W L → A → Set} {Z : Set} →
       (∀ {W L W′} (x : Kd W L) → V₂ x W′ → V₁ x W′) → ∀ {W} → D₊ Kd V₁ Z W → D₊ Kd V₂ Z W
mapD c n0 = n0
mapD c n1 = n1
mapD c (x ⨾ y) = mapD c x ⨾ mapD c y
mapD c (nl d) = nl (λ n → mapD c (d n))
mapD c (ni x u) = ni x (λ p l y → mapD c (u p l (c x y)))
mapD c (nκ z v) = nκ z (λ p l → mapD c (v p l))
mapD c (nw p x) = nw p (mapD c x)

fw : ∀ {L} (a b : AccY (lay L)) {W} → D′ L a W → D′ L b W
bw : ∀ {L} (a b : AccY (lay L)) {W} → D′ L b W → D′ L a W
fw (acc f) (acc g) = mapD (λ x y → bw (f x) (g x) y)
bw (acc f) (acc g) = mapD (λ x y → fw (f x) (g x) y)

toD : ∀ {L} (a : AccY (lay L)) {W} → D′ L a W → D L W
toD {L} (acc f) = mapD (λ x y → bw (f x) (subA (accY L) x) y)

ofD : ∀ {L} (a : AccY (lay L)) {W} → D L W → D′ L a W
ofD {L} (acc f) = mapD (λ x y → fw (f x) (subA (accY L) x) y)
```

### 顶层与一般的层

```agda
V : ∀ ly {W L′} → K ly W L′ → A → Set
V (lay L) x = VL L x
V top {L′ = L′} x W′ = D L′ W′

Zy : Ly → Set
Zy (lay L) = NZL L
Zy top = ⊤

Dl : Ly → A → Set
Dl ly = D₊ (K ly) (V ly) (Zy ly)

D̂ : A → Set
D̂ = Dl top

outV : ∀ ly {W L′ W′} (x : K ly W L′) → V ly x W′ → D L′ W′
outV (lay L) x y = toD (subA (accY L) x) y
outV top x y = y

inV : ∀ ly {W L′ W′} (x : K ly W L′) → D L′ W′ → V ly x W′
inV (lay L) x z = ofD (subA (accY L) x) z
inV top x z = z

LW : Ly → A → Set
LW (lay L) W = AllB L W
LW top W = ⊤

LW↑ : ∀ ly {W W′} → W ⊲ W′ → LW ly W → LW ly W′
LW↑ (lay L) q l = hk↑ l q
LW↑ top q l = tt

kk : ∀ ly {W₀ W L′} → K ly W₀ L′ → W₀ ⊲ W → LW ly W → AllB L′ W
kk (lay L) x q l = kkL x q l
kk top x q l = hk↑ x q

Kup : ∀ ly {W W′ L′} → W ⊲ W′ → K ly W L′ → K ly W′ L′
Kup (lay L) q x = KLup q x
Kup top q x = hk↑ x q

mkOf : ∀ ly {W₀ L′} → K ly W₀ L′ → ∀ {W₁ L″} → AllB L′ W₁ → KL W₁ L′ L″ → K ly W₁ L″
mkOf (lay L) x hk y = ktr x hk y
mkOf top x hk y = kkL y C.self hk

zyOf : ∀ ly {W L′} → K ly W L′ → Zy ly
zyOf (lay L) x = nzK x
zyOf top x = tt
```

## §3 第 0 层的树给层

层 `[]` 没有节点, 也没有 `nκ`. **合法性证明只有这一节.** 目标的各位为零时 (`Zs`), 第 0 层的树原样搬过去 (`drpZ`).

```agda
D₀ : A → Set
D₀ = D []

drp : ∀ {W W′} → D₀ W → D₀ W′
drp n0 = n0
drp n1 = n1
drp (x ⨾ y) = drp x ⨾ drp y
drp (nl d) = nl (λ n → drp (d n))
drp (ni (tz ()) u)
drp (nκ () u)
drp (nw p x) = drp x

drpZ : ∀ {L W W′} → Zs L → D₀ W → D L W′
drpZ z n0 = n0
drpZ z n1 = n1
drpZ z (x ⨾ y) = drpZ z x ⨾ drpZ z y
drpZ z (nl d) = nl (λ n → drpZ z (d n))
drpZ z (ni (tz ()) u)
drpZ z (nκ () u)
drpZ z (nw p x) = drpZ z x

pt  : ∀ {W} → A → (ℕ → D₀ W) → ℕ → A
sum : ∀ {W} → A → D₀ W → A
pt b d zero = b
pt b d (suc n) = sum (pt b d n) (d n)
sum b n0 = b
sum b n1 = asuc b
sum b (x ⨾ y) = sum (sum b x) y
sum b (nl d) = alim (pt b d)
sum b (ni (tz ()) u)
sum b (nκ () u)
sum b (nw p x) = sum b x

sum-fst : ∀ {W} b (x : D₀ W) → b ⊲ sum b x
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni (tz ()) u)
sum-fst b (nκ () u)
sum-fst b (nw p x) = sum-fst b x

Lg-sum : ∀ {W} b (x : D₀ W) → Lg b → Lg (sum b x)
Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → Lg b → Lg (pt b d n)
Lg-sum b n0 w = w
Lg-sum b n1 w = w
Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
Lg-sum b (ni (tz ()) u) w
Lg-sum b (nκ () u) w
Lg-sum b (nw p x) w = Lg-sum b x w
Lg-pt b d zero w = w
Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)
```

## §4 $\Omega$

$\Omega_L=1$ 接上从最高位到第 0 位的各段差, 对一切位数一个定义. 第 0 位的一步: 同层节点 (`DifI`). 第 $j\ge1$ 位的一步 $c\to c+1$: $\sum_{d\ge0}\sum_{z}1$, 节点的第 $j$ 位是 $c$, 第 $j-1$ 位是 $d$, 更低的位是 $0$, 更高的位照抄 (`Up`, 与三位时的 `stepH`, `stepR` 同形). `Up` 对列表递归, 节点种类由 `wk` 一层层包上 `tl _ 0`.

```agda
AllLg : Lay → Set
AllLg [] = ⊤
AllLg (a ∷ L) = Lg a × AllLg L

allLg : ∀ {L m} → AllB L m → Lg m → AllLg L
allLg {L = []} _ _ = tt
allLg {L = a ∷ L} (am , Lm) lm = lg⊲ am lm , allLg Lm lm

DifI : ∀ {L} b {a W Q} → a ⊲ b → b ⊲ Q → Lg b → D (Q ∷ L) W
DifI b C.self e w = n0
DifI {L} (asuc c) (C.suc p) e w = DifI c p (⊲-tr (C.suc C.self) e) w ⨾ ni (hd (eqr L) (◁∘⊲ H.zero e)) (λ _ _ _ → n1)
DifI (alim f) (C.lim n p) e (st , w) =
  DifI (f n) p (⊲-tr (C.lim n C.self) e) (w n) ⨾
  nl (λ m → DifI (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) e) (w (suc (m + n))))

DifG : ∀ {M Q} (stp : ∀ {c} → c ◁ Q → D M azero) b {a W} → a ⊲ b → b ⊲ Q → Lg b → D M W
DifG stp b C.self e w = n0
DifG stp (asuc c) {W = W} (C.suc p) e w = DifG stp c p (⊲-tr (C.suc C.self) e) w ⨾ nw (z⊲ W) (stp (◁∘⊲ H.zero e))
DifG stp (alim f) (C.lim n p) e (st , w) =
  DifG stp (f n) p (⊲-tr (C.lim n C.self) e) (w n) ⨾
  nl (λ m → DifG stp (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) e) (w (suc (m + n))))

Up : ∀ {M} (L : Lay) (wl : Lay → Lay) (wk : ∀ {W L′} → KL W (azero ∷ L) L′ → KL W M (wl L′)) → AllLg L → ∀ {W} → D M W
Up [] wl wk _ = n0
Up (b ∷ L) wl wk (lb , lL) =
  Up L (λ L′ → wl (azero ∷ L′)) (λ {W} k → wk (tl (rehd k) (z⊲ W))) lL ⨾
  DifG (λ {c} i → nκ (nzK (wk (tl (hd (eqr L) i) (z⊲ azero))))
                     (λ {d} _ _ → ni (wk (tl (hd (eqr L) i) (C.self {d}))) (λ _ _ _ → n1)))
       b (z⊲ b) C.self lb

Ωd : ∀ L {W} → AllLg L → D L W
Ωd [] _ = n1
Ωd (a ∷ L) (la , lL) = n1 ⨾ (Up L (λ L′ → L′) rehd lL ⨾ DifI a (z⊲ a) C.self la)
```

## §5 坐标

同 `SumClimbTree`.

```agda
Cut : ∀ {Kd : A → Lay → Set} {V′ : ∀ {W L} → Kd W L → A → Set} {Z : Set} {W₀ W} (v : ∀ {c} → W₀ ⊲ c → Lg c → D₊ Kd V′ Z c) b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → D₊ Kd V′ Z W
Cut v b C.self ab lb bW = n0
Cut v (asuc c) (C.suc p) ab lb bW =
  Cut v c p ab lb (⊲-tr (C.suc C.self) bW) ⨾ nw (⊲-tr (C.suc C.self) bW) (v (⊲-tr ab p) lb)
Cut v (alim f) (C.lim n p) ab (st , w) bW =
  Cut v (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW) ⨾
  nl (λ m → Cut v (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW))

Pre : ∀ {Kd : A → Lay → Set} {V′ : ∀ {W L} → Kd W L → A → Set} {Z : Set} {W₀ W} → W₀ ⊲ W → (ℕ → D₊ Kd V′ Z W₀) → ℕ → D₊ Kd V′ Z W
Pre q₀ d zero = n0
Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

Int : ∀ {ly L′ W₀ W} → AccY (lay L′) → D L′ W₀ → W₀ ⊲ W → Lg W → AllB L′ W → Zy ly →
      (∀ {W₁ L″} → AllB L′ W₁ → KL W₁ L′ L″ → K ly W₁ L″) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D L′ W′ → Dl ly W′) → D L′ W → Dl ly W
IW  : ∀ {ly L′ W₀ W} → AccY (lay L′) → (∀ {c} → W₀ ⊲ c → Lg c → D L′ c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → Lg W → AllB L′ W → Zy ly →
      (∀ {W₁ L″} → AllB L′ W₁ → KL W₁ L′ L″ → K ly W₁ L″) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D L′ W′ → Dl ly W′) → D L′ W → Dl ly W

Int ac n0 q₀ lW hk zy mk u w = n0
Int ac n1 q₀ lW hk zy mk u w = u C.self lW w
Int ac (x ⨾ y) q₀ lW hk zy mk u w =
  Int ac x q₀ lW hk zy mk u w ⨾ Int ac y q₀ lW hk zy mk u (w ⨾ nw q₀ x)
Int ac (nl d) q₀ lW hk zy mk u w =
  nl (λ n → Int ac (d n) q₀ lW hk zy mk u (w ⨾ Pre q₀ d n))
Int ac (nw p x) q₀ lW hk zy mk u w = Int ac x (⊲-tr p q₀) lW hk zy mk u w
Int {ly} {L′} (acc f) (ni R v) q₀ lW hk zy mk u w =
  ni (mk hk (Kup (lay L′) q₀ R)) (λ {W′} p lW′ y →
    Int (acc f) (v (⊲-tr q₀ p) lW′ (inV (lay L′) R (outV ly (mk hk (Kup (lay L′) q₀ R)) y))) C.self lW′ (hk↑ hk p) zy mk (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Int {lay L′} (f R) (outV ly (mk hk (Kup (lay L′) q₀ R)) y) C.self lW′ (kk (lay L′) R (⊲-tr q₀ p) (hk↑ hk p)) (zyOf (lay L′) R) (mkOf (lay L′) R)
                  (λ p′ l′ z′ → v (⊲-tr (⊲-tr q₀ p) p′) l′ (inV (lay L′) R z′)) n0))
Int {W = W} ac (nκ zz v) q₀ lW hk zy mk u w =
  IW ac v W q₀ C.self lW C.self lW hk zy mk u w ⨾
  nκ zy (λ {c} p lc →
    Int ac (v (⊲-tr q₀ p) lc) C.self lc (hk↑ hk p) zy mk (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Cut v c (⊲-tr q₀ p) C.self lc C.self))

IW ac v b C.self ap lb bW lW hk zy mk u co = n0
IW ac v (asuc c) (C.suc p) ap lb bW lW hk zy mk u co =
  IW ac v c p ap lb (⊲-tr (C.suc C.self) bW) lW hk zy mk u co ⨾
  Int ac (v (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bW) lW hk zy mk u (co ⨾ Cut v c p ap lb (⊲-tr (C.suc C.self) bW))
IW ac v (alim f) (C.lim n p) ap (st , wl) bW lW hk zy mk u co =
  IW ac v (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bW) lW hk zy mk u co ⨾
  nl (λ m → IW ac v (f (suc (m + n))) (st (m + n)) (⊲-tr ap (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lW hk zy mk u
       (co ⨾ Cut v (f (m + n)) (tailP f st p m) ap (wl (m + n)) (⊲-tr (C.lim (m + n) C.self) bW)))
```

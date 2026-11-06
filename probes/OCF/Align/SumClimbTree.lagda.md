# 和形式, 层取三位 (一): 定义

> 不含记号. 入口 [SumClimb](SumClimb.lagda.md). 由 [SumHtTree](SumHtTree.lagda.md) 改写. **差别只在层: 层从 $(p,a)$ 加一维成 $(r,p,a)$**, 读作 $\Omega_{\Omega^2\cdot r+\Omega\cdot p+a}$; 顶层的节点三位都在世界之下, 读作 $\Omega_{\Omega^3}$. 这正是 "每升一级加一维" 的那一步, 见 [SumClimb](SumClimb.lagda.md) 的翻译账.
>
> 节点种类 `KQ r p a W g h k`: `sm` 前两位相同, $k$ 严格低于 $a$ (不看世界); `lo` 第一位相同, $h\lhd p$, $k\sqsubseteq W$; `lr` $g\lhd r$, $h,k\sqsubseteq W$. 与 `SumHtTree` 的 `sm`/`lo` 同形, 多一种 `lr`. 合法性仍只有 §3 讲和的 `sum-fst`, `Lg-sum`, 无前提, 不提折叠. **没有 `HS`, `Goodᴺ`, `WF`, `ψW`.**
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumClimbTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; S→⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLOpsW using (_◁_; ◁-tr; ◁⊲; ⊲◁; ◁∘⊲)
import OCF.Align.TLOpsW as H
open import OCF.Align.SumHtTree using (NZ; NZ◁; NZ-S; Sk; ⊲S; tailP; ⊲-idl; ⊲-as) public
```

## §1 树

同 `SumHtTree`, 节点的层多一位.

```agda
module _ (Kd : A → A → A → A → Set) (V : ∀ {W g h k} → Kd W g h k → A → Set) (Zz : Set) where
  infixl 6 _⨾_
  data D₊ : A → Set where
    n0  : ∀ {W} → D₊ W
    n1  : ∀ {W} → D₊ W
    _⨾_ : ∀ {W} → D₊ W → D₊ W → D₊ W
    nl  : ∀ {W} → (ℕ → D₊ W) → D₊ W
    ni  : ∀ {W g h k} (r : Kd W g h k) → (∀ {W′} → W ⊲ W′ → Lg W′ → V r W′ → D₊ W′) → D₊ W
    nκ  : ∀ {W} → Zz → (∀ {c} → W ⊲ c → Lg c → D₊ c) → D₊ W
    nw  : ∀ {W₀ W} → W₀ ⊲ W → D₊ W₀ → D₊ W
```

## §2 层

分支的类型按 $a$ (`sm`), $p$ (`lo`), $r$ (`lr`) 结构递归; 三位分开写成三个参数, 停机检查看得见字典序.

```agda
data KQ (r p a W : A) : A → A → A → Set where
  sm : ∀ {k} → Strict k a → KQ r p a W r p k
  lo : ∀ {h k} → h ◁ p → k ⊲ W → KQ r p a W r h k
  lr : ∀ {g h k} → g ◁ r → h ⊲ W → k ⊲ W → KQ r p a W g h k

ZQ : A → A → A → Set
ZQ r p a = NZ r ⊎ (NZ p ⊎ NZ a)

D    : A → A → A → A → Set
VQ   : ∀ r p a {W g h k} → KQ r p a W g h k → A → Set
Vs   : ∀ r p a {b} → Strict b a → A → Set
Vc   : ∀ r p a {b} → b ⊲ a → A → Set
LowP : ∀ r p {h} → h ◁ p → A → A → Set
LowR : ∀ r {g} → g ◁ r → A → A → A → Set
D r p a = D₊ (KQ r p a) (VQ r p a) (ZQ r p a)
VQ r p a (sm R) W′ = Vs r p a R W′
VQ r p a (lo {k = k} i e) W′ = LowP r p i k W′
VQ r p a (lr {h = h} {k} j e₁ e₂) W′ = LowR r j h k W′
Vs r p (asuc b) (ss P) u = Vc r p b P u
Vs r p (alim f) (sl n P) u = Vc r p (f n) P u
Vc r p a C.self u = D r p a u
Vc r p (asuc b) (C.suc P) u = Vc r p b P u
Vc r p (alim f) (C.lim n P) u = Vc r p (f n) P u
LowP r (asuc q) H.zero k u = D r q k u
LowP r (asuc q) (H.suc i) k u = LowP r q i k u
LowP r (alim f) (H.self n) k u = D r (f n) k u
LowP r (alim f) (H.lim n i) k u = LowP r (f n) i k u
LowR (asuc s) H.zero h k u = D s h k u
LowR (asuc s) (H.suc j) h k u = LowR s j h k u
LowR (alim f) (H.self n) h k u = D (f n) h k u
LowR (alim f) (H.lim n j) h k u = LowR (f n) j h k u

outC : ∀ {r p a b u} (P : b ⊲ a) → Vc r p a P u → D r p b u
outC C.self x = x
outC (C.suc P) x = outC P x
outC (C.lim n P) x = outC P x

inC : ∀ {r p a b u} (P : b ⊲ a) → D r p b u → Vc r p a P u
inC C.self x = x
inC (C.suc P) x = inC P x
inC (C.lim n P) x = inC P x

outS : ∀ {r p a b u} (R : Strict b a) → Vs r p a R u → D r p b u
outS (ss P) x = outC P x
outS (sl n P) x = outC P x

inS : ∀ {r p a b u} (R : Strict b a) → D r p b u → Vs r p a R u
inS (ss P) x = inC P x
inS (sl n P) x = inC P x

outP : ∀ {r p h k u} (i : h ◁ p) → LowP r p i k u → D r h k u
outP H.zero x = x
outP (H.self n) x = x
outP (H.suc i) x = outP i x
outP (H.lim n i) x = outP i x

inP : ∀ {r p h k u} (i : h ◁ p) → D r h k u → LowP r p i k u
inP H.zero x = x
inP (H.self n) x = x
inP (H.suc i) x = inP i x
inP (H.lim n i) x = inP i x

outR : ∀ {r g h k u} (j : g ◁ r) → LowR r j h k u → D g h k u
outR H.zero x = x
outR (H.self n) x = x
outR (H.suc j) x = outR j x
outR (H.lim n j) x = outR j x

inR : ∀ {r g h k u} (j : g ◁ r) → D g h k u → LowR r j h k u
inR H.zero x = x
inR (H.self n) x = x
inR (H.suc j) x = inR j x
inR (H.lim n j) x = inR j x
```

顶层: 节点的三位都在世界之下.

```agda
HK : A → A → A → A → Set
HK g h k W = (g ⊲ W) × ((h ⊲ W) × (k ⊲ W))

KT : A → A → A → A → Set
KT W g h k = HK g h k W

VT : ∀ {W g h k} → KT W g h k → A → Set
VT {g = g} {h} {k} _ W′ = D g h k W′

D̂ : A → Set
D̂ = D₊ KT VT ⊤

data Ly : Set where
  lay : A → A → A → Ly
  top : Ly

K : Ly → A → A → A → A → Set
K (lay r p a) = KQ r p a
K top = KT

V : ∀ ly {W g h k} → K ly W g h k → A → Set
V (lay r p a) x = VQ r p a x
V top x = VT x

Zy : Ly → Set
Zy (lay r p a) = ZQ r p a
Zy top = ⊤

Dl : Ly → A → Set
Dl ly = D₊ (K ly) (V ly) (Zy ly)

outV : ∀ ly {W g h k W′} (x : K ly W g h k) → V ly x W′ → D g h k W′
outV (lay r p a) (sm R) y = outS R y
outV (lay r p a) (lo i e) y = outP i y
outV (lay r p a) (lr j e₁ e₂) y = outR j y
outV top x y = y

inV : ∀ ly {W g h k W′} (x : K ly W g h k) → D g h k W′ → V ly x W′
inV (lay r p a) (sm R) z = inS R z
inV (lay r p a) (lo i e) z = inP i z
inV (lay r p a) (lr j e₁ e₂) z = inR j z
inV top x z = z

hk↑ : ∀ {g h k W W′} → HK g h k W → W ⊲ W′ → HK g h k W′
hk↑ (x , (y , z)) q = ⊲-tr x q , (⊲-tr y q , ⊲-tr z q)

LW : Ly → A → Set
LW (lay r p a) W = HK r p a W
LW top W = ⊤

LW↑ : ∀ ly {W W′} → W ⊲ W′ → LW ly W → LW ly W′
LW↑ (lay r p a) q l = hk↑ l q
LW↑ top q l = tt

kk : ∀ ly {W₀ W g h k} → K ly W₀ g h k → W₀ ⊲ W → LW ly W → HK g h k W
kk (lay r p a) (sm R) q (rW , (pW , aW)) = rW , (pW , ⊲-tr (S→⊲ R) aW)
kk (lay r p a) (lo i e) q (rW , (pW , aW)) = rW , (⊲-tr (◁⊲ i) pW , ⊲-tr e q)
kk (lay r p a) (lr j e₁ e₂) q (rW , (pW , aW)) = ⊲-tr (◁⊲ j) rW , (⊲-tr e₁ q , ⊲-tr e₂ q)
kk top x q l = hk↑ x q

Kup : ∀ ly {W W′ g h k} → W ⊲ W′ → K ly W g h k → K ly W′ g h k
Kup (lay r p a) q (sm R) = sm R
Kup (lay r p a) q (lo i e) = lo i (⊲-tr e q)
Kup (lay r p a) q (lr j e₁ e₂) = lr j (⊲-tr e₁ q) (⊲-tr e₂ q)
Kup top q x = hk↑ x q

mkOf : ∀ ly {W₀ g h k} → K ly W₀ g h k → ∀ {W₁ g′ h′ k′} → HK g h k W₁ → KQ g h k W₁ g′ h′ k′ → K ly W₁ g′ h′ k′
mkOf (lay r p a) (sm R) hk (sm R′) = sm (Sk R′ (S→⊲ R))
mkOf (lay r p a) (sm R) hk (lo i e) = lo i e
mkOf (lay r p a) (sm R) hk (lr j e₁ e₂) = lr j e₁ e₂
mkOf (lay r p a) (lo i e₀) (gW , (hW , kW)) (sm R′) = lo i (⊲-tr (S→⊲ R′) kW)
mkOf (lay r p a) (lo i e₀) hk (lo i′ e) = lo (◁-tr i′ i) e
mkOf (lay r p a) (lo i e₀) hk (lr j e₁ e₂) = lr j e₁ e₂
mkOf (lay r p a) (lr j f₁ f₂) (gW , (hW , kW)) (sm R′) = lr j hW (⊲-tr (S→⊲ R′) kW)
mkOf (lay r p a) (lr j f₁ f₂) (gW , (hW , kW)) (lo i′ e) = lr j (⊲-tr (◁⊲ i′) hW) e
mkOf (lay r p a) (lr j f₁ f₂) hk (lr j′ e₁ e₂) = lr (◁-tr j′ j) e₁ e₂
mkOf top x (gW , (hW , kW)) (sm R′) = gW , (hW , ⊲-tr (S→⊲ R′) kW)
mkOf top x (gW , (hW , kW)) (lo i′ e) = gW , (⊲-tr (◁⊲ i′) hW , e)
mkOf top x (gW , (hW , kW)) (lr j′ e₁ e₂) = ⊲-tr (◁⊲ j′) gW , (e₁ , e₂)

zyOf : ∀ ly {W g h k} → K ly W g h k → Zy ly
zyOf (lay r p a) (sm R) = inj₂ (inj₂ (NZ-S R))
zyOf (lay r p a) (lo i e) = inj₂ (inj₁ (NZ◁ i))
zyOf (lay r p a) (lr j e₁ e₂) = inj₁ (NZ◁ j)
zyOf top x = tt
```

**层的良基.** 按 $(r,p,a)$ 的字典序结构递归.

```agda
data AccY (ly : Ly) : Set where
  acc : (∀ {W g h k} → K ly W g h k → AccY (lay g h k)) → AccY ly

accY  : ∀ r p a → AccY (lay r p a)
accYs : ∀ r p a {k} → Strict k a → AccY (lay r p k)
accYc : ∀ r p a {k} → k ⊲ a → AccY (lay r p k)
accYp : ∀ r p {h} → h ◁ p → ∀ k → AccY (lay r h k)
accYr : ∀ r {g} → g ◁ r → ∀ h k → AccY (lay g h k)
accY r p a = acc (λ { (sm R) → accYs r p a R ; (lo {k = k} i e) → accYp r p i k ; (lr {h = h} {k} j e₁ e₂) → accYr r j h k })
accYs r p (asuc b) (ss P) = accYc r p b P
accYs r p (alim f) (sl n P) = accYc r p (f n) P
accYc r p a C.self = accY r p a
accYc r p (asuc b) (C.suc P) = accYc r p b P
accYc r p (alim f) (C.lim n P) = accYc r p (f n) P
accYp r (asuc q) H.zero k = accY r q k
accYp r (asuc q) (H.suc i) k = accYp r q i k
accYp r (alim f) (H.self n) k = accY r (f n) k
accYp r (alim f) (H.lim n i) k = accYp r (f n) i k
accYr (asuc s) H.zero h k = accY s h k
accYr (asuc s) (H.suc j) h k = accYr s j h k
accYr (alim f) (H.self n) h k = accY (f n) h k
accYr (alim f) (H.lim n j) h k = accYr (f n) j h k

accTop : AccY top
accTop = acc (λ {_} {g} {h} {k} _ → accY g h k)
```

## §3 第 0 层的树给层

层 $(0,0,0)$ 没有节点, 也没有 `nκ`. **合法性证明只有这一节.**

```agda
D₀ : A → Set
D₀ = D azero azero azero

drp : ∀ {W W′} → D₀ W → D₀ W′
drp n0 = n0
drp n1 = n1
drp (x ⨾ y) = drp x ⨾ drp y
drp (nl d) = nl (λ n → drp (d n))
drp (ni (sm ()) u)
drp (ni (lo () e) u)
drp (ni (lr () e₁ e₂) u)
drp (nκ (inj₁ ()) u)
drp (nκ (inj₂ (inj₁ ())) u)
drp (nκ (inj₂ (inj₂ ())) u)
drp (nw p x) = drp x

pt  : ∀ {W} → A → (ℕ → D₀ W) → ℕ → A
sum : ∀ {W} → A → D₀ W → A
pt b d zero = b
pt b d (suc n) = sum (pt b d n) (d n)
sum b n0 = b
sum b n1 = asuc b
sum b (x ⨾ y) = sum (sum b x) y
sum b (nl d) = alim (pt b d)
sum b (ni (sm ()) u)
sum b (ni (lo () e) u)
sum b (ni (lr () e₁ e₂) u)
sum b (nκ (inj₁ ()) u)
sum b (nκ (inj₂ (inj₁ ())) u)
sum b (nκ (inj₂ (inj₂ ())) u)
sum b (nw p x) = sum b x

sum-fst : ∀ {W} b (x : D₀ W) → b ⊲ sum b x
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni (sm ()) u)
sum-fst b (ni (lo () e) u)
sum-fst b (ni (lr () e₁ e₂) u)
sum-fst b (nκ (inj₁ ()) u)
sum-fst b (nκ (inj₂ (inj₁ ())) u)
sum-fst b (nκ (inj₂ (inj₂ ())) u)
sum-fst b (nw p x) = sum-fst b x

Lg-sum : ∀ {W} b (x : D₀ W) → Lg b → Lg (sum b x)
Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → Lg b → Lg (pt b d n)
Lg-sum b n0 w = w
Lg-sum b n1 w = w
Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
Lg-sum b (ni (sm ()) u) w
Lg-sum b (ni (lo () e) u) w
Lg-sum b (ni (lr () e₁ e₂) u) w
Lg-sum b (nκ (inj₁ ()) u) w
Lg-sum b (nκ (inj₂ (inj₁ ())) u) w
Lg-sum b (nκ (inj₂ (inj₂ ())) u) w
Lg-sum b (nw p x) w = Lg-sum b x w
Lg-pt b d zero w = w
Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)
```

## §4 $\Omega$

$\Omega_{\Omega^2\cdot r+\Omega\cdot q+t}=1$ 接上三段差. 下标一步: 同层节点. 第二位一步 $c\to c+1$: $\sum_{d\ge0}\sum_{z:(r,c,d)}1$ (`stepH`, 同 `SumHtTree`). 第一位一步 $c\to c+1$: $\sum_{d\ge0}\sum_{z:(c,d,0)}1$ (`stepR`); 用 $(c,d,0)$ 而不用整段, 因为 $\sup_d\Omega_{\Omega^2\cdot c+\Omega\cdot d+1}=\Omega_{\Omega^2\cdot(c+1)}$ (值相同是判断).

```agda
DifI : ∀ {r q} b {a L W} → a ⊲ b → b ⊲ L → Lg b → D r q L W
DifI b C.self e w = n0
DifI (asuc c) (C.suc p) e w = DifI c p (⊲-tr (C.suc C.self) e) w ⨾ ni (sm (⊲S e)) (λ _ _ _ → n1)
DifI (alim f) (C.lim n p) e (st , w) =
  DifI (f n) p (⊲-tr (C.lim n C.self) e) (w n) ⨾
  nl (λ m → DifI (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) e) (w (suc (m + n))))

stepH : ∀ {r Q t c} → c ◁ Q → D r Q t azero
stepH i = nκ (inj₂ (inj₁ (NZ◁ i))) (λ {d} _ _ → ni (lo i (C.self {d})) (λ _ _ _ → n1))

DifH : ∀ {r t} b {a Q W} → a ⊲ b → b ⊲ Q → Lg b → D r Q t W
DifH b C.self e w = n0
DifH (asuc c) {W = W} (C.suc p) e w = DifH c p (⊲-tr (C.suc C.self) e) w ⨾ nw (z⊲ W) (stepH (◁∘⊲ H.zero e))
DifH (alim f) (C.lim n p) e (st , w) =
  DifH (f n) p (⊲-tr (C.lim n C.self) e) (w n) ⨾
  nl (λ m → DifH (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) e) (w (suc (m + n))))

stepR : ∀ {R q t c} → c ◁ R → D R q t azero
stepR i = nκ (inj₁ (NZ◁ i)) (λ {d} _ _ → ni (lr i (C.self {d}) (z⊲ d)) (λ _ _ _ → n1))

DifR : ∀ {q t} b {a R W} → a ⊲ b → b ⊲ R → Lg b → D R q t W
DifR b C.self e w = n0
DifR (asuc c) {W = W} (C.suc p) e w = DifR c p (⊲-tr (C.suc C.self) e) w ⨾ nw (z⊲ W) (stepR (◁∘⊲ H.zero e))
DifR (alim f) (C.lim n p) e (st , w) =
  DifR (f n) p (⊲-tr (C.lim n C.self) e) (w n) ⨾
  nl (λ m → DifR (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) e) (w (suc (m + n))))

Ωd : ∀ r q t {W} → Lg r → Lg q → Lg t → D r q t W
Ωd r q t lr′ lq lt = n1 ⨾ (DifR r (z⊲ r) C.self lr′ ⨾ (DifH q (z⊲ q) C.self lq ⨾ DifI t (z⊲ t) C.self lt))
```

## §5 坐标

同 `SumHtTree`.

```agda
Cut : ∀ {Kd : A → A → A → A → Set} {V′ : ∀ {W g h k} → Kd W g h k → A → Set} {Z : Set} {W₀ W} (v : ∀ {c} → W₀ ⊲ c → Lg c → D₊ Kd V′ Z c) b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → D₊ Kd V′ Z W
Cut v b C.self ab lb bW = n0
Cut v (asuc c) (C.suc p) ab lb bW =
  Cut v c p ab lb (⊲-tr (C.suc C.self) bW) ⨾ nw (⊲-tr (C.suc C.self) bW) (v (⊲-tr ab p) lb)
Cut v (alim f) (C.lim n p) ab (st , w) bW =
  Cut v (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW) ⨾
  nl (λ m → Cut v (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW))

Pre : ∀ {Kd : A → A → A → A → Set} {V′ : ∀ {W g h k} → Kd W g h k → A → Set} {Z : Set} {W₀ W} → W₀ ⊲ W → (ℕ → D₊ Kd V′ Z W₀) → ℕ → D₊ Kd V′ Z W
Pre q₀ d zero = n0
Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

Int : ∀ {ly g h k W₀ W} → AccY (lay g h k) → D g h k W₀ → W₀ ⊲ W → Lg W → HK g h k W → Zy ly →
      (∀ {W₁ g′ h′ k′} → HK g h k W₁ → KQ g h k W₁ g′ h′ k′ → K ly W₁ g′ h′ k′) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D g h k W′ → Dl ly W′) → D g h k W → Dl ly W
IW  : ∀ {ly g h k W₀ W} → AccY (lay g h k) → (∀ {c} → W₀ ⊲ c → Lg c → D g h k c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → Lg W → HK g h k W → Zy ly →
      (∀ {W₁ g′ h′ k′} → HK g h k W₁ → KQ g h k W₁ g′ h′ k′ → K ly W₁ g′ h′ k′) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D g h k W′ → Dl ly W′) → D g h k W → Dl ly W

Int ac n0 q₀ lW hk zy mk u w = n0
Int ac n1 q₀ lW hk zy mk u w = u C.self lW w
Int ac (x ⨾ y) q₀ lW hk zy mk u w =
  Int ac x q₀ lW hk zy mk u w ⨾ Int ac y q₀ lW hk zy mk u (w ⨾ nw q₀ x)
Int ac (nl d) q₀ lW hk zy mk u w =
  nl (λ n → Int ac (d n) q₀ lW hk zy mk u (w ⨾ Pre q₀ d n))
Int ac (nw p x) q₀ lW hk zy mk u w = Int ac x (⊲-tr p q₀) lW hk zy mk u w
Int {ly} {g} {h} {k} (acc f) (ni R v) q₀ lW hk zy mk u w =
  ni (mk hk (Kup (lay g h k) q₀ R)) (λ {W′} p lW′ y →
    Int (acc f) (v (⊲-tr q₀ p) lW′ (inV (lay g h k) R (outV ly (mk hk (Kup (lay g h k) q₀ R)) y))) C.self lW′ (hk↑ hk p) zy mk (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Int {lay g h k} (f R) (outV ly (mk hk (Kup (lay g h k) q₀ R)) y) C.self lW′ (kk (lay g h k) R (⊲-tr q₀ p) (hk↑ hk p)) (zyOf (lay g h k) R) (mkOf (lay g h k) R)
                  (λ p′ l′ z′ → v (⊲-tr (⊲-tr q₀ p) p′) l′ (inV (lay g h k) R z′)) n0))
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

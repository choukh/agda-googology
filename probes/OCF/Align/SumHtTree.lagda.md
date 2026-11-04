# 和形式, 高度取 $A$ (一): 定义

> 不含记号. 入口 [SumHt](SumHt.lagda.md). 由 [SumOneTree](SumOneTree.lagda.md) 改写. 差别只在层: [SumOne](SumOne.lagda.md) 的层只有两档 (可数层 `cnt a`, 顶层 $\Omega_\Omega$), 这里**层是一对 $(p,a)$, $p,a$ 都是字面合法的 $A$**, 读作 $\Omega_{\Omega\cdot p+a}$; 另有一个顶层 `top`, 它的节点高度也只要在世界之下, 读作 $\Omega_{\Omega^2}$.
>
> - 层 $(p,a)$ 的节点有两种, 与 [TLOpsW](TLOpsW.lagda.md) 的 `oi`, `od` 同形: 同高度 `sm` (下标严格在 $a$ 之下, 不看世界), 低高度 `lo` (高度 $h\lhd p$, 下标在世界之下). 顶层的节点 `KT`: 高度和下标都在世界之下, 与 `SumOne` 的顶层 (下标在世界之下) 同形, 只是多了一维.
> - 回灌闭包仍是一个节点 `nκ`: $\sum_{c\ge W}u(c)$. 除了 $(0,0)$, 每一层都允许它 (`ZP`).
> - 合法性仍只有讲和的 `sum-fst`, `Lg-sum` (§3), 无前提, 不提折叠. **没有 `HS`, `Goodᴺ`, `WF`, `ψW`.**
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumHtTree where

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
```

## §1 树

与 `SumOneTree` 相同, 只是节点的种类 `Kd W h k` 多了高度 $h$: 节点 `ni r u` 是 $\sum_z u(z)$, $z$ 过层 $(h,k)$ 的元素.

```agda
NZ : A → Set
NZ azero = ⊥
NZ (asuc _) = ⊤
NZ (alim _) = ⊤

module _ (Kd : A → A → A → Set) (V : ∀ {W h k} → Kd W h k → A → Set) (Zz : Set) where
  infixl 6 _⨾_
  data D₊ : A → Set where
    n0  : ∀ {W} → D₊ W
    n1  : ∀ {W} → D₊ W
    _⨾_ : ∀ {W} → D₊ W → D₊ W → D₊ W
    nl  : ∀ {W} → (ℕ → D₊ W) → D₊ W
    ni  : ∀ {W h k} (r : Kd W h k) → (∀ {W′} → W ⊲ W′ → Lg W′ → V r W′ → D₊ W′) → D₊ W
    nκ  : ∀ {W} → Zz → (∀ {c} → W ⊲ c → Lg c → D₊ c) → D₊ W
    nw  : ∀ {W₀ W} → W₀ ⊲ W → D₊ W₀ → D₊ W
```

## §2 层

`KP p a W h k`: 层 $(p,a)$ 在世界 $W$ 里, 节点可以过层 $(h,k)$. `sm`: 同高度, $k$ 严格低于 $a$. `lo`: 低高度, $k$ 在世界之下. 分支的类型 `VP` 按 $a$ (同高度) 或 $p$ (低高度) 结构递归, 与 `TLOpsW` 的 `Vs`, `Low` 同形.

```agda
data KP (p a W : A) : A → A → Set where
  sm : ∀ {k} → Strict k a → KP p a W p k
  lo : ∀ {h k} → h ◁ p → k ⊲ W → KP p a W h k

ZP : A → A → Set
ZP p a = NZ p ⊎ NZ a

D   : A → A → A → Set
VP  : ∀ p a {W h k} → KP p a W h k → A → Set
Vs  : ∀ p a {b} → Strict b a → A → Set
Vc  : ∀ p a {b} → b ⊲ a → A → Set
Low : ∀ p {h} → h ◁ p → A → A → Set
D p a = D₊ (KP p a) (VP p a) (ZP p a)
VP p a (sm R) W′ = Vs p a R W′
VP p a (lo {k = k} i e) W′ = Low p i k W′
Vs p (asuc b) (ss P) u = Vc p b P u
Vs p (alim f) (sl n P) u = Vc p (f n) P u
Vc p a C.self u = D p a u
Vc p (asuc b) (C.suc P) u = Vc p b P u
Vc p (alim f) (C.lim n P) u = Vc p (f n) P u
Low (asuc q) H.zero k u = D q k u
Low (asuc q) (H.suc i) k u = Low q i k u
Low (alim f) (H.self n) k u = D (f n) k u
Low (alim f) (H.lim n i) k u = Low (f n) i k u

outC : ∀ {p a b u} (P : b ⊲ a) → Vc p a P u → D p b u
outC C.self x = x
outC (C.suc P) x = outC P x
outC (C.lim n P) x = outC P x

inC : ∀ {p a b u} (P : b ⊲ a) → D p b u → Vc p a P u
inC C.self x = x
inC (C.suc P) x = inC P x
inC (C.lim n P) x = inC P x

outS : ∀ {p a b u} (R : Strict b a) → Vs p a R u → D p b u
outS (ss P) x = outC P x
outS (sl n P) x = outC P x

inS : ∀ {p a b u} (R : Strict b a) → D p b u → Vs p a R u
inS (ss P) x = inC P x
inS (sl n P) x = inC P x

outL : ∀ {p h k u} (i : h ◁ p) → Low p i k u → D h k u
outL H.zero x = x
outL (H.self n) x = x
outL (H.suc i) x = outL i x
outL (H.lim n i) x = outL i x

inL : ∀ {p h k u} (i : h ◁ p) → D h k u → Low p i k u
inL H.zero x = x
inL (H.self n) x = x
inL (H.suc i) x = inL i x
inL (H.lim n i) x = inL i x
```

顶层: 节点的高度和下标都在世界之下.

```agda
KT : A → A → A → Set
KT W h k = (h ⊲ W) × (k ⊲ W)

VT : ∀ {W h k} → KT W h k → A → Set
VT {h = h} {k} _ W′ = D h k W′

D̂ : A → Set
D̂ = D₊ KT VT ⊤

data Ly : Set where
  lay : A → A → Ly
  top : Ly

K : Ly → A → A → A → Set
K (lay p a) = KP p a
K top = KT

V : ∀ ly {W h k} → K ly W h k → A → Set
V (lay p a) r = VP p a r
V top r = VT r

Zy : Ly → Set
Zy (lay p a) = ZP p a
Zy top = ⊤

Dl : Ly → A → Set
Dl ly = D₊ (K ly) (V ly) (Zy ly)

outV : ∀ ly {W h k W′} (r : K ly W h k) → V ly r W′ → D h k W′
outV (lay p a) (sm R) y = outS R y
outV (lay p a) (lo i e) y = outL i y
outV top r y = y

inV : ∀ ly {W h k W′} (r : K ly W h k) → D h k W′ → V ly r W′
inV (lay p a) (sm R) z = inS R z
inV (lay p a) (lo i e) z = inL i z
inV top r z = z
```

层在世界之下 (`LW`), 节点的层在世界之下 (`kk`), 节点种类搬到大世界 (`Kup`), 低层节点嵌进高层 (`mkOf`).

```agda
HK : A → A → A → Set
HK h k W = (h ⊲ W) × (k ⊲ W)

hk↑ : ∀ {h k W W′} → HK h k W → W ⊲ W′ → HK h k W′
hk↑ (x , y) q = ⊲-tr x q , ⊲-tr y q

LW : Ly → A → Set
LW (lay p a) W = HK p a W
LW top W = ⊤

LW↑ : ∀ ly {W W′} → W ⊲ W′ → LW ly W → LW ly W′
LW↑ (lay p a) q l = hk↑ l q
LW↑ top q l = tt

kk : ∀ ly {W₀ W h k} → K ly W₀ h k → W₀ ⊲ W → LW ly W → HK h k W
kk (lay p a) (sm R) q (pW , aW) = pW , ⊲-tr (S→⊲ R) aW
kk (lay p a) (lo i e) q (pW , aW) = ⊲-tr (◁⊲ i) pW , ⊲-tr e q
kk top (hW , kW) q l = ⊲-tr hW q , ⊲-tr kW q

Kup : ∀ ly {W W′ h k} → W ⊲ W′ → K ly W h k → K ly W′ h k
Kup (lay p a) q (sm R) = sm R
Kup (lay p a) q (lo i e) = lo i (⊲-tr e q)
Kup top q (hW , kW) = ⊲-tr hW q , ⊲-tr kW q

Sk : ∀ {j k L} → Strict j k → k ⊲ L → Strict j L
Sk R C.self = R
Sk R (C.suc p) = ss (⊲-tr (S→⊲ R) p)
Sk R (C.lim n p) = sl n (⊲-tr (S→⊲ R) p)

mkOf : ∀ ly {W₀ h k} → K ly W₀ h k → ∀ {W₁ h′ k′} → HK h k W₁ → KP h k W₁ h′ k′ → K ly W₁ h′ k′
mkOf (lay p a) (sm R) hk (sm R′) = sm (Sk R′ (S→⊲ R))
mkOf (lay p a) (sm R) hk (lo i e) = lo i e
mkOf (lay p a) (lo i e₀) (hW , kW) (sm R′) = lo i (⊲-tr (S→⊲ R′) kW)
mkOf (lay p a) (lo i e₀) hk (lo j e) = lo (◁-tr j i) e
mkOf top r (hW , kW) (sm R′) = hW , ⊲-tr (S→⊲ R′) kW
mkOf top r (hW , kW) (lo j e) = ⊲-tr (◁⊲ j) hW , e

NZ◁ : ∀ {h p} → h ◁ p → NZ p
NZ◁ H.zero = tt
NZ◁ (H.suc i) = tt
NZ◁ (H.self n) = tt
NZ◁ (H.lim n i) = tt

NZ-S : ∀ {j k} → Strict j k → NZ k
NZ-S (ss P) = tt
NZ-S (sl n P) = tt

zyOf : ∀ ly {W h k} → K ly W h k → Zy ly
zyOf (lay p a) (sm R) = inj₂ (NZ-S R)
zyOf (lay p a) (lo i e) = inj₁ (NZ◁ i)
zyOf top r = tt
```

**层的良基.** 节点总过字面更低的层: 同高度时下标降, 低高度时高度降. 按 $(p,a)$ 的字典序结构递归.

```agda
data AccY (ly : Ly) : Set where
  acc : (∀ {W h k} → K ly W h k → AccY (lay h k)) → AccY ly

accY  : ∀ p a → AccY (lay p a)
accYs : ∀ p a {k} → Strict k a → AccY (lay p k)
accYc : ∀ p a {k} → k ⊲ a → AccY (lay p k)
accYl : ∀ p {h} → h ◁ p → ∀ k → AccY (lay h k)
accY p a = acc (λ { (sm R) → accYs p a R ; (lo {k = k} i e) → accYl p i k })
accYs p (asuc b) (ss P) = accYc p b P
accYs p (alim f) (sl n P) = accYc p (f n) P
accYc p a C.self = accY p a
accYc p (asuc b) (C.suc P) = accYc p b P
accYc p (alim f) (C.lim n P) = accYc p (f n) P
accYl (asuc q) H.zero k = accY q k
accYl (asuc q) (H.suc i) k = accYl q i k
accYl (alim f) (H.self n) k = accY (f n) k
accYl (alim f) (H.lim n i) k = accYl (f n) i k

accTop : AccY top
accTop = acc (λ {_} {h} {k} _ → accY h k)
```

## §3 第 0 层的树给层

层 $(0,0)$ 没有节点 (`sm` 要 $k$ 严格低于 $0$, `lo` 要高度低于 $0$), 也没有 `nκ` (`ZP 0 0` 是空的), 所以世界不起作用 (`drp`). **合法性证明只有这一节.**

```agda
D₀ : A → Set
D₀ = D azero azero

drp : ∀ {W W′} → D₀ W → D₀ W′
drp n0 = n0
drp n1 = n1
drp (x ⨾ y) = drp x ⨾ drp y
drp (nl d) = nl (λ n → drp (d n))
drp (ni (sm ()) u)
drp (ni (lo () e) u)
drp (nκ (inj₁ ()) u)
drp (nκ (inj₂ ()) u)
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
sum b (nκ (inj₁ ()) u)
sum b (nκ (inj₂ ()) u)
sum b (nw p x) = sum b x

sum-fst : ∀ {W} b (x : D₀ W) → b ⊲ sum b x
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni (sm ()) u)
sum-fst b (ni (lo () e) u)
sum-fst b (nκ (inj₁ ()) u)
sum-fst b (nκ (inj₂ ()) u)
sum-fst b (nw p x) = sum-fst b x

Lg-sum : ∀ {W} b (x : D₀ W) → Lg b → Lg (sum b x)
Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → Lg b → Lg (pt b d n)
Lg-sum b n0 w = w
Lg-sum b n1 w = w
Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
Lg-sum b (ni (sm ()) u) w
Lg-sum b (ni (lo () e) u) w
Lg-sum b (nκ (inj₁ ()) u) w
Lg-sum b (nκ (inj₂ ()) u) w
Lg-sum b (nw p x) w = Lg-sum b x w
Lg-pt b d zero w = w
Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)
```

## §4 $\Omega$

$\Omega_{\Omega\cdot q+t}=1$ 接上高度的差, 再接上下标的差. 下标的后继一步是同高度的节点 $\sum_{z:(q,c)}1$ (`DifI`). 高度的后继一步 $c\to c+1$ 是闭包 $\sum_{d\ge 0}\sum_{z:(c,d)}1$ (`stepH`), 世界从 $0$ 起; 这就是 `SumOne` 的 `Ω̂₀` 换一个高度.

```agda
⊲S : ∀ {c L} → asuc c ⊲ L → Strict c L
⊲S C.self = ss C.self
⊲S (C.suc P) = ss (⊲-tr (C.suc C.self) P)
⊲S (C.lim n P) = sl n (⊲-tr (C.suc C.self) P)

DifI : ∀ {q} b {a L W} → a ⊲ b → b ⊲ L → Lg b → D q L W
DifI b C.self e w = n0
DifI (asuc c) (C.suc p) e w = DifI c p (⊲-tr (C.suc C.self) e) w ⨾ ni (sm (⊲S e)) (λ _ _ _ → n1)
DifI (alim f) (C.lim n p) e (st , w) =
  DifI (f n) p (⊲-tr (C.lim n C.self) e) (w n) ⨾
  nl (λ m → DifI (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) e) (w (suc (m + n))))

stepH : ∀ {Q t c} → c ◁ Q → D Q t azero
stepH i = nκ (inj₁ (NZ◁ i)) (λ {d} _ _ → ni (lo i (C.self {d})) (λ _ _ _ → n1))

DifH : ∀ {t} b {a Q W} → a ⊲ b → b ⊲ Q → Lg b → D Q t W
DifH b C.self e w = n0
DifH (asuc c) {W = W} (C.suc p) e w = DifH c p (⊲-tr (C.suc C.self) e) w ⨾ nw (z⊲ W) (stepH (◁∘⊲ H.zero e))
DifH (alim f) (C.lim n p) e (st , w) =
  DifH (f n) p (⊲-tr (C.lim n C.self) e) (w n) ⨾
  nl (λ m → DifH (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) e) (w (suc (m + n))))

Ωd : ∀ q t {W} → Lg q → Lg t → D q t W
Ωd q t lq lt = n1 ⨾ (DifH q (z⊲ q) C.self lq ⨾ DifI t (z⊲ t) C.self lt)
```

## §5 坐标

`Cut`: 从 $a$ 走到 $b$, 每个后继位置放上分支 (同 `SumOneTree`). `Int`: 低层的坐标上走过, 每个位置放 `u`; 嵌套节点按 `mkOf` 换成高层的节点. 只被分支的参数用.

```agda
tailP : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a n} → a ⊲ f n → ∀ m → a ⊲ f (m + n)
tailP f st p zero = p
tailP f st {n = n} p (suc m) = ⊲-tr (tailP f st p m) (st (m + n))

Cut : ∀ {Kd : A → A → A → Set} {V′ : ∀ {W h k} → Kd W h k → A → Set} {Z : Set} {W₀ W} (v : ∀ {c} → W₀ ⊲ c → Lg c → D₊ Kd V′ Z c) b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → D₊ Kd V′ Z W
Cut v b C.self ab lb bW = n0
Cut v (asuc c) (C.suc p) ab lb bW =
  Cut v c p ab lb (⊲-tr (C.suc C.self) bW) ⨾ nw (⊲-tr (C.suc C.self) bW) (v (⊲-tr ab p) lb)
Cut v (alim f) (C.lim n p) ab (st , w) bW =
  Cut v (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW) ⨾
  nl (λ m → Cut v (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW))

Pre : ∀ {Kd : A → A → A → Set} {V′ : ∀ {W h k} → Kd W h k → A → Set} {Z : Set} {W₀ W} → W₀ ⊲ W → (ℕ → D₊ Kd V′ Z W₀) → ℕ → D₊ Kd V′ Z W
Pre q₀ d zero = n0
Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

Int : ∀ {ly h k W₀ W} → AccY (lay h k) → D h k W₀ → W₀ ⊲ W → Lg W → HK h k W → Zy ly →
      (∀ {W₁ h′ k′} → HK h k W₁ → KP h k W₁ h′ k′ → K ly W₁ h′ k′) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D h k W′ → Dl ly W′) → D h k W → Dl ly W
IW  : ∀ {ly h k W₀ W} → AccY (lay h k) → (∀ {c} → W₀ ⊲ c → Lg c → D h k c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → Lg W → HK h k W → Zy ly →
      (∀ {W₁ h′ k′} → HK h k W₁ → KP h k W₁ h′ k′ → K ly W₁ h′ k′) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D h k W′ → Dl ly W′) → D h k W → Dl ly W

Int ac n0 q₀ lW hk zy mk u w = n0
Int ac n1 q₀ lW hk zy mk u w = u C.self lW w
Int ac (x ⨾ y) q₀ lW hk zy mk u w =
  Int ac x q₀ lW hk zy mk u w ⨾ Int ac y q₀ lW hk zy mk u (w ⨾ nw q₀ x)
Int ac (nl d) q₀ lW hk zy mk u w =
  nl (λ n → Int ac (d n) q₀ lW hk zy mk u (w ⨾ Pre q₀ d n))
Int ac (nw p x) q₀ lW hk zy mk u w = Int ac x (⊲-tr p q₀) lW hk zy mk u w
Int {ly} {h} {k} (acc g) (ni R v) q₀ lW hk zy mk u w =
  ni (mk hk (Kup (lay h k) q₀ R)) (λ {W′} p lW′ y →
    Int (acc g) (v (⊲-tr q₀ p) lW′ (inV (lay h k) R (outV ly (mk hk (Kup (lay h k) q₀ R)) y))) C.self lW′ (hk↑ hk p) zy mk (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Int {lay h k} (g R) (outV ly (mk hk (Kup (lay h k) q₀ R)) y) C.self lW′ (kk (lay h k) R (⊲-tr q₀ p) (hk↑ hk p)) (zyOf (lay h k) R) (mkOf (lay h k) R)
                  (λ p′ l′ z′ → v (⊲-tr (⊲-tr q₀ p) p′) l′ (inV (lay h k) R z′)) n0))
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

## §6 路径的两条算律

只给 [SumHtGrow](SumHtGrow.lagda.md) 用.

```agda
⊲-idl : ∀ {a b} (q : a ⊲ b) → ⊲-tr C.self q ≡ q
⊲-idl C.self = refl
⊲-idl (C.suc q) = cong C.suc (⊲-idl q)
⊲-idl (C.lim n q) = cong (C.lim n) (⊲-idl q)

⊲-as : ∀ {a b c d} (p : a ⊲ b) (q : b ⊲ c) (r : c ⊲ d) → ⊲-tr p (⊲-tr q r) ≡ ⊲-tr (⊲-tr p q) r
⊲-as p q C.self = refl
⊲-as p q (C.suc r) = cong C.suc (⊲-as p q r)
⊲-as p q (C.lim n r) = cong (C.lim n) (⊲-as p q r)
```

# 和形式过 $\Omega_{\Omega+1}$ (一): 定义

> 不含记号. 入口 [SumOne](SumOne.lagda.md). [TLRuleSum](TLRuleSum.lagda.md) 的和形式加一件东西: **世界 $W$ 上的和 `nκ`**, 它就是 $\Omega_\Omega$ 的形状: $\sum_{c\ge W}$ 每个层 $c$ 上放一段. $\Omega_\Omega=1+\sum_{c\ge0}\sum_{z:c}1$. 输出在第 0 层时这个节点走回灌: 层是已有的第 0 层的和, 下一个层字面接在上一个层后面 (`sum-fst`). 输出在别的层时节点保留.
>
> **这里没有 `HS`, `Goodᴺ`, `WF`, `ψW`, 证书不进定义.** 合法性只有 §2 讲和的 `sum-fst`, `Lg-sum` (无前提, 不提折叠).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.SumOneTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; S→⊲; lgS; cmpF; Tg)
import OCF.Align.CumReadCF as C
```

## §1 树

`ni R u`: 节点, $\sum_z u(z)$, $z$ 过低层, 分支在更大的世界上才有 (世界是比较的字面上界). `nκ _ u`: $\sum_{c\ge W}u(c)$, 分支是层上的. `nw`: 世界的懒抬升.

```agda
NZ : A → Set
NZ azero = ⊥
NZ (asuc _) = ⊤
NZ (alim _) = ⊤

module _ (Kd : A → A → Set) (V : ∀ {W k} → Kd W k → A → Set) (Zz : Set) where
  infixl 6 _⨾_
  data D₊ : A → Set where
    n0  : ∀ {W} → D₊ W
    n1  : ∀ {W} → D₊ W
    _⨾_ : ∀ {W} → D₊ W → D₊ W → D₊ W
    nl  : ∀ {W} → (ℕ → D₊ W) → D₊ W
    ni  : ∀ {W k} (r : Kd W k) → (∀ {W′} → W ⊲ W′ → Lg W′ → V r W′ → D₊ W′) → D₊ W
    nκ  : ∀ {W} → Zz → (∀ {c} → W ⊲ c → Lg c → D₊ c) → D₊ W
    nw  : ∀ {W₀ W} → W₀ ⊲ W → D₊ W₀ → D₊ W

D  : A → A → Set
Ws : ∀ L {a} → Strict a L → A → Set
Wc : ∀ b {a} → a ⊲ b → A → Set
D L = D₊ (λ _ k → Strict k L) (λ {_} {_} R → Ws L R) (NZ L)
Ws (asuc b) (ss P) W = Wc b P W
Ws (alim f) (sl n P) W = Wc (f n) P W
Wc a C.self W = D a W
Wc (asuc b) (C.suc P) W = Wc b P W
Wc (alim f) (C.lim n P) W = Wc (f n) P W

outC : ∀ {b a W} (P : a ⊲ b) → Wc b P W → D a W
outC C.self x = x
outC (C.suc P) x = outC P x
outC (C.lim n P) x = outC P x

inC : ∀ {b a W} (P : a ⊲ b) → D a W → Wc b P W
inC C.self x = x
inC (C.suc P) x = inC P x
inC (C.lim n P) x = inC P x

outS : ∀ {b a W} (R : Strict a b) → Ws b R W → D a W
outS (ss P) x = outC P x
outS (sl n P) x = outC P x

inS : ∀ {b a W} (R : Strict a b) → D a W → Ws b R W
inS (ss P) x = inC P x
inS (sl n P) x = inC P x

out-inC : ∀ {b a W} (P : a ⊲ b) (x : D a W) → outC P (inC P x) ≡ x
out-inC C.self x = refl
out-inC (C.suc P) x = out-inC P x
out-inC (C.lim n P) x = out-inC P x

out-inS : ∀ {b a W} (R : Strict a b) (x : D a W) → outS R (inS R x) ≡ x
out-inS (ss P) x = out-inC P x
out-inS (sl n P) x = out-inC P x

-- 顶层 Ω_Ω 这一层: 节点的层只要低于世界
D̂ : A → Set
D̂ = D₊ (λ W k → k ⊲ W) (λ {_} {k} _ W′ → D k W′) ⊤

data Ly : Set where
  cnt : A → Ly
  top : Ly

K : Ly → A → A → Set
K (cnt L) W k = Strict k L
K top W k = k ⊲ W

V : ∀ ly {W k} → K ly W k → A → Set
V (cnt L) R W′ = Ws L R W′
V top {k = k} _ W′ = D k W′

Zy : Ly → Set
Zy (cnt L) = NZ L
Zy top = ⊤

Dl : Ly → A → Set
Dl ly = D₊ (K ly) (V ly) (Zy ly)

LW : Ly → A → Set
LW (cnt L) W = L ⊲ W
LW top W = ⊤

LW↑ : ∀ {W W′} ly → W ⊲ W′ → LW ly W → LW ly W′
LW↑ (cnt L) q l = ⊲-tr l q
LW↑ top q l = tt

kk : ∀ ly {W₀ W k} → K ly W₀ k → W₀ ⊲ W → LW ly W → k ⊲ W
kk (cnt L) R q l = ⊲-tr (S→⊲ R) l
kk top r q l = ⊲-tr r q

inV : ∀ ly {W₀ k W′} (r : K ly W₀ k) → D k W′ → V ly r W′
inV (cnt L) R z = inS R z
inV top r z = z

Sk : ∀ {j k L} → Strict j k → k ⊲ L → Strict j L
Sk R C.self = R
Sk R (C.suc p) = ss (⊲-tr (S→⊲ R) p)
Sk R (C.lim n p) = sl n (⊲-tr (S→⊲ R) p)
```

## §2 第 0 层的树给层

第 0 层没有节点, 所以世界不起作用 (`drp`).

```agda
drp : ∀ {W W′} → D azero W → D azero W′
drp n0 = n0
drp n1 = n1
drp (x ⨾ y) = drp x ⨾ drp y
drp (nl d) = nl (λ n → drp (d n))
drp (ni () u)
drp (nκ () u)
drp (nw p x) = drp x

pt  : ∀ {W} → A → (ℕ → D azero W) → ℕ → A
sum : ∀ {W} → A → D azero W → A
pt b d zero = b
pt b d (suc n) = sum (pt b d n) (d n)
sum b n0 = b
sum b n1 = asuc b
sum b (x ⨾ y) = sum (sum b x) y
sum b (nl d) = alim (pt b d)
sum b (ni () u)
sum b (nκ () u)
sum b (nw p x) = sum b x

sum-fst : ∀ {W} b (x : D azero W) → b ⊲ sum b x
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni () u)
sum-fst b (nκ () u)
sum-fst b (nw p x) = sum-fst b x

Lg-sum : ∀ {W} b (x : D azero W) → Lg b → Lg (sum b x)
Lg-pt  : ∀ {W} b (d : ℕ → D azero W) n → Lg b → Lg (pt b d n)
Lg-sum b n0 w = w
Lg-sum b n1 w = w
Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
Lg-sum b (ni () u) w
Lg-sum b (nκ () u) w
Lg-sum b (nw p x) w = Lg-sum b x w
Lg-pt b d zero w = w
Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)
```

## §3 $\Omega$

```agda
⊲S : ∀ {c L} → asuc c ⊲ L → Strict c L
⊲S C.self = ss C.self
⊲S (C.suc P) = ss (⊲-tr (C.suc C.self) P)
⊲S (C.lim n P) = sl n (⊲-tr (C.suc C.self) P)

Dif : ∀ b {a L W} → a ⊲ b → b ⊲ L → Lg b → D L W
Dif b C.self q w = n0
Dif (asuc c) (C.suc p) q w = Dif c p (⊲-tr (C.suc C.self) q) w ⨾ ni (⊲S q) (λ _ _ _ → n1)
Dif (alim f) (C.lim n p) q (st , w) =
  Dif (f n) p (⊲-tr (C.lim n C.self) q) (w n) ⨾ nl (λ m → Dif (f (suc (m + n))) (st (m + n)) (⊲-tr (C.lim (suc (m + n)) C.self) q) (w (suc (m + n))))

Ωd : ∀ a {L W} → a ⊲ L → Lg a → D L W
Ωd a q w = n1 ⨾ Dif a (z⊲ a) q w

-- Ω_Ω: 1 接上 ∑_{c≥0} ∑_{z:c} 1
Ω̂₀ : D̂ azero
Ω̂₀ = n1 ⨾ nκ tt (λ {c} _ _ → ni {k = c} C.self (λ _ _ _ → n1))

Ω̂ : ∀ {W} → D̂ W
Ω̂ {W} = nw (z⊲ W) Ω̂₀

tailP : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a n} → a ⊲ f n → ∀ m → a ⊲ f (m + n)
tailP f st p zero = p
tailP f st {n = n} p (suc m) = ⊲-tr (tailP f st p m) (st (m + n))

-- 从 a 走到 b, 分支都放上
Cut : ∀ {Kd : A → A → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W₀ W} (v : ∀ {c} → W₀ ⊲ c → Lg c → D₊ Kd V′ Z c) b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → D₊ Kd V′ Z W
Cut v b C.self ab lb bW = n0
Cut v (asuc c) (C.suc p) ab lb bW =
  Cut v c p ab lb (⊲-tr (C.suc C.self) bW) ⨾ nw (⊲-tr (C.suc C.self) bW) (v (⊲-tr ab p) lb)
Cut v (alim f) (C.lim n p) ab (st , w) bW =
  Cut v (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW) ⨾
  nl (λ m → Cut v (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW))
```

## §4 坐标

`Int`: 低层的坐标 $\delta$ 上走过, 每个位置放 `u`. 只被分支的参数用.

```agda
outV : ∀ ly {W₀ k W′} (r : K ly W₀ k) → V ly r W′ → D k W′
outV (cnt L) R y = outS R y
outV top r y = y

data AccL (k : A) : Set where
  acc : (∀ {j} → Strict j k → AccL j) → AccL k

accS : ∀ a {j} → j ⊲ a → AccL j
accL : ∀ a → AccL a
accS a C.self = accL a
accS (asuc a) (C.suc p) = accS a p
accS (alim f) (C.lim n p) = accS (f n) p
accL azero = acc (λ ())
accL (asuc a) = acc (λ { (ss P) → accS a P })
accL (alim f) = acc (λ { (sl n P) → accS (f n) P })

NZ-S : ∀ {j k} → Strict j k → NZ k
NZ-S (ss P) = tt
NZ-S (sl n P) = tt

Pre : ∀ {k W₀ W} → W₀ ⊲ W → (ℕ → D k W₀) → ℕ → D k W
Pre q₀ d zero = n0
Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

Int : ∀ {ly k W₀ W} → AccL k → D k W₀ → W₀ ⊲ W → Lg W → k ⊲ W → Zy ly → (∀ {W₁ j} → k ⊲ W₁ → Strict j k → K ly W₁ j) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → Dl ly W′) → D k W → Dl ly W
IW  : ∀ {ly k W₀ W} → AccL k → (∀ {c} → W₀ ⊲ c → Lg c → D k c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → Lg W → k ⊲ W → Zy ly → (∀ {W₁ j} → k ⊲ W₁ → Strict j k → K ly W₁ j) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → Dl ly W′) → D k W → Dl ly W

Int ac n0 q₀ lW kW zy mk u w = n0
Int ac n1 q₀ lW kW zy mk u w = u C.self lW w
Int ac (x ⨾ y) q₀ lW kW zy mk u w =
  Int ac x q₀ lW kW zy mk u w ⨾ Int ac y q₀ lW kW zy mk u (w ⨾ nw q₀ x)
Int ac (nl d) q₀ lW kW zy mk u w =
  nl (λ n → Int ac (d n) q₀ lW kW zy mk u (w ⨾ Pre q₀ d n))
Int ac (nw p x) q₀ lW kW zy mk u w = Int ac x (⊲-tr p q₀) lW kW zy mk u w
Int {ly} {k} (acc g) (ni {k = j} R v) q₀ lW kW zy mk u w =
  ni (mk kW R) (λ {W′} p lW′ y →
    Int (acc g) (v (⊲-tr q₀ p) lW′ (inS R (outV ly (mk kW R) y))) C.self lW′ (⊲-tr kW p) zy mk (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Int {cnt k} (g R) (outV ly (mk kW R) y) C.self lW′ (⊲-tr (⊲-tr (S→⊲ R) kW) p) (NZ-S R) (λ _ R′ → Sk R′ (S→⊲ R))
                  (λ p′ l′ z′ → v (⊲-tr (⊲-tr q₀ p) p′) l′ (inS R z′)) n0))
Int {W = W} ac (nκ zz v) q₀ lW kW zy mk u w =
  IW ac v W q₀ C.self lW C.self lW kW zy mk u w ⨾
  nκ zy (λ {c} p lc →
    Int ac (v (⊲-tr q₀ p) lc) C.self lc (⊲-tr kW p) zy mk (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Cut v c (⊲-tr q₀ p) C.self lc C.self))

IW ac v b C.self ap lb bW lW kW zy mk u co = n0
IW ac v (asuc c) (C.suc p) ap lb bW lW kW zy mk u co =
  IW ac v c p ap lb (⊲-tr (C.suc C.self) bW) lW kW zy mk u co ⨾
  Int ac (v (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bW) lW kW zy mk u (co ⨾ Cut v c p ap lb (⊲-tr (C.suc C.self) bW))
IW ac v (alim f) (C.lim n p) ap (st , wl) bW lW kW zy mk u co =
  IW ac v (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bW) lW kW zy mk u co ⨾
  nl (λ m → IW ac v (f (suc (m + n))) (st (m + n)) (⊲-tr ap (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lW kW zy mk u
       (co ⨾ Cut v (f (m + n)) (tailP f st p m) ap (wl (m + n)) (⊲-tr (C.lim (m + n) C.self) bW)))
```

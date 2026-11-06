# 高度是树 (一): 高度, 层, 数据树

> 不含记号. 入口 [HtFeed](HtFeed.lagda.md). 由 [SumHtTree](SumHtTree.lagda.md) 改写, 只改层: [SumHt](SumHt.lagda.md) 的层是一对 $(p,a)$ 加一个顶层, [SumClimb](SumClimb.lagda.md) 是三位加一个顶层; 这里**层就是一棵高度树** $L:H$, 没有坐标, 没有顶层, 没有字典序.
>
> - `H`: 第二数类的布劳威尔树. 四个构造子: $0$, 后继, $\mathbb N$-极限 `hl`, **$\Omega$-极限 `hΩ g`** ($g:A\to H$, 分支存在数据里).
> - `a ⊲[ W ] b`: $a$ 字面地是 $b$ 的第一位置, **走进 $\Omega$-极限的分支时, 分支的坐标 $c$ 要在世界 $W$ 之下** (`hLim : c ⊲ W → …`). 世界是比较的字面公共上界 (壁垒要求). 不带世界的版本不可比, 见 [HtFeedNeg](HtFeedNeg.lagda.md) 的 `no-glob`.
> - `LgH`: 合法: $\mathbb N$-极限相邻项是第一位置 (世界 $0$ 上), $\Omega$-极限的分支沿坐标的第一位置单调 ($c\lhd c'$ 则 $g\,c\lhd_{[c']} g\,c'$), 都遗传.
> - `cmpH`: 同一棵合法高度在同一个世界里的两个第一位置可比. 与 `cmpF` 同形, 多一种情形: 两边走进 $\Omega$-极限的不同分支 $c, c'$, 先在世界里比 $c, c'$ (`cmpF`), 再用单调把小的一边搬进大的一边.
> - 层 $L$ 的节点种类 `StH W k L`: $k$ 严格在 $L$ 之下 (世界 $W$ 里). 分支类型对 $L$ 的结构递归. **停机检查直接通过**: 节点的层总是 $L$ 的结构子项 (分支 $g\,c$ 是 `hΩ g` 的子项), 不要字典序, 不要可达性证明作下标.
>
> 数据树 `D₊` 与 `SumOneTree`, `SumHtTree` 的构造子相同. 合法性仍只有讲和的 `sum-fst`, `Lg-sum` (§5), 无前提, 不提折叠. **没有 `HS`, `Goodᴺ`, `WF`, `ψW`.**
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtFeedTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲; cmpF)
import OCF.Align.CumReadCF as C
```

## §1 高度

```agda
data H : Set where
  hz : H
  hs : H → H
  hl : (ℕ → H) → H
  hΩ : (A → H) → H

infix 4 _⊲[_]_
data _⊲[_]_ : H → A → H → Set where
  hself : ∀ {a W} → a ⊲[ W ] a
  hsuc  : ∀ {a b W} → a ⊲[ W ] b → a ⊲[ W ] hs b
  hlim  : ∀ {a f W} n → a ⊲[ W ] f n → a ⊲[ W ] hl f
  hLim  : ∀ {a g W c} → c ⊲ W → a ⊲[ W ] g c → a ⊲[ W ] hΩ g

⊲ᴴ-tr : ∀ {a b c W} → a ⊲[ W ] b → b ⊲[ W ] c → a ⊲[ W ] c
⊲ᴴ-tr p hself = p
⊲ᴴ-tr p (hsuc q) = hsuc (⊲ᴴ-tr p q)
⊲ᴴ-tr p (hlim n q) = hlim n (⊲ᴴ-tr p q)
⊲ᴴ-tr p (hLim e q) = hLim e (⊲ᴴ-tr p q)

-- 世界变大, 第一位置不变
⊲ᴴ↑ : ∀ {a b W W′} → W ⊲ W′ → a ⊲[ W ] b → a ⊲[ W′ ] b
⊲ᴴ↑ q hself = hself
⊲ᴴ↑ q (hsuc p) = hsuc (⊲ᴴ↑ q p)
⊲ᴴ↑ q (hlim n p) = hlim n (⊲ᴴ↑ q p)
⊲ᴴ↑ q (hLim e p) = hLim (⊲-tr e q) (⊲ᴴ↑ q p)

-- 世界 0 上的第一位置在一切世界上都是
⊲ᴴ0 : ∀ {a b W} → a ⊲[ azero ] b → a ⊲[ W ] b
⊲ᴴ0 {W = W} p = ⊲ᴴ↑ (z⊲ W) p

LgH : H → Set
LgH hz = ⊤
LgH (hs h) = LgH h
LgH (hl f) = (∀ n → f n ⊲[ azero ] f (suc n)) × (∀ n → LgH (f n))
LgH (hΩ g) = (∀ {c c′} → Lg c′ → c ⊲ c′ → g c ⊲[ c′ ] g c′) × (∀ c → Lg c → LgH (g c))

lgH⊲ : ∀ {a b W} → a ⊲[ W ] b → Lg W → LgH b → LgH a
lgH⊲ hself lW l = l
lgH⊲ (hsuc p) lW l = lgH⊲ p lW l
lgH⊲ (hlim n p) lW l = lgH⊲ p lW (proj₂ l n)
lgH⊲ (hLim e p) lW l = lgH⊲ p lW (proj₂ l _ (lg⊲ e lW))

z⊲ᴴ : ∀ {W} L → hz ⊲[ W ] L
z⊲ᴴ hz = hself
z⊲ᴴ (hs b) = hsuc (z⊲ᴴ b)
z⊲ᴴ (hl f) = hlim 0 (z⊲ᴴ (f 0))
z⊲ᴴ {W} (hΩ g) = hLim (z⊲ W) (z⊲ᴴ (g azero))

stepsᴴ : ∀ {f : ℕ → H} → (∀ n → f n ⊲[ azero ] f (suc n)) → ∀ {n m} → n <ᴺ m → f n ⊲[ azero ] f m
stepsᴴ s zero = s _
stepsᴴ s (suc q) = ⊲ᴴ-tr (stepsᴴ s q) (s _)
```

**比较.** 同 `cmpF`: 对上界结构递归. $\Omega$-极限处两个分支的坐标 $c,c'$ 都在世界 $W$ 之下, 由 `cmpF` 比, 再用 `LgH` 的单调把一边搬到另一边的分支里. 比较只在一个世界之内, 只比同一棵高度的两个第一位置.

```agda
cmpH : ∀ {a b L W} → a ⊲[ W ] L → b ⊲[ W ] L → Lg W → LgH L → (b ⊲[ W ] a) ⊎ (a ⊲[ W ] b)
cmpH hself q lW l = inj₁ q
cmpH p hself lW l = inj₂ p
cmpH (hsuc p) (hsuc q) lW l = cmpH p q lW l
cmpH (hlim n p) (hlim m q) lW (st , l) with <ᴺ-dec n m
... | injᵃ n<m = cmpH (⊲ᴴ-tr p (⊲ᴴ0 (stepsᴴ st n<m))) q lW (l m)
... | injᵇ m<n = cmpH p (⊲ᴴ-tr q (⊲ᴴ0 (stepsᴴ st m<n))) lW (l n)
... | injᶜ refl = cmpH p q lW (l n)
cmpH (hLim e p) (hLim e′ q) lW (mo , l) with cmpF e e′ lW
... | inj₁ c′⊲c = cmpH p (⊲ᴴ-tr q (⊲ᴴ↑ e (mo (lg⊲ e lW) c′⊲c))) lW (l _ (lg⊲ e lW))
... | inj₂ c⊲c′ = cmpH (⊲ᴴ-tr p (⊲ᴴ↑ e′ (mo (lg⊲ e′ lW) c⊲c′))) q lW (l _ (lg⊲ e′ lW))
```

## §2 层的节点种类

`StH W k L`: 层 $L$ 在世界 $W$ 里可以有过层 $k$ 的节点. 三种情形对应 $L$ 的三个非零构造子; 进 $\Omega$-极限的分支要坐标在世界之下.

```agda
data StH (W : A) (k : H) : H → Set where
  ss : ∀ {b} → k ⊲[ W ] b → StH W k (hs b)
  sl : ∀ {f} n → k ⊲[ W ] f n → StH W k (hl f)
  sL : ∀ {g c} → c ⊲ W → k ⊲[ W ] g c → StH W k (hΩ g)

S→⊲ᴴ : ∀ {W k L} → StH W k L → k ⊲[ W ] L
S→⊲ᴴ (ss P) = hsuc P
S→⊲ᴴ (sl n P) = hlim n P
S→⊲ᴴ (sL e P) = hLim e P

Kup : ∀ {W W′ k L} → W ⊲ W′ → StH W k L → StH W′ k L
Kup q (ss P) = ss (⊲ᴴ↑ q P)
Kup q (sl n P) = sl n (⊲ᴴ↑ q P)
Kup q (sL e P) = sL (⊲-tr e q) (⊲ᴴ↑ q P)

Sk : ∀ {W j k L} → StH W j k → k ⊲[ W ] L → StH W j L
Sk R hself = R
Sk R (hsuc p) = ss (⊲ᴴ-tr (S→⊲ᴴ R) p)
Sk R (hlim n p) = sl n (⊲ᴴ-tr (S→⊲ᴴ R) p)
Sk R (hLim e p) = sL e (⊲ᴴ-tr (S→⊲ᴴ R) p)

-- 层 0 没有节点, 也没有世界上的和
NZ : H → Set
NZ hz = ⊥
NZ (hs _) = ⊤
NZ (hl _) = ⊤
NZ (hΩ _) = ⊤

NZ-S : ∀ {W k L} → StH W k L → NZ L
NZ-S (ss P) = tt
NZ-S (sl n P) = tt
NZ-S (sL e P) = tt
```

## §3 数据树

与 `SumOneTree` 的 `D₊` 相同, 只是节点的层 $k$ 是一棵高度.

```agda
module _ (Kd : A → H → Set) (V : ∀ {W k} → Kd W k → A → Set) (Zz : Set) where
  infixl 6 _⨾_
  data D₊ : A → Set where
    n0  : ∀ {W} → D₊ W
    n1  : ∀ {W} → D₊ W
    _⨾_ : ∀ {W} → D₊ W → D₊ W → D₊ W
    nl  : ∀ {W} → (ℕ → D₊ W) → D₊ W
    ni  : ∀ {W k} (r : Kd W k) → (∀ {W′} → W ⊲ W′ → Lg W′ → V r W′ → D₊ W′) → D₊ W
    nκ  : ∀ {W} → Zz → (∀ {c} → W ⊲ c → Lg c → D₊ c) → D₊ W
    nw  : ∀ {W₀ W} → W₀ ⊲ W → D₊ W₀ → D₊ W

D  : H → A → Set
Vs : ∀ L {W k} → StH W k L → A → Set
Vc : ∀ b {W a} → a ⊲[ W ] b → A → Set
D L = D₊ (λ W k → StH W k L) (λ R → Vs L R) (NZ L)
Vs (hs b) (ss P) u = Vc b P u
Vs (hl f) (sl n P) u = Vc (f n) P u
Vs (hΩ g) (sL e P) u = Vc (g _) P u
Vc a hself u = D a u
Vc (hs b) (hsuc P) u = Vc b P u
Vc (hl f) (hlim n P) u = Vc (f n) P u
Vc (hΩ g) (hLim e P) u = Vc (g _) P u

outC : ∀ {b W a u} (P : a ⊲[ W ] b) → Vc b P u → D a u
outC hself x = x
outC (hsuc P) x = outC P x
outC (hlim n P) x = outC P x
outC (hLim e P) x = outC P x

inC : ∀ {b W a u} (P : a ⊲[ W ] b) → D a u → Vc b P u
inC hself x = x
inC (hsuc P) x = inC P x
inC (hlim n P) x = inC P x
inC (hLim e P) x = inC P x

outS : ∀ {L W k u} (R : StH W k L) → Vs L R u → D k u
outS (ss P) x = outC P x
outS (sl n P) x = outC P x
outS (sL e P) x = outC P x

inS : ∀ {L W k u} (R : StH W k L) → D k u → Vs L R u
inS (ss P) x = inC P x
inS (sl n P) x = inC P x
inS (sL e P) x = inC P x
```

**层的良基.** 节点总过 $L$ 的结构子项上的层. 对 $L$ 结构递归, 一条定义对一切高度.

```agda
data AccY (L : H) : Set where
  acc : (∀ {W k} → StH W k L → AccY k) → AccY L

accL : ∀ L → AccY L
accC : ∀ b {W a} → a ⊲[ W ] b → AccY a
accL hz = acc (λ ())
accL (hs b) = acc (λ { (ss P) → accC b P })
accL (hl f) = acc (λ { (sl n P) → accC (f n) P })
accL (hΩ g) = acc (λ { (sL e P) → accC (g _) P })
accC a hself = accL a
accC (hs b) (hsuc P) = accC b P
accC (hl f) (hlim n P) = accC (f n) P
accC (hΩ g) (hLim e P) = accC (g _) P

-- 构造子形式, 对变量 L 也能让折叠在节点处计算
accK : ∀ {W k L} → StH W k L → AccY k
accK (ss P) = accC _ P
accK (sl n P) = accC _ P
accK (sL e P) = accC _ P

accᴸ : ∀ {L} → AccY L
accᴸ = acc accK
```

## §4 第 0 层的树给下标

层 $0$ 没有节点, 也没有 `nκ`, 所以世界不起作用. **合法性证明只有这一节.**

```agda
D₀ : A → Set
D₀ = D hz

drp : ∀ {W W′} → D₀ W → D₀ W′
drp n0 = n0
drp n1 = n1
drp (x ⨾ y) = drp x ⨾ drp y
drp (nl d) = nl (λ n → drp (d n))
drp (ni () u)
drp (nκ () u)
drp (nw p x) = drp x

pt  : ∀ {W} → A → (ℕ → D₀ W) → ℕ → A
sum : ∀ {W} → A → D₀ W → A
pt b d zero = b
pt b d (suc n) = sum (pt b d n) (d n)
sum b n0 = b
sum b n1 = asuc b
sum b (x ⨾ y) = sum (sum b x) y
sum b (nl d) = alim (pt b d)
sum b (ni () u)
sum b (nκ () u)
sum b (nw p x) = sum b x

sum-fst : ∀ {W} b (x : D₀ W) → b ⊲ sum b x
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni () u)
sum-fst b (nκ () u)
sum-fst b (nw p x) = sum-fst b x

Lg-sum : ∀ {W} b (x : D₀ W) → Lg b → Lg (sum b x)
Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → Lg b → Lg (pt b d n)
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

## §5 $\Omega_L$

只看 $L$ 的最外一个构造子: $\Omega_0=1$; $\Omega_{b+1}=1+\sum_{z:b}1$; $\Omega_{\lim f}=1+\lim_n\sum_{z:f\,n}1$; $\Omega_{\mathrm{h\Omega}\,g}=1+\sum_{c\ge W}\sum_{z:g\,c}1$. 最后一种就是 `SumOne` 的 `Ω̂₀` 与 `SumHt` 的 `stepH` 的形状, 节点的层是 $g\,c$, $c$ 是世界上的坐标: **折叠到第 0 层时, $c$ 由回灌给出** (`nκ` 的回灌, 见 [HtFeedFold](HtFeedFold.lagda.md)). 不从 $0$ 走到 $L$, 所以没有 `Dif`.

```agda
Ωd : ∀ L {W} → D L W
Ωd hz = n1
Ωd (hs b) = n1 ⨾ ni (ss hself) (λ _ _ _ → n1)
Ωd (hl f) = n1 ⨾ nl (λ n → ni (sl n hself) (λ _ _ _ → n1))
Ωd (hΩ g) = n1 ⨾ nκ tt (λ {c} _ _ → ni (sL {c = c} C.self hself) (λ _ _ _ → n1))
```

## §6 坐标

与 `SumHtTree` 的 `Cut`, `Pre`, `Int`, `IW` 相同. 改了一处: 低层的节点嵌进高层 (`mk`) 不再要坐标层在世界之下的证据, 改要当前世界在节点的世界之上 (`W ⊲ W₁`), 因为节点种类里的 $\Omega$-分支坐标要搬到新世界.

```agda
tailP : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a n} → a ⊲ f n → ∀ m → a ⊲ f (m + n)
tailP f st p zero = p
tailP f st {n = n} p (suc m) = ⊲-tr (tailP f st p m) (st (m + n))

Cut : ∀ {Kd : A → H → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W₀ W} (v : ∀ {c} → W₀ ⊲ c → Lg c → D₊ Kd V′ Z c) b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → D₊ Kd V′ Z W
Cut v b C.self ab lb bW = n0
Cut v (asuc c) (C.suc p) ab lb bW =
  Cut v c p ab lb (⊲-tr (C.suc C.self) bW) ⨾ nw (⊲-tr (C.suc C.self) bW) (v (⊲-tr ab p) lb)
Cut v (alim f) (C.lim n p) ab (st , w) bW =
  Cut v (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW) ⨾
  nl (λ m → Cut v (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW))

Pre : ∀ {Kd : A → H → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W₀ W} → W₀ ⊲ W → (ℕ → D₊ Kd V′ Z W₀) → ℕ → D₊ Kd V′ Z W
Pre q₀ d zero = n0
Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

-- 节点 R (层 k 在 ly 里, 世界 W₀) 之下的节点嵌进 ly
mkOf : ∀ {ly W₀ k} → StH W₀ k ly → ∀ {W} → W₀ ⊲ W → ∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly
mkOf R q p R′ = Sk R′ (S→⊲ᴴ (Kup (⊲-tr q p) R))

Int : ∀ {ly k W₀ W} → AccY k → D k W₀ → W₀ ⊲ W → Lg W → NZ ly →
      (∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → D ly W′) → D k W → D ly W
IW  : ∀ {ly k W₀ W} → AccY k → (∀ {c} → W₀ ⊲ c → Lg c → D k c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ W → Lg W → NZ ly →
      (∀ {W₁ j} → W ⊲ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ⊲ W′ → Lg W′ → D k W′ → D ly W′) → D k W → D ly W

Int ac n0 q₀ lW zy mk u w = n0
Int ac n1 q₀ lW zy mk u w = u C.self lW w
Int ac (x ⨾ y) q₀ lW zy mk u w =
  Int ac x q₀ lW zy mk u w ⨾ Int ac y q₀ lW zy mk u (w ⨾ nw q₀ x)
Int ac (nl d) q₀ lW zy mk u w =
  nl (λ n → Int ac (d n) q₀ lW zy mk u (w ⨾ Pre q₀ d n))
Int ac (nw p x) q₀ lW zy mk u w = Int ac x (⊲-tr p q₀) lW zy mk u w
Int {ly} {k} (acc g) (ni R v) q₀ lW zy mk u w =
  ni (mk C.self (Kup q₀ R)) (λ {W′} p lW′ y →
    Int (acc g) (v (⊲-tr q₀ p) lW′ (inS R (outS (mk C.self (Kup q₀ R)) y))) C.self lW′ zy (λ p′ → mk (⊲-tr p p′)) (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Int (g R) (outS (mk C.self (Kup q₀ R)) y) C.self lW′ (NZ-S R) (mkOf R (⊲-tr q₀ p))
                  (λ p′ l′ z′ → v (⊲-tr (⊲-tr q₀ p) p′) l′ (inS R z′)) n0))
Int {W = W} ac (nκ zz v) q₀ lW zy mk u w =
  IW ac v W q₀ C.self lW C.self lW zy mk u w ⨾
  nκ zy (λ {c} p lc →
    Int ac (v (⊲-tr q₀ p) lc) C.self lc zy (λ p′ → mk (⊲-tr p p′)) (λ p′ → u (⊲-tr p p′))
      (nw p w ⨾ Cut v c (⊲-tr q₀ p) C.self lc C.self))

IW ac v b C.self ap lb bW lW zy mk u co = n0
IW ac v (asuc c) (C.suc p) ap lb bW lW zy mk u co =
  IW ac v c p ap lb (⊲-tr (C.suc C.self) bW) lW zy mk u co ⨾
  Int ac (v (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bW) lW zy mk u (co ⨾ Cut v c p ap lb (⊲-tr (C.suc C.self) bW))
IW ac v (alim f) (C.lim n p) ap (st , wl) bW lW zy mk u co =
  IW ac v (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bW) lW zy mk u co ⨾
  nl (λ m → IW ac v (f (suc (m + n))) (st (m + n)) (⊲-tr ap (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) lW zy mk u
       (co ⨾ Cut v (f (m + n)) (tailP f st p m) ap (wl (m + n)) (⊲-tr (C.lim (m + n) C.self) bW)))
```

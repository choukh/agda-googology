# 两种种类的折叠 (一): 世界, 层, 数据树, 两种走法

> 不含记号. 入口 [HtTowerF](HtTowerF.lagda.md). 由 [HtFeedTree](HtFeedTree.lagda.md) 改写, 层换成 [HtTowerTy](HtTowerTy.lagda.md) 的 `HB S₁`, `S₁ = step S₀`: 两种 $\Omega$-分支, 旧种类 `κA` (坐标 `A`), 新种类 `κH` (坐标是 `H₀ = HB S₀` 的高度).
>
> - **世界** `Wd₂ = A × H₀`: 第一个分量是 `A` 的界, 第二个是 `H₀` 的界 (`Step.W⁺`). 序 `_≤_`: `A` 分量变大, 高度分量在新的 `A` 世界里是第一位置.
> - **数据树** `D₊`: `HtFeedTree` 的七个构造子, 外加一个: `nκ` 升高 `A` 分量 (原样), **`nμ` 升高高度分量** (分支对一切更大的世界). `nκ` 允许在非零层 (`NZ`), `nμ` 允许在 $\ge 2$ 的层 (`NZ₁`): 第 1 层的树 (读成 `H₀` 的那一层) 没有 `nμ`.
> - `Ωd (hΩ κH g) = 1 ⨾ nμ (W′ ↦ 过层 g(W′ 的高度分量) 的节点)`: 与 `nκ` 的那一行同形.
> - **两种走法**: `Cut₀` 沿 `A` 的路径 (原样, 世界成对); **`Cut₁` 沿 `H₀` 的路径**: 后继与 ℕ-极限照 `Cut₀`, 走进旧种类的 $\Omega$-极限 (`hLim`) 时用旧种类的闭包 `nκ`: 坐标 $c$ 上的分支是从 $h(c_0)$ 走到 $h(c)$ 的一段.
> - `Int`, `IW₀`, `IW₁`: 节点的输入改写进上一层, `nμ` 一行用 `IW₁`.
>
> **选择 (值不忠实, 判断):** `Cut₁` 在 `hLim` 处的分支取 "从 $h(c_0)$ 到 $h(c)$ 的整段" (前缀), 不是相邻两点之间的差: 旧种类的分支 $h$ 只单调, 不连续, 相邻差覆盖不了 $[\sup_n h(f\,n), h(\lim f))$. 合法性不受影响.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtTowerFTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
```

## §1 世界与层

```agda
S₁ : KS
S₁ = step S₀

H₀ : Set
H₀ = HB S₀

Ht : Set
Ht = HB S₁

Wd₂ : Set
Wd₂ = Wd S₁

κA κH : K S₁
κA = inj₁ tt
κH = inj₂ tt

infix 4 _≤_
_≤_ : Wd₂ → Wd₂ → Set
_≤_ = _≤w_ S₁

LgW₂ : Wd₂ → Set
LgW₂ = LgW S₁

≤rf : ∀ {W} → W ≤ W
≤rf = C.self , hself

≤tr : ∀ {U V W} → U ≤ V → V ≤ W → U ≤ W
≤tr = ≤w-tr S₁

lgW≤ : ∀ {U V} → U ≤ V → LgW₂ V → LgW₂ U
lgW≤ (p , q) (l₀ , l₁) = lg⊲ p l₀ , lgB⊲ q l₀ l₁

-- 升高 A 分量 / 高度分量
≤A : ∀ {W c} → proj₁ W ⊲ c → W ≤ (c , proj₂ W)
≤A p = p , hself

tailᴮ : ∀ {S} (f : ℕ → HB S) (st : ∀ {w} n → f n ⊲[ w ] f (suc n)) {w a n} → a ⊲[ w ] f n → ∀ m → a ⊲[ w ] f (m + n)
tailᴮ f st p zero = p
tailᴮ f st {n = n} p (suc m) = ⊲ᴮ-tr (tailᴮ f st p m) (st (m + n))

tailP : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a n} → a ⊲ f n → ∀ m → a ⊲ f (m + n)
tailP f st p zero = p
tailP f st {n = n} p (suc m) = ⊲-tr (tailP f st p m) (st (m + n))
```

## §2 层的节点种类

```agda
data StH (W : Wd₂) (k : Ht) : Ht → Set where
  ss : ∀ {b} → k ⊲[ W ] b → StH W k (hs b)
  sl : ∀ {f} n → k ⊲[ W ] f n → StH W k (hl f)
  sL : ∀ {κ g c} → Bd S₁ κ c W → k ⊲[ W ] g c → StH W k (hΩ κ g)

S→⊲ : ∀ {W k L} → StH W k L → k ⊲[ W ] L
S→⊲ (ss P) = hsuc P
S→⊲ (sl n P) = hlim n P
S→⊲ (sL e P) = hLim e P

Kup : ∀ {W W′ k L} → W ≤ W′ → StH W k L → StH W′ k L
Kup q (ss P) = ss (⊲ᴮ↑ q P)
Kup q (sl n P) = sl n (⊲ᴮ↑ q P)
Kup q (sL {κ = κ} e P) = sL (Bd↑ S₁ {κ = κ} q e) (⊲ᴮ↑ q P)

Sk : ∀ {W j k L} → StH W j k → k ⊲[ W ] L → StH W j L
Sk R hself = R
Sk R (hsuc p) = ss (⊲ᴮ-tr (S→⊲ R) p)
Sk R (hlim n p) = sl n (⊲ᴮ-tr (S→⊲ R) p)
Sk R (hLim e p) = sL e (⊲ᴮ-tr (S→⊲ R) p)

NZ : Ht → Set
NZ hz = ⊥
NZ (hs _) = ⊤
NZ (hl _) = ⊤
NZ (hΩ _ _) = ⊤

-- 第 2 层及以上
NZ₁ : Ht → Set
NZ₁ hz = ⊥
NZ₁ (hs b) = NZ b
NZ₁ (hl _) = ⊤
NZ₁ (hΩ _ _) = ⊤

NZ-S : ∀ {W k L} → StH W k L → NZ L
NZ-S (ss P) = tt
NZ-S (sl n P) = tt
NZ-S (sL e P) = tt

nz⊲ : ∀ {W k b} → k ⊲[ W ] b → NZ k → NZ b
nz⊲ hself z = z
nz⊲ (hsuc p) z = tt
nz⊲ (hlim n p) z = tt
nz⊲ (hLim e p) z = tt

nz₁→nz : ∀ k → NZ₁ k → NZ k
nz₁→nz (hs b) _ = tt
nz₁→nz (hl f) _ = tt
nz₁→nz (hΩ κ g) _ = tt

NZ₁-S : ∀ {W k L} → StH W k L → NZ₁ k → NZ₁ L
NZ₁-S {k = k} (ss P) z = nz⊲ P (nz₁→nz k z)
NZ₁-S (sl n P) z = tt
NZ₁-S (sL e P) z = tt
```

## §3 数据树

```agda
module _ (Kd : Wd₂ → Ht → Set) (V : ∀ {W k} → Kd W k → Wd₂ → Set) (Z₀ Z₁ : Set) where
  infixl 6 _⨾_
  data D₊ : Wd₂ → Set where
    n0  : ∀ {W} → D₊ W
    n1  : ∀ {W} → D₊ W
    _⨾_ : ∀ {W} → D₊ W → D₊ W → D₊ W
    nl  : ∀ {W} → (ℕ → D₊ W) → D₊ W
    ni  : ∀ {W k} (r : Kd W k) → (∀ {W′} → W ≤ W′ → LgW₂ W′ → V r W′ → D₊ W′) → D₊ W
    nκ  : ∀ {W} → Z₀ → (∀ {c} → proj₁ W ⊲ c → Lg c → D₊ (c , proj₂ W)) → D₊ W
    nμ  : ∀ {W} → Z₁ → (∀ {W′} → W ≤ W′ → LgW₂ W′ → D₊ W′) → D₊ W
    nw  : ∀ {W₀ W} → W₀ ≤ W → D₊ W₀ → D₊ W

D  : Ht → Wd₂ → Set
Vs : ∀ L {W k} → StH W k L → Wd₂ → Set
Vc : ∀ b {W a} → a ⊲[ W ] b → Wd₂ → Set
D L = D₊ (λ W k → StH W k L) (λ R → Vs L R) (NZ L) (NZ₁ L)
Vs (hs b) (ss P) u = Vc b P u
Vs (hl f) (sl n P) u = Vc (f n) P u
Vs (hΩ κ g) (sL e P) u = Vc (g _) P u
Vc a hself u = D a u
Vc (hs b) (hsuc P) u = Vc b P u
Vc (hl f) (hlim n P) u = Vc (f n) P u
Vc (hΩ κ g) (hLim e P) u = Vc (g _) P u

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

data AccY (L : Ht) : Set where
  acc : (∀ {W k} → StH W k L → AccY k) → AccY L

accL : ∀ L → AccY L
accC : ∀ b {W a} → a ⊲[ W ] b → AccY a
accL hz = acc (λ ())
accL (hs b) = acc (λ { (ss P) → accC b P })
accL (hl f) = acc (λ { (sl n P) → accC (f n) P })
accL (hΩ κ g) = acc (λ { (sL e P) → accC (g _) P })
accC a hself = accL a
accC (hs b) (hsuc P) = accC b P
accC (hl f) (hlim n P) = accC (f n) P
accC (hΩ κ g) (hLim e P) = accC (g _) P

accK : ∀ {W k L} → StH W k L → AccY k
accK (ss P) = accC _ P
accK (sl n P) = accC _ P
accK (sL e P) = accC _ P

accᴸ : ∀ {L} → AccY L
accᴸ = acc accK
```

## §4 第 0 层

```agda
D₀ : Wd₂ → Set
D₀ = D hz

drp : ∀ {W W′} → D₀ W → D₀ W′
drp n0 = n0
drp n1 = n1
drp (x ⨾ y) = drp x ⨾ drp y
drp (nl d) = nl (λ n → drp (d n))
drp (ni () u)
drp (nκ () u)
drp (nμ () u)
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
sum b (nμ () u)
sum b (nw p x) = sum b x

sum-fst : ∀ {W} b (x : D₀ W) → b ⊲ sum b x
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni () u)
sum-fst b (nκ () u)
sum-fst b (nμ () u)
sum-fst b (nw p x) = sum-fst b x

Lg-sum : ∀ {W} b (x : D₀ W) → Lg b → Lg (sum b x)
Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → Lg b → Lg (pt b d n)
Lg-sum b n0 w = w
Lg-sum b n1 w = w
Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
Lg-sum b (ni () u) w
Lg-sum b (nκ () u) w
Lg-sum b (nμ () u) w
Lg-sum b (nw p x) w = Lg-sum b x w
Lg-pt b d zero w = w
Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)
```

## §5 $\Omega_L$

```agda
Ωd : ∀ L {W} → D L W
Ωd hz = n1
Ωd (hs b) = n1 ⨾ ni (ss hself) (λ _ _ _ → n1)
Ωd (hl f) = n1 ⨾ nl (λ n → ni (sl n hself) (λ _ _ _ → n1))
Ωd (hΩ (inj₁ tt) g) = n1 ⨾ nκ tt (λ {c} _ _ → ni (sL {κ = κA} {c = c} C.self hself) (λ _ _ _ → n1))
Ωd (hΩ (inj₂ tt) g) = n1 ⨾ nμ tt (λ {W′} _ _ → ni (sL {κ = κH} {c = proj₂ W′} hself hself) (λ _ _ _ → n1))
```

## §6 两种走法

`Cut₀ v b`: 沿 `A` 的路径从 $a$ 走到 $b$, 依次接上闭包 `nκ` 的分支 $v(c)$ (世界 $(c,\beta)$, 嵌进当前世界). 与 `HtFeedTree.Cut` 相同, 世界成对.

```agda
module _ {Kd : Wd₂ → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wd₂ → Set} {Z₀ Z₁ : Set} where
  DD : Wd₂ → Set
  DD = D₊ Kd V′ Z₀ Z₁

  Cut₀ : ∀ {w β W} (v : ∀ {c} → w ⊲ c → Lg c → DD (c , β)) b {a} → a ⊲ b → w ⊲ a → Lg b → b ⊲ proj₁ W → β ⊲[ proj₁ W ] proj₂ W → DD W
  Cut₀ v b C.self ab lb bW βW = n0
  Cut₀ v (asuc c) (C.suc p) ab lb bW βW =
    Cut₀ v c p ab lb (⊲-tr (C.suc C.self) bW) βW ⨾ nw (⊲-tr (C.suc C.self) bW , βW) (v (⊲-tr ab p) lb)
  Cut₀ v (alim f) (C.lim n p) ab (st , w) bW βW =
    Cut₀ v (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW) βW ⨾
    nl (λ m → Cut₀ v (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) βW)

  Pre : ∀ {W₀ W} → W₀ ≤ W → (ℕ → DD W₀) → ℕ → DD W
  Pre q₀ d zero = n0
  Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)
```

`Cut₁ v b`: 沿 `H₀` 的路径 (在当前的 `A` 世界里) 从 $a$ 走到 $b$, 依次接上闭包 `nμ` 的分支 $v$ (世界的高度分量取路上的点). `hLim` (旧种类的 $\Omega$-极限 $\mathrm{h\Omega}\,h$, 进的是坐标 $c_0$ 的分支): 先走到 $h(c_0)$, 再接一个旧种类的闭包 `nκ`, 坐标 $c$ 上是从 $h(c_0)$ 到 $h(c)$ 的一段 (世界的 `A` 分量升到 $c$; 单调由 `LgB` 给). 递归对 $b$ 结构.

```agda
  Cut₁ : ∀ {W₀ W} → Z₀ → (v : ∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → DD W′) → (b : H₀) {a : H₀} →
         a ⊲[ proj₁ W ] b → proj₂ W₀ ⊲[ proj₁ W ] a → LgB b → b ⊲[ proj₁ W ] proj₂ W → proj₁ W₀ ⊲ proj₁ W → Lg (proj₁ W) → DD W
  Cut₁ z₀ v b hself ap lb bW q l = n0
  Cut₁ z₀ v (hs b) (hsuc P) ap lb bW q l =
    Cut₁ z₀ v b P ap lb (⊲ᴮ-tr (hsuc hself) bW) q l ⨾ nw (C.self , ⊲ᴮ-tr (hsuc hself) bW) (v (q , ⊲ᴮ-tr ap P) (l , lb))
  Cut₁ z₀ v (hl f) (hlim n P) ap (st , lf) bW q l =
    Cut₁ z₀ v (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bW) q l ⨾
    nl (λ m → Cut₁ z₀ v (f (suc (m + n))) (st (m + n)) (⊲ᴮ-tr ap (tailᴮ f st P m)) (lf (suc (m + n))) (⊲ᴮ-tr (hlim (suc (m + n)) hself) bW) q l)
  Cut₁ {W₀} {W} z₀ v (hΩ tt h) (hLim {c = c₀} e P) ap (mo , lh) bW q l =
    Cut₁ z₀ v (h c₀) P ap (lh c₀ (lg⊲ e l)) (⊲ᴮ-tr (hLim e hself) bW) q l ⨾
    nκ z₀ (λ {c} p lc →
      Cut₁ {W = c , proj₂ W} z₀ v (h c) (mo lc (⊲-tr e p) C.self (⊲-tr e p)) (⊲ᴮ↑ {S₀} p (⊲ᴮ-tr ap P)) (lh c lc)
           (⊲ᴮ-tr {S₀} (hLim C.self hself) (⊲ᴮ↑ {S₀} p bW)) (⊲-tr q p) lc)
```

## §7 节点的输入改写进上一层

与 `HtFeedTree.Int`, `IW` 相同, 世界成对; 多一个参数 `zy₁` (把输入层的 `NZ₁` 搬到上一层) 与一行 `nμ`: 先沿高度分量从输入的世界走到当前世界 (`IW₁`), 再接 `nμ`, 分支的前缀是 `Cut₁`.

```agda
mkOf : ∀ {ly W₀ k} → StH W₀ k ly → ∀ {W} → W₀ ≤ W → ∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly
mkOf R q p R′ = Sk R′ (S→⊲ (Kup (≤tr q p) R))

Int : ∀ {ly k W₀ W} → AccY k → D k W₀ → W₀ ≤ W → LgW₂ W → NZ ly → (NZ₁ k → NZ₁ ly) →
      (∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ≤ W′ → LgW₂ W′ → D k W′ → D ly W′) → D k W → D ly W
IW₀ : ∀ {ly k w β W} → AccY k → (∀ {c} → w ⊲ c → Lg c → D k (c , β)) → ∀ b {a} → a ⊲ b → w ⊲ a → Lg b → b ⊲ proj₁ W →
      β ⊲[ proj₁ W ] proj₂ W → LgW₂ W → NZ ly → (NZ₁ k → NZ₁ ly) →
      (∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ≤ W′ → LgW₂ W′ → D k W′ → D ly W′) → D k W → D ly W
IW₁ : ∀ {ly k W₀ W} → AccY k → NZ k → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → D k W′) → (b : H₀) {a : H₀} →
      a ⊲[ proj₁ W ] b → proj₂ W₀ ⊲[ proj₁ W ] a → LgB b → b ⊲[ proj₁ W ] proj₂ W → proj₁ W₀ ⊲ proj₁ W → LgW₂ W → NZ ly → (NZ₁ k → NZ₁ ly) →
      (∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ≤ W′ → LgW₂ W′ → D k W′ → D ly W′) → D k W → D ly W

Int ac n0 q₀ lW zy zy₁ mk u w = n0
Int ac n1 q₀ lW zy zy₁ mk u w = u ≤rf lW w
Int ac (x ⨾ y) q₀ lW zy zy₁ mk u w =
  Int ac x q₀ lW zy zy₁ mk u w ⨾ Int ac y q₀ lW zy zy₁ mk u (w ⨾ nw q₀ x)
Int ac (nl d) q₀ lW zy zy₁ mk u w =
  nl (λ n → Int ac (d n) q₀ lW zy zy₁ mk u (w ⨾ Pre q₀ d n))
Int ac (nw p x) q₀ lW zy zy₁ mk u w = Int ac x (≤tr p q₀) lW zy zy₁ mk u w
Int {ly} {k} (acc g) (ni R v) q₀ lW zy zy₁ mk u w =
  ni (mk ≤rf (Kup q₀ R)) (λ {W′} p lW′ y →
    Int (acc g) (v (≤tr q₀ p) lW′ (inS R (outS (mk ≤rf (Kup q₀ R)) y))) ≤rf lW′ zy zy₁ (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′))
      (nw p w ⨾ Int (g R) (outS (mk ≤rf (Kup q₀ R)) y) ≤rf lW′ (NZ-S R) (NZ₁-S R) (mkOf R (≤tr q₀ p))
                  (λ p′ l′ z′ → v (≤tr (≤tr q₀ p) p′) l′ (inS R z′)) n0))
Int {W = W} ac (nκ zz v) q₀ lW zy zy₁ mk u w =
  IW₀ ac v (proj₁ W) (proj₁ q₀) C.self (proj₁ lW) C.self (proj₂ q₀) lW zy zy₁ mk u w ⨾
  nκ zy (λ {c} p lc →
    Int ac (v (⊲-tr (proj₁ q₀) p) lc) (C.self , ⊲ᴮ↑ {S₀} p (proj₂ q₀)) (lc , proj₂ lW) zy zy₁ (λ p′ → mk (≤tr (≤A p) p′)) (λ p′ → u (≤tr (≤A p) p′))
      (nw (≤A p) w ⨾ Cut₀ v c (⊲-tr (proj₁ q₀) p) C.self lc C.self (⊲ᴮ↑ {S₀} p (proj₂ q₀))))
Int {k = k} {W = W} ac (nμ zz v) q₀ lW zy zy₁ mk u w =
  IW₁ ac (nz₁→nz k zz) v (proj₂ W) (proj₂ q₀) hself (proj₂ lW) hself (proj₁ q₀) lW zy zy₁ mk u w ⨾
  nμ (zy₁ zz) (λ {W′} p lW′ →
    Int ac (v (≤tr q₀ p) lW′) ≤rf lW′ zy zy₁ (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′))
      (nw p w ⨾ Cut₁ (nz₁→nz k zz) v (proj₂ W′) (proj₂ (≤tr q₀ p)) hself (proj₂ lW′) hself (proj₁ (≤tr q₀ p)) (proj₁ lW′)))

IW₀ ac v b C.self ap lb bW βW lW zy zy₁ mk u co = n0
IW₀ ac v (asuc c) (C.suc p) ap lb bW βW lW zy zy₁ mk u co =
  IW₀ ac v c p ap lb (⊲-tr (C.suc C.self) bW) βW lW zy zy₁ mk u co ⨾
  Int ac (v (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bW , βW) lW zy zy₁ mk u (co ⨾ Cut₀ v c p ap lb (⊲-tr (C.suc C.self) bW) βW)
IW₀ ac v (alim f) (C.lim n p) ap (st , wl) bW βW lW zy zy₁ mk u co =
  IW₀ ac v (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bW) βW lW zy zy₁ mk u co ⨾
  nl (λ m → IW₀ ac v (f (suc (m + n))) (st (m + n)) (⊲-tr ap (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) βW lW zy zy₁ mk u
       (co ⨾ Cut₀ v (f (m + n)) (tailP f st p m) ap (wl (m + n)) (⊲-tr (C.lim (m + n) C.self) bW) βW))

IW₁ ac zk v b hself ap lb bW q lW zy zy₁ mk u co = n0
IW₁ ac zk v (hs b) (hsuc P) ap lb bW q lW zy zy₁ mk u co =
  IW₁ ac zk v b P ap lb (⊲ᴮ-tr (hsuc hself) bW) q lW zy zy₁ mk u co ⨾
  Int ac (v (q , ⊲ᴮ-tr ap P) (proj₁ lW , lb)) (C.self , ⊲ᴮ-tr (hsuc hself) bW) lW zy zy₁ mk u
    (co ⨾ Cut₁ zk v b P ap lb (⊲ᴮ-tr (hsuc hself) bW) q (proj₁ lW))
IW₁ ac zk v (hl f) (hlim n P) ap (st , lf) bW q lW zy zy₁ mk u co =
  IW₁ ac zk v (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bW) q lW zy zy₁ mk u co ⨾
  nl (λ m → IW₁ ac zk v (f (suc (m + n))) (st (m + n)) (⊲ᴮ-tr ap (tailᴮ f st P m)) (lf (suc (m + n))) (⊲ᴮ-tr (hlim (suc (m + n)) hself) bW) q lW zy zy₁ mk u
       (co ⨾ Cut₁ zk v (f (m + n)) (tailᴮ f st P m) ap (lf (m + n)) (⊲ᴮ-tr (hlim (m + n) hself) bW) q (proj₁ lW)))
IW₁ {W = W} ac zk v (hΩ tt h) (hLim {c = c₀} e P) ap (mo , lh) bW q lW zy zy₁ mk u co =
  IW₁ ac zk v (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lW))) (⊲ᴮ-tr (hLim e hself) bW) q lW zy zy₁ mk u co ⨾
  nκ zy (λ {c} p lc →
    IW₁ {W = c , proj₂ W} ac zk v (h c) (mo lc (⊲-tr e p) C.self (⊲-tr e p)) (⊲ᴮ↑ {S₀} p (⊲ᴮ-tr ap P)) (lh c lc)
        (⊲ᴮ-tr {S₀} (hLim C.self hself) (⊲ᴮ↑ {S₀} p bW)) (⊲-tr q p) (lc , proj₂ lW) zy zy₁ (λ p′ → mk (≤tr (≤A p) p′)) (λ p′ → u (≤tr (≤A p) p′))
        (nw (≤A p) (co ⨾ Cut₁ zk v (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lW))) (⊲ᴮ-tr (hLim e hself) bW) q (proj₁ lW))))
```

# 事件世界上的真折叠 (一): 层, 世界, 数据树, 离散走法

> 不含记号. 入口 [EvFold](EvFold.lagda.md). 作者选定原话: "事件世界上写真折叠". 由 [HtTowerFTree](HtTowerFTree.lagda.md) 改写, 层的种类换成 "`A` 的种类 + `AdmEvBase.evKS₀` 的带证据种类".
>
> - **事件种类结构** `evK = EvKS₀.evKS₀ 0 b₁ …`: 外层世界 $a_0=0$, 外层界 $b_1=1$ (`hs hz`), 内层世界族取全 0 (`AdmWCoh.wz`). 种类是带证据的坐标 $(c,p)$, $p : c\lhd_{[0]} 1$; 只有两个: $\kappa_0=(0,\mathrm{hsuc\,hself})$, 坐标是 $H_0$ 的高度; $\kappa_1=(1,\mathrm{hself})$, 坐标是 `HB S₁` 的高度 (`Lev 1 = step S₀`). 世界是事件表, 界由 `AdmEvBase` 的重放 `rp` 给出, 原样导入.
> - **层** `Ht = HB T`, `T = plus S₀ evK`: 种类 `κa` (坐标 `A`) 与两个事件种类. 世界 `Wε = A × Hist`, 序是 "`A` 分量第一位置, 事件表前面加事件". `plus` 是两个种类结构的并 (种类取和, 世界取积), 对一切 `S`, `S′` 一条定义.
> - **数据树** `D₊`: `HtTowerFTree` 的七个构造子, `nμ` 换成 **`nε κ`** (事件种类 κ 的闭包, 分支对一切更大的世界). 允许的层: `nε κ₀` 在 $\ge 2$ 的层 (`NZ₁`), `nε κ₁` 在 $\ge 3$ 的层 (`NZ₂`); 由 `ZE` 按种类给出. 读回层 (第 1, 2 层) 的树不含读不回的闭包.
> - **离散走法** `CutE`: 事件世界的序是事件表的后缀关系, 两个相邻的世界之间没有别的世界 ([EvFoldNeg](EvFoldNeg.lagda.md) 的 `between`, 定理). 所以 `HtTowerFTree.Cut₁` 沿高度坐标的连续走法在这里换成**沿新事件逐个走**: 区间 $[H_1, H_2)$ 上依次接分支在 $H_1, e_1∷H_1, \dots$ 处的数据. 不进坐标内部, 不调用别的种类的闭包.
> - `Int`, `IW₀`, `IWε`: 节点的输入改写进上一层, `nε` 一行用 `IWε`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvFoldTree where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.AdmEvBase using (module EvKS₀)
open import OCF.Align.AdmWCoh using (wz; lg-wz)
```

## §1 两个种类结构的并

```agda
module Plus (S S′ : KS) where
  Kp : Set
  Kp = K S ⊎ K S′

  Ep : Kp → Set
  Ep (inj₁ κ) = E S κ
  Ep (inj₂ κ) = E S′ κ

  Wp : Set
  Wp = Wd S × Wd S′

  LgWp : Wp → Set
  LgWp w = LgW S (proj₁ w) × LgW S′ (proj₂ w)

  _≤p_ : Wp → Wp → Set
  w ≤p w′ = _≤w_ S (proj₁ w) (proj₁ w′) × _≤w_ S′ (proj₂ w) (proj₂ w′)

  Bdp : (κ : Kp) → Ep κ → Wp → Set
  Bdp (inj₁ κ) c w = Bd S κ c (proj₁ w)
  Bdp (inj₂ κ) c w = Bd S′ κ c (proj₂ w)

  Prp : (κ : Kp) → Wp → Ep κ → Ep κ → Set
  Prp (inj₁ κ) w c c′ = Pr S κ (proj₁ w) c c′
  Prp (inj₂ κ) w c c′ = Pr S′ κ (proj₂ w) c c′

  Bd↑p : ∀ {κ c w w′} → w ≤p w′ → Bdp κ c w → Bdp κ c w′
  Bd↑p {inj₁ κ} q e = Bd↑ S (proj₁ q) e
  Bd↑p {inj₂ κ} q e = Bd↑ S′ (proj₂ q) e

  cmpKp : ∀ {κ c c′ w} → Bdp κ c w → Bdp κ c′ w → LgWp w → Prp κ w c′ c ⊎ Prp κ w c c′
  cmpKp {inj₁ κ} e e′ lw = cmpK S e e′ (proj₁ lw)
  cmpKp {inj₂ κ} e e′ lw = cmpK S′ e e′ (proj₂ lw)

  LgEp : (κ : Kp) → Ep κ → Set
  LgEp (inj₁ κ) = LgE S κ
  LgEp (inj₂ κ) = LgE S′ κ

  lgBdp : ∀ {κ c w} → Bdp κ c w → LgWp w → LgEp κ c
  lgBdp {inj₁ κ} e lw = lgBd S e (proj₁ lw)
  lgBdp {inj₂ κ} e lw = lgBd S′ e (proj₂ lw)

  botp : (κ : Kp) → Ep κ
  botp (inj₁ κ) = bot S κ
  botp (inj₂ κ) = bot S′ κ

  botBdp : ∀ κ w → Bdp κ (botp κ) w
  botBdp (inj₁ κ) w = botBd S κ (proj₁ w)
  botBdp (inj₂ κ) w = botBd S′ κ (proj₂ w)

plus : KS → KS → KS
plus S S′ = record
  { K = Kp ; E = Ep ; Wd = Wp ; LgW = LgWp ; _≤w_ = _≤p_
  ; ≤w-rf = ≤w-rf S , ≤w-rf S′ ; ≤w-tr = λ p q → ≤w-tr S (proj₁ p) (proj₁ q) , ≤w-tr S′ (proj₂ p) (proj₂ q)
  ; Bd = Bdp ; Pr = Prp ; Bd↑ = Bd↑p ; cmpK = cmpKp ; LgE = LgEp ; lgBd = lgBdp ; bot = botp ; botBd = botBdp }
  where open Plus S S′
```

## §2 事件种类, 层, 世界

```agda
b₁ : HB S₀
b₁ = hs hz

module EK = EvKS₀ azero b₁ tt tt wz lg-wz
open EK using (Kᵉ; Hist; Suf; here; there; suf-tr; Ev; ev; rp) public

evK : KS
evK = EK.evKS₀

T : KS
T = plus S₀ evK

Ht : Set
Ht = HB T

Wε : Set
Wε = Wd T

κa : K T
κa = inj₁ tt

κ₀ κ₁ : Kᵉ
κ₀ = hz , hsuc hself
κ₁ = hs hz , hself

-- 两个事件种类的坐标类型
H₀ : Set
H₀ = HB S₀

H₁ : Set
H₁ = HB (step S₀)

infix 4 _≤_
_≤_ : Wε → Wε → Set
_≤_ = _≤w_ T

LgWε : Wε → Set
LgWε = LgW T

≤rf : ∀ {W} → W ≤ W
≤rf = C.self , here

≤tr : ∀ {U V W} → U ≤ V → V ≤ W → U ≤ W
≤tr = ≤w-tr T

lgW≤ : ∀ {U V} → U ≤ V → LgWε V → LgWε U
lgW≤ (p , q) (l₀ , l₁) = lg⊲ p l₀ , tt

≤A : ∀ {W c} → proj₁ W ⊲ c → W ≤ (c , proj₂ W)
≤A p = p , here

-- 世界的事件分量不进 A-种类的界, A 分量不进事件种类的界 (定义相等)
bd-indepA : ∀ κ x a H → Bd T (inj₂ κ) x (a , H) → Bd evK κ x H
bd-indepA κ x a H e = e

tailP : ∀ (f : ℕ → A) (st : ∀ n → f n ⊲ f (suc n)) {a n} → a ⊲ f n → ∀ m → a ⊲ f (m + n)
tailP f st p zero = p
tailP f st {n = n} p (suc m) = ⊲-tr (tailP f st p m) (st (m + n))
```

## §3 层的节点种类与允许的层

```agda
data StH (W : Wε) (k : Ht) : Ht → Set where
  ss : ∀ {b} → k ⊲[ W ] b → StH W k (hs b)
  sl : ∀ {f} n → k ⊲[ W ] f n → StH W k (hl f)
  sL : ∀ {κ g c} → Bd T κ c W → k ⊲[ W ] g c → StH W k (hΩ κ g)

S→⊲ : ∀ {W k L} → StH W k L → k ⊲[ W ] L
S→⊲ (ss P) = hsuc P
S→⊲ (sl n P) = hlim n P
S→⊲ (sL e P) = hLim e P

Kup : ∀ {W W′ k L} → W ≤ W′ → StH W k L → StH W′ k L
Kup q (ss P) = ss (⊲ᴮ↑ q P)
Kup q (sl n P) = sl n (⊲ᴮ↑ q P)
Kup q (sL {κ = κ} e P) = sL (Bd↑ T {κ = κ} q e) (⊲ᴮ↑ q P)

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

-- 第 3 层及以上
NZ₂ : Ht → Set
NZ₂ hz = ⊥
NZ₂ (hs b) = NZ₁ b
NZ₂ (hl _) = ⊤
NZ₂ (hΩ _ _) = ⊤

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

nz₂→nz₁ : ∀ k → NZ₂ k → NZ₁ k
nz₂→nz₁ (hs b) z = nz₁→nz b z
nz₂→nz₁ (hl f) _ = tt
nz₂→nz₁ (hΩ κ g) _ = tt

nz₁⊲ : ∀ {W k b} → k ⊲[ W ] b → NZ₁ k → NZ₁ b
nz₁⊲ hself z = z
nz₁⊲ {k = k} (hsuc p) z = nz⊲ p (nz₁→nz k z)
nz₁⊲ (hlim n p) z = tt
nz₁⊲ (hLim e p) z = tt

NZ₁-S : ∀ {W k L} → StH W k L → NZ₁ k → NZ₁ L
NZ₁-S {k = k} (ss P) z = nz⊲ P (nz₁→nz k z)
NZ₁-S (sl n P) z = tt
NZ₁-S (sL e P) z = tt

NZ₂-S : ∀ {W k L} → StH W k L → NZ₂ k → NZ₂ L
NZ₂-S {k = k} (ss P) z = nz₁⊲ P (nz₂→nz₁ k z)
NZ₂-S (sl n P) z = tt
NZ₂-S (sL e P) z = tt

-- 事件种类 κ 的闭包允许的层
ZE : Kᵉ → Ht → Set
ZE (_ , hself) L = NZ₂ L
ZE (_ , hsuc hself) L = NZ₁ L

ZE-S : ∀ κ {W k L} → StH W k L → ZE κ k → ZE κ L
ZE-S (_ , hself) R z = NZ₂-S R z
ZE-S (_ , hsuc hself) R z = NZ₁-S R z

zEΩ : ∀ κ {κ′ g} → ZE κ (hΩ κ′ g)
zEΩ (_ , hself) = tt
zEΩ (_ , hsuc hself) = tt

ze0 : ∀ κ → ZE κ hz → ⊥
ze0 (_ , hself) ()
ze0 (_ , hsuc hself) ()

ze1 : ∀ κ → ZE κ (hs hz) → ⊥
ze1 (_ , hself) ()
ze1 (_ , hsuc hself) ()
```

## §4 数据树

```agda
module _ (Kd : Wε → Ht → Set) (V : ∀ {W k} → Kd W k → Wε → Set) (Z₀ : Set) (Zε : Kᵉ → Set) where
  infixl 6 _⨾_
  data D₊ : Wε → Set where
    n0  : ∀ {W} → D₊ W
    n1  : ∀ {W} → D₊ W
    _⨾_ : ∀ {W} → D₊ W → D₊ W → D₊ W
    nl  : ∀ {W} → (ℕ → D₊ W) → D₊ W
    ni  : ∀ {W k} (r : Kd W k) → (∀ {W′} → W ≤ W′ → LgWε W′ → V r W′ → D₊ W′) → D₊ W
    nκ  : ∀ {W} → Z₀ → (∀ {c} → proj₁ W ⊲ c → Lg c → D₊ (c , proj₂ W)) → D₊ W
    nε  : ∀ {W} (κ : Kᵉ) → Zε κ → (∀ {W′} → W ≤ W′ → LgWε W′ → D₊ W′) → D₊ W
    nw  : ∀ {W₀ W} → W₀ ≤ W → D₊ W₀ → D₊ W

D  : Ht → Wε → Set
Vs : ∀ L {W k} → StH W k L → Wε → Set
Vc : ∀ b {W a} → a ⊲[ W ] b → Wε → Set
D L = D₊ (λ W k → StH W k L) (λ R → Vs L R) (NZ L) (λ κ → ZE κ L)
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

## §5 第 0 层

```agda
D₀ : Wε → Set
D₀ = D hz

drp : ∀ {W W′} → D₀ W → D₀ W′
drp n0 = n0
drp n1 = n1
drp (x ⨾ y) = drp x ⨾ drp y
drp (nl d) = nl (λ n → drp (d n))
drp (ni () u)
drp (nκ () u)
drp (nε κ zz u) = ⊥-elim (ze0 κ zz)
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
sum b (nε κ zz u) = ⊥-elim (ze0 κ zz)
sum b (nw p x) = sum b x

sum-fst : ∀ {W} b (x : D₀ W) → b ⊲ sum b x
sum-fst b n0 = C.self
sum-fst b n1 = C.suc C.self
sum-fst b (x ⨾ y) = ⊲-tr (sum-fst b x) (sum-fst (sum b x) y)
sum-fst b (nl d) = C.lim 0 C.self
sum-fst b (ni () u)
sum-fst b (nκ () u)
sum-fst b (nε κ zz u) = ⊥-elim (ze0 κ zz)
sum-fst b (nw p x) = sum-fst b x

Lg-sum : ∀ {W} b (x : D₀ W) → Lg b → Lg (sum b x)
Lg-pt  : ∀ {W} b (d : ℕ → D₀ W) n → Lg b → Lg (pt b d n)
Lg-sum b n0 w = w
Lg-sum b n1 w = w
Lg-sum b (x ⨾ y) w = Lg-sum (sum b x) y (Lg-sum b x w)
Lg-sum b (nl d) w = (λ n → sum-fst (pt b d n) (d n)) , (λ n → Lg-pt b d n w)
Lg-sum b (ni () u) w
Lg-sum b (nκ () u) w
Lg-sum b (nε κ zz u) w = ⊥-elim (ze0 κ zz)
Lg-sum b (nw p x) w = Lg-sum b x w
Lg-pt b d zero w = w
Lg-pt b d (suc n) w = Lg-sum (pt b d n) (d n) (Lg-pt b d n w)
```

## §6 $\Omega_L$

事件种类的 $\Omega$-结点: 闭包 `nε κ`, 分支在更大的世界 $W'$ 处是过层 $g(\text{$W'$ 在 κ 处的界})$ 的节点. 界就是重放 `rp`, 它在自己之下 (`hself`).

```agda
Ωd : ∀ L {W} → D L W
Ωd hz = n1
Ωd (hs b) = n1 ⨾ ni (ss hself) (λ _ _ _ → n1)
Ωd (hl f) = n1 ⨾ nl (λ n → ni (sl n hself) (λ _ _ _ → n1))
Ωd (hΩ (inj₁ tt) g) = n1 ⨾ nκ tt (λ {c} _ _ → ni (sL {κ = κa} {c = c} C.self hself) (λ _ _ _ → n1))
Ωd (hΩ (inj₂ κ) g) =
  n1 ⨾ nε κ (zEΩ κ) (λ {W′} _ _ → ni (sL {κ = inj₂ κ} {c = rp (proj₂ W′) (proj₁ κ) (proj₂ κ)} hself hself) (λ _ _ _ → n1))
```

## §7 两种走法

`Cut₀`: 沿 `A` 的路径, 与 `HtTowerFTree.Cut₀` 相同, 事件分量不动. **`CutE`**: 沿新事件逐个走; 区间 $[H_1,H_2)$, 结果在世界 $W$ ($H_2$ 是 $W$ 的事件表的后缀). 分支取在世界 $(\mathrm{proj}_1 W, H')$ 处, $H'$ 取遍 $H_1$ 到 $H_2$ 之间 (不含 $H_2$) 的事件表.

```agda
module _ {Kd : Wε → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wε → Set} {Z₀ : Set} {Zε : Kᵉ → Set} where
  DD : Wε → Set
  DD = D₊ Kd V′ Z₀ Zε

  Cut₀ : ∀ {w β W} (v : ∀ {c} → w ⊲ c → Lg c → DD (c , β)) b {a} → a ⊲ b → w ⊲ a → Lg b → b ⊲ proj₁ W → Suf β (proj₂ W) → DD W
  Cut₀ v b C.self ab lb bW βW = n0
  Cut₀ v (asuc c) (C.suc p) ab lb bW βW =
    Cut₀ v c p ab lb (⊲-tr (C.suc C.self) bW) βW ⨾ nw (⊲-tr (C.suc C.self) bW , βW) (v (⊲-tr ab p) lb)
  Cut₀ v (alim f) (C.lim n p) ab (st , w) bW βW =
    Cut₀ v (f n) p ab (w n) (⊲-tr (C.lim n C.self) bW) βW ⨾
    nl (λ m → Cut₀ v (f (suc (m + n))) (st (m + n)) (⊲-tr ab (tailP f st p m)) (w (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) βW)

  Pre : ∀ {W₀ W} → W₀ ≤ W → (ℕ → DD W₀) → ℕ → DD W
  Pre q₀ d zero = n0
  Pre q₀ d (suc n) = Pre q₀ d n ⨾ nw q₀ (d n)

  CutE : ∀ {W₀ W H₁ H₂} → (v : ∀ {W′} → W₀ ≤ W′ → LgWε W′ → DD W′) → proj₁ W₀ ⊲ proj₁ W → Lg (proj₁ W) →
         Suf (proj₂ W₀) H₁ → Suf H₁ H₂ → Suf H₂ (proj₂ W) → DD W
  CutE v q l t here r = n0
  CutE v q l t (there e s) r =
    CutE v q l t s (suf-tr (there e here) r) ⨾ nw (C.self , suf-tr (there e here) r) (v (q , suf-tr t s) (l , tt))
```

## §8 节点的输入改写进上一层

与 `HtTowerFTree.Int` 相同, 世界换成 `Wε`; `zy₁` 换成按种类的 `zyE`; `nμ` 一行换成 `nε`: 先沿新事件从输入的世界走到当前世界 (`IWε`), 再接 `nε`, 分支的前缀是 `CutE`.

```agda
mkOf : ∀ {ly W₀ k} → StH W₀ k ly → ∀ {W} → W₀ ≤ W → ∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly
mkOf R q p R′ = Sk R′ (S→⊲ (Kup (≤tr q p) R))

Int : ∀ {ly k W₀ W} → AccY k → D k W₀ → W₀ ≤ W → LgWε W → NZ ly → (∀ κ → ZE κ k → ZE κ ly) →
      (∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ≤ W′ → LgWε W′ → D k W′ → D ly W′) → D k W → D ly W
IW₀ : ∀ {ly k w β W} → AccY k → (∀ {c} → w ⊲ c → Lg c → D k (c , β)) → ∀ b {a} → a ⊲ b → w ⊲ a → Lg b → b ⊲ proj₁ W →
      Suf β (proj₂ W) → LgWε W → NZ ly → (∀ κ → ZE κ k → ZE κ ly) →
      (∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ≤ W′ → LgWε W′ → D k W′ → D ly W′) → D k W → D ly W
IWε : ∀ {ly k W₀ W H₁ H₂} → AccY k → (∀ {W′} → W₀ ≤ W′ → LgWε W′ → D k W′) → proj₁ W₀ ⊲ proj₁ W → Lg (proj₁ W) →
      Suf (proj₂ W₀) H₁ → Suf H₁ H₂ → Suf H₂ (proj₂ W) → LgWε W → NZ ly → (∀ κ → ZE κ k → ZE κ ly) →
      (∀ {W₁ j} → W ≤ W₁ → StH W₁ j k → StH W₁ j ly) →
      (∀ {W′} → W ≤ W′ → LgWε W′ → D k W′ → D ly W′) → D k W → D ly W

Int ac n0 q₀ lW zy zyE mk u w = n0
Int ac n1 q₀ lW zy zyE mk u w = u ≤rf lW w
Int ac (x ⨾ y) q₀ lW zy zyE mk u w =
  Int ac x q₀ lW zy zyE mk u w ⨾ Int ac y q₀ lW zy zyE mk u (w ⨾ nw q₀ x)
Int ac (nl d) q₀ lW zy zyE mk u w =
  nl (λ n → Int ac (d n) q₀ lW zy zyE mk u (w ⨾ Pre q₀ d n))
Int ac (nw p x) q₀ lW zy zyE mk u w = Int ac x (≤tr p q₀) lW zy zyE mk u w
Int {ly} {k} (acc g) (ni R v) q₀ lW zy zyE mk u w =
  ni (mk ≤rf (Kup q₀ R)) (λ {W′} p lW′ y →
    Int (acc g) (v (≤tr q₀ p) lW′ (inS R (outS (mk ≤rf (Kup q₀ R)) y))) ≤rf lW′ zy zyE (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′))
      (nw p w ⨾ Int (g R) (outS (mk ≤rf (Kup q₀ R)) y) ≤rf lW′ (NZ-S R) (λ κ → ZE-S κ R) (mkOf R (≤tr q₀ p))
                  (λ p′ l′ z′ → v (≤tr (≤tr q₀ p) p′) l′ (inS R z′)) n0))
Int {W = W} ac (nκ zz v) q₀ lW zy zyE mk u w =
  IW₀ ac v (proj₁ W) (proj₁ q₀) C.self (proj₁ lW) C.self (proj₂ q₀) lW zy zyE mk u w ⨾
  nκ zy (λ {c} p lc →
    Int ac (v (⊲-tr (proj₁ q₀) p) lc) (C.self , proj₂ q₀) (lc , tt) zy zyE (λ p′ → mk (≤tr (≤A p) p′)) (λ p′ → u (≤tr (≤A p) p′))
      (nw (≤A p) w ⨾ Cut₀ v c (⊲-tr (proj₁ q₀) p) C.self lc C.self (proj₂ q₀)))
Int ac (nε κ zz v) q₀ lW zy zyE mk u w =
  IWε ac v (proj₁ q₀) (proj₁ lW) here (proj₂ q₀) here lW zy zyE mk u w ⨾
  nε κ (zyE κ zz) (λ {W′} p lW′ →
    Int ac (v (≤tr q₀ p) lW′) ≤rf lW′ zy zyE (λ p′ → mk (≤tr p p′)) (λ p′ → u (≤tr p p′))
      (nw p w ⨾ CutE v (proj₁ (≤tr q₀ p)) (proj₁ lW′) here (proj₂ (≤tr q₀ p)) here))

IW₀ ac v b C.self ap lb bW βW lW zy zyE mk u co = n0
IW₀ ac v (asuc c) (C.suc p) ap lb bW βW lW zy zyE mk u co =
  IW₀ ac v c p ap lb (⊲-tr (C.suc C.self) bW) βW lW zy zyE mk u co ⨾
  Int ac (v (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bW , βW) lW zy zyE mk u (co ⨾ Cut₀ v c p ap lb (⊲-tr (C.suc C.self) bW) βW)
IW₀ ac v (alim f) (C.lim n p) ap (st , wl) bW βW lW zy zyE mk u co =
  IW₀ ac v (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bW) βW lW zy zyE mk u co ⨾
  nl (λ m → IW₀ ac v (f (suc (m + n))) (st (m + n)) (⊲-tr ap (tailP f st p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bW) βW lW zy zyE mk u
       (co ⨾ Cut₀ v (f (m + n)) (tailP f st p m) ap (wl (m + n)) (⊲-tr (C.lim (m + n) C.self) bW) βW))

IWε ac v q l t here r lW zy zyE mk u co = n0
IWε ac v q l t (there e s) r lW zy zyE mk u co =
  IWε ac v q l t s (suf-tr (there e here) r) lW zy zyE mk u co ⨾
  Int ac (v (q , suf-tr t s) (l , tt)) (C.self , suf-tr (there e here) r) lW zy zyE mk u (co ⨾ CutE v q l t s (suf-tr (there e here) r))
```

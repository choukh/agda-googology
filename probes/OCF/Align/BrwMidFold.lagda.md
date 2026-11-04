# 中间层是布劳威尔树 (二): 折叠

> 不含记号. 入口 [BrwMid](BrwMid.lagda.md). 由 [SumOneFold](SumOneFold.lagda.md) 改写, 只改第 0 层: **第 0 层的输出是布劳威尔树 `Σ A Lg`**, 差的 `⨾` 换成布劳威尔树的加法 `⊞`, `nl` 换成部分和的极限 `Σlim`, 回灌的层是 $W\boxplus z$, 第一位置是 `⊞-fst`. 高层 ($t>0$) 的差仍是差树. 停机检查直接通过: 合法性的证明只作用在已经算出的输出上, 不调用折叠.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwMidFold where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; cmpF; Tg; S→⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_⊞_)
open import OCF.Align.SumOneTree hiding (acc)
open import OCF.Align.BrwMidZero using (L₀; 𝟎; 𝟏; _+ᴸ_; Σlim; ⊞-fst; Lg-⊞; dif)
```

## §0 输出: 第 0 层是布劳威尔树

`Out t W`: 目标 $t$ 上的差. $t=0$ 时是 `Σ A Lg` (布劳威尔树与它的字面合法性), 别的层仍是差树. 加法 `+ᴸ`, 极限 `Σlim` 都是 [BrwMidZero](BrwMidZero.lagda.md) 的, 合法性由 `⊞-fst` 给. **第 0 层的输出要再当输入走时 (链的起点, 也就是 $\Omega_1$ 的分支), 用 `dif` 把树读成差:** 它要的 `Lg` 就是树自带的那一个.

```agda
Out : A → A → Set
Out azero W = L₀
Out (asuc b) W = D (asuc b) W
Out (alim f) W = D (alim f) W

0ᵗ : ∀ {t W} → Out t W
0ᵗ {t = azero} = 𝟎
0ᵗ {t = asuc b} = n0
0ᵗ {t = alim f} = n0

infixl 6 _⨾ᵗ_
_⨾ᵗ_ : ∀ {t W} → Out t W → Out t W → Out t W
_⨾ᵗ_ {t = azero} x y = x +ᴸ y
_⨾ᵗ_ {t = asuc b} x y = x ⨾ y
_⨾ᵗ_ {t = alim f} x y = x ⨾ y

nlᵗ : ∀ {t W} → (ℕ → Out t W) → Out t W
nlᵗ {t = azero} F = Σlim 𝟎 F
nlᵗ {t = asuc b} F = nl F
nlᵗ {t = alim f} F = nl F

nwᵗ : ∀ {t W W′} → W ⊲ W′ → Out t W → Out t W′
nwᵗ {t = azero} q x = x
nwᵗ {t = asuc b} q x = nw q x
nwᵗ {t = alim f} q x = nw q x

-- ψ(a+1) - ψ(a) = ψ(a)·ω
Sᵗ : ∀ {t W} → Out t W → Out t W
Sᵗ {t = azero} c = Σlim 𝟎 (λ _ → c)
Sᵗ {t = asuc b} c = nl (λ _ → c)
Sᵗ {t = alim f} c = nl (λ _ → c)

Ωᵗ : ∀ t {W} → t ⊲ W → Lg t → Out t W
Ωᵗ azero q lt = 𝟏
Ωᵗ (asuc b) q lt = Ωd (asuc b) C.self lt
Ωᵗ (alim f) q lt = Ωd (alim f) C.self lt

-- 输出读回输入: 第 0 层用 dif
toD : ∀ {t W} → Lg t → Out t W → D t W
toD {t = azero} lt (b , lb) = dif b (z⊲ b) lb
toD {t = asuc b} lt x = x
toD {t = alim f} lt x = x

inD : ∀ {k t W} → Strict k t → D t W → Out t W
inD (ss P) x = x
inD (sl n P) x = x

outD : ∀ {k t W} → Strict k t → Out t W → D t W
outD (ss P) x = x
outD (sl n P) x = x
```


## §1 状态

```agda
wm : ∀ {t W} → Tg t W → A
wm {W = W} (inj₁ _) = W
wm {t} (inj₂ _) = t

W⊲wm : ∀ {t W} (τ : Tg t W) → W ⊲ wm τ
W⊲wm (inj₁ _) = C.self
W⊲wm (inj₂ q) = q

t⊲wm : ∀ {t W} (τ : Tg t W) → t ⊲ wm τ
t⊲wm (inj₁ q) = q
t⊲wm (inj₂ _) = C.self

Lg-wm : ∀ {t W} (τ : Tg t W) → Lg W → Lg t → Lg (wm τ)
Lg-wm (inj₁ _) lW lt = lW
Lg-wm (inj₂ _) lW lt = lt

record Df (W : A) : Set where
  constructor df
  field
    yc : ∀ {t} (τ : Tg t W) → Lg t → Out t (wm τ)
    ŷ  : D̂ W
open Df public

record St (W : A) : Set where
  constructor st
  field
    d : Df W
    z : L₀
open St public

zeroD : ∀ {W} → Df W
zeroD = df (λ τ lt → 0ᵗ) n0

infixl 6 _⨾ᴰ_ _⊕_
_⨾ᴰ_ : ∀ {W} → Df W → Df W → Df W
a ⨾ᴰ b = df (λ τ lt → yc a τ lt ⨾ᵗ yc b τ lt) (ŷ a ⨾ ŷ b)

nlᴰ : ∀ {W} → (ℕ → Df W) → Df W
nlᴰ F = df (λ τ lt → nlᵗ (λ n → yc (F n) τ lt)) (nl (λ n → ŷ (F n)))

_⊕_ : ∀ {W} → St W → Df W → St W
_⊕_ {W} Y Δ = st (d Y ⨾ᴰ Δ) (z Y +ᴸ yc Δ (inj₁ (z⊲ W)) tt)

-- 世界变大. 第 0 层的差从新世界重新算
cv : ∀ {W W′} → W ⊲ W′ → Lg W′ → St W → St W′
cv {W} {W′} q lW′ Y = st (df ycv (nw q (ŷ (d Y)))) 𝟎
  where
  ycv : ∀ {t} (τ : Tg t W′) → Lg t → Out t (wm τ)
  ycv {t} (inj₁ τ₁) lt with cmpF q τ₁ lW′
  ... | inj₁ t⊲W = nwᵗ q (yc (d Y) (inj₁ t⊲W) lt)
  ... | inj₂ W⊲t = nwᵗ τ₁ (yc (d Y) (inj₂ W⊲t) lt)
  ycv (inj₂ τ₂) lt = yc (d Y) (inj₂ (⊲-tr q τ₂)) lt

Step : ∀ {W} → St W → Df W
Step Y = df (λ {t} τ lt → Sᵗ (Ωᵗ t (t⊲wm τ) lt ⨾ᵗ yc (d Y) τ lt)) (nl (λ _ → Ω̂ ⨾ ŷ (d Y)))

Ig : Ly → A → Set
Ig ly W = ∀ {W′} → W ⊲ W′ → Lg W′ → Dl ly W′ → St W′ → Df W′

Ig↾ : ∀ {ly W W′} → W ⊲ W′ → Ig ly W → Ig ly W′
Ig↾ p A₀ p′ = A₀ (⊲-tr p p′)

data Rk′ (k t : A) : Set where
  keep : Strict k t → Rk′ k t
  rise : t ⊲ k → Rk′ k t

rkS : ∀ {k t} → k ⊲ t → Rk′ k t
rkS C.self = rise C.self
rkS (C.suc p) = keep (ss p)
rkS (C.lim n p) = keep (sl n p)

rkT : ∀ {k t W} → k ⊲ W → Tg t W → Lg W → Rk′ k t
rkT kW (inj₁ τ) lW with cmpF kW τ lW
... | inj₁ t⊲k = rise t⊲k
... | inj₂ k⊲t = rkS k⊲t
rkT kW (inj₂ τ) lW = rkS (⊲-tr kW τ)

-- nκ 回灌的一格
record Cl (W W₀ : A) (ly : Ly) : Set where
  constructor mkCl
  field
    v  : A
    lv : Lg v
    wv : W ⊲ v
    a  : A
    ap : W₀ ⊲ a
    av : a ⊲ v
    Sv : St v
    co : Dl ly v
open Cl public

mkOf : ∀ ly {W₀ k} → K ly W₀ k → ∀ {W₁ j} → k ⊲ W₁ → Strict j k → K ly W₁ j
mkOf (cnt L) R₀ _ R = Sk R (S→⊲ R₀)
mkOf top r kW R = ⊲-tr (S→⊲ R) kW

zyOf : ∀ ly {W₀ k} → K ly W₀ k → Zy ly
zyOf (cnt L) R₀ = NZ-S R₀
zyOf top r = tt

data AccY (ly : Ly) : Set where
  acc : (∀ {W k} → K ly W k → AccY (cnt k)) → AccY ly

accCs : ∀ a {j} → j ⊲ a → AccY (cnt j)
accCn : ∀ a → AccY (cnt a)
accCs a C.self = accCn a
accCs (asuc a) (C.suc p) = accCs a p
accCs (alim f) (C.lim n p) = accCs (f n) p
accCn azero = acc (λ ())
accCn (asuc a) = acc (λ { (ss P) → accCs a P })
accCn (alim f) = acc (λ { (sl n P) → accCs (f n) P })

accTop : AccY top
accTop = acc (λ {_} {k} _ → accCn k)
```

## §2 折叠

```agda
Run   : ∀ {ly W₀ W} → AccY ly → Dl ly W₀ → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
Rpt   : ∀ {ly W₀ W} → AccY ly → (ℕ → Dl ly W₀) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → ℕ → Dl ly W × St W
RunNi : ∀ {ly W₀ W k} → AccY ly → AccY (cnt k) → (r : K ly W₀ k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
Ai    : ∀ {ly W₀ W k} → AccY ly → (r : K ly W₀ k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → k ⊲ W → LW ly W → Ig ly W → Dl ly W → Ig (cnt k) W
Chn   : ∀ {k W} → AccY (cnt k) → k ⊲ W → Lg W → Lg k → Ig (cnt k) W → St W → ℕ → D k W × (D k W × St W)
RKi   : ∀ {ly W₀ W k t} → AccY ly → AccY (cnt k) → (r : K ly W₀ k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → (τ : Tg t W) → Lg t → Rk′ k t → Out t (wm τ)
BNi   : ∀ {ly W₀ W k W′} → AccY ly → AccY (cnt k) → (r : K ly W₀ k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → k ⊲ W → W ⊲ W′ → Lg W′ → D k W′ → Df W′
Walk  : ∀ {ly W₀ V₁} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ V₁ → Lg V₁ → LW ly V₁ → Ig ly V₁ → Dl ly V₁ → St V₁ → Df V₁
WRp   : ∀ {ly W₀ V₁ a n} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) → a ⊲ f n → W₀ ⊲ a → (∀ m → f m ⊲ V₁) → Lg V₁ → LW ly V₁ → Ig ly V₁ → Dl ly V₁ → St V₁ → ℕ → Dl ly V₁ × St V₁
RunK  : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
RKy   : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → ∀ t (τ : Tg t W) → Lg t → Out t (wm τ)
Kp    : ∀ {ly W₀ W W⁺} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → W ⊲ W⁺ → Lg W⁺ → Df W⁺
Kb    : ∀ {ly W₀ W W⁺ c} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → W ⊲ W⁺ → Lg W⁺ → W⁺ ⊲ c → Lg c → Df c
κc    : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → ℕ → Cl W W₀ ly
κΔ    : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → LW ly W → Ig ly W → (c : Cl W W₀ ly) → Df (v c)

Run ac n0 q₀ lW ll A₀ w Y = zeroD
Run ac n1 q₀ lW ll A₀ w Y = A₀ C.self lW w Y
Run ac (x ⨾ y) q₀ lW ll A₀ w Y =
  Run ac x q₀ lW ll A₀ w Y ⨾ᴰ Run ac y q₀ lW ll A₀ (w ⨾ nw q₀ x) (Y ⊕ Run ac x q₀ lW ll A₀ w Y)
Run ac (nl F) q₀ lW ll A₀ w Y =
  nlᴰ (λ n → Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))
Run ac (nw p x) q₀ lW ll A₀ w Y = Run ac x (⊲-tr p q₀) lW ll A₀ w Y
Run (acc f) (ni r u) q₀ lW ll A₀ w Y = RunNi (acc f) (f r) r u q₀ lW ll A₀ w Y
Run ac (nκ zz u) q₀ lW ll A₀ w Y = RunK ac u q₀ lW ll A₀ w Y

Rpt ac F q₀ lW ll A₀ w Y zero = w , Y
Rpt ac F q₀ lW ll A₀ w Y (suc n) =
  (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n) ⨾ nw q₀ (F n)) ,
  (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n) ⊕ Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))

RunNi {ly} ac ac′ r u q₀ lW ll A₀ w Y =
  df (λ {t} τ lt → RKi ac ac′ r u q₀ lW ll A₀ w Y τ lt (rkT kW τ lW))
     (ni kW (λ p lW′ z → ŷ (BNi ac ac′ r u q₀ ll A₀ w Y kW p lW′ z)))
  where
  kW = kk ly r q₀ ll

Ai {ly} {k = k} ac r u q₀ kW ll A₀ w {W′} p lW′ z Y′ =
  Run ac (u (⊲-tr q₀ p) lW′ (inV ly r z)) C.self lW′ (LW↑ ly p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int (accL k) z C.self lW′ (⊲-tr kW p) (zyOf ly r) (mkOf ly r) (λ p′ l′ z′ → u (⊲-tr (⊲-tr q₀ p) p′) l′ (inV ly r z′)) n0) Y′

BNi {ly} ac ac′ r u q₀ ll A₀ w Y kW p lW′ z =
  Ai ac r u q₀ kW ll A₀ w p lW′ z
    (cv p lW′ Y ⊕ Run ac′ z C.self lW′ (⊲-tr kW p) (Ig↾ p (Ai ac r u q₀ kW ll A₀ w)) n0 (cv p lW′ Y))

Chn ac′ kW lW lk A² Y zero = n0 , (toD lk (yc (d Y) (inj₁ kW) lk) , Y)
Chn ac′ kW lW lk A² Y (suc n) =
  (proj₁ (Chn ac′ kW lW lk A² Y n) ⨾ proj₁ (proj₂ (Chn ac′ kW lW lk A² Y n))) ,
  (toD lk (yc (Run ac′ (proj₁ (proj₂ (Chn ac′ kW lW lk A² Y n))) C.self lW kW A² (proj₁ (Chn ac′ kW lW lk A² Y n)) (proj₂ (proj₂ (Chn ac′ kW lW lk A² Y n)))) (inj₁ kW) lk) ,
   (proj₂ (proj₂ (Chn ac′ kW lW lk A² Y n)) ⊕ Run ac′ (proj₁ (proj₂ (Chn ac′ kW lW lk A² Y n))) C.self lW kW A² (proj₁ (Chn ac′ kW lW lk A² Y n)) (proj₂ (proj₂ (Chn ac′ kW lW lk A² Y n)))))

RKi {ly} {t = t} ac ac′ r u q₀ lW ll A₀ w Y τ lt (keep R) = inD R (
  ni R (λ {W′} p lW′ y → outD R (
    yc (BNi ac ac′ r u q₀ ll A₀ w Y (kk ly r q₀ ll) (⊲-tr (W⊲wm τ) p) lW′ (outS R y)) (inj₁ (⊲-tr (t⊲wm τ) p)) lt)))
RKi {ly} {k = k} ac ac′ r u q₀ lW ll A₀ w Y τ lt (rise _) =
  nlᵗ (λ n →
    yc (Run ac′ (proj₁ (proj₂ (C′ n))) C.self lW kW A² (proj₁ (C′ n)) (proj₂ (proj₂ (C′ n)))) τ lt)
  where
  kW = kk ly r q₀ ll
  A² = Ai ac r u q₀ kW ll A₀ w
  C′ = Chn ac′ kW lW (lg⊲ kW lW) A² Y

Walk ac u b C.self ap lb bV lV ll A₀ co Y = zeroD
Walk ac u (asuc c) (C.suc p) ap lb bV lV ll A₀ co Y =
  Walk ac u c p ap lb (⊲-tr (C.suc C.self) bV) lV ll A₀ co Y ⨾ᴰ
  Run ac (u (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bV) lV ll A₀ (co ⨾ Cut u c p ap lb (⊲-tr (C.suc C.self) bV))
    (Y ⊕ Walk ac u c p ap lb (⊲-tr (C.suc C.self) bV) lV ll A₀ co Y)
Walk ac u (alim f) {a} (C.lim n p) ap (stp , wl) bV lV ll A₀ co Y =
  Walk ac u (f n) p ap (wl n) (fV n) lV ll A₀ co Y ⨾ᴰ
  nlᴰ (λ m → Walk ac u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) lV ll A₀
        (proj₁ (R′ m)) (proj₂ (R′ m)))
  where
  fV : ∀ m → f m ⊲ _
  fV m = ⊲-tr (C.lim m C.self) bV
  R′ = WRp ac u f stp wl p ap fV lV ll A₀
         (co ⨾ Cut u (f n) p ap (wl n) (fV n))
         (Y ⊕ Walk ac u (f n) p ap (wl n) (fV n) lV ll A₀ co Y)

WRp ac u f stp wl p ap fV lV ll A₀ co Y zero = co , Y
WRp {n = n} ac u f stp wl p ap fV lV ll A₀ co Y (suc m) =
  (proj₁ (R′ m) ⨾ Cut u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n)))) ,
  (proj₂ (R′ m) ⊕ Walk ac u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) lV ll A₀ (proj₁ (R′ m)) (proj₂ (R′ m)))
  where
  R′ = WRp ac u f stp wl p ap fV lV ll A₀ co Y

RunK {ly} {W₀} ac u q₀ lW ll A₀ w Y =
  df (λ {t} τ lt → RKy ac u q₀ lW ll A₀ w Y t τ lt)
     (ŷ (Kp ac u q₀ ll A₀ w Y C.self lW) ⨾ nκ tt (λ {c} p lc → ŷ (Kb ac u q₀ ll A₀ w Y C.self lW p lc)))

Kp {ly} {W⁺ = W⁺} ac u q₀ ll A₀ w Y wu lW⁺ =
  Walk ac u W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self lW⁺ (LW↑ ly wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu lW⁺ Y)

Kb {ly} {W⁺ = W⁺} {c = c} ac u q₀ ll A₀ w Y wu lW⁺ p lc =
  Run ac (u (⊲-tr q₀ (⊲-tr wu p)) lc) C.self lc (LW↑ ly (⊲-tr wu p) ll) (Ig↾ (⊲-tr wu p) A₀)
    (nw p co₊ ⨾ Cut u c p (⊲-tr q₀ wu) lc C.self)
    (cv p lc S₊ ⊕ Walk ac u c p (⊲-tr q₀ wu) lc C.self lc (LW↑ ly (⊲-tr wu p) ll) (Ig↾ (⊲-tr wu p) A₀) (nw p co₊) (cv p lc S₊))
  where
  S₊ = cv wu lW⁺ Y ⊕ Kp ac u q₀ ll A₀ w Y wu lW⁺
  co₊ = nw wu w ⨾ Cut u W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self

RKy ac u q₀ lW ll A₀ w Y azero τ lt =
  Σlim 𝟎 (λ n → yc (κΔ ac u ll A₀ (κc ac u q₀ lW ll A₀ w Y n)) (inj₁ (z⊲ (v (κc ac u q₀ lW ll A₀ w Y n)))) tt)
RKy ac u q₀ lW ll A₀ w Y (asuc b) τ lt =
  yc (Kp ac u q₀ ll A₀ w Y (W⊲wm τ) (Lg-wm τ lW lt)) (inj₁ (t⊲wm τ)) lt ⨾
  nκ tt (λ {c} p lc → yc (Kb ac u q₀ ll A₀ w Y (W⊲wm τ) (Lg-wm τ lW lt) p lc) (inj₁ (⊲-tr (t⊲wm τ) p)) lt)
RKy ac u q₀ lW ll A₀ w Y (alim f) τ lt =
  yc (Kp ac u q₀ ll A₀ w Y (W⊲wm τ) (Lg-wm τ lW lt)) (inj₁ (t⊲wm τ)) lt ⨾
  nκ tt (λ {c} p lc → yc (Kb ac u q₀ ll A₀ w Y (W⊲wm τ) (Lg-wm τ lW lt) p lc) (inj₁ (⊲-tr (t⊲wm τ) p)) lt)

κc {W₀ = W₀} {W = W} ac u q₀ lW ll A₀ w Y zero =
  mkCl (W ⊞ proj₁ (z Y)) (Lg-⊞ W _ lW (proj₂ (z Y))) (⊞-fst W _) W₀ C.self (⊲-tr q₀ (⊞-fst W _))
     (cv (⊞-fst W _) (Lg-⊞ W _ lW (proj₂ (z Y))) Y) (nw (⊞-fst W _) w)
κc ac u q₀ lW ll A₀ w Y (suc n) =
  mkCl (v c ⊞ proj₁ d₀) (Lg-⊞ (v c) _ (lv c) (proj₂ d₀)) (⊲-tr (wv c) q) (v c) (⊲-tr (ap c) (av c)) q
     (cv q (Lg-⊞ (v c) _ (lv c) (proj₂ d₀)) (Sv c ⊕ Δ))
     (nw q (co c ⨾ Cut u (v c) (av c) (ap c) (lv c) C.self))
  where
  c = κc ac u q₀ lW ll A₀ w Y n
  Δ = κΔ ac u ll A₀ c
  d₀ = yc Δ (inj₁ (z⊲ (v c))) tt
  q = ⊞-fst (v c) (proj₁ d₀)

κΔ {ly} ac u ll A₀ c =
  Walk ac u (v c) (av c) (ap c) (lv c) C.self (lv c) (LW↑ ly (wv c) ll) (Ig↾ (wv c) A₀) (co c) (Sv c)
```

## §3 闭项

世界从 $1$ 起: 第 0 层的输出从 $\Omega_0=1$ 开始. $\psi_0(\Omega_\Omega)$ 走 `Ω̂₀`; 再往上是第 $\Omega_\Omega$ 层上的链: 坐标 $\delta_0$ 是状态在顶层的差, 每一段里每一格做一次 `Step`.

```agda
one : A
one = asuc azero

A₁ : ∀ {W} → Ig top W
A₁ p lW′ _ Y = Step Y

Y₀ : St one
Y₀ = st zeroD 𝟎

Δ₀ : Df one
Δ₀ = Run accTop Ω̂₀ (z⊲ one) tt tt A₁ n0 Y₀

Y₁ : St one
Y₁ = Y₀ ⊕ Δ₀

τ₀ : Tg azero one
τ₀ = inj₁ (z⊲ one)

ΨΩ : L₀
ΨΩ = 𝟏 +ᴸ yc Δ₀ τ₀ tt

Chŷ : ℕ → D̂ one × (D̂ one × St one)
Chŷ zero = n0 , (ŷ (d Y₁) , Y₁)
Chŷ (suc n) =
  (proj₁ (Chŷ n) ⨾ proj₁ (proj₂ (Chŷ n))) ,
  (ŷ (Run accTop (proj₁ (proj₂ (Chŷ n))) C.self tt tt A₁ (proj₁ (Chŷ n)) (proj₂ (proj₂ (Chŷ n)))) ,
   (proj₂ (proj₂ (Chŷ n)) ⊕ Run accTop (proj₁ (proj₂ (Chŷ n))) C.self tt tt A₁ (proj₁ (Chŷ n)) (proj₂ (proj₂ (Chŷ n)))))

Δₙ : ℕ → Df one
Δₙ n = Run accTop (proj₁ (proj₂ (Chŷ n))) C.self tt tt A₁ (proj₁ (Chŷ n)) (proj₂ (proj₂ (Chŷ n)))

E₁ : ℕ → L₀
E₁ n = yc (Δₙ n) τ₀ tt

ΨΩ+1 : L₀
ΨΩ+1 = ΨΩ +ᴸ Σlim 𝟎 E₁

T₀ T₁ : A
T₀ = proj₁ ΨΩ
T₁ = proj₁ ΨΩ+1

Lg-T₀ : Lg T₀
Lg-T₀ = proj₂ ΨΩ

Lg-T₁ : Lg T₁
Lg-T₁ = proj₂ ΨΩ+1
```

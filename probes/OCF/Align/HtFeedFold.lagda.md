# 高度是树 (二): 折叠

> 不含记号. 入口 [HtFeed](HtFeed.lagda.md). 由 [SumHtFold](SumHtFold.lagda.md) 改写, 结构不变: 状态记每个目标的差, 输入走一段返回差; 节点低于目标就保留, 否则上升成链; `nκ` 在第 $0$ 层回灌, 在别的层保留. 改了两件:
>
> 1. **目标是一棵高度 $t$ 加一个字面的世界 $m$** (`Tg W t m`: $W\lhd m$, $t\lhd_{[m]}\Lambda$). $\Lambda$ 是模块参数: 这次折叠的最高的层. 一切层都是 $\Lambda$ 的第一位置, 所以被比较的两个层总有字面公共上界 $\Lambda$, 它们的 $\Omega$-分支坐标总有字面公共上界 $m$.
> 2. **节点与目标的比较** (`rkT`) 是一次 `cmpH`, 不分高度与下标, 没有字典序.
>
> `S`: 一步, 模块参数, 闭项里取 $S=\cdot\omega$ ([HtFeedClosed](HtFeedClosed.lagda.md)). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtFeedTree using (D₊; H; LgH)
open import OCF.Align.CumReadCF using (A)
module OCF.Align.HtFeedFold (S : ∀ {Kd : A → H → Set} {V′ : ∀ {W k} → Kd W k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W)
  (Λ : H) (lΛ : LgH Λ) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtFeedTree
```

## §1 状态

```agda
LW : H → A → Set
LW L W = L ⊲[ W ] Λ

record Tg (W : A) (t : H) (m : A) : Set where
  constructor tg
  field
    wm : W ⊲ m
    tm : t ⊲[ m ] Λ
    lm : Lg m
open Tg public

tg↑ : ∀ {W W′ t m} → W ⊲ W′ → Tg W′ t m → Tg W t m
tg↑ q T = tg (⊲-tr q (wm T)) (tm T) (lm T)

τ₀ : ∀ {W} → Lg W → Tg W hz W
τ₀ lW = tg C.self (z⊲ᴴ Λ) lW

record Df (W : A) : Set where
  constructor df
  field
    yc : ∀ {t m} → Tg W t m → D t m
open Df public

record St (W : A) : Set where
  constructor st
  field
    d : Df W
    z : D₀ W
open St public

zeroD : ∀ {W} → Df W
zeroD = df (λ T → n0)

infixl 6 _⨾ᴰ_
_⨾ᴰ_ : ∀ {W} → Df W → Df W → Df W
a ⨾ᴰ b = df (λ T → yc a T ⨾ yc b T)

nlᴰ : ∀ {W} → (ℕ → Df W) → Df W
nlᴰ F = df (λ T → nl (λ n → yc (F n) T))

_⊕⟨_⟩_ : ∀ {W} → St W → Lg W → Df W → St W
Y ⊕⟨ lW ⟩ Δ = st (d Y ⨾ᴰ Δ) (z Y ⨾ yc Δ (τ₀ lW))

cv : ∀ {W W′} → W ⊲ W′ → St W → St W′
cv q Y = st (df (λ T → yc (d Y) (tg↑ q T))) n0

Step : ∀ {W} → St W → Df W
Step Y = df (λ {t} T → S (Ωd t ⨾ yc (d Y) T))

Ig : H → A → Set
Ig ly W = ∀ {W′} → W ⊲ W′ → Lg W′ → D ly W′ → St W′ → Df W′

Ig↾ : ∀ {ly W W′} → W ⊲ W′ → Ig ly W → Ig ly W′
Ig↾ p A₀ p′ = A₀ (⊲-tr p p′)

kk : ∀ {W₀ W k L} → StH W₀ k L → W₀ ⊲ W → LW L W → LW k W
kk r q l = ⊲ᴴ-tr (S→⊲ᴴ (Kup q r)) l
```

## §2 节点与目标

节点的层 $k$ 与目标 $t$ 都是 $\Lambda$ 在世界 $m$ 里的第一位置. 一次 `cmpH`: $t\lhd k$ 就上升; $k\lhd t$ 且不相等就保留.

```agda
data Rk (k t : H) (m : A) : Set where
  keep : StH m k t → Rk k t m
  rise : Rk k t m

rkS : ∀ {k t m} → k ⊲[ m ] t → Rk k t m
rkS hself = rise
rkS (hsuc p) = keep (ss p)
rkS (hlim n p) = keep (sl n p)
rkS (hLim e p) = keep (sL e p)

rkT : ∀ {k t m} → k ⊲[ m ] Λ → t ⊲[ m ] Λ → Lg m → Rk k t m
rkT km tm lm with cmpH km tm lm lΛ
... | inj₁ t⊲k = rise
... | inj₂ k⊲t = rkS k⊲t

-- nκ 回灌的一格 (同 SumOneFold)
record Cl (W W₀ : A) (ly : H) : Set where
  constructor mkCl
  field
    v  : A
    lv : Lg v
    wv : W ⊲ v
    a  : A
    ap : W₀ ⊲ a
    av : a ⊲ v
    Sv : St v
    co : D ly v
open Cl public
```

## §3 折叠

与 `SumHtFold` 逐个对应.

```agda
Run   : ∀ {ly W₀ W} → AccY ly → D ly W₀ → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → D ly W → St W → Df W
Rpt   : ∀ {ly W₀ W} → AccY ly → (ℕ → D ly W₀) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → D ly W → St W → ℕ → D ly W × St W
RunNi : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → D ly W → St W → Df W
Ai    : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′) → W₀ ⊲ W → LW k W → LW ly W → Ig ly W → D ly W → Ig k W
Chn   : ∀ {k W} → AccY k → LW k W → Lg W → Ig k W → St W → ℕ → D k W × (D k W × St W)
RKi   : ∀ {ly W₀ W k t m} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → Rk k t m → D t m
BNi   : ∀ {ly W₀ W k W′} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → Vs ly r W′ → D ly W′) → W₀ ⊲ W → LW ly W → Ig ly W → D ly W → St W → LW k W → W ⊲ W′ → Lg W′ → D k W′ → Df W′
Walk  : ∀ {ly W₀ V₁} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ V₁ → Lg V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → Df V₁
WRp   : ∀ {ly W₀ V₁ a n} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) → a ⊲ f n → W₀ ⊲ a → (∀ m → f m ⊲ V₁) → Lg V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → ℕ → D ly V₁ × St V₁
RunK  : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → D ly W → St W → Df W
RKy   : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → D ly W → St W → ∀ t {m} → Tg W t m → D t m
RKk   : ∀ {ly W₀ W t m} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → W₀ ⊲ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → NZ t → D t m
Kp    : ∀ {ly W₀ W W⁺} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → W₀ ⊲ W → LW ly W → Ig ly W → D ly W → St W → W ⊲ W⁺ → Lg W⁺ → Df W⁺
Kb    : ∀ {ly W₀ W W⁺ c} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → W₀ ⊲ W → LW ly W → Ig ly W → D ly W → St W → W ⊲ W⁺ → Lg W⁺ → W⁺ ⊲ c → Lg c → Df c
κc    : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → D ly W → St W → ℕ → Cl W W₀ ly
κΔ    : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → D ly c) → LW ly W → Ig ly W → (c : Cl W W₀ ly) → Df (v c)

Run ac n0 q₀ lW ll A₀ w Y = zeroD
Run ac n1 q₀ lW ll A₀ w Y = A₀ C.self lW w Y
Run ac (x ⨾ y) q₀ lW ll A₀ w Y =
  Run ac x q₀ lW ll A₀ w Y ⨾ᴰ Run ac y q₀ lW ll A₀ (w ⨾ nw q₀ x) (Y ⊕⟨ lW ⟩ Run ac x q₀ lW ll A₀ w Y)
Run ac (nl F) q₀ lW ll A₀ w Y =
  nlᴰ (λ n → Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))
Run ac (nw p x) q₀ lW ll A₀ w Y = Run ac x (⊲-tr p q₀) lW ll A₀ w Y
Run (acc f) (ni r u) q₀ lW ll A₀ w Y = RunNi (acc f) (f r) r u q₀ lW ll A₀ w Y
Run ac (nκ zz u) q₀ lW ll A₀ w Y = RunK ac u q₀ lW ll A₀ w Y

Rpt ac F q₀ lW ll A₀ w Y zero = w , Y
Rpt ac F q₀ lW ll A₀ w Y (suc n) =
  (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n) ⨾ nw q₀ (F n)) ,
  (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n) ⊕⟨ lW ⟩ Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))

RunNi ac ac′ r u q₀ lW ll A₀ w Y =
  df (λ T → RKi ac ac′ r u q₀ lW ll A₀ w Y T (rkT (⊲ᴴ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T)))

Ai ac ac′ r u q₀ hk ll A₀ w {W′} p lW′ z Y′ =
  Run ac (u (⊲-tr q₀ p) lW′ (inS r z)) C.self lW′ (⊲ᴴ↑ p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac′ z C.self lW′ (NZ-S r) (mkOf r (⊲-tr q₀ p)) (λ p′ l′ z′ → u (⊲-tr (⊲-tr q₀ p) p′) l′ (inS r z′)) n0) Y′

BNi ac ac′ r u q₀ ll A₀ w Y hk p lW′ z =
  Ai ac ac′ r u q₀ hk ll A₀ w p lW′ z
    (cv p Y ⊕⟨ lW′ ⟩ Run ac′ z C.self lW′ (⊲ᴴ↑ p hk) (Ig↾ p (Ai ac ac′ r u q₀ hk ll A₀ w)) n0 (cv p Y))

Chn ac′ hk lW A² Y zero = n0 , (yc (d Y) (tg C.self hk lW) , Y)
Chn ac′ hk lW A² Y (suc n) =
  (proj₁ (Chn ac′ hk lW A² Y n) ⨾ proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ,
  (yc (Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
      (tg C.self hk lW) ,
   (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)) ⊕⟨ lW ⟩
      Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))))

RKi ac ac′ r u q₀ lW ll A₀ w Y T (keep R′) =
  ni R′ (λ {W′} p lW′ y →
    yc (BNi ac ac′ r u q₀ ll A₀ w Y (kk r q₀ ll) (⊲-tr (wm T) p) lW′ (outS R′ y))
       (tg C.self (⊲ᴴ↑ p (tm T)) lW′))
RKi ac ac′ r u q₀ lW ll A₀ w Y T rise =
  nl (λ n →
    yc (Run ac′ (proj₁ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))) C.self lW (kk r q₀ ll)
              (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w)
              (proj₁ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))
              (proj₂ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n)))) T)

Walk ac u b C.self ap lb bV lV ll A₀ co Y = zeroD
Walk ac u (asuc c) (C.suc p) ap lb bV lV ll A₀ co Y =
  Walk ac u c p ap lb (⊲-tr (C.suc C.self) bV) lV ll A₀ co Y ⨾ᴰ
  Run ac (u (⊲-tr ap p) lb) (⊲-tr (C.suc C.self) bV) lV ll A₀ (co ⨾ Cut u c p ap lb (⊲-tr (C.suc C.self) bV))
    (Y ⊕⟨ lV ⟩ Walk ac u c p ap lb (⊲-tr (C.suc C.self) bV) lV ll A₀ co Y)
Walk ac u (alim f) {a} (C.lim n p) ap (stp , wl) bV lV ll A₀ co Y =
  Walk ac u (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) lV ll A₀ co Y ⨾ᴰ
  nlᴰ (λ m → Walk ac u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bV) lV ll A₀
        (proj₁ (WRp ac u f stp wl p ap (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV) lV ll A₀
                  (co ⨾ Cut u (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV))
                  (Y ⊕⟨ lV ⟩ Walk ac u (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) lV ll A₀ co Y) m))
        (proj₂ (WRp ac u f stp wl p ap (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV) lV ll A₀
                  (co ⨾ Cut u (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV))
                  (Y ⊕⟨ lV ⟩ Walk ac u (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) lV ll A₀ co Y) m)))

WRp ac u f stp wl p ap fV lV ll A₀ co Y zero = co , Y
WRp {n = n} ac u f stp wl p ap fV lV ll A₀ co Y (suc m) =
  (proj₁ (WRp ac u f stp wl p ap fV lV ll A₀ co Y m) ⨾ Cut u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n)))) ,
  (proj₂ (WRp ac u f stp wl p ap fV lV ll A₀ co Y m) ⊕⟨ lV ⟩
     Walk ac u (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) lV ll A₀
       (proj₁ (WRp ac u f stp wl p ap fV lV ll A₀ co Y m)) (proj₂ (WRp ac u f stp wl p ap fV lV ll A₀ co Y m)))

RunK ac u q₀ lW ll A₀ w Y = df (λ {t} T → RKy ac u q₀ lW ll A₀ w Y t T)

-- 目标是第 0 层: 回灌. 别的目标: 走到目标的世界, 再保留
RKy ac u q₀ lW ll A₀ w Y hz T =
  nl (λ n → drp (yc (κΔ ac u ll A₀ (κc ac u q₀ lW ll A₀ w Y n)) (τ₀ (lv (κc ac u q₀ lW ll A₀ w Y n)))))
RKy ac u q₀ lW ll A₀ w Y (hs b) T = RKk ac u q₀ ll A₀ w Y T tt
RKy ac u q₀ lW ll A₀ w Y (hl f) T = RKk ac u q₀ ll A₀ w Y T tt
RKy ac u q₀ lW ll A₀ w Y (hΩ g) T = RKk ac u q₀ ll A₀ w Y T tt

RKk ac u q₀ ll A₀ w Y T zz =
  yc (Kp ac u q₀ ll A₀ w Y (wm T) (lm T)) (tg C.self (tm T) (lm T)) ⨾
  nκ zz (λ {c} p lc → yc (Kb ac u q₀ ll A₀ w Y (wm T) (lm T) p lc) (tg C.self (⊲ᴴ↑ p (tm T)) lc))

Kp {W⁺ = W⁺} ac u q₀ ll A₀ w Y wu lW⁺ =
  Walk ac u W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self lW⁺ (⊲ᴴ↑ wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu Y)

Kb {W⁺ = W⁺} {c = c} ac u q₀ ll A₀ w Y wu lW⁺ p lc =
  Run ac (u (⊲-tr q₀ (⊲-tr wu p)) lc) C.self lc (⊲ᴴ↑ (⊲-tr wu p) ll) (Ig↾ (⊲-tr wu p) A₀)
    (nw p (nw wu w ⨾ Cut u W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self) ⨾ Cut u c p (⊲-tr q₀ wu) lc C.self)
    (cv p (cv wu Y ⊕⟨ lW⁺ ⟩ Kp ac u q₀ ll A₀ w Y wu lW⁺) ⊕⟨ lc ⟩
       Walk ac u c p (⊲-tr q₀ wu) lc C.self lc (⊲ᴴ↑ (⊲-tr wu p) ll) (Ig↾ (⊲-tr wu p) A₀)
         (nw p (nw wu w ⨾ Cut u W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self))
         (cv p (cv wu Y ⊕⟨ lW⁺ ⟩ Kp ac u q₀ ll A₀ w Y wu lW⁺)))

κc {W₀ = W₀} {W = W} ac u q₀ lW ll A₀ w Y zero =
  mkCl (sum W (z Y)) (Lg-sum W (z Y) lW) (sum-fst W (z Y)) W₀ C.self (⊲-tr q₀ (sum-fst W (z Y)))
     (cv (sum-fst W (z Y)) Y) (nw (sum-fst W (z Y)) w)
κc ac u q₀ lW ll A₀ w Y (suc n) =
  mkCl (sum (v c₀) (yc (κΔ ac u ll A₀ c₀) (τ₀ (lv c₀)))) (Lg-sum (v c₀) (yc (κΔ ac u ll A₀ c₀) (τ₀ (lv c₀))) (lv c₀))
     (⊲-tr (wv c₀) (sum-fst (v c₀) (yc (κΔ ac u ll A₀ c₀) (τ₀ (lv c₀))))) (v c₀) (⊲-tr (ap c₀) (av c₀))
     (sum-fst (v c₀) (yc (κΔ ac u ll A₀ c₀) (τ₀ (lv c₀))))
     (cv (sum-fst (v c₀) (yc (κΔ ac u ll A₀ c₀) (τ₀ (lv c₀)))) (Sv c₀ ⊕⟨ lv c₀ ⟩ κΔ ac u ll A₀ c₀))
     (nw (sum-fst (v c₀) (yc (κΔ ac u ll A₀ c₀) (τ₀ (lv c₀)))) (co c₀ ⨾ Cut u (v c₀) (av c₀) (ap c₀) (lv c₀) C.self))
  where
  c₀ = κc ac u q₀ lW ll A₀ w Y n

κΔ ac u ll A₀ c =
  Walk ac u (v c) (av c) (ap c) (lv c) C.self (lv c) (⊲ᴴ↑ (wv c) ll) (Ig↾ (wv c) A₀) (co c) (Sv c)
```

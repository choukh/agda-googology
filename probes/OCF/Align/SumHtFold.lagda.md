# 和形式, 高度取 $A$ (二): 折叠

> 不含记号. 入口 [SumHt](SumHt.lagda.md). 由 [SumOneFold](SumOneFold.lagda.md) 改写, 结构不变: 状态记每个目标的差, 输入走一段返回差; 节点低于目标就保留, 否则上升成链; `nκ` 在第 $(0,0)$ 层回灌, 在别的层保留. 改了三件:
>
> 1. **目标是 $(q,t)$ 加一个字面的世界 $m$** (`Tg W q t m`: $W,q,t\sqsubseteq m$). `SumOne` 的目标是 $t$ 与 $W$ 二选一的较大者 (`Tg t W`); 这里两维都要上界, 两个都在 $W$ 之上时没有字面公共上界去比, 所以把上界写进目标. 好处是换世界 (`cv`) 不用比较.
> 2. **节点与目标的比较** (`rkT`): 先在 $m$ 之内比高度 (`cmpF`), 高度相同再比下标. 被比较的两个下标总有字面公共上界 $m$.
> 3. 没有单独的顶层目标 `ŷ`: 顶层不是任何节点的层, $(1,0)$ 就是原来的 $\Omega_\Omega$ 那一档.
>
> `S`: 一步, 模块参数, 闭项里取 $S=\cdot\omega$ (`SumHtClosed`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.SumHtTree using (D₊)
open import OCF.Align.CumReadCF using (A)
module OCF.Align.SumHtFold (S : ∀ {Kd : A → A → A → Set} {V′ : ∀ {W h k} → Kd W h k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (azero; asuc; alim; _⊲_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; cmpF; S→⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLOpsW using (_◁_; ⊲◁)
open import OCF.Align.SumHtTree
```

## §1 状态

```agda
record Tg (W q t m : A) : Set where
  constructor tg
  field
    wm : W ⊲ m
    qm : q ⊲ m
    tm : t ⊲ m
    lm : Lg m
open Tg public

tg↑ : ∀ {W W′ q t m} → W ⊲ W′ → Tg W′ q t m → Tg W q t m
tg↑ q T = tg (⊲-tr q (wm T)) (qm T) (tm T) (lm T)

τ₀ : ∀ {W} → Lg W → Tg W azero azero W
τ₀ {W} lW = tg C.self (z⊲ W) (z⊲ W) lW

record Df (W : A) : Set where
  constructor df
  field
    yc : ∀ {q t m} → Tg W q t m → D q t m
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

-- 世界变大: 目标的上界本来就在目标里, 不用比较. 第 0 层的差从新世界重新算
cv : ∀ {W W′} → W ⊲ W′ → St W → St W′
cv q Y = st (df (λ T → yc (d Y) (tg↑ q T))) n0

Step : ∀ {W} → St W → Df W
Step Y = df (λ {q} {t} T → S (Ωd q t (lg⊲ (qm T) (lm T)) (lg⊲ (tm T) (lm T)) ⨾ yc (d Y) T))

Ig : Ly → A → Set
Ig ly W = ∀ {W′} → W ⊲ W′ → Lg W′ → Dl ly W′ → St W′ → Df W′

Ig↾ : ∀ {ly W W′} → W ⊲ W′ → Ig ly W → Ig ly W′
Ig↾ p A₀ p′ = A₀ (⊲-tr p p′)
```

## §2 节点与目标

节点的层 $(h,k)$, 目标 $(q,t)$, 都在 $m$ 之下. 高度严格低: 保留 (`lo`); 高度相同, 下标严格低: 保留 (`sm`); 否则上升.

```agda
data Rk (h k q t m : A) : Set where
  keep : KP q t m h k → Rk h k q t m
  rise : Rk h k q t m

rkS : ∀ {q k t m} → k ⊲ t → Rk q k q t m
rkS C.self = rise
rkS (C.suc p) = keep (sm (ss p))
rkS (C.lim n p) = keep (sm (sl n p))

rkI : ∀ {q k t m} → k ⊲ m → t ⊲ m → Lg m → Rk q k q t m
rkI km tm lm with cmpF km tm lm
... | inj₁ t⊲k = rise
... | inj₂ k⊲t = rkS k⊲t

rkT : ∀ {h k q t m} → h ⊲ m → k ⊲ m → q ⊲ m → t ⊲ m → Lg m → Rk h k q t m
rkT hm km qm tm lm with cmpF hm qm lm
... | inj₁ q⊲h with ⊲◁ q⊲h
...   | inj₁ refl = rkI km tm lm
...   | inj₂ _ = rise
rkT hm km qm tm lm | inj₂ h⊲q with ⊲◁ h⊲q
...   | inj₁ refl = rkI km tm lm
...   | inj₂ i = keep (lo i km)

-- nκ 回灌的一格 (同 SumOneFold)
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
```

## §3 折叠

与 `SumOneFold` 逐个对应. `Run`: 走输入. `RunNi`/`RKi`: 节点. `Chn`: 上升的链, 坐标从状态在节点层的差起. `Ai`: 链与分支里每一格走一次分支. `BNi`: 保留的节点的分支. `RunK`/`RKy`: `nκ`; 目标 $(0,0)$ 走回灌 (`κc`, `κΔ`), 别的目标走到目标的世界 (`Kp`) 再保留 (`Kb`).

```agda
Run   : ∀ {ly W₀ W} → AccY ly → Dl ly W₀ → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
Rpt   : ∀ {ly W₀ W} → AccY ly → (ℕ → Dl ly W₀) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → ℕ → Dl ly W × St W
RunNi : ∀ {ly W₀ W h k} → AccY ly → AccY (lay h k) → (r : K ly W₀ h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
Ai    : ∀ {ly W₀ W h k} → AccY ly → AccY (lay h k) → (r : K ly W₀ h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → HK h k W → LW ly W → Ig ly W → Dl ly W → Ig (lay h k) W
Chn   : ∀ {h k W} → AccY (lay h k) → HK h k W → Lg W → Ig (lay h k) W → St W → ℕ → D h k W × (D h k W × St W)
RKi   : ∀ {ly W₀ W h k q t m} → AccY ly → AccY (lay h k) → (r : K ly W₀ h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Tg W q t m → Rk h k q t m → D q t m
BNi   : ∀ {ly W₀ W h k W′} → AccY ly → AccY (lay h k) → (r : K ly W₀ h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → HK h k W → W ⊲ W′ → Lg W′ → D h k W′ → Df W′
Walk  : ∀ {ly W₀ V₁} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ V₁ → Lg V₁ → LW ly V₁ → Ig ly V₁ → Dl ly V₁ → St V₁ → Df V₁
WRp   : ∀ {ly W₀ V₁ a n} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) → a ⊲ f n → W₀ ⊲ a → (∀ m → f m ⊲ V₁) → Lg V₁ → LW ly V₁ → Ig ly V₁ → Dl ly V₁ → St V₁ → ℕ → Dl ly V₁ × St V₁
RunK  : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
RKy   : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → ∀ q t {m} → Tg W q t m → D q t m
RKk   : ∀ {ly W₀ W q t m} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → Tg W q t m → ZP q t → D q t m
Kp    : ∀ {ly W₀ W W⁺} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → W ⊲ W⁺ → Lg W⁺ → Df W⁺
Kb    : ∀ {ly W₀ W W⁺ c} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → W ⊲ W⁺ → Lg W⁺ → W⁺ ⊲ c → Lg c → Df c
κc    : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → ℕ → Cl W W₀ ly
κΔ    : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → LW ly W → Ig ly W → (c : Cl W W₀ ly) → Df (v c)

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

RunNi {ly} ac ac′ r u q₀ lW ll A₀ w Y =
  df (λ T → RKi ac ac′ r u q₀ lW ll A₀ w Y T
              (rkT (⊲-tr (proj₁ (kk ly r q₀ ll)) (wm T)) (⊲-tr (proj₂ (kk ly r q₀ ll)) (wm T)) (qm T) (tm T) (lm T)))

Ai {ly} ac ac′ r u q₀ hk ll A₀ w {W′} p lW′ z Y′ =
  Run ac (u (⊲-tr q₀ p) lW′ (inV ly r z)) C.self lW′ (LW↑ ly p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac′ z C.self lW′ (hk↑ hk p) (zyOf ly r) (mkOf ly r) (λ p′ l′ z′ → u (⊲-tr (⊲-tr q₀ p) p′) l′ (inV ly r z′)) n0) Y′

BNi {ly} ac ac′ r u q₀ ll A₀ w Y hk p lW′ z =
  Ai ac ac′ r u q₀ hk ll A₀ w p lW′ z
    (cv p Y ⊕⟨ lW′ ⟩ Run ac′ z C.self lW′ (hk↑ hk p) (Ig↾ p (Ai ac ac′ r u q₀ hk ll A₀ w)) n0 (cv p Y))

Chn ac′ hk lW A² Y zero = n0 , (yc (d Y) (tg C.self (proj₁ hk) (proj₂ hk) lW) , Y)
Chn ac′ hk lW A² Y (suc n) =
  (proj₁ (Chn ac′ hk lW A² Y n) ⨾ proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ,
  (yc (Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
      (tg C.self (proj₁ hk) (proj₂ hk) lW) ,
   (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)) ⊕⟨ lW ⟩
      Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))))

RKi {ly} ac ac′ r u q₀ lW ll A₀ w Y T (keep R′) =
  ni R′ (λ {W′} p lW′ y →
    yc (BNi ac ac′ r u q₀ ll A₀ w Y (kk ly r q₀ ll) (⊲-tr (wm T) p) lW′ (outV (lay _ _) R′ y))
       (tg C.self (⊲-tr (qm T) p) (⊲-tr (tm T) p) lW′))
RKi {ly} ac ac′ r u q₀ lW ll A₀ w Y T rise =
  nl (λ n →
    yc (Run ac′ (proj₁ (proj₂ (Chn ac′ (kk ly r q₀ ll) lW (Ai ac ac′ r u q₀ (kk ly r q₀ ll) ll A₀ w) Y n))) C.self lW (kk ly r q₀ ll)
              (Ai ac ac′ r u q₀ (kk ly r q₀ ll) ll A₀ w)
              (proj₁ (Chn ac′ (kk ly r q₀ ll) lW (Ai ac ac′ r u q₀ (kk ly r q₀ ll) ll A₀ w) Y n))
              (proj₂ (proj₂ (Chn ac′ (kk ly r q₀ ll) lW (Ai ac ac′ r u q₀ (kk ly r q₀ ll) ll A₀ w) Y n)))) T)

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

RunK ac u q₀ lW ll A₀ w Y = df (λ {q} {t} T → RKy ac u q₀ lW ll A₀ w Y q t T)

RKy ac u q₀ lW ll A₀ w Y azero azero T =
  nl (λ n → drp (yc (κΔ ac u ll A₀ (κc ac u q₀ lW ll A₀ w Y n)) (τ₀ (lv (κc ac u q₀ lW ll A₀ w Y n)))))
RKy ac u q₀ lW ll A₀ w Y (asuc b) t T = RKk ac u q₀ ll A₀ w Y T (inj₁ tt)
RKy ac u q₀ lW ll A₀ w Y (alim f) t T = RKk ac u q₀ ll A₀ w Y T (inj₁ tt)
RKy ac u q₀ lW ll A₀ w Y azero (asuc b) T = RKk ac u q₀ ll A₀ w Y T (inj₂ tt)
RKy ac u q₀ lW ll A₀ w Y azero (alim f) T = RKk ac u q₀ ll A₀ w Y T (inj₂ tt)

RKk ac u q₀ ll A₀ w Y T zz =
  yc (Kp ac u q₀ ll A₀ w Y (wm T) (lm T)) (tg C.self (qm T) (tm T) (lm T)) ⨾
  nκ zz (λ {c} p lc → yc (Kb ac u q₀ ll A₀ w Y (wm T) (lm T) p lc) (tg C.self (⊲-tr (qm T) p) (⊲-tr (tm T) p) lc))

Kp {ly} {W⁺ = W⁺} ac u q₀ ll A₀ w Y wu lW⁺ =
  Walk ac u W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self lW⁺ (LW↑ ly wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu Y)

Kb {ly} {W⁺ = W⁺} {c = c} ac u q₀ ll A₀ w Y wu lW⁺ p lc =
  Run ac (u (⊲-tr q₀ (⊲-tr wu p)) lc) C.self lc (LW↑ ly (⊲-tr wu p) ll) (Ig↾ (⊲-tr wu p) A₀)
    (nw p (nw wu w ⨾ Cut u W⁺ (⊲-tr q₀ wu) C.self lW⁺ C.self) ⨾ Cut u c p (⊲-tr q₀ wu) lc C.self)
    (cv p (cv wu Y ⊕⟨ lW⁺ ⟩ Kp ac u q₀ ll A₀ w Y wu lW⁺) ⊕⟨ lc ⟩
       Walk ac u c p (⊲-tr q₀ wu) lc C.self lc (LW↑ ly (⊲-tr wu p) ll) (Ig↾ (⊲-tr wu p) A₀)
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

κΔ {ly} ac u ll A₀ c =
  Walk ac u (v c) (av c) (ap c) (lv c) C.self (lv c) (LW↑ ly (wv c) ll) (Ig↾ (wv c) A₀) (co c) (Sv c)
```

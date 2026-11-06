# 和形式, 层取三位 (二): 折叠

> 不含记号. 入口 [SumClimb](SumClimb.lagda.md). 由 [SumHtFold](SumHtFold.lagda.md) 逐字改写, 只改层的位数: 目标是 $(r,q,t)$ 加字面世界 $m$ (`Tg W r q t m`), 节点与目标在 $m$ 之内先比第一位, 再比第二位, 再比下标 (`rkT`, `rkH`, `rkI`); `nκ` 只在目标 $(0,0,0)$ 回灌. 其余与 `SumHtFold` 相同.
>
> `S`: 一步, 模块参数. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.SumClimbTree using (D₊)
open import OCF.Align.CumReadCF using (A)
module OCF.Align.SumClimbFold (S : ∀ {Kd : A → A → A → A → Set} {V′ : ∀ {W g h k} → Kd W g h k → A → Set} {Z : Set} {W} → D₊ Kd V′ Z W → D₊ Kd V′ Z W) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (azero; asuc; alim; _⊲_; Strict; ss; sl; Lg; ⊲-tr; lg⊲; z⊲; cmpF; S→⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLOpsW using (_◁_; ⊲◁)
open import OCF.Align.SumClimbTree
```

## §1 状态

```agda
record Tg (W r q t m : A) : Set where
  constructor tg
  field
    wm : W ⊲ m
    rm : r ⊲ m
    qm : q ⊲ m
    tm : t ⊲ m
    lm : Lg m
open Tg public

tg↑ : ∀ {W W′ r q t m} → W ⊲ W′ → Tg W′ r q t m → Tg W r q t m
tg↑ q T = tg (⊲-tr q (wm T)) (rm T) (qm T) (tm T) (lm T)

τ₀ : ∀ {W} → Lg W → Tg W azero azero azero W
τ₀ {W} lW = tg C.self (z⊲ W) (z⊲ W) (z⊲ W) lW

record Df (W : A) : Set where
  constructor df
  field
    yc : ∀ {r q t m} → Tg W r q t m → D r q t m
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
Step Y = df (λ {r} {q} {t} T → S (Ωd r q t (lg⊲ (rm T) (lm T)) (lg⊲ (qm T) (lm T)) (lg⊲ (tm T) (lm T)) ⨾ yc (d Y) T))

Ig : Ly → A → Set
Ig ly W = ∀ {W′} → W ⊲ W′ → Lg W′ → Dl ly W′ → St W′ → Df W′

Ig↾ : ∀ {ly W W′} → W ⊲ W′ → Ig ly W → Ig ly W′
Ig↾ p A₀ p′ = A₀ (⊲-tr p p′)
```

## §2 节点与目标

节点的层 $(g,h,k)$, 目标 $(r,q,t)$, 都在 $m$ 之下. 字典序: 第一位严格低保留 (`lr`); 第一位相同, 第二位严格低保留 (`lo`); 前两位相同, 下标严格低保留 (`sm`); 否则上升.

```agda
data Rk (g h k r q t m : A) : Set where
  keep : KQ r q t m g h k → Rk g h k r q t m
  rise : Rk g h k r q t m

rkS : ∀ {r q k t m} → k ⊲ t → Rk r q k r q t m
rkS C.self = rise
rkS (C.suc p) = keep (sm (ss p))
rkS (C.lim n p) = keep (sm (sl n p))

rkI : ∀ {r q k t m} → k ⊲ m → t ⊲ m → Lg m → Rk r q k r q t m
rkI km tm lm with cmpF km tm lm
... | inj₁ t⊲k = rise
... | inj₂ k⊲t = rkS k⊲t

rkH : ∀ {r h k q t m} → h ⊲ m → k ⊲ m → q ⊲ m → t ⊲ m → Lg m → Rk r h k r q t m
rkH hm km qm tm lm with cmpF hm qm lm
... | inj₁ q⊲h with ⊲◁ q⊲h
...   | inj₁ refl = rkI km tm lm
...   | inj₂ _ = rise
rkH hm km qm tm lm | inj₂ h⊲q with ⊲◁ h⊲q
...   | inj₁ refl = rkI km tm lm
...   | inj₂ i = keep (lo i km)

rkT : ∀ {g h k r q t m} → g ⊲ m → h ⊲ m → k ⊲ m → r ⊲ m → q ⊲ m → t ⊲ m → Lg m → Rk g h k r q t m
rkT gm hm km rm qm tm lm with cmpF gm rm lm
... | inj₁ r⊲g with ⊲◁ r⊲g
...   | inj₁ refl = rkH hm km qm tm lm
...   | inj₂ _ = rise
rkT gm hm km rm qm tm lm | inj₂ g⊲r with ⊲◁ g⊲r
...   | inj₁ refl = rkH hm km qm tm lm
...   | inj₂ j = keep (lr j hm km)

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
RunNi : ∀ {ly W₀ W g h k} → AccY ly → AccY (lay g h k) → (r : K ly W₀ g h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
Ai    : ∀ {ly W₀ W g h k} → AccY ly → AccY (lay g h k) → (r : K ly W₀ g h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → HK g h k W → LW ly W → Ig ly W → Dl ly W → Ig (lay g h k) W
Chn   : ∀ {g h k W} → AccY (lay g h k) → HK g h k W → Lg W → Ig (lay g h k) W → St W → ℕ → D g h k W × (D g h k W × St W)
RKi   : ∀ {ly W₀ W g h k r′ q t m} → AccY ly → AccY (lay g h k) → (r : K ly W₀ g h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Tg W r′ q t m → Rk g h k r′ q t m → D r′ q t m
BNi   : ∀ {ly W₀ W g h k W′} → AccY ly → AccY (lay g h k) → (r : K ly W₀ g h k) → (∀ {W′} → W₀ ⊲ W′ → Lg W′ → V ly r W′ → Dl ly W′) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → HK g h k W → W ⊲ W′ → Lg W′ → D g h k W′ → Df W′
Walk  : ∀ {ly W₀ V₁} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → ∀ b {a} → a ⊲ b → W₀ ⊲ a → Lg b → b ⊲ V₁ → Lg V₁ → LW ly V₁ → Ig ly V₁ → Dl ly V₁ → St V₁ → Df V₁
WRp   : ∀ {ly W₀ V₁ a n} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) → a ⊲ f n → W₀ ⊲ a → (∀ m → f m ⊲ V₁) → Lg V₁ → LW ly V₁ → Ig ly V₁ → Dl ly V₁ → St V₁ → ℕ → Dl ly V₁ × St V₁
RunK  : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → Df W
RKy   : ∀ {ly W₀ W} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → Lg W → LW ly W → Ig ly W → Dl ly W → St W → ∀ r q t {m} → Tg W r q t m → D r q t m
RKk   : ∀ {ly W₀ W r q t m} → AccY ly → (∀ {c} → W₀ ⊲ c → Lg c → Dl ly c) → W₀ ⊲ W → LW ly W → Ig ly W → Dl ly W → St W → Tg W r q t m → ZQ r q t → D r q t m
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
              (rkT (⊲-tr (proj₁ (kk ly r q₀ ll)) (wm T)) (⊲-tr (proj₁ (proj₂ (kk ly r q₀ ll))) (wm T)) (⊲-tr (proj₂ (proj₂ (kk ly r q₀ ll))) (wm T))
                   (rm T) (qm T) (tm T) (lm T)))

Ai {ly} ac ac′ r u q₀ hk ll A₀ w {W′} p lW′ z Y′ =
  Run ac (u (⊲-tr q₀ p) lW′ (inV ly r z)) C.self lW′ (LW↑ ly p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac′ z C.self lW′ (hk↑ hk p) (zyOf ly r) (mkOf ly r) (λ p′ l′ z′ → u (⊲-tr (⊲-tr q₀ p) p′) l′ (inV ly r z′)) n0) Y′

BNi {ly} ac ac′ r u q₀ ll A₀ w Y hk p lW′ z =
  Ai ac ac′ r u q₀ hk ll A₀ w p lW′ z
    (cv p Y ⊕⟨ lW′ ⟩ Run ac′ z C.self lW′ (hk↑ hk p) (Ig↾ p (Ai ac ac′ r u q₀ hk ll A₀ w)) n0 (cv p Y))

Chn ac′ hk lW A² Y zero = n0 , (yc (d Y) (tg C.self (proj₁ hk) (proj₁ (proj₂ hk)) (proj₂ (proj₂ hk)) lW) , Y)
Chn ac′ hk lW A² Y (suc n) =
  (proj₁ (Chn ac′ hk lW A² Y n) ⨾ proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ,
  (yc (Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
      (tg C.self (proj₁ hk) (proj₁ (proj₂ hk)) (proj₂ (proj₂ hk)) lW) ,
   (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)) ⊕⟨ lW ⟩
      Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) C.self lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))))

RKi {ly} ac ac′ r u q₀ lW ll A₀ w Y T (keep R′) =
  ni R′ (λ {W′} p lW′ y →
    yc (BNi ac ac′ r u q₀ ll A₀ w Y (kk ly r q₀ ll) (⊲-tr (wm T) p) lW′ (outV (lay _ _ _) R′ y))
       (tg C.self (⊲-tr (rm T) p) (⊲-tr (qm T) p) (⊲-tr (tm T) p) lW′))
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

RunK ac u q₀ lW ll A₀ w Y = df (λ {r} {q} {t} T → RKy ac u q₀ lW ll A₀ w Y r q t T)

RKy ac u q₀ lW ll A₀ w Y azero azero azero T =
  nl (λ n → drp (yc (κΔ ac u ll A₀ (κc ac u q₀ lW ll A₀ w Y n)) (τ₀ (lv (κc ac u q₀ lW ll A₀ w Y n)))))
RKy ac u q₀ lW ll A₀ w Y (asuc b) q t T = RKk ac u q₀ ll A₀ w Y T (inj₁ tt)
RKy ac u q₀ lW ll A₀ w Y (alim f) q t T = RKk ac u q₀ ll A₀ w Y T (inj₁ tt)
RKy ac u q₀ lW ll A₀ w Y azero (asuc b) t T = RKk ac u q₀ ll A₀ w Y T (inj₂ (inj₁ tt))
RKy ac u q₀ lW ll A₀ w Y azero (alim f) t T = RKk ac u q₀ ll A₀ w Y T (inj₂ (inj₁ tt))
RKy ac u q₀ lW ll A₀ w Y azero azero (asuc b) T = RKk ac u q₀ ll A₀ w Y T (inj₂ (inj₂ tt))
RKy ac u q₀ lW ll A₀ w Y azero azero (alim f) T = RKk ac u q₀ ll A₀ w Y T (inj₂ (inj₂ tt))

RKk ac u q₀ ll A₀ w Y T zz =
  yc (Kp ac u q₀ ll A₀ w Y (wm T) (lm T)) (tg C.self (rm T) (qm T) (tm T) (lm T)) ⨾
  nκ zz (λ {c} p lc → yc (Kb ac u q₀ ll A₀ w Y (wm T) (lm T) p lc) (tg C.self (⊲-tr (rm T) p) (⊲-tr (qm T) p) (⊲-tr (tm T) p) lc))

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

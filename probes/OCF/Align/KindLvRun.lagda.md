# 按级回灌 (三): 折叠, 第 0 层目标下每个旧种类按自己的级回灌

> 不含记号. 入口 [KindLv](KindLv.lagda.md), 接口 [KindLvIf](KindLvIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **由 [GenFoldRun](GenFoldRun.lagda.md) 逐行拷贝, 只加一处**: 旧种类 `inj₁ κ` 的闭包结点在第 0 层目标下, GenFoldRun 直接查 `fbA G κ : FBA T κ ⊎ ⊤` (`RKa`), 只能处理坐标是 `A` 的种类 (级层 0, 读回 `sum`). 这里先查模块参数 `lv : LvFb T (tpK G) Λ` (接口 §3, 新加的一行 `RKv`): 种类 $\kappa$ 有级回灌 `L : KLv T (tpK G) Λ κ` 时 (`κcL`)
>
> $$v_0=\mathrm{rd}_L(\mathrm{top}_\kappa w,\ d_{\ell}),\quad w_1=\mathrm{rs}_L\,w\,v_0,\qquad v_{n+1}=\mathrm{rd}_L(\mathrm{top}_\kappa w_{n+1},\ \Delta_n),\quad w_{n+2}=\mathrm{rs}_L\,w_{n+1}\,v_{n+1},$$
>
> 其中 $d_\ell$ 是状态里累计的输出在级层 $\ell_L$ 上的值, $\Delta_n$ 是分支在世界 $(w_{n+1},\beta)$ 里折叠后在级层 $\ell_L$ 上的输出; 第 0 层的输出是 $\Delta_n$ 在第 0 层上的值的 ℕ-极限 (同 `GenFoldRun.RKa`). `lv κ = inj₂ tt` 时**退回 GenFoldRun 原样的一行** (`RKa`: `fbA G κ` 给 A-回灌或有损; `RKa`, `κcA`, `κΔA` 逐字不变). 所以 `lv` 恒为 `inj₂ tt` 时本折叠与 GenFoldRun 逐行相同. 其余各行 (新种类在第 0, 1 层用 `rd₁` 回灌; 第 $\ge1$ 层保留; 结点; 比较 `cmpB`) 逐字不变. 停机: 同 GenFoldRun (对数据结构递归, 结点经 `AccY`); 合法: 数据没有合法性, 世界的合法由 `rsLg`, `rd-lg` 给出.
>
> 下面的表沿用 GenFoldRun 的, 第三行换成级回灌:
>
> | 种类 | 目标层 | 做法 |
> |---|---|---|
> | 新种类 `inj₂ tt` (坐标 `HB T`) | $0$, $1$ | 回灌 (`κc₁`, 读回 `rd₁`) |
> | 新种类 | $\ge2$ | 保留 |
> | 旧种类 `inj₁ κ` 且 `lv κ = inj₁ L` | $0$ | **按 $\kappa$ 的级回灌** (`κcL`): 级层 $\ell_L$, 读回 $\mathrm{rd}_L$, 升界 $\mathrm{rs}_L$ |
> | 旧种类, `lv κ = inj₂ tt`, `fbA κ = inj₁ F` | $0$ | A-回灌 (`κcA`, 同 GenFoldRun) |
> | 旧种类, `lv κ = inj₂ tt`, `fbA κ = inj₂ tt` | $0$ | 有损 |
> | 旧种类 | $\ge1$ | 保留 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (KS; HB; hs; hz; step; _⊲[_]_; LgB)
open import OCF.Align.GenFoldIf using (GenK; LgDn; tpK; FbLg)
open import OCF.Align.KindLvIf using (LvFb)
module OCF.Align.KindLvRun (T : KS) (G : GenK T) (Ld : LgDn T) (fl : FbLg G)
  (Λ : HB (step T)) (lΛ : LgB Λ) (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (lv : LvFb T (tpK G) Λ) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; _⊲_; Lg)
open import OCF.Align.HtTowerTy hiding (KS; HB; hs; hz; step; _⊲[_]_; LgB)
open import OCF.Align.HtTowerTy using (KS; HB; hs; hz; step; _⊲[_]_; LgB)
open import OCF.Align.GenFoldIf hiding (GenK; LgDn; tpK; FbLg; rs≤; rsLg)
open FBA renaming (rs≤ to rsA≤; rsLg to rsALg)
open import OCF.Align.KindLvIf using (KLv; ℓ; ℓ⊲; rd; rd-fst; rd-lg; rs; rs≤; rsLg)
open import OCF.Align.GenFoldTree
open Tree T
open Om (topStepG (tpK G))
open import OCF.Align.GenFoldRd T G Ld
open FoldTy T Λ using (LW; Tg; tg; Df; df; St; st; Ig)
open Tg public
open Df public
open St public
```

## §1 状态

```agda
ω⋅ : ∀ {L W} → D L W → D L W
ω⋅ c = nl (λ _ → c)

tg↑ : ∀ {W W′ t m} → W ≤ W′ → Tg W′ t m → Tg W t m
tg↑ q Tq = tg (≤tr q (wm Tq)) (tm Tq) (lm Tq)

τ₀ : ∀ {W} → LgW L₀ W → Tg W hz W
τ₀ lW = tg ≤rf (z⊲ᴮ Λ) lW

τ₁ : ∀ {W} → LgW L₀ W → Tg W (hs hz) W
τ₁ lW = tg ≤rf one⊲ lW

zeroD : ∀ {W} → Df W
zeroD = df (λ Tq → n0)

infixl 6 _⨾ᴰ_
_⨾ᴰ_ : ∀ {W} → Df W → Df W → Df W
a ⨾ᴰ b = df (λ Tq → yc a Tq ⨾ yc b Tq)

nlᴰ : ∀ {W} → (ℕ → Df W) → Df W
nlᴰ F = df (λ Tq → nl (λ n → yc (F n) Tq))

_⊕⟨_⟩_ : ∀ {W} → St W → LgW L₀ W → Df W → St W
Y ⊕⟨ lW ⟩ Δ = st (d Y ⨾ᴰ Δ) (z Y ⨾ yc Δ (τ₀ lW)) (z₁ Y ⨾ yc Δ (τ₁ lW))

cv : ∀ {W W′} → W ≤ W′ → St W → St W′
cv q Y = st (df (λ Tq → yc (d Y) (tg↑ q Tq))) n0 n0

Stp : ∀ {W} → St W → Df W
Stp Y = df (λ {t} Tq → ω⋅ (Ωd t ⨾ yc (d Y) Tq))

Ig↾ : ∀ {ly W W′} → W ≤ W′ → Ig ly W → Ig ly W′
Ig↾ p A₀ p′ = A₀ (≤tr p p′)

kk : ∀ {W₀ W k L} → StH W₀ k L → W₀ ≤ W → LW L W → LW k W
kk r q l = ⊲ᴮ-tr (S→⊲ {L₀} (Kup {L₀} q r)) l

Bu : HB L₀ → Wd L₀ → Set
Bu ly W₀ = ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → D ly W′
```

## §2 节点与目标

```agda
data Rk (k t : HB L₀) (m : Wd L₀) : Set where
  keep : StH m k t → Rk k t m
  rise : Rk k t m

rkS : ∀ {k t m} → k ⊲[ m ] t → Rk k t m
rkS hself = rise
rkS (hsuc p) = keep (ss p)
rkS (hlim n p) = keep (sl n p)
rkS (hLim e p) = keep (sL e p)

rkT : ∀ {k t m} → k ⊲[ m ] Λ → t ⊲[ m ] Λ → LgW L₀ m → Rk k t m
rkT km tm′ lm′ with cmpB km tm′ lm′ lΛ
... | inj₁ t⊲k = rise
... | inj₂ k⊲t = rkS k⊲t
```

## §3 回灌一格的记录

```agda
-- 新种类: 世界 (w , v₁)
record Cl₁ (W : Wd L₀) (ly : HB L₀) : Set where
  constructor mkCl₁
  field
    v₁  : HB T
    lv₁ : LgB v₁
    wv₁ : proj₂ W ⊲[ proj₁ W ] v₁
    Sv₁ : St (proj₁ W , v₁)
    co₁ : D ly (proj₁ W , v₁)
open Cl₁ public

-- 旧种类按级回灌: 世界 (wA , 原新种类的界)
record ClA (W : Wd L₀) (ly : HB L₀) : Set where
  constructor mkClA
  field
    wA  : Wd T
    lwA : LgW T wA
    qA  : _≤w_ T (proj₁ W) wA
    SA  : St (wA , proj₂ W)
    coA : D ly (wA , proj₂ W)
open ClA public
```

## §4 折叠

```agda
Run   : ∀ {ly W₀ W} → AccY ly → D ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Df W
Rpt   : ∀ {ly W₀ W} → AccY ly → (ℕ → D ly W₀) → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ℕ → D ly W × St W
RunNi : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Df W
Ai    : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW k W → LW ly W → Ig ly W → D ly W → Ig k W
Chn   : ∀ {k W} → AccY k → LW k W → LgW L₀ W → Ig k W → St W → ℕ → D k W × (D k W × St W)
RKi   : ∀ {ly W₀ W k t m} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → Rk k t m → D t m
BNi   : ∀ {ly W₀ W k W′} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → LW k W → W ≤ W′ → LgW L₀ W′ → D k W′ → Df W′
RunC  : ∀ {ly W₀ W} → AccY ly → (κ : K L₀) → ZK T ly κ → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Df W
RKc   : ∀ {ly W₀ W} → AccY ly → (κ : K L₀) → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ∀ t {m} → Tg W t m → D t m
RKk   : ∀ {ly W₀ W t m} → AccY ly → (κ : K L₀) → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → ZK T t κ → D t m
κc₁   : ∀ {ly W₀ W} → AccY ly → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ℕ → Cl₁ W ly
κΔ₁   : ∀ {ly W₀ W} → AccY ly → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → (c : Cl₁ W ly) → Df (proj₁ W , v₁ c)
RKv   : ∀ {ly W₀ W m} → AccY ly → ∀ κ (s : KLv T (tpK G) Λ κ ⊎ ⊤) → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Tg W hz m → D hz m
RKa   : ∀ {ly W₀ W m} → AccY ly → ∀ {κ} (s : FBA T κ ⊎ ⊤) → FbLgAt {T} {κ} s → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Tg W hz m → D hz m
κcL   : ∀ {ly W₀ W κ} → AccY ly → (F : KLv T (tpK G) Λ κ) → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ℕ → ClA W ly
κcA   : ∀ {ly W₀ W κ} → AccY ly → (F : FBA T κ) → (∀ {w} → LgW T w → Lg (tpA F w)) → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ℕ → ClA W ly
κΔA   : ∀ {ly W₀ W} → AccY ly → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → (c : ClA W ly) → Df (wA c , proj₂ W)

Run ac n0 q₀ lW ll A₀ w Y = zeroD
Run ac n1 q₀ lW ll A₀ w Y = A₀ ≤rf lW w Y
Run ac (x ⨾ y) q₀ lW ll A₀ w Y =
  Run ac x q₀ lW ll A₀ w Y ⨾ᴰ Run ac y q₀ lW ll A₀ (w ⨾ nw q₀ x) (Y ⊕⟨ lW ⟩ Run ac x q₀ lW ll A₀ w Y)
Run ac (nl F) q₀ lW ll A₀ w Y =
  nlᴰ (λ n → Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))
Run ac (nw p x) q₀ lW ll A₀ w Y = Run ac x (≤tr p q₀) lW ll A₀ w Y
Run (acc f) (ni r u) q₀ lW ll A₀ w Y = RunNi (acc f) (f r) r u q₀ lW ll A₀ w Y
Run ac (nc κ zz u) q₀ lW ll A₀ w Y = RunC ac κ zz u q₀ lW ll A₀ w Y

Rpt ac F q₀ lW ll A₀ w Y zero = w , Y
Rpt ac F q₀ lW ll A₀ w Y (suc n) =
  (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n) ⨾ nw q₀ (F n)) ,
  (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n) ⊕⟨ lW ⟩ Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))

RunNi ac ac′ r u q₀ lW ll A₀ w Y =
  df (λ Tq → RKi ac ac′ r u q₀ lW ll A₀ w Y Tq (rkT (⊲ᴮ↑ (wm Tq) (kk r q₀ ll)) (tm Tq) (lm Tq)))

Ai ac ac′ r u q₀ hk ll A₀ w {W′} p lW′ zz Y′ =
  Run ac (u (≤tr q₀ p) lW′ (inS r zz)) ≤rf lW′ (⊲ᴮ↑ p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac′ zz ≤rf lW′ (zkS {T} r) (mkOf r (≤tr q₀ p)) (λ p′ l′ z′ → u (≤tr (≤tr q₀ p) p′) l′ (inS r z′)) n0) Y′

BNi ac ac′ r u q₀ ll A₀ w Y hk p lW′ zz =
  Ai ac ac′ r u q₀ hk ll A₀ w p lW′ zz
    (cv p Y ⊕⟨ lW′ ⟩ Run ac′ zz ≤rf lW′ (⊲ᴮ↑ p hk) (Ig↾ p (Ai ac ac′ r u q₀ hk ll A₀ w)) n0 (cv p Y))

Chn ac′ hk lW A² Y zero = n0 , (yc (d Y) (tg ≤rf hk lW) , Y)
Chn ac′ hk lW A² Y (suc n) =
  (proj₁ (Chn ac′ hk lW A² Y n) ⨾ proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ,
  (yc (Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
      (tg ≤rf hk lW) ,
   (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)) ⊕⟨ lW ⟩
      Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))))

RKi ac ac′ r u q₀ lW ll A₀ w Y Tq (keep R′) =
  ni R′ (λ {W′} p lW′ y →
    yc (BNi ac ac′ r u q₀ ll A₀ w Y (kk r q₀ ll) (≤tr (wm Tq) p) lW′ (outS R′ y))
       (tg ≤rf (⊲ᴮ↑ p (tm Tq)) lW′))
RKi ac ac′ r u q₀ lW ll A₀ w Y Tq rise =
  nl (λ n →
    yc (Run ac′ (proj₁ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))) ≤rf lW (kk r q₀ ll)
              (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w)
              (proj₁ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))
              (proj₂ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n)))) Tq)
```

**闭包结点.** 按种类与目标层分 (见文件头的表).

```agda
RunC ac κ zz u q₀ lW ll A₀ w Y = df (λ {t} Tq → RKc ac κ u q₀ lW ll A₀ w Y t Tq)

RKc ac (inj₂ tt) u q₀ lW ll A₀ w Y hz Tq =
  nl (λ n → drp (yc (κΔ₁ ac u q₀ lW ll A₀ (κc₁ ac u q₀ lW ll A₀ w Y n))
                    (τ₀ (proj₁ lW , lv₁ (κc₁ ac u q₀ lW ll A₀ w Y n)))))
RKc ac (inj₂ tt) u q₀ lW ll A₀ w Y (hs hz) Tq =
  nl (λ n → nw (proj₁ (wm Tq) , hself)
              (drp₁ (proj₁ lW , lv₁ (κc₁ ac u q₀ lW ll A₀ w Y n))
                 (yc (κΔ₁ ac u q₀ lW ll A₀ (κc₁ ac u q₀ lW ll A₀ w Y n))
                     (τ₁ (proj₁ lW , lv₁ (κc₁ ac u q₀ lW ll A₀ w Y n))))))
RKc ac (inj₂ tt) u q₀ lW ll A₀ w Y (hs (hs b)) Tq = RKk ac (inj₂ tt) u q₀ ll A₀ w Y Tq tt
RKc ac (inj₂ tt) u q₀ lW ll A₀ w Y (hs (hl f)) Tq = RKk ac (inj₂ tt) u q₀ ll A₀ w Y Tq tt
RKc ac (inj₂ tt) u q₀ lW ll A₀ w Y (hs (hΩ κ g)) Tq = RKk ac (inj₂ tt) u q₀ ll A₀ w Y Tq tt
RKc ac (inj₂ tt) u q₀ lW ll A₀ w Y (hl f) Tq = RKk ac (inj₂ tt) u q₀ ll A₀ w Y Tq tt
RKc ac (inj₂ tt) u q₀ lW ll A₀ w Y (hΩ κ g) Tq = RKk ac (inj₂ tt) u q₀ ll A₀ w Y Tq tt
RKc ac (inj₁ κ) u q₀ lW ll A₀ w Y hz Tq = RKv ac κ (lv κ) u q₀ lW ll A₀ w Y Tq
RKc ac (inj₁ κ) u q₀ lW ll A₀ w Y (hs b) Tq = RKk ac (inj₁ κ) u q₀ ll A₀ w Y Tq tt
RKc ac (inj₁ κ) u q₀ lW ll A₀ w Y (hl f) Tq = RKk ac (inj₁ κ) u q₀ ll A₀ w Y Tq tt
RKc ac (inj₁ κ) u q₀ lW ll A₀ w Y (hΩ κ′ g) Tq = RKk ac (inj₁ κ) u q₀ ll A₀ w Y Tq tt

RKk ac κ u q₀ ll A₀ w Y Tq zt =
  nc κ zt (λ {W′} q lW′ →
    yc (Run ac (u (≤tr (≤tr q₀ (wm Tq)) q) lW′) ≤rf lW′ (⊲ᴮ↑ (≤tr (wm Tq) q) ll) (Ig↾ (≤tr (wm Tq) q) A₀)
          (nw (≤tr (wm Tq) q) w) (cv (≤tr (wm Tq) q) Y))
       (tg ≤rf (⊲ᴮ↑ q (tm Tq)) lW′))

κΔ₁ ac u q₀ lW ll A₀ c =
  Run ac (u (≤tr q₀ (≤w-rf T , wv₁ c)) (proj₁ lW , lv₁ c)) ≤rf (proj₁ lW , lv₁ c)
    (⊲ᴮ↑ (≤w-rf T , wv₁ c) ll) (Ig↾ (≤w-rf T , wv₁ c) A₀) (co₁ c) (Sv₁ c)

κc₁ {W = W} ac u q₀ lW ll A₀ w Y zero =
  mkCl₁ (rd₁ lW (proj₂ W) (z₁ Y)) (Lg-rd₁ lW (proj₂ W) (z₁ Y) (proj₂ lW)) (rd₁-fst lW (proj₂ W) (z₁ Y))
    (cv (≤w-rf T , rd₁-fst lW (proj₂ W) (z₁ Y)) Y) (nw (≤w-rf T , rd₁-fst lW (proj₂ W) (z₁ Y)) w)
κc₁ {W = W} ac u q₀ lW ll A₀ w Y (suc n) =
  mkCl₁ (rd₁ lW₀ (v₁ c₀) Δ₁) (Lg-rd₁ lW₀ (v₁ c₀) Δ₁ (lv₁ c₀))
    (⊲ᴮ-tr (wv₁ c₀) (rd₁-fst lW₀ (v₁ c₀) Δ₁))
    (cv (≤w-rf T , rd₁-fst lW₀ (v₁ c₀) Δ₁) (Sv₁ c₀ ⊕⟨ lW₀ ⟩ κΔ₁ ac u q₀ lW ll A₀ c₀))
    (nw (≤w-rf T , rd₁-fst lW₀ (v₁ c₀) Δ₁) (co₁ c₀))
  where
  c₀ : Cl₁ W _
  c₀ = κc₁ ac u q₀ lW ll A₀ w Y n
  lW₀ : LgW L₀ (proj₁ W , v₁ c₀)
  lW₀ = proj₁ lW , lv₁ c₀
  Δ₁ : D (hs hz) (proj₁ W , v₁ c₀)
  Δ₁ = yc (κΔ₁ ac u q₀ lW ll A₀ c₀) (τ₁ lW₀)

RKv ac κ (inj₁ F) u q₀ lW ll A₀ w Y Tq =
  nl (λ n → drp (yc (κΔA ac u q₀ lW ll A₀ (κcL ac F u q₀ lW ll A₀ w Y n))
                    (τ₀ (lwA (κcL ac F u q₀ lW ll A₀ w Y n) , proj₂ lW))))
RKv ac κ (inj₂ _) u q₀ lW ll A₀ w Y Tq = RKa ac (fbA G κ) (fl κ) u q₀ lW ll A₀ w Y Tq

RKa ac (inj₁ F) tl u q₀ lW ll A₀ w Y Tq =
  nl (λ n → drp (yc (κΔA ac u q₀ lW ll A₀ (κcA ac F tl u q₀ lW ll A₀ w Y n))
                    (τ₀ (lwA (κcA ac F tl u q₀ lW ll A₀ w Y n) , proj₂ lW))))
RKa ac (inj₂ _) tl u q₀ lW ll A₀ w Y Tq =
  ω⋅ (drp (yc (Run ac (u q₀ lW) ≤rf lW ll A₀ w Y) (τ₀ lW)))

κΔA ac u q₀ lW ll A₀ c =
  Run ac (u (≤tr q₀ (qA c , hself)) (lwA c , proj₂ lW)) ≤rf (lwA c , proj₂ lW)
    (⊲ᴮ↑ (qA c , hself) ll) (Ig↾ (qA c , hself) A₀) (coA c) (SA c)

κcA {W = W} ac F tl u q₀ lW ll A₀ w Y zero =
  mkClA (rsA F (proj₁ W) v) (rsALg F (proj₁ lW) (Lg-sum _ (z Y) (tl (proj₁ lW)))) q (cv (q , hself) Y) (nw (q , hself) w)
  where
  v : A
  v = sum (tpA F (proj₁ W)) (z Y)
  q : _≤w_ T (proj₁ W) (rsA F (proj₁ W) v)
  q = rsA≤ F (sum-fst _ (z Y))
κcA {W = W} ac F tl u q₀ lW ll A₀ w Y (suc n) =
  mkClA (rsA F (wA c₀) v) (rsALg F (lwA c₀) (Lg-sum _ Δ (tl (lwA c₀)))) (≤w-tr T (qA c₀) q)
    (cv (q , hself) (SA c₀ ⊕⟨ (lwA c₀ , proj₂ lW) ⟩ κΔA ac u q₀ lW ll A₀ c₀)) (nw (q , hself) (coA c₀))
  where
  c₀ : ClA W _
  c₀ = κcA ac F tl u q₀ lW ll A₀ w Y n
  Δ : D hz (wA c₀ , proj₂ W)
  Δ = yc (κΔA ac u q₀ lW ll A₀ c₀) (τ₀ (lwA c₀ , proj₂ lW))
  v : A
  v = sum (tpA F (wA c₀)) Δ
  q : _≤w_ T (wA c₀) (rsA F (wA c₀) v)
  q = rsA≤ F (sum-fst _ Δ)

κcL {W = W} {κ = κ} ac F u q₀ lW ll A₀ w Y zero =
  mkClA (rs F (proj₁ W) v) (rsLg F (proj₁ lW) (rd-lg F lW t₀ dℓ (lgBd T (topBd (tpK G) κ (proj₁ W)) (proj₁ lW)))) q
    (cv (q , hself) Y) (nw (q , hself) w)
  where
  t₀ : E T κ
  t₀ = top (tpK G) κ (proj₁ W)
  dℓ : D (ℓ F) W
  dℓ = yc (d Y) (tg ≤rf (ℓ⊲ F) lW)
  v : E T κ
  v = rd F lW t₀ dℓ
  q : _≤w_ T (proj₁ W) (rs F (proj₁ W) v)
  q = rs≤ F (rd-fst F lW t₀ dℓ)
κcL {W = W} {κ = κ} ac F u q₀ lW ll A₀ w Y (suc n) =
  mkClA (rs F (wA c₀) v) (rsLg F (lwA c₀) (rd-lg F lW₀ t₀ Δ (lgBd T (topBd (tpK G) κ (wA c₀)) (lwA c₀)))) (≤w-tr T (qA c₀) q)
    (cv (q , hself) (SA c₀ ⊕⟨ lW₀ ⟩ κΔA ac u q₀ lW ll A₀ c₀)) (nw (q , hself) (coA c₀))
  where
  c₀ : ClA W _
  c₀ = κcL ac F u q₀ lW ll A₀ w Y n
  lW₀ : LgW L₀ (wA c₀ , proj₂ W)
  lW₀ = lwA c₀ , proj₂ lW
  t₀ : E T κ
  t₀ = top (tpK G) κ (wA c₀)
  Δ : D (ℓ F) (wA c₀ , proj₂ W)
  Δ = yc (κΔA ac u q₀ lW ll A₀ c₀) (tg ≤rf (ℓ⊲ F) lW₀)
  v : E T κ
  v = rd F lW₀ t₀ Δ
  q : _≤w_ T (wA c₀) (rs F (wA c₀) v)
  q = rs≤ F (rd-fst F lW₀ t₀ Δ)
```

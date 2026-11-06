# LeanT (四): 一般折叠, 带级回灌参数

> 不含记号. 入口 [LeanT](LeanT.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.
>
> 重写 `GenFoldRun`, 并把 `KindLvRun` 合进来: 两者逐行相同, 只在 "旧种类的闭包, 第 0 层目标" 一行不同 (`GenFoldRun.RKa` 查 `fbA`, `KindLvRun.RKv` 先查级回灌再退回 `fbA`). 这里那一行查模块参数 `fb : K T → Fb ⊎ ⊤` ([LeanTTree](LeanTTree.lagda.md) §6): `inj₁ F` 时按 `F` 回灌 (`κcF`), `inj₂ tt` 时有损. 原来的 `κcA` (A-回灌) 与 `κcL` (按级回灌) 都是 `κcF` 在某个 `F` 上的展开 ([LeanTFb](LeanTFb.lagda.md)).
>
> 其余各行 (状态, 目标, 结点 `RunNi`/`Ai`/`BNi`/`Chn`/`RKi`, 比较 `cmpB` 以 $\Lambda$ 为公共上界, 新种类在第 0, 1 层用 `rd₁` 回灌, 第 $\ge1$ 层保留) 与 `GenFoldRun` 逐条相同. 停机: 对数据结构递归, 结点经 `AccY`. 数据没有合法性; 世界的合法由 `nxLg`, `Lg-rd₁` 给出.
>
> | 种类 | 目标层 | 做法 |
> |---|---|---|
> | 新种类 `inj₂ tt` (坐标 `HB T`) | $0$, $1$ | 回灌: $v_0=\mathrm{rd}_1(\text{界}, z_1)$, $v_{n+1}=\mathrm{rd}_1(v_n,\Delta_n)$, 世界 $(w, v_n)$ (`κc₁`) |
> | 新种类 | $\ge2$ | 保留 (`RKk`) |
> | 旧种类, `fb κ = inj₁ F` | $0$ | 级回灌: $w_1=\mathrm{nx}(d_0)$, $w_{n+2}=\mathrm{nx}(\Delta_n)$, $\Delta_n$ 是分支在 $(w_{n+1},\beta)$ 里在级层 $\ell$ 上的输出 (`κcF`) |
> | 旧种类, `fb κ = inj₂ tt` | $0$ | 有损: 当前世界的分支, 重复 $\omega$ 次 |
> | 旧种类 | $\ge1$ | 保留 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import OCF.Lean.LeanTBase
open import OCF.Lean.LeanTTree
module OCF.Lean.LeanTFold (T : KS) (bk : Tree.BotK T) (Λ : HB (step T)) (lΛ : LgB Λ)
  (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (fb : K T → FoldTy.Fb T Λ ⊎ ⊤) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open Tree T
open Rd bk
open FoldTy T Λ
```

## §1 状态

```agda
LW : HB L₀ → Wd L₀ → Set
LW L W = L ⊲[ W ] Λ

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
kk r q l = ⊲ᴮ-tr (S→⊲ (Kup q r)) l

Bu : HB L₀ → Wd L₀ → Set
Bu ly W₀ = ∀ {W′} → W₀ ≤ W′ → LgW L₀ W′ → D ly W′
```

## §2 结点与目标

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

-- 旧种类的级回灌: 世界 (wA , 原新种类的界)
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
RunC  : ∀ {ly W₀ W} → AccY ly → (κ : K L₀) → ZK ly κ → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Df W
RKc   : ∀ {ly W₀ W} → AccY ly → (κ : K L₀) → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ∀ t {m} → Tg W t m → D t m
RKk   : ∀ {ly W₀ W t m} → AccY ly → (κ : K L₀) → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → ZK t κ → D t m
κc₁   : ∀ {ly W₀ W} → AccY ly → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ℕ → Cl₁ W ly
κΔ₁   : ∀ {ly W₀ W} → AccY ly → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → (c : Cl₁ W ly) → Df (proj₁ W , v₁ c)
RKa   : ∀ {ly W₀ W m} → AccY ly → Fb ⊎ ⊤ → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → Tg W hz m → D hz m
κcF   : ∀ {ly W₀ W} → AccY ly → Fb → Bu ly W₀ → W₀ ≤ W → LgW L₀ W → LW ly W → Ig ly W → D ly W → St W → ℕ → ClA W ly
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
    (nw p w ⨾ Int ac′ zz ≤rf lW′ (zkS r) (mkOf r (≤tr q₀ p)) (λ p′ l′ z′ → u (≤tr (≤tr q₀ p) p′) l′ (inS r z′)) n0) Y′

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

**闭包结点.** 按种类与目标层分 (文件头的表). 新种类要 $L\ge2$ 的许可 `NZ₁ t`, 所以第 $\ge2$ 层按 $t$ 的头逐行写出.

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
RKc ac (inj₁ κ) u q₀ lW ll A₀ w Y hz Tq = RKa ac (fb κ) u q₀ lW ll A₀ w Y Tq
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

RKa ac (inj₁ F) u q₀ lW ll A₀ w Y Tq =
  nl (λ n → drp (yc (κΔA ac u q₀ lW ll A₀ (κcF ac F u q₀ lW ll A₀ w Y n))
                    (τ₀ (lwA (κcF ac F u q₀ lW ll A₀ w Y n) , proj₂ lW))))
RKa ac (inj₂ _) u q₀ lW ll A₀ w Y Tq =
  ω⋅ (drp (yc (Run ac (u q₀ lW) ≤rf lW ll A₀ w Y) (τ₀ lW)))

κΔA ac u q₀ lW ll A₀ c =
  Run ac (u (≤tr q₀ (qA c , hself)) (lwA c , proj₂ lW)) ≤rf (lwA c , proj₂ lW)
    (⊲ᴮ↑ (qA c , hself) ll) (Ig↾ (qA c , hself) A₀) (coA c) (SA c)
```

**级回灌一格** (`κcF`): 第 0 格读状态在级层上的数据 `d₀`, 第 $n+1$ 格读第 $n$ 格的分支在级层 `ℓ` 上的输出; 每格的世界由 `nx` 给出.

```agda
κcF {W = W} ac F u q₀ lW ll A₀ w Y zero =
  mkClA (nx F lW (d₀ F lW Y)) (nxLg F lW (d₀ F lW Y)) (nx≤ F lW (d₀ F lW Y))
    (cv (nx≤ F lW (d₀ F lW Y) , hself) Y) (nw (nx≤ F lW (d₀ F lW Y) , hself) w)
κcF {W = W} ac F u q₀ lW ll A₀ w Y (suc n) =
  mkClA (nx F lW₀ Δ) (nxLg F lW₀ Δ) (≤w-tr T (qA c₀) (nx≤ F lW₀ Δ))
    (cv (nx≤ F lW₀ Δ , hself) (SA c₀ ⊕⟨ lW₀ ⟩ κΔA ac u q₀ lW ll A₀ c₀)) (nw (nx≤ F lW₀ Δ , hself) (coA c₀))
  where
  c₀ : ClA W _
  c₀ = κcF ac F u q₀ lW ll A₀ w Y n
  lW₀ : LgW L₀ (wA c₀ , proj₂ W)
  lW₀ = lwA c₀ , proj₂ lW
  Δ : D (ℓ F) (wA c₀ , proj₂ W)
  Δ = yc (κΔA ac u q₀ lW ll A₀ c₀) (tg ≤rf (ℓ⊲ F) lW₀)
```

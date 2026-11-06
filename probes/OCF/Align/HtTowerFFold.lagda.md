# 两种种类的折叠 (三): 折叠

> 不含记号. 入口 [HtTowerF](HtTowerF.lagda.md). 由 [HtFeedFold](HtFeedFold.lagda.md) 改写; 节点, 目标, 比较 (`cmpB`), 链 (`Chn`) 原样, 世界成对. 改了三件:
>
> 1. **旧种类的闭包抽成模块 `KG`**: `HtFeedFold` 的 `RunK`, `RKy`, `RKk`, `Kp`, `Kb`, `κc`, `κΔ`, `Walk`, `WRp` 只经过分支的两种用法: 作数据 (前缀 `Cut₀`) 与作折叠 (分支的 `Run`). 把这两样作参数 `ud`, `ur`. 数据树里的 `nκ` 用 `ur = Run (u c)`; 下面第 3 条用另一个 `ur`.
> 2. **新种类的闭包 `nμ`** (`RunM`): 目标的层是 $0$ 或 $1$ (读回层及以下) 就**回灌**: 高度分量的界一格一格升 ($x_0=\mathrm{rd}(\text{世界的界},z_1)$, $x_{n+1}=\mathrm{rd}(x_n,\Delta_n)$, $\Delta_n$ 是第 $n$ 格在第 1 层目标上的输出), 第 0 层目标取 `drp`, 第 1 层目标取 **`drp₁` 丢掉升高的分量**再嵌进目标世界 (不用并). 目标在第 2 层及以上就**保留**: 沿高度分量走到目标世界的界 (`Kp₁`), 再接 `nμ` (`Kb₁`). 状态多记一格 `z₁` (当前世界以来第 1 层的输出), 与 `z` 同法.
> 3. **沿高度坐标的走法 `Walk₁`**: 后继与 ℕ-极限照 `Walk`; 走进旧种类的 $\Omega$-极限 $\mathrm{h\Omega}\,h$ (`hLim`) 时, 这一段是一个**旧种类的闭包**, 用 `KG` 折叠, 坐标 $c$ 上的分支作数据是 `Cut₁` 从 $h(c_0)$ 到 $h(c)$, 作折叠是 `Walk₁` 从 $h(c_0)$ 到 $h(c)$ (对 $h(c)$ 结构递归).
>
> 模块参数: 一步 `S`, 最高层 $\Lambda$, 合法 `lΛ`, 与 **`one⊲`**: 第 1 层是 $\Lambda$ 在一切世界里的第一位置 (回灌要第 1 层目标; 同 `HtOutFeed` 的 `top⁺`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree using (D₊; Ht; Wd₂)
module OCF.Align.HtTowerFFold
  (S : ∀ {Kd : Wd₂ → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wd₂ → Set} {Z₀ Z₁ : Set} {W} → D₊ Kd V′ Z₀ Z₁ W → D₊ Kd V′ Z₀ Z₁ W)
  (Λ : Ht) (lΛ : LgB Λ) (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy hiding (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerTy using (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerFTree
open import OCF.Align.HtTowerFRead using (D₁; rd; rd-fst; Lg-rd; drp₁)
```

## §1 状态

```agda
LW : Ht → Wd₂ → Set
LW L W = L ⊲[ W ] Λ

record Tg (W : Wd₂) (t : Ht) (m : Wd₂) : Set where
  constructor tg
  field
    wm : W ≤ m
    tm : t ⊲[ m ] Λ
    lm : LgW₂ m
open Tg public

tg↑ : ∀ {W W′ t m} → W ≤ W′ → Tg W′ t m → Tg W t m
tg↑ q T = tg (≤tr q (wm T)) (tm T) (lm T)

τ₀ : ∀ {W} → LgW₂ W → Tg W hz W
τ₀ lW = tg ≤rf (z⊲ᴮ Λ) lW

τ₁ : ∀ {W} → LgW₂ W → Tg W (hs hz) W
τ₁ lW = tg ≤rf one⊲ lW

record Df (W : Wd₂) : Set where
  constructor df
  field
    yc : ∀ {t m} → Tg W t m → D t m
open Df public

record St (W : Wd₂) : Set where
  constructor st
  field
    d  : Df W
    z  : D₀ W
    z₁ : D₁ W
open St public

zeroD : ∀ {W} → Df W
zeroD = df (λ T → n0)

infixl 6 _⨾ᴰ_
_⨾ᴰ_ : ∀ {W} → Df W → Df W → Df W
a ⨾ᴰ b = df (λ T → yc a T ⨾ yc b T)

nlᴰ : ∀ {W} → (ℕ → Df W) → Df W
nlᴰ F = df (λ T → nl (λ n → yc (F n) T))

_⊕⟨_⟩_ : ∀ {W} → St W → LgW₂ W → Df W → St W
Y ⊕⟨ lW ⟩ Δ = st (d Y ⨾ᴰ Δ) (z Y ⨾ yc Δ (τ₀ lW)) (z₁ Y ⨾ yc Δ (τ₁ lW))

cv : ∀ {W W′} → W ≤ W′ → St W → St W′
cv q Y = st (df (λ T → yc (d Y) (tg↑ q T))) n0 n0

Stp : ∀ {W} → St W → Df W
Stp Y = df (λ {t} T → S (Ωd t ⨾ yc (d Y) T))

Ig : Ht → Wd₂ → Set
Ig ly W = ∀ {W′} → W ≤ W′ → LgW₂ W′ → D ly W′ → St W′ → Df W′

Ig↾ : ∀ {ly W W′} → W ≤ W′ → Ig ly W → Ig ly W′
Ig↾ p A₀ p′ = A₀ (≤tr p p′)

kk : ∀ {W₀ W k L} → StH W₀ k L → W₀ ≤ W → LW L W → LW k W
kk r q l = ⊲ᴮ-tr (S→⊲ (Kup q r)) l
```

## §2 节点与目标

```agda
data Rk (k t : Ht) (m : Wd₂) : Set where
  keep : StH m k t → Rk k t m
  rise : Rk k t m

rkS : ∀ {k t m} → k ⊲[ m ] t → Rk k t m
rkS hself = rise
rkS (hsuc p) = keep (ss p)
rkS (hlim n p) = keep (sl n p)
rkS (hLim e p) = keep (sL e p)

rkT : ∀ {k t m} → k ⊲[ m ] Λ → t ⊲[ m ] Λ → LgW₂ m → Rk k t m
rkT km tm lm with cmpB km tm lm lΛ
... | inj₁ t⊲k = rise
... | inj₂ k⊲t = rkS k⊲t
```

## §3 旧种类的闭包, 对分支的用法抽象

`ud`: 坐标 $c$ 上的分支 (数据); `ur`: 坐标 $c$ 上的分支在更大的世界里折叠, 给定前缀与状态. 下面与 `HtFeedFold` 的同名函数逐个对应, `Run ac (u …)` 换成 `ur`, `Cut u` 换成 `Cut₀ ud`.

```agda
module KG {ly : Ht} {w₀ : A} {β : H₀}
  (ud : ∀ {c} → w₀ ⊲ c → Lg c → D ly (c , β))
  (ur : ∀ {c} → w₀ ⊲ c → Lg c → ∀ {V} → (c , β) ≤ V → LgW₂ V → LW ly V → Ig ly V → D ly V → St V → Df V) where

  Walk : ∀ {V₁} b {a} → a ⊲ b → w₀ ⊲ a → Lg b → b ⊲ proj₁ V₁ → β ⊲[ proj₁ V₁ ] proj₂ V₁ → LgW₂ V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → Df V₁
  WRp  : ∀ {V₁ a n} (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) → a ⊲ f n → w₀ ⊲ a → (∀ m → f m ⊲ proj₁ V₁) →
         β ⊲[ proj₁ V₁ ] proj₂ V₁ → LgW₂ V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → ℕ → D ly V₁ × St V₁

  Walk b C.self ap lb bV βV lV ll A₀ co Y = zeroD
  Walk (asuc c) (C.suc p) ap lb bV βV lV ll A₀ co Y =
    Walk c p ap lb (⊲-tr (C.suc C.self) bV) βV lV ll A₀ co Y ⨾ᴰ
    ur (⊲-tr ap p) lb (⊲-tr (C.suc C.self) bV , βV) lV ll A₀ (co ⨾ Cut₀ ud c p ap lb (⊲-tr (C.suc C.self) bV) βV)
      (Y ⊕⟨ lV ⟩ Walk c p ap lb (⊲-tr (C.suc C.self) bV) βV lV ll A₀ co Y)
  Walk (alim f) {a} (C.lim n p) ap (stp , wl) bV βV lV ll A₀ co Y =
    Walk (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) βV lV ll A₀ co Y ⨾ᴰ
    nlᴰ (λ m → Walk (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (⊲-tr (C.lim (suc (m + n)) C.self) bV) βV lV ll A₀
          (proj₁ (WRp f stp wl p ap (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV) βV lV ll A₀
                    (co ⨾ Cut₀ ud (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) βV)
                    (Y ⊕⟨ lV ⟩ Walk (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) βV lV ll A₀ co Y) m))
          (proj₂ (WRp f stp wl p ap (λ m₁ → ⊲-tr (C.lim m₁ C.self) bV) βV lV ll A₀
                    (co ⨾ Cut₀ ud (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) βV)
                    (Y ⊕⟨ lV ⟩ Walk (f n) p ap (wl n) (⊲-tr (C.lim n C.self) bV) βV lV ll A₀ co Y) m)))

  WRp f stp wl p ap fV βV lV ll A₀ co Y zero = co , Y
  WRp {n = n} f stp wl p ap fV βV lV ll A₀ co Y (suc m) =
    (proj₁ (WRp f stp wl p ap fV βV lV ll A₀ co Y m) ⨾
       Cut₀ ud (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) βV) ,
    (proj₂ (WRp f stp wl p ap fV βV lV ll A₀ co Y m) ⊕⟨ lV ⟩
       Walk (f (suc (m + n))) (stp (m + n)) (⊲-tr ap (tailP f stp p m)) (wl (suc (m + n))) (fV (suc (m + n))) βV lV ll A₀
         (proj₁ (WRp f stp wl p ap fV βV lV ll A₀ co Y m)) (proj₂ (WRp f stp wl p ap fV βV lV ll A₀ co Y m)))

  module KR {W} (q₀ : (w₀ , β) ≤ W) (lW : LgW₂ W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
    record Cl : Set where
      constructor mkCl
      field
        v  : A
        lv : Lg v
        wv : proj₁ W ⊲ v
        a  : A
        ap : w₀ ⊲ a
        av : a ⊲ v
        Sv : St (v , proj₂ W)
        co : D ly (v , proj₂ W)
    open Cl public

    βv : (c : Cl) → β ⊲[ v c ] proj₂ W
    βv c = ⊲ᴮ↑ {S₀} (wv c) (proj₂ q₀)

    lWv : (c : Cl) → LgW₂ (v c , proj₂ W)
    lWv c = lv c , proj₂ lW

    κΔ : (c : Cl) → Df (v c , proj₂ W)
    κΔ c = Walk (v c) (av c) (ap c) (lv c) C.self (βv c) (lWv c) (⊲ᴮ↑ (≤A (wv c)) ll) (Ig↾ (≤A (wv c)) A₀) (co c) (Sv c)

    κc : ℕ → Cl
    κc zero =
      mkCl (sum (proj₁ W) (z Y)) (Lg-sum (proj₁ W) (z Y) (proj₁ lW)) (sum-fst (proj₁ W) (z Y)) w₀ C.self
        (⊲-tr (proj₁ q₀) (sum-fst (proj₁ W) (z Y))) (cv (≤A (sum-fst (proj₁ W) (z Y))) Y) (nw (≤A (sum-fst (proj₁ W) (z Y))) w)
    κc (suc n) =
      mkCl (sum (v c₀) Δ₀) (Lg-sum (v c₀) Δ₀ (lv c₀)) (⊲-tr (wv c₀) (sum-fst (v c₀) Δ₀)) (v c₀) (⊲-tr (ap c₀) (av c₀)) (sum-fst (v c₀) Δ₀)
        (cv (≤A (sum-fst (v c₀) Δ₀)) (Sv c₀ ⊕⟨ lWv c₀ ⟩ κΔ c₀))
        (nw (≤A (sum-fst (v c₀) Δ₀)) (co c₀ ⨾ Cut₀ ud (v c₀) (av c₀) (ap c₀) (lv c₀) C.self (βv c₀)))
      where
      c₀ : Cl
      c₀ = κc n
      Δ₀ : D₀ (v c₀ , proj₂ W)
      Δ₀ = yc (κΔ c₀) (τ₀ (lWv c₀))

    Kp : ∀ {W⁺} → W ≤ W⁺ → LgW₂ W⁺ → Df W⁺
    Kp {W⁺} wu lW⁺ =
      Walk (proj₁ W⁺) (proj₁ (≤tr q₀ wu)) C.self (proj₁ lW⁺) C.self (proj₂ (≤tr q₀ wu)) lW⁺ (⊲ᴮ↑ wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu Y)

    Kb : ∀ {W⁺ c} → W ≤ W⁺ → LgW₂ W⁺ → proj₁ W⁺ ⊲ c → Lg c → Df (c , proj₂ W⁺)
    Kb {W⁺} {c} wu lW⁺ p lc =
      ur (⊲-tr q′ p) lc (C.self , βc) (lc , proj₂ lW⁺) (⊲ᴮ↑ (≤tr wu (≤A p)) ll) (Ig↾ (≤tr wu (≤A p)) A₀)
         (nw (≤A p) ctx ⨾ Cut₀ ud c p q′ lc C.self βc)
         (cv (≤A p) Y⁺ ⊕⟨ (lc , proj₂ lW⁺) ⟩
            Walk c p q′ lc C.self βc (lc , proj₂ lW⁺) (⊲ᴮ↑ (≤tr wu (≤A p)) ll) (Ig↾ (≤tr wu (≤A p)) A₀) (nw (≤A p) ctx) (cv (≤A p) Y⁺))
      where
      q′ : w₀ ⊲ proj₁ W⁺
      q′ = proj₁ (≤tr q₀ wu)
      βc : β ⊲[ c ] proj₂ W⁺
      βc = ⊲ᴮ↑ {S₀} p (proj₂ (≤tr q₀ wu))
      ctx : D ly W⁺
      ctx = nw wu w ⨾ Cut₀ ud (proj₁ W⁺) q′ C.self (proj₁ lW⁺) C.self (proj₂ (≤tr q₀ wu))
      Y⁺ : St W⁺
      Y⁺ = cv wu Y ⊕⟨ lW⁺ ⟩ Kp wu lW⁺

    RKk : ∀ {t m} → Tg W t m → NZ t → D t m
    RKk T zz =
      yc (Kp (wm T) (lm T)) (tg ≤rf (tm T) (lm T)) ⨾
      nκ zz (λ {c} p lc → yc (Kb (wm T) (lm T) p lc) (tg ≤rf (⊲ᴮ↑ (≤A p) (tm T)) (lc , proj₂ (lm T))))

    -- 目标是第 0 层: 回灌. 别的目标: 走到目标的世界, 再保留
    RKy : ∀ t {m} → Tg W t m → D t m
    RKy hz T = nl (λ n → drp (yc (κΔ (κc n)) (τ₀ (lWv (κc n)))))
    RKy (hs b) T = RKk T tt
    RKy (hl f) T = RKk T tt
    RKy (hΩ κ g) T = RKk T tt

    RunK : Df W
    RunK = df (λ {t} T → RKy t T)
```

## §4 新种类的闭包: 回灌一格的记录

```agda
record Cl₁ (W W₀ : Wd₂) (ly : Ht) : Set where
  constructor mkCl₁
  field
    v₁  : H₀
    lv₁ : LgB v₁
    wv₁ : proj₂ W ⊲[ proj₁ W ] v₁
    a₁  : H₀
    ap₁ : proj₂ W₀ ⊲[ proj₁ W ] a₁
    av₁ : a₁ ⊲[ proj₁ W ] v₁
    Sv₁ : St (proj₁ W , v₁)
    co₁ : D ly (proj₁ W , v₁)
open Cl₁ public

Bu : Ht → Wd₂ → Set
Bu ly W₀ = ∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → D ly W′
```

## §5 折叠

```agda
Run   : ∀ {ly W₀ W} → AccY ly → D ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Df W
Rpt   : ∀ {ly W₀ W} → AccY ly → (ℕ → D ly W₀) → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → ℕ → D ly W × St W
RunNi : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Df W
Ai    : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW k W → LW ly W → Ig ly W → D ly W → Ig k W
Chn   : ∀ {k W} → AccY k → LW k W → LgW₂ W → Ig k W → St W → ℕ → D k W × (D k W × St W)
RKi   : ∀ {ly W₀ W k t m} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → Rk k t m → D t m
BNi   : ∀ {ly W₀ W k W′} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgW₂ W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → LW k W → W ≤ W′ → LgW₂ W′ → D k W′ → Df W′
Walk₁ : ∀ {ly W₀ V₁} → AccY ly → NZ ly → Bu ly W₀ → (b : H₀) {a : H₀} → a ⊲[ proj₁ V₁ ] b → proj₂ W₀ ⊲[ proj₁ V₁ ] a → LgB b → b ⊲[ proj₁ V₁ ] proj₂ V₁ →
        proj₁ W₀ ⊲ proj₁ V₁ → LgW₂ V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → Df V₁
WRp₁  : ∀ {ly W₀ V₁ a n} → AccY ly → NZ ly → Bu ly W₀ → (f : ℕ → H₀) (stp : ∀ {w} n → f n ⊲[ w ] f (suc n)) (lf : ∀ n → LgB (f n)) →
        a ⊲[ proj₁ V₁ ] f n → proj₂ W₀ ⊲[ proj₁ V₁ ] a → (∀ m → f m ⊲[ proj₁ V₁ ] proj₂ V₁) → proj₁ W₀ ⊲ proj₁ V₁ →
        LgW₂ V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → ℕ → D ly V₁ × St V₁
RunM  : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → Df W
RKμ   : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → ∀ t {m} → Tg W t m → D t m
RKμk  : ∀ {ly W₀ W t m} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → NZ₁ t → D t m
Kp₁   : ∀ {ly W₀ W W⁺} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → W ≤ W⁺ → LgW₂ W⁺ → Df W⁺
Kb₁   : ∀ {ly W₀ W W⁺ W′} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → W ≤ W⁺ → LgW₂ W⁺ → W⁺ ≤ W′ → LgW₂ W′ → Df W′
κc₁   : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → D ly W → St W → ℕ → Cl₁ W W₀ ly
κΔ₁   : ∀ {ly W₀ W} → AccY ly → NZ ly → Bu ly W₀ → W₀ ≤ W → LgW₂ W → LW ly W → Ig ly W → (c : Cl₁ W W₀ ly) → Df (proj₁ W , v₁ c)

Run ac n0 q₀ lW ll A₀ w Y = zeroD
Run ac n1 q₀ lW ll A₀ w Y = A₀ ≤rf lW w Y
Run ac (x ⨾ y) q₀ lW ll A₀ w Y =
  Run ac x q₀ lW ll A₀ w Y ⨾ᴰ Run ac y q₀ lW ll A₀ (w ⨾ nw q₀ x) (Y ⊕⟨ lW ⟩ Run ac x q₀ lW ll A₀ w Y)
Run ac (nl F) q₀ lW ll A₀ w Y =
  nlᴰ (λ n → Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))
Run ac (nw p x) q₀ lW ll A₀ w Y = Run ac x (≤tr p q₀) lW ll A₀ w Y
Run (acc f) (ni r u) q₀ lW ll A₀ w Y = RunNi (acc f) (f r) r u q₀ lW ll A₀ w Y
Run ac (nκ zz u) q₀ lW ll A₀ w Y =
  KG.KR.RunK u (λ p lc q lV ll′ A′ co′ Y′ → Run ac (u p lc) q lV ll′ A′ co′ Y′) q₀ lW ll A₀ w Y
Run {ly} ac (nμ zz u) q₀ lW ll A₀ w Y = RunM ac (nz₁→nz ly zz) u q₀ lW ll A₀ w Y

Rpt ac F q₀ lW ll A₀ w Y zero = w , Y
Rpt ac F q₀ lW ll A₀ w Y (suc n) =
  (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n) ⨾ nw q₀ (F n)) ,
  (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n) ⊕⟨ lW ⟩ Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))

RunNi ac ac′ r u q₀ lW ll A₀ w Y =
  df (λ T → RKi ac ac′ r u q₀ lW ll A₀ w Y T (rkT (⊲ᴮ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T)))

Ai ac ac′ r u q₀ hk ll A₀ w {W′} p lW′ z Y′ =
  Run ac (u (≤tr q₀ p) lW′ (inS r z)) ≤rf lW′ (⊲ᴮ↑ p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac′ z ≤rf lW′ (NZ-S r) (NZ₁-S r) (mkOf r (≤tr q₀ p)) (λ p′ l′ z′ → u (≤tr (≤tr q₀ p) p′) l′ (inS r z′)) n0) Y′

BNi ac ac′ r u q₀ ll A₀ w Y hk p lW′ z =
  Ai ac ac′ r u q₀ hk ll A₀ w p lW′ z
    (cv p Y ⊕⟨ lW′ ⟩ Run ac′ z ≤rf lW′ (⊲ᴮ↑ p hk) (Ig↾ p (Ai ac ac′ r u q₀ hk ll A₀ w)) n0 (cv p Y))

Chn ac′ hk lW A² Y zero = n0 , (yc (d Y) (tg ≤rf hk lW) , Y)
Chn ac′ hk lW A² Y (suc n) =
  (proj₁ (Chn ac′ hk lW A² Y n) ⨾ proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ,
  (yc (Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n))))
      (tg ≤rf hk lW) ,
   (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)) ⊕⟨ lW ⟩
      Run ac′ (proj₁ (proj₂ (Chn ac′ hk lW A² Y n))) ≤rf lW hk A² (proj₁ (Chn ac′ hk lW A² Y n)) (proj₂ (proj₂ (Chn ac′ hk lW A² Y n)))))

RKi ac ac′ r u q₀ lW ll A₀ w Y T (keep R′) =
  ni R′ (λ {W′} p lW′ y →
    yc (BNi ac ac′ r u q₀ ll A₀ w Y (kk r q₀ ll) (≤tr (wm T) p) lW′ (outS R′ y))
       (tg ≤rf (⊲ᴮ↑ p (tm T)) lW′))
RKi ac ac′ r u q₀ lW ll A₀ w Y T rise =
  nl (λ n →
    yc (Run ac′ (proj₁ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))) ≤rf lW (kk r q₀ ll)
              (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w)
              (proj₁ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n))
              (proj₂ (proj₂ (Chn ac′ (kk r q₀ ll) lW (Ai ac ac′ r u q₀ (kk r q₀ ll) ll A₀ w) Y n)))) T)
```

**沿高度坐标走** (`Walk₁`). `hLim` 一行: 先走到 $h(c_0)$, 这一段的其余部分是旧种类的闭包, 基世界取当前世界, 交给 `KG`.

```agda
Walk₁ ac zy u b hself ap lb bV q lV ll A₀ co Y = zeroD
Walk₁ ac zy u (hs b) (hsuc P) ap lb bV q lV ll A₀ co Y =
  Walk₁ ac zy u b P ap lb (⊲ᴮ-tr (hsuc hself) bV) q lV ll A₀ co Y ⨾ᴰ
  Run ac (u (q , ⊲ᴮ-tr ap P) (proj₁ lV , lb)) (C.self , ⊲ᴮ-tr (hsuc hself) bV) lV ll A₀
    (co ⨾ Cut₁ zy u b P ap lb (⊲ᴮ-tr (hsuc hself) bV) q (proj₁ lV))
    (Y ⊕⟨ lV ⟩ Walk₁ ac zy u b P ap lb (⊲ᴮ-tr (hsuc hself) bV) q lV ll A₀ co Y)
Walk₁ ac zy u (hl f) (hlim n P) ap (stp , lf) bV q lV ll A₀ co Y =
  Walk₁ ac zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q lV ll A₀ co Y ⨾ᴰ
  nlᴰ (λ m → Walk₁ ac zy u (f (suc (m + n))) (stp (m + n)) (⊲ᴮ-tr ap (tailᴮ f stp P m)) (lf (suc (m + n))) (⊲ᴮ-tr (hlim (suc (m + n)) hself) bV) q lV ll A₀
        (proj₁ (WRp₁ ac zy u f stp lf P ap (λ m₁ → ⊲ᴮ-tr (hlim m₁ hself) bV) q lV ll A₀
                  (co ⨾ Cut₁ zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q (proj₁ lV))
                  (Y ⊕⟨ lV ⟩ Walk₁ ac zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q lV ll A₀ co Y) m))
        (proj₂ (WRp₁ ac zy u f stp lf P ap (λ m₁ → ⊲ᴮ-tr (hlim m₁ hself) bV) q lV ll A₀
                  (co ⨾ Cut₁ zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q (proj₁ lV))
                  (Y ⊕⟨ lV ⟩ Walk₁ ac zy u (f n) P ap (lf n) (⊲ᴮ-tr (hlim n hself) bV) q lV ll A₀ co Y) m)))
Walk₁ {ly} {W₀} {V₁} ac zy u (hΩ tt h) (hLim {c = c₀} e P) ap (mo , lh) bV q lV ll A₀ co Y =
  Walk₁ ac zy u (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lV))) (⊲ᴮ-tr (hLim e hself) bV) q lV ll A₀ co Y ⨾ᴰ
  KG.KR.RunK {ly} {proj₁ V₁} {proj₂ V₁}
    (λ {c} p lc → Cut₁ zy u (h c) (mo lc (⊲-tr e p) C.self (⊲-tr e p)) (⊲ᴮ↑ {S₀} p (⊲ᴮ-tr ap P)) (lh c lc)
                       (⊲ᴮ-tr {S₀} (hLim C.self hself) (⊲ᴮ↑ {S₀} p bV)) (⊲-tr q p) lc)
    (λ {c} p lc {V} qV lV′ ll′ A′ co′ Y′ →
       Walk₁ ac zy u (h c) (⊲ᴮ↑ {S₀} (proj₁ qV) (mo lc (⊲-tr e p) C.self (⊲-tr e p))) (⊲ᴮ↑ {S₀} (⊲-tr p (proj₁ qV)) (⊲ᴮ-tr ap P)) (lh c lc)
             (⊲ᴮ-tr {S₀} (⊲ᴮ↑ {S₀} (proj₁ qV) (⊲ᴮ-tr {S₀} (hLim C.self hself) (⊲ᴮ↑ {S₀} p bV))) (proj₂ qV)) (⊲-tr (⊲-tr q p) (proj₁ qV)) lV′ ll′ A′ co′ Y′)
    ≤rf lV ll A₀
    (co ⨾ Cut₁ zy u (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lV))) (⊲ᴮ-tr (hLim e hself) bV) q (proj₁ lV))
    (Y ⊕⟨ lV ⟩ Walk₁ ac zy u (h c₀) P ap (lh c₀ (lg⊲ e (proj₁ lV))) (⊲ᴮ-tr (hLim e hself) bV) q lV ll A₀ co Y)

WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y zero = co , Y
WRp₁ {n = n} ac zy u f stp lf p ap fV q lV ll A₀ co Y (suc m) =
  (proj₁ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m) ⨾
     Cut₁ zy u (f (suc (m + n))) (stp (m + n)) (⊲ᴮ-tr ap (tailᴮ f stp p m)) (lf (suc (m + n))) (fV (suc (m + n))) q (proj₁ lV)) ,
  (proj₂ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m) ⊕⟨ lV ⟩
     Walk₁ ac zy u (f (suc (m + n))) (stp (m + n)) (⊲ᴮ-tr ap (tailᴮ f stp p m)) (lf (suc (m + n))) (fV (suc (m + n))) q lV ll A₀
       (proj₁ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m)) (proj₂ (WRp₁ ac zy u f stp lf p ap fV q lV ll A₀ co Y m)))
```

**新种类的闭包.** 目标层 $0$: 回灌, `drp`. 目标层 $1$: 回灌, `drp₁` 丢掉升高的高度分量, 嵌进目标世界. 目标层 $\ge2$: 走到目标世界的高度界, 再保留.

```agda
RunM ac zy u q₀ lW ll A₀ w Y = df (λ {t} T → RKμ ac zy u q₀ lW ll A₀ w Y t T)

RKμ ac zy u q₀ lW ll A₀ w Y hz T =
  nl (λ n → drp (yc (κΔ₁ ac zy u q₀ lW ll A₀ (κc₁ ac zy u q₀ lW ll A₀ w Y n))
                    (τ₀ (proj₁ lW , lv₁ (κc₁ ac zy u q₀ lW ll A₀ w Y n)))))
RKμ ac zy u q₀ lW ll A₀ w Y (hs hz) T =
  nl (λ n → nw (proj₁ (wm T) , hself)
              (drp₁ (proj₁ lW , lv₁ (κc₁ ac zy u q₀ lW ll A₀ w Y n))
                 (yc (κΔ₁ ac zy u q₀ lW ll A₀ (κc₁ ac zy u q₀ lW ll A₀ w Y n))
                     (τ₁ (proj₁ lW , lv₁ (κc₁ ac zy u q₀ lW ll A₀ w Y n))))))
RKμ ac zy u q₀ lW ll A₀ w Y (hs (hs b)) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hs (hl f)) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hs (hΩ κ g)) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hl f) T = RKμk ac zy u q₀ ll A₀ w Y T tt
RKμ ac zy u q₀ lW ll A₀ w Y (hΩ κ g) T = RKμk ac zy u q₀ ll A₀ w Y T tt

RKμk ac zy u q₀ ll A₀ w Y T zz₁ =
  yc (Kp₁ ac zy u q₀ ll A₀ w Y (wm T) (lm T)) (tg ≤rf (tm T) (lm T)) ⨾
  nμ zz₁ (λ {W′} q lW′ → yc (Kb₁ ac zy u q₀ ll A₀ w Y (wm T) (lm T) q lW′) (tg ≤rf (⊲ᴮ↑ q (tm T)) lW′))

Kp₁ {W⁺ = W⁺} ac zy u q₀ ll A₀ w Y wu lW⁺ =
  Walk₁ ac zy u (proj₂ W⁺) (proj₂ (≤tr q₀ wu)) hself (proj₂ lW⁺) hself (proj₁ (≤tr q₀ wu)) lW⁺ (⊲ᴮ↑ wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu Y)

Kb₁ {W⁺ = W⁺} {W′} ac zy u q₀ ll A₀ w Y wu lW⁺ q lW′ =
  Run ac (u (≤tr (≤tr q₀ wu) q) lW′) ≤rf lW′ (⊲ᴮ↑ (≤tr wu q) ll) (Ig↾ (≤tr wu q) A₀)
    (nw q (nw wu w ⨾ Cut₁ zy u (proj₂ W⁺) (proj₂ (≤tr q₀ wu)) hself (proj₂ lW⁺) hself (proj₁ (≤tr q₀ wu)) (proj₁ lW⁺)) ⨾
       Cut₁ zy u (proj₂ W′) (proj₂ q) (⊲ᴮ↑ {S₀} (proj₁ q) (proj₂ (≤tr q₀ wu))) (proj₂ lW′) hself (proj₁ (≤tr (≤tr q₀ wu) q)) (proj₁ lW′))
    (cv q (cv wu Y ⊕⟨ lW⁺ ⟩ Kp₁ ac zy u q₀ ll A₀ w Y wu lW⁺) ⊕⟨ lW′ ⟩
       Walk₁ ac zy u (proj₂ W′) (proj₂ q) (⊲ᴮ↑ {S₀} (proj₁ q) (proj₂ (≤tr q₀ wu))) (proj₂ lW′) hself (proj₁ (≤tr (≤tr q₀ wu) q)) lW′
         (⊲ᴮ↑ (≤tr wu q) ll) (Ig↾ (≤tr wu q) A₀)
         (nw q (nw wu w ⨾ Cut₁ zy u (proj₂ W⁺) (proj₂ (≤tr q₀ wu)) hself (proj₂ lW⁺) hself (proj₁ (≤tr q₀ wu)) (proj₁ lW⁺)))
         (cv q (cv wu Y ⊕⟨ lW⁺ ⟩ Kp₁ ac zy u q₀ ll A₀ w Y wu lW⁺)))

κc₁ {W₀ = W₀} {W} ac zy u q₀ lW ll A₀ w Y zero =
  mkCl₁ (rd lW (proj₂ W) (z₁ Y)) (Lg-rd lW (proj₂ W) (z₁ Y) (proj₂ lW)) (rd-fst lW (proj₂ W) (z₁ Y)) (proj₂ W₀) hself
    (⊲ᴮ-tr (proj₂ q₀) (rd-fst lW (proj₂ W) (z₁ Y)))
    (cv (C.self , rd-fst lW (proj₂ W) (z₁ Y)) Y) (nw (C.self , rd-fst lW (proj₂ W) (z₁ Y)) w)
κc₁ {W₀ = W₀} {W} ac zy u q₀ lW ll A₀ w Y (suc n) =
  mkCl₁ (rd (proj₁ lW , lv₁ c₀) (v₁ c₀) Δ₁) (Lg-rd (proj₁ lW , lv₁ c₀) (v₁ c₀) Δ₁ (lv₁ c₀))
    (⊲ᴮ-tr (wv₁ c₀) (rd-fst (proj₁ lW , lv₁ c₀) (v₁ c₀) Δ₁)) (v₁ c₀) (⊲ᴮ-tr (ap₁ c₀) (av₁ c₀)) (rd-fst (proj₁ lW , lv₁ c₀) (v₁ c₀) Δ₁)
    (cv (C.self , rd-fst (proj₁ lW , lv₁ c₀) (v₁ c₀) Δ₁) (Sv₁ c₀ ⊕⟨ (proj₁ lW , lv₁ c₀) ⟩ κΔ₁ ac zy u q₀ lW ll A₀ c₀))
    (nw (C.self , rd-fst (proj₁ lW , lv₁ c₀) (v₁ c₀) Δ₁)
        (co₁ c₀ ⨾ Cut₁ zy u (v₁ c₀) (av₁ c₀) (ap₁ c₀) (lv₁ c₀) hself (proj₁ q₀) (proj₁ lW)))
  where
  c₀ : Cl₁ W W₀ _
  c₀ = κc₁ ac zy u q₀ lW ll A₀ w Y n
  Δ₁ : D₁ (proj₁ W , v₁ c₀)
  Δ₁ = yc (κΔ₁ ac zy u q₀ lW ll A₀ c₀) (τ₁ (proj₁ lW , lv₁ c₀))

κΔ₁ ac zy u q₀ lW ll A₀ c =
  Walk₁ ac zy u (v₁ c) (av₁ c) (ap₁ c) (lv₁ c) hself (proj₁ q₀) (proj₁ lW , lv₁ c) (⊲ᴮ↑ (C.self , wv₁ c) ll) (Ig↾ (C.self , wv₁ c) A₀) (co₁ c) (Sv₁ c)
```

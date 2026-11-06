# 事件世界上的真折叠 (三): 折叠

> 不含记号. 入口 [EvFold](EvFold.lagda.md). 由 [HtTowerFFold](HtTowerFFold.lagda.md) 改写. 节点, 目标, 比较 (`cmpB`, 种类结构是 `T`), 链 (`Chn`), `A`-种类的闭包 (`KG`) 原样, 世界换成 `Wε = A × Hist`. 改了的只有事件种类的闭包 `nε κ` (`RunE`):
>
> 1. **回灌.** 目标的层在 κ 的读回层及以下 (κ₀: 第 0, 1 层; κ₁: 第 0, 1, 2 层) 就回灌. 格 $n$ 的世界是 $(\mathrm{proj}_1 W, H_n)$, $H_0 = e_0 ∷ \mathrm{proj}_2 W$, $H_{n+1} = e_{n+1} ∷ H_n$; 事件 $e_n$ 的增量是**折叠自己的输出**的读回: $e_0$ 读状态里读回层的累积 (`zRL κ Y`, 同 `HtTowerFFold.κc₁` 的 `z₁ Y`), $e_{n+1}$ 读第 $n$ 格在读回层目标上的输出 (`yc (κΔε c) (τRL κ …)`). 读回是 `RB κ` (`rd₁` 或 `rd₂`, 从 0 读起); 事件接上后界字面地是旧界 ⊞ 增量 (`AdmEvBase.new-gen₀`). 输出落回目标世界: 第 0 层 `drp`, 第 1 层 `drp₁`, 第 2 层 `drp₂` (丢掉格加上的事件, 移植目标世界的新事件).
> 2. **保留.** 目标更高 (κ₀: $\ge2$; κ₁: $\ge3$): 沿新事件从闭包的世界走到目标世界 (`Kpε`, 离散走法 `WalkE`), 再接 `nε κ` (`Kbε`).
> 3. **离散走法 `WalkE`**: 区间 $[H_1, H_2)$ 上依次折叠分支在 $H_1, \dots$ 处的树, 状态逐格累加. 与 `HtTowerFFold.Walk₁` 的差: 不沿高度坐标走, 所以**不进坐标内部, 不调用别的种类的闭包** (`Walk₁` 在 `hLim` 处要交给 `KG`). 格 $n+1$ 的区间只有一个世界 $H_n$; 格 0 的区间是 $[\mathrm{proj}_2 W_0, H_0)$.
>
> 模块参数: 一步 `S`, 最高层 $\Lambda$, 合法 `lΛ`, `one⊲`, `two⊲` (第 1, 2 层是 $\Lambda$ 在一切世界里的第一位置; 回灌要第 1, 2 层目标). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.EvFoldTree using (D₊; Ht; Wε; Kᵉ)
module OCF.Align.EvFoldFold
  (S : ∀ {Kd : Wε → Ht → Set} {V′ : ∀ {W k} → Kd W k → Wε → Set} {Z₀ : Set} {Zε : Kᵉ → Set} {W} → D₊ Kd V′ Z₀ Zε W → D₊ Kd V′ Z₀ Zε W)
  (Λ : Ht) (lΛ : LgB Λ) (one⊲ : ∀ {w} → hs hz ⊲[ w ] Λ) (two⊲ : ∀ {w} → hs (hs hz) ⊲[ w ] Λ) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; lg⊲; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy hiding (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.HtTowerTy using (HB; hs; hz; _⊲[_]_; LgB)
open import OCF.Align.EvFoldTree hiding (D₊; Ht; Wε; Kᵉ)
open import OCF.Align.EvFoldRead using (D₁; D₂; RLay; evRB; drp₁; drp₂)
```

## §1 状态

```agda
LW : Ht → Wε → Set
LW L W = L ⊲[ W ] Λ

record Tg (W : Wε) (t : Ht) (m : Wε) : Set where
  constructor tg
  field
    wm : W ≤ m
    tm : t ⊲[ m ] Λ
    lm : LgWε m
open Tg public

tg↑ : ∀ {W W′ t m} → W ≤ W′ → Tg W′ t m → Tg W t m
tg↑ q T = tg (≤tr q (wm T)) (tm T) (lm T)

τ₀ : ∀ {W} → LgWε W → Tg W hz W
τ₀ lW = tg ≤rf (z⊲ᴮ Λ) lW

τ₁ : ∀ {W} → LgWε W → Tg W (hs hz) W
τ₁ lW = tg ≤rf one⊲ lW

τ₂ : ∀ {W} → LgWε W → Tg W (hs (hs hz)) W
τ₂ lW = tg ≤rf two⊲ lW

record Df (W : Wε) : Set where
  constructor df
  field
    yc : ∀ {t m} → Tg W t m → D t m
open Df public

record St (W : Wε) : Set where
  constructor st
  field
    d  : Df W
    z  : D₀ W
    z₁ : D₁ W
    z₂ : D₂ W
open St public

zeroD : ∀ {W} → Df W
zeroD = df (λ T → n0)

infixl 6 _⨾ᴰ_
_⨾ᴰ_ : ∀ {W} → Df W → Df W → Df W
a ⨾ᴰ b = df (λ T → yc a T ⨾ yc b T)

nlᴰ : ∀ {W} → (ℕ → Df W) → Df W
nlᴰ F = df (λ T → nl (λ n → yc (F n) T))

_⊕⟨_⟩_ : ∀ {W} → St W → LgWε W → Df W → St W
Y ⊕⟨ lW ⟩ Δ = st (d Y ⨾ᴰ Δ) (z Y ⨾ yc Δ (τ₀ lW)) (z₁ Y ⨾ yc Δ (τ₁ lW)) (z₂ Y ⨾ yc Δ (τ₂ lW))

cv : ∀ {W W′} → W ≤ W′ → St W → St W′
cv q Y = st (df (λ T → yc (d Y) (tg↑ q T))) n0 n0 n0

Stp : ∀ {W} → St W → Df W
Stp Y = df (λ {t} T → S (Ωd t ⨾ yc (d Y) T))

Ig : Ht → Wε → Set
Ig ly W = ∀ {W′} → W ≤ W′ → LgWε W′ → D ly W′ → St W′ → Df W′

Ig↾ : ∀ {ly W W′} → W ≤ W′ → Ig ly W → Ig ly W′
Ig↾ p A₀ p′ = A₀ (≤tr p p′)

kk : ∀ {W₀ W k L} → StH W₀ k L → W₀ ≤ W → LW L W → LW k W
kk r q l = ⊲ᴮ-tr (S→⊲ (Kup q r)) l

-- 事件种类的读回层: 状态里的累积, 目标
zRL : ∀ κ {W} → St W → D (RLay κ) W
zRL (_ , hself) Y = z₂ Y
zRL (_ , hsuc hself) Y = z₁ Y

τRL : ∀ κ {W} → LgWε W → Tg W (RLay κ) W
τRL (_ , hself) lW = τ₂ lW
τRL (_ , hsuc hself) lW = τ₁ lW
```

## §2 节点与目标

```agda
data Rk (k t : Ht) (m : Wε) : Set where
  keep : StH m k t → Rk k t m
  rise : Rk k t m

rkS : ∀ {k t m} → k ⊲[ m ] t → Rk k t m
rkS hself = rise
rkS (hsuc p) = keep (ss p)
rkS (hlim n p) = keep (sl n p)
rkS (hLim e p) = keep (sL e p)

rkT : ∀ {k t m} → k ⊲[ m ] Λ → t ⊲[ m ] Λ → LgWε m → Rk k t m
rkT km tm lm with cmpB km tm lm lΛ
... | inj₁ t⊲k = rise
... | inj₂ k⊲t = rkS k⊲t
```

## §3 `A`-种类的闭包 (与 `HtTowerFFold.KG` 相同, 世界换成 `Wε`)

```agda
module KG {ly : Ht} {w₀ : A} {β : Hist}
  (ud : ∀ {c} → w₀ ⊲ c → Lg c → D ly (c , β))
  (ur : ∀ {c} → w₀ ⊲ c → Lg c → ∀ {V} → (c , β) ≤ V → LgWε V → LW ly V → Ig ly V → D ly V → St V → Df V) where

  Walk : ∀ {V₁} b {a} → a ⊲ b → w₀ ⊲ a → Lg b → b ⊲ proj₁ V₁ → Suf β (proj₂ V₁) → LgWε V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → Df V₁
  WRp  : ∀ {V₁ a n} (f : ℕ → A) (stp : ∀ n → f n ⊲ f (suc n)) (wl : ∀ n → Lg (f n)) → a ⊲ f n → w₀ ⊲ a → (∀ m → f m ⊲ proj₁ V₁) →
         Suf β (proj₂ V₁) → LgWε V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → ℕ → D ly V₁ × St V₁

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

  module KR {W} (q₀ : (w₀ , β) ≤ W) (lW : LgWε W) (ll : LW ly W) (A₀ : Ig ly W) (w : D ly W) (Y : St W) where
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

    lWv : (c : Cl) → LgWε (v c , proj₂ W)
    lWv c = lv c , tt

    κΔ : (c : Cl) → Df (v c , proj₂ W)
    κΔ c = Walk (v c) (av c) (ap c) (lv c) C.self (proj₂ q₀) (lWv c) (⊲ᴮ↑ (≤A (wv c)) ll) (Ig↾ (≤A (wv c)) A₀) (co c) (Sv c)

    κc : ℕ → Cl
    κc zero =
      mkCl (sum (proj₁ W) (z Y)) (Lg-sum (proj₁ W) (z Y) (proj₁ lW)) (sum-fst (proj₁ W) (z Y)) w₀ C.self
        (⊲-tr (proj₁ q₀) (sum-fst (proj₁ W) (z Y))) (cv (≤A (sum-fst (proj₁ W) (z Y))) Y) (nw (≤A (sum-fst (proj₁ W) (z Y))) w)
    κc (suc n) =
      mkCl (sum (v c₀) Δ₀) (Lg-sum (v c₀) Δ₀ (lv c₀)) (⊲-tr (wv c₀) (sum-fst (v c₀) Δ₀)) (v c₀) (⊲-tr (ap c₀) (av c₀)) (sum-fst (v c₀) Δ₀)
        (cv (≤A (sum-fst (v c₀) Δ₀)) (Sv c₀ ⊕⟨ lWv c₀ ⟩ κΔ c₀))
        (nw (≤A (sum-fst (v c₀) Δ₀)) (co c₀ ⨾ Cut₀ ud (v c₀) (av c₀) (ap c₀) (lv c₀) C.self (proj₂ q₀)))
      where
      c₀ : Cl
      c₀ = κc n
      Δ₀ : D₀ (v c₀ , proj₂ W)
      Δ₀ = yc (κΔ c₀) (τ₀ (lWv c₀))

    Kp : ∀ {W⁺} → W ≤ W⁺ → LgWε W⁺ → Df W⁺
    Kp {W⁺} wu lW⁺ =
      Walk (proj₁ W⁺) (proj₁ (≤tr q₀ wu)) C.self (proj₁ lW⁺) C.self (proj₂ (≤tr q₀ wu)) lW⁺ (⊲ᴮ↑ wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu Y)

    Kb : ∀ {W⁺ c} → W ≤ W⁺ → LgWε W⁺ → proj₁ W⁺ ⊲ c → Lg c → Df (c , proj₂ W⁺)
    Kb {W⁺} {c} wu lW⁺ p lc =
      ur (⊲-tr q′ p) lc (C.self , βc) (lc , tt) (⊲ᴮ↑ (≤tr wu (≤A p)) ll) (Ig↾ (≤tr wu (≤A p)) A₀)
         (nw (≤A p) ctx ⨾ Cut₀ ud c p q′ lc C.self βc)
         (cv (≤A p) Y⁺ ⊕⟨ (lc , tt) ⟩
            Walk c p q′ lc C.self βc (lc , tt) (⊲ᴮ↑ (≤tr wu (≤A p)) ll) (Ig↾ (≤tr wu (≤A p)) A₀) (nw (≤A p) ctx) (cv (≤A p) Y⁺))
      where
      q′ : w₀ ⊲ proj₁ W⁺
      q′ = proj₁ (≤tr q₀ wu)
      βc : Suf β (proj₂ W⁺)
      βc = proj₂ (≤tr q₀ wu)
      ctx : D ly W⁺
      ctx = nw wu w ⨾ Cut₀ ud (proj₁ W⁺) q′ C.self (proj₁ lW⁺) C.self βc
      Y⁺ : St W⁺
      Y⁺ = cv wu Y ⊕⟨ lW⁺ ⟩ Kp wu lW⁺

    RKk : ∀ {t m} → Tg W t m → NZ t → D t m
    RKk T zz =
      yc (Kp (wm T) (lm T)) (tg ≤rf (tm T) (lm T)) ⨾
      nκ zz (λ {c} p lc → yc (Kb (wm T) (lm T) p lc) (tg ≤rf (⊲ᴮ↑ (≤A p) (tm T)) (lc , tt)))

    RKy : ∀ t {m} → Tg W t m → D t m
    RKy hz T = nl (λ n → drp (yc (κΔ (κc n)) (τ₀ (lWv (κc n)))))
    RKy (hs b) T = RKk T tt
    RKy (hl f) T = RKk T tt
    RKy (hΩ κ g) T = RKk T tt

    RunK : Df W
    RunK = df (λ {t} T → RKy t T)
```

## §4 事件种类的闭包: 格的记录

格的世界 $(\mathrm{proj}_1 W, h_c)$; 区间 $[h_1, h_c)$ (`s₁`), 起点在闭包的世界之后 (`t₁`), 格的世界在当前世界之后 (`wc`).

```agda
record Clε (W W₀ : Wε) (ly : Ht) : Set where
  constructor mkClε
  field
    hc : Hist
    h₁ : Hist
    t₁ : Suf (proj₂ W₀) h₁
    s₁ : Suf h₁ hc
    wc : Suf (proj₂ W) hc
    Sc : St (proj₁ W , hc)
    cc : D ly (proj₁ W , hc)
open Clε public

Bu : Ht → Wε → Set
Bu ly W₀ = ∀ {W′} → W₀ ≤ W′ → LgWε W′ → D ly W′
```

## §5 折叠

```agda
Run   : ∀ {ly W₀ W} → AccY ly → D ly W₀ → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → D ly W → St W → Df W
Rpt   : ∀ {ly W₀ W} → AccY ly → (ℕ → D ly W₀) → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → D ly W → St W → ℕ → D ly W × St W
RunNi : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgWε W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → D ly W → St W → Df W
Ai    : ∀ {ly W₀ W k} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgWε W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW k W → LW ly W → Ig ly W → D ly W → Ig k W
Chn   : ∀ {k W} → AccY k → LW k W → LgWε W → Ig k W → St W → ℕ → D k W × (D k W × St W)
RKi   : ∀ {ly W₀ W k t m} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgWε W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → Rk k t m → D t m
BNi   : ∀ {ly W₀ W k W′} → AccY ly → AccY k → (r : StH W₀ k ly) → (∀ {W′} → W₀ ≤ W′ → LgWε W′ → Vs ly r W′ → D ly W′) → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → LW k W → W ≤ W′ → LgWε W′ → D k W′ → Df W′
WalkE : ∀ {ly W₀ V₁ H₁ H₂} → AccY ly → Bu ly W₀ → proj₁ W₀ ⊲ proj₁ V₁ → Suf (proj₂ W₀) H₁ → Suf H₁ H₂ → Suf H₂ (proj₂ V₁) →
        LgWε V₁ → LW ly V₁ → Ig ly V₁ → D ly V₁ → St V₁ → Df V₁
RunE  : ∀ {ly W₀ W} → AccY ly → Kᵉ → Bu ly W₀ → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → D ly W → St W → Df W
RKε   : ∀ {ly W₀ W} → AccY ly → Kᵉ → Bu ly W₀ → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → D ly W → St W → ∀ t {m} → Tg W t m → D t m
RKεk  : ∀ {ly W₀ W t m} → AccY ly → (κ : Kᵉ) → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → Tg W t m → ZE κ t → D t m
Kpε   : ∀ {ly W₀ W W⁺} → AccY ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → W ≤ W⁺ → LgWε W⁺ → Df W⁺
Kbε   : ∀ {ly W₀ W W⁺ W′} → AccY ly → Bu ly W₀ → W₀ ≤ W → LW ly W → Ig ly W → D ly W → St W → W ≤ W⁺ → LgWε W⁺ → W⁺ ≤ W′ → LgWε W′ → Df W′
κcε   : ∀ {ly W₀ W} → AccY ly → Kᵉ → Bu ly W₀ → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → D ly W → St W → ℕ → Clε W W₀ ly
κΔε   : ∀ {ly W₀ W} → AccY ly → Bu ly W₀ → W₀ ≤ W → LgWε W → LW ly W → Ig ly W → (c : Clε W W₀ ly) → Df (proj₁ W , hc c)

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
Run ac (nε κ zz u) q₀ lW ll A₀ w Y = RunE ac κ u q₀ lW ll A₀ w Y

Rpt ac F q₀ lW ll A₀ w Y zero = w , Y
Rpt ac F q₀ lW ll A₀ w Y (suc n) =
  (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n) ⨾ nw q₀ (F n)) ,
  (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n) ⊕⟨ lW ⟩ Run ac (F n) q₀ lW ll A₀ (proj₁ (Rpt ac F q₀ lW ll A₀ w Y n)) (proj₂ (Rpt ac F q₀ lW ll A₀ w Y n)))

RunNi ac ac′ r u q₀ lW ll A₀ w Y =
  df (λ T → RKi ac ac′ r u q₀ lW ll A₀ w Y T (rkT (⊲ᴮ↑ (wm T) (kk r q₀ ll)) (tm T) (lm T)))

Ai ac ac′ r u q₀ hk ll A₀ w {W′} p lW′ z Y′ =
  Run ac (u (≤tr q₀ p) lW′ (inS r z)) ≤rf lW′ (⊲ᴮ↑ p ll) (Ig↾ p A₀)
    (nw p w ⨾ Int ac′ z ≤rf lW′ (NZ-S r) (λ κ → ZE-S κ r) (mkOf r (≤tr q₀ p)) (λ p′ l′ z′ → u (≤tr (≤tr q₀ p) p′) l′ (inS r z′)) n0) Y′

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

**离散走法.** 区间 $[H_1, H_2)$, 结果在 $V_1$. 分支在 $(\mathrm{proj}_1 V_1, H')$ 处, 前缀是 `CutE` 走到 $H'$, 状态是前面各格累加.

```agda
WalkE ac u q t here r lV ll A₀ co Y = zeroD
WalkE ac u q t (there e s) r lV ll A₀ co Y =
  WalkE ac u q t s (suf-tr (there e here) r) lV ll A₀ co Y ⨾ᴰ
  Run ac (u (q , suf-tr t s) (proj₁ lV , tt)) (C.self , suf-tr (there e here) r) lV ll A₀
    (co ⨾ CutE u q (proj₁ lV) t s (suf-tr (there e here) r))
    (Y ⊕⟨ lV ⟩ WalkE ac u q t s (suf-tr (there e here) r) lV ll A₀ co Y)
```

**事件种类的闭包.** κ₀ (`(_ , hsuc hself)`): 目标层 0, 1 回灌; κ₁ (`(_ , hself)`): 目标层 0, 1, 2 回灌. 其余保留 (目标层满足 `ZE κ`).

```agda
RunE ac κ u q₀ lW ll A₀ w Y = df (λ {t} T → RKε ac κ u q₀ lW ll A₀ w Y t T)

RKε ac (_ , hsuc hself) u q₀ lW ll A₀ w Y hz T =
  nl (λ n → drp (yc (κΔε ac u q₀ lW ll A₀ (κcε ac κ₀ u q₀ lW ll A₀ w Y n)) (τ₀ (proj₁ lW , tt))))
RKε ac (_ , hsuc hself) u q₀ lW ll A₀ w Y (hs hz) T =
  nl (λ n → nw (proj₁ (wm T) , here) (drp₁ (yc (κΔε ac u q₀ lW ll A₀ (κcε ac κ₀ u q₀ lW ll A₀ w Y n)) (τ₁ (proj₁ lW , tt)))))
RKε ac (_ , hsuc hself) u q₀ lW ll A₀ w Y (hs (hs b)) T = RKεk ac κ₀ u q₀ ll A₀ w Y T tt
RKε ac (_ , hsuc hself) u q₀ lW ll A₀ w Y (hs (hl f)) T = RKεk ac κ₀ u q₀ ll A₀ w Y T tt
RKε ac (_ , hsuc hself) u q₀ lW ll A₀ w Y (hs (hΩ κ′ g)) T = RKεk ac κ₀ u q₀ ll A₀ w Y T tt
RKε ac (_ , hsuc hself) u q₀ lW ll A₀ w Y (hl f) T = RKεk ac κ₀ u q₀ ll A₀ w Y T tt
RKε ac (_ , hsuc hself) u q₀ lW ll A₀ w Y (hΩ κ′ g) T = RKεk ac κ₀ u q₀ ll A₀ w Y T tt
RKε ac (_ , hself) u q₀ lW ll A₀ w Y hz T =
  nl (λ n → drp (yc (κΔε ac u q₀ lW ll A₀ (κcε ac κ₁ u q₀ lW ll A₀ w Y n)) (τ₀ (proj₁ lW , tt))))
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hs hz) T =
  nl (λ n → nw (proj₁ (wm T) , here) (drp₁ (yc (κΔε ac u q₀ lW ll A₀ (κcε ac κ₁ u q₀ lW ll A₀ w Y n)) (τ₁ (proj₁ lW , tt)))))
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hs (hs hz)) T =
  nl (λ n → nw (proj₁ (wm T) , here) (drp₂ (yc (κΔε ac u q₀ lW ll A₀ (κcε ac κ₁ u q₀ lW ll A₀ w Y n)) (τ₂ (proj₁ lW , tt)))))
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hs (hs (hs b))) T = RKεk ac κ₁ u q₀ ll A₀ w Y T tt
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hs (hs (hl f))) T = RKεk ac κ₁ u q₀ ll A₀ w Y T tt
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hs (hs (hΩ κ′ g))) T = RKεk ac κ₁ u q₀ ll A₀ w Y T tt
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hs (hl f)) T = RKεk ac κ₁ u q₀ ll A₀ w Y T tt
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hs (hΩ κ′ g)) T = RKεk ac κ₁ u q₀ ll A₀ w Y T tt
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hl f) T = RKεk ac κ₁ u q₀ ll A₀ w Y T tt
RKε ac (_ , hself) u q₀ lW ll A₀ w Y (hΩ κ′ g) T = RKεk ac κ₁ u q₀ ll A₀ w Y T tt

RKεk ac κ u q₀ ll A₀ w Y T zz =
  yc (Kpε ac u q₀ ll A₀ w Y (wm T) (lm T)) (tg ≤rf (tm T) (lm T)) ⨾
  nε κ zz (λ {W′} q lW′ → yc (Kbε ac u q₀ ll A₀ w Y (wm T) (lm T) q lW′) (tg ≤rf (⊲ᴮ↑ q (tm T)) lW′))

Kpε {W⁺ = W⁺} ac u q₀ ll A₀ w Y wu lW⁺ =
  WalkE ac u (proj₁ (≤tr q₀ wu)) here (proj₂ (≤tr q₀ wu)) here lW⁺ (⊲ᴮ↑ wu ll) (Ig↾ wu A₀) (nw wu w) (cv wu Y)

Kbε {W⁺ = W⁺} {W′} ac u q₀ ll A₀ w Y wu lW⁺ q lW′ =
  Run ac (u (≤tr (≤tr q₀ wu) q) lW′) ≤rf lW′ (⊲ᴮ↑ (≤tr wu q) ll) (Ig↾ (≤tr wu q) A₀)
    (nw q (nw wu w ⨾ CutE u (proj₁ (≤tr q₀ wu)) (proj₁ lW⁺) here (proj₂ (≤tr q₀ wu)) here) ⨾
       CutE u (proj₁ (≤tr (≤tr q₀ wu) q)) (proj₁ lW′) (proj₂ (≤tr q₀ wu)) (proj₂ q) here)
    (cv q (cv wu Y ⊕⟨ lW⁺ ⟩ Kpε ac u q₀ ll A₀ w Y wu lW⁺) ⊕⟨ lW′ ⟩
       WalkE ac u (proj₁ (≤tr (≤tr q₀ wu) q)) (proj₂ (≤tr q₀ wu)) (proj₂ q) here lW′ (⊲ᴮ↑ (≤tr wu q) ll) (Ig↾ (≤tr wu q) A₀)
         (nw q (nw wu w ⨾ CutE u (proj₁ (≤tr q₀ wu)) (proj₁ lW⁺) here (proj₂ (≤tr q₀ wu)) here))
         (cv q (cv wu Y ⊕⟨ lW⁺ ⟩ Kpε ac u q₀ ll A₀ w Y wu lW⁺)))
```

**回灌的格.** 格 0: 事件 $e_0$ 的增量读状态的累积; 区间从闭包的世界起. 格 $n+1$: 事件的增量读第 $n$ 格在读回层目标上的输出; 区间是第 $n$ 格的世界.

```agda
κcε {W₀ = W₀} {W} ac κ u q₀ lW ll A₀ w Y zero =
  mkClε (evRB κ lW (zRL κ Y) ∷ proj₂ W) (proj₂ W₀) here (there (evRB κ lW (zRL κ Y)) (proj₂ q₀)) (there (evRB κ lW (zRL κ Y)) here)
    (cv (C.self , there (evRB κ lW (zRL κ Y)) here) Y) (nw (C.self , there (evRB κ lW (zRL κ Y)) here) w)
κcε {W₀ = W₀} {W} ac κ u q₀ lW ll A₀ w Y (suc n) =
  mkClε (eN ∷ hc c₀) (hc c₀) (suf-tr (t₁ c₀) (s₁ c₀)) (there eN here) (there eN (wc c₀))
    (cv (C.self , there eN here) (Sc c₀ ⊕⟨ (proj₁ lW , tt) ⟩ κΔε ac u q₀ lW ll A₀ c₀))
    (nw (C.self , there eN here) (cc c₀ ⨾ CutE u (proj₁ q₀) (proj₁ lW) (t₁ c₀) (s₁ c₀) here))
  where
  c₀ : Clε W W₀ _
  c₀ = κcε ac κ u q₀ lW ll A₀ w Y n
  eN : Ev
  eN = evRB κ (proj₁ lW , tt) (yc (κΔε ac u q₀ lW ll A₀ c₀) (τRL κ (proj₁ lW , tt)))

κΔε ac u q₀ lW ll A₀ c =
  WalkE ac u (proj₁ q₀) (t₁ c) (s₁ c) here (proj₁ lW , tt) (⊲ᴮ↑ (C.self , wc c) ll) (Ig↾ (C.self , wc c) A₀) (cc c) (Sc c)
```

# Ω-极限坐标上的读回包 (二): 读世界的读回与翻译, 对一切高度一条

> 不含记号. 入口 [LvOm](LvOm.lagda.md). 依赖 [LvOmLev](LvOmLev.lagda.md), 只读导入 [LvRdEmb](LvRdEmb.lagda.md) (`Emb`, `nodeA`, `nodeH` 与它们的一步定理) 与 [LvRdIf](LvRdIf.lagda.md) (`RdC`). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> **R1 读世界.** 读回与翻译都以 "读的世界" $W$ 为参数, 带两件事: $W$ 合法, $a\lhd W_A$ (外层世界在 $W$ 的 `A` 分量之下).
>
> - **翻译** `trK`/`trN`: 种类 $((x,e),\kappa)$ 进 $\Omega$-层的第 $x$ 支, 结点证据是 `sL (⊲-tr e i)`: $x\lhd a\lhd W_A$. 证据**在当前世界里**给出 (`(∀ {W} → a ⊲ proj₁ W → Ly c ⊲[ W ] L″)`), 不对一切世界.
> - **读回** `RW.rdW`: 与 `LvRdPkg.RG.rdG` 同形, 多一个 "读的世界" $W$ 与树的世界 $W_0\le W$ (`nw` 往下嵌的子树按 $W$ 读, 所以读的世界只增: `nκ` 升 `A` 分量, `nμ` 升高度分量, `nw` 不动). 过 $\Omega$-层第 $x$ 支的结点: 在公共上界 $W_A$ 之下判定 $x\lhd a$ (`dec⊲`); 可入就读成种类 $((x,e'),\cdot)$, 否则读成底 (丢掉).
> - **包** `pk c`: 对 `c : H₀` 结构递归 (`hΩ g` 处用一切 `pk (g x)`), 含种类翻译 `trK`, 结点解释 `ndS` 与它的两条一步定理. 读回 `rdc`, 翻译 `trN` 由包导出. **合法由形状给出**: `lgc` (底合法则读出合法), `fstc` (底是第一位置), 对一切 $c$ 一条证明.
> - 外层世界 $a=0$ 时 $a\lhd W_A$ 恒成立 (`z⊲`), 包就是接口 `LvRdIf.RdC` 的实例 (`rdcZ c`, 对一切 $c$).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvOmRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
  using (H₀; Ht; Wd₂; LgW₂; _≤_; D; StH; ss; sl; sL; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf; ≤tr; NZ₁; nz⊲; inS; outS; κA)
  renaming (Sk to SkH)
open import OCF.Align.HtTowerFRead using (toD; lwκ; pwκ; wκ)
open import OCF.Align.HtTowerNRead using (lxμ; ≤μ; xμ)
open import OCF.Align.LvRdEmb
open import OCF.Align.LvRdIf using (RdC)
open import OCF.Align.LvOmLev
```

## §1 结点解释与读世界的读回

```agda
module Rd (a : A) where
  open LvM a public

  record NdW (T : KS) (L : Ht) : Set where
    field
      ndR : ∀ {W₀ k} → StH W₀ k L → (W : Wd₂) → proj₁ W₀ ⊲ proj₁ W → LgW₂ W → a ⊲ proj₁ W →
            HB T → (D k W → HB T → HB T) → HB T
      fsR : ∀ {W₀ k} (r : StH W₀ k L) W q lW i b s {w} → b ⊲[ w ] ndR r W q lW i b s
      lgR : ∀ {W₀ k} (r : StH W₀ k L) W q lW i {b s} → (∀ y h {w} → h ⊲[ w ] s y h) → LgB b →
            (∀ y h → LgB h → LgB (s y h)) → LgB (ndR r W q lW i b s)
      eAR : Emb S₀ T
      eMR : NZ₁ L → Emb (step S₀) T

  module RW {T L} (N : NdW T L) where
    open NdW N

    -- nκ 处读的世界: A 分量接上坐标
    Wκ : Wd₂ → A → Wd₂
    Wκ W c = wκ (proj₁ W) c , proj₂ W

    rdW  : ∀ {W₀} (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ⊲ proj₁ W → HB T → D L W₀ → HB T
    rdpW : ∀ {W₀} (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ⊲ proj₁ W → HB T → (ℕ → D L W₀) → ℕ → HB T
    rdW W p lW i b n0 = b
    rdW W p lW i b n1 = hs b
    rdW W p lW i b (x ⨾ y) = rdW W p lW i (rdW W p lW i b x) y
    rdW W p lW i b (nl d) = hl (rdpW W p lW i b d)
    rdW W p lW i b (ni r u) = ndR r W (proj₁ p) lW i b (λ y h → rdW W ≤rf lW i h (u p lW (inS r y)))
    rdW W p lW i b (nκ _ u) =
      nodeA eAR b (λ c h → rdW (Wκ W c) (C.self , ⊲ᴮ↑ {S₀} (pwκ (proj₁ W) c) (proj₂ p)) (lwκ c (proj₁ lW) , proj₂ lW)
                              (⊲-tr i (pwκ (proj₁ W) c)) h (u (⊲-tr (proj₁ p) (pwκ (proj₁ W) c)) (lwκ c (proj₁ lW))))
    rdW W p lW i b (nμ z u) =
      nodeH (eMR z) b (λ x h → rdW (proj₁ W , xμ lW x) ≤rf (proj₁ lW , lxμ lW x) i h (u (≤tr p (≤μ lW x)) (proj₁ lW , lxμ lW x)))
    rdW W p lW i b (nw q x) = rdW W (≤tr q p) lW i b x
    rdpW W p lW i b d zero = b
    rdpW W p lW i b d (suc k) = rdW W p lW i (rdpW W p lW i b d k) (d k)

    fstW : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (x : D L W₀) {w} → b ⊲[ w ] rdW W p lW i b x
    fstW W p lW i b n0 = hself
    fstW W p lW i b n1 = hsuc hself
    fstW W p lW i b (x ⨾ y) = ⊲ᴮ-tr (fstW W p lW i b x) (fstW W p lW i (rdW W p lW i b x) y)
    fstW W p lW i b (nl d) = hlim 0 hself
    fstW W p lW i b (ni r u) = fsR r W (proj₁ p) lW i b _
    fstW W p lW i b (nκ _ u) = fst-nodeA eAR b _
    fstW W p lW i b (nμ z u) = fst-nodeH (eMR z) b _
    fstW W p lW i b (nw q x) = fstW W (≤tr q p) lW i b x

    lgW  : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (x : D L W₀) → LgB b → LgB (rdW W p lW i b x)
    lgpW : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (d : ℕ → D L W₀) → LgB b → ∀ k → LgB (rdpW W p lW i b d k)
    lgW W p lW i b n0 l = l
    lgW W p lW i b n1 l = l
    lgW W p lW i b (x ⨾ y) l = lgW W p lW i (rdW W p lW i b x) y (lgW W p lW i b x l)
    lgW W p lW i b (nl d) l = (λ k → fstW W p lW i (rdpW W p lW i b d k) (d k)) , lgpW W p lW i b d l
    lgW W p lW i b (ni r u) l =
      lgR r W (proj₁ p) lW i (λ y h → fstW W ≤rf lW i h (u p lW (inS r y))) l (λ y h lh → lgW W ≤rf lW i h (u p lW (inS r y)) lh)
    lgW W p lW i b (nκ _ u) l =
      Lg-nodeA eAR
        (λ c h → fstW (Wκ W c) (C.self , ⊲ᴮ↑ {S₀} (pwκ (proj₁ W) c) (proj₂ p)) (lwκ c (proj₁ lW) , proj₂ lW)
                      (⊲-tr i (pwκ (proj₁ W) c)) h (u (⊲-tr (proj₁ p) (pwκ (proj₁ W) c)) (lwκ c (proj₁ lW))))
        l
        (λ c h lh → lgW (Wκ W c) (C.self , ⊲ᴮ↑ {S₀} (pwκ (proj₁ W) c) (proj₂ p)) (lwκ c (proj₁ lW) , proj₂ lW)
                      (⊲-tr i (pwκ (proj₁ W) c)) h (u (⊲-tr (proj₁ p) (pwκ (proj₁ W) c)) (lwκ c (proj₁ lW))) lh)
    lgW W p lW i b (nμ z u) l =
      Lg-nodeH (eMR z)
        (λ x h → fstW (proj₁ W , xμ lW x) ≤rf (proj₁ lW , lxμ lW x) i h (u (≤tr p (≤μ lW x)) (proj₁ lW , lxμ lW x)))
        l
        (λ x h lh → lgW (proj₁ W , xμ lW x) ≤rf (proj₁ lW , lxμ lW x) i h (u (≤tr p (≤μ lW x)) (proj₁ lW , lxμ lW x)) lh)
    lgW W p lW i b (nw q x) l = lgW W (≤tr q p) lW i b x l
    lgpW W p lW i b d l zero = l
    lgpW W p lW i b d l (suc k) = lgW W p lW i (rdpW W p lW i b d k) (d k) (lgpW W p lW i b d l k)

    -- 世界长高 (树往上嵌) 时读回不变: 定义相等
    rd-nw : ∀ {W₁ W₀} (W : Wd₂) (q : W₁ ≤ W₀) (p : W₀ ≤ W) lW i b (x : D L W₁) →
            rdW W p lW i b (nw q x) ≡ rdW W (≤tr q p) lW i b x
    rd-nw W q p lW i b x = refl
```

## §2 包: 对一切高度一条

```agda
  -- 结点的读法与它的一步定理 (类型)
  NdT : (c : H₀) → Set₁
  NdT c = ∀ {T} → Emb (Lv c) T → ∀ {W₀ k} → StH W₀ k (Ly c) → (W : Wd₂) → proj₁ W₀ ⊲ proj₁ W → LgW₂ W → a ⊲ proj₁ W →
          HB T → (D k W → HB T → HB T) → HB T

  TrT : (c : H₀) → Set
  TrT c = (κ : K (Lv c)) → ∀ {L″} → (∀ {W} → a ⊲ proj₁ W → Ly c ⊲[ W ] L″) →
          (E (Lv c) κ → (W : Wd₂) → a ⊲ proj₁ W → D L″ W) → (W : Wd₂) → a ⊲ proj₁ W → D L″ W

  record Pkg (c : H₀) : Set₁ where
    field
      trK : TrT c
      ndS : NdT c
      fsS : ∀ {T} (o : Emb (Lv c) T) {W₀ k} (r : StH W₀ k (Ly c)) W q lW i b s {w} → b ⊲[ w ] ndS o r W q lW i b s
      lgS : ∀ {T} (o : Emb (Lv c) T) {W₀ k} (r : StH W₀ k (Ly c)) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS o r W q lW i b s)
  open Pkg public

  module _ {c : H₀} (P : Pkg c) where
    trN : HB (Lv c) → (W : Wd₂) → a ⊲ proj₁ W → D (Ly c) W
    trN hz W i = n0
    trN (hs x) W i = trN x W i ⨾ n1
    trN (hl f) W i = nl (λ k → trN (f k) W i)
    trN (hΩ κ h) W i = trK P κ (λ _ → hself) (λ e W′ i′ → trN (h e) W′ i′) W i

    ndi : NdW (Lv c) (Ly c)
    ndi = record { ndR = ndS P (idE (Lv c)) ; fsR = fsS P (idE (Lv c)) ; lgR = lgS P (idE (Lv c)) ; eAR = eA c ; eMR = eM c }

    rdc : ∀ {W₀} (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ⊲ proj₁ W → HB (Lv c) → D (Ly c) W₀ → HB (Lv c)
    rdc = RW.rdW ndi

    fstc : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (x : D (Ly c) W₀) {w} → b ⊲[ w ] rdc W p lW i b x
    fstc = RW.fstW ndi

    lgc : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (x : D (Ly c) W₀) → LgB b → LgB (rdc W p lW i b x)
    lgc = RW.lgW ndi

  -- 过 Ly c 本身或其下的结点 (路径可以是 hself), 外层嵌入从 step (Lv c) 出发
  ndQ : ∀ {c} → Pkg c → ∀ {T} → Emb (step (Lv c)) T → ∀ {W₀ k} → k ⊲[ W₀ ] Ly c → (W : Wd₂) → proj₁ W₀ ⊲ proj₁ W →
        LgW₂ W → a ⊲ proj₁ W → HB T → (D k W → HB T → HB T) → HB T
  ndQ {c = hz} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hz} P o (hsuc Q) W q lW i b s = ndS P (compE (inj₁E S₀) o) (ss Q) W q lW i b s
  ndQ {c = hs c} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hs c} P o (hsuc Q) W q lW i b s = ndS P (compE (inj₁E (Lv (hs c))) o) (ss Q) W q lW i b s
  ndQ {c = hl f} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hl f} P o (hlim n Q) W q lW i b s = ndS P (compE (inj₁E (Lv (hl f))) o) (sl n Q) W q lW i b s
  ndQ {c = hΩ κ g} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hΩ κ g} P o (hLim e Q) W q lW i b s = ndS P (compE (inj₁E (Lv (hΩ κ g))) o) (sL e Q) W q lW i b s

  fsQ : ∀ {c} (P : Pkg c) {T} (o : Emb (step (Lv c)) T) {W₀ k} (Q : k ⊲[ W₀ ] Ly c) W q lW i b s {w} →
        b ⊲[ w ] ndQ P o Q W q lW i b s
  fsQ {c = hz} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hz} P o (hsuc Q) W q lW i b s = fsS P (compE (inj₁E S₀) o) (ss Q) W q lW i b s
  fsQ {c = hs c} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hs c} P o (hsuc Q) W q lW i b s = fsS P (compE (inj₁E (Lv (hs c))) o) (ss Q) W q lW i b s
  fsQ {c = hl f} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hl f} P o (hlim n Q) W q lW i b s = fsS P (compE (inj₁E (Lv (hl f))) o) (sl n Q) W q lW i b s
  fsQ {c = hΩ κ g} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hΩ κ g} P o (hLim e Q) W q lW i b s = fsS P (compE (inj₁E (Lv (hΩ κ g))) o) (sL e Q) W q lW i b s

  lgQ : ∀ {c} (P : Pkg c) {T} (o : Emb (step (Lv c)) T) {W₀ k} (Q : k ⊲[ W₀ ] Ly c) W q lW i {b s} →
        (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndQ P o Q W q lW i b s)
  lgQ {c = hz} P o hself W q lW i fs lb ls = Lg-nodeH o (λ x h → fs _ h) lb (λ x h → ls _ h)
  lgQ {c = hz} P o (hsuc Q) W q lW i fs lb ls = lgS P (compE (inj₁E S₀) o) (ss Q) W q lW i fs lb ls
  lgQ {c = hs c} P o hself W q lW i fs lb ls = Lg-nodeH o (λ x h → fs _ h) lb (λ x h → ls _ h)
  lgQ {c = hs c} P o (hsuc Q) W q lW i fs lb ls = lgS P (compE (inj₁E (Lv (hs c))) o) (ss Q) W q lW i fs lb ls
  lgQ {c = hl f} P o hself W q lW i fs lb ls = Lg-nodeH o (λ x h → fs _ h) lb (λ x h → ls _ h)
  lgQ {c = hl f} P o (hlim n Q) W q lW i fs lb ls = lgS P (compE (inj₁E (Lv (hl f))) o) (sl n Q) W q lW i fs lb ls
  lgQ {c = hΩ κ g} P o hself W q lW i fs lb ls = Lg-nodeH o (λ x h → fs _ h) lb (λ x h → ls _ h)
  lgQ {c = hΩ κ g} P o (hLim e Q) W q lW i fs lb ls = lgS P (compE (inj₁E (Lv (hΩ κ g))) o) (sL e Q) W q lW i fs lb ls
```

### 各构造子的包

```agda
  -- 新种类的结点: 输入经 c 的读回读成坐标, 读在继续的世界里
  newN : ∀ {c} → Pkg c → ∀ {L″ W} (R : StH W (Ly c) L″) → (HB (Lv c) → (W′ : Wd₂) → a ⊲ proj₁ W′ → D L″ W′) →
         a ⊲ proj₁ W → D L″ W
  newN P R g i = ni R (λ {W′} p lW′ y → g (rdc P W′ ≤rf lW′ (⊲-tr i (proj₁ p)) hz (outS R y)) W′ (⊲-tr i (proj₁ p)))

  -- hz
  trK-z : TrT hz
  trK-z κ Pv g W i = nκ (nz⊲ (Pv {W} i) tt) (λ {x} p lx → g x (x , proj₂ W) (⊲-tr i p))

  ndS-z : NdT hz
  ndS-z o (ss hself) W q lW i b s = nodeA o b (λ x h → s (toD x) h)

  fsS-z : ∀ {T} (o : Emb S₀ T) {W₀ k} (r : StH W₀ k (Ly hz)) W q lW i b s {w} → b ⊲[ w ] ndS-z o r W q lW i b s
  fsS-z o (ss hself) W q lW i b s = fst-nodeA o b _

  lgS-z : ∀ {T} (o : Emb S₀ T) {W₀ k} (r : StH W₀ k (Ly hz)) W q lW i {b s} →
          (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-z o r W q lW i b s)
  lgS-z o (ss hself) W q lW i fs lb ls = Lg-nodeA o (λ x h → fs _ h) lb (λ x h → ls _ h)

  -- hs c
  module PS {c : H₀} (P : Pkg c) where
    trK-s : TrT (hs c)
    trK-s (inj₂ tt) Pv g W i = newN P (SkH (ss hself) (Pv {W} i)) g i
    trK-s (inj₁ κ) Pv g W i = trK P κ (λ i′ → ⊲ᴮ-tr (hsuc hself) (Pv i′)) g W i

    ndS-s : NdT (hs c)
    ndS-s o (ss Q) = ndQ P o Q

    fsS-s : ∀ {T} (o : Emb (Lv (hs c)) T) {W₀ k} (r : StH W₀ k (Ly (hs c))) W q lW i b s {w} → b ⊲[ w ] ndS-s o r W q lW i b s
    fsS-s o (ss Q) = fsQ P o Q

    lgS-s : ∀ {T} (o : Emb (Lv (hs c)) T) {W₀ k} (r : StH W₀ k (Ly (hs c))) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-s o r W q lW i b s)
    lgS-s o (ss Q) = lgQ P o Q

  -- hl f
  module PL {f : ℕ → H₀} (P : ∀ n → Pkg (f n)) where
    ιL : ∀ n → Emb (step (Lv (f n))) (Lv (hl f))
    ιL n = ιE {F = λ n → step (Lv (f n))} n

    trK-l : TrT (hl f)
    trK-l (n , inj₂ tt) Pv g W i = newN (P n) (SkH (sl n hself) (Pv {W} i)) g i
    trK-l (n , inj₁ κ) Pv g W i = trK (P n) κ (λ i′ → ⊲ᴮ-tr (hlim n hself) (Pv i′)) g W i

    ndS-l : NdT (hl f)
    ndS-l o (sl n Q) = ndQ (P n) (compE (ιL n) o) Q

    fsS-l : ∀ {T} (o : Emb (Lv (hl f)) T) {W₀ k} (r : StH W₀ k (Ly (hl f))) W q lW i b s {w} → b ⊲[ w ] ndS-l o r W q lW i b s
    fsS-l o (sl n Q) = fsQ (P n) (compE (ιL n) o) Q

    lgS-l : ∀ {T} (o : Emb (Lv (hl f)) T) {W₀ k} (r : StH W₀ k (Ly (hl f))) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-l o r W q lW i b s)
    lgS-l o (sl n Q) = lgQ (P n) (compE (ιL n) o) Q

  -- hΩ g: 过第 x 支的结点, 在公共上界 W_A 之下判定 x ⊲ a
  module PΩ {g : A → H₀} (P : ∀ x → Pkg (g x)) where
    ιΩ : (p : Σ A (λ x → x ⊲ a)) → Emb (step (Lv (g (proj₁ p)))) (Lv (hΩ tt g))
    ιΩ p = ιE {F = λ p → step (Lv (g (proj₁ p)))} p

    trK-Ω : TrT (hΩ tt g)
    trK-Ω ((x , e) , inj₂ tt) Pv g′ W i = newN (P x) (SkH (sL {κ = κA} {c = x} (⊲-tr e i) hself) (Pv {W} i)) g′ i
    trK-Ω ((x , e) , inj₁ κ) Pv g′ W i =
      trK (P x) κ (λ i′ → ⊲ᴮ-tr (hLim {κ = κA} {c = x} (⊲-tr e i′) hself) (Pv i′)) g′ W i

    ndΩd : ∀ {T} → Emb (Lv (hΩ tt g)) T → ∀ {W₀ k} (x : A) → k ⊲[ W₀ ] Ly (g x) → (W : Wd₂) → proj₁ W₀ ⊲ proj₁ W →
           LgW₂ W → a ⊲ proj₁ W → HB T → (D k W → HB T → HB T) → Dec (x ⊲ a) → HB T
    ndΩd o x Q W q lW i b s (yes e′) = ndQ (P x) (compE (ιΩ (x , e′)) o) Q W q lW i b s
    ndΩd o x Q W q lW i b s (no _) = b

    ndS-Ω : NdT (hΩ tt g)
    ndS-Ω o (sL {c = x} e Q) W q lW i b s = ndΩd o x Q W q lW i b s (dec⊲ (⊲-tr e q) i (proj₁ lW))

    fsΩd : ∀ {T} (o : Emb (Lv (hΩ tt g)) T) {W₀ k} (x : A) (Q : k ⊲[ W₀ ] Ly (g x)) W q lW i b s d {w} →
           b ⊲[ w ] ndΩd o x Q W q lW i b s d
    fsΩd o x Q W q lW i b s (yes e′) = fsQ (P x) (compE (ιΩ (x , e′)) o) Q W q lW i b s
    fsΩd o x Q W q lW i b s (no _) = hself

    lgΩd : ∀ {T} (o : Emb (Lv (hΩ tt g)) T) {W₀ k} (x : A) (Q : k ⊲[ W₀ ] Ly (g x)) W q lW i {b s} d →
           (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndΩd o x Q W q lW i b s d)
    lgΩd o x Q W q lW i (yes e′) fs lb ls = lgQ (P x) (compE (ιΩ (x , e′)) o) Q W q lW i fs lb ls
    lgΩd o x Q W q lW i (no _) fs lb ls = lb

    fsS-Ω : ∀ {T} (o : Emb (Lv (hΩ tt g)) T) {W₀ k} (r : StH W₀ k (Ly (hΩ tt g))) W q lW i b s {w} →
            b ⊲[ w ] ndS-Ω o r W q lW i b s
    fsS-Ω o (sL {c = x} e Q) W q lW i b s = fsΩd o x Q W q lW i b s (dec⊲ (⊲-tr e q) i (proj₁ lW))

    lgS-Ω : ∀ {T} (o : Emb (Lv (hΩ tt g)) T) {W₀ k} (r : StH W₀ k (Ly (hΩ tt g))) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-Ω o r W q lW i b s)
    lgS-Ω o (sL {c = x} e Q) W q lW i = lgΩd o x Q W q lW i (dec⊲ (⊲-tr e q) i (proj₁ lW))

  pk : ∀ c → Pkg c
  pk hz = record { trK = trK-z ; ndS = ndS-z ; fsS = fsS-z ; lgS = lgS-z }
  pk (hs c) = record { trK = PS.trK-s (pk c) ; ndS = PS.ndS-s (pk c) ; fsS = PS.fsS-s (pk c) ; lgS = PS.lgS-s (pk c) }
  pk (hl f) = record { trK = PL.trK-l P ; ndS = PL.ndS-l P ; fsS = PL.fsS-l P ; lgS = PL.lgS-l P }
    where P = λ n → pk (f n)
  pk (hΩ κ g) = record { trK = PΩ.trK-Ω P ; ndS = PΩ.ndS-Ω P ; fsS = PΩ.fsS-Ω P ; lgS = PΩ.lgS-Ω P }
    where P = λ x → pk (g x)
```

## §3 外层世界 0: 接口 `RdC` 的实例 (对一切高度)

外层世界 $a=0$ 时 $0\lhd W_A$ 对一切世界成立 (`z⊲`), 读世界的包退化成接口 `LvRdIf.RdC` 的形状: 层证据与世界无关. 代价 (定理, `LvOmLev.adm₀`): 种类下标只能是 $0$, $\Omega$-结点 $\mathrm{h\Omega}\,g$ 的层结构只剩第 0 支.

```agda
module Z where
  open Rd azero

  rdcZ : ∀ c → RdC (Lv c) (Ly c)
  rdcZ c = record
    { rdr = λ {W} lW b x → rdc (pk c) W ≤rf lW (z⊲ (proj₁ W)) b x
    ; fst = λ {W} lW b x → fstc (pk c) W ≤rf lW (z⊲ (proj₁ W)) b x
    ; lgr = λ {W} lW b x → lgc (pk c) W ≤rf lW (z⊲ (proj₁ W)) b x
    ; tr  = λ {W} x → trN (pk c) x W (z⊲ (proj₁ W)) }
```

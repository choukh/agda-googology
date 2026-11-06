# 有内容的下降 (二): 层号在 `Ht` 的读回包 (`LvOm` 加一行 κH, 外层世界 `A × H₀`)

> 不含记号. 入口 [DnFold](DnFold.lagda.md), 接口 [DnFoldIf](DnFoldIf.lagda.md). 由 [LvOmLev](LvOmLev.lagda.md) §4 与 [LvOmRd](LvOmRd.lagda.md) 改写 (KcFold 接手清单第 1 条). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> **改了三件.**
>
> 1. **层号** $c$ 从 `H₀` 换成 `Ht` (两种种类 κA, κH); 层 `LvH a c = LvW {S₁} a c` (接口 §1), 读回层 `LyH c`. $\Omega$-结点的一行对**一切种类** $\kappa$ 一条 (`PΩ`), κA 与 κH 不分开写: 种类 $((x,e),\cdot)$ 进第 $x$ 支, 结点证据 `Bd↑ S₁ i e` (外层世界 $a\le W$ 把 $e$ 搬到当前世界).
> 2. **外层世界** $a$ 从 `A` 换成 `Wd₂ = A × H₀`; "外层世界在读的世界之下" 从 $a\lhd W_A$ 换成 $a\le W$ (两个分量). 结点解释收到的树世界的关系也从 `proj₁ W₀ ⊲ proj₁ W` 换成 $W_0\le W$ (κH 的证据要高度分量也搬).
> 3. **读回的判定**: 过 $\Omega$-层第 $x$ 支的结点, 判定 `Bd S₁ κ x a`, 公共上界是读的世界 $W$ (`Bd S₁ κ x W`, $a\le W$, $W$ 合法): 就是 `KcFoldBdec.bdecLv (hs hz) : BDecK S₁` (`Lev (hs hz)` 与 `S₁` 定义相等). 不对裸坐标判定.
>
> 其余 (`RW.rdW`, `trN`, `ndQ`, `newN`, `PS`, `PL`, `pk`) 逐行照 `LvOmRd`. 合法由形状给出 (`lgc`, `fstc`, 对一切 $c$).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldRd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (Dec; yes; no)
open import OCF.Align.CumReadCF using (A; azero; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree
  using (S₁; H₀; Ht; Wd₂; LgW₂; _≤_; D; StH; ss; sl; sL; n0; n1; _⨾_; nl; ni; nκ; nμ; nw; ≤rf; ≤tr; NZ₁; nz⊲; inS; outS)
  renaming (Sk to SkH)
open import OCF.Align.HtTowerFRead using (toD; lwκ; pwκ; wκ)
open import OCF.Align.HtTowerNRead using (lxμ; ≤μ; xμ)
open import OCF.Align.LvRdEmb
open import OCF.Align.KcFoldIf using (LvW; BDecK)
open import OCF.Align.KcFoldBdec using (bdecLv)
open import OCF.Align.DnFoldIf using (LvH; LyH)
```

## §0 公共上界之下的可入判定 (两种种类一条)

```agda
bdecS₁ : BDecK S₁
bdecS₁ = bdecLv {S₀} (hs hz)
```

## §1 层的嵌入 (照 `LvOmLev` §4)

```agda
module Rd (a : Wd₂) where
  Lv : Ht → KS
  Lv = LvH a

  o⋆ : (κ : K S₁) → Σ (E S₁ κ) (λ x → Bd S₁ κ x a)
  o⋆ κ = bot S₁ κ , botBd S₁ κ a

  eA : ∀ c → Emb S₀ (Lv c)
  eA hz = idE S₀
  eA (hs c) = compE (eA c) (inj₁E (Lv c))
  eA (hl f) = compE (compE (eA (f 0)) (inj₁E (Lv (f 0)))) (ιE {F = λ n → step (Lv (f n))} 0)
  eA (hΩ κ g) = compE (compE (eA (g (bot S₁ κ))) (inj₁E (Lv (g (bot S₁ κ))))) (ιE {F = λ p → step (Lv (g (proj₁ p)))} (o⋆ κ))

  eS : ∀ c → Emb (step S₀) (step (Lv c))
  eS hz = idE (step S₀)
  eS (hs c) = compE (eS c) (inj₁E (step (Lv c)))
  eS (hl f) = compE (compE (eS (f 0)) (ιE {F = λ n → step (Lv (f n))} 0)) (inj₁E (Lv (hl f)))
  eS (hΩ κ g) = compE (compE (eS (g (bot S₁ κ))) (ιE {F = λ p → step (Lv (g (proj₁ p)))} (o⋆ κ))) (inj₁E (Lv (hΩ κ g)))

  eM : ∀ c → NZ₁ (LyH c) → Emb (step S₀) (Lv c)
  eM hz ()
  eM (hs c) _ = eS c
  eM (hl f) _ = compE (eS (f 0)) (ιE {F = λ n → step (Lv (f n))} 0)
  eM (hΩ κ g) _ = compE (eS (g (bot S₁ κ))) (ιE {F = λ p → step (Lv (g (proj₁ p)))} (o⋆ κ))

  -- 外层世界在 nκ / nμ 的继续世界之下
  iκ : ∀ (W : Wd₂) c → a ≤ W → a ≤ (wκ (proj₁ W) c , proj₂ W)
  iκ W c i = ⊲-tr (proj₁ i) (pwκ (proj₁ W) c) , ⊲ᴮ↑ {S₀} (pwκ (proj₁ W) c) (proj₂ i)
```

## §2 结点解释与读世界的读回

```agda
  record NdW (T : KS) (L : Ht) : Set where
    field
      ndR : ∀ {W₀ k} → StH W₀ k L → (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ≤ W →
            HB T → (D k W → HB T → HB T) → HB T
      fsR : ∀ {W₀ k} (r : StH W₀ k L) W q lW i b s {w} → b ⊲[ w ] ndR r W q lW i b s
      lgR : ∀ {W₀ k} (r : StH W₀ k L) W q lW i {b s} → (∀ y h {w} → h ⊲[ w ] s y h) → LgB b →
            (∀ y h → LgB h → LgB (s y h)) → LgB (ndR r W q lW i b s)
      eAR : Emb S₀ T
      eMR : NZ₁ L → Emb (step S₀) T

  module RW {T L} (N : NdW T L) where
    open NdW N

    Wκ : Wd₂ → A → Wd₂
    Wκ W c = wκ (proj₁ W) c , proj₂ W

    rdW  : ∀ {W₀} (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ≤ W → HB T → D L W₀ → HB T
    rdpW : ∀ {W₀} (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ≤ W → HB T → (ℕ → D L W₀) → ℕ → HB T
    rdW W p lW i b n0 = b
    rdW W p lW i b n1 = hs b
    rdW W p lW i b (x ⨾ y) = rdW W p lW i (rdW W p lW i b x) y
    rdW W p lW i b (nl d) = hl (rdpW W p lW i b d)
    rdW W p lW i b (ni r u) = ndR r W p lW i b (λ y h → rdW W ≤rf lW i h (u p lW (inS r y)))
    rdW W p lW i b (nκ _ u) =
      nodeA eAR b (λ c h → rdW (Wκ W c) (C.self , ⊲ᴮ↑ {S₀} (pwκ (proj₁ W) c) (proj₂ p)) (lwκ c (proj₁ lW) , proj₂ lW)
                              (iκ W c i) h (u (⊲-tr (proj₁ p) (pwκ (proj₁ W) c)) (lwκ c (proj₁ lW))))
    rdW W p lW i b (nμ z u) =
      nodeH (eMR z) b (λ x h → rdW (proj₁ W , xμ lW x) ≤rf (proj₁ lW , lxμ lW x) (≤tr i (≤μ lW x)) h
                                   (u (≤tr p (≤μ lW x)) (proj₁ lW , lxμ lW x)))
    rdW W p lW i b (nw q x) = rdW W (≤tr q p) lW i b x
    rdpW W p lW i b d zero = b
    rdpW W p lW i b d (suc k) = rdW W p lW i (rdpW W p lW i b d k) (d k)

    fstW : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (x : D L W₀) {w} → b ⊲[ w ] rdW W p lW i b x
    fstW W p lW i b n0 = hself
    fstW W p lW i b n1 = hsuc hself
    fstW W p lW i b (x ⨾ y) = ⊲ᴮ-tr (fstW W p lW i b x) (fstW W p lW i (rdW W p lW i b x) y)
    fstW W p lW i b (nl d) = hlim 0 hself
    fstW W p lW i b (ni r u) = fsR r W p lW i b _
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
      lgR r W p lW i (λ y h → fstW W ≤rf lW i h (u p lW (inS r y))) l (λ y h lh → lgW W ≤rf lW i h (u p lW (inS r y)) lh)
    lgW W p lW i b (nκ _ u) l =
      Lg-nodeA eAR
        (λ c h → fstW (Wκ W c) (C.self , ⊲ᴮ↑ {S₀} (pwκ (proj₁ W) c) (proj₂ p)) (lwκ c (proj₁ lW) , proj₂ lW)
                      (iκ W c i) h (u (⊲-tr (proj₁ p) (pwκ (proj₁ W) c)) (lwκ c (proj₁ lW))))
        l
        (λ c h lh → lgW (Wκ W c) (C.self , ⊲ᴮ↑ {S₀} (pwκ (proj₁ W) c) (proj₂ p)) (lwκ c (proj₁ lW) , proj₂ lW)
                      (iκ W c i) h (u (⊲-tr (proj₁ p) (pwκ (proj₁ W) c)) (lwκ c (proj₁ lW))) lh)
    lgW W p lW i b (nμ z u) l =
      Lg-nodeH (eMR z)
        (λ x h → fstW (proj₁ W , xμ lW x) ≤rf (proj₁ lW , lxμ lW x) (≤tr i (≤μ lW x)) h (u (≤tr p (≤μ lW x)) (proj₁ lW , lxμ lW x)))
        l
        (λ x h lh → lgW (proj₁ W , xμ lW x) ≤rf (proj₁ lW , lxμ lW x) (≤tr i (≤μ lW x)) h (u (≤tr p (≤μ lW x)) (proj₁ lW , lxμ lW x)) lh)
    lgW W p lW i b (nw q x) l = lgW W (≤tr q p) lW i b x l
    lgpW W p lW i b d l zero = l
    lgpW W p lW i b d l (suc k) = lgW W p lW i (rdpW W p lW i b d k) (d k) (lgpW W p lW i b d l k)
```

## §3 包: 对一切层号一条

```agda
  NdT : (c : Ht) → Set₁
  NdT c = ∀ {T} → Emb (Lv c) T → ∀ {W₀ k} → StH W₀ k (LyH c) → (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ≤ W →
          HB T → (D k W → HB T → HB T) → HB T

  TrT : (c : Ht) → Set
  TrT c = (κ : K (Lv c)) → ∀ {L″} → (∀ {W} → a ≤ W → LyH c ⊲[ W ] L″) →
          (E (Lv c) κ → (W : Wd₂) → a ≤ W → D L″ W) → (W : Wd₂) → a ≤ W → D L″ W

  record Pkg (c : Ht) : Set₁ where
    field
      trK : TrT c
      ndS : NdT c
      fsS : ∀ {T} (o : Emb (Lv c) T) {W₀ k} (r : StH W₀ k (LyH c)) W q lW i b s {w} → b ⊲[ w ] ndS o r W q lW i b s
      lgS : ∀ {T} (o : Emb (Lv c) T) {W₀ k} (r : StH W₀ k (LyH c)) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS o r W q lW i b s)
  open Pkg public

  module _ {c : Ht} (P : Pkg c) where
    trN : HB (Lv c) → (W : Wd₂) → a ≤ W → D (LyH c) W
    trN hz W i = n0
    trN (hs x) W i = trN x W i ⨾ n1
    trN (hl f) W i = nl (λ k → trN (f k) W i)
    trN (hΩ κ h) W i = trK P κ (λ _ → hself) (λ e W′ i′ → trN (h e) W′ i′) W i

    ndi : NdW (Lv c) (LyH c)
    ndi = record { ndR = ndS P (idE (Lv c)) ; fsR = fsS P (idE (Lv c)) ; lgR = lgS P (idE (Lv c)) ; eAR = eA c ; eMR = eM c }

    rdc : ∀ {W₀} (W : Wd₂) → W₀ ≤ W → LgW₂ W → a ≤ W → HB (Lv c) → D (LyH c) W₀ → HB (Lv c)
    rdc = RW.rdW ndi

    fstc : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (x : D (LyH c) W₀) {w} → b ⊲[ w ] rdc W p lW i b x
    fstc = RW.fstW ndi

    lgc : ∀ {W₀} (W : Wd₂) (p : W₀ ≤ W) (lW : LgW₂ W) i b (x : D (LyH c) W₀) → LgB b → LgB (rdc W p lW i b x)
    lgc = RW.lgW ndi

  ndQ : ∀ {c} → Pkg c → ∀ {T} → Emb (step (Lv c)) T → ∀ {W₀ k} → k ⊲[ W₀ ] LyH c → (W : Wd₂) → W₀ ≤ W →
        LgW₂ W → a ≤ W → HB T → (D k W → HB T → HB T) → HB T
  ndQ {c = hz} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hz} P o (hsuc Q) W q lW i b s = ndS P (compE (inj₁E S₀) o) (ss Q) W q lW i b s
  ndQ {c = hs c} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hs c} P o (hsuc Q) W q lW i b s = ndS P (compE (inj₁E (Lv (hs c))) o) (ss Q) W q lW i b s
  ndQ {c = hl f} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hl f} P o (hlim n Q) W q lW i b s = ndS P (compE (inj₁E (Lv (hl f))) o) (sl n Q) W q lW i b s
  ndQ {c = hΩ κ g} P o hself W q lW i b s = nodeH o b (λ x h → s (trN P x W i) h)
  ndQ {c = hΩ κ g} P o (hLim e Q) W q lW i b s = ndS P (compE (inj₁E (Lv (hΩ κ g))) o) (sL e Q) W q lW i b s

  fsQ : ∀ {c} (P : Pkg c) {T} (o : Emb (step (Lv c)) T) {W₀ k} (Q : k ⊲[ W₀ ] LyH c) W q lW i b s {w} →
        b ⊲[ w ] ndQ P o Q W q lW i b s
  fsQ {c = hz} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hz} P o (hsuc Q) W q lW i b s = fsS P (compE (inj₁E S₀) o) (ss Q) W q lW i b s
  fsQ {c = hs c} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hs c} P o (hsuc Q) W q lW i b s = fsS P (compE (inj₁E (Lv (hs c))) o) (ss Q) W q lW i b s
  fsQ {c = hl f} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hl f} P o (hlim n Q) W q lW i b s = fsS P (compE (inj₁E (Lv (hl f))) o) (sl n Q) W q lW i b s
  fsQ {c = hΩ κ g} P o hself W q lW i b s = fst-nodeH o b _
  fsQ {c = hΩ κ g} P o (hLim e Q) W q lW i b s = fsS P (compE (inj₁E (Lv (hΩ κ g))) o) (sL e Q) W q lW i b s

  lgQ : ∀ {c} (P : Pkg c) {T} (o : Emb (step (Lv c)) T) {W₀ k} (Q : k ⊲[ W₀ ] LyH c) W q lW i {b s} →
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
  newN : ∀ {c} → Pkg c → ∀ {L″ W} (R : StH W (LyH c) L″) → (HB (Lv c) → (W′ : Wd₂) → a ≤ W′ → D L″ W′) →
         a ≤ W → D L″ W
  newN P R g i = ni R (λ {W′} p lW′ y → g (rdc P W′ ≤rf lW′ (≤tr i p) hz (outS R y)) W′ (≤tr i p))

  -- hz
  trK-z : TrT hz
  trK-z κ Pv g W i = nκ (nz⊲ (Pv {W} i) tt) (λ {x} p lx → g x (x , proj₂ W) (⊲-tr (proj₁ i) p , ⊲ᴮ↑ {S₀} p (proj₂ i)))

  ndS-z : NdT hz
  ndS-z o (ss hself) W q lW i b s = nodeA o b (λ x h → s (toD x) h)

  fsS-z : ∀ {T} (o : Emb S₀ T) {W₀ k} (r : StH W₀ k (LyH hz)) W q lW i b s {w} → b ⊲[ w ] ndS-z o r W q lW i b s
  fsS-z o (ss hself) W q lW i b s = fst-nodeA o b _

  lgS-z : ∀ {T} (o : Emb S₀ T) {W₀ k} (r : StH W₀ k (LyH hz)) W q lW i {b s} →
          (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-z o r W q lW i b s)
  lgS-z o (ss hself) W q lW i fs lb ls = Lg-nodeA o (λ x h → fs _ h) lb (λ x h → ls _ h)

  -- hs c
  module PS {c : Ht} (P : Pkg c) where
    trK-s : TrT (hs c)
    trK-s (inj₂ tt) Pv g W i = newN P (SkH (ss hself) (Pv {W} i)) g i
    trK-s (inj₁ κ) Pv g W i = trK P κ (λ i′ → ⊲ᴮ-tr (hsuc hself) (Pv i′)) g W i

    ndS-s : NdT (hs c)
    ndS-s o (ss Q) = ndQ P o Q

    fsS-s : ∀ {T} (o : Emb (Lv (hs c)) T) {W₀ k} (r : StH W₀ k (LyH (hs c))) W q lW i b s {w} → b ⊲[ w ] ndS-s o r W q lW i b s
    fsS-s o (ss Q) = fsQ P o Q

    lgS-s : ∀ {T} (o : Emb (Lv (hs c)) T) {W₀ k} (r : StH W₀ k (LyH (hs c))) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-s o r W q lW i b s)
    lgS-s o (ss Q) = lgQ P o Q

  -- hl f
  module PL {f : ℕ → Ht} (P : ∀ n → Pkg (f n)) where
    ιL : ∀ n → Emb (step (Lv (f n))) (Lv (hl f))
    ιL n = ιE {F = λ n → step (Lv (f n))} n

    trK-l : TrT (hl f)
    trK-l (n , inj₂ tt) Pv g W i = newN (P n) (SkH (sl n hself) (Pv {W} i)) g i
    trK-l (n , inj₁ κ) Pv g W i = trK (P n) κ (λ i′ → ⊲ᴮ-tr (hlim n hself) (Pv i′)) g W i

    ndS-l : NdT (hl f)
    ndS-l o (sl n Q) = ndQ (P n) (compE (ιL n) o) Q

    fsS-l : ∀ {T} (o : Emb (Lv (hl f)) T) {W₀ k} (r : StH W₀ k (LyH (hl f))) W q lW i b s {w} → b ⊲[ w ] ndS-l o r W q lW i b s
    fsS-l o (sl n Q) = fsQ (P n) (compE (ιL n) o) Q

    lgS-l : ∀ {T} (o : Emb (Lv (hl f)) T) {W₀ k} (r : StH W₀ k (LyH (hl f))) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-l o r W q lW i b s)
    lgS-l o (sl n Q) = lgQ (P n) (compE (ιL n) o) Q

  -- hΩ κ g, 对一切种类 κ (κA, κH 同一条): 过第 x 支的结点, 在公共上界 W 之下判定 Bd S₁ κ x a
  module PΩ {κ : K S₁} {g : E S₁ κ → Ht} (P : ∀ x → Pkg (g x)) where
    ιΩ : (p : Σ (E S₁ κ) (λ x → Bd S₁ κ x a)) → Emb (step (Lv (g (proj₁ p)))) (Lv (hΩ κ g))
    ιΩ p = ιE {F = λ p → step (Lv (g (proj₁ p)))} p

    trK-Ω : TrT (hΩ κ g)
    trK-Ω ((x , e) , inj₂ tt) Pv g′ W i =
      newN (P x) (SkH (sL {κ = κ} {c = x} (Bd↑ S₁ {κ = κ} i e) hself) (Pv {W} i)) g′ i
    trK-Ω ((x , e) , inj₁ κ′) Pv g′ W i =
      trK (P x) κ′ (λ i′ → ⊲ᴮ-tr (hLim {κ = κ} {c = x} (Bd↑ S₁ {κ = κ} i′ e) hself) (Pv i′)) g′ W i

    ndΩd : ∀ {T} → Emb (Lv (hΩ κ g)) T → ∀ {W₀ k} (x : E S₁ κ) → k ⊲[ W₀ ] LyH (g x) → (W : Wd₂) → W₀ ≤ W →
           LgW₂ W → a ≤ W → HB T → (D k W → HB T → HB T) → Dec (Bd S₁ κ x a) → HB T
    ndΩd o x Q W q lW i b s (yes e′) = ndQ (P x) (compE (ιΩ (x , e′)) o) Q W q lW i b s
    ndΩd o x Q W q lW i b s (no _) = b

    ndS-Ω : NdT (hΩ κ g)
    ndS-Ω o (sL {c = x} e Q) W q lW i b s = ndΩd o x Q W q lW i b s (bdecS₁ (Bd↑ S₁ {κ = κ} q e) i lW)

    fsΩd : ∀ {T} (o : Emb (Lv (hΩ κ g)) T) {W₀ k} (x : E S₁ κ) (Q : k ⊲[ W₀ ] LyH (g x)) W q lW i b s d {w} →
           b ⊲[ w ] ndΩd o x Q W q lW i b s d
    fsΩd o x Q W q lW i b s (yes e′) = fsQ (P x) (compE (ιΩ (x , e′)) o) Q W q lW i b s
    fsΩd o x Q W q lW i b s (no _) = hself

    lgΩd : ∀ {T} (o : Emb (Lv (hΩ κ g)) T) {W₀ k} (x : E S₁ κ) (Q : k ⊲[ W₀ ] LyH (g x)) W q lW i {b s} d →
           (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndΩd o x Q W q lW i b s d)
    lgΩd o x Q W q lW i (yes e′) fs lb ls = lgQ (P x) (compE (ιΩ (x , e′)) o) Q W q lW i fs lb ls
    lgΩd o x Q W q lW i (no _) fs lb ls = lb

    fsS-Ω : ∀ {T} (o : Emb (Lv (hΩ κ g)) T) {W₀ k} (r : StH W₀ k (LyH (hΩ κ g))) W q lW i b s {w} →
            b ⊲[ w ] ndS-Ω o r W q lW i b s
    fsS-Ω o (sL {c = x} e Q) W q lW i b s = fsΩd o x Q W q lW i b s (bdecS₁ (Bd↑ S₁ {κ = κ} q e) i lW)

    lgS-Ω : ∀ {T} (o : Emb (Lv (hΩ κ g)) T) {W₀ k} (r : StH W₀ k (LyH (hΩ κ g))) W q lW i {b s} →
            (∀ y h {w} → h ⊲[ w ] s y h) → LgB b → (∀ y h → LgB h → LgB (s y h)) → LgB (ndS-Ω o r W q lW i b s)
    lgS-Ω o (sL {c = x} e Q) W q lW i = lgΩd o x Q W q lW i (bdecS₁ (Bd↑ S₁ {κ = κ} q e) i lW)

  pk : ∀ c → Pkg c
  pk hz = record { trK = trK-z ; ndS = ndS-z ; fsS = fsS-z ; lgS = lgS-z }
  pk (hs c) = record { trK = PS.trK-s (pk c) ; ndS = PS.ndS-s (pk c) ; fsS = PS.fsS-s (pk c) ; lgS = PS.lgS-s (pk c) }
  pk (hl f) = record { trK = PL.trK-l P ; ndS = PL.ndS-l P ; fsS = PL.fsS-l P ; lgS = PL.lgS-l P }
    where P = λ n → pk (f n)
  pk (hΩ κ g) = record { trK = PΩ.trK-Ω P ; ndS = PΩ.ndS-Ω P ; fsS = PΩ.fsS-Ω P ; lgS = PΩ.lgS-Ω P }
    where P = λ x → pk (g x)
```

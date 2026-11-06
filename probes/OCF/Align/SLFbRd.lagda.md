# 带证据的回灌 (二): 第 1 层的数据读进某一层的值

> 不含记号. 入口 [SLFb](SLFb.lagda.md), 接口 [SLFbIf](SLFbIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> [GenFoldRd](GenFoldRd.lagda.md) 的 `rd₁` 把第 1 层的数据读成 `HB T`, 过第 0 层的结点读成底种类 `aK G` 的 $\Omega$-结点. 这里把目标换成任一种类结构 $Q$ 的高度 `HB Q`, 结点的种类换成 $Q$ 里一个可读成 `A` 的种类 `κa ak` (接口 `AK`); 其余逐行照 `rd₁` (闭包结点有损地读当前世界的分支). 合法由形状给出 (`Lg-rdQ`, 用 `fr-mono`, `fr-lg`). 构造文件取 $Q$ = 第 $n$ 站的层 `Lv (kₙ n)`, 作头种类的级读回 (级层 $1$).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.HtTowerTy using (KS)
open import OCF.Align.GenFoldIf using (GenK; LgDn)
open import OCF.Align.SLFbIf using (AK)
module OCF.Align.SLFbRd (T : KS) (G : GenK T) (Ld : LgDn T) {Q : KS} (ak : AK Q) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.HtTowerTy hiding (KS)
open import OCF.Align.GenFoldIf hiding (GenK; LgDn)
open import OCF.Align.GenFoldTree
open Tree T
open import OCF.Align.GenFoldRd T G Ld using (module NbA; lgW≤)
open NbA
open import OCF.Align.SLFbIf hiding (AK)
```

```agda
rdQ  : ∀ {W} → LgW L₀ W → HB Q → D (hs hz) W → HB Q
rdpQ : ∀ {W} → LgW L₀ W → HB Q → (ℕ → D (hs hz) W) → ℕ → HB Q
rdQ lW b n0 = b
rdQ lW b n1 = hs b
rdQ lW b (x ⨾ y) = rdQ lW (rdQ lW b x) y
rdQ lW b (nl d) = hl (rdpQ lW b d)
rdQ lW b (ni (ss hself) u) = hΩ (κa ak) (λ e → nbA b (λ c h → rdQ lW h (u ≤rf lW (toD₀ c))) (fr ak e))
rdQ lW b (nc (inj₁ κ) z u) = rdQ lW b (u ≤rf lW)
rdQ lW b (nc (inj₂ _) () u)
rdQ lW b (nw p x) = rdQ (lgW≤ p lW) b x
rdpQ lW b d zero = b
rdpQ lW b d (suc n) = rdQ lW (rdpQ lW b d n) (d n)

rdQ-fst : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) {w} → b ⊲[ w ] rdQ lW b x
rdQ-fst lW b n0 = hself
rdQ-fst lW b n1 = hsuc hself
rdQ-fst lW b (x ⨾ y) = ⊲ᴮ-tr (rdQ-fst lW b x) (rdQ-fst lW (rdQ lW b x) y)
rdQ-fst lW b (nl d) = hlim 0 hself
rdQ-fst lW b (ni (ss hself) u) {w} =
  hLim {Q} {κ = κa ak} {c = bot Q (κa ak)} (botBd Q (κa ak) w)
    (nbA-fst (λ c h → rdQ-fst lW h (u ≤rf lW (toD₀ c))) (fr ak (bot Q (κa ak))))
rdQ-fst lW b (nc (inj₁ κ) z u) = rdQ-fst lW b (u ≤rf lW)
rdQ-fst lW b (nc (inj₂ _) () u)
rdQ-fst lW b (nw p x) = rdQ-fst (lgW≤ p lW) b x

Lg-rdQ  : ∀ {W} (lW : LgW L₀ W) b (x : D (hs hz) W) → LgB b → LgB (rdQ lW b x)
Lg-rdpQ : ∀ {W} (lW : LgW L₀ W) b (d : ℕ → D (hs hz) W) → LgB b → ∀ n → LgB (rdpQ lW b d n)
Lg-rdQ lW b n0 l = l
Lg-rdQ lW b n1 l = l
Lg-rdQ lW b (x ⨾ y) l = Lg-rdQ lW (rdQ lW b x) y (Lg-rdQ lW b x l)
Lg-rdQ lW b (nl d) l = (λ n → rdQ-fst lW (rdpQ lW b d n) (d n)) , Lg-rdpQ lW b d l
Lg-rdQ lW b (ni (ss hself) u) l =
  (λ lw e e′ p → nbA-mono fs (fr-mono ak lw e e′ p)) ,
  (λ e le → Lg-nbA fs l (λ c h lh → Lg-rdQ lW h (u ≤rf lW (toD₀ c)) lh) (fr ak e) (fr-lg ak le))
  where
  fs : ∀ c h {w} → h ⊲[ w ] rdQ lW h (u ≤rf lW (toD₀ c))
  fs c h = rdQ-fst lW h (u ≤rf lW (toD₀ c))
Lg-rdQ lW b (nc (inj₁ κ) z u) l = Lg-rdQ lW b (u ≤rf lW) l
Lg-rdQ lW b (nc (inj₂ _) () u) l
Lg-rdQ lW b (nw p x) l = Lg-rdQ (lgW≤ p lW) b x l
Lg-rdpQ lW b d l zero = l
Lg-rdpQ lW b d l (suc n) = Lg-rdQ lW (rdpQ lW b d n) (d n) (Lg-rdpQ lW b d l n)
```

**读回只含一种 $\Omega$-结点 (盲点, 定理).** `rdQ` 的输出 (起点只含这种结点时) 的一切 $\Omega$-结点的种类都是 `κa ak`: 级层 $1$ 的读回看不见 $Q$ 里别的种类 (同 `NewTwrObs.onlyA-rd₁` 对 `rd₁`). 这是本路读法的上界依据 (判断见入口).

```agda
data OnlyA : HB Q → Set where
  oz : OnlyA hz
  os : ∀ {h} → OnlyA h → OnlyA (hs h)
  ol : ∀ {f} → (∀ n → OnlyA (f n)) → OnlyA (hl f)
  oΩ : ∀ {g} → (∀ e → OnlyA (g e)) → OnlyA (hΩ (κa ak) g)

open import OCF.Align.CumReadCF using (A; azero; asuc; alim)

onlyA-nbA : ∀ {b} {s : A → HB Q → HB Q} → OnlyA b → (∀ c {h} → OnlyA h → OnlyA (s c h)) → ∀ c → OnlyA (nbA b s c)
onlyA-nbA ob os′ azero = ob
onlyA-nbA ob os′ (asuc c) = os′ c (onlyA-nbA ob os′ c)
onlyA-nbA ob os′ (alim f) = ol (λ n → onlyA-nbA ob os′ (f n))

onlyA-rdQ  : ∀ {W} (lW : LgW L₀ W) {b} (x : D (hs hz) W) → OnlyA b → OnlyA (rdQ lW b x)
onlyA-rdpQ : ∀ {W} (lW : LgW L₀ W) {b} (d : ℕ → D (hs hz) W) → OnlyA b → ∀ n → OnlyA (rdpQ lW b d n)
onlyA-rdQ lW n0 o = o
onlyA-rdQ lW n1 o = os o
onlyA-rdQ lW (x ⨾ y) o = onlyA-rdQ lW y (onlyA-rdQ lW x o)
onlyA-rdQ lW (nl d) o = ol (onlyA-rdpQ lW d o)
onlyA-rdQ lW (ni (ss hself) u) o = oΩ (λ e → onlyA-nbA o (λ c oh → onlyA-rdQ lW (u ≤rf lW (toD₀ c)) oh) (fr ak e))
onlyA-rdQ lW (nc (inj₁ κ) z u) o = onlyA-rdQ lW (u ≤rf lW) o
onlyA-rdQ lW (nc (inj₂ _) () u) o
onlyA-rdQ lW (nw p x) o = onlyA-rdQ (lgW≤ p lW) x o
onlyA-rdpQ lW d o zero = o
onlyA-rdpQ lW d o (suc n) = onlyA-rdQ lW (d n) (onlyA-rdpQ lW d o n)
```

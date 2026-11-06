# 事件历史世界 (三): 一级回灌的格链, 与 `no-chain` 对照

> 不含记号. 入口 [EvW](EvW.lagda.md). `HtTowerFFold.RunM` 的回灌在一个槽上一格一格升界: $x_0$ 是当前界, $x_{n+1}=x_n\boxplus\Delta_n$, $\Delta_n$ 由第 $n$ 格读出; 每一格要在它的世界里有界, 极限是格的 ℕ-极限. 这一篇在事件历史世界 (`EvWBase.EvKS`) 上写出这条格链 (读回 $\mathrm{rd}$ 是参数, 不写折叠本身), 并在 `κ₂` 的坐标类型上与 `ChainZNeg.no-Ω-cell` 对照.
>
> - **`Feed`** (对一切 `S`, 一切合法外层世界, 一切坐标 $c_0$ 与证据 $p_0$, 一切合法的读回): 世界链 `Hn` (每一步在 $(c_0,p_0)$ 处加一个事件, 增量是读回作用在当前格上), 格 `cell n` = 重放的界. 定理: 每一格在自己的世界里有界 (`cell-bd`), 在之后一切世界里有界 (`cell-later`); 格链单调 (`cell-step`); 新格是旧格 ⊞ 读回 (沿自环, `cell-faith`); 格链的 ℕ-极限合法 (`Lg-lim`); **严格低于 $c_0$ 的一切坐标的一切证据拷贝, 界在整条链上不变** (`low-fixed`, 回灌 "低层搬回" 的对应物).
> - **后继坐标的新种类节点** (`S = S₀`, 坐标 $c_0=\mathrm{hs}\,y$, 读回取 `Ωtop (Lev y)`): 每一格含新种类的 $\Omega$-节点且有界 (`new-cell`), 对一切 $y$, 一切证据.
> - **`contrast`** (`κ₂` 处): `L′ 1` 的 `κ₂` 与这里坐标 $\mathrm{hs\,hz}$ 的槽是同一个类型 `HB (step S₀)` (`same-type`, `refl`). 在由 `dW 1` 经 `growL′` 生成的世界里, 当前界 ⊞ `Ωtop S₀` 不有界 (`ChainZNeg.no-Ω-cell`); 在事件世界里, 当前界 ⊞ `Ωtop S₀` 在加一个事件后的世界里有界 (证据是 `hself` 时定义相等).
>
> **范围.** 外层世界 $(w,b)$ 在整条链上固定 (事件世界只长事件); 内层世界取固定的合法族 (`dWLev`, `CohWNeg.lgdW`). 这里没有折叠, 没有读回的定义, 没有值定理; 对照是两个不同种类结构上的两条定理, 不是同一个世界的比较.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EvWFeed where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerNStage using (L′; dWLev)
open import OCF.Align.CohWNeg using (lgdW)
open import OCF.Align.StallDxBdec using (_<ᴮ_)
open import OCF.Align.DiagK3One using (NoNew; κ₂)
open import OCF.Align.ChainZNeg using (Reach; bnd₂; no-Ω-cell; noNew-⊞r)
open import OCF.Align.EvWBase
```

## §1 格链

```agda
module Feed {S : KS} (w : Wd S) (b : HB S) (lw : LgW S w) (lb : LgB b)
            (v₀ : (c : HB S) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c))
            (c₀ : HB S) (p₀ : c₀ ⊲[ w ] b)
            (rd : ℕ → HB (Lev c₀) → HB (Lev c₀)) (lrd : ∀ n x → LgB x → LgB (rd n x))
            (H₀ : Rp.Hist {S} w b lw lb) where
  open EvKS w b lw lb v₀ lv₀ public

  κ : Kᵉ
  κ = c₀ , p₀

  Hn  : ℕ → Hist
  evn : ℕ → Ev
  Hn zero = H₀
  Hn (suc n) = evn n ∷ Hn n
  evn n = ev c₀ p₀ (rd n (rp (Hn n) c₀ p₀)) (lrd n (rp (Hn n) c₀ p₀) (Lg-rp (Hn n) c₀ p₀))

  cell : ℕ → X c₀
  cell n = rp (Hn n) c₀ p₀

  cell-bd : ∀ n → Bdᵉ κ (cell n) (Hn n)
  cell-bd n = hself

  cell-step : ∀ n {v} → cell n ⊲[ v ] cell (suc n)
  cell-step n = rp-mono (evn n) (Hn n) c₀ p₀

  cell-faith : ∀ n → Σ (c₀ ≡ c₀) (λ e → cell (suc n) ≡ cell n ⊞ subst X e (rd n (cell n)))
  cell-faith n = new-gen c₀ p₀ (eδ (evn n)) (elδ (evn n)) (Hn n)

  suf-k : ∀ n k → Suf (Hn n) (Hn (k + n))
  suf-k n zero = here
  suf-k n (suc k) = there (evn (k + n)) (suf-k n k)

  cell-later : ∀ n k → Bdᵉ κ (cell n) (Hn (k + n))
  cell-later n k = Bd↑ᵉ {κ} (suf-k n k) (cell-bd n)

  lim : HB (Lev c₀)
  lim = hl cell

  Lg-lim : LgB lim
  Lg-lim = (λ n → cell-step n) , (λ n → Lg-rp (Hn n) c₀ p₀)

  -- 严格低于 c₀ 的坐标 (每一份证据拷贝): 界在整条链上不变
  low-fixed : ∀ c (p : c ⊲[ w ] b) → c <ᴮ c₀ → ∀ n → rp (Hn n) c p ≡ rp H₀ c p
  low-fixed c p l zero = refl
  low-fixed c p l (suc n) = trans (rp-below (evn n) (Hn n) c p l) (low-fixed c p l n)
```

## §2 后继坐标: 格含新种类节点

`NewF x t`: 坐标 $x$ 是后继 $\mathrm{hs}\,y$ 时, 槽 `HB (Lev (hs y)) = HB (step (Lev y))` 里的 $t$ 含新种类 (`inj₂`) 的 $\Omega$-节点. 它沿坐标的相等搬运 (对 `refl` 匹配, 端点是变量, 不用 K), 所以 `cell-faith` 的自环不碍事.

```agda
NewF : (x : HB S₀) → HB (Lev x) → Set
NewF hz t = ⊤
NewF (hs y) t = ¬ NoNew {Lev y} t
NewF (hl f) t = ⊤
NewF (hΩ κ g) t = ⊤

newF-subst : ∀ {x x′ : HB S₀} (e : x ≡ x′) t → NewF x t → NewF x′ (subst (λ z → HB (Lev z)) e t)
newF-subst refl t n = n

module NewCell (a : A) (b : HB S₀) (la : Lg a) (lb : LgB b) (y : HB S₀) (p₀ : hs y ⊲[ a ] b)
               (H₀ : Rp.Hist {S₀} a b la lb) where
  open Feed {S₀} a b la lb dWLev lgdW (hs y) p₀ (λ _ _ → Ωtop (Lev y)) (λ _ _ _ → Lg-Ωtop (Lev y)) H₀

  new-cell : ∀ n → ¬ NoNew {Lev y} (cell (suc n)) × Bdᵉ κ (cell (suc n)) (Hn (suc n))
  new-cell n = nn , cell-bd (suc n)
    where
    e  = proj₁ (cell-faith n)
    eq = proj₂ (cell-faith n)
    δ′ = subst X e (Ωtop (Lev y))
    nδ : ¬ NoNew {Lev y} δ′
    nδ = newF-subst e (Ωtop (Lev y)) (λ ())
    nn : ¬ NoNew {Lev y} (cell (suc n))
    nn h = nδ (noNew-⊞r (cell n) δ′ (subst NoNew eq h))
```

## §3 `κ₂` 处的对照

`κ₂` 是 `L′ 1` 里 `Lev (Ωtop S₀)` 在坐标 `hs (hs hz)` 处的新种类, 坐标类型 `HB (step S₀)`. 事件世界里坐标 `hs hz` 的槽是 `HB (Lev (hs hz))`, 同一个类型 (定义相等). 外层界取 $b=\mathrm{hs\,hz}$, 证据 `hself`.

```agda
same-type : E (L′ 1) κ₂ ≡ HB (Lev {S₀} (hs hz))
same-type = refl

module K2 (a : A) (la : Lg a) where
  open EvKS {S₀} a (hs hz) la tt dWLev lgdW public

  κ₂ᵉ : Kᵉ
  κ₂ᵉ = hs hz , hself

  ev₂ : Hist → Hist
  ev₂ H = ev (hs hz) hself (Ωtop S₀) (Lg-Ωtop S₀) ∷ H

  -- 新世界里的界恰好是 当前界 ⊞ Ωtop S₀ (定义相等)
  exact₂ : ∀ H → rp (ev₂ H) (hs hz) hself ≡ rp H (hs hz) hself ⊞ Ωtop S₀
  exact₂ H = refl

  yes-Ω-cell : ∀ H → Bdᵉ κ₂ᵉ (rp H (hs hz) hself ⊞ Ωtop S₀) (ev₂ H)
  yes-Ω-cell H = hself

  contrast : (∀ {w} → Reach w → ¬ Bd (L′ 1) κ₂ (bnd₂ w ⊞ Ωtop S₀) w) ×
             (∀ H → Suf H (ev₂ H) × Bdᵉ κ₂ᵉ (rp H (hs hz) hself ⊞ Ωtop S₀) (ev₂ H))
  contrast = (λ {w} r → no-Ω-cell (bnd₂ w) r) , (λ H → there (ev (hs hz) hself (Ωtop S₀) (Lg-Ωtop S₀)) here , yes-Ω-cell H)
```

**前提可满足.** `a = azero`, `la = tt` 给出 `K2`; `Lg-Ωtop` 给出增量合法; `NewCell` 取 $b=\mathrm{hs}\,y$, $p_0$ = `hself`, $H_0=[]$ 即可 (下面). `Reach (dW 1)` 由 `ChainZNeg.r0`.

```agda
module _ where
  open K2 azero tt
  inst-K2 : Bdᵉ κ₂ᵉ (hz ⊞ Ωtop S₀) (ev₂ [])
  inst-K2 = yes-Ω-cell []

inst-new : ∀ (y : HB S₀) (ly : LgB y) n →
  ¬ NoNew {Lev y} (Feed.cell {S₀} azero (hs y) tt ly dWLev lgdW (hs y) hself
                     (λ _ _ → Ωtop (Lev y)) (λ _ _ _ → Lg-Ωtop (Lev y)) [] (suc n))
inst-new y ly n = proj₁ (NewCell.new-cell azero (hs y) tt ly y hself [] n)
```

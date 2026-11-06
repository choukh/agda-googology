# 种类带证据, 比较取 `cmpB₀` (四): 一级回灌的骨架

> 不含记号. 入口 [AdmEv](AdmEv.lagda.md). 接手清单第 4 条. **这里没有写出 `HtTowerFFold.RunM` 在 `evKS₀` 上的折叠** (那要把 `HtTowerFTree` 的数据树 `D`, `D₊`, `Cut₁` 与 `Walk₁` 搬到事件世界上, 本轮没有做). 写出的是 `RunM` 回灌的两个形状, 读回 `rd` 作参数:
>
> 1. **`Feed₀`** (外层界固定, 在一个种类上逐格加事件; 对照 `EvWFeed.Feed`): 新格**字面地**是旧格 ⊞ 读回 (`cell-faith₀`, 不经自环); 读回头部非零时格链**严格**增长 (`cell-strict`, 严格子项); ℕ-极限合法.
> 2. **`Tower`** (外层界随回灌长高, `RunM` 第 1 层回灌的形状: 读回给出外层高度界的增量): 第 $n$ 站是 (外层界 $b_n$, 它的合法证明, $K_n$ = `evKS₀` 在 $b_n$ 之下, 一个合法高度 $t_n$ : `HB K_n`). 下一站: $b_{n+1}=b_n\boxplus\mathrm{rd}_n$, $t_{n+1}=\mathrm{rl}(t_n)\boxplus\Omega^{\mathrm{new}}_{n+1}$, 其中 `rl` 是 [AdmEvGrow](AdmEvGrow.lagda.md) 的改贴, $\Omega^{\mathrm{new}}_{n+1}$ 是新界自己那个种类 $(b_{n+1},\mathrm{hself})$ 上的 $\Omega$-节点. **每一站的高度合法是构造的一部分** (要 `Lg-rl`; 没有它这个递归写不出来).
>
> **值的陈述 (交付 b), 全是严格增长一档, 不是强度定理** (手册 §3.3): `b-strict`: 读回头部非零时外层界严格增长; `new-kind`: 第 $n+1$ 站的新种类的坐标 $b_{n+1}$ 不在 $b_n$ 之下 (所以不是任何旧种类的像); `cell-strict`. **没有**序数值, 没有 ψ₀(Ω_x) 的界, 连粗界也没有.
>
> **第一个没过的地方 (判断).** 塔的 ℕ-极限: 各站的高度在不同的种类结构 $K_n$ 里, 要合到极限界 $\mathrm{hl}\,b$ 之下的 `evKS₀`, 需要沿 `hlim n hself` (以及 `stepsᴮ` 的复合) 改贴; `AdmEvGrow.fac` 只对 `⊞-⊲ b σ` 形状的长高路径证明, 而 $b_m$ 写成 $b_n\boxplus(\dots)$ 要 ⊞ 的结合律, 在 ℕ-极限处要函数外延 (判断, 未写成定理).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.AdmEvFeed where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)
open import OCF.Align.CumReadCF using (A; azero; Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.StallDxBdec using (_<ᴮ_; <s₀; <s; <l₀; <l; <Ω₀; <Ω; toLt; wf; irr)
open import OCF.Align.AdmWCmp using (<ᴮ-tr)
open import OCF.Align.AdmEvBase
open import OCF.Align.AdmEvGrow using (module Relabel; module Grow₀)
```

## §1 接上头部非零的增量是严格的

```agda
NZ : ∀ {S} → HB S → Set
NZ hz = ⊥
NZ _ = ⊤

module _ {S : KS} where
  private
    lt-hs : ∀ {x y : HB S} → (x ≡ y) ⊎ (x <ᴮ y) → x <ᴮ hs y
    lt-hs (inj₁ refl) = <s₀
    lt-hs (inj₂ l) = <s l

    lt-hl : ∀ {x} {f : ℕ → HB S} n → (x ≡ f n) ⊎ (x <ᴮ f n) → x <ᴮ hl f
    lt-hl n (inj₁ refl) = <l₀ n
    lt-hl n (inj₂ l) = <l n l

    lt-hΩ : ∀ {x κ} {g : E S κ → HB S} c → (x ≡ g c) ⊎ (x <ᴮ g c) → x <ᴮ hΩ κ g
    lt-hΩ c (inj₁ refl) = <Ω₀ c
    lt-hΩ c (inj₂ l) = <Ω c l

  ⊞-strict : ∀ (x δ : HB S) → NZ δ → Wd S → x <ᴮ x ⊞ δ
  ⊞-strict x (hs δ) _ w = lt-hs (toLt (⊞-fst {w = w} x δ))
  ⊞-strict x (hl f) _ w = lt-hl 0 (toLt (⊞-fst {w = w} x (f 0)))
  ⊞-strict x (hΩ κ g) _ w = lt-hΩ (bot S κ) (toLt (⊞-fst {w = w} x (g (bot S κ))))

  not-below : ∀ {x y : HB S} {w} → x <ᴮ y → ¬ (y ⊲[ w ] x)
  not-below {x} {y} l q with toLt q
  ... | inj₁ refl = irr (wf x) l
  ... | inj₂ m = irr (wf x) (<ᴮ-tr l m)
```

## §2 外层界固定的格链

```agda
module Feed₀ (a : A) (b : HB S₀) (la : Lg a) (lb : LgB b)
             (v₀ : (c : HB S₀) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c))
             (c₀ : HB S₀) (p₀ : c₀ ⊲[ a ] b)
             (rd : ℕ → HB (Lev c₀) → HB (Lev c₀)) (lrd : ∀ n x → LgB x → LgB (rd n x))
             (H₀ : Rp₀.Hist a b la lb) where
  open EvKS₀ a b la lb v₀ lv₀ public

  Hn  : ℕ → Hist
  evn : ℕ → Ev
  Hn zero = H₀
  Hn (suc n) = evn n ∷ Hn n
  evn n = ev c₀ p₀ (rd n (rp (Hn n) c₀ p₀)) (lrd n (rp (Hn n) c₀ p₀) (Lg-rp (Hn n) c₀ p₀))

  cell : ℕ → X c₀
  cell n = rp (Hn n) c₀ p₀

  cell-faith₀ : ∀ n → cell (suc n) ≡ cell n ⊞ rd n (cell n)
  cell-faith₀ n = new-gen₀ c₀ p₀ (eδ (evn n)) (elδ (evn n)) (Hn n)

  cell-bd : ∀ n → Bdᵉ (c₀ , p₀) (cell n) (Hn n)
  cell-bd n = hself

  cell-strict : (∀ n x → NZ (rd n x)) → ∀ n → cell n <ᴮ cell (suc n)
  cell-strict nz n = subst (λ t → cell n <ᴮ t) (sym (cell-faith₀ n)) (⊞-strict (cell n) (rd n (cell n)) (nz n (cell n)) (v₀ c₀))

  Lg-lim : LgB {Lev c₀} (hl cell)
  Lg-lim = (λ n → rp-mono (evn n) (Hn n) c₀ p₀) , (λ n → Lg-rp (Hn n) c₀ p₀)
```

## §3 外层界随回灌长高: 塔

```agda
module Tower (a : A) (la : Lg a) (v₀ : (c : HB S₀) → Wd (Lev c)) (lv₀ : ∀ c → LgW (Lev c) (v₀ c)) where
  Kat : (b : HB S₀) → LgB b → KS
  Kat b lb = EvKS₀.evKS₀ a b la lb v₀ lv₀

  record Stage : Set where
    constructor stage
    field
      sb  : HB S₀
      slb : LgB sb
      st  : HB (Kat sb slb)
      slt : LgB {Kat sb slb} st
  open Stage public

  -- 新界自己那个种类上的 Ω-节点 (常值分支)
  Ωnew : (b : HB S₀) (lb : LgB b) → HB (Kat b lb)
  Ωnew b lb = hΩ (b , hself) (λ _ → hz)

  Lg-Ωnew : ∀ b lb → LgB {Kat b lb} (Ωnew b lb)
  Lg-Ωnew b lb = (λ lw e e′ pr → hself) , (λ x lx → tt)

  module Run (rd : ℕ → (s : Stage) → Σ (HB S₀) LgB) (s₀ : Stage) where
    δ  : ℕ → Stage → HB S₀
    δ n s = proj₁ (rd n s)

    next : ℕ → Stage → Stage
    next n s = stage b′ lb′ (R.rl (st s) ⊞ Ωnew b′ lb′)
                     (Lg-⊞ (R.rl (st s)) (Ωnew b′ lb′) (R.Lg-rl (st s) (slt s)) (Lg-Ωnew b′ lb′))
      where
      module R = Relabel a la (sb s) (slb s) (δ n s) (proj₂ (rd n s)) v₀ lv₀
      b′ = sb s ⊞ δ n s
      lb′ = Lg-⊞ (sb s) (δ n s) (slb s) (proj₂ (rd n s))

    tower : ℕ → Stage
    tower zero = s₀
    tower (suc n) = next n (tower n)

    -- 每一站的高度合法 (构造的一部分)
    legal : ∀ n → LgB {Kat (sb (tower n)) (slb (tower n))} (st (tower n))
    legal n = slt (tower n)

    b-step : ∀ n {w} → sb (tower n) ⊲[ w ] sb (tower (suc n))
    b-step n = ⊞-fst (sb (tower n)) (δ n (tower n))

    b-strict : (∀ n s → NZ (δ n s)) → ∀ n → sb (tower n) <ᴮ sb (tower (suc n))
    b-strict nz n = ⊞-strict (sb (tower n)) (δ n (tower n)) (nz n (tower n)) a

    -- 第 n+1 站的新种类: 坐标 b_{n+1} 不在 b_n 之下, 所以不是任何旧种类 (c, wk p) 的像
    new-kind : (∀ n s → NZ (δ n s)) → ∀ n → ¬ (sb (tower (suc n)) ⊲[ a ] sb (tower n))
    new-kind nz n = not-below (b-strict nz n)
```

## §4 闭项实例

外层世界 $a=0$, 内层世界取全 $0$ 的族 (`AdmWCoh.wz`), 起点 $b_0=0$, $t_0=0$, 读回恒为 $\mathrm{hs}\,0$. 这是一个闭的 `Stage` 序列: 每一站合法, 外层界严格增长, 每一站有一个新种类.

```agda
open import OCF.Align.AdmWCoh using (wz; lg-wz)

module Inst where
  open Tower azero tt wz lg-wz

  s₀ : Stage
  s₀ = stage hz tt hz tt

  rd₁ : ℕ → Stage → Σ (HB S₀) LgB
  rd₁ _ _ = hs hz , tt

  open Run rd₁ s₀

  T₃ : Stage
  T₃ = tower 3

  inst-strict : ∀ n → sb (tower n) <ᴮ sb (tower (suc n))
  inst-strict = b-strict (λ _ _ → tt)

  inst-new : ∀ n → ¬ (sb (tower (suc n)) ⊲[ azero ] sb (tower n))
  inst-new = new-kind (λ _ _ → tt)
```

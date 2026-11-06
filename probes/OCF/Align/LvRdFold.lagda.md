# 读回包 (四): 一条折叠对一切码, 有限级, 第 ω 级的下降, 第 ω+1 级折叠, 闭项

> 不含记号. 入口 [LvRd](LvRd.lagda.md), 接口 [LvRdIf](LvRdIf.lagda.md) §3, §5, §6. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延; 本篇没有模块参数作前提, 闭项无参数.
>
> - **§1 一条折叠对一切码** `GF k₀ L trO inc`: 层 `HB (step (Pc k₀))` ↦ 第 $L$ 层的树. 旧种类交给 `trO`, 新种类回灌: 世界链在码 $k_0$ 上 `raise`, 增量 `inc` 是输出的函数, 分支读当前世界在 $k_0$ 的槽. 与 `LvFbFold.FKc` 同形, 但不写死级数: 有限级与第 $\omega+1$ 级是同一个模块的两个实例.
> - **§2 两种种类折叠在层 $L_x$ 上的输出** `OG.outX` (`FamFoldAll.OL` 对一般的层).
> - **§3 有限级**: `FF n d` (码 `kfin (n+1)`, 层 `ly (n+2)`, 旧种类 `trKg (pkgF n)`), 下降 `dnF`, 级顶 `Hn`, 对角 `ΛF`.
> - **§4 第 ω 级的下降** `dω : Dn Gω`: 混合高度先经 `trω` 读成第 $\omega$ 层的树, 再用两种种类折叠的求值 `Run` (层 $\Lambda=\omega$, 它对过任何有限层的结点都有定义) 求到第 2 层, 经第 1 级的读回落到 `Ht`. 不逐结点下降.
> - **§5 第 ω+1 级折叠** `FΩ = GF kω lyω trOω incΩ`: 旧种类 $(m,\kappa)$ 交给第 $m$ 级的翻译, 过第 $m$ 层 (在第 $\omega$ 层的第 $m$ 支之下); 新种类在码 `kω` 上回灌, 增量 = 输出经 `RdΩ` 读回, `dω` 下降, 两种种类折叠 $\Omega_{\omega\boxplus h}$ 在第 $\omega$ 层上的输出经 `RdΩ` 读回 (与有限级同法).
> - **§6 ω 层的槽被回灌升高, 被读**: 链 `V` 的第 $n+1$ 步把第 $n+1$ 级级顶折叠输出的读回 `rt n` 经 `ι (n+1)` 接到 `kω` 的槽上; 极限世界 `V∞` 在 `kω` 的槽是链上各槽的 ℕ-极限. 第 $\omega+1$ 级折叠从 `V∞` 起.
> - **§7 闭项** `T∞ω1 = T⁺ (ΛF ⊞ Hω1)`, `Hω1` 是第 $\omega+1$ 级的级顶 `Ωtop Gω` 经第 $\omega+1$ 级折叠 (在 `V∞`) 与 `dω` 降到 `Ht`; `fghω1`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvRdFold where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; Lg; z⊲)
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerCont using (Ωtop; Lg-Ωtop)
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; D; ss; sl; n0; n1; _⨾_; nl; ≤rf; accᴸ)
open import OCF.Align.HtTowerFClosed using (module At; T⁺; Lg-T⁺; ord; W₁; one)
open import OCF.Align.FamFoldIf using (Sk)
open import OCF.Align.FamFoldLift using (≤r; ≤s)
open import OCF.Align.FamFoldRead using (ly)
open import OCF.Align.LvRdIf using (Gω; Gω1; lyω; Dn; Cd; Pc; kω; kfin; Wld; LgV)
open import OCF.Align.LvRdPkg using (rdr; lgr; pkgF; trKg; RdF; RdΩ; trω; trOm)
open import OCF.Align.LvRdWorld using (raise; mono; legal; v₀; lv₀)
```

## §1 一条折叠对一切码

```agda
module GF (k₀ : Cd) (L : Ht)
  (trO : (κ : K (Pc k₀)) → (E (Pc k₀) κ → (W : Wd₂) → D L W) → (W : Wd₂) → D L W)
  (inc : ((W : Wd₂) → D L W) → HB (Pc k₀)) where

  Out : Set
  Out = (W : Wd₂) → D L W

  ch : (Wld → Out) → Wld → ℕ → Wld
  ch Fo v zero = v
  ch Fo v (suc k) = raise (ch Fo v k) k₀ (inc (Fo (ch Fo v k)))

  fold : Wld → HB (step (Pc k₀)) → Out
  fold v hz W = n0
  fold v (hs x) W = fold v x W ⨾ n1
  fold v (hl f) W = nl (λ k → fold v (f k) W)
  fold v (hΩ (inj₁ κ) g) W = trO κ (λ c W′ → fold v (g c) W′) W
  fold v (hΩ (inj₂ tt) g) W =
    nl (λ k → fold (ch (λ u → fold u (g (u k₀))) v k) (g (ch (λ u → fold u (g (u k₀))) v k k₀)) W)

  chain : Wld → (HB (Pc k₀) → HB (step (Pc k₀))) → ℕ → Wld
  chain v g = ch (λ u → fold u (g (u k₀))) v

  fold-Ω : ∀ v g W → fold v (hΩ (inj₂ tt) g) W ≡ nl (λ k → fold (chain v g k) (g (chain v g k k₀)) W)
  fold-Ω v g W = refl

  ch-s : ∀ v g k → chain v g (suc k) ≡ raise (chain v g k) k₀ (inc (fold (chain v g k) (g (chain v g k k₀))))
  ch-s v g k = refl

  ch-lg : (∀ o → LgB (inc o)) → ∀ v g → LgV v → ∀ k → LgV (chain v g k)
  ch-lg li v g lv zero = lv
  ch-lg li v g lv (suc k) = legal (chain v g k) k₀ _ (li _) (ch-lg li v g lv k)

  ch-≤ : ∀ v g k k′ {w} → chain v g k k′ ⊲[ w ] chain v g (suc k) k′
  ch-≤ v g k k′ = mono (chain v g k) k₀ _ k′
```

## §2 两种种类折叠在层 $L_x$ 上的输出

```agda
module OG (Lx : Ht) (lx : LgB Lx) (o1 : ∀ {w} → hs hz ⊲[ w ] Lx) (h : Ht) (lh : LgB h) where
  open At (Lx ⊞ h) (Lg-⊞ Lx h lx lh) (⊲ᴮ-tr o1 (⊞-fst Lx h))
  outX : D Lx W₁
  outX = yc ΔΩ (tg ≤rf (⊞-fst Lx h) (tt , tt))

lgly : ∀ n → LgB {Sk 1} (ly n)
lgly zero = tt
lgly (suc n) = lgly n

one⊲ly : ∀ n {w} → hs hz ⊲[ w ] ly (suc n)
one⊲ly zero = hself
one⊲ly (suc n) = hsuc (one⊲ly n)

-- 第 L 级: 底 1 读回 Ω_{(L+1) ⊞ h} 在第 L+1 层上的输出
δF : ∀ L (h : Ht) → LgB h → HB (Sk L)
δF L h lh = rdr (RdF L) (tt , tt) (hs hz) (OG.outX (ly (suc L)) (lgly (suc L)) (one⊲ly L) h lh)

lδF : ∀ L h lh → LgB (δF L h lh)
lδF L h lh = lgr (RdF L) (tt , tt) (hs hz) _ tt
```

## §3 有限级

```agda
module FF (n : ℕ) (d : Dn (Sk (suc n))) where
  K₁ : ℕ
  K₁ = suc n

  lay : ((W : Wd₂) → D (ly (suc K₁)) W) → HB (Sk K₁)
  lay o = rdr (RdF K₁) (tt , tt) hz (o W₁)

  Lg-lay : ∀ o → LgB (lay o)
  Lg-lay o = lgr (RdF K₁) (tt , tt) hz (o W₁) tt

  inc : ((W : Wd₂) → D (ly (suc K₁)) W) → HB (Sk K₁)
  inc o = δF K₁ (proj₁ d (lay o)) (proj₂ d _ (Lg-lay o))

  lg-inc : ∀ o → LgB (inc o)
  lg-inc o = lδF K₁ _ _

  trO : (κ : K (Sk K₁)) → (E (Sk K₁) κ → (W : Wd₂) → D (ly (suc K₁)) W) → (W : Wd₂) → D (ly (suc K₁)) W
  trO κ g W = trKg (pkgF n) ≤r κ (ss hself) g W

  open GF (kfin K₁) (ly (suc K₁)) trO inc public

idxF : ∀ n → Dn (Sk (suc n)) → HB (Sk (suc (suc n))) → HB (Sk (suc n))
idxF n d Λ = FF.lay n d (FF.fold n d v₀ Λ)

dnF : ∀ n → Dn (Sk (suc n))
dnF zero = (λ x → x) , (λ x l → l)
dnF (suc n) = (λ Λ → proj₁ (dnF n) (idxF n (dnF n) Λ)) , (λ Λ _ → proj₂ (dnF n) _ (FF.Lg-lay n (dnF n) (FF.fold n (dnF n) v₀ Λ)))

-- 第 n+1 级的级顶降到 Ht
Hn : ℕ → Ht
Hn n = proj₁ (dnF n) (Ωtop (Sk n))

lgHn : ∀ n → LgB (Hn n)
lgHn n = proj₂ (dnF n) (Ωtop (Sk n)) (Lg-Ωtop (Sk n))

cumF : ℕ → Ht
cumF zero = Hn zero
cumF (suc k) = cumF k ⊞ Hn (suc k)

lcumF : ∀ k → LgB (cumF k)
lcumF zero = lgHn zero
lcumF (suc k) = Lg-⊞ (cumF k) (Hn (suc k)) (lcumF k) (lgHn (suc k))

ΛF : Ht
ΛF = hl cumF

lΛF : LgB ΛF
lΛF = (λ k → ⊞-fst (cumF k) (Hn (suc k))) , lcumF
```

## §4 第 ω 级的下降

```agda
lgω : LgB lyω
lgω = (λ n → hsuc hself) , (λ n → lgly (suc n))

o1ω : ∀ {w} → hs hz ⊲[ w ] lyω
o1ω = hlim 0 hself

module Ev where
  open At lyω lgω o1ω
  -- 第 ω 层的树在 Λ = ω 里求值到第 2 层, 读成 Ht
  evω : D lyω (azero , hz) → Ht
  evω X = rdr (RdF 1) (tt , tt) hz
            (yc (Run {W = W₁} accᴸ X (z⊲ one , hself) (tt , tt) hself Act n0 Y₀) (tg ≤rf (hlim 1 hself) (tt , tt)))

  lg-evω : ∀ X → LgB (evω X)
  lg-evω X = lgr (RdF 1) (tt , tt) hz _ tt

dω : Dn Gω
dω = (λ x → Ev.evω (trω x (azero , hz))) , (λ x _ → Ev.lg-evω _)
```

## §5 第 ω+1 级折叠

```agda
layΩ : ((W : Wd₂) → D lyω W) → HB Gω
layΩ o = rdr RdΩ (tt , tt) hz (o W₁)

Lg-layΩ : ∀ o → LgB (layΩ o)
Lg-layΩ o = lgr RdΩ (tt , tt) hz (o W₁) tt

-- 底 1 读回 Ω_{ω ⊞ h} 在第 ω 层上的输出
δΩ : (h : Ht) → LgB h → HB Gω
δΩ h lh = rdr RdΩ (tt , tt) (hs hz) (OG.outX lyω lgω o1ω h lh)

incΩ : ((W : Wd₂) → D lyω W) → HB Gω
incΩ o = δΩ (proj₁ dω (layΩ o)) (proj₂ dω _ (Lg-layΩ o))

lg-incΩ : ∀ o → LgB (incΩ o)
lg-incΩ o = lgr RdΩ (tt , tt) (hs hz) _ tt

-- 旧种类 (m, κ): 第 m 级的翻译, 过第 m 层 (与 trω 同一个 trOm)
trOω : (κ : K Gω) → (E Gω κ → (W : Wd₂) → D lyω W) → (W : Wd₂) → D lyω W
trOω κ g W = trOm κ (λ m → sl m hself) g W

module FΩ where
  open GF kω lyω trOω incΩ public
```

## §6 ω 层的槽被回灌升高

```agda
-- 第 n+1 级的级顶折叠输出的读回 (同 LvFbFold.rt, 世界取 v₀: 有限级只读自己的码)
rt : ∀ n → HB (Sk (suc n))
rt n = idxF n (dnF n) (Ωtop (Sk (suc n)))

lrt : ∀ n → LgB (rt n)
lrt n = FF.Lg-lay n (dnF n) (FF.fold n (dnF n) v₀ (Ωtop (Sk (suc n))))

ιω : ∀ n → HB Gω
ιω n = ι {F = Sk} (suc n) (rt n)

V : ℕ → Wld
V zero = v₀
V (suc n) = raise (V n) kω (ιω n)

lgV : ∀ n → LgV (V n)
lgV zero = lv₀
lgV (suc n) = legal (V n) kω (ιω n) (Lg-ι {F = Sk} (suc n) (rt n) (lrt n)) (lgV n)

-- ω 层的界: 链上各槽的 ℕ-极限
slotLim : HB Gω
slotLim = hl (λ N → V (suc N) kω)

lslotLim : LgB slotLim
lslotLim = (λ N → mono (V (suc N)) kω (ιω (suc N)) kω) , (λ N → lgV (suc N) kω)

V∞ : Wld
V∞ = raise v₀ kω slotLim

lgV∞ : LgV V∞
lgV∞ = legal v₀ kω slotLim lslotLim lv₀
```

## §7 第 ω+1 级的下降, 闭项

```agda
idxΩ : HB Gω1 → HB Gω
idxΩ Λ = layΩ (FΩ.fold V∞ Λ)

dω1 : Dn Gω1
dω1 = (λ Λ → proj₁ dω (idxΩ Λ)) , (λ Λ _ → proj₂ dω _ (Lg-layΩ (FΩ.fold V∞ Λ)))

Hω1 : Ht
Hω1 = proj₁ dω1 (Ωtop Gω)

lgHω1 : LgB Hω1
lgHω1 = proj₂ dω1 (Ωtop Gω) (Lg-Ωtop Gω)

Λω1 : Ht
Λω1 = ΛF ⊞ Hω1

lΛω1 : LgB Λω1
lΛω1 = Lg-⊞ ΛF Hω1 lΛF lgHω1

T∞ω1 : A
T∞ω1 = T⁺ Λω1 lΛω1

Lg-T∞ω1 : Lg T∞ω1
Lg-T∞ω1 = Lg-T⁺ Λω1 lΛω1

fghω1 : ℕ → ℕ
fghω1 = FL.FGH (ord T∞ω1)

-- 对照: 只有有限级的对角
T∞F : A
T∞F = T⁺ ΛF lΛF
```

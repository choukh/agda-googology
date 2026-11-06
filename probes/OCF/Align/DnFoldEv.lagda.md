# 有内容的下降 (一): 经求值的下降, 对一切种类结构一条

> 不含记号. 入口 [DnFold](DnFold.lagda.md), 接口 [DnFoldIf](DnFoldIf.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> - **§1 在层 $L$ 上求值 `EvAt.evAt`**: 世界 $W$ 里第 $L$ 层的数据树, 用两种种类折叠的 `Run` (层 $\Lambda=L$, `HtTowerFClosed.At`) 求到第 2 层 (目标 `tg ≤rf e lW`, $e$ 是第 2 层在 $W$ 里的第一位置), 经第 1 级读回 (`LvRdPkg.RdF 1`) 落到 `Ht`. 与 `LvOmClosed.Dc.ev`, `LvRdFold.Ev.evω` 是同一个式子, 层与世界换成参数. **合法由读回的形状给出** (`lg-evAt`), 对一切数据树.
> - **§2 由 `DnEv S` 得下降 `toDn : DnEv S → DnK S`**: 翻译后求值. 下降的合法不要求输入合法, 也不要求翻译有任何性质.
> - **§3 求值系统的实例 `evSysHt : EvSys`** (层在 `Ht`), 与由 `DnEvS E S` 得下降 `toDnS`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DnFoldEv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (Ht; Wd₂; LgW₂; D; accᴸ; ≤rf; n0)
open import OCF.Align.HtTowerFClosed using (module At)
open import OCF.Align.LvRdPkg using (rdr; lgr; RdF)
open import OCF.Align.KcFoldIf using (DnK)
open import OCF.Align.DnFoldIf
```

## §1 在层 $L$ 上求值

```agda
module EvAt (L : Ht) (lL : LgB L) (o : ∀ {w} → hs hz ⊲[ w ] L) where
  open At L lL o

  evAt : ∀ {W} → LgW₂ W → hs (hs hz) ⊲[ W ] L → D L W → Ht
  evAt {W} lW e X = rdr (RdF 1) lW hz (yc (Run {W = W} accᴸ X ≤rf lW hself Act n0 Y₀) (tg ≤rf e lW))

  lg-evAt : ∀ {W} (lW : LgW₂ W) e X → LgB (evAt lW e X)
  lg-evAt lW e X = lgr (RdF 1) lW hz _ tt
```

## §2 由 `DnEv` 得下降

```agda
module _ {S : KS} (P : DnEv S) where
  open DnEv P

  evD : D Lw Wv → Ht
  evD X = EvAt.evAt Lw lLw o1 lWv ev2 X

  toDn : DnK S
  toDn = (λ x → evD (tr x)) , (λ x _ → EvAt.lg-evAt Lw lLw o1 lWv ev2 (tr x))
```

## §3 求值系统的实例 (层在 `Ht`)

```agda
OkHt : Ht → Wd₂ → Set
OkHt L W = Σ (LgB L) (λ _ → (∀ {w} → hs hz ⊲[ w ] L) × (hs (hs hz) ⊲[ W ] L))

evSysHt : EvSys
evSysHt = record
  { Lay = Ht ; Wor = Wd₂ ; LgWo = LgW₂ ; Dat = D ; Ok = OkHt
  ; evH = λ {L} ok lW X → EvAt.evAt L (proj₁ ok) (proj₁ (proj₂ ok)) lW (proj₂ (proj₂ ok)) X
  ; lgEv = λ {L} ok lW X → EvAt.lg-evAt L (proj₁ ok) (proj₁ (proj₂ ok)) lW (proj₂ (proj₂ ok)) X }

toDnS : ∀ {E : EvSys} {S : KS} → DnEvS E S → DnK S
toDnS {E} P = (λ x → EvSys.evH E ok lWv (tr x)) , (λ x _ → EvSys.lgEv E ok lWv (tr x))
  where open DnEvS P

-- DnEv 是 evSysHt 上的 DnEvS
ofDnEv : ∀ {S : KS} → DnEv S → DnEvS evSysHt S
ofDnEv P = record { Lw = Lw ; Wv = Wv ; ok = lLw , (o1 , ev2) ; lWv = lWv ; tr = tr }
  where open DnEv P
```

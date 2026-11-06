# Ω-极限坐标上的读回包 (七): 下降与闭项

> 不含记号. 入口 [LvOm](LvOm.lagda.md). 依赖 [LvOmFold](LvOmFold.lagda.md); 只读导入两种种类折叠的求值 (`HtTowerFClosed.At`, `T⁺`, `ord`) 与 `LvRdPkg.RdF` (第 1 级读回). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP.
>
> **下降 `Dc`** (照 `LvRdFold.Ev.evω` 的做法, 换到一般坐标): `Lv a c` 的高度经 `trN` 在世界 $W_a=(a,0)$ 上翻译成第 `Ly c` 层的树, 用两种种类折叠的求值 `Run` (层 $\Lambda=$ `Ly c`) 求到第 2 层, 经第 1 级读回落到 `Ht`. 要三件:
>
> - `Ly c` 合法 (`lgLy`, 对一切合法 $c$; `Ly-mono`: `H₀` 的路径在世界 $W_A$ 里搬成读回层的路径, `hLim` 的证据原样);
> - $1\lhd$ `Ly c` 对一切世界 (`o1`, 走第 0 支);
> - 第 2 层在 $W_a$ 里是 `Ly c` 的第一位置 (`ev2`, **模块参数**, 与 $c$ 和 $a$ 有关: 对 ΩA 与 $a=\omega$ 是 `hLim (lim 1 self) hself`, 即第 1 支在世界 $\omega$ 里可入).
>
> **闭项.** `TΩ = T⁺ (Dc HΩ)`: 层号 ΩA (外层世界 $\omega$) 的级顶经一级回灌读回 (`LvOmFold.HΩ`), 下降到 `Ht`, 再作两种种类折叠的下标. 合法 (`Lg-TΩ`), FGH (`fghΩ`). 无参数. 读法: 没有定理 (见入口 "值").

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvOmClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; z⊲)
import OCF.Align.CumReadCF as C
import OCF.Free.Level as FL
open import OCF.Align.HtTowerTy
open import OCF.Align.HtTowerFTree using (H₀; Ht; Wd₂; LgW₂; D; ≤rf; accᴸ; n0; κA)
open import OCF.Align.HtTowerFClosed using (module At; T⁺; Lg-T⁺; ord)
open import OCF.Align.LvRdPkg using (rdr; lgr; RdF)
open import OCF.Align.LvOmLev
open import OCF.Align.LvOmRd
open import OCF.Align.LvOmFold using (hA₀; ΩA; Lg-ΩA; ωA; Lg-ωA; HΩ; Lg-HΩ)
```

## §1 读回层合法

```agda
Ly-mono : ∀ {c c′ : H₀} {W : Wd₂} → c ⊲[ proj₁ W ] c′ → Ly c ⊲[ W ] Ly c′
Ly-mono hself = hself
Ly-mono (hsuc p) = hsuc (Ly-mono p)
Ly-mono (hlim n p) = hlim n (Ly-mono p)
Ly-mono (hLim {c = x} e p) = hLim {κ = κA} {c = x} e (Ly-mono p)

lgLy : ∀ c → LgB c → LgB (Ly c)
lgLy hz _ = tt
lgLy (hs c) l = lgLy c l
lgLy (hl f) (st , l) = (λ n → Ly-mono (st n)) , (λ n → lgLy (f n) (l n))
lgLy (hΩ κ g) (mo , l) = (λ lw e e′ pr → Ly-mono (mo (proj₁ lw) e e′ pr)) , (λ x lx → lgLy (g x) (l x lx))

o1 : ∀ c {w : Wd₂} → hs hz ⊲[ w ] Ly c
o1 hz = hself
o1 (hs c) = hsuc (o1 c)
o1 (hl f) = hlim 0 (o1 (f 0))
o1 (hΩ κ g) {w} = hLim {κ = κA} {c = azero} (z⊲ (proj₁ w)) (o1 (g azero))
```

## §2 下降

```agda
module Dc (a : A) (la : Lg a) (c : H₀) (lc : LgB c) (ev2 : hs (hs hz) ⊲[ (a , hz) ] Ly c) where
  open Rd a
  open At (Ly c) (lgLy c lc) (o1 c)

  Wa : Wd₂
  Wa = a , hz

  lWa : LgW₂ Wa
  lWa = la , tt

  ev : D (Ly c) Wa → Ht
  ev X = rdr (RdF 1) lWa hz (yc (Run {W = Wa} accᴸ X ≤rf lWa hself Act n0 Y₀) (tg ≤rf ev2 lWa))

  lg-ev : ∀ X → LgB (ev X)
  lg-ev X = lgr (RdF 1) lWa hz _ tt

  dn : HB (Lv c) → Ht
  dn x = ev (trN (pk c) x Wa C.self)

  lg-dn : ∀ x → LgB (dn x)
  lg-dn x = lg-ev _
```

## §3 闭项

```agda
ev2Ω : hs (hs hz) ⊲[ (ωA , hz) ] Ly ΩA
ev2Ω = hLim {κ = κA} {c = asuc azero} (C.lim 1 C.self) hself

module DΩ = Dc ωA Lg-ωA ΩA Lg-ΩA ev2Ω

HΩd : Ht
HΩd = DΩ.dn HΩ

lgHΩd : LgB HΩd
lgHΩd = DΩ.lg-dn HΩ

TΩ : A
TΩ = T⁺ HΩd lgHΩd

Lg-TΩ : Lg TΩ
Lg-TΩ = Lg-T⁺ HΩd lgHΩd

fghΩ : ℕ → ℕ
fghΩ = FL.FGH (ord TΩ)
```

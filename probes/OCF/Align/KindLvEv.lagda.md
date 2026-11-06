# 按级回灌 (三之二): 每站的求值走同一个折叠

> 不含记号. 入口 [KindLv](KindLv.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延, 不用 UIP 作前提.
>
> 与 [NewTwrEv](NewTwrEv.lagda.md) 的 `evN` 同一个求值 (层 `LX X`, 基世界 `W₀X X`, 数据 `ΩX X`, 都从 NewTwrEv 导入; 折到第 2 层; 读回 `NewTwrRd.rdG`), 只是折叠换成 [KindLvRun](KindLvRun.lagda.md), 级回灌取平凡的 `λ _ → inj₂ tt`: 这时 `KindLvRun` 的每一行都退回 `GenFoldRun` 的原样一行 (`RKv … (inj₂ _) = RKa …`), 所以 [判断, 逐行] 与 `evN` 是同一个折叠. 不导入 `GenFoldRun`, 让闭项的切片只含一份折叠 (行数).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.KindLvEv where

open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_)
open import OCF.Align.HtTowerTy
open import OCF.Align.GenFoldIf using (DK; module FoldTy; n0)
open import OCF.Align.GenFoldTree using (module Tree; accᴸ)
open import OCF.Align.GenFoldInst using (genLev; ldLev; flLev)
open import OCF.Align.NewTwrEv using (two; LX; lLX; oLX; eLX; W₀X; lW₀X; ΩX)
import OCF.Align.KindLvRun as KR
import OCF.Align.NewTwrRd as NR

module EvK {S : KS} (X : HB S) where
  open Tree (Lev X)
  open KR (Lev X) (genLev X) (ldLev X) (flLev X) (LX X) (lLX X) (oLX X) (λ _ → inj₂ tt)
  open FoldTy (Lev X) (LX X) using (Ig; St; st; tg)

  Act : ∀ {ly W} → Ig ly W
  Act p lW′ _ Y = Stp Y

  Y₀ : ∀ {W} → St W
  Y₀ = st zeroD n0 n0

  out₂ : ∀ {W} → LgW L₀ W → two ⊲[ W ] LX X → D (LX X) W → D two W
  out₂ {W} lW e D′ = yc (Run {W = W} accᴸ D′ ≤rf lW hself Act n0 Y₀) (tg ≤rf e lW)

out₂K : ∀ {S : KS} (X : HB S) → DK (Lev X) (hs (hs hz)) (W₀X X)
out₂K X = EvK.out₂ X (lW₀X X) (eLX X) (ΩX X)

evK : ∀ {S : KS} (X : HB S) → HB (step (Lev X))
evK X = NR.rdG (Lev X) (genLev X) (ldLev X) (lW₀X X) hz (out₂K X)

lg-evK : ∀ {S : KS} (X : HB S) → LgB (evK X)
lg-evK X = NR.Lg-rdG (Lev X) (genLev X) (ldLev X) (lW₀X X) hz (out₂K X) tt

-- 每站的下降 (同 NewTwrEv.ρ′): 层号是后继时求值, 否则 0
ρK : ∀ {S : KS} (b : HB S) → HB (Lev b)
ρK hz = hz
ρK (hs X) = evK X
ρK (hl f) = hz
ρK (hΩ κ g) = hz

lρK : ∀ {S : KS} (b : HB S) → LgB (ρK b)
lρK hz = tt
lρK (hs X) = lg-evK X
lρK (hl f) = tt
lρK (hΩ κ g) = tt
```

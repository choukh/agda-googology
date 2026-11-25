# YiSuc 接线：`StrChain` 到两站的 BTBO 下界

**验收文件，档位：条件定理 (前提 `StrChain`，即 [YiUBP2](YiUBP2.lagda.md) 的链点上的 `Str`)。** `chainP-str : StrChain → ChainP` (主线的 `ChainP`)，`btbo⁺-str : StrChain → D.BTBOᴵ ≼ NA.read NT.T⁺` (下一站)。
办法：`p2₂-str` 给 `P2₂`，`chain-cond₂` 给链点两向，`ˣ→ᵖ` 落到 `ChainP`，再接 [YiNextValFin](YiNextValFin.lagda.md) 的 `btbo⁺-from-main`。`StrChain` 的进展在 [YiSucOne](YiSucOne.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSucWire where

open import Data.Product.Base using (_,_; proj₁)
open import OCF.Align.Value using (_≼_)
open import OCF.Align.YiVmConExact using (ˣ→ᵖ)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Lean.YiLeanValFin as MV
import OCF.Lean.YiNextAcc as NA
import OCF.Lean.YiNextTop as NT
open import OCF.Lean.YiNextValFin using (btbo⁺-from-main)
open import OCF.Lean.YiEmb2 using (P2₂; chain-cond₂)
open import OCF.Lean.YiUBP2 using (StrChain; p2₂-str; btbo-str)
```

```agda
p2₂→chainP : P2₂ → MV.ChainP
p2₂→chainP p2 n = n , ˣ→ᵖ (proj₁ (chain-cond₂ p2 n))

chainP-str : StrChain → MV.ChainP
chainP-str s = p2₂→chainP (p2₂-str s)

btbo⁺-str : StrChain → D.BTBOᴵ ≼ NA.read NT.T⁺
btbo⁺-str s = btbo⁺-from-main (chainP-str s)
```

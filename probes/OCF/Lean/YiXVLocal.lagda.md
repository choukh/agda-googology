# YiXV：实际层号 2 前缀所用的第 1 层底
> 验收文件。编译定理：`B2` 的两个目标层 0 分量不高于 ε₀；实际孩子底 `D1` 上的 Ω 树不高于参照 `ψ⁰ (Ω₁ + Ω₁)`。
> `zeroU`、`ΩU` 实填 `YiXVSim` 的关系。没有 `pre 1`、`Need1` 或塔的整体上界。
> 分量上界来源 `YiCeilRead.ε₀-upper`、`YiLSTw1.KG`；没有改底或折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch #-}
module OCF.Lean.YiXVLocal where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (self; ins)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiXVStart using (B2)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
open import OCF.Lean.YiLSTw1 using (KG)
open import OCF.Lean.YiCeilRead using (ε₀-upper)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVSim as S

b2 : read (b⊥ B2) ≼ D.γ 1
b2 = ε₀-upper

s2 : read (bs B2 zero (ins (ins self))) ≼ D.γ 1
s2 = ≼-trans (≅→≼ (KG (suc zero))) ε₀-upper

D1 : Base (suc zero)
D1 = dS (suc zero) tt tt B2 zero

module U = S.Sim D1

zeroU : U.U zero O.Ω₁
zeroU = U.uz b2 s2

ΩU : U.U (Ωt (suc zero)) (O.Ω₁ L.+ O.Ω₁)
ΩU = U.un (λ a y q → U.uu O.Gd-Ω zeroU q)

Ω-upper : read (ψ⊥ (suc zero) tt tt D1 (Ωt (suc zero))) ≼ L.ψ⁰ (O.Ω₁ L.+ O.Ω₁)
Ω-upper = proj₁ (U.upper (O.Gd-+ O.Gd-Ω O.Gd-Ω) ΩU)
```

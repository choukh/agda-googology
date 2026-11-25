# YiLamFold: `T⁺ʷ` 的值问到极限层号上的结点, 那里的派发一律折叠

验收文件. 编译定理 `asked : NA.read (Ψ₀ (gK ξa)) ≼ NA.read W.T⁺ʷ` (坐标 `ξa = 1 + (Tw 2 + 1)` 经第一位置在结点链第 1 点之下); `Tt-node` (`refl`): `Tt ξa` 是位置 `rN` 上的结点, 层号 `lev (tw 2) rN` 是 ℕ 极限 (`lim-level`);
`lost` (`refl`): 它的链的派发对一切位置是折叠, `root-lost`: 包括 Ω_Ω 的根 (层号 0); `could`: 这个层号里有层号 0 的槽位. 对照 `root-kept`: 字面有限的层号 2 上同一个根保留. 不陈述丢掉多少值. [判断] `Stepᴳʷ` ([YiLamVStep](YiLamVStep.lagda.md)) 要的值来自这类层号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamVLost where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiLamVBtbo using (Vw)
open import OCF.Lean.YiLamVOne using (V2; Ψ₀; p₀; up≼; Tt; gK; gk₁; d)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)
```

## 1 被问到的坐标

```agda
a : R
a = plus zero G.top (W.Tw 2)

ξa : R
ξa = plus zero G.top (G.suc (W.Tw 2))

ξa-form : ξa ≡ G.suc a
ξa-form = refl

c-g : Cp zero (G.suc (W.Tw 2)) (gk₁ G.top)
c-g = inj₂ (0 , inj₂ (0 , inj₂ (1 , inj₂ (0 , inj₂ (0 , inj₂ (0 , inj₁ refl))))))

c-d : Cp zero ξa (d 1)
c-d = add-cp zero G.lc dnLc G.top c-g

asked : NA.read (Ψ₀ (gK ξa)) ≼ NA.read W.T⁺ʷ
asked = ≼-trans (up≼ (add-cp (tw 2) G.lc dnLc G.top (W.Kfk-cp zero Tt c-d))) (≼l 1 (≼l 1 (≼-refl _)))
```

## 2 那里的结点与它的派发

```agda
rN : Pre (tw 2)
rN = W.nrmk zero ξa , W.nrmk-lgl zero ξa , inj₁ tt

gN : Raw ⌜ W.nrmk zero a ⌝ → Raw (tw 2)
gN η = W.Ψ (tw 2) (Vw (W.nrmk zero a) (W.nrmk-lgl zero ξa)) (λ r → keep (W.nrmk zero ξa , W.nrmk-lgl zero ξa , inj₂ r) refl) η

Tt-node : Tt ξa ≡ G.lc rN gN
Tt-node = refl

IsLimL : LF → Set
IsLimL (lim _) = ⊤
IsLimL _ = ⊥

lim-level : IsLimL (lev (tw 2) rN)
lim-level = tt

lost : ∀ r → W.cmpw V2 rN r ≡ fold
lost r = refl

root-lost : W.rootW (lev (tw 2) rN) zero ⌜_⌝ (W.witU zero) (W.cmpw V2 rN) ≡ fold
root-lost = refl

could : Way (lev (tw 2) rN) zero
could = keep (0 , 0 , 0 , inj₂ (inj₁ tt)) refl
```

## 3 对照: 字面有限的层号上同一个根保留

```agda
rF : Pre (tw 2)
rF = G.suc (G.suc G.top) , tt , inj₁ tt

root-kept : W.rootW (lev (tw 2) rF) zero ⌜_⌝ (W.witU zero) (W.cmpw V2 rF) ≡ keep (inj₂ (inj₁ tt)) refl
root-kept = refl
```

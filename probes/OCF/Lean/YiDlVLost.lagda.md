# 燃料搜索派发的 `T⁺ʷ` 的值问到 `YiDlLost` 的那个结点

验收文件. 编译定理 `asked : NA.read (Ψ₀ (gK ξa)) ≼ NA.read W.T⁺ʷ` (照 [YiLamVLost](YiLamVLost.lagda.md) §1, 坐标经第一位置在结点链第 1 点之下), `asked-node`: 其中结点 `G.lc rN bN` 的值不高于 `T⁺ʷ`; `asked-step`: 也不高于 `Stepᴳʷ` 结论里的 `Ψ₀ (gK (d (suc m)))`, 对一切 m; `same-gK` (`refl`): 这里的 `gK` 就是 [YiDlLost](YiDlLost.lagda.md) 的. 那个结点链的第一步在 ℕ 极限层号的位置 `pN` 上折叠 (`YiDlLost.lostP`). 只是下界, 不陈述丢掉多少值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDlVLost where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
import OCF.Lean.YiDlLost as X
open import OCF.Lean.YiDlInst using (ξa; rN)
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; up≼; Tt; gK; gk₁; d)
open import OCF.Lean.YiUniNegCmp using (cp-trans)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)
```

```agda
same-gK : X.gK ≡ gK
same-gK = refl

c-g : Cp zero (G.suc (W.Tw 2)) (gk₁ G.top)
c-g = inj₂ (0 , inj₂ (0 , inj₂ (1 , inj₂ (0 , inj₂ (0 , inj₂ (0 , inj₁ refl))))))

c-d : Cp zero ξa (d 1)
c-d = add-cp zero G.lc dnLc G.top c-g

asked : NA.read (Ψ₀ (gK ξa)) ≼ NA.read W.T⁺ʷ
asked = ≼-trans (up≼ (add-cp (tw 2) G.lc dnLc G.top (WL.Kfk-cp zero Tt c-d))) (≼l 1 (≼l 1 (≼-refl _)))

asked-node : NA.read (Ψ₀ (G.lc rN X.bN)) ≼ NA.read W.T⁺ʷ
asked-node = ≼-trans (≼l 1 (≼-refl _)) asked

-- `Stepᴳʷ` 的结论里的项对一切 m 都在这个结点之上.
dchain : ∀ m → Cp zero (d 1) (d (suc m))
dchain zero = inj₁ refl
dchain (suc m) = cp-trans (dchain m) (plus-weak zero (d (suc m)) (gk₁ (d (suc m))))

asked-step : ∀ m → NA.read (Ψ₀ (G.lc rN X.bN)) ≼ NA.read (Ψ₀ (gK (d (suc m))))
asked-step m = ≼-trans (≼l 1 (≼-refl _))
  (up≼ (add-cp (tw 2) G.lc dnLc G.top (WL.Kfk-cp zero Tt (cp-trans c-d (dchain m)))))
```

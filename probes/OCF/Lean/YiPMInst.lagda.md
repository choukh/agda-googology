# F2 参数化族的空表与最小表实例

验收文件；六条闭输入相等为有限测试，覆盖指定孩子那一行；`empty-row` 为任意输入的回退行定理。
两个命名空间共用一份折叠、保持与下降证明；未把闭输入测试当作两套递归函数的全域相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMInst where

open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold using (B₀; Base)
open import OCF.Lean.YiPMTable using (empty; tbᶠ)
import OCF.Lean.YiPMFold
import OCF.Lean.YiPMLSFold
import OCF.Lean.YiPMLSTw1
import OCF.Lean.YiPMEBShape
import OCF.Lean.YiPMLSBtbo
import OCF.Lean.YiPMEBBtbo
import OCF.Lean.YiPMMEAnchor
import OCF.Lean.YiPMMEStep
import OCF.Lean.YiPMT2Desc
import OCF.Lean.YiPMT2Frame
import OCF.Lean.YiPMEXRow
import OCF.Lean.YiPMMWPre
import OCF.Lean.YiPMEVReach
import OCF.Lean.YiPMPHBase
import OCF.Lean.YiPMPHCtx
import OCF.Lean.YiPMANFam
import OCF.Lean.YiPMANKp
import OCF.Lean.YiPMANLv
import OCF.Lean.YiPMPHEnd
import OCF.Lean.YiPMANReach
import OCF.Lean.YiPMANEnd

module Empty where
  module Fold = OCF.Lean.YiPMFold.F empty
  module LSFold = OCF.Lean.YiPMLSFold.F empty
  module LSTw1 = OCF.Lean.YiPMLSTw1.F empty
  module EBShape = OCF.Lean.YiPMEBShape.F empty
  module LSBtbo = OCF.Lean.YiPMLSBtbo.F empty
  module EBBtbo = OCF.Lean.YiPMEBBtbo.F empty
  module MEAnchor = OCF.Lean.YiPMMEAnchor.F empty
  module MEStep = OCF.Lean.YiPMMEStep.F empty
  module T2Desc = OCF.Lean.YiPMT2Desc.F empty
  module T2Frame = OCF.Lean.YiPMT2Frame.F empty
  module EXRow = OCF.Lean.YiPMEXRow.F empty
  module MWPre = OCF.Lean.YiPMMWPre.F empty
  module EVReach = OCF.Lean.YiPMEVReach.F empty
  module PHBase = OCF.Lean.YiPMPHBase.F empty
  module PHCtx = OCF.Lean.YiPMPHCtx.F empty
  module ANFam = OCF.Lean.YiPMANFam.F empty
  module ANKp = OCF.Lean.YiPMANKp.F empty
  module ANLv = OCF.Lean.YiPMANLv.F empty
  module PHEnd = OCF.Lean.YiPMPHEnd.F empty
  module ANReach = OCF.Lean.YiPMANReach.F empty
  module ANEnd = OCF.Lean.YiPMANEnd.F empty

module Minimum where
  module Fold = OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ
  module LSFold = OCF.Lean.YiPMLSFold.F OCF.Lean.YiPMTable.tbᶠ
  module LSTw1 = OCF.Lean.YiPMLSTw1.F OCF.Lean.YiPMTable.tbᶠ
  module EBShape = OCF.Lean.YiPMEBShape.F OCF.Lean.YiPMTable.tbᶠ
  module LSBtbo = OCF.Lean.YiPMLSBtbo.F OCF.Lean.YiPMTable.tbᶠ
  module EBBtbo = OCF.Lean.YiPMEBBtbo.F OCF.Lean.YiPMTable.tbᶠ
  module MEAnchor = OCF.Lean.YiPMMEAnchor.F OCF.Lean.YiPMTable.tbᶠ
  module MEStep = OCF.Lean.YiPMMEStep.F OCF.Lean.YiPMTable.tbᶠ
  module T2Desc = OCF.Lean.YiPMT2Desc.F OCF.Lean.YiPMTable.tbᶠ
  module T2Frame = OCF.Lean.YiPMT2Frame.F OCF.Lean.YiPMTable.tbᶠ
  module EXRow = OCF.Lean.YiPMEXRow.F OCF.Lean.YiPMTable.tbᶠ
  module MWPre = OCF.Lean.YiPMMWPre.F OCF.Lean.YiPMTable.tbᶠ
  module EVReach = OCF.Lean.YiPMEVReach.F OCF.Lean.YiPMTable.tbᶠ
  module PHBase = OCF.Lean.YiPMPHBase.F OCF.Lean.YiPMTable.tbᶠ
  module PHCtx = OCF.Lean.YiPMPHCtx.F OCF.Lean.YiPMTable.tbᶠ
  module ANFam = OCF.Lean.YiPMANFam.F OCF.Lean.YiPMTable.tbᶠ
  module ANKp = OCF.Lean.YiPMANKp.F OCF.Lean.YiPMTable.tbᶠ
  module ANLv = OCF.Lean.YiPMANLv.F OCF.Lean.YiPMTable.tbᶠ
  module PHEnd = OCF.Lean.YiPMPHEnd.F OCF.Lean.YiPMTable.tbᶠ
  module ANReach = OCF.Lean.YiPMANReach.F OCF.Lean.YiPMTable.tbᶠ
  module ANEnd = OCF.Lean.YiPMANEnd.F OCF.Lean.YiPMTable.tbᶠ

import OCF.Lean.YiLegFold as Old
import OCF.Lean.YiVTFold as New
module E = OCF.Lean.YiPMFold.F empty
module M = OCF.Lean.YiPMFold.F OCF.Lean.YiPMTable.tbᶠ

old-zero : E.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) zero ≡ Old.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) zero
old-zero = refl
old-one : E.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) (suc zero) ≡ Old.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) (suc zero)
old-one = refl
new-zero : M.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) zero ≡ New.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) zero
new-zero = refl
new-one : M.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) (suc zero) ≡ New.ψs zero tt tt (B₀ zero) zero self (Ωt zero) (Ωt-nz zero) (suc zero)
new-one = refl

K : L
K = Ωₗ zero (λ _ → zero)
eK : Ev K
eK = tt , λ _ → self , tt
rK : Rt K
rK = tt , λ _ → tt
uK : Tr K
uK = up zero zero (suc zero) ◃s
old-row : E.ψs K eK rK (B₀ K) zero (inb zero self) (Ωt zero) (Ωt-nz zero) uK ≡ Old.ψs K eK rK (B₀ K) zero (inb zero self) (Ωt zero) (Ωt-nz zero) uK
old-row = refl
new-row : M.ψs K eK rK (B₀ K) zero (inb zero self) (Ωt zero) (Ωt-nz zero) uK ≡ New.ψs K eK rK (B₀ K) zero (inb zero self) (Ωt zero) (Ωt-nz zero) uK
new-row = refl

empty-row : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
  (c′ : Tr k) (w : j ≤ h c′) (β : Tr j) (nβ : j ⊢ zero ◃ β) (x : Tr (Ωₗ k h)) (c : Tr k) (y : Tr (h c))
  (e : h c ⊢ zero ◃ y)
  → E.ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ (up x c y e)
  ≡ E.ψs (Ωₗ k h) ε ρ B j (inb c′ w) β nβ x + ι j (E.ψ₀ (h c) (proj₂ (proj₂ ε c)) (proj₂ ρ c) y)
empty-row k h ε ρ B j c′ w β nβ x c y e = refl

module EmptyShape where
  open import Data.Sum using (inj₁)
  open Empty.Fold using (ψs; dW; bs)
  open Empty.LSTw1 using (h₁; G)
  open Empty.T2Frame using (one; two; β; ε¹; ρ¹; IsLim)
  β₁-form : bs (dW zero h₁ ε¹ ρ¹ (B₀ (tw 1)) two β) (suc zero) (ins self)
          ≡ Ω (inj₁ tt) (λ c → Ωt (suc zero) + ι (suc zero) (G c))
  β₁-form = refl
  flat-lim : IsLim (ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (suc zero) (inb one self) (Ωt (suc zero)) (Ωt-nz (suc zero))
                       (Upc (tw 1) one β (Ωt-nz (tw 1)) (Ωt (h₁ one))))
  flat-lim = tt

module MinimumShape where
  open Minimum.Fold using (ψs)
  open Minimum.LSTw1 using (h₁)
  open Minimum.T2Frame using (one; β; ε¹; ρ¹; IsLim)
  flat-lim : IsLim (ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) (suc zero) (inb one self) (Ωt (suc zero)) (Ωt-nz (suc zero))
                       (Upc (tw 1) one β (Ωt-nz (tw 1)) (Ωt (h₁ one))))
  flat-lim = tt
```

# Ω 形状的具证据、非空步进实例
验收文件（读记号）；下标层为 0，孩子层恒为 0，比较表逐字给 self，不使用判定或全局三歧。
`LayerIndex` 和空前缀均有闭项，由此给所有底、前缀、分支的条件步进，不是假前提组装。
这是接口可满足片段，不是规范塔的强度结果；实际 tw 1 的证据失败另见 YiGTIndexNeg。
入口：`layer-Ω₀`、`step-Ω₀`、`prefix-Ω₀`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTOmega where
open import Data.Unit using (tt)
open import Data.Maybe using (just)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiSUMin using (rd-zero)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiGTIndex
open import OCF.Lean.YiGTDirect using (LayerIndex)
open import OCF.Lean.YiGTSlot using (OmegaStepAt; omega-step-at)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR

Ω₀ : L
Ω₀ = nd (sΩ zero) (λ _ → zero)

oΩ : Ok Ω₀
oΩ = (tt , λ _ → self) , λ _ → tt

rΩ : Rb Ω₀
rΩ = (λ _ _ → just (inj₁ self)) , λ _ → tt

zero-path : (w : zero ≤ zero) → IndexOK zero tt tt zero w []
zero-path self = index-zero zero tt tt

layer-Ω₀ : LayerIndex Ω₀ oΩ rΩ
layer-Ω₀ = slots , λ _ → tt
  where
  slots : OCF.Lean.YiGTDirect.SlotIndex Ω₀ oΩ rΩ
  slots (inj₁ (inj₁ tt)) ν nu with rd-zero nu
  ... | refl = zero-frame Ω₀ oΩ (ink self) , λ _ → zero-path self
  slots (inj₁ (inj₂ ())) ν nu
  slots (inj₂ (c , inj₁ tt)) ν nu with rd-zero nu
  ... | refl = zero-frame Ω₀ oΩ (inc c self) , λ _ → zero-path self
  slots (inj₂ (c , inj₂ ())) ν nu

prefix-Ω₀ : PrefixU (B₀ Ω₀) []
prefix-Ω₀ (inj₁ (inj₁ tt)) ν nu with rd-zero nu
... | refl = H.m1 refl H.mz
prefix-Ω₀ (inj₁ (inj₂ ())) ν nu
prefix-Ω₀ (inj₂ (c , inj₁ tt)) ν nu with rd-zero nu
... | refl = H.m1 refl H.mz
prefix-Ω₀ (inj₂ (c , inj₂ ())) ν nu

step-Ω₀ : OmegaStepAt zero (λ _ → zero) oΩ rΩ
step-Ω₀ = omega-step-at zero (λ _ → zero) oΩ rΩ layer-Ω₀
```

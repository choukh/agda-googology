# 精确 ψ 的有界种子合同

ψ 只用到源层之下的目标种子与共尾层种子。
因此合同以同一个源层为字面公共界，不假设所有裸层号上已存在正确 Ω。
第 1 层的合同在本篇实填；更高层的合同须由后续 Ω 构造给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactSeeds where

open import Data.List.Base using ([])
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Align.EboLeanDef using (T; Ωt)
open import OCF.Align.EboLeanBase using (<sucT)
open import OCF.Align.EboLean3Omega using (Acc′)
open import OCF.Align.JiaBase using (Seeds; Below; below; module Layer)
open import OCF.Align.JiaRep using (Rep; module RelLayer)

record SeedSpec (seeds : Seeds) (ℓ : T) : Set where
  field
    sound : ∀ {i} → Below i ℓ → (ai : Acc′ i) → Rep ai (Seeds.seed seeds i ai) (Ωt i)
open SeedSpec public

one-seeds : Seeds
Seeds.seed one-seeds i a = Layer.s Layer.z

one-spec : SeedSpec one-seeds (Ωt [])
sound one-spec (below ni p) ai with <sucT [] p
... | inj₁ ()
... | inj₂ refl = RelLayer.rs RelLayer.rz
```

`one-seeds` 只在 `one-spec` 的有界域内被证明正确；没有说高层种子也已完成。
合同不是无条件闭项，不能据它宣称全塔已经接线。

# 甲脚手架：沿可及层族的关系式码树对应

按作者第三轮选定的设计，原树及其 Ω 分支域完全不动。
关系随原树族同一份可及证明分层：本层的 Ω 子句只将已经定义好的
低层关系放在蕴含前件，本层关系只出现在后件。
这没有要求任意 raw 树有码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRep where

open import Data.Nat.Base using (ℕ)
open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.EboLeanDef using (T; sucT; cof; cω; cΩ; fsn; fsT)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase using (Tree; Low; Below; below; module Layer)

module RelLayer
  (ℓ : T)
  (Low₀ : ∀ j → Below j ℓ → Set)
  (RepLow₀ : ∀ j p → Low₀ j p → T → Set)
  where

  data Rel : Layer.Tree ℓ Low₀ → T → Set where
    rz : Rel Layer.z []
    rs : ∀ {x c} → Rel x c → Rel (Layer.s x) (sucT c)
    rl : ∀ {f c} → cof c ≡ cω →
      (∀ n → Rel (f n) (fsn c n)) → Rel (Layer.l f) c
    ro : ∀ {j p f c} → cof c ≡ cΩ j →
      (∀ {y d} → RepLow₀ j p y d → Rel (f y) (fsT c d)) →
      Rel (Layer.o p f) c

Rep : ∀ {ℓ} (a : Acc′ ℓ) → Tree ℓ a → T → Set
RepLow : ∀ ℓ (a : Acc′ ℓ) j p → Low ℓ a j p → T → Set
Rep {ℓ} a = RelLayer.Rel ℓ (Low ℓ a) (RepLow ℓ a)
RepLow ℓ (acc h) j (below nj p) = Rep (h nj p)
```

`ro` 的前提只消费已有的低层对应证据，没有生成从原始输入到码的函数。
这里只定义对应关系；尚无 ψ 保持定理或序数值验收。

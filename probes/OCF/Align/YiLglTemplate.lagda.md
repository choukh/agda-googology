# D7 模板边界：逐点 ψ 不会自动把常列变严格

这是第4层的模板接口诊断，明读甲的记号依赖，不进入平行树侧基础模块。
只写已有程序的归约等式，不续写 ψ、γ 或正则性。
常零极限源经逐点 ψ 仍是常种子极限；合同没有源列的严格性字段。
该源不是已经认证的 EBO 实际输入，不能由此否定实际轨道的严格保持。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglTemplate where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase using (Tree; Seeds; Below; module Layer)
import OCF.Align.JiaExactFold as J
open import OCF.Align.JiaExactSeeds using (one-seeds; one-spec; SeedSpec)
open import OCF.Align.EboLeanDef using (Ωt)
open import Data.List.Base using ([])

module _ (seeds : Seeds) where
  module F = J.Fold seeds

  constant-output : ∀ {ℓ i} (aℓ : Acc′ ℓ) (ai : Acc′ i) (p : Below i ℓ) →
    F.ψ aℓ ai p (Layer.l (λ _ → Layer.z)) ≡
    Layer.l (λ _ → Seeds.seed seeds i ai)
  constant-output (acc h) (acc hi) p = refl

-- 有界种子合同本身并非空假设；这不为上述常列源提供 Rep 或实际 Reach。
contract-instance : SeedSpec one-seeds (Ωt [])
contract-instance = one-spec
```

constant-output 是对模板全部种子的归约事实；“每支输出相等”由右边常函数直接展示。
它没有主张满足逐项 Rep 的实际 EBO 列会停顿，也没有检验全部 gt 链的严格保持。
因此基础构造的正面严格性定理不能自动作为完整模板的严格性合同。

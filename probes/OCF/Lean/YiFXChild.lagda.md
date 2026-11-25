# 干净对象的内链孩子等式
验收文件；编译定理：每个实际链点的下一步是其孩子层号上标准底 Ω 树的折叠。
只陈述树侧等式；不推出 ψ₀(Ω_Ω) 或 ψ₀(Ω_{Ω₂}) 值界。
`out` 的对应等式已有 `YiUTTwoLocal.out-child`，这里不重证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFXChild where
open import Data.Nat using (ℕ; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiUTTwo as U

-- perf: C-9/S-1；在变量 d 上展开一次 opaque 内层函数，保留组合路径的原样。
opaque
  unfolding U.Inner.feed U.Inner.g
  feed-child : ∀ d → U.Inner.feed d ≡ proj₁ (TB.ψ (U.a d) (proj₂ U.o₂ d) (MT.rbᶻ (U.a d))
    (F.B₀ (U.a d)) K.one (P.self P.∙ proj₂ (proj₁ U.o₂) d)
    (O.Ωt K.one) (proj₁ (O.Ωt (U.a d))))
  feed-child d = refl

chain-child : ∀ n → U.Inner.chain (suc n) ≡ proj₁
  (TB.ψ (U.a (U.Inner.chain n)) (proj₂ U.o₂ (U.Inner.chain n))
    (MT.rbᶻ (U.a (U.Inner.chain n))) (F.B₀ (U.a (U.Inner.chain n))) K.one
    (P.self P.∙ proj₂ (proj₁ U.o₂) (U.Inner.chain n))
    (O.Ωt K.one) (proj₁ (O.Ωt (U.a (U.Inner.chain n)))))
chain-child n = feed-child (U.Inner.chain n)
```

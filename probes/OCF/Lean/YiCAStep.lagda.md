# 后续链点推进的值形式前提
不读记号；条件定理，对任意颈结点证书 o：两条链每个对应点上的值形式一步（`StepChain`：源、目标链点按值有序时，下一链点与该点输出也按值有序）推出一切 n 的 `ChainAdvance n`（`advance`）与 `YiTZLocal.At.Cover`（`cover`）；第 0 点无前提成立（`at-zero`）。
`Step`（对一切第 0 层树对）是台账 V120（跨孩子层的值关系，`YiVRRead.GMono` 一类）带两格底偏移的形式，推出 `StepChain`；两者都是待填类型，本文件不证也不否定。
不否定什么；为何 `YiPTLadder.E` 的做法到不了第 2 点见 [YiCAShape](YiCAShape.lagda.md)，末端接线在 [YiCAAccept](YiCAAccept.lagda.md)。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCAStep where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTZLocal as T
import OCF.Lean.YiTYLocal as Y
import OCF.Lean.YiTQChain as Q

module At (o : P.Ok T.neck) where
  module A = T.At o
  module C = Y.At o
  module D = Q.At o
  Step-at : B.Tr B.zero → B.Tr B.zero → Set
  Step-at z z′ = V.val B.zero z V.≼ V.val B.zero z′
    → (V.val B.zero (T.Source.feed z) V.≼ V.val B.zero (A.Target.feed z′))
    × (V.val B.zero (proj₁ (T.Source.out z)) V.≼ V.val B.zero (proj₁ (A.Target.out z′)))
  Step : Set
  Step = (z z′ : B.Tr B.zero) → Step-at z z′
  StepChain : Set
  StepChain = (n : ℕ) → Step-at (T.Source.chain n) (A.Target.chain n)

  from-step : Step → StepChain
  from-step s n = s (T.Source.chain n) (A.Target.chain n)

  at-zero : Step-at B.zero B.zero
  at-zero _ = D.chain-one , A.first-piece

  chain-le : StepChain → (n : ℕ) → V.val B.zero (T.Source.chain n) V.≼ V.val B.zero (A.Target.chain n)
  chain-le s zero    = V.z≼
  chain-le s (suc n) = proj₁ (s n (chain-le s n))

  out-le : StepChain → (n : ℕ) → V.val B.zero (proj₁ (T.Source.out (T.Source.chain n)))
    V.≼ V.val B.zero (proj₁ (A.Target.out (A.Target.chain n)))
  out-le s n = proj₂ (s n (chain-le s n))

  cum-le : StepChain → (n : ℕ) → V.val B.zero (T.source-cum n) V.≼ V.val B.zero (A.target-cum n)
  cum-le s zero    = out-le s zero
  cum-le s (suc n) = V.≼-trans (proj₁ (V.val-+ (T.source-cum n) _))
    (V.≼-trans (V.⊹-monoˡ (cum-le s n) _)
      (V.≼-trans (V.⊹-mono (V.val B.zero (A.target-cum n)) (out-le s (suc n)))
        (proj₂ (V.val-+ (A.target-cum n) _))))

  cover : StepChain → A.Cover
  cover s n = n , cum-le s n

  advance : StepChain → (n : ℕ) → C.ChainAdvance n
  advance s n _ = suc n , chain-le s (suc n)
```

# 首链点与现主线的对应
验收文件，读记号依赖仅从已核验的主线实例导入；不重新验收上一批的数学结论。
编译目标为本路规范底、feed 与任一有限链点同主线的相等，避免把另造的链当作实际链。
来源：YiFOBase 的定义等式，有限迭代按自然数归纳；不使用函数外延。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFOCorrespond where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiFOBase as FO

base-same : ∀ n i u → FO.base n i u ≡ GI.baseᴱ n i u
base-same zero i u = refl
base-same (suc n) i u = refl
feed-same : ∀ n c → FO.Run.feed n c ≡ FR.Step.feed n c
feed-same n c = FO.Run.feed-eq n c
chain-same : ∀ n q → FO.Run.chain n q ≡ FR.Step.chain n q
chain-same n zero = refl
chain-same n (suc q) = trans (feed-same n (FO.Run.chain n q))
  (cong (FR.Step.feed n) (chain-same n q))
```

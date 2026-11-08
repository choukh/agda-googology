# 固定世界秩把全部原地板读成零值

**编译定理的范围：** 这里研究 `ThirdVal.Stage.rk`，不是 `Φ` 或 `TΛ`。
原各底地板与 `gtX` 的秩全为零值。这使旧读法中的局限具体化：
`rk-⊲` 的第一位置控制不能直接充当折叠输出的序数上界。
本篇不由零秩推出零折叠值，也不证明原闭项有任何具名上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.TLambdaAuditRank where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; l≤)
open import OCF.Lean.ThirdTw using (Sb; fl; gtX)
import OCF.Lean.ThirdVal as V
import OCF.Lean.ThirdLeg as L

module At (c₀ : Cd) (lc₀ : LgB c₀) where
  module W = L.W c₀ lc₀

  branch-zero : ∀ n (c : HB (Sb n)) →
    V.Stage.rk c₀ lc₀ (suc n) (gtX (Sb n) (fl n) c) ≤ᵛ hz
  branch-zero n hz = z≤
  branch-zero n (hs c) = branch-zero n c
  branch-zero n (hl f) = l≤ (λ k → branch-zero n (f k))
  branch-zero n (hΩ κ g) = branch-zero n (g (W.pkS n κ))

  floor-zero : ∀ n → V.Stage.rk c₀ lc₀ n (fl n) ≤ᵛ hz
  floor-zero zero = z≤
  floor-zero (suc n) = branch-zero n (W.bnd n)
```

后继分量地板是 Ω 节点，固定组件槽取 `pkT=0`，于是其 `up 0` 分支
在秩中成为零；所以 `gtX` 的后继累加没有增加秩。极限只留下零值的
极限，指标旧种类递归到其原代表坐标。这解释了证明的全部子句，
不需要有限截断、FGH 测试或关于高层值的假定。

## 秩本身不是原实际下降输出的值上界

下例取原第一站完整 `TN`，不另造输入。仅用于精确否定“把 rk 的值
直接当下降值上界”这一字段，不否定任何用 rk 加额外闭包运算的估计。

```agda
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import OCF.Lean.Fold1If using (≤l; s≤s)
open import OCF.Lean.NegFold1Base using (≤ᵛ-trans)
import OCF.Lean.ThirdTm as T

one : Cd
one = hs hz

actual-positive : one ≤ᵛ T.Cn.TN one tt zero
actual-positive = ≤l 0 (≤l 0 (s≤s z≤))

no-rank-upper : ¬ (T.Cn.TN one tt zero ≤ᵛ V.Stage.rk one tt 1 (fl 1))
no-rank-upper p = impossible (≤ᵛ-trans actual-positive (≤ᵛ-trans p (At.floor-zero one tt 1)))
  where
  impossible : ¬ (one ≤ᵛ hz)
  impossible ()
```

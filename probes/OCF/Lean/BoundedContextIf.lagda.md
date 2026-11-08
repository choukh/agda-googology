# 有共同最大分量的上下文接口

本接口只处理已经给出字面公共界 B 的分量族。它不提供全地板、
改变 B 的折叠、或任意分支的统一有限支撑。世界将由共同目标分量拉回，
不是先给任意积世界再要求所有证明拷贝相干。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedContextIf where

open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLeg using (Ctx)

record Bounded (k : LH) (w : Wd (Lv k))
               (g : HB (Lv k) → LH) (B : HB (Lv k)) : Set₁ where
  field
    context : ∀ c → c ⊲[ w ] B → Ctx (Lv (g B)) (Lv (g c))
```

此字段没有比较两个裸坐标，只有带共同 B 的成员到目标的上下文。
前提可满足性由 BoundedContextRun 的实际 `prefix ⊕L upL k c` 族给出。
上下文不是层号值比较：它明确提供种类嵌入、坐标往返与世界投影。

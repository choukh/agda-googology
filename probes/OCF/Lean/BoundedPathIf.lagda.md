# 保留种类的路径接口

ClP 是跨层路径证明的充分接口，不是原始 LgB 定理的逻辑必要条件。
本篇复用 ThirdPS 的真实 Ev/Ad/nx；不把路径世界和 KS 世界混为一谈。
源目标路径共享世界序，源种类通过指定 Ctx 保留到目标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedPathIf where
open import Data.Product using (Σ)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecLeg using (Ctx; ek; frC)
open import OCF.Lean.ThirdPS using (Po; PS)

record Keep {O : Po} {S T : KS} (c : Ctx T S)
  (source : PS O S) (target : PS O T) : Set₁ where
  field
    event : ∀ {V κ} → PS.Ev source V κ → PS.Ev target V (ek c κ)
    admission : ∀ V κ e → PS.Ad target V (ek c κ) e → PS.Ad source V κ (frC c κ e)
    next : ∀ V κ e (a : PS.Ad target V (ek c κ) e) →
      Po._≤_ O (PS.nx source V κ (frC c κ e) (admission V κ e a))
        (PS.nx target V (ek c κ) e a)
```

next 的字面公共上界是目标进入后的世界；admission 未比较两个裸坐标。
源/目标路径结构的实例必须给出，不能用 triv 代替实际内层指标的移动。
KS 的世界投影由同一个 Ctx.pw 和 BoundedFoldWorld.ext 另行连接。

# YiXVReadPhiPaths
> 验收文件。档位：编译定理。同一实际目标和公共根内，不同弱路径上的输出作辅助比较。
> 从 SourceWorld*/ReadAffineLift 推广，树、原折叠与 UR 未改；未交自然极限跨分支和节点的完整世界输出、原 n=2 读回界或 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadPhiPaths where
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadWorldInput as W
change : ∀ {root y} (p q : y P.≤ᵀ root) {X} → A.Gd X → A.Le (W.φ p X) (W.φ q X)
change {y = y} p q gx = A.Layer.pack (W.φ-good p gx) (W.φ-good q gx)
  (A.Layer.ce (L.ψ-≅ {p = W.pc p} {σ = λ r → L.suc r} {p′ = W.pc q} {σ′ = λ r → L.suc r}
    (L.≅ᴵ-refl (T.lvl y)) (A.self gx)))
```

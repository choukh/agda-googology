# 新干净闭项的完整ψ₀(Ω₂)下界

验收专用。闭项、完成合法性和树上FGH全部来自不导入记号的
GeneralOmegaOneObserveIf；本篇只增加大小证明，不修改其任何定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaFiniteTypedObserveActual where
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Lean.Fold1Base using (≤-trans)
import OCF.Lean.GeneralOmegaOneObserveIf as O
import OCF.Align.Level as L
import OCF.Align.OCFSpecBase as V
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.GeneralOmegaGammaCoverFinite as F
open import OCF.Align.GeneralOmegaFiniteTypedRun using (orbit)
open import OCF.Align.GeneralOmegaFiniteTypedObserveRun using (observe)

whole : L.ψ⁰ (L.Ω (L.suc (L.suc L.zero))) L.≅ B.read O.raw
whole = L.l≅ (λ n → observe (orbit n))

reference≤raw : F.finite 2 ≤ᵛ O.raw
reference≤raw = B.reference-lower-reflect (V.≅→≼ whole)
raw≤reference : O.raw ≤ᵛ F.finite 2
raw≤reference = ≤-trans (B.roundtrip≥ O.raw)
  (B.forget-mono (V.≅→≼ (L.≅-sym whole)))

reference≤tree : F.finite 2 ≤ᵛ O.tree
reference≤tree = ≤-trans reference≤raw O.raw-lower
```

已证：原raw与ψ₀(Ω₂)参照互相≤ᵛ；原合法完成闭项tree不低于该参照。
尚未证明tree的反向上界，不把完成天然当作保值。这里是完整反馈轨道
及整个输出极限的比较，不是只选一个低回调，也不是含记号观察器的新命名。

翻译账：新单Ω观察规则受旧typed规则启发，种子1、无累加反馈、
后继从0份起均是明确的选择。验收未要求反改定义；定义与证书没有
记号依赖，但仍不宣称树自足。该结果既不是γ₂整族下界，也不是EBO
终点验收；与旧全Ω候选、C、D的相互比较仍待独立证明。

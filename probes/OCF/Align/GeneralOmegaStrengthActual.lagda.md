# 原闭项的整闭包迭代下界与现有标签锚点

验收专用。EBO第二站的实际family只在第0项接入；从这一已标注ε₀的
树再迭代Close所得的新整族，不冒充family的其它项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaStrengthActual where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-trans)
open import OCF.Align.GeneralOmegaStrengthIf
open import OCF.Align.GeneralOmegaStrengthRun
open import OCF.Align.GeneralOmegaIndexOperationalActual using (stage)
import OCF.Align.GeneralOmegaConsumeValueClosed as Old
import OCF.Align.BoundedCompletionStageFamily as Stage
import OCF.Lean.GeneralOmegaConsumeClosed as Closed

reference≤raw : reference ≤ᵛ Closed.raw
reference≤raw = l≤ (λ n → ≤l n (iteration n))
reference≤closed : reference ≤ᵛ Closed.tree
reference≤closed = ≤-trans reference≤raw Closed.raw-lower

anchored : ℕ → Cd
anchored zero = Stage.family zero
anchored (suc n) = Close (anchored n)
anchored≤stage : ∀ n → anchored n ≤ᵛ stage (suc n)
anchored≤stage zero = ≤-trans Stage.first≤old Old.first
anchored≤stage (suc n) = ≤-trans (close-mono (anchored≤stage n)) (stage-close (suc n))
anchored-limit≤raw : hl anchored ≤ᵛ Closed.raw
anchored-limit≤raw = l≤ (λ n → ≤l (suc n) (anchored≤stage n))
anchored-limit≤closed : hl anchored ≤ᵛ Closed.tree
anchored-limit≤closed = ≤-trans anchored-limit≤raw Closed.raw-lower
```

Stage.family zero具有已有Lab锚点ψ₀(Ω₁)。anchored其余项的确切记号
值尚未校准，以上不是ψ₀(Ω_{Ω₁})下界。真实EBO第二站下一步使用
ψ⁰(Ω(toLevel γn))，而这里Close仅以Cd基值作P反馈；两者间仍缺值桥。
没有从本下界推断原算法的上界或关闭其达到EBO的路线。

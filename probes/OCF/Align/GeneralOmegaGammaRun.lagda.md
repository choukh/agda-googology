# γ提升接口的真实非空实例

t=1的参照是ψ₀(Ω₁)。证明先比较整个旧TΩ1纯轨道，再经已证生成树
的实际up输出桥进入原后继层；不使用任意Same输入的run同余。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaGammaRun where
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤s; ≤l; l≤)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.FrozenWorldLift using (same-value)
open import OCF.Lean.LHRecTy using (lz; ls)
open import OCF.Lean.LHRecFl using (flL)
open import OCF.Lean.HigherIndexConsumeCode using (pure)
open import OCF.Lean.HigherIndexConsumePositive using (old-act; mul-partial)
open import OCF.Lean.HigherIndexConsumeLowest using (old-compare)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Align.GeneralOmegaConsumeValuePure using (Pure; pz; ps; pl; positive)
import OCF.Lean.HigherIndexConsumeDiagonal as Diagonal
import OCF.Lean.GeneralOmegaConsumeLayerRun as Layer
import OCF.Lean.GeneralOmegaEmbedGenerated as Generated
import OCF.Lean.Fold1 as Old
import OCF.Align.BoundedCompletionStageFamily as Stage
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaGammaIf

pure-only : ∀ x {d a} → Pure d a → old-act d ≤ᵛ run x a
pure-only x pz = positive x hz
pure-only x (ps p) = l≤ (λ n → ≤l n (mul-partial (pure-only x p) n))
pure-only x (pl p) = l≤ (λ n → ≤l n (pure-only x (p n)))
encoded : Cd → HB (step S⊥)
encoded d = up (hz ⊞ pure S⊥ d)
encoded-pure : ∀ d → Pure d (encoded d)
encoded-pure hz = pz
encoded-pure (hs d) = ps (encoded-pure d)
encoded-pure (hl f) = pl (λ n → encoded-pure (f n))
H : Cd → Cd
H d = run (ls lz) (encoded (leg d))
action : ∀ d → old-act d ≤ᵛ H d
action d = ≤-trans (old-compare (tt , hz) (inflation d))
  (pure-only (ls lz) (encoded-pure (leg d)))
old≤first-floor : Old.TΩ1 ≤ᵛ run (ls lz) (flL (ls lz))
old≤first-floor = Diagonal.Cover.whole H action

one-lower : reference (L.suc L.zero) (L.hs L.hz) ≤ᵛ candidate (L.suc L.zero)
one-lower = ≤-trans Stage.first≤old (≤-trans old≤first-floor
  (≤-trans (same-value Generated.first-tower-up)
    (≤-trans (≤s (≤-refl _)) (Layer.strict-step (ls lz)))))
instance-one : Comparison (L.suc L.zero) (L.hs L.hz)
instance-one = record { lower = one-lower }
```

这里不是γ₂比较，亦未证明同源Comparison对所有t成立。实例只说明
接口确有非零可满足对象，并明确比较完整原轨道而非有限基本列样本。

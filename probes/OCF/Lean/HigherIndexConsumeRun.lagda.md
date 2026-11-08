# 原完整高层源的总可数回灌

全部Ω使用同一个对角规则；没有keep或raw坐标补证。每次递归仍只
调用原源子树，Coord编码负责给出真实可入证书，世界按原next更新。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeRun where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.CRw as C
open import OCF.Lean.LHRecFl using (flL)
import OCF.Lean.LHRecLeg as L
open import OCF.Lean.LHRecIf using (LHRecIf)
open import OCF.Lean.BoundedFoldRun using (diagonal)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.HigherIndexClassIf using (U)
open import OCF.Lean.HigherIndexFoldIf using (k; Source)
open import OCF.Lean.HigherIndexSupportIf using (next)
open import OCF.Lean.HigherIndexSupportSource using (Supported)
open import OCF.Lean.HigherIndexConsumeIf
open import OCF.Lean.HigherIndexConsumeCode using (code; legal-next; pure)

high-coordinate : HB U → Cd → HB U
high-coordinate B d = B ⊞ L.leg k (flL k ⊞ pure U (C.leg d))

run : ∀ β → LgB β → ∀ B → LgB B → ∀ a → Supported β B a → Cd
run β lb B lB hz p = hs hz
run β lb B lB (hs a) p = Ops.repeat S⊥ (run β lb B lB a p)
run β lb B lB (hl f) p = hl (λ n → run β lb B lB (f n) (p n))
run β lb B lB (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) p
run β lb B lB (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) p = diagonal branch branch
  where
  branch : Cd → Cd
  branch d = run (hs e) le B lB (f e) (p e (⊞-fst β (C.leg d)) le)
    where
    e = β ⊞ C.leg d
    le : LgB e
    le = Lg-⊞ β (C.leg d) lb (C.Lg-leg d)
run β lb B lB (hΩ (inj₁ _ , inj₂ _) f) p = diagonal branch branch
  where
  branch : Cd → Cd
  branch d = run β lb (hs e) le (f e) (p e ad)
    where
    e = high-coordinate B d
    le : LgB e
    le = Lg-⊞ B _ lB (L.Lg-leg k (flL k ⊞ pure U (C.leg d)))
    ad = LHRecIf.adm-sh L.J₁ k {W = (tt , β) , B} (flL k ⊞ pure U (C.leg d)) ((tt , lb) , lB)
run β lb B lB (hΩ (inj₂ c , κ) f) (ev , p) = diagonal branch branch
  where
  branch : Cd → Cd
  branch d = run (next c κ β e ad) (legal-next c κ β lb e ad) B lB (f e) (p e ad)
    where
    encoded = code c κ β lb d
    e = proj₁ encoded
    ad = proj₂ encoded

instance-consumer : Consumer
instance-consumer = record { run = run }
```

high-coordinate在源最高指标反馈中显式包含原flL U（含Ω）。这没有
声称回灌保持旧typed fold值；新算法的值界须针对本run另证。

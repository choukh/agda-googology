# 原消费者的实际首输出跟踪

状态只打包原run参数；probe选择原对角的首坐标1时给原值下界。
本篇不改算法，也不把任意probe d声称为原链中的点。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexConsumeTrace where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
import OCF.Lean.CRw as C
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl)
open import OCF.Lean.LHRecFl using (flL)
import OCF.Lean.LHRecLeg as L
open import OCF.Lean.LHRecIf using (LHRecIf)
open import OCF.Lean.HigherIndexClassIf using (U)
open import OCF.Lean.HigherIndexFoldIf using (k; Source)
open import OCF.Lean.HigherIndexSupportIf using (next)
import OCF.Lean.HigherIndexSupportSource as S
open import OCF.Lean.HigherIndexConsumeCode using (code; legal-next; pure)
open import OCF.Lean.HigherIndexConsumeRun using (run; high-coordinate)

record State : Set where
  constructor state
  field
    β : Cd
    lb : LgB β
    B : HB U
    lB : LgB B
    tree : HB Source
    support : S.Supported β B tree
open State
result : State → Cd
result (state β lb B lB a p) = run β lb B lB a p
probe : Cd → State → State
probe d s@(state β lb B lB hz p) = s
probe d (state β lb B lB (hs a) p) = state β lb B lB a p
probe d (state β lb B lB (hl f) p) = state β lb B lB (f 0) (p 0)
probe d (state β lb B lB (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) p)
probe d (state β lb B lB (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) p) =
  state (hs e) le B lB (f e) (p e (⊞-fst β (C.leg d)) le)
  where
  e = β ⊞ C.leg d
  le : LgB e
  le = Lg-⊞ β (C.leg d) lb (C.Lg-leg d)
probe d (state β lb B lB (hΩ (inj₁ _ , inj₂ _) f) p) =
  state β lb (hs e) le (f e) (p e ad)
  where
  e = high-coordinate B d
  le : LgB e
  le = Lg-⊞ B _ lB (L.Lg-leg k (flL k ⊞ pure U (C.leg d)))
  ad = LHRecIf.adm-sh L.J₁ k {W = (tt , β) , B} (flL k ⊞ pure U (C.leg d)) ((tt , lb) , lB)
probe d (state β lb B lB (hΩ (inj₂ c , κ) f) (ev , p)) =
  state (next c κ β e ad) (legal-next c κ β lb e ad) B lB (f e) (p e ad)
  where
  enc = code c κ β lb d
  e = proj₁ enc
  ad = proj₂ enc

advance : State → State
advance = probe (hs hz)
advance-lower : ∀ s → result (advance s) ≤ᵛ result s
advance-lower (state β lb B lB hz p) = ≤-refl _
advance-lower (state β lb B lB (hs a) p) = ≤l 0 (≤-refl _)
advance-lower (state β lb B lB (hl f) p) = ≤l 0 (≤-refl _)
advance-lower (state β lb B lB (hΩ (inj₁ _ , inj₁ (inj₁ ())) f) p)
advance-lower (state β lb B lB (hΩ (inj₁ _ , inj₁ (inj₂ _)) f) p) = ≤l 0 (≤-refl _)
advance-lower (state β lb B lB (hΩ (inj₁ _ , inj₂ _) f) p) = ≤l 0 (≤-refl _)
advance-lower (state β lb B lB (hΩ (inj₂ c , κ) f) p) = ≤l 0 (≤-refl _)

initial : State
initial = state hz tt hz tt S.input (S.input-supported hz hz)
third : State
third = advance (advance (advance initial))

data IsOmega : HB Source → Set where
  is-omega : ∀ {κ f} → IsOmega (hΩ κ f)
record Node : Set where
  constructor node
  field
    nβ : Cd
    nlb : LgB nβ
    nB : HB U
    nlB : LgB nB
    kind : K Source
    branch : E Source kind → HB Source
    cert : S.Supported nβ nB (hΩ kind branch)
open Node public
focus : (s : State) → IsOmega (tree s) → Node
focus (state β lb B lB (hΩ κ f) p) is-omega = node β lb B lB κ f p
third-node : Node
third-node = focus third is-omega
```

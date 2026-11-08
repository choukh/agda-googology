# EBO第二站的实际整族值验收目标

验收专用，读取已有记号标签。第二站的目标为ψ₀(Ω_{Ω₁})；它的参照
使用已编译的NoCumsum.BTBOᴵ，而不是重新从良基证据展开大树。
整族为其真实基本列γ(n+1)，首项就是本轮已校准的ε₀。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionStageFamily where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase using (Cd; hl)
open import OCF.Lean.Fold1If using (_≤ᵛ_; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
import OCF.Lean.Fold1 as Old
import OCF.Align.Level as L
import OCF.Align.EBO as E
import OCF.Align.NoCumsum as N
import OCF.Align.Label as Labels
import OCF.Align.Correspond as Correspond
import OCF.Align.OCFSpecBase as S
import OCF.Align.Value as V
import OCF.Align.LambdaOrderBridge as Order
import OCF.Align.LambdaCountableBridge as B
import OCF.Align.BoundedCompletionCalibrateAccept as A
import OCF.Align.BoundedNativeCompletionClosed as C

open import OCF.Align.BoundedCompletionStageCore public

first≤old : family zero ≤ᵛ Old.TΩ1
first≤old = A.epsilon≤A
old≤first : Old.TΩ1 ≤ᵛ family zero
old≤first = ≤-trans (B.roundtrip≥ Old.TΩ1) (B.forget-mono A.A≤reference)
first≤completed : family zero ≤ᵛ C.tree
first≤completed = ≤-trans first≤old
  (≤-trans (OCF.Lean.Fold1If.≤s (≤-refl Old.TΩ1)) C.strict-old-lower)

```

核心整族及第二站标签由StageCore重导出；本篇额外把真实首项接到原C。
仍未填全族≤C，不能据此宣称第二站或EBO下界。

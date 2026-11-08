# 新运行保留原链行的完整零分量

仅使用原 D-val 的参数零结论；不外推非零相对算子。链的第 i+1 项
仍是原 stepL，先用 ΩI≡ 对齐原族，再由真实 run 的同形相容与累计
右包含取得整个分量。原第0项与累计前缀没有被删掉。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueBuildHighChain (S : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (_≅ᶻ_; toZ-≅)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.ValLabLadder S using (e₀; ev₀; D-val)
open import OCF.Align.TotalValueTailCongruence using (read-run-cong)
open import OCF.Align.TotalValuePureLower using (part)
open import OCF.Align.ValueJudgeBase
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

value : Ht → Ordᶜ zero
value m = A.read (R.run (toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ m zero) ev₀ zero)))

component : ∀ m F (qq : ∀ i → F i <ᴸ m) →
  view m ≡ chain F qq → ∀ i → value (F i) ≼ value m
component m F qq ve i = subst
  (λ x → value (F i) ≼ A.read (R.run (toZ (ψ̄ᵠ ok₀ e₀ x ev₀ zero))))
  (sym eq)
  (≼l (suc i) (≼-trans
    (≅→≼ (read-run-cong (d (ΩI m (qq i)) (ΩI≡ (qq i)))))
    (part branches (suc i))))
  where
  eq : Ω̇ m zero ≡ ql (rowL F qq (λ i → ΩI m (qq i)))
  eq = cong (rowV m (ΩI m)) ve

  branches : ℕ → Ordᴵ
  branches n = R.run (toZ (ψ̄ᵠ ok₀ e₀
    (rowL F qq (λ j → ΩI m (qq j)) n) ev₀ zero))

  d : ∀ (X : XΩ (F i)) → X ≡ Ω̇ (F i) →
    toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ (F i) zero) ev₀ zero) ≅ᶻ
    toZ (ψ̄ᵠ ok₀ e₀ (stepL (qq i) X) ev₀ zero)
  d _ refl = toZ-≅ (D-val (qq i) ok₀
    (λ j h r → κ-cap (F i) (λ _ → tt) j (ok₀ j))
    ev₀ zero ev₀ zero z≅)
```

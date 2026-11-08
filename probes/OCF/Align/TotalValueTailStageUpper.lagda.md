# 允许错位的两次实际折叠上界

源参数只带明确的 SV、Pos 和读回值界。两次累计提升分别消耗一次
额外旧阶段；不从裸值界反推原层号的前驱包含。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailStageUpper where
open import Data.Nat using (ℕ; suc)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZUniform using (Uniform)
open import OCF.Align.TotalValueBuildStrict using (SV; Pos; SV-L; St-F; SV-toLevel; module N)
open import OCF.Align.TotalValueBuildTypedEmbedding using (bounded-ψ)
open import OCF.Align.ValueJudgeBase
import OCF.Align.TotalValueCumulativeLift as Lift
import OCF.Free.TotalOrbitBuild as A

read-level : ∀ (a : Ordᶜ zero) h → A.read (toLevel a h) ≅ a
read-level zero h = z≅
read-level (suc a) h = s≅ (read-level a (hs⁻ h))
read-level (lim f) h = l≅ (λ n → read-level (f n) (hl₁ h n))
read-level (limᵢ () f) h
read-level (up () x) h

once : ∀ a → SV a → ∀ n → A.read a ≼ N.γ n →
  ψ⁰ (Ω a) ≼ N.γ (suc (suc n))
once a sa n p = bounded-ψ (Lift.lift a (N.L n) sa (SV-L n) (Uniform (N.L n))
  (≼-trans p (≅→≼ (≅-sym (read-level (N.γ n) (N.cert n))))))

twice : ∀ a → SV a → Pos a → ∀ n → A.read a ≼ N.γ n →
  ψ⁰ (Ω (toLevel (ψ⁰ (Ω a)) (Uniform a))) ≼ N.γ (suc (suc (suc (suc n))))
twice a sa pa n p = once (toLevel (ψ⁰ (Ω a)) (Uniform a))
  (SV-toLevel _ (Uniform a) (St-F sa pa)) (suc (suc n))
  (≼-trans (≅→≼ (read-level (ψ⁰ (Ω a)) (Uniform a))) (once a sa n p))
```

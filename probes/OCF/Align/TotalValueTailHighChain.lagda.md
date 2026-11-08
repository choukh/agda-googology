# 原高行的完整累计形状，不删首项

把原链行的每个低行读取还原成同一个新运行器的低行输出。这里是
整个累计树的同形，而不只是选一个分量的下界。首项逐字保留原𝟏L
经 ψ̄ 后的实际输出；𝟏L 是输入名，不能把该输出误写成数值1。
本归约不比较旧force与新run，后者仍需独立的非零参数高行控制。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailHighChain (S : HtB) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Free.Level
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Eq using (_≅ᶻ_; toZ-≅)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.ValLabLadder S using (e₀; ev₀; D-val)
open import OCF.Align.TotalValueTailCongruence using (run-cong; complete-cong)
import OCF.Free.TotalOrbitRun as R

native : Ht → Ordᴵ
native m = R.run (toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ m zero) ev₀ zero))
head : Ordᴵ
head = R.run (toZ (ψ̄ᵠ ok₀ e₀ (𝟏L {m = h₀}) ev₀ zero))
seq : (ℕ → Ordᴵ) → ℕ → Ordᴵ
seq f zero = head
seq f (suc n) = f n

chain-shape : ∀ m F (qq : ∀ i → F i <ᴸ m) →
  view m ≡ chain F qq → native m ≅ᴵ R.complete (seq (λ i → native (F i)))
chain-shape m F qq ve = subst
  (λ x → R.run (toZ (ψ̄ᵠ ok₀ e₀ x ev₀ zero)) ≅ᴵ
    R.complete (seq (λ i → native (F i)))) (sym eq)
  (complete-cong branches)
  where
  eq : Ω̇ m zero ≡ ql (rowL F qq (λ i → ΩI m (qq i)))
  eq = cong (rowV m (ΩI m)) ve
  d : ∀ i (X : XΩ (F i)) → X ≡ Ω̇ (F i) →
    toZ (ψ̄ᵠ ok₀ e₀ (Ω̇ (F i) zero) ev₀ zero) ≅ᶻ
    toZ (ψ̄ᵠ ok₀ e₀ (stepL (qq i) X) ev₀ zero)
  d i _ refl = toZ-≅ (D-val (qq i) ok₀
    (λ j h r → κ-cap (F i) (λ _ → tt) j (ok₀ j))
    ev₀ zero ev₀ zero z≅)
  branches : ∀ n →
    R.run (toZ (ψ̄ᵠ ok₀ e₀ (rowL F qq (λ i → ΩI m (qq i)) n) ev₀ zero)) ≅ᴵ
    seq (λ i → native (F i)) n
  branches zero = ≅ᴵ-refl _
  branches (suc i) = ≅ᴵ-sym (run-cong (d i (ΩI m (qq i)) (ΩI≡ (qq i))))
```

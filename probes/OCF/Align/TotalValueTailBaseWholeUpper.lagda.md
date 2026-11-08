# 原 base 完整反馈与全部部分和的上界

预算只重编号旧 NC 参照的阶段，不更改原 seed、坐标、界证明或输出。
所有坐标和完整累计输出均由原 ActualTrace 读取。最终目标是原 BTBO
参照；本篇不将这一基座上界自动送到最高端行。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueTailBaseWholeUpper (S : HtB) where
open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n; m≤n+m)
open import Data.Product using (proj₂)
open import OCF.Align.OrdLabZLevel
open import OCF.Free.Prefix using (toZ)
open import OCF.Free.Floor using (Ev; iF)
open import OCF.Free.Tree using (Fl)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueBuildStrict using (svz; svs; ps; module N)
open import OCF.Align.TotalValueBuildTypedValue using (1≼ψ⁰; add-mono-value)
open import OCF.Align.TotalValueTailBaseAbsorb S using (omega-upper-absorbed)
open import OCF.Align.TotalValueTailStageUpper using (twice)
open import OCF.Align.TotalValueTailPureUpper using (read-add)
open import OCF.Align.TotalValueNegBound using (bound-one)
open import OCF.Align.TotalValueTraceShape using (equality-shape)
import OCF.Align.TotalValueBuildBaseOrbit S as Orbit
import OCF.Align.OrdLabZNoCumsum as NC
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

module From
  (double : ∀ n → (N.γ n + N.γ n) ≼ N.γ (suc (suc n)))
  (monotone : ∀ n → N.γ n ≼ N.γ (suc n)) where
  grow : ∀ {n k} → n ≤′ k → N.γ n ≼ N.γ k
  grow ≤′-refl = ≼-refl _
  grow (≤′-step p) = ≼-trans (grow p) (monotone _)
  up2 : ∀ n → N.γ n ≼ N.γ (suc (suc n))
  up2 n = ≼-trans (monotone n) (monotone (suc n))
  positive : ∀ n → suc (zero {ℓ = zero}) ≼ N.γ n
  positive zero = ≼-refl _
  positive (suc n) = 1≼ψ⁰ (Ω (N.L n))
  four : ℕ → ℕ
  four n = suc (suc (suc (suc n)))
  six : ℕ → ℕ
  six n = suc (suc (four n))
  index : ℕ → ℕ
  index zero = four zero
  index (suc n) = six (index n)
  join : ℕ → ℕ → ℕ
  join a b = suc (suc (a +ᴺ b))
  mixed : ∀ a b → (N.γ a + N.γ b) ≼ N.γ (join a b)
  mixed a b = ≼-trans (add-mono-value
    (grow (≤⇒≤′ (m≤m+n a b))) (grow (≤⇒≤′ (m≤n+m b a))))
    (double (a +ᴺ b))
  budget : ℕ → ℕ
  budget zero = index zero
  budget (suc n) = join (budget n) (index (suc n))

  module Actual {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
    (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) where
    module B = Orbit.Actual ok env ev p
    c-one : A.read B.c ≅ suc (zero {ℓ = zero})
    c-one = A.read-cong (equality-shape (bound-one ev p))
    prefixed : ∀ a n → A.read a ≼ N.γ n → A.read (R.add B.c a) ≼ N.γ (suc (suc n))
    prefixed a n h = ≼-trans (≅→≼ (read-add B.c a))
      (≼-trans (add-mono-value (≼-trans (≅→≼ c-one) (positive n)) h) (double n))
    seed-upper : A.read (R.run (toZ B.seed)) ≼ N.γ (suc (suc zero))
    seed-upper = omega-upper-absorbed (svs svz) ps proj₂ ok env ev p

    coordinates : ∀ n → A.read (B.η n) ≼ N.γ (index n)
    coordinates zero = ≼-trans (≅→≼ (A.read-cong (equality-shape B.start)))
      (prefixed (R.run (toZ B.seed)) (suc (suc zero)) seed-upper)
    coordinates (suc n) = ≼-trans (≅→≼ (A.read-cong (equality-shape (B.step n))))
      (prefixed (R.run (toZ (B.next (B.η n) (B.bound n)))) (four (index n))
        (≼-trans (omega-upper-absorbed (B.coordinate-sv n) (B.coordinate-pos n)
          (λ v q → proj₂ v (suc q)) ok env
          (evη _ B.F (B.η n) (B.bound n)) (lim 0 (iF B.F)))
          (twice (B.η n) (B.coordinate-sv n) (B.coordinate-pos n) (index n) (coordinates n))))

    emitted : ∀ n → A.read (R.run (toZ (B.next (B.η n) (B.bound n)))) ≼ N.γ (four (index n))
    emitted n = ≼-trans (omega-upper-absorbed (B.coordinate-sv n) (B.coordinate-pos n)
      (λ v q → proj₂ v (suc q)) ok env
      (evη _ B.F (B.η n) (B.bound n)) (lim 0 (iF B.F)))
      (twice (B.η n) (B.coordinate-sv n) (B.coordinate-pos n) (index n) (coordinates n))
    outputs : ∀ n → A.read (B.Full.outputs n) ≼ N.γ (index n)
    outputs zero = ≼-trans seed-upper (up2 (suc (suc zero)))
    outputs (suc n) = ≼-trans (emitted n) (up2 (four (index n)))
    sums : ∀ n → A.read (R.sum B.Full.outputs n) ≼ N.γ (budget n)
    sums zero = outputs zero
    sums (suc n) = ≼-trans (≅→≼ (read-add (R.sum B.Full.outputs n) (B.Full.outputs (suc n))))
      (≼-trans (add-mono-value (sums n) (outputs (suc n))) (mixed (budget n) (index (suc n))))
    whole : A.read (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p))) ≼ NC.BTBOᴵ
    whole = ≼-trans (≅→≼ (A.read-cong B.Full.Actual.shape))
      (l≼ (λ n → ≼l (budget n) (≼-trans (sums n) (monotone (budget n)))))
```

旧参照算术在下段实填，所以 whole-upper 没有剩余局部合同参数。

```agda
import OCF.Align.TotalValueGammaBounds as G
module Filled = From G.double G.monotone

whole-upper : ∀ {m w ℓ} (ok : Ok w) (env : Eh h₀ m w (κ Fl))
  (ev : Ev ℓ Fl) (p : zero <ᴵ ℓ) →
  A.read (R.run (toZ (ψ̄ᵠ ok env (rowB {m = m}) ev p))) ≼ NC.BTBOᴵ
whole-upper = Filled.Actual.whole
```

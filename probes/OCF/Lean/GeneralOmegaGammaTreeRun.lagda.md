# 树侧一步变换在任意实际上下文中的完成稳定与输入界

证明对输入Cd结构统一进行。极限分支保留原ΣF和read组合，用原输出
的ω重复增长吸收累计；不从有向值关系推leg单调性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaGammaTreeRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Σ₀)
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (_⊕L_; upL)
open import OCF.Lean.LHRecFl using (flL; ΣF)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.TowerCollapseIf using (module Ops)
open import OCF.Lean.GeneralOmegaConsumeRun using (run)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.GeneralOmegaCompletionRun using (parts-mono)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.GeneralOmegaConsumeValuePure using (positive)
open import OCF.Align.GeneralOmegaIndexRaise
open import OCF.Align.GeneralOmegaIndexOperationalIf
import OCF.Align.GeneralOmegaIndexOperationalRun as O
import OCF.Lean.GeneralOmegaCompletionSeries as Series
open import OCF.Lean.GeneralOmegaGammaTreeIf

step-context : ∀ x → Context x (ls x)
step-context x = record { read = up ; kind = inj₁ ; pull = λ κ e → e ;
  r-s = λ a → refl ; r-l = λ f → refl ; r-Ω = λ κ f → refl ; back = λ κ d → refl }

module Limit (f : ℕ → Cd) (y : LH) (j : Context (level (hl f)) y) where
  layers : ℕ → LH
  layers n = level (f n)
  q : ℕ → Cd
  q n = run y (read j (ΣF layers n))
  component : ∀ n → Context (level (f n)) y
  component zero = compose j (sum layers zero)
  component (suc n) = compose j (compose (prefix (level (hl f)) (ΣF layers n)) (sum layers (suc n)))
  growth : ∀ n → Ops.repeat S⊥ (q n) ≤ᵛ q (suc n)
  growth n = O.Mapped.repeated j (ΣF layers n)
    (raises-ι (suc n) (floor-raises (plus-shape successor (upL lz (f (suc n))))))
  q-step : ∀ n → q n ≤ᵛ q (suc n)
  q-step n = ≤-trans (≤l 0 (≤-refl _)) (growth n)

stable : ∀ c y (j : Context (level c) y) →
  leg (run y (read j (flL (level c)))) ≤ᵛ run y (read j (flL (level c)))
stable hz y j = O.Next.stable lz y j
stable (hs c) y j = O.Next.stable (level c) y j
stable (hl f) y j rewrite r-l j (ΣF (λ n → level (f n))) = Series.Result.upper L.q stages
  where
  module L = Limit f y j
  each : ∀ n → leg (L.q n) ≤ᵛ L.q n
  each zero = stable (f zero) y (L.component zero)
  each (suc n) = stable (f (suc n)) y (L.component (suc n))
  stages : Series.Stages L.q
  stages = record { stable = each ; growth = L.growth }

successor-bound : ∀ x y (j : Context (ls x) y) {b} →
  b ≤ᵛ run y (read j (up (flL x))) → hs b ≤ᵛ run y (read j (flL (ls x)))
successor-bound x y j {b} p rewrite r-Ω j (inj₂ tt) up = ≤l 0 first
  where
  first : hs b ≤ᵛ O.Next.H x y j (hs hz)
  first rewrite back j (inj₂ tt) (hs hz) | r-s j (up (flL x)) =
    ≤-trans (s≤s p) (≤l 1 (add-mono (≤-refl _) (positive y (read j (up (flL x))))))

completed-input : ∀ c y (j : Context (level c) y) → leg c ≤ᵛ run y (read j (flL (level c)))
completed-input hz y j = z≤
completed-input (hs c) y j = successor-bound (level c) y j
  (completed-input c y (compose j (step-context (level c))))
completed-input (hl f) y j rewrite r-l j (ΣF (λ n → level (f n))) =
  l≤ (λ n → ≤l (suc n) (≤-trans (sums n) (≤-trans (≤l n (≤-refl _)) (L.growth n))))
  where
  module L = Limit f y j
  each : ∀ n → leg (f n) ≤ᵛ L.q n
  each zero = completed-input (f zero) y (L.component zero)
  each (suc n) = completed-input (f (suc n)) y (L.component (suc n))
  sums : ∀ n → Σ₀ (λ k → leg (f k)) n ≤ᵛ Ops.partial S⊥ (λ _ → L.q n) n
  sums zero = each zero
  sums (suc n) = add-mono (≤-trans (sums n) (parts-mono (λ _ → L.q-step n) n)) (each (suc n))

input : ∀ c y (j : Context (level c) y) → c ≤ᵛ run y (read j (flL (level c)))
input c y j = ≤-trans (inflation c) (completed-input c y j)
raw-stable : ∀ c → tree c ≤ᵛ raw c
raw-stable c = stable c (level c) (identity (level c))
raw-lower : ∀ c → raw c ≤ᵛ tree c
raw-lower c = inflation (raw c)
completed-input≤raw : ∀ c → leg c ≤ᵛ raw c
completed-input≤raw c = completed-input c (level c) (identity (level c))
input≤tree : ∀ c → c ≤ᵛ tree c
input≤tree c = ≤-trans (input c (level c) (identity (level c))) (raw-lower c)
```

tree对全部raw输入均合法，且与raw同值；原输入的完成树已被raw覆盖。
这些定理未比较记号ψ⁰(Ω(toLevel t))，不能将此变换命名为已验收的
γ一步。所有导入闭包另由工具核查无标签/记号命中。

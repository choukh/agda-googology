# 原完整可数高度反馈的合法迭代闭项

每步先将当前Cd树完成为合法高度，再观察该高度的整个累计地板。
Γ输出也完成，所以全部迭代项合法；最后整体ℕ树再次完成，合法性
不依赖未证的阶段步进。FGH只作用于最终合法布劳威尔树。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaCountableObserveClosed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.GeneralOmegaCountableObserveIf
open import OCF.Lean.GeneralOmegaCountableObserveClass using (floor-legal)
open import OCF.Lean.GeneralOmegaCountableObserveRun using (observe)
open import OCF.Lean.Fold1If using (_≤ᵛ_; s≤s; z≤; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Lean.CountableCompletionRun using (inflation)
import OCF.Lean.Fold1 as FGH

node-positive : ∀ {B A} (pt : hz ⊲ B) (v : C.Dc F B hz A)
  (rec : ∀ r → r ⊲ B → A → HB (F r)) →
  (∀ e → hs hz ≤ᵛ rec hz pt e) → hs hz ≤ᵛ node pt v rec
node-positive pt (C.keep () fr) rec positive
node-positive pt (C.same to) rec positive = ≤l zero (positive (to (floor hz)))
node-positive pt (C.above r pr tr to) rec positive = ≤l zero (positive (to (floor r)))
positive : ∀ B lB pt a → hs hz ≤ᵛ observe B lB hz pt a
positive B lB pt hz = s≤s z≤
positive B lB pt (hs a) = ≤l 1 (positive B lB pt a)
positive B lB pt (hl f) = ≤l zero (positive B lB pt (f zero))
positive B lB pt (hΩ κ f) = node-positive pt (classify B lB hz pt κ)
  (λ r pr e → observe B lB r pr (f e)) (λ e → positive B lB pt (f e))

rawΓ : Cd → Cd
rawΓ c = observe (leg c) (Lg-leg c) hz (z⊲ᴮ (leg c)) (floor (leg c))
Γ : Cd → Cd
Γ c = leg (rawΓ c)
Γ-legal : ∀ c → LgB (Γ c)
Γ-legal c = Lg-leg (rawΓ c)
Γ-input-legal : ∀ c → LgB (floor (leg c))
Γ-input-legal c = floor-legal (leg c)
Γ-positive : ∀ c → hs hz ≤ᵛ Γ c
Γ-positive c = ≤-trans (positive (leg c) (Lg-leg c) (z⊲ᴮ (leg c)) (floor (leg c))) (inflation (rawΓ c))

stage : ℕ → Cd
stage zero = hs hz
stage (suc n) = Γ (stage n)
stage-legal : ∀ n → LgB (stage n)
stage-legal zero = tt
stage-legal (suc n) = Γ-legal (stage n)
raw : Cd
raw = hl stage
tree : Cd
tree = leg raw
legal : LgB tree
legal = Lg-leg raw
raw-lower : raw ≤ᵛ tree
raw-lower = inflation raw
stage-lower : ∀ n → stage n ≤ᵛ tree
stage-lower n = ≤-trans (≤l n (≤-refl _)) raw-lower
tree-positive : hs hz ≤ᵛ tree
tree-positive = stage-lower zero
fgh : ℕ → ℕ
fgh = FGH.FGH tree
```

这交付实际总构造、合法闭项、所有阶段值包含及正性。没有声称Γ
保值单调、阶段严格增长、完成不抬值，或该闭项等于ψ₀Λ。真正的
γ提升值桥仍须比较原typed参照，不能由Γ名称或高度范围推断。

# 最后完成的无条件树形上界

不能把两次累计假设为幂等。这里给全部可数树上的显式上界：
leg a 不高于 unary a，后者在后继处加 ω 重复、极限处取累计。
此上界在原完整高闭项实填；尚不是具名 Ω 算术上界或完成保值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailUpper where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; _×_; _,_)
open import OCF.Lean.CRwBase
import OCF.Free.LiteralCompletion as C
open import OCF.Lean.DirectedPrefixIf using (unary; sums)
open import OCF.Lean.DirectedPrefixBuild using (positive; in-sums)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans; ⊞≤ˡ; ⊞≤ʳ)
import OCF.Align.RadicalValueNativeFinal as Final

sum-mono : ∀ (f g : ℕ → Cd) → (∀ n → f n ≤ᵛ g n) →
  ∀ n → C.Σ₀ f n ≤ᵛ sums g n
sum-mono f g p zero = p zero
sum-mono f g p (suc n) = ≤ᵛ-trans
  (⊞≤ˡ (f (suc n)) (sum-mono f g p n))
  (⊞≤ʳ (sums g n) (p (suc n)))

upper : ∀ a → C.leg a ≤ᵛ unary a
upper hz = z≤
upper (hs a) = ≤l (suc zero)
  (≤ᵛ-trans (s≤s (upper a)) (⊞≤ʳ (unary a) (positive a)))
upper (hl f) = l≤ (λ n → ≤l n
  (sum-mono (λ k → C.leg (f k)) (λ k → unary (f k)) (λ k → upper (f k)) n))
upper (hΩ () g)

right : ∀ (a b : Cd) → b ≤ᵛ (a ⊞ b)
right a hz = z≤
right a (hs b) = s≤s (right a b)
right a (hl f) = l≤ (λ n → ≤l n (right a (f n)))

item : ∀ (f : ℕ → Cd) n → f n ≤ᵛ C.Σ₀ f n
item f zero = ≤ᵛ-refl _
item f (suc n) = right _ _

lower : ∀ a → a ≤ᵛ C.leg a
lower hz = z≤
lower (hs a) = s≤s (lower a)
lower (hl f) = l≤ (λ n → ≤l n (≤ᵛ-trans (lower (f n)) (item _ n)))
lower (hΩ () g)

actual-bounds : (Final.raw ≤ᵛ proj₁ Final.closed) ×
  (proj₁ Final.closed ≤ᵛ unary Final.raw)
actual-bounds = lower Final.raw , upper Final.raw
```

actual-bounds 的参数就是原 HB ω² 端行全部新反馈后的输出，不取首分量。
它不能自动导出 final≤raw。若采用吸收策略，仍须针对实际源证明足够的
后续分量覆盖这些重复及内部前缀；既有 GeneralOmegaCompletionSeries
提供一套充分判据及另外真实闭包族的实例，但尚未实例化到这个源。
这里不将别的候选的吸收定理移用于本闭项。

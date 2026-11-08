# 以外部参照控制最后的第一位置完成

上界必须来自外部 y，不能只把 raw 再包一个 unary。当原 native
输出及 y 都有遗传严格性时，先用旧累计层比较，再由 V3 吸入
ψ⁰Ω(toLevel y)。不假设 leg 对一般值序单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailHighExternal where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase using (Cd; hz; hs; hl; hΩ; _⊞_)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueBuildTypedValue using (add-mono-value)
open import OCF.Align.TotalValueBuildStrict using (SV; SV-toLevel; St-≅)
open import OCF.Align.TotalValueBuildStrictBase using (St)
open import OCF.Align.TotalValueBuildReadStrict using (read-strictness)
open import OCF.Align.TotalValueTailPureUpper using (readD; readD-add)
open import OCF.Align.TotalValueTailAbsorb using (eb-sound)
open import OCF.Align.TotalValueTailStageUpper using (read-level)
open import OCF.Align.TotalValueCumulativeLift using (read-back)
import OCF.Align.TotalValueCumulativeAbsorb as V
import OCF.Align.TotalValueCumulativeEb as E
open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module O = Ord-Ord
module B = BoundedTrich
module D = E.Blocks E.𝕆
module T = E.Blocks V.𝕋₀
import OCF.Free.TotalOrbitBuild as A
import OCF.Free.LiteralCompletion as C
open import OCF.Align.RadicalValueNativeFinal using (forget)
import OCF.Align.RadicalValueNativeAccept as Read

read-cd-add : ∀ a b → Read.read (a ⊞ b) ≅ (Read.read a + Read.read b)
read-cd-add a hz = ≅-refl⁰ _
read-cd-add a (hs b) = s≅ (read-cd-add a b)
read-cd-add a (hl f) = l≅ (λ n → read-cd-add a (f n))
read-cd-add a (hΩ () g)

sum-upper : ∀ (f : ℕ → Cd) (g : ℕ → B.Ordᴰ) →
  (∀ n → Read.read (f n) ≼ readD (g n)) → ∀ n →
  Read.read (C.Σ₀ f n) ≼ readD (B.cumsum g n)
sum-upper f g p zero = p zero
sum-upper f g p (suc n) = ≼-trans (≅→≼ (read-cd-add (C.Σ₀ f n) (f (suc n))))
  (≼-trans (add-mono-value (sum-upper f g p n) (≼-suc (p (suc n))))
    (≅→≼ (≅-sym (readD-add (B.cumsum g n) (B.suc (g (suc n)))))))

completion-upper : ∀ a → Read.read (C.leg (forget a)) ≼ readD (O.ordᴰ (V.bkᴵ a))
completion-upper zero = z≼
completion-upper (suc a) = s≼s (completion-upper a)
completion-upper (lim f st) = l≼ (λ n → ≼l n
  (sum-upper (λ k → C.leg (forget (f k))) (λ k → O.ordᴰ (V.bkᴵ (f k)))
    (λ k → completion-upper (f k)) n))

compose : ∀ {a b y} → D.Eb a b → T.Eb b y → T.Eb a y
compose e d = record
  { map = λ p → T.map d (D.below e p)
  ; below = λ p → T.below d (D.below e p)
  ; mono = λ p q r → T.mono d (D.below e p) (D.below e q) (D.mono e p q r)
  ; coh = λ p q r → T.coh d (D.below e p) (D.below e q) (D.coh e p q r) }

external-upper : ∀ a → SV a → ∀ (y : Ordᶜ zero) (hy : HS y) → St y →
  A.read a ≼ y → Read.read (C.leg (forget a)) ≼ ψ⁰ (Ω (toLevel y hy))
external-upper a sa y hy sy v = ≼-trans (completion-upper a)
  (eb-sound _ (compose
    (E.V2 (V.bkᴵ a) (V.bkᴵ (toLevel y hy))
      (St-≅ (read-back a) (read-strictness sa))
      (St-≅ (≅-trans (read-back (toLevel y hy)) (read-level y hy)) sy)
      (≼-trans (≅→≼ (read-back a))
        (≼-trans v (≅→≼ (≅-sym (≅-trans (read-back (toLevel y hy)) (read-level y hy)))))))
    (V.V3 (SV-toLevel y hy sy))))
```

结论的三个实质前提是 SV a、HS/St y、原输出的外部值界。
它不从 HS 单独推出严格性，也不自动实例化到尚未控制的最高端行。
下一实例将使用已证明的完整原 rowB 与固定的旧 BTBO，而非选择 y=raw。

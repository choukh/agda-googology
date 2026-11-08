# 真实纯读取的累计上界

新 run 的部分和不额外添加后继，原 src ordᴰ 的部分和会添加。
这里沿完整异族读取证明比较两者，目标使用 V3 所需的原累计层，
而不是另一个 unary 估计。无需假设 run 保任意值序。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailPureUpper where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open import OCF.Align.OrdLabZLevel
open import OCF.Free.Prefix using (Ordˢ; toZ)
open import OCF.Align.OrdLabZPrefix using (_~_; z~; s~; l~; lᵢ~; upˡ; upʳ)
open import OCF.Align.ValueJudgeBase
open import OCF.Align.TotalValueBuildTypedValue using (add-mono-value)
open import OCF.Align.TotalValueCumulativeBase using (τ)
open import OCF.Align.TotalValueCumulativeAbsorb using (bkᴵ)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

readD : B.Ordᴰ → Ordᶜ zero
readD a = A.read (τ a)
read-add : ∀ a b → A.read (R.add a b) ≅ (A.read a + A.read b)
read-add a zero = ≅-refl⁰ _
read-add a (suc b) = s≅ (read-add a b)
read-add a (lim f st) = l≅ (λ n → read-add a (f n))
readD-add : ∀ a b → readD (B._+_ a b) ≅ (readD a + readD b)
readD-add a B.zero = ≅-refl⁰ _
readD-add a (B.suc b) = s≅ (readD-add a b)
readD-add a (B.lim f st) = l≅ (λ n → readD-add a (f n))

sums-upper : ∀ (f : ℕ → Ordᴵ) (g : ℕ → B.Ordᴰ) →
  (∀ n → A.read (f n) ≼ readD (g n)) → ∀ n →
  A.read (R.sum f n) ≼ readD (B.cumsum g n)
sums-upper f g p zero = p zero
sums-upper f g p (suc n) = ≼-trans (≅→≼ (read-add (R.sum f n) (f (suc n))))
  (≼-trans (add-mono-value (sums-upper f g p n) (≼-suc (p (suc n))))
    (≅→≼ (≅-sym (readD-add (B.cumsum g n) (B.suc (g (suc n)))))))

pure-upper : ∀ {x : Ordˢ zero} {y : Ordᶜ zero} (hy : HS y) → x ~ y →
  A.read (R.run (toZ x)) ≼ readD (S.ordᴰ (bkᴵ (toLevel y hy)))
pure-upper hy z~ = z≼
pure-upper hy (s~ p) = s≼s (pure-upper (hs⁻ hy) p)
pure-upper hy (l~ {f = f} {g = g} p) = l≼ (λ n → ≼l n
  (sums-upper (λ k → R.run (toZ (f k)))
    (λ k → S.ordᴰ (bkᴵ (toLevel (g k) (hl₁ hy k))))
    (λ k → pure-upper (hl₁ hy k) (p k)) n))
pure-upper hy (lᵢ~ {p = ()} e p)
pure-upper hy (upˡ {r = ()} p)
pure-upper hy (upʳ {r = ()} p)
```

# 第一位置完成的单向值验收

只证明未完成的 TotalOrbit 输出不高于最终完成树；不是旧高值验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.RadicalValueNativeAccept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)
import OCF.Free.Level as L
import OCF.Free.TotalOrbitBuild as A
import OCF.Align.TotalOrbitClosed as Source
import OCF.Align.ValueJudgeBase as V
open import OCF.Align.RadicalValueNativeFinal using (closed; raw; forget)
open import OCF.Align.LadderOrdPos using (end)
import OCF.Free.LiteralCompletion as C
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)

right-add : ∀ (a b : Cd) → b ≤ᵛ a ⊞ b
right-add a hz = z≤
right-add a (hs b) = s≤s (right-add a b)
right-add a (hl f) = l≤ (λ n → ≤l n (right-add a (f n)))

item-sum : ∀ (f : ℕ → Cd) n → f n ≤ᵛ C.Σ₀ f n
item-sum f zero = ≤-refl _
item-sum f (suc n) = right-add _ _

inflation : ∀ a → a ≤ᵛ C.leg a
inflation hz = z≤
inflation (hs a) = s≤s (inflation a)
inflation (hl f) = l≤ (λ n → ≤l n
  (≤-trans (inflation (f n)) (item-sum (λ k → C.leg (f k)) n)))

-- 以下仅作表示和值的验收；不参与 closed 的构造。
read : Cd → L.Ordᶜ L.zero
read hz = L.zero
read (hs a) = L.suc (read a)
read (hl f) = L.lim (λ n → read (f n))
read (hΩ () g)

read-lower : ∀ {a b} → a ≤ᵛ b → read a V.≼ read b
read-lower z≤ = V.z≼
read-lower (s≤s p) = V.s≼s (read-lower p)
read-lower (≤s p) = V.≼-suc (read-lower p)
read-lower (l≤ p) = V.l≼ (λ n → read-lower (p n))
read-lower (≤l n p) = V.≼l n (read-lower p)

forget-shape : ∀ a → A.read a L.≅ read (forget a)
forget-shape L.zero = L.z≅
forget-shape (L.suc a) = L.s≅ (forget-shape a)
forget-shape (L.lim f st) = L.l≅ (λ n → forget-shape (f n))

original-lower : Source.closed V.≼ read (proj₁ closed)
original-lower = V.≼-trans
  (V.≅→≼ (forget-shape (A.run (Source.High.raw end L.zero))))
  (read-lower (inflation raw))
```

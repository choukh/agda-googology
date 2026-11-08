# 原 typed 折叠的底层值工具

将 BTBOFullLe 消费的两个底层引理重基到当前 Free.Level 类型；
只作验收，不改任何折叠或坐标。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildTypedValue where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase
≼-+ʳ : ∀ (a b : Ordᶜ zero) → a ≼ a + b
≼-+ʳ a zero        = ≼-refl a
≼-+ʳ a (suc b)     = ≼-suc (≼-+ʳ a b)
≼-+ʳ a (lim f)     = ≼l 0 (≼-+ʳ a (f 0))
≼-+ʳ a (limᵢ () f)
≼-+ʳ a (up () x)

add-mono-value : ∀ {a a′ b b′ : Ordᶜ zero} → a ≼ a′ → b ≼ b′ → a + b ≼ a′ + b′
add-mono-value {a′ = a′} {b′ = b′} pa z≼ = ≼-trans pa (≼-+ʳ a′ b′)
add-mono-value pa (s≼s q)  = s≼s (add-mono-value pa q)
add-mono-value pa (≼l n q) = ≼l n (add-mono-value pa q)
add-mono-value pa (l≼ h)   = l≼ (λ n → add-mono-value pa (h n))
add-mono-value pa (≼i {p = ()} x ex q)
add-mono-value pa (i≼ {p = ()} h)
add-mono-value pa (≼u {r = ()} q)
add-mono-value pa (u≼ {r = ()} q)

iter-≼ : ∀ {A B : Ordᶜ zero} → A ≼ B → ∀ n → iter (A +_) zero n ≼ iter (B +_) zero n
iter-≼ e zero    = z≼
iter-≼ e (suc n) = add-mono-value e (iter-≼ e n)
1≼ψ⁰ : ∀ {k} (y : Ordᶜ k) → suc (zero {Ordᴵ.zero}) ≼ ψ⁰ y
1≼ψ⁰ zero = s≼s z≼
1≼ψ⁰ (suc y) = ≼l 1 (1≼ψ⁰ y)
1≼ψ⁰ (lim f) = ≼l 0 (1≼ψ⁰ (f 0))
1≼ψ⁰ (limᵢ q f) = ≼l 0 (1≼ψ⁰ (f (into (<→◃ q) (Ω _))))
1≼ψ⁰ (up zero y) = 1≼ψ⁰ y
1≼ψ⁰ (up (self n) y) = 1≼ψ⁰ y
```

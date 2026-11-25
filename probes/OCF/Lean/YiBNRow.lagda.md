# 一致目标槽位的结点行（原型）
编译定理：固定目标槽位、只取源第一分支的行对新第一位置单调，且非零性保持。
不用 `kp`、比较表或退路；不声称保留全部分支的值，也未给第 0 层折叠。
来源：`YiFWNode.through-step` 的一致目标形状；差别是换型恒取第一点，入口为 `row-step`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBNRow where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Lean.YiFWBlock

Positive : Sg → Set
Positive S = Σ (T S) (Lt S zero)

row : ∀ {S S′ : Sg} (q : P S′) (p : P S) → (B S p → T S′) → T S′
row {S} q p G = Ω q (λ _ → G (b₀ S p))

row-first : ∀ {S S′ : Sg} (q : P S′) (p : P S) (G : B S p → T S′)
  → Lt S′ (G (b₀ S p)) (row {S = S} {S′ = S′} q p G)
row-first q p G = ◃w

row-step : ∀ {S S′ : Sg} (q : P S′) {p p′ : P S} (e : E S p p′)
  (G : B S p → T S′) (G′ : B S p′ → T S′)
  → (∀ z → Lt S′ (G (cv S e z)) (G′ z))
  → Lt S′ (row {S = S} {S′ = S′} q p G) (row {S = S} {S′ = S′} q p′ G′)
row-step {S} {S′} q {p} {p′} e G G′ h = ◃σ (reflE S′ q) (λ _ →
  subst (λ z → Lt S′ (G z) (G′ (b₀ S p′))) (cv₀ S e) (h (b₀ S p′)))

row⁺ : ∀ {S S′ : Sg} (q : P S′) (p : P S) → (B S p → Positive S′) → Positive S′
row⁺ {S} {S′} q p G = row {S = S} {S′ = S′} q p (λ z → proj₁ (G z)) ,
  ◃t (proj₂ (G (b₀ S p))) ◃w
```

# 单字段生成域：原全部 Ω 行的平衡标记

本篇不把任意原 Q 说成平衡。平衡只要求每个 omk 的第二字段逐字为
低字段的 ι；低字段本身暂仍是原坐标类型。ι 和 ι↓ 擦除标记，所以
它们的输出可对任意原输入满足此条件。此为完整新容器之前的生成域证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.RadicalBuildGenerated (𝕊 : HtB) where

import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Tree
open import OCF.Free.Level
open import OCF.Free.Prefix using (Ordˢ; Ord₊ˢ; Ωˢ)
open import OCF.Free.Floor using (Flr; Ev; cvFlo)
open import OCF.Align.LadderOrdTree 𝕊

Balanced : ∀ {m a φ χ} → Q m a φ χ → Set
Balanced q0 = ⊤
Balanced (qs x) = Balanced x
Balanced (ql f) = ∀ n → Balanced (f n)
Balanced (qi ac f) = ∀ x → Balanced (f x)
Balanced (qŝ c t g) = Balanced t × (∀ η e → Balanced (g η e))
Balanced (qĉ c t g o h) = Balanced o × (∀ η e → Balanced (h η e))
Balanced (qclo t g) = Balanced t × (∀ η → Balanced (g η))
Balanced (qcl q ψ s t g) = Balanced t × (∀ η → Balanced (g η))
Balanced (qwk le lc x) = Balanced x
Balanced (qΩ↓ q fe ac h) = ∀ ξ ζ z → Balanced (h ξ ζ z)
Balanced (qΩ fe r h) = ∀ ξ ζ z → Balanced (h ξ ζ z)
Balanced (omk r z x) = x ≡ ι (◃₁→◃ r) (outU (◃₁→◃ r) z)

up-balanced : ∀ {m a b φ χ} (r : a ◃ b) (x : Q m a φ χ) → Balanced (ι r x)
up-balanced r q0 = tt
up-balanced r (qs x) = up-balanced r x
up-balanced r (ql f) = λ n → up-balanced r (f n)
up-balanced r (qi ac f) = λ x → up-balanced r (f x)
up-balanced r (qŝ c t g) = up-balanced r t , (λ η e → up-balanced r (g η e))
up-balanced r (qĉ c t g o h) = up-balanced r o , (λ η e → up-balanced r (h η e))
up-balanced r (qclo t g) = up-balanced r t , (λ η → up-balanced r (g η))
up-balanced r (qcl q ψ s t g) = up-balanced r t , (λ η → up-balanced r (g η))
up-balanced r (qwk le lc x) = up-balanced r x
up-balanced r (qΩ↓ q fe ac h) = λ ξ ζ z → up-balanced r (h ξ ζ z)
up-balanced r (qΩ fe q h) = λ ξ ζ z → up-balanced r (h ξ ζ (intoU (<→◃ q) (outU (<→◃ (OCF.Free.Tree.<◃ q r)) z)))
up-balanced r (omk q z x) = up-balanced r x

down-balanced : ∀ {n m k α φ χ} (r : n <ᴸ m) (x : Q n k φ χ) → Balanced (ι↓ {α = α} r x)
down-balanced r q0 = tt
down-balanced r (qs x) = down-balanced r x
down-balanced r (ql f) = λ i → down-balanced r (f i)
down-balanced r (qi ac f) = λ x → down-balanced r (f x)
down-balanced r (qŝ c t g) = down-balanced r t , (λ η e → down-balanced r (g η e))
down-balanced r (qĉ c t g o h) = down-balanced r o , (λ η e → down-balanced r (h η e))
down-balanced r (qclo t g) = down-balanced r t , (λ η → down-balanced r (g η))
down-balanced r (qcl q ψ s t g) = down-balanced r t , (λ η → down-balanced r (g η))
down-balanced r (qwk le lc x) = down-balanced r x
down-balanced r (qΩ↓ q fe ac h) = λ ξ ζ z → down-balanced r (h ξ ζ (intoV q (outV (tr< q r) z)))
down-balanced r (qΩ fe q h) = λ ξ ζ z → down-balanced r (h ξ ζ (intoU (<→◃ q) (outV r z)))
down-balanced r (omk zero z x) = down-balanced r z
down-balanced r (omk (self i) z x) = down-balanced r z

tl-balanced : ∀ {m k c χ φ} (cv : ∀ {L} → Ev L φ → Simᴵ k L) (a : Ordˢ k) → Balanced (tl {m = m} {c = c} {χ = χ} φ cv a)
tl-balanced cv Ord₊ˢ.zero = tt
tl-balanced cv (Ord₊ˢ.suc a) = tl-balanced cv a
tl-balanced cv (Ord₊ˢ.lim f) = λ i → tl-balanced cv (f i)
tl-balanced cv (Ord₊ˢ.limᵢ q f) = λ x → tl-balanced cv (f (OCF.Free.Prefix.intoˢ (<→◃ q) x))
tl-balanced {k = suc k} cv (Ord₊ˢ.up zero x) = tl-balanced (cvFlo k) x
tl-balanced {k = lim f s} cv (Ord₊ˢ.up (self i) x) = tl-balanced (cvFlo (f i)) x
tl-balanced {k = zero} cv (Ord₊ˢ.ŝ c t g) = tl-balanced cv t , (λ η e → tl-balanced cv (g η e))
tl-balanced {k = suc k} cv (Ord₊ˢ.ŝ c t g) = tl-balanced cv t , (λ η e → tl-balanced cv (g η e))
tl-balanced {k = lim f s} cv (Ord₊ˢ.ŝ c t g) = tl-balanced cv t , (λ η e → tl-balanced cv (g η e))
tl-balanced cv (Ord₊ˢ.ĉᴸ c t g o h) = tl-balanced cv o , (λ η e → tl-balanced cv (h η e))

row-balanced : ∀ m (I : ∀ {n} → n <ᴸ m → XΩ n) (v : View _<ᴸ_ h₀ m) → Balanced (rowV m I v)
row-balanced m I base = tl-balanced _ (Ωˢ (suc zero)) , (λ η → tl-balanced _ (Ωˢ η))
row-balanced m I (clos q) = down-balanced q (I q (suc zero)) , (λ η → down-balanced q (I q η))
row-balanced m I (chain F qs₁) Data.Nat.zero = tt
row-balanced m I (chain F qs₁) (Data.Nat.suc i) = down-balanced (qs₁ i) (I (qs₁ i) zero)

omega-balanced : ∀ m a → Balanced (Ω̇ m a)
omega-balanced m zero = row-balanced m (ΩI m) (view m)
omega-balanced m (suc a) = λ ξ ζ z → refl
omega-balanced m (lim f s) = λ i → refl
```

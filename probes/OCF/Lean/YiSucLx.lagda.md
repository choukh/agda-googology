# YiSuc 同余：第 1 层的 ψ₁ 在 `≼ˣ` 下的同余

**验收文件，档位：编译定理。** `F₁ y = ψ₁(y)` (第 0 层的树经 `tr⁻` 抬到第 1 层再折到第 1 层，`refγ 1 1` 的分支)。`cong₁ : y ≼ˣ y′ → ψ⁰ (F₁ y) ≼ˣ ψ⁰ (F₁ y′)`。
办法：[YiEmb2Le](YiEmb2Le.lagda.md) 的 `Lx` 取恒等嵌入 `XEmb-⊑ ⊑ᴵ-refl` 的实例 (同 [YiEmb2](YiEmb2.lagda.md) 的 `Inst`)，第 0 层的 `≼ˣ` 逐构造子落进 `Lx`，再用 `Le-ψ` 与 `Le-ψ⁰ˣ`。只谈参照框架。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSucLx where

open import Data.Product.Base using (_×_; _,_)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.Align.YiVmConExact using (_≼ˣ_; zˣ; sˣ; wˣ; ≼lˣ; lˣ; XEmb-⊑)
open import OCF.Lean.YiEmb2 using (module Inst)
open import OCF.Lean.YiEmb2Le using (module Two)
open import OCF.Lean.YiChainBase using (T₀)

T₁ : Set
T₁ = L.Ordᶜ (L.suc L.zero)

F₁ : T₀ → T₁
F₁ y = L.ψ L.zero (λ q → L.suc (L.suc q)) (L.tr⁻ L.z≅ y)

private
  X₁ = XEmb-⊑ (L.⊑ᴵ-refl {a = L.suc L.zero})
  module I = Inst X₁ X₁

open Two I.PX.E I.PX.E-resp I.PY.E I.PY.E-resp
open WithLaws I.PX.lt′ I.PX.eq′ I.PY.ℒ I.flip (I.Ω′ L.⊑ᴵ-refl)
```

```agda
≼→B : ∀ {a b : T₀} → a ≼ b → B.Le a b
≼→B z≼ = B.Lz
≼→B (s≼s d) = B.Ls (≼→B d)
≼→B (≼l n d) = B.Llr n (≼→B d)
≼→B (l≼ h) = B.Lll (λ n → ≼→B (h n))
≼→B (≼i {p = ()} x ex d)
≼→B (i≼ {p = ()} h)
≼→B (≼u {r = ()} d)
≼→B (u≼ {r = ()} d)

ˣ→Lx : ∀ {a b : T₀} → a ≼ˣ b → Lx a b
ˣ→Lx zˣ = Lz
ˣ→Lx (sˣ d e) = Ls (ˣ→Lx d) (≼→B e)
ˣ→Lx (wˣ d) = Lsr (ˣ→Lx d)
ˣ→Lx (≼lˣ n d) = Llr n (ˣ→Lx d)
ˣ→Lx (lˣ h) = Lll (λ n → ˣ→Lx (h n))

cong₁ : ∀ {y y′ : T₀} → y ≼ˣ y′ → L.ψ⁰ (F₁ y) ≼ˣ L.ψ⁰ (F₁ y′)
cong₁ d = Le-ψ⁰ˣ (Le-ψ (I.PX.top (L.≅ᴵ-refl _) (L.≅ᴵ-refl _)) L.zero (λ q → L.suc (L.suc q))
  L.zero (λ q → L.suc (L.suc q)) (Lr-tr⁻ L.z≅ (Ll-tr⁻ L.z≅ (ˣ→Lx d))))
```

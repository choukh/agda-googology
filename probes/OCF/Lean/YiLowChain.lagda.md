# YiLow：链归纳只要链上的值单调

**验收文件，档位：条件定理。** `FromVMᶜ`：前提 `VMᶜ` (只对参照第 n 项与主线第 n 个链点，推导任意) 推出 `D.BTBOᴵ ≼ read T₃` 与 `D.BTBOᴵ ≼ NA.read NT.T⁺`。
`VMᶜ` 由 `VMᴸ` 推出，也由 `VMˢ` 加链上两边的严格性推出；n = 0 的实例与严格性是定理 (`vmᶜ₀`, `S₀`)。一般 n 未证；经嵌入的证法被 [YiLowNeg](YiLowNeg.lagda.md) 否定。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLowChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_)
open import OCF.Lean.YiLeanTw3 using (pts; obs; module Pt; T₃)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read; plus≽)
open import OCF.Lean.YiLeanValFin using (HS-read; lower-read; κ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l; l≼; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiMonoVM using (VMᴸ)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Align.YiVmNegBase using (SHS; sz; ss)
open import OCF.Align.YiVmNegBound using (emb-fin)
open import OCF.Lean.YiLowBase using (VMˢ)
import OCF.Lean.YiNextAcc as NA
import OCF.Lean.YiNextTop as NT
open import OCF.Lean.YiNextValFin using (T₃≅)
```

```agda
VMᶜ : Set
VMᶜ = ∀ n → D.γ n ≼ read (co (pts n)) → L.ψ⁰ (L.Ω (D.L n)) ≼ L.ψ⁰ (L.Ω (κ n))

module FromVMᶜ (vm : VMᶜ) where
  chainV : ∀ n → D.γ n ≼ read (co (pts n))
  mono : ∀ n → L.ψ⁰ (L.Ω (D.L n)) ≼ read (obs (pts n))
  chainV zero = ≼-refl _
  chainV (suc n) = plus≽ (co (pts n)) (obs (pts n)) (mono n)
  mono n = ≼-trans (vm n (chainV n)) (lower-read (co (pts n)) (lw (pts n)))

  btbo : D.BTBOᴵ ≼ read T₃
  btbo = l≼ (λ n → ≼l n (mono n))

  btbo⁺ : D.BTBOᴵ ≼ NA.read NT.T⁺
  btbo⁺ = ≼-trans btbo (≼-trans (≅→≼ T₃≅) NA.T₃≼T⁺)

vmᴸ→vmᶜ : VMᴸ → VMᶜ
vmᴸ→vmᶜ vm n d = vm (D.γ n) (D.cert n) (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n))) d

vmˢ→vmᶜ : VMˢ → (∀ n → SHS (D.γ n)) → (∀ n → SHS (read (co (pts n)))) → VMᶜ
vmˢ→vmᶜ vm sx sy n d = vm (D.γ n) (D.cert n) (read (co (pts n))) (HS-read (co (pts n)) (lw (pts n))) (sx n) (sy n) d

S₀ : SHS (D.γ 0) × SHS (read (co (pts 0)))
S₀ = ss sz , ss sz

vmᶜ₀ : D.γ 0 ≼ read (co (pts 0)) → L.ψ⁰ (L.Ω (D.L 0)) ≼ L.ψ⁰ (L.Ω (κ 0))
vmᶜ₀ d = Ψ-emb (emb-fin 1 (D.cert 0) (read (co (pts 0))) (HS-read (co (pts 0)) (lw (pts 0))) d)
```

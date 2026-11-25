# `T⁺ʷ` 不低于 ψ₀(Ω_Ω+Ω₁·2) (无前提)

验收文件. 编译定理 `X₁₂≼ʷ : X₁₂ ≼ NA.read W.T⁺ʷ`, 参照 `X₁₂ = ψ⁰ (Ω_{ℓ₀} ⊕ (Ω₁ + Ω₁))` 读作 ψ₀(Ω_Ω+Ω₁·2). 只是下界.
办法照 [YiDlVOne](YiDlVOne.lagda.md) 的 `ctx`, 换到根链第 2 点 `chain (tw 2) Φ₂ 2` 的结点 `G.lc p₀ Bᵗ`: 底由 `χ₁` 的已证下界给出, 后继与 `top` 两步多用一次目标层 `tw 2` 的保留 (`Φ₂`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiShpOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; Φ₂; p₀; topᶜʷ; up≼; gK; sucK; gm₀; c₃d; ctx; ch≼; d)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 参照

```agda
σA : L.Simᴵ (L.suc L.zero) S2.ℓ₀
σA = λ q → L.lim 0 q

fA : L.Ordᶜ L.zero → L.Ordᶜ S2.ℓ₀
fA y = L.add (L.Ω S2.ℓ₀) σA (L.add (L.Ω (L.suc L.zero)) (λ q → L.suc q) y)

X₁₂ : L.Ordᶜ L.zero
X₁₂ = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (L.Ω (L.suc L.zero) L.+ L.Ω (L.suc L.zero)))

eA : ℕ → L.Ordᶜ L.zero
eA = iterᴸ (λ x → L.ψ (L.lim 0 L.zero) (λ r → r) (fA x)) (L.suc L.zero)

X₁₂-form : X₁₂ ≡ L.lim (λ n → L.ψ⁰ (fA (eA n)))
X₁₂-form = refl

fA-0 : L.ψ⁰ (fA L.zero) ≡ S2.χ 1
fA-0 = refl
```

## 2 根链第 2 点

```agda
c1 : Raw (tw 2)
c1 = G.lc p₀ gK

Bᵗ : R → Raw (tw 2)
Bᵗ ξ = plus (tw 2) c1 (Φ₂ (gK ξ))

term₂ : chain (tw 2) Φ₂ 2 ≡ G.lc p₀ Bᵗ
term₂ = refl

χ₁≼c1 : S2.χ 1 ≼ NA.read (Ψ₀ c1)
χ₁≼c1 = l≼ (λ m → ≼l m (ctx (ch≼ m) (d m) refl))

sucΦ : ∀ x → Cp (tw 2) (G.suc (Φ₂ x)) (Φ₂ (G.suc x))
sucΦ x = inj₂ (1 , add-cp (tw 2) G.lc dnLc (Φ₂ x) (topᶜʷ (tw 2) V2 (self (tw 2)) x))

stepB : ∀ a → NA.read (Ψ₀ (G.suc (Bᵗ a))) ≼ NA.read (Ψ₀ (Bᵗ (G.suc a)))
stepB a = ≼-trans (up≼ (add-cp (tw 2) G.lc dnLc c1 (sucΦ (gK a))))
  (up≼ (add-cp (tw 2) G.lc dnLc c1 (W.Ψ-cp (tw 2) V2 (self (tw 2)) (sucK a))))

hB : R → Raw (tw 2)
hB ζ = plus (tw 2) c1 (Φ₂ (plus (tw 2) G.top (gm₀ ζ)))

Btop : Bᵗ G.top ≡ G.lc p₀ hB
Btop = refl

gk₅ : R → R
gk₅ ζ = W.Ψ zero V2 (W.cmpw V2 p₀) (hB ζ)

e₅ : R
e₅ = chain zero gk₅ 1

c₅a : Cp zero (G.suc G.top) e₅
c₅a = add-cp zero G.lc dnLc G.top (topᶜʷ zero V2 (W.cmpw V2 p₀) (hB G.top))

topB : NA.read (Ψ₀ (G.suc (Bᵗ G.zero))) ≼ NA.read (Ψ₀ (Bᵗ G.top))
topB = ≼-trans (up≼ (add-cp (tw 2) G.lc dnLc c1 (sucΦ (gK G.zero))))
  (≼-trans (up≼ (add-cp (tw 2) G.lc dnLc c1 (W.Ψ-cp (tw 2) V2 (self (tw 2)) c₃d)))
  (≼-trans (up≼ (add-cp (tw 2) G.lc dnLc c1 (W.Ψ-cp (tw 2) V2 (self (tw 2))
     (add-cp (tw 2) G.lc dnLc G.top (W.Ψ-cp (tw 2) WL.w0 (λ r → keep (G.top , tt , inj₂ r) refl) c₅a)))))
  (≼l 1 (≼-refl _))))
```

## 3 上下文引理与 ψ₀(Ω_Ω+Ω₁·2)

```agda
ctx₂ : ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ξ → b ≡ NA.read ξ → L.ψ⁰ (fA y) ≼ NA.read (Ψ₀ (Bᵗ ξ))
ctx₂ z≼ ξ q = ≼-trans χ₁≼c1 (up≼ (plus-weak (tw 2) c1 (Φ₂ (gK ξ))))
ctx₂ (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (Bᵗ a)) (ctx₂ p a refl)) (stepB a)
ctx₂ (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (Bᵗ G.zero)) (ctx₂ p G.zero refl)) topB
ctx₂ (≼l n p) (G.lim f) refl = ≼l n (ctx₂ p (f n) refl)
ctx₂ (l≼ h) ξ q = l≼ (λ n → ctx₂ (h n) ξ q)
ctx₂ (≼i {p = ()} x ex p) ξ q
ctx₂ (i≼ {p = ()} h) ξ q
ctx₂ (≼u {r = ()} p) ξ q
ctx₂ (u≼ {r = ()} p) ξ q

gk₂ : R → R
gk₂ ζ = W.Ψ zero V2 (W.cmpw V2 p₀) (Bᵗ ζ)

d₂ : ℕ → R
d₂ = chain zero gk₂

fA-≅ : ∀ y → fA y L.≅ fA y
fA-≅ y = L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀)
  (L.add-≅ {σ = λ q → L.suc q} {σ′ = λ q → L.suc q} (L.Ω-refl (L.suc L.zero)) (L.≅-refl⁰ y))

eA≼ : ∀ m → eA m ≼ NA.read (d₂ m)
eA≼ zero = ≼-refl _
eA≼ (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r} (fA-≅ (eA m)))))
  (NA.plus≽ (d₂ m) (gk₂ (d₂ m)) (ctx₂ (eA≼ m) (d₂ m) refl))

X₁₂≼ʷ : X₁₂ ≼ NA.read W.T⁺ʷ
X₁₂≼ʷ = ≼l 2 (l≼ (λ m → ≼l m (ctx₂ (eA≼ m) (d₂ m) refl)))
```

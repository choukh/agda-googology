# ψ₀(Ω_Ω+Ω₃): 树在 Ω₃ 结点的形状, 参照, 一条条件定理

验收文件. 树: 根链第 1 点的分支 `gK (suc (suc top))` 里有层号 2 的 Ω₃ 结点 `Tt ssT` (位置 `s₃`); 目标层 2 的折叠 `ψ₂` 在根 `p₀` 上保留层号 0 (`ψ₂-top`), 在 `G₃` 的层号 0, 1 的结点上都保留 (`refl`). 参照 `X₃ = ψ⁰ (Ω_{ℓ₀} ⊕ Ω₃)` 读作 ψ₀(Ω_Ω+Ω₃) (读法是判断, 没有逐项一致证明), `X₃-form` (`refl`) 是它的链.
条件定理 `X₃≼ᶜ : Sync₃ → X₃ ≼ NA.read W.TΛ`; [YiStepThree](YiStepThree.lagda.md) 在第 2 层的对角定理之下给出 `Sync₃`. 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiStepTree where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open NA using (R₁)
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; up≼; Tt; gK; gk₁; d)
open import OCF.Lean.YiDlVBtbo using (Vw)
open import OCF.Lean.YiShpOmega using (cpT)
open import OCF.Lean.YiShpSq using (ψ₁)
open import OCF.Lean.YiIntoTw3 using (T⁺ʷ≼TΛ)
open import OCF.Align.YiLvVal2 using (ℓ₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼l; l≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 Ω₃ 结点与它的分支族

`G₃` 是 `Tt ssT` 那一支的分支族 (`Ω_Ω + K₀ + η`, `K₀` 含 Ω₁, Ω₂ 结点); `G₃′`, `G₃″` 是它在层号 1, 0 的嵌入上.

```agda
L2 : LF
L2 = suc (suc zero)

R₂ : Set
R₂ = Raw L2

ssT : R
ssT = G.suc (G.suc G.top)

s₃ s₁ᵗ s₀ᵗ : Pre (tw 2)
s₃ = ssT , tt , inj₁ tt
s₁ᵗ = ssT , tt , inj₂ (inj₁ tt)
s₀ᵗ = ssT , tt , inj₂ (inj₂ (inj₁ tt))

gm₃ : R₂ → Raw (tw 2)
gm₃ = W.Ψ (tw 2) (WL.ws (WL.ws WL.w0)) (λ r → keep (ssT , tt , inj₂ r) refl)

gm₃′ : R₁ → Raw (tw 2)
gm₃′ = W.Ψ (tw 2) (WL.ws WL.w0) (λ r → keep (ssT , tt , inj₂ (inj₂ r)) refl)

gm₃″ : R → Raw (tw 2)
gm₃″ = W.Ψ (tw 2) WL.w0 (λ r → keep (ssT , tt , inj₂ (inj₂ (inj₂ r))) refl)

K₀ : Raw (tw 2)
K₀ = WL.Kfk zero Tt (G.suc G.top)

G₃ : R₂ → Raw (tw 2)
G₃ η = plus (tw 2) G.top (plus (tw 2) K₀ (gm₃ η))

G₃′ : R₁ → Raw (tw 2)
G₃′ η = plus (tw 2) G.top (plus (tw 2) K₀ (gm₃′ η))

G₃″ : R → Raw (tw 2)
G₃″ a = plus (tw 2) G.top (plus (tw 2) K₀ (gm₃″ a))

ψ₂ : Raw (tw 2) → R₂
ψ₂ = W.Ψ L2 V2 (W.cmpw V2 s₃)

γ₃ : ℕ → R₂
γ₃ = chain L2 (λ η → ψ₂ (G₃ η))

Tt-s₃ : Tt ssT ≡ G.lc s₃ gm₃
Tt-s₃ = refl

N₃-form : plus (tw 2) G.top (plus (tw 2) K₀ (Tt ssT)) ≡ G.lc s₃ G₃
N₃-form = refl

N₃-chain : Ψ₀ (G.lc s₃ G₃) ≡ G.lim (λ n → Ψ₀ (G₃ (γ₃ n)))
N₃-chain = refl
```

## 2 派发: 目标层 2 在层号 0, 1 上保留, 目标层 1 在层号 0 上保留

```agda
Tψ₂ : R → R₂
Tψ₂ η = W.Ψ L2 (Vw (WL.nrmk zero η) (WL.nrmk-lgl zero η))
  (λ r → W.cmpw V2 s₃ (WL.nrmk zero η , WL.nrmk-lgl zero η , r)) G.top

K₂ : R → R₂
K₂ = WL.Kfk zero Tψ₂

ψ₂-top : ψ₂ G.top ≡ G.lc (inj₂ (inj₁ tt)) K₂
ψ₂-top = refl

G₃-em : ∀ a → G₃ (G.em tt a) ≡ G₃′ a
G₃-em a = refl

G₃′-em : ∀ a → G₃′ (G.em tt a) ≡ G₃″ a
G₃′-em a = refl

ψ₂-lc₁ : ∀ g → ψ₂ (G₃ (G.lc (inj₁ tt) g)) ≡ G.lc (inj₁ tt) (λ η → ψ₂ (G₃ (g η)))
ψ₂-lc₁ g = refl

ψ₂-lc₀ : ∀ g → ψ₂ (G₃ (G.lc (inj₂ (inj₁ tt)) g)) ≡ G.lc (inj₂ (inj₁ tt)) (λ η → ψ₂ (G₃ (g η)))
ψ₂-lc₀ g = refl

ψ₂-tp : ψ₂ (G₃ G.top) ≡ G.lc (inj₁ tt) (λ η → ψ₂ (G₃′ η))
ψ₂-tp = refl

ψ₂′-lc : ∀ g → ψ₂ (G₃′ (G.lc (inj₁ tt) g)) ≡ G.lc (inj₂ (inj₁ tt)) (λ η → ψ₂ (G₃′ (g η)))
ψ₂′-lc g = refl

ψ₂′-tp : ψ₂ (G₃′ G.top) ≡ G.lc (inj₂ (inj₁ tt)) (λ a → ψ₂ (G₃″ a))
ψ₂′-tp = refl

ψ₁-lc₀ : ∀ g → ψ₁ (G₃ (G.lc (inj₂ (inj₁ tt)) g)) ≡ G.lc (inj₁ tt) (λ η → ψ₁ (G₃ (g η)))
ψ₁-lc₀ g = refl

ψ₁-lc₁ : ∀ g → ψ₁ (G₃ (G.lc (inj₁ tt) g)) ≡ G.lim (λ n → ψ₁ (G₃ (g (chain (suc zero) (λ η → ψ₁ (G₃ (g η))) n))))
ψ₁-lc₁ g = refl

Ψ₀-lc₁ : ∀ g → Ψ₀ (G₃ (G.lc (inj₁ tt) g)) ≡ G.lim (λ n → Ψ₀ (G₃ (g (chain (suc zero) (λ η → ψ₁ (G₃ (g η))) n))))
Ψ₀-lc₁ g = refl
```

## 3 结点在 `T⁺ʷ` 之下

```agda
cT : Cp zero (G.suc G.top) (W.Tw 2)
cT = inj₂ (0 , inj₂ (0 , inj₂ (1 , inj₁ refl)))

c-g : Cp zero (G.suc (W.Tw 2)) (gk₁ G.top)
c-g = inj₂ (0 , inj₂ (0 , inj₂ (1 , inj₂ (0 , inj₂ (0 , inj₂ (0 , inj₁ refl))))))

c-d₃ : Cp zero ssT (d 1)
c-d₃ = add-cp zero G.lc dnLc G.top (cpT zero (inj₂ cT) c-g)

N₃≼T : ∀ {X : L.Ordᶜ L.zero} → X ≼ NA.read (Ψ₀ (G.lc s₃ G₃)) → X ≼ NA.read W.T⁺ʷ
N₃≼T h = ≼l 1 (≼l 1 (≼-trans h
  (≼-trans (up≼ {A = G.lc s₃ G₃} {B = gK ssT} (inj₂ (1 , inj₁ refl)))
    (up≼ (add-cp (tw 2) G.lc dnLc G.top (WL.Kfk-cp zero Tt c-d₃))))))
```

## 4 参照与条件定理

```agda
σ₃ : L.Simᴵ (L.suc (L.suc (L.suc L.zero))) S2.ℓ₀
σ₃ q = L.lim 1 (L.lim 0 (L.lim 3 q))

σ₃′ : L.Simᴵ ℓ₂ S2.ℓ₀
σ₃′ q = σ₃ (L.suc q)

X₃ : L.Ordᶜ L.zero
X₃ = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃ (L.Ω (L.suc (L.suc (L.suc L.zero)))))

e₃ : ℕ → L.Ordᶜ ℓ₂
e₃ = iterᴸ (λ x → L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃′ x)) (L.Ω ℓ₂)

X₃-form : X₃ ≡ L.lim (λ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃′ (e₃ n)))
X₃-form = refl

Sync₃ : Set
Sync₃ = ∀ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃′ (e₃ n)) ≼ NA.read (Ψ₀ (G₃ (γ₃ n)))

X₃≼ʷᶜ : Sync₃ → X₃ ≼ NA.read W.T⁺ʷ
X₃≼ʷᶜ h = N₃≼T (l≼ (λ n → ≼l n (h n)))

X₃≼ᶜ : Sync₃ → X₃ ≼ NA.read W.TΛ
X₃≼ᶜ h = ≼-trans (X₃≼ʷᶜ h) T⁺ʷ≼TΛ
```

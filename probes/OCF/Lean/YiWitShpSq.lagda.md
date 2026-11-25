# `T⁺ʷ` 不低于 ψ₀(Ω_Ω+Ω₁²) (无前提) (搬到收缩见证的折叠)

验收文件. [YiShpSq](YiShpSq.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitShpSq where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiWitVOne using (V2; Ψ₀; p₀; topᶜʷ; up≼; gK; Tt; d)
open import OCF.Lean.YiWitVBtbo using (btbo-Tw2)
open import OCF.Lean.YiWitShpOne using (σA)
open import OCF.Lean.YiWitShpOmega using (cpT; fQ; fQ-≅)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 位置族 (取值形式的 `top` 一步)

与 [YiShpOmega](YiShpOmega.lagda.md) 的 `Fam` 相同, 只是 `top` 支只要求取值的一步; 结点引理不指定位置, 结论写成层号 0 的链的极限.

```agda
record FamV (Q : L.Ordᶜ (L.suc L.zero)) (B : R → Raw (tw 2)) : Set where
  field
    base : ∀ ξ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA Q) ≼ NA.read (Ψ₀ (B ξ))
    sucB : ∀ a → Cp (tw 2) (G.suc (B a)) (B (G.suc a))
    limB : ∀ f n → Cp (tw 2) (B (f n)) (B (G.lim f))
    topV : NA.read (Ψ₀ (G.suc (B G.zero))) ≼ NA.read (Ψ₀ (B G.top))
open FamV

ctxV : ∀ {Q B} → FamV Q B → ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ξ → b ≡ NA.read ξ →
  L.ψ⁰ (fQ Q y) ≼ NA.read (Ψ₀ (B ξ))
ctxV F z≼ ξ q = base F ξ
ctxV {B = B} F (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (B a)) (ctxV F p a refl)) (up≼ (sucB F a))
ctxV {B = B} F (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (B G.zero)) (ctxV F p G.zero refl)) (topV F)
ctxV F (≼l n p) (G.lim f) refl = ≼-trans (ctxV F p (f n) refl) (up≼ (limB F f n))
ctxV F (l≼ h) ξ q = l≼ (λ n → ctxV F (h n) ξ q)
ctxV F (≼i {p = ()} x ex p) ξ q
ctxV F (i≼ {p = ()} h) ξ q
ctxV F (≼u {r = ()} p) ξ q
ctxV F (u≼ {r = ()} p) ξ q

eV : L.Ordᶜ (L.suc L.zero) → ℕ → L.Ordᶜ L.zero
eV Q = iterᴸ (λ x → L.ψ (L.lim 0 L.zero) (λ r → r) (fQ Q x)) (L.suc L.zero)

dV : (R → Raw (tw 2)) → ℕ → R
dV B = chain zero (λ ζ → Ψ₀ (B ζ))

eV≼ : ∀ {Q B} → Q L.≅ Q → FamV Q B → ∀ m → eV Q m ≼ NA.read (dV B m)
eV≼ e F zero = ≼-refl _
eV≼ {Q} {B} e F (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r} (fQ-≅ Q e (eV Q m)))))
  (NA.plus≽ (dV B m) (Ψ₀ (B (dV B m))) (ctxV F (eV≼ e F m) (dV B m) refl))

nodeV : ∀ {Q B} → Q L.≅ Q → FamV Q B →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (Q L.+ L.Ω (L.suc L.zero))) ≼ L.lim (λ m → NA.read (Ψ₀ (B (dV B m))))
nodeV e F = l≼ (λ m → ≼l m (ctxV F (eV≼ e F m) (dV _ m) refl))
```

## 2 Ω₂ 结点 `Tt (suc top)` 与目标层 1 的保留

```agda
s₂ s₀″ : Pre (tw 2)
s₂ = G.suc G.top , tt , inj₁ tt
s₀″ = G.suc G.top , tt , inj₂ (inj₁ tt)

gm₂ : Raw (suc zero) → Raw (tw 2)
gm₂ = W.Ψ (tw 2) (WL.ws WL.w0) (λ r → keep (G.suc G.top , tt , inj₂ r) refl)

gm₀″ : R → Raw (tw 2)
gm₀″ = W.Ψ (tw 2) WL.w0 (λ r → keep (G.suc G.top , tt , inj₂ (inj₂ r)) refl)

Tt-s₂ : Tt (G.suc G.top) ≡ G.lc s₂ gm₂
Tt-s₂ = refl

gm₂-top : gm₂ G.top ≡ G.lc s₀″ gm₀″
gm₂-top = refl

dl-keep : W.cmpw V2 s₂ s₀″ ≡ keep (inj₁ tt) refl
dl-keep = refl

G₂ : Raw (suc zero) → Raw (tw 2)
G₂ η = plus (tw 2) G.top (plus (tw 2) (Tt G.top) (gm₂ η))

A : R → Raw (tw 2)
A ζ = plus (tw 2) G.top (plus (tw 2) (Tt G.top) (gm₀″ ζ))

ψ₁ : Raw (tw 2) → Raw (suc zero)
ψ₁ = W.Ψ (suc zero) V2 (W.cmpw V2 s₂)

Y : R → Raw (suc zero)
Y ζ = ψ₁ (A ζ)

Bq : R → Raw (tw 2)
Bq ζ = G₂ (plus (suc zero) G.top (Y ζ))

N₂-form : plus (tw 2) G.top (plus (tw 2) (Tt G.top) (Tt (G.suc G.top))) ≡ G.lc s₂ G₂
N₂-form = refl

γ₁-form : chain (suc zero) (λ η → ψ₁ (G₂ η)) 1 ≡ G.lc (inj₁ tt) (λ ζ → plus (suc zero) G.top (Y ζ))
γ₁-form = refl

G₂γ₁ : G₂ (chain (suc zero) (λ η → ψ₁ (G₂ η)) 1) ≡ G.lc s₀″ Bq
G₂γ₁ = refl
```

## 3 第 1 层的链点上 Ω₁ 的累加

```agda
sucg : ∀ {k} (V : WL.Lw k) x Z → Cp (tw 2) (G.suc (W.Ψ (tw 2) V x Z)) (W.Ψ (tw 2) V x (G.suc Z))
sucg V x Z = inj₂ (1 , add-cp (tw 2) G.lc dnLc (W.Ψ (tw 2) V x Z) (topᶜʷ (tw 2) V x Z))

Asuc : ∀ a → Cp (tw 2) (G.suc (A a)) (A (G.suc a))
Asuc a = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Tt G.top) (sucg WL.w0 _ a))

Atop : Cp (tw 2) (G.suc (A G.zero)) (A G.top)
Atop = inj₂ (1 , inj₁ refl)

Y+Ω : ∀ a → Cp (suc zero) (plus (suc zero) (Y a) G.top) (ψ₁ (G.suc (A a)))
Y+Ω a = inj₂ (1 , add-cp (suc zero) G.lc dnLc (Y a) (topᶜʷ (suc zero) V2 (W.cmpw V2 s₂) (A a)))

Ysuc : ∀ a → Cp (suc zero) (plus (suc zero) (Y a) G.top) (Y (G.suc a))
Ysuc a = cpT (suc zero) (Y+Ω a) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (Asuc a))

Ytop : Cp (suc zero) (plus (suc zero) (Y G.zero) G.top) (Y G.top)
Ytop = cpT (suc zero) (Y+Ω G.zero) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) Atop)

Bs : R → R → Raw (tw 2)
Bs a η = G₂ (plus (suc zero) G.top (plus (suc zero) (Y a) (G.em tt η)))

Bs-node : ∀ a → G.lc s₀″ (Bs a) ≡ G₂ (plus (suc zero) G.top (plus (suc zero) (Y a) G.top))
Bs-node a = refl

up-Bq : ∀ {a ζ} → Cp (suc zero) (plus (suc zero) (Y a) G.top) (Y ζ) → Cp (tw 2) (G.lc s₀″ (Bs a)) (Bq ζ)
up-Bq c = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Tt G.top)
  (W.Ψ-cp (tw 2) (WL.ws WL.w0) _ (add-cp (suc zero) G.lc dnLc G.top c)))
```

## 4 参照 Ω₁·y 与上下文引理

```agda
mulΩ : L.Ordᶜ L.zero → L.Ordᶜ (L.suc L.zero)
mulΩ L.zero = L.zero
mulΩ (L.suc y) = mulΩ y L.+ L.Ω (L.suc L.zero)
mulΩ (L.lim f) = L.lim (λ n → mulΩ (f n))
mulΩ (L.limᵢ () f)
mulΩ (L.up () x)

mulΩ-≅ : ∀ y → mulΩ y L.≅ mulΩ y
mulΩ-≅ L.zero = L.z≅
mulΩ-≅ (L.suc y) = L.add-≅ {σ = λ q → q} {σ′ = λ q → q} (mulΩ-≅ y) (L.Ω-refl (L.suc L.zero))
mulΩ-≅ (L.lim f) = L.l≅ (λ n → mulΩ-≅ (f n))
mulΩ-≅ (L.limᵢ () f)
mulΩ-≅ (L.up () x)

ctxY : ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ζ → b ≡ NA.read ζ →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (mulΩ y)) ≼ NA.read (Ψ₀ (Bq ζ))
famY : ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ NA.read a → FamV (mulΩ y) (Bs a)

ctxY z≼ ζ q = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
ctxY {L.suc y} (s≼s p) (G.suc a) refl = ≼-trans (nodeV (mulΩ-≅ y) (famY p a refl)) (up≼ (up-Bq (Ysuc a)))
ctxY {L.suc y} (s≼s p) G.top refl = ≼-trans (nodeV (mulΩ-≅ y) (famY p G.zero refl)) (up≼ (up-Bq Ytop))
ctxY (≼l n p) (G.lim f) refl = ≼l n (ctxY p (f n) refl)
ctxY (l≼ h) ζ q = l≼ (λ n → ctxY (h n) ζ q)
ctxY (≼i {p = ()} x ex p) ζ q
ctxY (i≼ {p = ()} h) ζ q
ctxY (≼u {r = ()} p) ζ q
ctxY (u≼ {r = ()} p) ζ q

famY p a q .base η = ≼-trans (ctxY p a q) (up≼ (add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Tt G.top)
  (W.Ψ-cp (tw 2) (WL.ws WL.w0) _ (add-cp (suc zero) G.lc dnLc G.top (plus-weak (suc zero) (Y a) (G.em tt η)))))))
famY p a q .sucB η = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Tt G.top)
  (sucg (WL.ws WL.w0) _ (plus (suc zero) G.top (plus (suc zero) (Y a) (G.em tt η)))))
famY p a q .limB f n = inj₂ (n , inj₁ refl)
famY p a q .topV = up≼ (add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Tt G.top)
  (sucg (WL.ws WL.w0) _ (plus (suc zero) G.top (Y a)))))
```

## 5 ψ₀(Ω_Ω+Ω₁²)

```agda
X² : L.Ordᶜ L.zero
X² = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (L.limᵢ L.zero mulΩ))

e² : ℕ → L.Ordᶜ L.zero
e² = iterᴸ (λ x → L.ψ (L.lim 0 L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA (mulΩ x))) (L.suc L.zero)

X²-form : X² ≡ L.lim (λ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (mulΩ (e² n))))
X²-form = refl

δ : ℕ → R
δ = chain zero (λ ζ → Ψ₀ (Bq ζ))

e²≼ : ∀ m → e² m ≼ NA.read (δ m)
e²≼ zero = ≼-refl _
e²≼ (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
    (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀) (mulΩ-≅ (e² m))))))
  (NA.plus≽ (δ m) (Ψ₀ (Bq (δ m))) (ctxY (e²≼ m) (δ m) refl))

X²≼node : X² ≼ NA.read (Ψ₀ (G.lc s₀″ Bq))
X²≼node = l≼ (λ m → ≼l m (ctxY (e²≼ m) (δ m) refl))

c-d1 : Cp zero (G.suc G.top) (d 1)
c-d1 = add-cp zero G.lc dnLc G.top (topᶜʷ zero V2 (W.cmpw V2 p₀) (gK G.top))

N₂≼T : ∀ {X : L.Ordᶜ L.zero} → X ≼ NA.read (Ψ₀ (G.lc s₂ G₂)) → X ≼ NA.read WF.T⁺ʷ
N₂≼T h = ≼l 1 (≼l 1 (≼-trans h
  (≼-trans (up≼ {A = G.lc s₂ G₂} {B = gK (G.suc G.top)} (inj₂ (1 , inj₁ refl)))
    (up≼ (add-cp (tw 2) G.lc dnLc G.top (WL.Kfk-cp zero Tt c-d1))))))

node≼T : ∀ {X : L.Ordᶜ L.zero} → X ≼ NA.read (Ψ₀ (G.lc s₀″ Bq)) → X ≼ NA.read WF.T⁺ʷ
node≼T h = N₂≼T (≼-trans h (≼l 1 (≼-refl _)))

X²≼ʷ : X² ≼ NA.read WF.T⁺ʷ
X²≼ʷ = node≼T X²≼node
```

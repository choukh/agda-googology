# 裸折叠的 `T⁺ʷᵇ` 不低于 ψ₀(Ω_Ω+Ω₁·n) 对一切 n, 从而不低于 ψ₀(Ω_Ω+Ω₁·ω) (无前提)

验收文件. 编译定理 `Ω₁n≼`, `Xω≼ʷ : Xω ≼ NA.read W.T⁺ʷᵇ`, 参照与读法同 [YiShpOmega](YiShpOmega.lagda.md); 只是下界. 搬到 [YiBareFold](YiBareFold.lagda.md): §1 与 §3 的参照部分逐字.
改写: `Fam` 的 `top` 字段由结点形状 (`H`, `topEq`, `HM`, `HS`) 换成一条第一位置 `topC`; `Fam-step` 带前缀 `c` 与 `Cp (G.lc p₀ B) c` (裸折叠的根链点是 ℕ-极限, 第 0 项才是结点), 所以不要 `chain-eq`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBareShpOmega where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiBareFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiBareVOne using (V2; Ψ₀; Φ₂; p₀; topᶜʷ; up≼; gK; sucK; gm₀)
open import OCF.Lean.YiBareVBtbo using (btbo-Tw2)
open import OCF.Lean.YiBareShpOne using (σA; sucΦ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 一般层上第一位置的传递

```agda
cpT : ∀ y {a b c : Raw y} → Cp y a b → Cp y b c → Cp y a c
dnT : ∀ y {a b : Raw y} c → Cp y a b → Dn y b c → Dn y a c
dnI : ∀ y (i : Kid y) {a b} c → Lay.dn (KS y i) a b → Lay.dn (KS y i) b c → Lay.dn (KS y i) a c

cpT y p (inj₁ refl) = p
cpT y p (inj₂ q) = inj₂ (dnT y _ p q)

dnT y (G.suc d) p q = cpT y p q
dnT y (G.lim f) p (n , q) = n , cpT y p q
dnT y (G.lc r g) p q = cpT y p q
dnT y (G.em j d) (inj₁ refl) q = q
dnT y {G.em i a} {G.em i′ b} (G.em j d) (inj₂ (refl , p)) (refl , q) = refl , dnI y i d p q
dnT y {G.zero} {G.em i′ b} (G.em j d) (inj₂ ()) q
dnT y {G.suc a} {G.em i′ b} (G.em j d) (inj₂ ()) q
dnT y {G.lim f} {G.em i′ b} (G.em j d) (inj₂ ()) q
dnT y {G.lc r g} {G.em i′ b} (G.em j d) (inj₂ ()) q
dnT y {G.top} {G.em i′ b} (G.em j d) (inj₂ ()) q
dnT y {b = G.zero} (G.em j d) (inj₂ p) ()
dnT y {b = G.suc b} (G.em j d) (inj₂ p) ()
dnT y {b = G.lim f} (G.em j d) (inj₂ p) ()
dnT y {b = G.lc r g} (G.em j d) (inj₂ p) ()
dnT y {b = G.top} (G.em j d) (inj₂ p) ()

dnI (suc k) i c p q = dnT k c (inj₂ p) q
dnI (lim f) n c p q = dnT (f n) c (inj₂ p) q
dnI (lc k g) (η , l) c p q = dnT (g η) c (inj₂ p) q
```

## 2 位置族与上下文引理

```agda
fQ : L.Ordᶜ (L.suc L.zero) → L.Ordᶜ L.zero → L.Ordᶜ S2.ℓ₀
fQ Q y = L.add (L.Ω S2.ℓ₀) σA (L.add Q (λ q → L.suc q) y)

record Fam (Q : L.Ordᶜ (L.suc L.zero)) (B : R → Raw (tw 2)) : Set where
  field
    base : ∀ ξ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA Q) ≼ NA.read (Ψ₀ (B ξ))
    sucB : ∀ a → Cp (tw 2) (G.suc (B a)) (B (G.suc a))
    limB : ∀ f n → Cp (tw 2) (B (f n)) (B (G.lim f))
    topC : Cp (tw 2) (G.suc (B G.zero)) (B G.top)
open Fam

ctxF : ∀ {Q B} → Fam Q B → ∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ξ → b ≡ NA.read ξ →
  L.ψ⁰ (fQ Q y) ≼ NA.read (Ψ₀ (B ξ))
ctxF F z≼ ξ q = base F ξ
ctxF {B = B} F (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (B a)) (ctxF F p a refl)) (up≼ (sucB F a))
ctxF {B = B} F (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (B G.zero)) (ctxF F p G.zero refl)) (up≼ (topC F))
ctxF F (≼l n p) (G.lim f) refl = ≼-trans (ctxF F p (f n) refl) (up≼ (limB F f n))
ctxF F (l≼ h) ξ q = l≼ (λ n → ctxF F (h n) ξ q)
ctxF F (≼i {p = ()} x ex p) ξ q
ctxF F (i≼ {p = ()} h) ξ q
ctxF F (≼u {r = ()} p) ξ q
ctxF F (u≼ {r = ()} p) ξ q
```

## 3 沿根链推一点

```agda
eQ : L.Ordᶜ (L.suc L.zero) → ℕ → L.Ordᶜ L.zero
eQ Q = iterᴸ (λ x → L.ψ (L.lim 0 L.zero) (λ r → r) (fQ Q x)) (L.suc L.zero)

form : ∀ Q → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (Q L.+ L.Ω (L.suc L.zero))) ≡ L.lim (λ n → L.ψ⁰ (fQ Q (eQ Q n)))
form Q = refl

fQ-≅ : ∀ Q → Q L.≅ Q → ∀ y → fQ Q y L.≅ fQ Q y
fQ-≅ Q eQ y = L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀)
  (L.add-≅ {σ = λ q → L.suc q} {σ′ = λ q → L.suc q} eQ (L.≅-refl⁰ y))

dB : (R → Raw (tw 2)) → ℕ → R
dB B = chain zero (λ ζ → W.Ψ zero V2 (W.cmpw V2 p₀) (B ζ))

eQ≼ : ∀ {Q B} → Q L.≅ Q → Fam Q B → ∀ m → eQ Q m ≼ NA.read (dB B m)
eQ≼ e F zero = ≼-refl _
eQ≼ {Q} {B} e F (suc m) = ≼-trans
  (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r} (fQ-≅ Q e (eQ Q m)))))
  (NA.plus≽ (dB B m) (W.Ψ zero V2 (W.cmpw V2 p₀) (B (dB B m))) (ctxF F (eQ≼ e F m) (dB B m) refl))

node≼ : ∀ {Q B} → Q L.≅ Q → Fam Q B →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (Q L.+ L.Ω (L.suc L.zero))) ≼ NA.read (Ψ₀ (G.lc p₀ B))
node≼ e F = l≼ (λ m → ≼l m (ctxF F (eQ≼ e F m) (dB _ m) refl))

Fam-step : ∀ {Q B} → Q L.≅ Q → Fam Q B → ∀ c → Cp (tw 2) (G.lc p₀ B) c →
  Fam (Q L.+ L.Ω (L.suc L.zero)) (λ ξ → plus (tw 2) c (Φ₂ (B ξ)))
Fam-step {B = B} e F c cc .base ξ = ≼-trans (node≼ e F) (up≼ (cpT (tw 2) cc (plus-weak (tw 2) c (Φ₂ (B ξ)))))
Fam-step {B = B} e F c cc .sucB a = add-cp (tw 2) G.lc dnLc c
  (cpT (tw 2) (sucΦ (B a)) (W.Ψ-cp (tw 2) V2 (self (tw 2)) (sucB F a)))
Fam-step {B = B} e F c cc .limB f n = add-cp (tw 2) G.lc dnLc c (W.Ψ-cp (tw 2) V2 (self (tw 2)) (limB F f n))
Fam-step {B = B} e F c cc .topC = add-cp (tw 2) G.lc dnLc c
  (cpT (tw 2) (sucΦ (B G.zero)) (W.Ψ-cp (tw 2) V2 (self (tw 2)) (topC F)))
```

## 4 根链的起点与 ψ₀(Ω_Ω+Ω₁·ω)

```agda
Fam₀ : Fam L.zero gK
Fam₀ .base ξ = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top (gm₀ ξ)))
Fam₀ .sucB = sucK
Fam₀ .limB f n = inj₂ (n , inj₁ refl)
Fam₀ .topC = inj₂ (1 , inj₁ refl)

P : ℕ → L.Ordᶜ (L.suc L.zero)
P zero = L.zero
P (suc n) = P n L.+ L.Ω (L.suc L.zero)

P-≅ : ∀ n → P n L.≅ P n
P-≅ zero = L.z≅
P-≅ (suc n) = L.add-≅ {σ = λ q → q} {σ′ = λ q → q} (P-≅ n) (L.Ω-refl (L.suc L.zero))

Bn : ℕ → R → Raw (tw 2)
Bn zero = gK
Bn (suc n) ξ = plus (tw 2) (chain (tw 2) Φ₂ (suc n)) (Φ₂ (Bn n ξ))

-- 根链第 suc n 点的第一位置里有结点 G.lc p₀ (Bn n) (目标层 tw 2 在 p₀ 上保留, 加法保持结点).
c₀ : ∀ n → Cp (tw 2) (G.lc p₀ (Bn n)) (chain (tw 2) Φ₂ (suc n))
c₀ zero = inj₂ (0 , inj₁ refl)
c₀ (suc n) = add-cp (tw 2) G.lc dnLc (chain (tw 2) Φ₂ (suc n)) (W.Ψ-cp (tw 2) V2 (self (tw 2)) (c₀ n))

FamN : ∀ n → Fam (P n) (Bn n)
FamN zero = Fam₀
FamN (suc n) = Fam-step (P-≅ n) (FamN n) (chain (tw 2) Φ₂ (suc n)) (c₀ n)

Ω₁n≼ : ∀ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (P (suc n))) ≼ NA.read (Ψ₀ (chain (tw 2) Φ₂ (suc n)))
Ω₁n≼ n = ≼-trans (node≼ (P-≅ n) (FamN n)) (up≼ (c₀ n))

Xω : L.Ordᶜ L.zero
Xω = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (L.lim P))

Xω≼ʷ : Xω ≼ NA.read W.T⁺ʷᵇ
Xω≼ʷ = l≼ λ where
  zero → ≼l 0 btbo-Tw2
  (suc n) → ≼l (suc n) (Ω₁n≼ n)
```

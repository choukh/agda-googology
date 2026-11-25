# 第 2 层的对角定理归约到 BTBO 链点 (第 0 项无前提)

验收文件. 参照的静态对角线 ψ₂(Ω_{ℓ₀}) = lim F₂ (`ψ₂ᴸ-lim`, `refl`). 编译定理: `F₂0⊴K` (第 0 项 ψ₂(Ω₁) 在门槛以上的一切分支 `K₂ a` 之下, 无前提); `chain→diag : Chain₂ → Diag₂ᵀ`; `X₃≼ᵇ : Chain₂ → X₃ ≼ NA.read W.TΛ`.
前提 `Chain₂`: 每个 F₂ (n+1) = ψ₂(Ω_{L_{n+1}}) 落在某个 `K₂ (suc (ξ m))` 之下, 是 [YiSyncDiag](YiSyncDiag.lagda.md) `chain₁′` 在第 2 层的对应; 未走通 (见回报). 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiStepDiag2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVOne using (V2; topᶜʷ)
open import OCF.Lean.YiShpSq using (s₂)
open import OCF.Lean.YiShpOmega using (cpT)
open import OCF.Lean.YiSyncDiag using (c₁)
open import OCF.Lean.YiL1Base using (ξ)
open import OCF.Align.YiLvVal2 using (T₀; ℓ₂; tr⁻≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiStepTree using (L2; s₃; σ₃; ψ₂; Tψ₂; K₂; X₃)
open import OCF.Lean.YiStepRel2
open import OCF.Lean.YiStepThree using (Diag₂ᵀ; X₃≼ᵈ)
```

## 1 参照的对角线与第 0 项

```agda
ψ₂ᴸ-lim : Σ (ℕ → L.Ordᶜ ℓ₂) (λ F → L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀) ≡ L.lim F)
ψ₂ᴸ-lim = _ , refl

F₂ : ℕ → L.Ordᶜ ℓ₂
F₂ n = proj₁ ψ₂ᴸ-lim n

F₂-form : ∀ n → F₂ n ≡ L.ψ (σ₃ L.zero) (λ q → L.lim n q) (L.Ω (S2.ℓ₀ L.[ n ]ᴵ))
F₂-form n = refl

σ₀ᵈ : L.Simᴵ L.zero S2.ℓ₀
σ₀ᵈ q = L.lim 0 (L.suc q)

hT : ∀ (x : Ext L2 zero) {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a →
  L.ψ (σ₃ L.zero) σ₀ᵈ y ⊴² W.Ψ L2 WL.w0 x a
hT x z≼ a q = ⊴²-cp Ω²⊴top (topᶜʷ L2 WL.w0 x a)
hT x {L.suc y} (s≼s p) (G.suc a) refl = suc-step² (L.ψ-≅ {p = σ₃ L.zero} {σ = σ₀ᵈ} {p′ = σ₃ L.zero} {σ′ = σ₀ᵈ}
  (L.≅ᴵ-refl _) (L.≅-refl⁰ y)) (hT x p a refl)
hT x {L.suc y} (s≼s p) G.top refl = suc-step² (L.ψ-≅ {p = σ₃ L.zero} {σ = σ₀ᵈ} {p′ = σ₃ L.zero} {σ′ = σ₀ᵈ}
  (L.≅ᴵ-refl _) (L.≅-refl⁰ y)) (hT x p G.zero refl)
hT x (≼l n p) (G.lim f) refl = ⊴l n (hT x p (f n) refl)
hT x (l≼ h) a q = l⊴ (λ n → hT x (h n) a q)
hT x (≼i {p = ()} z ez p) a q
hT x (i≼ {p = ()} h) a q
hT x (≼u {r = ()} p) a q
hT x (u≼ {r = ()} p) a q

F₂0⊴T : F₂ 0 ⊴² Tψ₂ G.top
F₂0⊴T = n0 (λ y a q → hT _ (≼-trans (tr⁻≼ y) q) a refl)

F₂0⊴K : ∀ a → Cp zero thr a → F₂ 0 ⊴² K₂ a
F₂0⊴K a c = ⊴²-cp F₂0⊴T (WL.Kfk-cp zero Tψ₂ (cpT zero (plus-weak zero G.top (W.Tw 2)) c))
```

## 2 归约

```agda
Chain₂ : Set
Chain₂ = ∀ n → Σ ℕ (λ m → F₂ (suc n) ⊴² K₂ (G.suc (ξ m)))

chain→diag : Chain₂ → Diag₂ᵀ
chain→diag h = dg F₂⊴K
  where
  F₂⊴K : ∀ n a → Cp zero thr a → F₂ n ⊴² K₂ a
  F₂⊴K zero a c = F₂0⊴K a c
  F₂⊴K (suc n) a c = ⊴²-cp (proj₂ (h n))
    (WL.Kfk-cp zero Tψ₂ (cpT zero (add-cp zero G.lc dnLc G.top (c₁ (proj₁ (h n)))) c))

X₃≼ᵇ : Chain₂ → X₃ ≼ NA.read W.TΛ
X₃≼ᵇ h = X₃≼ᵈ (chain→diag h)
```

## 3 `Chain₂` 的链点上的派发 (m = 0)

根位置的源层号是 ℕ 极限; 目标层 2 与目标层 1 的派发在那里都折叠 (层号不低于目标). 第 1 层的 `chain₁′` 用的是同形的链点 `K₁ (suc (ξ m))`; m = 0 时那里目标层 1 的派发同样折叠 (`root-fold₁`).

```agda
IsLimL : LF → Set
IsLimL (lim _) = ⊤
IsLimL _ = ⊥

lim-src₀ : IsLimL (lev (tw 2) (WL.nrmk zero (G.suc (ξ 0)) , WL.nrmk-lgl zero (G.suc (ξ 0)) , inj₁ tt))
lim-src₀ = tt

root-fold₂ : W.cmpw V2 s₃ (WL.nrmk zero (G.suc (ξ 0)) , WL.nrmk-lgl zero (G.suc (ξ 0)) , inj₁ tt) ≡ fold
root-fold₂ = refl

root-fold₁ : W.cmpw V2 s₂ (WL.nrmk zero (G.suc (ξ 0)) , WL.nrmk-lgl zero (G.suc (ξ 0)) , inj₁ tt) ≡ fold
root-fold₁ = refl
```

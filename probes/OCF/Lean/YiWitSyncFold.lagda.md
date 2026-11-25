# 关系 `⊴⁺` 经前缀 Ω_{ℓ₀} 送到值, 并经第 1 层的 ψ 保持 (搬到收缩见证的折叠)

验收文件. [YiSyncFold](YiSyncFold.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitSyncFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiWitVOne using (V2; Ψ₀; up≼)
open import OCF.Lean.YiWitVBtbo using (btbo-Tw2)
open import OCF.Lean.YiWitShpOne using (σA)
open import OCF.Lean.YiWitShpSq using (s₂; G₂; A; Asuc; Atop; ψ₁)
open import OCF.Lean.YiWitShpEps using (G₂mono; G₂suc; fold0; module NodeP)
open import OCF.Lean.YiWitShpTwo using (σB)
open import OCF.Align.YiLvVal2 using (T₀; T₁; s≅⁻; l≅⁻; lᵢ≅⁻; tr⁻≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.Lean.YiWitSyncRel
open import OCF.Lean.YiWitSyncDiag using (Diag)
```

## 1 目标层 0: `fold1⁺`

`dg` 情形取链的第 1 点 `top + Ψ₀ (G₂ (g top))`, 它在门槛 `top + Tw 2` 之上.

```agda
fold1⁺ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA X) ≼ NA.read (Ψ₀ (G₂ η))
fold1⁺ z⊴ s = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
fold1⁺ {η = G.suc η} (s⊴s p) s = ≼-trans (NA.suc-lower (Ψ₀ (G₂ η)) (fold1⁺ p (s≅⁻ s))) (up≼ (G₂suc η))
fold1⁺ (⊴s p) s = ≼-trans (fold1⁺ p s) (up≼ (G₂mono (inj₂ (inj₁ refl))))
fold1⁺ (⊴l n p) s = ≼l n (fold1⁺ p s)
fold1⁺ (l⊴ h) s = l≼ (λ n → fold1⁺ (h n) (l≅⁻ s n))
fold1⁺ (⊴b h) s = ≼-trans (fold1⁺ h s) (up≼ (inj₂ (inj₁ refl)))
fold1⁺ {η = G.lc (inj₁ _) g} (nd {f = f} h) s =
  NodeP.result f (lᵢ≅⁻ s) g (λ y a q → fold1⁺ (h y a q) (lᵢ≅⁻ s y))
fold1⁺ (nt {f = f} h) s =
  NodeP.result f (lᵢ≅⁻ s) (λ a → G.em tt a) (λ y a q → fold1⁺ (h y a q) (lᵢ≅⁻ s y))
fold1⁺ (u⊴ p) s = fold0 p
fold1⁺ {η = G.lc (inj₁ _) g} (dg h) s = l≼ (λ n → ≼l 1 (fold1⁺ (h n _
  (add-cp zero G.lc dnLc G.top (W.Ψ-cp zero V2 (λ _ → fold) (plus-weak (tw 2) G.top _)))) (l≅⁻ s n)))
fold1⁺ (≅⊴ e p) s = ≼-trans (≅→≼ (L.ψ⁰-≅ (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀) e)))
  (fold1⁺ p (L.≅-trans (L.≅-sym e) e))
```

## 2 目标层 1: `Fold₁ᴾ`

```agda
ψ₀ᴿ-self : ∀ (y : T₀) → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y)
  L.≅ L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y)
ψ₀ᴿ-self y = L.ψ-≅ {p = σB L.zero} {σ = λ r → r} {p′ = σB L.zero} {σ′ = λ r → r} (L.≅ᴵ-refl _)
  (L.add-≅ {σ = S2.σ₁} {σ′ = S2.σ₁} (L.Ω-refl S2.ℓ₀) (L.≅-refl⁰ y))

ψ₁ᴿ-≅ : ∀ {X Y : T₁} → X L.≅ Y → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA X)
  L.≅ L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA Y)
ψ₁ᴿ-≅ e = L.ψ-≅ {p = σB L.zero} {σ = λ r → r} {p′ = σB L.zero} {σ′ = λ r → r} (L.≅ᴵ-refl _)
  (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀) e)

Z⊴ : ∀ (B : Raw (tw 2)) → L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴⁺ ψ₁ (plus (tw 2) G.top B)
Z⊴ B = ⊴⁺-cp Diag (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (plus-weak (tw 2) G.top B))

CtxA : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a →
  L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ⊴⁺ ψ₁ (A a)
CtxA z≼ a q = Z⊴ _
CtxA {L.suc y} (s≼s p) (G.suc a) refl =
  ⊴⁺-cp (suc-step⁺ (ψ₀ᴿ-self y) (CtxA p a refl)) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (Asuc a))
CtxA {L.suc y} (s≼s p) G.top refl =
  ⊴⁺-cp (suc-step⁺ (ψ₀ᴿ-self y) (CtxA p G.zero refl)) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) Atop)
CtxA (≼l n p) (G.lim f) refl = ⊴l n (CtxA p (f n) refl)
CtxA (l≼ h) a q = l⊴ (λ n → CtxA (h n) a q)
CtxA (≼i {p = ()} x ex p) a q
CtxA (i≼ {p = ()} h) a q
CtxA (≼u {r = ()} p) a q
CtxA (u≼ {r = ()} p) a q

Fold₀ᴾ : ∀ {y : T₀} {η} → y NA.⊴ η → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ⊴⁺ ψ₁ (G₂ η)
Fold₀ᴾ NA.z⊴ = Z⊴ _
Fold₀ᴾ {L.suc y} {G.suc η} (NA.s⊴s p) =
  ⊴⁺-cp (suc-step⁺ (ψ₀ᴿ-self y) (Fold₀ᴾ p)) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (G₂suc η))
Fold₀ᴾ {η = G.suc η} (NA.⊴s p) =
  ⊴⁺-cp (Fold₀ᴾ p) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (G₂mono {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
Fold₀ᴾ (NA.⊴l n p) = ⊴l n (Fold₀ᴾ p)
Fold₀ᴾ (NA.l⊴ h) = l⊴ (λ n → Fold₀ᴾ (h n))
Fold₀ᴾ (NA.⊴b h) = ⊴b (Fold₀ᴾ h)
Fold₀ᴾ (NA.em⊴ {a = a} q) = CtxA q a refl

Fold₁ᴾ : ∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X →
  L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA X) ⊴⁺ ψ₁ (G₂ η)
Fold₁ᴾ z⊴ s = Z⊴ _
Fold₁ᴾ {L.suc X} {G.suc η} (s⊴s p) s =
  ⊴⁺-cp (suc-step⁺ (ψ₁ᴿ-≅ (s≅⁻ s)) (Fold₁ᴾ p (s≅⁻ s))) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (G₂suc η))
Fold₁ᴾ {η = G.suc η} (⊴s p) s =
  ⊴⁺-cp (Fold₁ᴾ p s) (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (G₂mono {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
Fold₁ᴾ (⊴l n p) s = ⊴l n (Fold₁ᴾ p s)
Fold₁ᴾ (l⊴ h) s = l⊴ (λ n → Fold₁ᴾ (h n) (l≅⁻ s n))
Fold₁ᴾ (⊴b h) s = ⊴b (Fold₁ᴾ h s)
Fold₁ᴾ (nd h) s = nd (λ y a q →
  Fold₁ᴾ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ y)))
Fold₁ᴾ (nt h) s = nd (λ y a q →
  Fold₁ᴾ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ y)))
Fold₁ᴾ (u⊴ p) s = Fold₀ᴾ p
Fold₁ᴾ (dg h) s = dg (λ n a c → Fold₁ᴾ (h n a c) (l≅⁻ s n))
Fold₁ᴾ (≅⊴ e p) s = ≅⊴ (ψ₁ᴿ-≅ e) (Fold₁ᴾ p (L.≅-trans (L.≅-sym e) e))
```

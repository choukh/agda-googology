# 关系 `⊴²` 经前缀 Ω_{ℓ₀} 送到目标层 2, 1, 0 (以第 2 层的对角定理为模块参数)

验收文件. 模块 `F2 (Diag₂ : …)`: 参数是第 2 层的对角定理 (静态对角线 ψ₂(Ω_{ℓ₀}) 在 `ψ₂ top` 之下), 是唯一的前提. 编译定理: `Fold22` (目标层 2, ψ₂(Ω_{ℓ₀}+X) 不高于 `ψ₂ (G₃ η)`), `Fold21` (目标层 1, 关系 `⊴⁺`), `fold2²` (目标层 0, 值), 各带第 0, 1 层参照的部件; 层号 1 的嵌入交给 [YiStepPfx](YiStepPfx.lagda.md) 的 `P1 P₃′`.
层号 1 的结点在目标层 1, 0 上折叠成层号 1 的链 (`Node1`), 层号 0 的结点在目标层 0 上折叠成层号 0 的链 (`Node0`). 只是下界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiStepFold2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVOne using (V2; Ψ₀; up≼)
open import OCF.Lean.YiDlVBtbo using (btbo-Tw2)
open import OCF.Lean.YiShpOne using (σA)
open import OCF.Lean.YiShpSq using (s₂; ψ₁; sucg)
open import OCF.Lean.YiShpTwo using (σB)
open import OCF.Align.YiLvVal2 using (T₀; T₁; ℓ₁; ℓ₂; s≅⁻; l≅⁻; lᵢ≅⁻; tr⁻≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
import OCF.Lean.YiSyncRel as S
open S using (_⊴⁺_; ⊴⁺-cp; ⊴⁺-+ˡ; suc-step⁺; ⊴→⊴⁺)
open import OCF.Lean.YiSyncDiag using (Diag)
open import OCF.Lean.YiStepTree
open import OCF.Lean.YiStepPfx using (Pfx; P₃′; mG₃′; module P1)
open import OCF.Lean.YiStepRel2
```

## 1 部件: Sim, `≅` 的反演, 分支族的单调

```agda
σ₃″ : L.Simᴵ ℓ₁ S2.ℓ₀
σ₃″ q = σ₃′ (L.suc q)

σ₃‴ : L.Simᴵ L.zero S2.ℓ₀
σ₃‴ q = σ₃″ (L.suc q)

upˡ⁻ : ∀ {k ℓ′} {x : L.Ordᶜ k} {b : L.Ordᶜ ℓ′} → L.up {k = k} L.zero x L.≅ b → x L.≅ b
upˡ⁻ (L.upˡ e) = e
upˡ⁻ (L.upʳ {r = L.zero} e) = L.upʳ {r = L.zero} (upˡ⁻ e)
upˡ⁻ (L.upʳ {r = L.self n} e) = L.upʳ {r = L.self n} (upˡ⁻ e)

upʳ⁻ : ∀ {k ℓ} {a : L.Ordᶜ ℓ} {y : L.Ordᶜ k} → a L.≅ L.up {k = k} L.zero y → a L.≅ y
upʳ⁻ (L.upʳ e) = e
upʳ⁻ (L.upˡ {r = L.zero} e) = L.upˡ {r = L.zero} (upʳ⁻ e)
upʳ⁻ (L.upˡ {r = L.self n} e) = L.upˡ {r = L.self n} (upʳ⁻ e)

u≅⁻ : ∀ {y y′ : T₁} → L.up {k = ℓ₁} L.zero y L.≅ L.up {k = ℓ₁} L.zero y′ → y L.≅ y′
u≅⁻ e = upʳ⁻ (upˡ⁻ e)

lᵢ≅⁻₁ : ∀ {f f′ : T₁ → T₂} → L.limᵢ {i = ℓ₁} L.zero f L.≅ L.limᵢ {i = ℓ₁} L.zero f′ →
  ∀ y y′ → y L.≅ y′ → f y L.≅ f′ y′
lᵢ≅⁻₁ (L.lᵢ≅ e h) y y′ d = h y y′ d

lᵢ≅⁻₀ : ∀ {f f′ : T₀ → T₂} → L.limᵢ {i = L.zero} (L.suc L.zero) f L.≅ L.limᵢ {i = L.zero} (L.suc L.zero) f′ →
  ∀ y → f y L.≅ f′ y
lᵢ≅⁻₀ (L.lᵢ≅ e h) y = h y y (L.≅-refl⁰ y)

trs : ∀ {y : T₁} → y L.≅ y → L.tr⁻ (L.s≅ L.z≅) y L.≅ L.tr⁻ (L.s≅ L.z≅) y
trs t = L.≅-trans (L.≅-sym (L.≅-tr⁻ (L.s≅ L.z≅) t)) (L.≅-tr⁻ (L.s≅ L.z≅) t)

tr⊴ : ∀ {y : T₁} {a} → y S.⊴⁺ a → y L.≅ y → L.tr⁻ (L.s≅ L.z≅) y S.⊴⁺ a
tr⊴ q t = S.≅⊴ (L.≅-sym (L.≅-tr⁻ (L.s≅ L.z≅) t)) q

cg₂ : ∀ {k} (σ : L.Simᴵ k S2.ℓ₀) {X Y : L.Ordᶜ k} → X L.≅ Y →
  L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ X) L.≅ L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ Y)
cg₂ σ e = L.ψ-≅ {p = σ₃ L.zero} {σ = λ r → r} {p′ = σ₃ L.zero} {σ′ = λ r → r} (L.≅ᴵ-refl _)
  (L.add-≅ {σ = σ} {σ′ = σ} (L.Ω-refl S2.ℓ₀) e)

cv₁ : ∀ {k k′} (σ : L.Simᴵ k S2.ℓ₀) (σ′ : L.Simᴵ k′ S2.ℓ₀) {X : L.Ordᶜ k} {Y : L.Ordᶜ k′} → X L.≅ Y →
  L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ X) L.≅ L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ′ Y)
cv₁ σ σ′ e = L.ψ-≅ {p = σB L.zero} {σ = λ r → r} {p′ = σB L.zero} {σ′ = λ r → r} (L.≅ᴵ-refl _)
  (L.add-≅ {σ = σ} {σ′ = σ′} (L.Ω-refl S2.ℓ₀) e)

cv₀ : ∀ {k k′} (σ : L.Simᴵ k S2.ℓ₀) (σ′ : L.Simᴵ k′ S2.ℓ₀) {X : L.Ordᶜ k} {Y : L.Ordᶜ k′} → X L.≅ Y →
  L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ X) L.≅ L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ′ Y)
cv₀ σ σ′ e = L.ψ⁰-≅ (L.add-≅ {σ = σ} {σ′ = σ′} (L.Ω-refl S2.ℓ₀) e)

mG₃ : ∀ {a b} → Cp L2 a b → Cp (tw 2) (G₃ a) (G₃ b)
mG₃ c = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc K₀ (W.Ψ-cp (tw 2) (WL.ws (WL.ws WL.w0)) _ c))

sG₃ : ∀ η → Cp (tw 2) (G.suc (G₃ η)) (G₃ (G.suc η))
sG₃ η = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc K₀ (sucg (WL.ws (WL.ws WL.w0)) _ η))

cp₂ : ∀ {A B} → Cp (tw 2) A B → Cp L2 (ψ₂ A) (ψ₂ B)
cp₂ c = W.Ψ-cp L2 V2 (W.cmpw V2 s₃) c

cp₁ : ∀ {A B} → Cp (tw 2) A B → Cp (suc zero) (ψ₁ A) (ψ₁ B)
cp₁ c = W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) c

thrp : ∀ ξ → Cp zero thr (plus zero G.top (Ψ₀ (plus (tw 2) G.top ξ)))
thrp ξ = add-cp zero G.lc dnLc G.top (W.Ψ-cp zero V2 (λ _ → fold) (plus-weak (tw 2) G.top ξ))

module Q = P1 P₃′
```

## 2 目标层 2

```agda
module F2 (Diag₂ : L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴² ψ₂ G.top) where

  Z2 : ∀ ξ → L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴² ψ₂ (plus (tw 2) G.top ξ)
  Z2 ξ = ⊴²-cp Diag₂ (cp₂ (plus-weak (tw 2) G.top ξ))

  Ctx2 : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a →
    L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃‴ y) ⊴² ψ₂ (G₃″ a)
  Ctx2 z≼ a q = Z2 _
  Ctx2 {L.suc y} (s≼s p) (G.suc a) refl =
    ⊴²-cp (suc-step² (cg₂ σ₃‴ (L.≅-refl⁰ y)) (Ctx2 p a refl)) (cp₂ (Pfx.sA P₃′ a))
  Ctx2 {L.suc y} (s≼s p) G.top refl =
    ⊴²-cp (suc-step² (cg₂ σ₃‴ (L.≅-refl⁰ y)) (Ctx2 p G.zero refl)) (cp₂ (Pfx.tA P₃′))
  Ctx2 (≼l n p) (G.lim f) refl = ⊴l n (Ctx2 p (f n) refl)
  Ctx2 (l≼ h) a q = l⊴ (λ n → Ctx2 (h n) a q)
  Ctx2 (≼i {p = ()} x ex p) a q
  Ctx2 (i≼ {p = ()} h) a q
  Ctx2 (≼u {r = ()} p) a q
  Ctx2 (u≼ {r = ()} p) a q

  Fold02 : ∀ {y : T₀} {η} → y NA.⊴ η → L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃‴ y) ⊴² ψ₂ (G₃′ η)
  Fold02 NA.z⊴ = Z2 _
  Fold02 {L.suc y} {G.suc η} (NA.s⊴s p) =
    ⊴²-cp (suc-step² (cg₂ σ₃‴ (L.≅-refl⁰ y)) (Fold02 p)) (cp₂ (Pfx.sG P₃′ η))
  Fold02 {η = G.suc η} (NA.⊴s p) = ⊴²-cp (Fold02 p) (cp₂ (mG₃′ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold02 (NA.⊴l n p) = ⊴l n (Fold02 p)
  Fold02 (NA.l⊴ h) = l⊴ (λ n → Fold02 (h n))
  Fold02 (NA.⊴b h) = ⊴b₀ (Fold02 h)
  Fold02 (NA.em⊴ {a = a} q) = Ctx2 q a refl

  Fold12 : ∀ {y : T₁} {η} → y ⊴⁺ η → y L.≅ y →
    L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃″ y) ⊴² ψ₂ (G₃′ η)
  Fold12 S.z⊴ s = Z2 _
  Fold12 {L.suc y} {G.suc η} (S.s⊴s p) s =
    ⊴²-cp (suc-step² (cg₂ σ₃″ (s≅⁻ s)) (Fold12 p (s≅⁻ s))) (cp₂ (Pfx.sG P₃′ η))
  Fold12 {η = G.suc η} (S.⊴s p) s = ⊴²-cp (Fold12 p s) (cp₂ (mG₃′ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold12 (S.⊴l n p) s = ⊴l n (Fold12 p s)
  Fold12 (S.l⊴ h) s = l⊴ (λ n → Fold12 (h n) (l≅⁻ s n))
  Fold12 (S.⊴b h) s = ⊴b₀ (Fold12 h s)
  Fold12 (S.nd h) s = n0 (λ z a q → Fold12 (h (L.tr⁻ L.z≅ z) a (≼-trans (tr⁻≼ z) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ z)))
  Fold12 (S.nt h) s = n0 (λ z a q → Fold12 (h (L.tr⁻ L.z≅ z) a (≼-trans (tr⁻≼ z) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ z)))
  Fold12 (S.u⊴ p) s = Fold02 p
  Fold12 (S.dg h) s = dg (λ n a c → Fold12 (h n a c) (l≅⁻ s n))
  Fold12 (S.≅⊴ e p) s = ≅⊴ (cg₂ σ₃″ e) (Fold12 p (L.≅-trans (L.≅-sym e) e))

  Fold0²2 : ∀ {y : T₀} {η} → y ⊴² η → L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃‴ y) ⊴² ψ₂ (G₃ η)
  Fold0²2 z⊴ = Z2 _
  Fold0²2 {L.suc y} {G.suc η} (s⊴s p) = ⊴²-cp (suc-step² (cg₂ σ₃‴ (L.≅-refl⁰ y)) (Fold0²2 p)) (cp₂ (sG₃ η))
  Fold0²2 {η = G.suc η} (⊴s p) = ⊴²-cp (Fold0²2 p) (cp₂ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold0²2 (⊴l n p) = ⊴l n (Fold0²2 p)
  Fold0²2 (l⊴ h) = l⊴ (λ n → Fold0²2 (h n))
  Fold0²2 (⊴b₁ h) = ⊴b₁ (Fold0²2 h)
  Fold0²2 (⊴b₀ h) = ⊴b₀ (Fold0²2 h)
  Fold0²2 (e0 q) = Fold02 q
  Fold0²2 (dg h) = dg (λ n a c → Fold0²2 (h n a c))
  Fold0²2 (≅⊴ e p) = ≅⊴ (cg₂ σ₃‴ e) (Fold0²2 p)

  Fold1²2 : ∀ {y : T₁} {η} → y ⊴² η → y L.≅ y →
    L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃″ y) ⊴² ψ₂ (G₃ η)
  Fold1²2 z⊴ s = Z2 _
  Fold1²2 {L.suc y} {G.suc η} (s⊴s p) s =
    ⊴²-cp (suc-step² (cg₂ σ₃″ (s≅⁻ s)) (Fold1²2 p (s≅⁻ s))) (cp₂ (sG₃ η))
  Fold1²2 {η = G.suc η} (⊴s p) s = ⊴²-cp (Fold1²2 p s) (cp₂ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold1²2 (⊴l n p) s = ⊴l n (Fold1²2 p s)
  Fold1²2 (l⊴ h) s = l⊴ (λ n → Fold1²2 (h n) (l≅⁻ s n))
  Fold1²2 (⊴b₁ h) s = ⊴b₁ (Fold1²2 h s)
  Fold1²2 (⊴b₀ h) s = ⊴b₀ (Fold1²2 h s)
  Fold1²2 (n0′ h) s = n0 (λ z a q → Fold1²2 (h (L.tr⁻ L.z≅ z) a (≼-trans (tr⁻≼ z) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ z)))
  Fold1²2 (e1 q) s = Fold12 q s
  Fold1²2 (u0 p) s = Fold0²2 p
  Fold1²2 (dg h) s = dg (λ n a c → Fold1²2 (h n a c) (l≅⁻ s n))
  Fold1²2 (≅⊴ e p) s = ≅⊴ (cg₂ σ₃″ e) (Fold1²2 p (L.≅-trans (L.≅-sym e) e))

  Fold22 : ∀ {X : T₂} {η} → X ⊴² η → X L.≅ X →
    L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃′ X) ⊴² ψ₂ (G₃ η)
  Fold22 z⊴ s = Z2 _
  Fold22 {L.suc X} {G.suc η} (s⊴s p) s =
    ⊴²-cp (suc-step² (cg₂ σ₃′ (s≅⁻ s)) (Fold22 p (s≅⁻ s))) (cp₂ (sG₃ η))
  Fold22 {η = G.suc η} (⊴s p) s = ⊴²-cp (Fold22 p s) (cp₂ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold22 (⊴l n p) s = ⊴l n (Fold22 p s)
  Fold22 (l⊴ h) s = l⊴ (λ n → Fold22 (h n) (l≅⁻ s n))
  Fold22 (⊴b₁ h) s = ⊴b₁ (Fold22 h s)
  Fold22 (⊴b₀ h) s = ⊴b₀ (Fold22 h s)
  Fold22 (n1 h) s = n1 (λ y a q t →
    Fold22 (h (L.tr⁻ (L.s≅ L.z≅) y) a (tr⊴ q t) (trs t)) (lᵢ≅⁻₁ s _ _ (trs t)))
  Fold22 (t1 h) s = n1 (λ y a q t →
    Fold22 (h (L.tr⁻ (L.s≅ L.z≅) y) a (tr⊴ q t) (trs t)) (lᵢ≅⁻₁ s _ _ (trs t)))
  Fold22 (n0 h) s = n0 (λ y a q → Fold22 (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (lᵢ≅⁻₀ s (L.tr⁻ L.z≅ y)))
  Fold22 (u1 p) s = Fold1²2 p (u≅⁻ s)
  Fold22 (dg h) s = dg (λ n a c → Fold22 (h n a c) (l≅⁻ s n))
  Fold22 (≅⊴ e p) s = ≅⊴ (cg₂ σ₃′ e) (Fold22 p (L.≅-trans (L.≅-sym e) e))
```

## 3 目标层 1

```agda
  Z1 : ∀ ξ → L.ψ (σB L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴⁺ ψ₁ (plus (tw 2) G.top ξ)
  Z1 ξ = ⊴⁺-cp Diag (cp₁ (plus-weak (tw 2) G.top ξ))

  Fold0²1 : ∀ {y : T₀} {η} → y ⊴² η → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃‴ y) ⊴⁺ ψ₁ (G₃ η)
  Fold0²1 z⊴ = Z1 _
  Fold0²1 {L.suc y} {G.suc η} (s⊴s p) = ⊴⁺-cp (suc-step⁺ (cv₁ σ₃‴ σ₃‴ (L.≅-refl⁰ y)) (Fold0²1 p)) (cp₁ (sG₃ η))
  Fold0²1 {η = G.suc η} (⊴s p) = ⊴⁺-cp (Fold0²1 p) (cp₁ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold0²1 (⊴l n p) = S.⊴l n (Fold0²1 p)
  Fold0²1 (l⊴ h) = S.l⊴ (λ n → Fold0²1 (h n))
  Fold0²1 (⊴b₁ h) = S.⊴l 0 (Fold0²1 h)
  Fold0²1 (⊴b₀ h) = S.⊴b (Fold0²1 h)
  Fold0²1 {y = y} (e0 q) = S.≅⊴ (cv₁ σ₃‴ S2.σ₁ (L.≅-refl⁰ y)) (Q.Fold₀ᴳ q)
  Fold0²1 (dg h) = S.dg (λ n a c → Fold0²1 (h n a c))
  Fold0²1 (≅⊴ e p) = S.≅⊴ (cv₁ σ₃‴ σ₃‴ e) (Fold0²1 p)

  Fold1²1 : ∀ {y : T₁} {η} → y ⊴² η → y L.≅ y →
    L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃″ y) ⊴⁺ ψ₁ (G₃ η)
  Fold1²1 z⊴ s = Z1 _
  Fold1²1 {L.suc y} {G.suc η} (s⊴s p) s =
    ⊴⁺-cp (suc-step⁺ (cv₁ σ₃″ σ₃″ (s≅⁻ s)) (Fold1²1 p (s≅⁻ s))) (cp₁ (sG₃ η))
  Fold1²1 {η = G.suc η} (⊴s p) s = ⊴⁺-cp (Fold1²1 p s) (cp₁ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold1²1 (⊴l n p) s = S.⊴l n (Fold1²1 p s)
  Fold1²1 (l⊴ h) s = S.l⊴ (λ n → Fold1²1 (h n) (l≅⁻ s n))
  Fold1²1 (⊴b₁ h) s = S.⊴l 0 (Fold1²1 h s)
  Fold1²1 (⊴b₀ h) s = S.⊴b (Fold1²1 h s)
  Fold1²1 (n0′ h) s = S.nd (λ z a q → Fold1²1 (h (L.tr⁻ L.z≅ z) a (≼-trans (tr⁻≼ z) q)) (lᵢ≅⁻ s (L.tr⁻ L.z≅ z)))
  Fold1²1 (e1 q) s = S.≅⊴ (cv₁ σ₃″ σA s) (Q.Fold₁ᴳ q s)
  Fold1²1 (u0 p) s = Fold0²1 p
  Fold1²1 (dg h) s = S.dg (λ n a c → Fold1²1 (h n a c) (l≅⁻ s n))
  Fold1²1 (≅⊴ e p) s = S.≅⊴ (cv₁ σ₃″ σ₃″ e) (Fold1²1 p (L.≅-trans (L.≅-sym e) e))

  module Node1 (f : T₁ → T₂) (g : NA.R₁ → R₂) (sf : ∀ y → y L.≅ y → f y L.≅ f y)
    (hm : ∀ (y : T₁) a → y ⊴⁺ a → y L.≅ y →
      L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃′ (f y)) ⊴⁺ ψ₁ (G₃ (g a))) where
    c : ℕ → T₁
    c = iterᴸ (λ x → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃′ (f x))) (L.Ω ℓ₁)

    δ : ℕ → NA.R₁
    δ = chain (suc zero) (λ η → ψ₁ (G₃ (g η)))

    sc : ∀ n → c n L.≅ c n
    sc zero = L.Ω-refl ℓ₁
    sc (suc n) = cv₁ σ₃′ σ₃′ (sf (c n) (sc n))

    sync : ∀ n → c n ⊴⁺ δ n
    sync zero = ⊴→⊴⁺ NA.Ω⊴top
    sync (suc n) = ⊴⁺-+ˡ (δ n) (hm (c n) (δ n) (sync n) (sc n))

  Fold21 : ∀ {X : T₂} {η} → X ⊴² η → X L.≅ X →
    L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃′ X) ⊴⁺ ψ₁ (G₃ η)
  Fold21 z⊴ s = Z1 _
  Fold21 {L.suc X} {G.suc η} (s⊴s p) s =
    ⊴⁺-cp (suc-step⁺ (cv₁ σ₃′ σ₃′ (s≅⁻ s)) (Fold21 p (s≅⁻ s))) (cp₁ (sG₃ η))
  Fold21 {η = G.suc η} (⊴s p) s = ⊴⁺-cp (Fold21 p s) (cp₁ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  Fold21 (⊴l n p) s = S.⊴l n (Fold21 p s)
  Fold21 (l⊴ h) s = S.l⊴ (λ n → Fold21 (h n) (l≅⁻ s n))
  Fold21 (⊴b₁ h) s = S.⊴l 0 (Fold21 h s)
  Fold21 (⊴b₀ h) s = S.⊴b (Fold21 h s)
  Fold21 {η = G.lc (inj₁ _) g} (n1 {f = f} h) s = S.l⊴ (λ n → S.⊴l n (Fold21 (h (N.c n) (N.δ n) (N.sync n) (N.sc n)) (lᵢ≅⁻₁ s _ _ (N.sc n))))
    where module N = Node1 f g (λ y t → lᵢ≅⁻₁ s y y t) (λ y a q t → Fold21 (h y a q t) (lᵢ≅⁻₁ s y y t))
  Fold21 (t1 {f = f} h) s = S.l⊴ (λ n → S.⊴l n (Fold21 (h (N.c n) (N.δ n) (N.sync n) (N.sc n)) (lᵢ≅⁻₁ s _ _ (N.sc n))))
    where module N = Node1 f (λ a → G.em tt a) (λ y t → lᵢ≅⁻₁ s y y t) (λ y a q t → Fold21 (h y a q t) (lᵢ≅⁻₁ s y y t))
  Fold21 (n0 h) s = S.nd (λ y a q → Fold21 (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)) (lᵢ≅⁻₀ s (L.tr⁻ L.z≅ y)))
  Fold21 (u1 p) s = Fold1²1 p (u≅⁻ s)
  Fold21 (dg h) s = S.dg (λ n a c → Fold21 (h n a c) (l≅⁻ s n))
  Fold21 (≅⊴ e p) s = S.≅⊴ (cv₁ σ₃′ σ₃′ e) (Fold21 p (L.≅-trans (L.≅-sym e) e))
```

## 4 目标层 0

```agda
  module Node0 (q : L.zero L.<ᴵ S2.ℓ₀) (Fz : T₀ → L.Ordᶜ S2.ℓ₀) (sF : ∀ y → Fz y L.≅ Fz y) (g : R → R₂)
    (hm : ∀ (y : T₀) a → y ≼ NA.read a → L.ψ⁰ (Fz y) ≼ NA.read (Ψ₀ (G₃ (g a)))) where
    c : ℕ → T₀
    c = iterᴸ (λ z → L.ψ q (λ r → r) (Fz z)) (L.suc L.zero)

    δ : ℕ → R
    δ = chain zero (λ ζ → Ψ₀ (G₃ (g ζ)))

    sync : ∀ n → c n ≼ NA.read (δ n)
    sync zero = ≼-refl _
    sync (suc n) = ≼-trans (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = q} {σ = λ r → r} (sF (c n)))))
      (NA.plus≽ (δ n) (Ψ₀ (G₃ (g (δ n)))) (hm (c n) (δ n) (sync n)))

  fold0² : ∀ {y : T₀} {η} → y ⊴² η → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃‴ y) ≼ NA.read (Ψ₀ (G₃ η))
  fold0² z⊴ = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
  fold0² {η = G.suc η} (s⊴s p) = ≼-trans (NA.suc-lower (Ψ₀ (G₃ η)) (fold0² p)) (up≼ (sG₃ η))
  fold0² {η = G.suc η} (⊴s p) = ≼-trans (fold0² p) (up≼ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  fold0² (⊴l n p) = ≼l n (fold0² p)
  fold0² (l⊴ h) = l≼ (λ n → fold0² (h n))
  fold0² {η = G.lc (inj₁ _) g} (⊴b₁ h) = ≼-trans (fold0² h) (up≼ (mG₃ {a = g G.top} {b = G.lc (inj₁ tt) g} (inj₂ (inj₁ refl))))
  fold0² {η = G.lc (inj₂ (inj₁ _)) g} (⊴b₀ h) =
    ≼-trans (fold0² h) (up≼ (mG₃ {a = g G.top} {b = G.lc (inj₂ (inj₁ tt)) g} (inj₂ (inj₁ refl))))
  fold0² {y = y} (e0 q) = ≼-trans (≅→≼ (cv₀ σ₃‴ S2.σ₁ (L.≅-refl⁰ y))) (Q.fold0ᴳ q)
  fold0² {η = G.lc (inj₂ (inj₁ _)) g} (dg h) = l≼ (λ n → ≼l 1 (fold0² (h n _ (thrp _))))
  fold0² (≅⊴ e p) = ≼-trans (≅→≼ (cv₀ σ₃‴ σ₃‴ e)) (fold0² p)

  fold1² : ∀ {y : T₁} {η} → y ⊴² η → y L.≅ y → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃″ y) ≼ NA.read (Ψ₀ (G₃ η))
  fold1² z⊴ s = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
  fold1² {η = G.suc η} (s⊴s p) s = ≼-trans (NA.suc-lower (Ψ₀ (G₃ η)) (fold1² p (s≅⁻ s))) (up≼ (sG₃ η))
  fold1² {η = G.suc η} (⊴s p) s = ≼-trans (fold1² p s) (up≼ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  fold1² (⊴l n p) s = ≼l n (fold1² p s)
  fold1² (l⊴ h) s = l≼ (λ n → fold1² (h n) (l≅⁻ s n))
  fold1² {η = G.lc (inj₁ _) g} (⊴b₁ h) s =
    ≼-trans (fold1² h s) (up≼ (mG₃ {a = g G.top} {b = G.lc (inj₁ tt) g} (inj₂ (inj₁ refl))))
  fold1² {η = G.lc (inj₂ (inj₁ _)) g} (⊴b₀ h) s =
    ≼-trans (fold1² h s) (up≼ (mG₃ {a = g G.top} {b = G.lc (inj₂ (inj₁ tt)) g} (inj₂ (inj₁ refl))))
  fold1² {η = G.lc (inj₂ (inj₁ _)) g} (n0′ {f = f} h) s = l≼ (λ n → ≼l n (fold1² (h (N.c n) (N.δ n) (N.sync n)) (lᵢ≅⁻ s (N.c n))))
    where module N = Node0 (σ₃″ L.zero) (λ z → L.add (L.Ω S2.ℓ₀) σ₃″ (f z))
            (λ z → L.add-≅ {σ = σ₃″} {σ′ = σ₃″} (L.Ω-refl S2.ℓ₀) (lᵢ≅⁻ s z)) g
            (λ z a q → fold1² (h z a q) (lᵢ≅⁻ s z))
  fold1² (e1 q) s = ≼-trans (≅→≼ (cv₀ σ₃″ σA s)) (Q.fold1ᴳ q s)
  fold1² (u0 p) s = fold0² p
  fold1² {η = G.lc (inj₂ (inj₁ _)) g} (dg h) s = l≼ (λ n → ≼l 1 (fold1² (h n _ (thrp _)) (l≅⁻ s n)))
  fold1² (≅⊴ e p) s = ≼-trans (≅→≼ (cv₀ σ₃″ σ₃″ e)) (fold1² p (L.≅-trans (L.≅-sym e) e))

  fold2² : ∀ {X : T₂} {η} → X ⊴² η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃′ X) ≼ NA.read (Ψ₀ (G₃ η))
  fold2² z⊴ s = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
  fold2² {η = G.suc η} (s⊴s p) s = ≼-trans (NA.suc-lower (Ψ₀ (G₃ η)) (fold2² p (s≅⁻ s))) (up≼ (sG₃ η))
  fold2² {η = G.suc η} (⊴s p) s = ≼-trans (fold2² p s) (up≼ (mG₃ {a = η} {b = G.suc η} (inj₂ (inj₁ refl))))
  fold2² (⊴l n p) s = ≼l n (fold2² p s)
  fold2² (l⊴ h) s = l≼ (λ n → fold2² (h n) (l≅⁻ s n))
  fold2² {η = G.lc (inj₁ _) g} (⊴b₁ h) s =
    ≼-trans (fold2² h s) (up≼ (mG₃ {a = g G.top} {b = G.lc (inj₁ tt) g} (inj₂ (inj₁ refl))))
  fold2² {η = G.lc (inj₂ (inj₁ _)) g} (⊴b₀ h) s =
    ≼-trans (fold2² h s) (up≼ (mG₃ {a = g G.top} {b = G.lc (inj₂ (inj₁ tt)) g} (inj₂ (inj₁ refl))))
  fold2² {η = G.lc (inj₁ _) g} (n1 {f = f} h) s =
    l≼ (λ n → ≼l n (fold2² (h (N.c n) (N.δ n) (N.sync n) (N.sc n)) (lᵢ≅⁻₁ s _ _ (N.sc n))))
    where module N = Node1 f g (λ y t → lᵢ≅⁻₁ s y y t) (λ y a q t → Fold21 (h y a q t) (lᵢ≅⁻₁ s y y t))
  fold2² (t1 {f = f} h) s =
    l≼ (λ n → ≼l n (fold2² (h (N.c n) (N.δ n) (N.sync n) (N.sc n)) (lᵢ≅⁻₁ s _ _ (N.sc n))))
    where module N = Node1 f (λ a → G.em tt a) (λ y t → lᵢ≅⁻₁ s y y t) (λ y a q t → Fold21 (h y a q t) (lᵢ≅⁻₁ s y y t))
  fold2² {η = G.lc (inj₂ (inj₁ _)) g} (n0 {f = f} h) s = l≼ (λ n → ≼l n (fold2² (h (N.c n) (N.δ n) (N.sync n)) (lᵢ≅⁻₀ s (N.c n))))
    where module N = Node0 (σ₃′ (L.suc L.zero)) (λ z → L.add (L.Ω S2.ℓ₀) σ₃′ (f z))
            (λ z → L.add-≅ {σ = σ₃′} {σ′ = σ₃′} (L.Ω-refl S2.ℓ₀) (lᵢ≅⁻₀ s z)) g
            (λ z a q → fold2² (h z a q) (lᵢ≅⁻₀ s z))
  fold2² (u1 p) s = fold1² p (u≅⁻ s)
  fold2² {η = G.lc (inj₂ (inj₁ _)) g} (dg h) s = l≼ (λ n → ≼l 1 (fold2² (h n _ (thrp _)) (l≅⁻ s n)))
  fold2² (≅⊴ e p) s = ≼-trans (≅→≼ (cv₀ σ₃′ σ₃′ e)) (fold2² p (L.≅-trans (L.≅-sym e) e))
```

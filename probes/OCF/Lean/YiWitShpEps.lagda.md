# `T⁺ʷ` 不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) (无前提) (搬到收缩见证的折叠)

验收文件. [YiShpEps](YiShpEps.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitShpEps where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open NA using (_⊴_; z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; nt; em⊴; u⊴; ⊴-+ˡ; ⊴-+ʳ; Ω⊴top; suc-step; R₁)
open import OCF.Lean.YiWitVOne using (V2; Ψ₀; topᶜʷ; up≼; Tt)
open import OCF.Lean.YiWitVBtbo using (btbo-Tw2; Vw)
open import OCF.Lean.YiWitShpOne using (σA)
open import OCF.Lean.YiWitShpSq using (s₂; s₀″; gm₂; G₂; A; Asuc; Atop; ψ₁; Y; Bq; sucg; node≼T)
open import OCF.Align.YiLvVal2 using (T₀; T₁; ℓ₁; Ψ₁; s≅⁻; l≅⁻; lᵢ≅⁻; tr⁻≼) renaming (Ψ₀ to Ψ₀ᴸ)
open import OCF.Align.YiLvValBase using (γ; γ-self)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Align.Stage2 as S2
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 目标层 1 的折叠 (根位置保留时)

照 [YiNextAcc](YiNextAcc.lagda.md) §4 写在 [YiDlFold](YiDlFold.lagda.md) 的折叠上, 对派发参数化, 只要它在根位置保留 (`kx`).

```agda
module Lv1 (x : Ext (suc zero) (suc zero)) (kx : x (inj₁ tt) ≡ keep (inj₁ tt) refl) where
  Φx : R₁ → R₁
  Φx = W.Ψ (suc zero) (WL.ws WL.w0) x

  node : ∀ gm gk → Ψn (suc zero) zero (x (inj₁ tt)) gm gk ≡ G.lc (inj₁ tt) gm
  node gm gk = cong (λ w → Ψn (suc zero) zero w gm gk) kx

  Ω⊴Φ₀ : ∀ x′ a → L.Ω ℓ₁ ⊴ W.Ψ (suc zero) WL.w0 x′ a
  Ω⊴Φ₀ x′ G.zero = Ω⊴top
  Ω⊴Φ₀ x′ (G.suc a) = ⊴l 0 (Ω⊴Φ₀ x′ a)
  Ω⊴Φ₀ x′ (G.lim f) = ⊴l 0 (Ω⊴Φ₀ x′ (f 0))
  Ω⊴Φ₀ x′ (G.lc () g)
  Ω⊴Φ₀ x′ (G.em () a)
  Ω⊴Φ₀ x′ G.top = ⊴l 0 Ω⊴top

  Ψ₀⊴Φ₀ : ∀ x′ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a → Ψ₀ᴸ y ⊴ W.Ψ (suc zero) WL.w0 x′ a
  Ψ₀⊴Φ₀ x′ z≼ a q = Ω⊴Φ₀ x′ a
  Ψ₀⊴Φ₀ x′ (s≼s p) (G.suc a) refl = suc-step (Ψ₀⊴Φ₀ x′ p a refl)
  Ψ₀⊴Φ₀ x′ (s≼s p) G.top refl = suc-step (Ψ₀⊴Φ₀ x′ p G.zero refl)
  Ψ₀⊴Φ₀ x′ (≼l n p) (G.lim f) refl = ⊴l n (Ψ₀⊴Φ₀ x′ p (f n) refl)
  Ψ₀⊴Φ₀ x′ (l≼ h) a q = l⊴ (λ n → Ψ₀⊴Φ₀ x′ (h n) a q)
  Ψ₀⊴Φ₀ x′ (≼i {p = ()} z ez p) a q
  Ψ₀⊴Φ₀ x′ (i≼ {p = ()} h) a q
  Ψ₀⊴Φ₀ x′ (≼u {r = ()} p) a q
  Ψ₀⊴Φ₀ x′ (u≼ {r = ()} p) a q

  Ω⊴Φ : ∀ η → L.Ω ℓ₁ ⊴ Φx η
  Ω⊴Φ G.zero = Ω⊴top
  Ω⊴Φ (G.suc η) = ⊴l 0 (Ω⊴Φ η)
  Ω⊴Φ (G.lim f) = ⊴l 0 (Ω⊴Φ (f 0))
  Ω⊴Φ (G.lc (inj₁ _) g) = subst (λ z → L.Ω ℓ₁ ⊴ z) (sym (node _ _)) (⊴b (Ω⊴Φ (g G.top)))
  Ω⊴Φ (G.lc (inj₂ ()) g)
  Ω⊴Φ (G.em _ a) = Ω⊴Φ₀ _ a
  Ω⊴Φ G.top = subst (λ z → L.Ω ℓ₁ ⊴ z)
    (sym (node (λ η → W.Ψ (suc zero) WL.w0 (λ r → x (inj₂ r)) η) (λ η → W.Ψ zero WL.w0 (self zero) η)))
    (⊴b (Ω⊴Φ₀ (λ r → x (inj₂ r)) G.top))

  Ψ₀⊴Φ : ∀ {y : T₀} {η} → y ⊴ η → Ψ₀ᴸ y ⊴ Φx η
  Ψ₀⊴Φ {η = η} z⊴ = Ω⊴Φ η
  Ψ₀⊴Φ (s⊴s p) = suc-step (Ψ₀⊴Φ p)
  Ψ₀⊴Φ (⊴s p) = ⊴l 0 (Ψ₀⊴Φ p)
  Ψ₀⊴Φ (⊴l n p) = ⊴l n (Ψ₀⊴Φ p)
  Ψ₀⊴Φ (l⊴ h) = l⊴ (λ n → Ψ₀⊴Φ (h n))
  Ψ₀⊴Φ {y = y} (⊴b h) = subst (λ z → Ψ₀ᴸ y ⊴ z) (sym (node _ _)) (⊴b (Ψ₀⊴Φ h))
  Ψ₀⊴Φ (em⊴ {a = a} q) = Ψ₀⊴Φ₀ _ q a refl

  Ψ₁⊴Φ : ∀ {X : T₁} {η} → X ⊴ η → Ψ₁ X ⊴ Φx η
  Ψ₁⊴Φ {η = η} z⊴ = Ω⊴Φ η
  Ψ₁⊴Φ (s⊴s p) = suc-step (Ψ₁⊴Φ p)
  Ψ₁⊴Φ (⊴s p) = ⊴l 0 (Ψ₁⊴Φ p)
  Ψ₁⊴Φ (⊴l n p) = ⊴l n (Ψ₁⊴Φ p)
  Ψ₁⊴Φ (l⊴ h) = l⊴ (λ n → Ψ₁⊴Φ (h n))
  Ψ₁⊴Φ {X = X} (⊴b h) = subst (λ z → Ψ₁ X ⊴ z) (sym (node _ _)) (⊴b (Ψ₁⊴Φ h))
  Ψ₁⊴Φ {X = X} (nd h) = subst (λ z → Ψ₁ X ⊴ z) (sym (node _ _))
    (nd (λ y a q → Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q))))
  Ψ₁⊴Φ {X = X} (nt h) = subst (λ z → Ψ₁ X ⊴ z) (sym (node _ _))
    (nd (λ y a q → Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q))))
  Ψ₁⊴Φ (u⊴ p) = Ψ₀⊴Φ p
```

## 2 前缀 Ω_{ℓ₀} 下的目标层 0 的折叠

`G₂` 是 `Tt (suc top)` 那一支的分支族 (`Ω_Ω + ψ_Ω(Ω₁) + ψ_Ω(η)`), 第 1 层的 Ω₁ 结点经 `gm₂` 落到层号 0 的位置 `s₀″`.

```agda
G₂mono : ∀ {a b} → Cp (suc zero) a b → Cp (tw 2) (G₂ a) (G₂ b)
G₂mono c = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Tt G.top) (W.Ψ-cp (tw 2) (WL.ws WL.w0) _ c))

G₂suc : ∀ η → Cp (tw 2) (G.suc (G₂ η)) (G₂ (G.suc η))
G₂suc η = add-cp (tw 2) G.lc dnLc G.top (add-cp (tw 2) G.lc dnLc (Tt G.top) (sucg (WL.ws WL.w0) _ η))

ctxA : ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (A a))
ctxA z≼ a q = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
ctxA (s≼s p) (G.suc a) refl = ≼-trans (NA.suc-lower (Ψ₀ (A a)) (ctxA p a refl)) (up≼ (Asuc a))
ctxA (s≼s p) G.top refl = ≼-trans (NA.suc-lower (Ψ₀ (A G.zero)) (ctxA p G.zero refl)) (up≼ Atop)
ctxA (≼l n p) (G.lim f) refl = ≼l n (ctxA p (f n) refl)
ctxA (l≼ h) a q = l≼ (λ n → ctxA (h n) a q)
ctxA (≼i {p = ()} x ex p) a q
ctxA (i≼ {p = ()} h) a q
ctxA (≼u {r = ()} p) a q
ctxA (u≼ {r = ()} p) a q

module NodeP (f : T₀ → T₁) (same : ∀ y → f y L.≅ f y) (g : R → R₁)
  (hm : ∀ (y : T₀) a → y ≼ NA.read a → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (f y)) ≼ NA.read (Ψ₀ (G₂ (g a)))) where

  c : ℕ → T₀
  c = iterᴸ (λ z → L.ψ (L.lim 0 L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA (f z))) (L.suc L.zero)

  δ : ℕ → R
  δ = chain zero (λ ζ → Ψ₀ (G₂ (g ζ)))

  sync : ∀ n → c n ≼ NA.read (δ n)
  sync zero = ≼-refl _
  sync (suc n) = ≼-trans
    (≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.lim 0 L.zero} {σ = λ r → r}
      (L.add-≅ {σ = σA} {σ′ = σA} (L.Ω-refl S2.ℓ₀) (same (c n))))))
    (NA.plus≽ (δ n) (Ψ₀ (G₂ (g (δ n)))) (hm (c n) (δ n) (sync n)))

  result : L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (L.limᵢ {i = L.zero} L.zero f)) ≼ L.lim (λ n → NA.read (Ψ₀ (G₂ (g (δ n)))))
  result = l≼ (λ n → ≼l n (hm (c n) (δ n) (sync n)))

fold0 : ∀ {y : T₀} {η} → y ⊴ η → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (G₂ η))
fold0 z⊴ = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
fold0 {η = G.suc η} (s⊴s p) = ≼-trans (NA.suc-lower (Ψ₀ (G₂ η)) (fold0 p)) (up≼ (G₂suc η))
fold0 (⊴s p) = ≼-trans (fold0 p) (up≼ (G₂mono (inj₂ (inj₁ refl))))
fold0 (⊴l n p) = ≼l n (fold0 p)
fold0 (l⊴ h) = l≼ (λ n → fold0 (h n))
fold0 (⊴b h) = ≼-trans (fold0 h) (up≼ (inj₂ (inj₁ refl)))
fold0 (em⊴ {a = a} q) = ctxA q a refl

fold1 : ∀ {X : T₁} {η} → X ⊴ η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA X) ≼ NA.read (Ψ₀ (G₂ η))
fold1 z⊴ s = ≼-trans btbo-Tw2 (up≼ (plus-weak (tw 2) G.top _))
fold1 {η = G.suc η} (s⊴s p) s = ≼-trans (NA.suc-lower (Ψ₀ (G₂ η)) (fold1 p (s≅⁻ s))) (up≼ (G₂suc η))
fold1 (⊴s p) s = ≼-trans (fold1 p s) (up≼ (G₂mono (inj₂ (inj₁ refl))))
fold1 (⊴l n p) s = ≼l n (fold1 p s)
fold1 (l⊴ h) s = l≼ (λ n → fold1 (h n) (l≅⁻ s n))
fold1 (⊴b h) s = ≼-trans (fold1 h s) (up≼ (inj₂ (inj₁ refl)))
fold1 {η = G.lc (inj₁ _) g} (nd {f = f} h) s =
  NodeP.result f (lᵢ≅⁻ s) g (λ y a q → fold1 (h y a q) (lᵢ≅⁻ s y))
fold1 (nt {f = f} h) s =
  NodeP.result f (lᵢ≅⁻ s) (λ a → G.em tt a) (λ y a q → fold1 (h y a q) (lᵢ≅⁻ s y))
fold1 (u⊴ p) s = fold0 p
```

## 3 第 1 层的 ψ₁(Ω₂) 在树里的位置

```agda
Tψ : R → R₁
Tψ η = W.Ψ (suc zero) (Vw (WL.nrmk zero η) (WL.nrmk-lgl zero η))
  (λ r → W.cmpw V2 s₂ (WL.nrmk zero η , WL.nrmk-lgl zero η , r)) G.top

K₁ : R → R₁
K₁ = WL.Kfk zero Tψ

ψ₁-top : ψ₁ G.top ≡ G.lc (inj₁ tt) K₁
ψ₁-top = refl

Φ₁ : R₁ → R₁
Φ₁ = W.Ψ (suc zero) (WL.ws WL.w0) (self (suc zero))

gmε : R₁ → R₁
gmε = W.Ψ (suc zero) (WL.ws WL.w0) (λ r → W.cmpw V2 s₂ (G.suc G.top , tt , inj₂ r))

Tψ-s : Tψ (G.suc G.top) ≡ G.lim (λ n → gmε (chain (suc zero) Φ₁ n))
Tψ-s = refl

module S = Lv1 (self (suc zero)) refl
module E = Lv1 (λ r → W.cmpw V2 s₂ (G.suc G.top , tt , inj₂ r)) refl

sync : ∀ n → γ 1 n ⊴ chain (suc zero) Φ₁ n
sync zero = Ω⊴top
sync (suc n) = ⊴-+ˡ (chain (suc zero) Φ₁ n) (S.Ψ₁⊴Φ (sync n))

γ1⊴ : ∀ n → γ 1 n ⊴ gmε (chain (suc zero) Φ₁ n)
γ1⊴ zero = E.Ω⊴Φ G.top
γ1⊴ (suc n) = E.Ψ₁⊴Φ (⊴-+ʳ (sync n) (Φ₁ (chain (suc zero) Φ₁ n)))

Eε : T₁
Eε = L.lim (γ 1)

Eε⊴ : Eε ⊴ Tψ (G.suc G.top)
Eε⊴ = l⊴ (λ n → ⊴l n (γ1⊴ n))
```

## 4 ψ₀(Ω_Ω+ψ₁(Ω₂))

```agda
Xε : L.Ordᶜ L.zero
Xε = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA Eε)

δ′ : ℕ → R
δ′ = chain zero (λ η → Ψ₀ (G₂ (plus (suc zero) G.top (K₁ η))))

cδ : Cp zero (G.suc G.top) (δ′ 1)
cδ = add-cp zero G.lc dnLc G.top (topᶜʷ zero V2 (λ _ → fold) (G₂ (plus (suc zero) G.top (K₁ G.top))))

Xε≼Bq : ∀ ζ → Xε ≼ NA.read (Ψ₀ (Bq ζ))
Xε≼Bq ζ = ≼-trans (fold1 (⊴-+ˡ G.top (⊴-+ˡ (Tψ G.top) Eε⊴)) (L.l≅ (γ-self 1)))
  (≼-trans (up≼ (G₂mono (add-cp (suc zero) G.lc dnLc G.top (inj₂ (1 , inj₁ refl)))))
  (≼-trans (up≼ (G₂mono (add-cp (suc zero) G.lc dnLc G.top (WL.Kfk-cp zero Tψ cδ))))
  (≼-trans (≼l 1 (≼-refl _))
  (up≼ (G₂mono (add-cp (suc zero) G.lc dnLc G.top
    (W.Ψ-cp (suc zero) V2 (W.cmpw V2 s₂) (plus-weak (tw 2) G.top _))))))))

Xε≼ʷ : Xε ≼ NA.read WF.T⁺ʷ
Xε≼ʷ = node≼T (≼l 0 (Xε≼Bq G.top))
```

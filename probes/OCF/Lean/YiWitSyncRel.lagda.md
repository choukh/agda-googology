# 第 1 层的读回关系 `⊴⁺`: 携带静态对角线 (搬到收缩见证的折叠)

验收文件. [YiSyncRel](YiSyncRel.lagda.md) 逐字搬到 [YiWitFold](YiWitFold.lagda.md): 只换模块名与导入, 链内模块换成 `YiWit` 的搬运件, 塔的 `Lw-tw`, `lgl→Lw`, `Tw`, `T⁺ʷ`, `TΛ` 取 `WF` (YiWitFold), 折叠 `W.Ψ` 仍是 YiDlFold 的 `Fold dl`. 定理与原文同名; 下文的讲解是原文.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitSyncRel where

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
open NA using (R₁; σ₀)
open import OCF.Lean.YiWitL1Emb using (⊴-dn)
open import OCF.Align.YiLvVal2 using (T₀; T₁)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 关系

`dg` 的门槛 `top + Tw 2` 是目标层 0 在前缀 `G₂` 下折叠这个结点时链的第 1 点必过的位置 (`Ψ₀ top` 就是 `Tw 2`).

```agda
infix 4 _⊴⁺_
data _⊴⁺_ : T₁ → R₁ → Set where
  z⊴ : ∀ {η} → L.zero ⊴⁺ η
  s⊴s : ∀ {x η} → x ⊴⁺ η → L.suc x ⊴⁺ G.suc η
  ⊴s : ∀ {x η} → x ⊴⁺ η → x ⊴⁺ G.suc η
  ⊴l : ∀ {x} {H : ℕ → R₁} n → x ⊴⁺ H n → x ⊴⁺ G.lim H
  l⊴ : ∀ {H : ℕ → T₁} {η} → (∀ n → H n ⊴⁺ η) → L.lim H ⊴⁺ η
  ⊴b : ∀ {x} {g : R → R₁} → x ⊴⁺ g G.top → x ⊴⁺ G.lc (inj₁ tt) g
  nd : ∀ {f : T₀ → T₁} {g : R → R₁} → (∀ (y : T₀) a → y ≼ NA.read a → f y ⊴⁺ g a) →
    L.limᵢ {i = L.zero} L.zero f ⊴⁺ G.lc (inj₁ tt) g
  nt : ∀ {f : T₀ → T₁} → (∀ (y : T₀) a → y ≼ NA.read a → f y ⊴⁺ G.em tt a) →
    L.limᵢ {i = L.zero} L.zero f ⊴⁺ G.top
  u⊴ : ∀ {y : T₀} {η} → y NA.⊴ η → L.up {k = L.zero} L.zero y ⊴⁺ η
  dg : ∀ {F : ℕ → T₁} {g : R → R₁} →
    (∀ n a → Cp zero (plus zero G.top (WF.Tw 2)) a → F n ⊴⁺ g a) → L.lim F ⊴⁺ G.lc (inj₁ tt) g
  ≅⊴ : ∀ {x y : T₁} {η} → x L.≅ y → y ⊴⁺ η → x ⊴⁺ η

⊴→⊴⁺ : ∀ {x : T₁} {η} → x NA.⊴ η → x ⊴⁺ η
⊴→⊴⁺ NA.z⊴ = z⊴
⊴→⊴⁺ (NA.s⊴s p) = s⊴s (⊴→⊴⁺ p)
⊴→⊴⁺ (NA.⊴s p) = ⊴s (⊴→⊴⁺ p)
⊴→⊴⁺ (NA.⊴l n p) = ⊴l n (⊴→⊴⁺ p)
⊴→⊴⁺ (NA.l⊴ h) = l⊴ (λ n → ⊴→⊴⁺ (h n))
⊴→⊴⁺ (NA.⊴b p) = ⊴b (⊴→⊴⁺ p)
⊴→⊴⁺ (NA.nd h) = nd (λ y a q → ⊴→⊴⁺ (h y a q))
⊴→⊴⁺ (NA.nt h) = nt (λ y a q → ⊴→⊴⁺ (h y a q))
⊴→⊴⁺ (NA.u⊴ p) = u⊴ p
```

## 2 右边沿第一位置上移

```agda
⊴⁺-cp : ∀ {x η η′} → x ⊴⁺ η → Cp (suc zero) η η′ → x ⊴⁺ η′
⊴⁺-dn : ∀ {x η} η′ → x ⊴⁺ η → Dn (suc zero) η η′ → x ⊴⁺ η′
⊴⁺-cp h (inj₁ refl) = h
⊴⁺-cp h (inj₂ p) = ⊴⁺-dn _ h p
⊴⁺-dn (G.suc η′) h p = ⊴s (⊴⁺-cp h p)
⊴⁺-dn (G.lim f) h (n , p) = ⊴l n (⊴⁺-cp h p)
⊴⁺-dn (G.lc (inj₁ _) g) h p = ⊴b (⊴⁺-cp h p)
⊴⁺-dn (G.lc (inj₂ ()) g) h p
⊴⁺-dn {η = G.em _ a} (G.em _ d) z⊴ (refl , p) = z⊴
⊴⁺-dn {η = G.em _ a} (G.em _ d) (l⊴ h) (refl , p) = l⊴ (λ n → ⊴⁺-dn (G.em tt d) (h n) (refl , p))
⊴⁺-dn {η = G.em _ a} (G.em _ d) (u⊴ h) (refl , p) = u⊴ (⊴-dn (G.em tt d) h (refl , p))
⊴⁺-dn {η = G.em _ a} (G.em _ d) (≅⊴ e h) (refl , p) = ≅⊴ e (⊴⁺-dn (G.em tt d) h (refl , p))
```

## 3 加法上下文

```agda
⊴⁺-embed : ∀ {x η} → x ⊴⁺ η → ∀ a → x ⊴⁺ plus (suc zero) η (G.em tt a)
⊴⁺-embed p G.zero = p
⊴⁺-embed p (G.suc a) = ⊴s (⊴⁺-embed p a)
⊴⁺-embed p (G.lim f) = ⊴l 0 (⊴⁺-embed p (f 0))
⊴⁺-embed p (G.lc () g)
⊴⁺-embed p (G.em () a)
⊴⁺-embed p G.top = ⊴s p

⊴⁺-+ʳ : ∀ {x η} → x ⊴⁺ η → ∀ η′ → x ⊴⁺ plus (suc zero) η η′
⊴⁺-+ʳ p G.zero = p
⊴⁺-+ʳ p (G.suc y) = ⊴s (⊴⁺-+ʳ p y)
⊴⁺-+ʳ p (G.lim f) = ⊴l 0 (⊴⁺-+ʳ p (f 0))
⊴⁺-+ʳ p (G.lc (inj₁ _) g) = ⊴b (⊴⁺-+ʳ p (g G.top))
⊴⁺-+ʳ p (G.lc (inj₂ ()) g)
⊴⁺-+ʳ p (G.em _ a) = ⊴⁺-embed p a
⊴⁺-+ʳ p G.top = ⊴b (⊴s p)

⊴⁺-+ˡ : ∀ θ {x η} → x ⊴⁺ η → x ⊴⁺ plus (suc zero) θ η
⊴⁺-+ˡ θ z⊴ = z⊴
⊴⁺-+ˡ θ (s⊴s p) = s⊴s (⊴⁺-+ˡ θ p)
⊴⁺-+ˡ θ (⊴s p) = ⊴s (⊴⁺-+ˡ θ p)
⊴⁺-+ˡ θ (⊴l n p) = ⊴l n (⊴⁺-+ˡ θ p)
⊴⁺-+ˡ θ (l⊴ h) = l⊴ (λ n → ⊴⁺-+ˡ θ (h n))
⊴⁺-+ˡ θ (⊴b h) = ⊴b (⊴⁺-+ˡ θ h)
⊴⁺-+ˡ θ (nd h) = nd (λ y a q → ⊴⁺-+ˡ θ (h y a q))
⊴⁺-+ˡ θ (nt h) = nd (λ y a q → ⊴⁺-+ˡ θ (h y a q))
⊴⁺-+ˡ θ (u⊴ p) = u⊴ (NA.⊴-+ˡ θ p)
⊴⁺-+ˡ θ (dg h) = dg (λ n a c → ⊴⁺-+ˡ θ (h n a c))
⊴⁺-+ˡ θ (≅⊴ e p) = ≅⊴ e (⊴⁺-+ˡ θ p)

add-em⁺ : ∀ {x : T₁} {η} → x ⊴⁺ η → ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a →
  L.add x σ₀ y ⊴⁺ plus (suc zero) η (G.em tt a)
add-em⁺ px z≼ a q = ⊴⁺-embed px a
add-em⁺ px (s≼s p) (G.suc a) refl = s⊴s (add-em⁺ px p a refl)
add-em⁺ px (s≼s p) G.top refl = s⊴s (add-em⁺ px p G.zero refl)
add-em⁺ px (≼l n p) (G.lim f) refl = ⊴l n (add-em⁺ px p (f n) refl)
add-em⁺ px (l≼ h) a q = l⊴ (λ n → add-em⁺ px (h n) a q)
add-em⁺ px (≼i {p = ()} x ex p) a q
add-em⁺ px (i≼ {p = ()} h) a q
add-em⁺ px (≼u {r = ()} p) a q
add-em⁺ px (u≼ {r = ()} p) a q

⊴⁺-add₀ : ∀ {x : T₁} {η} → x ⊴⁺ η → ∀ {y : T₀} {η′} → y NA.⊴ η′ → L.add x σ₀ y ⊴⁺ plus (suc zero) η η′
⊴⁺-add₀ px {η′ = η′} NA.z⊴ = ⊴⁺-+ʳ px η′
⊴⁺-add₀ px (NA.s⊴s q) = s⊴s (⊴⁺-add₀ px q)
⊴⁺-add₀ px (NA.⊴s q) = ⊴s (⊴⁺-add₀ px q)
⊴⁺-add₀ px (NA.⊴l n q) = ⊴l n (⊴⁺-add₀ px q)
⊴⁺-add₀ px (NA.l⊴ h) = l⊴ (λ n → ⊴⁺-add₀ px (h n))
⊴⁺-add₀ px (NA.⊴b h) = ⊴b (⊴⁺-add₀ px h)
⊴⁺-add₀ px (NA.em⊴ {a = a} q) = add-em⁺ px q a refl

⊴⁺-add₁ : ∀ {x : T₁} {η} → x L.≅ x → x ⊴⁺ η → ∀ {x′ : T₁} {η′} → x′ ⊴⁺ η′ →
  (x L.+ x′) ⊴⁺ plus (suc zero) η η′
⊴⁺-add₁ s px {η′ = η′} z⊴ = ⊴⁺-+ʳ px η′
⊴⁺-add₁ s px (s⊴s q) = s⊴s (⊴⁺-add₁ s px q)
⊴⁺-add₁ s px (⊴s q) = ⊴s (⊴⁺-add₁ s px q)
⊴⁺-add₁ s px (⊴l n q) = ⊴l n (⊴⁺-add₁ s px q)
⊴⁺-add₁ s px (l⊴ h) = l⊴ (λ n → ⊴⁺-add₁ s px (h n))
⊴⁺-add₁ s px (⊴b h) = ⊴b (⊴⁺-add₁ s px h)
⊴⁺-add₁ s px (nd h) = nd (λ y a q → ⊴⁺-add₁ s px (h y a q))
⊴⁺-add₁ s px (nt h) = nd (λ y a q → ⊴⁺-add₁ s px (h y a q))
⊴⁺-add₁ s px (u⊴ q) = ⊴⁺-add₀ px q
⊴⁺-add₁ s px (dg h) = dg (λ n a c → ⊴⁺-add₁ s px (h n a c))
⊴⁺-add₁ s px (≅⊴ e q) = ≅⊴ (L.add-≅ {σ = λ r → r} {σ′ = λ r → r} s e) (⊴⁺-add₁ s px q)

copies⁺ : ∀ {A : T₁} {β} → A L.≅ A → A ⊴⁺ β → ∀ n →
  iterᴸ (A L.+_) L.zero (suc n) ⊴⁺ acc (λ _ z → plus (suc zero) β z) β n
copies⁺ s p zero = p
copies⁺ s p (suc n) = ⊴⁺-add₁ s p (copies⁺ s p n)

suc-step⁺ : ∀ {A : T₁} {β} → A L.≅ A → A ⊴⁺ β → L.lim (iterᴸ (A L.+_) L.zero) ⊴⁺ succ (suc zero) β
suc-step⁺ s p = l⊴ λ where
  zero → z⊴
  (suc n) → ⊴l n (copies⁺ s p n)
```

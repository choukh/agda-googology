# 实际 Free 层的严格输出基础

只抽取 BTBOValNeg 的同界前驱工具和 BTBOValAbsorb 的严格列谓词。
不继承其具体否定闭项；下标比较始终有同一个原 c 作界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueBuildStrictBase where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_)
open import Relation.Nullary using (¬_)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.ValueJudgeBase

data St : Ordᶜ zero → Set where
  stz : St zero
  sts : ∀ {a} → St a → St (suc a)
  stl : ∀ {f : ℕ → Ordᶜ zero} → (∀ n → St (f n)) →
    (∀ n → suc (f n) ≼ f (suc n)) → St (lim f)

forget : Ordᴵ → Ordᶜ zero
forget zero      = zero
forget (suc a)   = suc (forget a)
forget (lim f _) = lim (λ n → forget (f n))

forget-toLevel : ∀ x (h : HS x) → forget (toLevel x h) ≅ x
forget-toLevel zero        h = z≅
forget-toLevel (suc a)     h = s≅ (forget-toLevel a (hs⁻ h))
forget-toLevel (lim f)     h = l≅ (λ n → forget-toLevel (f n) (hl₁ h n))
forget-toLevel (limᵢ () f) h
forget-toLevel (up () x)   h

HS-≅ : ∀ {a b : Ordᶜ Ordᴵ.zero} → a ≅ b → HS b → HS a
HS-≅ z≅     h = hz
HS-≅ (s≅ e) h = hs (HS-≅ e (hs⁻ h))
HS-≅ (l≅ k) h = hl (λ n → HS-≅ (k n) (hl₁ h n))
                   (λ n → ⊑-trans (≅→⊑ (k n)) (⊑-trans (hl₂ h n) (≅→⊑ (≅-sym (k (suc n))))))
HS-≅ (lᵢ≅ {p = ()} e k) h
HS-≅ (upˡ {r = ()} e) h
HS-≅ (upʳ {r = ()} e) h

HS-≺ : ∀ {c b : Ordᶜ Ordᴵ.zero} → c ≺ b → HS b → HS c
HS-≺ (≺z e)   h = HS-≅ e (hs⁻ h)
HS-≺ (≺s d)   h = HS-≺ d (hs⁻ h)
HS-≺ (≺l n d) h = HS-≺ d (hl₁ h n)
HS-≺ (≺i {p = ()} x ex d) h
HS-≺ (≺u {r = ()} d) h

forget-≅ᴵ : ∀ {a b} → a ≅ᴵ b → forget a ≅ forget b
forget-≅ᴵ z≅     = z≅
forget-≅ᴵ (s≅ e) = s≅ (forget-≅ᴵ e)
forget-≅ᴵ (l≅ h) = l≅ (λ n → forget-≅ᴵ (h n))

<→s≼ : ∀ {a b} → a <ᴵ b → suc (forget a) ≼ forget b
<→s≼ zero      = s≼s (≼-refl _)
<→s≼ (suc q)   = ≼-suc (<→s≼ q)
<→s≼ (lim n q) = ≼l n (<→s≼ q)

≺ᴵ→s≼ : ∀ {a b} → a ≺ᴵ b → suc (forget a) ≼ forget b
≺ᴵ→s≼ (via e q) = ≼-trans (s≼s (≅→≼ (forget-≅ᴵ e))) (<→s≼ q)

s≼0 : ∀ {a : Ordᶜ Ordᴵ.zero} → ¬ (suc a ≼ (zero {Ordᴵ.zero}))
s≼0 ()

≼-irr : ∀ (a : Ordᶜ Ordᴵ.zero) → ¬ (suc a ≼ a)
≼-irr zero        p = s≼0 p
≼-irr (suc a)     p = ≼-irr a (s≼s⁻ p)
≼-irr (lim f)     p with ≼lim⁻ p
... | n , q = ≼-irr (f n) (≼-trans (s≼s (≼l n (≼-refl (f n)))) q)
≼-irr (limᵢ () f) p
≼-irr (up () x)   p

two-preds : ∀ {a b c} → a ≺ᴵ c → b ≺ᴵ c → a ≺ᴵ b ⊎ b ≺ᴵ a ⊎ a ≅ᴵ b
two-preds (via e q) (via e′ q′) with <ᴵ-dec q q′
... | injᵃ r = injᵃ (≺ᴵ-respˡ e (≺ᴵ-respʳ r (≅ᴵ-sym e′)))
... | injᵇ r = injᵇ (≺ᴵ-respˡ e′ (≺ᴵ-respʳ r (≅ᴵ-sym e)))
... | injᶜ r = injᶜ (≅ᴵ-trans e (≅ᴵ-trans r (≅ᴵ-sym e′)))

```

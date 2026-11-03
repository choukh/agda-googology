# 读回的实例: `Ordᴵ` 上的 $F$ 与 $\mathrm{Lv}_5$, 无条件

> 不含记号. 结论写在 [LvGuard](LvGuard.lagda.md). 这是 [LvGuardUni](LvGuardUni.lagda.md) 取 `Dom₀` 的实例, 再加两件事: 合法的 `Ordᴵ` 嵌入 `ofL`, 与 "$\Omega$ 看得见" (`¬Ω⊑zero`, 它取代 [UniformLvBase](UniformLvBase.lagda.md) 的 `base⊑zero`).

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvGuardFeed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level using (Ordᴵ; _≅ᴵ_; _⊑ᴵ_; _<ᴵ_; _≺ᴵ_; via; zero; suc; lim; z≅; s≅; l≅; z⊑; s⊑; l⊑; Ω; ≅ᴵ-refl; Ordᶜ; Ω-≅; Ω-refl)
open import OCF.Align.LvGuardBase
open Lv Dom₀
import OCF.Align.LvGuardUni as Uni
private module U = Uni Dom₀
open U using (F; Lv₅; Cf-F; Cf-Lv₅; F-mono; rb₁; rb-≈₁₁; Good-Ω; Good→WF₁; ψ¹)
```

## §1 第 5 站的下标

**定理.** `F θ` 与 `Lv₅` 的 `WFˢ` 与自反, 对一切 $\theta$, 无条件, 没有世界, 没有判决. `Fᵍ`: 好层号上的函数. **这就是 `good-feed` 在 `Ordᴵ` 下标上的形式.**

```agda
GLG : Set
GLG = Σ LG Cfˢ

Fᵍ : Ordᴵ → GLG
Fᵍ θ = F θ , Cf-F θ

Lv₅ᵍ : GLG
Lv₅ᵍ = Lv₅ , Cf-Lv₅

Ωᴸ : LG
Ωᴸ = rb₁ (Ω (suc zero))

Cf-Ωᴸ : Cfˢ Ωᴸ
Cf-Ωᴸ = Good→WF₁ (Good-Ω (suc zero)) , rb-≈₁₁ (Ω-refl (suc zero))
```

## §2 `base⊑zero` 的取代

旧的 `base` 是没有前驱的原子, 所以 `base ⊑ zero`, `P̂⊑` 不成立. 这里 $\Omega$ 是真的闭包, 前驱看得见. **这是对 `base⊑zero` 的回答: $\Omega$ 不要原子, 也不要 "含 $\Omega$" 的标记.**

```agda
¬Ω⊑zero : Ωᴸ ⊑ⁿ zero → ⊥
¬Ω⊑zero h with h (fst zero)
... | pre _ ()
```

## §3 `Ordᴵ` 的合法嵌入

```agda
ofL : Ordᴵ → LG
ofL zero      = zero
ofL (suc a)   = suc (ofL a)
ofL (lim f s) = lim (λ n → ofL (f n))

ofL≈ : ∀ {a b} → a ≅ᴵ b → ofL a ≈ ofL b
ofL≈ z≅     = z≈
ofL≈ (s≅ e) = s≈ (ofL≈ e)
ofL≈ (l≅ h) = l≈ (λ n → ofL≈ (h n))

ofL≈⁻ : ∀ {a b} → ofL a ≈ ofL b → a ≅ᴵ b
ofL≈⁻ {a = zero}    {b = zero}    z≈     = z≅
ofL≈⁻ {a = suc a}   {b = suc b}   (s≈ e) = s≅ (ofL≈⁻ e)
ofL≈⁻ {a = lim f s} {b = lim g t} (l≈ h) = l≅ (λ n → ofL≈⁻ (h n))

ofL< : ∀ {a b} → a <ᴵ b → ofL a < ofL b
ofL< zero      = zero
ofL< (suc q)   = suc (ofL< q)
ofL< (lim n q) = lim n (ofL< q)

ofL≪ : ∀ {a b} → a <ᴵ b → ofL a ≪ ofL b
ofL≪ zero      = zero
ofL≪ (suc q)   = suc (ofL≪ q)
ofL≪ (lim n q) = lim n (ofL≪ q)

adm : ∀ {a b} (q : a <ᴵ b) E → Adm E (ofL< q)
adm zero      E = tt
adm (suc q)   E = adm q E
adm (lim n q) E = adm q E

pull : ∀ a {k} → k < ofL a → Σ Ordᴵ λ a′ → (k ≡ ofL a′) × (a′ <ᴵ a)
pull (suc a) zero = a , refl , zero
pull (suc a) (suc r) with pull a r
... | a′ , e , q = a′ , e , suc q
pull (lim f s) (lim n r) with pull (f n) r
... | a′ , e , q = a′ , e , lim n q

pullᶠ : ∀ a {k} → k ≪ ofL a → Σ Ordᴵ λ a′ → (k ≡ ofL a′) × (a′ <ᴵ a)
pullᶠ (suc a) zero = a , refl , zero
pullᶠ (suc a) (suc r) with pullᶠ a r
... | a′ , e , q = a′ , e , suc q
pullᶠ (lim f s) (lim n r) with pullᶠ (f n) r
... | a′ , e , q = a′ , e , lim n q

noCpᶠ : ∀ a {c t g} → Cpᶠ (lc c t g) (ofL a) → ⊥
noCpᶠ (suc a) (suc p) = noCpᶠ a p
noCpᶠ (lim f s) (lim n p) = noCpᶠ (f n) p

noCp : ∀ a {c t g} → Cp (lc c t g) (ofL a) → ⊥
noCp (suc a) (suc p) = noCp a p
noCp (lim f s) (lim n p) = noCp (f n) p

ofL⊴ : ∀ {a b} → a ⊑ᴵ b → ofL a ⊴ ofL b
ofL⊴ {a} {b} e = ⊴i pp ff (λ p → ⊥-case (noCpᶠ a p)) (λ p → ⊥-case′ (noCp a p))
  where
  open import Data.Empty using (⊥-elim)
  ⊥-case : ∀ {c t g} → ⊥ → Kvᶠ c t g (ofL b)
  ⊥-case = ⊥-elim
  ⊥-case′ : ∀ {c t g A} → ⊥ → Kv c t g A (ofL b)
  ⊥-case′ = ⊥-elim
  open import OCF.Align.Level using (sim)
  pp : ofL a ⊑ ofL b
  pp r with pull a r
  ... | a′ , refl , q with sim e q
  ... | via d q′ = viaᴸ (ofL≈ d) (ofL< q′) (λ E _ → adm q′ E)
  ff : ofL a ⊑ᶠ ofL b
  ff r with pullᶠ a r
  ... | a′ , refl , q with sim e q
  ... | via d q′ = preᶠ (ofL≈ d) (ofL≪ q′)

WF-ofL : ∀ a → WFˢ (ofL a)
WF-ofL zero      = tt
WF-ofL (suc a)   = WF-ofL a
WF-ofL (lim f s) = (λ n → ofL⊴ (s n)) , (λ n → WF-ofL (f n))

ofLᵍ : Ordᴵ → GLG
ofLᵍ a = ofL a , WF-ofL a , ofL≈ (≅ᴵ-refl a)
```

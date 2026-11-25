# YiSuc 好树：合法的第 0 层主线树读回后是好树

**验收文件，档位：编译定理。** `good-read : ∀ d → Lgl zero d → Good (read d)` (`Good` 是 [YiFlatObs](YiFlatObs.lagda.md) 的好树，极限的相邻项要观测前序 `⊑ᵒ`)。
办法：只经后继与 ℕ 极限下降的第一位置 `≤₁` 被一切观测 (ψ, ψ⁰, 压平, 加法, 搬运) 保持，到底是结构前驱包含 (`fp-obs`)；合法性的 `Cp` 读回就是 `≤₁`。用途：`HS-flat` 给出压平后的证书。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSucGood where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanTw3 using (R)
open import OCF.Lean.YiLeanAccFin using (read)
import OCF.Align.Level as L
open L using (Ordᶜ; _≅_; _⊑_)
open import OCF.Lean.YiChainFlat using (flat)
open import OCF.Lean.YiFlatObs using (Obs; run; _≈ᵒ_; idO; ψ⁰o; flo; ψo; addo; tro; tr⁻o; _⊑ᵒ_;
  Good; gz; gs; gl; flat-≅)
```

## 1 第一位置被观测保持

```agda
infix 4 _≤₁_
data _≤₁_ {k} : Ordᶜ k → Ordᶜ k → Set where
  r₁ : ∀ {y} → y ≤₁ y
  s₁ : ∀ {x y} → x ≤₁ y → x ≤₁ L.suc y
  l₁ : ∀ {x f} n → x ≤₁ f n → x ≤₁ L.lim f

≤₁-⊑ : ∀ {k} {x y : Ordᶜ k} → x ≤₁ y → x ⊑ y
≤₁-⊑ r₁ h = h
≤₁-⊑ (s₁ d) h = L.≺s (≤₁-⊑ d h)
≤₁-⊑ (l₁ n d) h = L.≺l n (≤₁-⊑ d h)

≤₁-ψ : ∀ {i k ℓ} {p : i L.<ᴵ ℓ} {σ : L.Simᴵ k ℓ} {x y : Ordᶜ k} → x ≤₁ y → L.ψ p σ x ≤₁ L.ψ p σ y
≤₁-ψ r₁ = r₁
≤₁-ψ (s₁ d) = l₁ 1 (≤₁-ψ d)
≤₁-ψ (l₁ n d) = l₁ n (≤₁-ψ d)

≤₁-ψ⁰ : ∀ {k} {x y : Ordᶜ k} → x ≤₁ y → L.ψ⁰ x ≤₁ L.ψ⁰ y
≤₁-ψ⁰ r₁ = r₁
≤₁-ψ⁰ (s₁ d) = l₁ 1 (≤₁-ψ⁰ d)
≤₁-ψ⁰ (l₁ n d) = l₁ n (≤₁-ψ⁰ d)

≤₁-flat : ∀ {k} {x y : Ordᶜ k} → x ≤₁ y → flat x ≤₁ flat y
≤₁-flat r₁ = r₁
≤₁-flat (s₁ d) = s₁ (≤₁-flat d)
≤₁-flat (l₁ n d) = l₁ n (≤₁-flat d)

≤₁-add : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : L.Simᴵ k ℓ} {x y : Ordᶜ k} → x ≤₁ y → L.add a σ x ≤₁ L.add a σ y
≤₁-add r₁ = r₁
≤₁-add (s₁ d) = s₁ (≤₁-add d)
≤₁-add (l₁ n d) = l₁ n (≤₁-add d)

≤₁-tr : ∀ {a b} {e : a L.≅ᴵ b} {x y : Ordᶜ a} → x ≤₁ y → L.tr e x ≤₁ L.tr e y
≤₁-tr r₁ = r₁
≤₁-tr (s₁ d) = s₁ (≤₁-tr d)
≤₁-tr (l₁ n d) = l₁ n (≤₁-tr d)

≤₁-tr⁻ : ∀ {a b} {e : a L.≅ᴵ b} {x y : Ordᶜ b} → x ≤₁ y → L.tr⁻ e x ≤₁ L.tr⁻ e y
≤₁-tr⁻ r₁ = r₁
≤₁-tr⁻ (s₁ d) = s₁ (≤₁-tr⁻ d)
≤₁-tr⁻ (l₁ n d) = l₁ n (≤₁-tr⁻ d)

fp-obs : ∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ →
  ∀ {x : Ordᶜ k} {y₀ y : Ordᶜ k′} → x ≅ y₀ → y₀ ≤₁ y → run O x ⊑ run O′ y
fp-obs idO e d = L.⊑-trans (L.≅→⊑ e) (≤₁-⊑ d)
fp-obs (ψ⁰o o) e d = fp-obs o (L.ψ⁰-≅ e) (≤₁-ψ⁰ d)
fp-obs (flo o) e d = fp-obs o (flat-≅ e) (≤₁-flat d)
fp-obs (ψo o) e d = fp-obs o (L.ψ-≅ (L.≅ᴵ-refl _) e) (≤₁-ψ d)
fp-obs (addo o ea) e d = fp-obs o (L.add-≅ ea e) (≤₁-add d)
fp-obs (tro {e = e₁} {e′ = e₂} o) e d = fp-obs o (L.tr-≅ e₁ (L.≅-tr e₂ e)) (≤₁-tr d)
fp-obs (tr⁻o {e = e₁} {e′ = e₂} o) e d = fp-obs o (L.tr⁻-≅ e₁ (L.≅-tr⁻ e₂ e)) (≤₁-tr⁻ d)
```

## 2 合法树的读回

```agda
cp-≤₁ : ∀ {a} b → Cp zero a b → read a ≤₁ read b
cp-≤₁ b (inj₁ refl) = r₁
cp-≤₁ (G.suc b) (inj₂ p) = s₁ (cp-≤₁ b p)
cp-≤₁ (G.lim f) (inj₂ (n , p)) = l₁ n (cp-≤₁ (f n) p)

good-read : ∀ d → Lgl zero d → Good (read d)
good-read G.zero l = gz
good-read (G.suc d) l = gs (good-read d l)
good-read (G.lim f) (st , lf) = gl (λ n → good-read (f n) (lf n))
  (λ n o → fp-obs o (L.≅-refl⁰ (read (f n))) (cp-≤₁ (f (suc n)) (st n)))
good-read (G.lc () g) l
good-read (G.em () a) l
good-read G.top l = gs gz
```

# YiFlat 见证：压平后 Ω 的结构严格单调

**验收文件，档位：编译定理。** `flatΩ-≺ : a ≺ᴵ b → flat (Ω a) ≺ flat (Ω b)`：层号的结构前驱给出压平后的结构前驱。基本一步 `flat (Ω a) ≺ flat (Ω (suc a))` 走 Ω_{a+1} 的链的第 1 项 ψ_a(Ω_a)，它的第 2 项含 Ω_a + Ω_a 里的后继 Ω_a + 1；其余由 [YiFlatObs](YiFlatObs.lagda.md) 的 `flatΩ-mono`。
只谈参照框架。`W0 x`：压平时沿每个极限的第 0 支能走到一个 0 的前驱 (对 `limᵢ` 要求对一切 ≅ Ω_j 的支，以便穿透后仍可用)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFlatWit where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (sym; subst)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.Uniform using (≅-reflˡ)
open import OCF.Lean.YiChainFlat using (flat)
open import OCF.Lean.YiFlatObs using (flat-≅; flatΩ-mono)
```

## 1 零样的树与带 0 前驱的树

```agda
data Zr : ∀ {k} → Ordᶜ k → Set where
  zz : ∀ {k} → Zr (𝟎 {k})
  zu : ∀ {k ℓ} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → Zr (out (◃₁→◃ r) x) → Zr (up r x)

data W0 : ∀ {k} → Ordᶜ k → Set where
  wz : ∀ {k} {y : Ordᶜ k} → Zr y → W0 (suc y)
  ws : ∀ {k} {y : Ordᶜ k} → W0 y → W0 (suc y)
  wl : ∀ {k} {f : ℕ → Ordᶜ k} n → W0 (f n) → W0 (lim f)
  wi : ∀ {k j} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} →
       (∀ z → z ≅ Ω j → W0 (f (into (<→◃ q) z))) → W0 (limᵢ q f)
  wu : ∀ {k ℓ} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → W0 (out (◃₁→◃ r) x) → W0 (up r x)

Zr-u : ∀ {k ℓ} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → Zr (up r x) → Zr (out (◃₁→◃ r) x)
Zr-u (zu z) = z

W0-s : ∀ {k} {y : Ordᶜ k} → W0 (suc y) → Zr y ⊎ W0 y
W0-s (wz z) = inj₁ z
W0-s (ws w) = inj₂ w

W0-l : ∀ {k} {f : ℕ → Ordᶜ k} → W0 (lim f) → Σ ℕ λ n → W0 (f n)
W0-l (wl n w) = n , w

W0-i : ∀ {k j} {q : j <ᴵ k} {f : U j (<→◃ q) → Ordᶜ k} → W0 (limᵢ q f) →
       ∀ z → z ≅ Ω j → W0 (f (into (<→◃ q) z))
W0-i (wi H) = H

W0-u : ∀ {k ℓ} {r : k ◃₁ ℓ} {x : U k (◃₁→◃ r)} → W0 (up r x) → W0 (out (◃₁→◃ r) x)
W0-u (wu w) = w
```

两者对 ≅ 不变 (对 ≅ 的推导递归)。

```agda
Zr-≅ : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → Zr x → x ≅ y → Zr y
Zr-≅ z (upʳ e) = zu (Zr-≅ z e)
Zr-≅ z z≅ = zz
Zr-≅ z (upˡ {r = zero} e) = Zr-≅ (Zr-u z) e
Zr-≅ z (upˡ {r = self n} e) = Zr-≅ (Zr-u z) e
Zr-≅ () (s≅ e)
Zr-≅ () (l≅ h)
Zr-≅ () (lᵢ≅ e h)

W0-≅ : ∀ {k k′} {x : Ordᶜ k} {y : Ordᶜ k′} → W0 x → x ≅ y → W0 y
W0-≅ w (upʳ e) = wu (W0-≅ w e)
W0-≅ w (upˡ {r = zero} e) = W0-≅ (W0-u w) e
W0-≅ w (upˡ {r = self n} e) = W0-≅ (W0-u w) e
W0-≅ () z≅
W0-≅ w (s≅ e) with W0-s w
... | inj₁ z = wz (Zr-≅ z e)
... | inj₂ w′ = ws (W0-≅ w′ e)
W0-≅ w (l≅ h) with W0-l w
... | n , w′ = wl n (W0-≅ w′ (h n))
W0-≅ w (lᵢ≅ {p = q} e h) = wi (λ z′ d →
  W0-≅ (W0-i w (tr⁻ e z′) (tr⁻-≅ e (≅-trans d (Ω-≅ (≅ᴵ-sym e)))))
       (h (tr⁻ e z′) z′ (≅→R (<→◃ q) (tr⁻-≅ e (≅-reflˡ d)))))

W0Ω : ∀ i → W0 (Ω i)
W0Ω zero      = wz zz
W0Ω (suc c)   = wi (λ z d → wu {r = zero} (W0-≅ (W0Ω c) (≅-sym d)))
W0Ω (lim g s) = wl 0 (wu (W0Ω (g 0)))
```

## 2 加法与折叠的严格一步

```agda
ZA : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {y : Ordᶜ k} → Zr y → flat (add a σ y) ≅ flat a
ZA {a = a} zz = ≅-refl⁰ (flat a)
ZA {σ = σ} (zu {r = zero} z) = ZA {σ = λ q → σ (suc q)} z
ZA {σ = σ} (zu {r = self n} z) = ZA {σ = λ q → σ (lim n q)} z

ZS : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → Zr x → ψ p σ x ≅ Ω i
ZS {i} zz = Ω-refl i
ZS {p = p} {σ = σ} (zu {r = zero} z) = ZS {p = p} {σ = λ q → σ (suc q)} z
ZS {p = p} {σ = σ} (zu {r = self n} z) = ZS {p = p} {σ = λ q → σ (lim n q)} z

addW : ∀ {k ℓ} {a : Ordᶜ ℓ} {σ : Simᴵ k ℓ} {y : Ordᶜ k} → W0 y → flat a ≺ flat (add a σ y)
addW {σ = σ} (wz z) = ≺z (≅-sym (ZA {σ = σ} z))
addW {σ = σ} (ws w) = ≺s (addW {σ = σ} w)
addW {σ = σ} (wl n w) = ≺l n (addW {σ = σ} w)
addW {a = a} {σ = σ} (wi {j = j} {q = q} {f = f} H) =
  ≺l 0 (subst (λ u → flat a ≺ flat (add a σ (f (into (<→◃ q) u)))) (sym (out-into (<→◃ (σ q)) (Ω j)))
              (addW {σ = σ} (H (Ω j) (Ω-refl j))))
addW {σ = σ} (wu {r = zero} w) = addW {σ = λ q → σ (suc q)} w
addW {σ = σ} (wu {r = self n} w) = addW {σ = λ q → σ (lim n q)} w

ψW : ∀ {i k ℓ} {p : i <ᴵ ℓ} {σ : Simᴵ k ℓ} {x : Ordᶜ k} → W0 x → flat (Ω i) ≺ flat (ψ p σ x)
ψW {i} {p = p} {σ = σ} (wz z) =
  ≺l 2 (≺-respˡ (flat-≅ (ZS {p = p} {σ = σ} z))
    (addW {σ = λ r → r} (W0-≅ (W0Ω i) (≅-sym (ZS {p = p} {σ = σ} z)))))
ψW {p = p} {σ = σ} (ws w) = ≺l 1 (ψW {p = p} {σ = σ} w)
ψW {p = p} {σ = σ} (wl n w) = ≺l n (ψW {p = p} {σ = σ} w)
ψW {i} {p = p} {σ = σ} (wi {j = j} {q = q} {f = f} H) with <ᴵ-dec (σ q) p
... | injᵃ (via {a′ = j′} e r) =
  ≺l 0 (subst (λ u → flat (Ω i) ≺ flat (ψ p σ (f (into (<→◃ q) (tr⁻ e u))))) (sym (out-into (<→◃ r) (Ω j′)))
              (ψW {p = p} {σ = σ} (H (tr⁻ e (Ω j′)) (tr⁻-≅ e (Ω-≅ (≅ᴵ-sym e))))))
... | injᵇ _ = ≺l 0 (ψW {p = p} {σ = σ} (H (Ω j) (Ω-refl j)))
... | injᶜ _ = ≺l 0 (ψW {p = p} {σ = σ} (H (Ω j) (Ω-refl j)))
ψW {p = p} {σ = σ} (wu {r = zero} w) = ψW {p = p} {σ = λ q → σ (suc q)} w
ψW {p = p} {σ = σ} (wu {r = self n} w) = ψW {p = p} {σ = λ q → σ (lim n q)} w
```

## 3 Ω 的严格一步与严格单调

`Ω (suc a)` 压平后第 1 项是 ψ_a(Ω_a)。

```agda
flatΩ-suc : ∀ a → flat (Ω a) ≺ flat (Ω (suc a))
flatΩ-suc a = ≺l 1 (ψW {p = zero} {σ = λ r → r} (wu {r = zero} (W0Ω a)))

flatΩ-≺ : ∀ {a b} → a ≺ᴵ b → flat (Ω a) ≺ flat (Ω b)
flatΩ-≺ {a} h = flatΩ-mono (s⊑′ h) (flatΩ-suc a)
```

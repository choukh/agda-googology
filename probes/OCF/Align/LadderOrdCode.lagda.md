# 序数高度: 码的例子, `Ordᴵ` 进码

> **判决: HOLDS (编译过, 无条件).** 结论写在 [LadderOrd](LadderOrd.lagda.md). 码的算术与检查点 $\omega$, $\omega\cdot 2$, $\omega^2$, $\omega^\omega$, $\varepsilon_0$; 读值是判断 (`val` 的相等只测了小的例子). `⌈ η ⌉`: 任何 `η : Ordᴵ` 都有码, 无条件, `η ≼ val ⌈ η ⌉` (`dom`); 非严格的极限会被求和放大, 所以这个方向只保证不低. 严格的 $\eta$ 的精确码见 [LadderOrdStr](LadderOrdStr.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LadderOrdCode where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _⊑ᴵ_)
open import OCF.Align.LadderOrdPos
```

## §1 Brouwer 序

`_⊑ᴵ_` 是字面的, 太细 (不对后继单调). 这里用通常的序, 只用于陈述.

```agda
infix 4 _≼_
data _≼_ : Ordᴵ → Ordᴵ → Set where
  z≼  : ∀ {b} → zero ≼ b
  s≼  : ∀ {a b} → a ≼ b → suc a ≼ suc b
  s≼ʳ : ∀ {a b} → a ≼ b → a ≼ suc b
  l≼  : ∀ {f s b} → (∀ n → f n ≼ b) → lim f s ≼ b
  l≼ʳ : ∀ {a f s} n → a ≼ f n → a ≼ lim f s

≼-refl : ∀ a → a ≼ a
≼-refl zero = z≼
≼-refl (suc a) = s≼ (≼-refl a)
≼-refl (lim f s) = l≼ (λ n → l≼ʳ n (≼-refl (f n)))

≼-trans : ∀ {a b c} → a ≼ b → b ≼ c → a ≼ c
≼-trans z≼ y = z≼
≼-trans (s≼ x) (s≼ y) = s≼ (≼-trans x y)
≼-trans (s≼ x) (s≼ʳ y) = s≼ʳ (≼-trans (s≼ x) y)
≼-trans (s≼ x) (l≼ʳ n y) = l≼ʳ n (≼-trans (s≼ x) y)
≼-trans (s≼ʳ x) (s≼ y) = s≼ʳ (≼-trans x y)
≼-trans (s≼ʳ x) (s≼ʳ y) = s≼ʳ (≼-trans (s≼ʳ x) y)
≼-trans (s≼ʳ x) (l≼ʳ n y) = l≼ʳ n (≼-trans (s≼ʳ x) y)
≼-trans (l≼ h) y = l≼ (λ n → ≼-trans (h n) y)
≼-trans (l≼ʳ n x) (l≼ h) = ≼-trans x (h n)
≼-trans (l≼ʳ n x) (s≼ʳ y) = s≼ʳ (≼-trans (l≼ʳ n x) y)
≼-trans (l≼ʳ n x) (l≼ʳ k y) = l≼ʳ k (≼-trans (l≼ʳ n x) y)

-- b ≼ b + c
≼-plus : ∀ b c → b ≼ plus b c
≼-Sb : ∀ b g j → b ≼ Sb b g j
≼-plus b cz = ≼-refl b
≼-plus b (cs c) = s≼ʳ (≼-plus b c)
≼-plus b (cl g) = l≼ʳ 0 (≼-refl b)
≼-Sb b g zero = ≼-refl b
≼-Sb b g (suc j) = s≼ʳ (≼-trans (≼-Sb b g j) (≼-plus (Sb b g j) (g j)))
```

## §2 `Ordᴵ` 进码

```agda
⌈_⌉ : Ordᴵ → Code
⌈ zero ⌉ = cz
⌈ suc a ⌉ = cs ⌈ a ⌉
⌈ lim f s ⌉ = cl (λ n → ⌈ f n ⌉)

dom : ∀ η b → η ≼ plus b ⌈ η ⌉
dom zero b = z≼
dom (suc a) b = s≼ (dom a b)
dom (lim f s) b = l≼ (λ n → l≼ʳ (suc n) (s≼ʳ (dom (f n) (Sb b (λ i → ⌈ f i ⌉) n))))

dom₀ : ∀ η → η ≼ val ⌈ η ⌉
dom₀ η = dom η zero
```

## §3 码的算术与检查点

`c ᶜ+ d` 是 $c+d$: 只改第一块. `cl (λ _ → c)` 是 $(c+1)\cdot\omega$; $c$ 是极限或 $0$ 时就是 $c\cdot\omega$ (判断).

```agda
_ᶜ+_ : Code → Code → Code
c ᶜ+ cz = c
c ᶜ+ cs d = cs (c ᶜ+ d)
c ᶜ+ cl g = cl (λ { zero → c ᶜ+ g 0 ; (suc j) → g (suc j) })

ωᶜ : Code
ωᶜ = cl (λ _ → cz)

natᶜ : ℕ → Code
natᶜ zero = cz
natᶜ (suc n) = cs (natᶜ n)

-- c·ω
_·ωᶜ : Code → Code
c ·ωᶜ = cl (λ _ → c)

-- ω·2 与 ω·(n+1)
ω·ᶜ : ℕ → Code
ω·ᶜ zero = ωᶜ
ω·ᶜ (suc n) = ω·ᶜ n ᶜ+ ωᶜ

ω²ᶜ : Code
ω²ᶜ = ωᶜ ·ωᶜ

ω^ᶜ : ℕ → Code
ω^ᶜ zero = cs cz
ω^ᶜ (suc n) = ω^ᶜ n ·ωᶜ

ω^ωᶜ : Code
ω^ωᶜ = cl ω^ᶜ

-- a·ω^c: 对 c 递归. c = Σ(g j + 1) 时是 a·ω^{S_j} 的上确界
mulE : Code → Code → Code
mulEP : Code → (ℕ → Code) → ℕ → Code
mulE a cz = a
mulE a (cs c) = mulE a c ·ωᶜ
mulE a (cl g) = cl (mulEP a g)
mulEP a g zero = a
mulEP a g (suc j) = mulE (mulEP a g j) (g j) ·ωᶜ

expω : Code → Code
expω = mulE (cs cz)

tower : ℕ → Code
tower zero = ωᶜ
tower (suc n) = expω (tower n)

ε₀ᶜ : Code
ε₀ᶜ = cl tower
```

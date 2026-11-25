# K4 (四): 关系的两条边界

> **判决: 否定 (定理, 已编译), 只否定写明的一种加宽.** `no-cross-level`: 逐点规则不能放宽到分支层不同的两个 Ω-结点. 第 2 层的闭项 `Aˣ` (分支层 0), `Bˣ` (分支层 1) 分支逐点相关 (`hyp`), 值上 `Aˣ ≼ Bˣ`, 折叠后 $2\preccurlyeq\psi^0A^\times$ 而 $\psi^0B^\times\preccurlyeq1$. 所以 `i≤` 的前提 `j ≅ᴵ j′` 去不掉; 带着它, [K4MonoFold](K4MonoFold.lagda.md) 的 `ψ-⊑` 成立.
> **不完全 (`incomplete`):** $\Omega_1$ 与 $\Omega_2$ 不在关系里, 而 $\psi^0\Omega_1\preccurlyeq\psi^0\Omega_2$ 成立 (`Level.Ψ⁰-mono`). 层号平移的比较不归这个关系管.
> **不否定:** 用别的办法把层号平移纳入. 入口 [K4Mono](K4Mono.lagda.md). 导入闭包经 `Value` 含记号模块.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.K4MonoNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; subst)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼i; i≼; ≼-refl; ≼-trans; s≼s⁻; s≼0; 𝟏; 𝟐; ⊑→≼)
open import OCF.Align.K4MonoValue using (module W)

ℓ₁ ℓ₂ : Ordᴵ
ℓ₁ = suc zero
ℓ₂ = suc (suc zero)
```

## §1 分支层不同的两个结点

`fˣ` 把第 0 层的树提升到第 2 层. `gˣ` 把第 1 层的树提升到第 2 层, 但遇到 Ω-结点就取它在 $0$ 处的那一支. `≤i` 说第 0 层的 $x$ 在一个 Ω-结点之下当且仅当它在每一支之下, 所以 $x\sqsubseteq y\Rightarrow f^\times x\sqsubseteq g^\times y$ 仍成立 (`hyp`); 而 $g^\times(\Omega_1)=\uparrow\uparrow0$, 右边的链停在 $\Omega_1$ (`stallˣ`).

```agda
fˣ : Ordᶜ zero → Ordᶜ ℓ₂
fˣ x = up zero (up zero x)

gˣ : Ordᶜ ℓ₁ → Ordᶜ ℓ₂
gˣ zero              = zero
gˣ (suc y)           = suc (gˣ y)
gˣ (lim h)           = lim (λ n → gˣ (h n))
gˣ (limᵢ zero φ)     = gˣ (φ zero)
gˣ (limᵢ (suc ()) φ)
gˣ (up zero x)       = up zero (up zero x)

key : ∀ {x : Ordᶜ zero} {y : Ordᶜ ℓ₁} → x W.⊑ᵖ y → x W.⊑ᵖ gˣ y
key W.z≤                  = W.z≤
key (W.s≤ d)              = W.s≤ (key d)
key (W.≤s d)              = W.≤s (key d)
key (W.≤l n d)            = W.≤l n (key d)
key (W.l≤ k)              = W.l≤ (λ n → key (k n))
key (W.i≤ {p = ()} e m h)
key (W.≤i {q = zero} k)   = key (k zero)
key (W.≤i {q = suc ()} k)
key (W.u≤ {r = ()} d)
key (W.≤u {r = zero} d)   = W.≤u (W.≤u d)

hyp : ∀ (x : Ordᶜ zero) (y : Ordᶜ ℓ₁) → x W.⊑ᵖ y → fˣ x W.⊑ᵖ gˣ y
hyp x y d = W.u≤ (W.u≤ (key d))

Aˣ Bˣ : Ordᶜ ℓ₂
Aˣ = limᵢ (suc zero) fˣ
Bˣ = limᵢ zero gˣ

STEPˣ : Ordᶜ ℓ₁ → Ordᶜ ℓ₁
STEPˣ y = ψ {i = ℓ₁} {k = ℓ₂} {ℓ = ℓ₂} zero (λ r → r) (gˣ y)

stallˣ : ∀ n → iter STEPˣ (Ω ℓ₁) n ≡ Ω ℓ₁
stallˣ zero    = refl
stallˣ (suc n) = cong STEPˣ (stallˣ n)

ψ⁰Bˣ≼1 : ψ⁰ Bˣ ≼ 𝟏
ψ⁰Bˣ≼1 = l≼ (λ n → subst (λ w → ψ⁰ (gˣ w) ≼ 𝟏) (sym (stallˣ n)) (≼-refl 𝟏))

2≼ψ⁰Aˣ : 𝟐 ≼ ψ⁰ Aˣ
2≼ψ⁰Aˣ = ≼l 0 (≼l 2 (≼-refl 𝟐))

-- 值上 Aˣ 不高于 Bˣ: Aˣ 的每一支 fˣ x 就是 Bˣ 在 ↑x 处的那一支
Aˣ≼Bˣ : Aˣ ≼ Bˣ
Aˣ≼Bˣ = i≼ (λ x ex → ≼i (up zero x) (upˡ (upʳ (≅-refl⁰ x))) (≼-refl (fˣ x)))

no-cross-level : (Rel : Ordᶜ ℓ₂ → Ordᶜ ℓ₂ → Set) →
                 (∀ {a b} → Rel a b → ψ⁰ a ≼ ψ⁰ b) →
                 ¬ (∀ (f : Ordᶜ zero → Ordᶜ ℓ₂) (g : Ordᶜ ℓ₁ → Ordᶜ ℓ₂) →
                      (∀ x y → x W.⊑ᵖ y → f x W.⊑ᵖ g y) → Rel (limᵢ (suc zero) f) (limᵢ zero g))
no-cross-level Rel snd cross = s≼0 (s≼s⁻ (≼-trans 2≼ψ⁰Aˣ (≼-trans (snd (cross fˣ gˣ hyp)) ψ⁰Bˣ≼1)))
```

第一个前提可满足 (本文的关系, `W.ψ⁰-monoᵖ`), 于是 `Aˣ`, `Bˣ` 不在关系里:

```agda
Aˣ⋢Bˣ : ¬ (Aˣ W.⊑ᵖ Bˣ)
Aˣ⋢Bˣ d = s≼0 (s≼s⁻ (≼-trans 2≼ψ⁰Aˣ (≼-trans (W.ψ⁰-monoᵖ d) ψ⁰Bˣ≼1)))
```

`ψ-⊑` 的证明里对应的一行是规则 6 的链起点 `Ω-⊑ e : Ω j ⊑ᵖ Ω j′`, 它要 `e : j ≅ᴵ j′`. 分支层是 $0$ 与 $1$ 时起点是 $\Omega_0=1$ 与 $\Omega_1$, 不相关:

```agda
¬s⊑z : ∀ {a : Ordᶜ zero} → suc a W.⊑ᵖ 𝟎 {zero} → ⊥
¬s⊑z ()

Ω₀⋢Ω₁ : ¬ (Ω zero W.⊑ᵖ Ω ℓ₁)
Ω₀⋢Ω₁ (W.≤i k) = ¬s⊑z (W.≤u⁻ (k zero))
```

## §2 关系不完全: 层号平移

```agda
¬i⊑z : ∀ {ℓ ℓ′ j} {p : j <ᴵ ℓ} {f : U j (<→◃ p) → Ordᶜ ℓ} → limᵢ p f W.⊑ᵖ 𝟎 {ℓ′} → ⊥
¬i⊑z ()

Ω₁⋢Ω₂ : ¬ (Ω ℓ₁ W.⊑ᵖ Ω ℓ₂)
Ω₁⋢Ω₂ (W.i≤ () m h)
Ω₁⋢Ω₂ (W.≤i k) = ¬i⊑z (W.≤u⁻ (k zero))

incomplete : ¬ (Ω ℓ₁ W.⊑ᵖ Ω ℓ₂) × (ψ⁰ (Ω ℓ₁) ≼ ψ⁰ (Ω ℓ₂))
incomplete = Ω₁⋢Ω₂ , ⊑→≼ (ψ⁰ (Ω ℓ₁)) (Ψ⁰-mono (natᴵ-step 1))
```

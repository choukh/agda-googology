# $\theta\mapsto\psi_1(\Omega_\theta)$ 作层号, 不带标签 (定义)

> 底座 [LvKeyBase](LvKeyBase.lagda.md). 不含记号. 结论写在 [LvKey](LvKey.lagda.md). 与 [UniformLvTheta](UniformLvTheta.lagda.md) 逐字相同, 只是 `lcl` 没有标签, 并把那边底座里的 `_⊕ᴸ_`, `rp` 搬过来. 这里只有定义: `F` 的 `WF` 没有证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LvKeyTheta where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; _◃_; _◃₁_; ◃₁→◃; <→◃; Simᴵ; <ᴵ-dec; via; zero; suc; lim; self)
import OCF.Align.Level as Lv
open import OCF.Align.Prefix using (Ord₊ˢ; Ordˢ; outˢ; intoˢ; tr⁻ˢ; Ωˢ; _+ˢ_)
open import OCF.Align.LvKeyBase
```

## §1 字面世界里的折叠

`ψᵛ p σ`: 树在第 $k$ 层, 目标 $j$, 世界 $\ell$ 同时含 $k$ 的字面前驱与 $j$. 与 `Level` 的 `ψ` 同形. `Ωˢ θ` 与它的折叠都没有 `ŝ`, `ĉᴸ`; 它们的行只是为了总函数.

```agda
ψᵛ : ∀ {k j ℓ} → j <ᴵ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ j
ψᵛ {j = j} p σ Ord₊ˢ.zero = Ωˢ j
ψᵛ p σ (Ord₊ˢ.suc a) = Ord₊ˢ.lim (iter (ψᵛ p σ a +ˢ_) Ord₊ˢ.zero)
ψᵛ p σ (Ord₊ˢ.lim f) = Ord₊ˢ.lim (λ n → ψᵛ p σ (f n))
ψᵛ {j = j} p σ (Ord₊ˢ.limᵢ {i} r f) with <ᴵ-dec (σ r) p
... | injᵃ (via e s) = Ord₊ˢ.limᵢ s (λ y → ψᵛ p σ (f (intoˢ (<→◃ r) (tr⁻ˢ e (outˢ (<→◃ s) y)))))
... | injᵇ _ = Ord₊ˢ.lim (λ m → ψᵛ p σ (f (intoˢ (<→◃ r) (iter (λ x → ψᵛ (σ r) σ (f (intoˢ (<→◃ r) x))) (Ωˢ i) m))))
... | injᶜ _ = Ord₊ˢ.lim (λ m → ψᵛ p σ (f (intoˢ (<→◃ r) (iter (λ x → ψᵛ (σ r) σ (f (intoˢ (<→◃ r) x))) (Ωˢ i) m))))
ψᵛ {k = suc _} p σ (Ord₊ˢ.up zero x) = ψᵛ p (λ q → σ (suc q)) x
ψᵛ {k = lim _ _} p σ (Ord₊ˢ.up (self n) x) = ψᵛ p (λ q → σ (lim n q)) x
ψᵛ p σ (Ord₊ˢ.ŝ c t g) = ψᵛ p σ t
ψᵛ p σ (Ord₊ˢ.ĉᴸ c t g o₀ o) = ψᵛ p σ o₀
```

## §3 层号的加法

```agda
infixl 6 _⊕ᴸ_
_⊕ᴸ_ : LI → LI → LI
M ⊕ᴸ zero  = M
M ⊕ᴸ base  = times M
M ⊕ᴸ suc x = suc (M ⊕ᴸ x)
M ⊕ᴸ lim h = lim (λ n → M ⊕ᴸ h n)
M ⊕ᴸ lcl g = lcl (λ η → M ⊕ᴸ g η)

rp : LI → ℕ → LI
rp M zero    = zero
rp M (suc n) = M ⊕ᴸ rp M n
```

## §2 目标 1 到层号

`P¹`: 节点的参数层是 $0$ 就穿透, 成为 `lcl`; 否则是链, 链的目标是节点自己. 判决只看 $a$ 的头, 这是 `finD`: 退化的 `lim [0,0,…]` 会读错, 与 `Reg` 的情形相同.

```agda
ofI : Ordᴵ → Ordˢ zero
ofI zero = Ord₊ˢ.zero
ofI (suc a) = Ord₊ˢ.suc (ofI a)
ofI (lim f s) = Ord₊ˢ.lim (λ n → ofI (f n))

P¹ : ∀ {k ℓ} → Simᴵ k ℓ → Ordˢ k → LI
P¹ σ Ord₊ˢ.zero = base
P¹ σ (Ord₊ˢ.suc x) = lim (rp (P¹ σ x))
P¹ σ (Ord₊ˢ.lim f) = lim (λ n → P¹ σ (f n))
P¹ σ (Ord₊ˢ.limᵢ {i = zero} r f) = lcl (λ η → P¹ σ (f (intoˢ (<→◃ r) (ofI η))))
P¹ σ (Ord₊ˢ.limᵢ {i = suc a} r f) = lim (λ m → P¹ σ (f (intoˢ (<→◃ r) (iter (λ x → ψᵛ (σ r) σ (f (intoˢ (<→◃ r) x))) (Ωˢ (suc a)) m))))
P¹ σ (Ord₊ˢ.limᵢ {i = lim g s} r f) = lim (λ m → P¹ σ (f (intoˢ (<→◃ r) (iter (λ x → ψᵛ (σ r) σ (f (intoˢ (<→◃ r) x))) (Ωˢ (lim g s)) m))))
P¹ {k = suc _} σ (Ord₊ˢ.up zero x) = P¹ (λ q → σ (suc q)) x
P¹ {k = lim _ _} σ (Ord₊ˢ.up (self n) x) = P¹ (λ q → σ (lim n q)) x
P¹ σ (Ord₊ˢ.ŝ c t g) = P¹ σ t
P¹ σ (Ord₊ˢ.ĉᴸ c t g o₀ o) = P¹ σ o₀

F : Ordᴵ → LI
F θ = P¹ (λ q → q) (Ωˢ θ)

-- 第 5 站的层号: ψ₁(Ω_Ω) = sup_θ ψ₁(Ω_θ)
Lv₅ : LI
Lv₅ = lcl F
```

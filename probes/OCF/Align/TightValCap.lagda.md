# 紧界树比值 (二): 占位封顶定理

> [TightVal](TightVal.lagda.md) 的第二篇. **`Cap.capΩ`: 在目标 0 处, 紧界树 `ψᵉ′ ∅ˢ` 对一切 $\Omega_\eta$ 的任何证书计值, 都不超过四个低处的值 ($\psi_0(\Omega_\Omega)$, $\Omega_0,\Omega_1,\Omega_2$ 处的计值) 的公共上界 $B$.** $\eta$ 跑遍一切 `Ordᴵ`, 环境任意. 于是 `TΩ2′ˢ` 上不去 (`cap-T`).
>
> 机制: 第 $\ge2$ 层指数 $x$ 落进类 `C` 时, 目标 0 的折叠只看外形, 叶子只有三种: $x=0$ 给 $\psi_0(\Omega_\Omega)$; $x=a+1$ 给占位 $0$; $x=\Omega_k$ 退到更低的 $k$. 链点在高层目标上是折叠输出 (`cloE`), 所以都在 `C` 里, 链再长也不产生新东西.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. 定义与证明不读记号, $B$ 是参数. 证书只用 `Goodᴺ`, 不用它的单调和链的正确性: 这个上界对链点完全不敏感.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TightValCap where

open import Data.Nat using (ℕ; zero; suc)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open Ord-Ord using (iter)
open import OCF.Align.Level
open import OCF.Align.Prefix using (Z; ĉᴸ; Ord₊ˢ; Uˢ; Ordˢ; outˢ; intoˢ; toZ; Ωˢ)
open import OCF.Align.OmegaExpBase using (Stk; ψˢ; ∅ˢ; _▹Ω̂)
open import OCF.Align.OmegaSqBase using (ψᵉ′; repᴷ; _▹[_]_)
open import OCF.Align.OmegaSq using (TΩ2′ˢ; t₀′; gΩ)
open import OCF.Align.TightValBase
```

`High k`: `ψᵉ′` 在第 $k$ 层后继处走占位子句的层号, 字面上就是那三种模式.

```agda
data High : Ordᴵ → Set where
  h1 : ∀ {a} → High (suc (suc a))
  h2 : ∀ {f s} → High (suc (lim f s))
  h3 : ∀ {f s} → High (lim f s)

module Cap (B : Ordᶜ zero)
  (h∅  : ∀ {ℓ} (z p : zero <ᴵ ℓ) → Cp B (toZ ((∅ˢ ▹Ω̂) z p)))
  (hΩ₀ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ zero ℓ) → Cp B (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ zero))))
  (hΩ₁ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc zero) ℓ) → Cp B (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ (suc zero)))))
  (hΩ₂ : ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc (suc zero)) ℓ) → Cp B (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ (suc (suc zero))))))
  where

  capΩ : ∀ (η : Ordᴵ) {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ η ℓ) → Cp B (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ η)))
  cap  : ∀ {k} {x : Ordˢ k} → High k → C x → ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ k ℓ) → Cp B (toZ (ψᵉ′ ∅ˢ z p σ x))
  stepΩ : ∀ {k} → High k → ∀ {ℓ} (z p : zero <ᴵ ℓ) (σ : Simᴵ (suc k) ℓ) → Cp B (toZ (ψᵉ′ ∅ˢ z p σ (Ωˢ (suc k))))

  capΩ zero                z p σ = hΩ₀ z p σ
  capΩ (suc zero)          z p σ = hΩ₁ z p σ
  capΩ (suc (suc zero))    z p σ = hΩ₂ z p σ
  capΩ (suc (suc (suc a))) z p σ = stepΩ h1 z p σ
  capΩ (suc (suc (lim f s))) z p σ = stepΩ h2 z p σ
  capΩ (suc (lim f s))     z p σ = stepΩ h3 z p σ
  capΩ (lim f s)           z p σ = cp-lim (λ m → capΩ (f m) z p (λ q → σ (lim m q)))

  stepΩ {k} h z p σ with <ᴵ-dec (σ zero) p
  ... | injᵃ (via e ())
  ... | injᵇ _ = cp-lim (λ m → cap h (chain m) z p (λ q → σ (suc q)))
    where
    chain : ∀ m → C (iter (λ x → ψᵉ′ ∅ˢ z (σ zero) (λ q → σ (suc q)) x) (Ωˢ k) m)
    chain zero    = cΩ
    chain (suc m) = cloE ∅ˢ c∅ z (σ zero) (λ q → σ (suc q)) _
  ... | injᶜ _ = cp-lim (λ m → cap h (chain m) z p (λ q → σ (suc q)))
    where
    chain : ∀ m → C (iter (λ x → ψᵉ′ ∅ˢ z (σ zero) (λ q → σ (suc q)) x) (Ωˢ k) m)
    chain zero    = cΩ
    chain (suc m) = cloE ∅ˢ c∅ z (σ zero) (λ q → σ (suc q)) _

  cap {k} h cΩ z p σ = capΩ k z p σ
  cap h c0 z p σ = h∅ z p
  cap h1 cs z p σ = cp-zero
  cap h2 cs z p σ = cp-zero
  cap h3 cs z p σ = cp-zero
  cap h (cl H) z p σ = cp-lim (λ n → cap h (H n) z p σ)
  cap h (ci {q = q} H) z p σ with <ᴵ-dec (σ q) p
  ... | injᵃ (via e ())
  ... | injᵇ _ = cp-lim (λ m → cap h (H _) z p σ)
  ... | injᶜ _ = cp-lim (λ m → cap h (H _) z p σ)
  cap h1 (cŝ H₀ H) z p σ = cp-ĉ (cap h1 H₀ z p σ) (λ η e → cap h1 (H η e) z p σ)
  cap h2 (cŝ H₀ H) z p σ = cp-ĉ (cap h2 H₀ z p σ) (λ η e → cap h2 (H η e) z p σ)
  cap h3 (cŝ H₀ H) z p σ = cp-ĉ (cap h3 H₀ z p σ) (λ η e → cap h3 (H η e) z p σ)
  cap h (cĉ H₀ H) z p σ = cp-ĉ (cap h H₀ z p σ) (λ η e → cap h (H η e) z p σ)

  cap-T : Cp B (toZ TΩ2′ˢ)
  cap-T = cp-ĉ (capΩ (suc zero) _ _ _) (λ η e → capΩ η _ _ _)
```

**读法.** `stepΩ` 里 `injᵃ (via e ())`: 目标是 $0$, 没有 $r:\_<^\mathsf I0$, 穿透不可能. `chain`: 第 $k$ 层的链从 $\Omega_k$ 起, 其后都是目标 $k$ 上的折叠输出, 由 `cloE` 进 `C`. 这条定理没有用到链点的值, 所以 `Goodᴺ` 的 `ys`, `dy`, 单调字段都没用. `cap-T` 把 $\Omega_\eta$ 的上界收成 `TΩ2′ˢ` 的上界.

**这不是说 `TΩ2′ˢ` 有值.** 前提 `Goodᴺ` 可能无居留; 在 $\Omega_3$ 处确实无居留, 见 [TightValNeg](TightValNeg.lagda.md).

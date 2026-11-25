# YiFlat 吸收：第 1 层以上的两向吸收，只以左加数的值为前提

**验收文件，档位：编译定理。** 对任意层号 `a ≺ᴵ b` 与第 0 层的 `X`：若 `X` 与 ψ⁰(Ω_a) 两向相等 (一向 `≼ˣ`，一向值序)，则 `ψ⁰ (Ω b) ≼ˣ X + ψ⁰ (Ω b)` (`absΩ`)，以及反向 `X + ψ⁰ (Ω b) ≼ˣ ψ⁰ (Ω b)` (`absΩR`)。
`ABSΩ` 的两个结构假设已无条件：证书 `HS-flatΩ`，见证 `c = flat (Ω a)` 由 `flatΩ-≺`。只谈参照框架；用在链上见 [YiFlatChain](YiFlatChain.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFlatAbs where

import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼)
open import OCF.Align.YiVmConExact using (_≼ˣ_; reflˣ; ≅→≼ˣ)
open import OCF.Lean.YiZeroAccP using (+ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ)
open import OCF.Lean.YiChainBack using (module AbsR)
open import OCF.Lean.YiChainFlat using (flat; ψ⁰-flat; ABSΩ)
open import OCF.Lean.YiFlatObs using (HS-flatΩ)
open import OCF.Lean.YiFlatWit using (flatΩ-≺)
```

## 1 反向的压平吸收

与 `ABSΩ` 对称，用 [YiChainBack](YiChainBack.lagda.md) 的 `AbsR`。

```agda
ABSΩR : ∀ {X c : T₀} → X ≼ˣ L.ψ⁰ c → L.ψ⁰ c ≼ X → ∀ {k} (s : L.Ordᶜ k) → L.HS (flat s) → c L.≺ flat s →
  (X L.+ L.ψ⁰ s) ≼ˣ L.ψ⁰ s
ABSΩR {X} hx hv s h d = transˣ (+ˣ (reflˣ X) (≼-refl X) (≅→≼ˣ (ψ⁰-flat s)))
  (transˣ (AbsR.ABSR hx hv (flat s) h d) (≅→≼ˣ (L.≅-sym (ψ⁰-flat s))))
```

## 2 层号严格前驱上的两向吸收

见证取 `c = flat (Ω a)`；ψ⁰ c 与 ψ⁰ (Ω a) 结构互模拟 (`ψ⁰-flat`)，所以前提可以对 ψ⁰ (Ω a) 陈述。

```agda
absΩ : ∀ {a b} → a L.≺ᴵ b → ∀ {X : T₀} → L.ψ⁰ (L.Ω a) ≼ˣ X → X ≼ L.ψ⁰ (L.Ω a) →
  L.ψ⁰ (L.Ω b) ≼ˣ (X L.+ L.ψ⁰ (L.Ω b))
absΩ {a} {b} r hx hv = ABSΩ (transˣ (≅→≼ˣ (L.≅-sym (ψ⁰-flat (L.Ω a)))) hx) (≼-trans hv (≅→≼ (ψ⁰-flat (L.Ω a))))
  (L.Ω b) (HS-flatΩ b) (flatΩ-≺ r)

absΩR : ∀ {a b} → a L.≺ᴵ b → ∀ {X : T₀} → X ≼ˣ L.ψ⁰ (L.Ω a) → L.ψ⁰ (L.Ω a) ≼ X →
  (X L.+ L.ψ⁰ (L.Ω b)) ≼ˣ L.ψ⁰ (L.Ω b)
absΩR {a} {b} r hx hv = ABSΩR (transˣ hx (≅→≼ˣ (ψ⁰-flat (L.Ω a)))) (≼-trans (≅→≼ (L.≅-sym (ψ⁰-flat (L.Ω a)))) hv)
  (L.Ω b) (HS-flatΩ b) (flatΩ-≺ r)
```

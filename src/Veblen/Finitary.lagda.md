---
title: 形式化大数数学 (1.3 - 有限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.3 - 有限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Finitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Finitary.lagda.md)  
> 高亮渲染: [Finitary.html](https://choukh.github.io/agda-googology/Veblen.Finitary.html)  

```agda
{-# OPTIONS --lossy-unification #-}

module Veblen.Finitary where
open import Veblen.Multinary public
module Bin = BinaryVeblen
module Tri = TrinaryVeblen
module Qua = QuaternaryVeblen
```

有限元Veblen函数 (Finitary Veblen Function) 也叫扩展Veblen函数 (Extended Veblen Function).

## 有限元函数类型

**定义**

```agda
_→ⁿ_ : Set → ℕ → Set
A →ⁿ zero = A
A →ⁿ suc n = Ord → A →ⁿ n
```

```agda
_0⋯0 : A →ⁿ n → A
_0⋯0 {n = zero} = id
_0⋯0 {n = suc n} F = F 0 0⋯0
```

```agda
_0⋯_ : A →ⁿ (suc n) → A →ⁿ 1
_0⋯_ {n = zero} = id
_0⋯_ {n = suc n} F = F 0 0⋯_
```

```agda
_0⋯_,_ : A →ⁿ (2+ n) → A →ⁿ 2
_0⋯_,_ {n = zero} = id
_0⋯_,_ {n = suc n} F = F 0 0⋯_,_
```

**引理**

```agda
0-0⋯ : {F : A →ⁿ (suc n)} → F 0⋯0 ≡ F 0 0⋯0
0-0⋯ = refl

⋯0-0 : {F : A →ⁿ (suc n)} → F 0⋯0 ≡ F 0⋯ 0
⋯0-0 {n = zero} = refl
⋯0-0 {n = suc _} {F} = ⋯0-0 {F = F 0}
```

## 有限元Veblen函数

**定义**

```agda
Φ : Ord →ⁿ suc n → Ord →ⁿ 2+ n
Φⁿ : (Ord → Ord) → Ord →ⁿ suc n
```

```agda
Φ F = rec F
  (λ φ-α  → Φⁿ $ fixpt λ β → φ-α β 0⋯0)
  (λ φ[_] → Φⁿ $ jump λ β → lim λ n → φ[ n ] β 0⋯0)
```

```agda
Φⁿ {n = zero} = id
Φⁿ {n = suc n} F = Φ (Φⁿ F)
```

**定义**

```agda
φ : Ord →ⁿ suc n
φ = Φⁿ (ω ^_)
```

**事实**

```agda
Φ-φ : φ {suc n} ≡ Φ (φ {n})
Φ-φ = refl
```

**事实**

```agda
φ-0 : φ {suc n} 0 ≡ φ {n}
φ-0 = refl
```

**例**

```agda
φ₀ : φ {0} ≡ ω ^_
φ₀ = refl
```

```agda
φ₁ : φ {1} ≡ Bin.φ
φ₁ = refl
```

```agda
φ₂ : φ {2} ≡ Tri.φ
φ₂ = refl
```

```agda
φ₃ : φ {3} ≡ Qua.φ
φ₃ = refl
```

**引理**

```agda
Φⁿ-0⋯x : Φⁿ {n} F 0⋯_ ≡ F
Φⁿ-0⋯x {n = zero} = refl
Φⁿ-0⋯x {n = suc n} = Φⁿ-0⋯x {n}
```

**定理**

```agda
φ-s-z⋯x : φ {suc n} (suc α) 0⋯_ ≡ fixpt λ β → φ α β 0⋯0
φ-s-z⋯x {n} {α} = begin
  φ {suc n} (suc α) 0⋯_           ≡⟨⟩
  Φ (φ {n}) (suc α) 0⋯_           ≡⟨⟩
  Φⁿ (fixpt λ β → φ α β 0⋯0) 0⋯_  ≡⟨ Φⁿ-0⋯x ⟩
  fixpt (λ β → φ α β 0⋯0)         ∎
```

**定理**

```agda
φ-l-z⋯x : φ {suc n} (lim f) 0⋯_ ≡ jump λ β → lim λ m → φ {suc n} (f m) β 0⋯0
φ-l-z⋯x {n} {f} = begin
  φ {suc n} (lim f) 0⋯_                       ≡⟨⟩
  Φ (φ {n}) (lim f) 0⋯_                       ≡⟨⟩
  Φⁿ (jump λ β → lim λ m → φ (f m) β 0⋯0) 0⋯_ ≡⟨ Φⁿ-0⋯x ⟩
  jump (λ β → lim λ m → φ (f m) β 0⋯0)        ∎
```

回想二元Veblen函数的计算式

$$
\begin{aligned}
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}0 &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}0 \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(β^+) &= \text{lim}\kern{0.17em}λn,φ_{f\kern{0.17em}n}\kern{0.17em}(\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}β)^+ \\
\varphi_{\text{lim}\kern{0.17em}f}\kern{0.17em}(\text{lim}\kern{0.17em}g) &= \text{lim}\kern{0.17em}λn,φ_{\text{lim}\kern{0.17em}f}\kern{0.17em}(g\kern{0.17em}n)
\end{aligned}
$$

**推论**

```agda
φ-l-z⋯z : φ {n} (lim f) 0⋯0 ≡ lim λ m → φ {n} (f m) 0⋯0
φ-l-z⋯z {n = zero} = refl
φ-l-z⋯z {n = suc n} {f} = begin
  φ {suc n} (lim f) 0 0⋯0                         ≡⟨ ⋯0-0 ⟩
  φ {suc n} (lim f) 0⋯ 0                          ≡⟨ cong-app φ-l-z⋯x 0 ⟩
  jump (λ β → lim λ m → φ {suc n} (f m) β 0⋯0) 0  ≡⟨⟩
  lim (λ m → φ (f m) 0⋯0)                         ∎
```

```agda
φ-l-z⋯s : φ {suc n} (lim f) 0⋯ (suc α) ≡ lim λ m → φ (f m) (suc (φ {suc n} (lim f) 0⋯ α)) 0⋯0
φ-l-z⋯s {n} {f} {α} =
  let j = jump λ β → lim λ m → φ (f m) β 0⋯0 in   begin
  φ {suc n} (lim f) 0⋯ (suc α)                    ≡⟨ cong-app φ-l-z⋯x (suc α) ⟩
  j (suc α)                                       ≡⟨⟩
  lim (λ m → φ (f m) (suc (j α)) 0⋯0)             ≡˘⟨
    cong (λ x → lim (λ m → φ {suc n} (f m) (suc (x α)) 0⋯0)) φ-l-z⋯x ⟩
  lim (λ m → φ (f m) (suc (φ (lim f) 0⋯ α)) 0⋯0)  ∎
```

```agda
φ-l-z⋯l : φ {suc n} (lim f) 0⋯ (lim g) ≡ lim λ m → φ (lim f) 0⋯ (g m)
φ-l-z⋯l {n} {f} {g} =
  let j = jump λ β → lim λ m → φ (f m) β 0⋯0 in begin
  φ {suc n} (lim f) 0⋯ (lim g)                  ≡⟨ cong-app φ-l-z⋯x (lim g) ⟩
  j (lim g)                                     ≡⟨⟩
  lim (λ m → j (g m))                           ≡˘⟨ cong (λ x → lim (λ m → x (g m))) φ-l-z⋯x ⟩
  lim (λ m → φ (lim f) 0⋯ (g m))                ∎
```

**定理**

```agda
φ-x-s-0⋯y : φ {2+ n} α (suc β) 0⋯_ ≡ fixpt λ γ → φ {2+ n} α β γ 0⋯0
φ-x-s-0⋯y {n = zero} {α = zero} = refl
φ-x-s-0⋯y {n = zero} {α = suc _} = refl
φ-x-s-0⋯y {n = zero} {α = lim _} = refl
φ-x-s-0⋯y {n = suc n} {α = zero} = Φⁿ-0⋯x
φ-x-s-0⋯y {n = suc n} {α = suc _} = Φⁿ-0⋯x
φ-x-s-0⋯y {n = suc n} {α = lim _} = Φⁿ-0⋯x

φ-x-l-0⋯y : φ {2+ n} α (lim f) 0⋯_ ≡ jump λ δ → lim λ m → φ {2+ n} α (f m) δ 0⋯0
φ-x-l-0⋯y {n = zero} {α = zero} = refl
φ-x-l-0⋯y {n = zero} {α = suc _} = refl
φ-x-l-0⋯y {n = zero} {α = lim _} = refl
φ-x-l-0⋯y {n = suc n} {α = zero} = Φⁿ-0⋯x
φ-x-l-0⋯y {n = suc n} {α = suc _} = Φⁿ-0⋯x
φ-x-l-0⋯y {n = suc n} {α = lim _} = Φⁿ-0⋯x
```

**引理**

```agda
Φ-0⋯s-x : Φ {n} (Φⁿ F) 0⋯ (suc α) ,_ ≡ fixpt (Φ {n} (Φⁿ F) 0⋯ α ,_)
Φ-0⋯s-x {n = zero} = refl
Φ-0⋯s-x {n = suc n} = Φ-0⋯s-x {n}

Φ-0⋯l-x : Φ {n} (Φⁿ F) 0⋯ (lim f) ,_ ≡ jump λ β → lim λ m → Φ {n} (Φⁿ F) 0⋯ (f m) , β
Φ-0⋯l-x {n = zero} = refl
Φ-0⋯l-x {n = suc n} = Φ-0⋯l-x {n}
```

**定理**

```agda
φ-0⋯s-x : φ {suc n} 0⋯ (suc α) ,_ ≡ fixpt (φ {suc n} 0⋯ α ,_)
φ-0⋯s-x = Φ-0⋯s-x

φ-0⋯l-x : φ {suc n} 0⋯ (lim f) ,_ ≡ jump λ β → lim λ m → φ {suc n} 0⋯ (f m) , β
φ-0⋯l-x = Φ-0⋯l-x
```

**定理**

```agda
φ-x-0⋯s-y : φ {2+ n} α 0⋯ (suc β) ,_ ≡ fixpt (φ {2+ n} α 0⋯ β ,_)
φ-x-0⋯s-y {n = zero} {α = zero} = refl
φ-x-0⋯s-y {n = zero} {α = suc _} = refl
φ-x-0⋯s-y {n = zero} {α = lim _} = refl
φ-x-0⋯s-y {n = suc n} {α = zero} = Φ-0⋯s-x
φ-x-0⋯s-y {n = suc n} {α = suc _} = Φ-0⋯s-x
φ-x-0⋯s-y {n = suc n} {α = lim _} = Φ-0⋯s-x

φ-x-0⋯l-y : φ {2+ n} α 0⋯ (lim f) ,_ ≡ jump λ δ → lim λ m → φ {2+ n} α 0⋯ (f m) , δ
φ-x-0⋯l-y {n = zero} {α = zero} = refl
φ-x-0⋯l-y {n = zero} {α = suc _} = refl
φ-x-0⋯l-y {n = zero} {α = lim _} = refl
φ-x-0⋯l-y {n = suc n} {α = zero} = Φ-0⋯l-x
φ-x-0⋯l-y {n = suc n} {α = suc _} = Φ-0⋯l-x
φ-x-0⋯l-y {n = suc n} {α = lim _} = Φ-0⋯l-x
```

## SVO

**定义**

SVO (~~Subject–Verb–Object~~ Small Veblen Ordinal)

```agda
SVO : Ord
SVO = lim λ n → φ {n} 1 0⋯0
```

一个很大的大数:

```agda
svo₉₉ = FGH.f SVO 99
```

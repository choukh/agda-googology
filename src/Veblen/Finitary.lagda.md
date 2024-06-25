---
title: 形式化大数数学 (1.3 - 任意有限元Veblen函数)
zhihu-tags: Agda, 序数, 大数数学
---

# 形式化大数数学 (1.3 - 任意有限元Veblen函数)

> 交流Q群: 893531731  
> 本文源码: [Finitary.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/Veblen/Finitary.lagda.md)  
> 高亮渲染: [Finitary.html](https://choukh.github.io/agda-googology/Veblen.Finitary.html)  

```agda
module Veblen.Finitary where
open import Veblen.Multinary public
module Bin = BinaryVeblen
module Tri = TrinaryVeblen
module Qua = QuaternaryVeblen
```

任意有限元Veblen函数 (Finitary Veblen Function) 也叫扩展Veblen函数 (Extended Veblen Function).

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

```agda
Φ : Ord →ⁿ suc n → Ord →ⁿ 2+ n
Ψ : Ord →ⁿ 1 → Ord →ⁿ suc n
```

```agda
Φ F = rec F
  (λ φ-α  → Ψ $ fixpt λ β → φ-α β 0⋯0)
  (λ φ[_] → Ψ $ jump λ β → lim λ n → φ[ n ] β 0⋯0)
```

```agda
Ψ {n = zero} = id
Ψ {n = suc n} F = Φ (Ψ F)
```

```agda
φ : Ord →ⁿ suc n
φ = Ψ (ω ^_)
```

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

SVO (~~Subject–Verb–Object~~ Small Veblen Ordinal)

```agda
SVO : Ord
SVO = lim λ n → φ {n} 1 0⋯0
```

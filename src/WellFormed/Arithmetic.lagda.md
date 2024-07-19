---
title: 形式化大数数学 (2.1 - 序数算术)
zhihu-tags: Agda, 大数数学, 序数
---

# 形式化大数数学 (2.1 - 序数算术)

> 交流Q群: 893531731  
> 本文源码: [Arithmetic.lagda.md](https://github.com/choukh/agda-googology/blob/main/src/WellFormed/Arithmetic.lagda.md)  
> 高亮渲染: [Arithmetic.html](https://choukh.github.io/agda-googology/WellFormed.Arithmetic.html)  

```agda
{-# OPTIONS --safe --lossy-unification #-}
module WellFormed.Arithmetic where
open import WellFormed.Base
```

```agda
private
  pres = ^⟨◌⟩-pres<
  instance
    _ = z≤
    _ = ≤-refl
    _ : NonZero (suc a)
    _ = _
    _ : ⦃ _ : f ⇡ ⦄ → NonZero (lim f)
    _ = _
```

**约定** 非平凡序数指不等于零或一的序数.

```agda
not01 : Ord → Set
not01 zero       = ⊥
not01 (suc zero) = ⊥
not01 _          = ⊤

record NonTrivial (a : Ord) : Set where
  field nonTrivial : not01 a
```

```agda
nt-intro : 1 < a → NonTrivial a
nt-intro {suc zero} (suc₂ ())
nt-intro {2+ a}         _ = _
nt-intro {suc (lim _)}  _ = _
nt-intro {lim _}        _ = _

nt-elim : ⦃ NonTrivial a ⦄ → 1 < a
nt-elim {2+ _}        = s<s z<s
nt-elim {suc (lim _)} = s<s z<l
nt-elim {lim f}       = lim₂ (n<fs f 1)
```

## 加法

```agda
_+_ : Ord → Ord → Ord; infixl 6 _+_
+◌-pres< : (a +_) preserves _<_

zero + b = b
a + zero = a
a + suc b = suc (a + b)
a + lim f = lim (λ n → a + f n) ⦃ +◌-pres< it ⦄

+◌-pres< {a = zero}             = id
+◌-pres< {a = suc a} suc        = suc
+◌-pres< {a = suc a} (suc₂ p)   = suc₂ (+◌-pres< p)
+◌-pres< {a = suc a} lim        = lim ⦃ +◌-pres< it ⦄
+◌-pres< {a = suc a} (lim₂ p)   = lim₂ ⦃ +◌-pres< it ⦄ (+◌-pres< p)
+◌-pres< {a = lim f} suc        = suc
+◌-pres< {a = lim f} (suc₂ p)   = suc₂ (+◌-pres< p)
+◌-pres< {a = lim f} lim        = lim ⦃ +◌-pres< it ⦄
+◌-pres< {a = lim f} (lim₂ p)   = lim₂ ⦃ +◌-pres< it ⦄ (+◌-pres< p)
```

左右幺元

```agda
+-idˡ : zero + a ≡ a
+-idˡ = refl

+-idʳ : ∀ a → a + zero ≡ a
+-idʳ zero = refl
+-idʳ (suc a) = refl
+-idʳ (lim f) = refl
```

结合律

```agda
+-assoc : a + (b + c) ≡ (a + b) + c
+-assoc {a = zero} = refl
+-assoc {a} {b = zero} rewrite +-idʳ a = refl
+-assoc {a} {b} {c = zero} rewrite +-idʳ b | +-idʳ (a + b) = refl
+-assoc {a = suc a} {b = suc b} {c = suc c} = cong suc (+-assoc {suc a} {suc b} {c})
+-assoc {a = lim a} {b = suc b} {c = suc c} = cong suc (+-assoc {lim a} {suc b} {c})
+-assoc {a = suc a} {b = lim b} {c = suc c} = cong suc (+-assoc {suc a} {lim b} {c})
+-assoc {a = lim a} {b = lim b} {c = suc c} = cong suc (+-assoc {lim a} {lim b} {c})
+-assoc {a = suc a} {b = suc b} {c = lim c} = {!   !}
+-assoc {a = lim a} {b = suc b} {c = lim c} = {!   !}
+-assoc {a = suc a} {b = lim b} {c = lim c} = {!   !}
+-assoc {a = lim a} {b = lim b} {c = lim c} = {!   !}
```

```agda
◌+_ : (b : Ord) → ⦃ NonZero b ⦄ → Iterable
◌+ b = iterable 0 (_+ b) {!   !}
```

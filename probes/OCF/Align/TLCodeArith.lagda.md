# 严格列 (三): 列的写法, 检查点

> 入口 [TLCode](TLCode.lagda.md). **判决: HOLDS (编译过, 无条件).** 这里的算术只是通常的序数加法, $\omega^x$, 落在 `Ordᴵ` 上; 没有 `Code`, 没有 $\sum_j(g_j+1)$. 每个检查点是一个严格列加证书:
>
> | 码 | 项 | 列 |
> | --- | --- | --- |
> | `Lω` | `ωᴵ` | $0,1,2,\dots$ |
> | `Lω·2` | `ω·2ᴸ` | $\omega,\omega+1,\dots$ |
> | `Lω²` | `ω²ᴸ` | $\omega,\omega\cdot2,\dots$ |
> | `Lω^ω` | `ω^ωᴸ` | $\omega^0,\omega^1,\dots$, 即 `E ωᴵ` |
> | `Lε₀` | `ε₀ᴸ` | $\omega^1,\omega^{\omega^1},\dots$ |
>
> `Lε₀` 的证书是实质内容: $\omega^x$ 把字面子项映到字面子项 (`E<`), 所以塔的后一项字面含前一项. **不用加分隔符.** 底取 $\omega^1$ 不取 `ωᴵ`: `ωᴵ` 不是 $\omega^{\omega}$ 的字面子项 (列差一个头), 这是写法的事, 值相同是判断. 这些项的读值 (`E` 是 $\omega^x$) 是判断, 项本身和证书是定理. 与现有的树的关系见 [TLCodeAccept](TLCodeAccept.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeArith where

open import Data.Nat using (ℕ; zero; suc)
open import OCF.Free.Level using (Ordᴵ; zero; suc; lim; _<ᴵ_; _⊑ᴵ_; _≅ᴵ_; z⊑; s⊑; l⊑; z≅; s≅; l≅; <ᴵ-trans; ⊑ᴵ-trans; Sim→⊑ᴵ; ≅ᴵ-refl; natᴵ; natᴵ-step; ωᴵ)
open import OCF.Align.TLCodeLit
```

## §1 由字面路径造极限

```agda
<→⊑ : ∀ {a b} → a <ᴵ b → a ⊑ᴵ b
<→⊑ r = Sim→⊑ᴵ (λ q → <ᴵ-trans q r)

limᴸ : (f : ℕ → Ordᴵ) → (∀ n → f n <ᴵ f (suc n)) → Ordᴵ
limᴸ f r = lim f (λ n → <→⊑ (r n))

≅→⊑ᴵ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅→⊑ᴵ z≅ = z⊑
≅→⊑ᴵ (s≅ e) = s⊑ e zero
≅→⊑ᴵ (l≅ h) = l⊑ (λ n → ⊑ᴵ-trans (≅→⊑ᴵ (h n)) (Sim→⊑ᴵ (lim n)))
```

## §2 $\omega$, $a+\omega$, $\omega\cdot n$, $\omega^2$

```agda
Lnat : ∀ n → Lit (natᴵ n)
Lnat zero = lz
Lnat (suc n) = ls (Lnat n)

Lω : Lit ωᴵ
Lω = ll Lnat (λ n → zero)

addN : Ordᴵ → ℕ → Ordᴵ
addN a zero = a
addN a (suc n) = suc (addN a n)

Laddn : ∀ {a} → Lit a → ∀ n → Lit (addN a n)
Laddn h zero = h
Laddn h (suc n) = ls (Laddn h n)

-- a + ω
_+ω : Ordᴵ → Ordᴵ
a +ω = limᴸ (addN a) (λ n → zero)

L+ω : ∀ {a} → Lit a → Lit (a +ω)
L+ω h = ll (Laddn h) (λ n → zero)

-- ω·(k+1)
ω·ᴸ : ℕ → Ordᴵ
ω·ᴸ zero = ωᴵ
ω·ᴸ (suc k) = ω·ᴸ k +ω

Lω· : ∀ k → Lit (ω·ᴸ k)
Lω· zero = Lω
Lω· (suc k) = L+ω (Lω· k)

ω·2ᴸ : Ordᴵ
ω·2ᴸ = ω·ᴸ 1

Lω·2 : Lit ω·2ᴸ
Lω·2 = Lω· 1

ω²ᴸ : Ordᴵ
ω²ᴸ = limᴸ ω·ᴸ (λ k → lim 1 zero)

Lω² : Lit ω²ᴸ
Lω² = ll Lω· (λ k → lim 1 zero)
```

## §3 序数加法

```agda
infixl 6 _⊕_
_⊕_ : Ordᴵ → Ordᴵ → Ordᴵ
⊕-mono : ∀ a {x y} → x ⊑ᴵ y → a ⊕ x ⊑ᴵ a ⊕ y
⊕-path : ∀ a {x y} → x <ᴵ y → a ⊕ x <ᴵ a ⊕ y
⊕-≅ : ∀ {a a′} {x y} → a ≅ᴵ a′ → x ≅ᴵ y → a ⊕ x ≅ᴵ a′ ⊕ y
⊑⊕ : ∀ a y → a ⊑ᴵ a ⊕ y
<⊕ : ∀ a y {c} → c <ᴵ a → c <ᴵ a ⊕ y
a ⊕ zero = a
a ⊕ suc b = suc (a ⊕ b)
a ⊕ lim f s = lim (λ n → a ⊕ f n) (λ n → ⊕-mono a (s n))
⊕-mono a z⊑ = ⊑⊕ a _
⊕-mono a (s⊑ e q) = s⊑ (⊕-≅ (≅ᴵ-refl a) e) (⊕-path a q)
⊕-mono a (l⊑ h) = l⊑ (λ n → ⊕-mono a (h n))
⊕-path a zero = zero
⊕-path a (suc q) = suc (⊕-path a q)
⊕-path a (lim n q) = lim n (⊕-path a q)
⊕-≅ e z≅ = e
⊕-≅ e (s≅ d) = s≅ (⊕-≅ e d)
⊕-≅ e (l≅ h) = l≅ (λ n → ⊕-≅ e (h n))
⊑⊕ a y = Sim→⊑ᴵ (<⊕ a y)
<⊕ a zero q = q
<⊕ a (suc y) q = suc (<⊕ a y q)
<⊕ a (lim f s) q = lim 0 (<⊕ a (f 0) q)

L⊕ : ∀ {a b} → Lit a → Lit b → Lit (a ⊕ b)
L⊕ ha lz = ha
L⊕ ha (ls hb) = ls (L⊕ ha hb)
L⊕ {a} ha (ll hf hr) = ll (λ n → L⊕ ha (hf n)) (λ n → ⊕-path a (hr n))
```

## §4 $\omega^x$

`E x` 是 $\omega^x$, `E (suc a)` 的列是 $\omega^a\cdot(k+1)$, 极限是逐项.

```agda
M : Ordᴵ → ℕ → Ordᴵ
M x zero = x
M x (suc k) = M x k ⊕ x

M-step : ∀ x k → M x k ⊑ᴵ M x (suc k)
M-step x k = ⊑⊕ (M x k) x

M-≅ : ∀ {x y} → x ≅ᴵ y → ∀ k → M x k ≅ᴵ M y k
M-≅ e zero = e
M-≅ e (suc k) = ⊕-≅ (M-≅ e k) e

E : Ordᴵ → Ordᴵ
E-mono : ∀ {x y} → x ⊑ᴵ y → E x ⊑ᴵ E y
E-≅ : ∀ {x y} → x ≅ᴵ y → E x ≅ᴵ E y
E-M : ∀ {a y} → a <ᴵ y → ∀ k → M (E a) k <ᴵ E y
z<E : ∀ y → zero <ᴵ E y
pos : ∀ x a → a <ᴵ a ⊕ E x
E zero = suc zero
E (suc a) = lim (M (E a)) (M-step (E a))
E (lim f s) = lim (λ n → E (f n)) (λ n → E-mono (s n))
E-mono {y = y} z⊑ = s⊑ z≅ (z<E y)
E-mono (s⊑ e q) = l⊑ (λ k → ⊑ᴵ-trans (≅→⊑ᴵ (M-≅ (E-≅ e) k)) (<→⊑ (E-M q k)))
E-mono (l⊑ h) = l⊑ (λ n → E-mono (h n))
E-≅ z≅ = s≅ z≅
E-≅ (s≅ e) = l≅ (M-≅ (E-≅ e))
E-≅ (l≅ h) = l≅ (λ n → E-≅ (h n))
E-M {a} zero k = lim (suc k) (pos a (M (E a) k))
E-M {a} (suc {b = y} q) k = lim 1 (<ᴵ-trans (E-M q k) (pos y (E y)))
E-M (lim n q) k = lim n (E-M q k)
z<E zero = zero
z<E (suc a) = lim 0 (z<E a)
z<E (lim f s) = lim 0 (z<E (f 0))
pos zero a = zero
pos (suc x) a = lim 0 (pos x a)
pos (lim f s) a = lim 0 (pos (f 0) a)

-- 字面子项映到字面子项
E< : ∀ {a y} → a <ᴵ y → E a <ᴵ E y
E< q = E-M q 0

LM : ∀ {x} → Lit x → ∀ k → Lit (M x k)
LM h zero = h
LM h (suc k) = L⊕ (LM h k) h

LE : ∀ {x} → Lit x → Lit (E x)
LE lz = ls lz
LE {suc a} (ls h) = ll (LM (LE h)) (λ k → pos a (M (E a) k))
LE (ll hf hr) = ll (λ n → LE (hf n)) (λ n → E< (hr n))
```

## §5 $\omega^\omega$, $\varepsilon_0$

```agda
ω^ωᴸ : Ordᴵ
ω^ωᴸ = E ωᴵ

Lω^ω : Lit ω^ωᴸ
Lω^ω = LE Lω

tw : ℕ → Ordᴵ
tw zero = E (suc zero)
tw (suc n) = E (tw n)

tw< : ∀ n → tw n <ᴵ tw (suc n)
tw< zero = E< (lim 1 zero)
tw< (suc n) = E< (tw< n)

Ltw : ∀ n → Lit (tw n)
Ltw zero = LE (ls lz)
Ltw (suc n) = LE (Ltw n)

ε₀ᴸ : Ordᴵ
ε₀ᴸ = limᴸ tw tw<

Lε₀ : Lit ε₀ᴸ
Lε₀ = ll Ltw tw<
```

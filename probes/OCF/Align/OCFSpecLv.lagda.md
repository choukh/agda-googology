# 折叠的外部规格: 搬到 `Lv` 上 (陈述)

> 底座, 不含记号. 结论写在 [OCFSpec](OCFSpec.lagda.md). `Ordᶜ` 装不下 $\Omega_\Omega$ (壁垒: 不可数下标不是可数层的构造子). [InaccTreeBase](InaccTreeBase.lagda.md) 的 `Ordᴸ` 装得下: `limᴼ` 的分支读树. 本文把规格逐字搬过去: 值序 `≼ᴸ`, 良基 `wfᴸ`, 下标的值 `rf`, 闭包 `Clᴸ₊`, `IsPsiᴸ`. **只有定义与陈述, 没有锚点.** 它说明的是: 规格本身不要判决 `S`, 也不要 `<ᴵ-dec`, $\psi_0(\Omega_\Omega+1)$ 能不带替身地写出来.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OCFSpecLv where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)

open import OCF.Align.InaccTreeBase using
  (Lv; zero; suc; lim; limᴼ; Ordᴸ; Pre; Low; Dn; DnT; at; down; outL; intoL; outD; intoD; Tree; limᵢ; up; Ω; toLv; Sim; add)

infix 4 _≼ᴸ_ _≺ᴸ_

data _≼ᴸ_ : ∀ {ℓ₁ ℓ₂} → Ordᴸ ℓ₁ → Ordᴸ ℓ₂ → Set where
  z≼  : ∀ {ℓ₁ ℓ₂} {b : Ordᴸ ℓ₂} → _≼ᴸ_ {ℓ₁} {ℓ₂} Tree.zero b
  s≼s : ∀ {ℓ₁ ℓ₂} {a : Ordᴸ ℓ₁} {b : Ordᴸ ℓ₂} → a ≼ᴸ b → Tree.suc a ≼ᴸ Tree.suc b
  ≼l  : ∀ {ℓ₁ ℓ₂} {a : Ordᴸ ℓ₁} {f : ℕ → Ordᴸ ℓ₂} n → a ≼ᴸ f n → a ≼ᴸ Tree.lim f
  l≼  : ∀ {ℓ₁ ℓ₂} {f : ℕ → Ordᴸ ℓ₁} {b : Ordᴸ ℓ₂} → (∀ n → f n ≼ᴸ b) → Tree.lim f ≼ᴸ b
  ≼i  : ∀ {ℓ₁ ℓ₂} {a : Ordᴸ ℓ₁} {r : Pre ℓ₂} {f : Low ℓ₂ r → Ordᴸ ℓ₂}
        (x : Ordᴸ (at ℓ₂ r)) → a ≼ᴸ f (intoL ℓ₂ r x) → a ≼ᴸ limᵢ r f
  i≼  : ∀ {ℓ₁ ℓ₂} {r : Pre ℓ₁} {f : Low ℓ₁ r → Ordᴸ ℓ₁} {b : Ordᴸ ℓ₂} →
        (∀ (x : Ordᴸ (at ℓ₁ r)) → f (intoL ℓ₁ r x) ≼ᴸ b) → limᵢ r f ≼ᴸ b
  ≼u  : ∀ {ℓ₁ ℓ₂} {a : Ordᴸ ℓ₁} {d : Dn ℓ₂} {y : DnT ℓ₂ d} → a ≼ᴸ outD ℓ₂ d y → a ≼ᴸ up d y
  u≼  : ∀ {ℓ₁ ℓ₂} {d : Dn ℓ₁} {y : DnT ℓ₁ d} {b : Ordᴸ ℓ₂} → outD ℓ₁ d y ≼ᴸ b → up d y ≼ᴸ b

_≺ᴸ_ : ∀ {ℓ₁ ℓ₂} → Ordᴸ ℓ₁ → Ordᴸ ℓ₂ → Set
a ≺ᴸ b = Tree.suc a ≼ᴸ b
```

`rf`: 层号的值, 作树. `limᴼ k g` 的值是 $\sup_{x}g(x)$, 分支读第 $k$ 层的树, 所以 `rf` 的层就是把 `limᴼ` 的骨架留下. 这是 `forget` 的版本: 第 0 层放不下它, 这就是 `Ordᶜ` 不够的地方.

```agda
ρ : Lv → Lv
ρ zero       = zero
ρ (suc k)    = ρ k
ρ (lim f)    = lim (λ n → ρ (f n))
ρ (limᴼ k g) = limᴼ k (λ x → ρ (g x))

rf : (u : Lv) → Ordᴸ (ρ u)
rf zero       = Tree.zero
rf (suc k)    = Tree.suc (rf k)
rf (lim f)    = Tree.lim (λ n → up n (rf (f n)))
rf (limᴼ k g) = limᵢ (inj₁ (inj₁ tt)) (λ x → up x (rf (g x)))

data Accᴸ {k} (a : Ordᴸ k) : Set where
  acc : (∀ {m} (ξ : Ordᴸ m) → ξ ≺ᴸ a → Accᴸ ξ) → Accᴸ a

≼ᴸ-trans : ∀ {ℓ₁ ℓ₂ ℓ₃} {a : Ordᴸ ℓ₁} {b : Ordᴸ ℓ₂} {c : Ordᴸ ℓ₃} → a ≼ᴸ b → b ≼ᴸ c → a ≼ᴸ c
≼ᴸ-trans z≼       q        = z≼
≼ᴸ-trans p        (≼l n q) = ≼l n (≼ᴸ-trans p q)
≼ᴸ-trans p        (≼i x q) = ≼i x (≼ᴸ-trans p q)
≼ᴸ-trans p        (≼u q)   = ≼u (≼ᴸ-trans p q)
≼ᴸ-trans (l≼ p)   q        = l≼ (λ n → ≼ᴸ-trans (p n) q)
≼ᴸ-trans (i≼ p)   q        = i≼ (λ x → ≼ᴸ-trans (p x) q)
≼ᴸ-trans (u≼ p)   q        = u≼ (≼ᴸ-trans p q)
≼ᴸ-trans (s≼s p)  (s≼s q)  = s≼s (≼ᴸ-trans p q)
≼ᴸ-trans (≼l n p) (l≼ q)   = ≼ᴸ-trans p (q n)
≼ᴸ-trans (≼i x p) (i≼ q)   = ≼ᴸ-trans p (q x)
≼ᴸ-trans (≼u p)   (u≼ q)   = ≼ᴸ-trans p q

acc-≼ᴸ : ∀ {k m} {x : Ordᴸ k} {y : Ordᴸ m} → x ≼ᴸ y → Accᴸ y → Accᴸ x
acc-≼ᴸ p (acc h) = acc (λ ξ q → h ξ (≼ᴸ-trans q p))

wfᴸ    : ∀ {k} (a : Ordᴸ k) → Accᴸ a
belowᴸ : ∀ {k} (a : Ordᴸ k) → ∀ {m} (ξ : Ordᴸ m) → ξ ≺ᴸ a → Accᴸ ξ
wfᴸ a = acc (belowᴸ a)
belowᴸ (Tree.suc b)  ξ (s≼s p)  = acc-≼ᴸ p (wfᴸ b)
belowᴸ (Tree.lim f)  ξ (≼l n q) = belowᴸ (f n) ξ q
belowᴸ {k} (limᵢ r f) ξ (≼i x q) = belowᴸ (f (intoL k r x)) ξ q
belowᴸ {suc k}    (up d y) ξ (≼u q) = belowᴸ y ξ q
belowᴸ {lim f}    (up d y) ξ (≼u q) = belowᴸ y ξ q
belowᴸ {limᴼ k g} (up d y) ξ (≼u q) = belowᴸ y ξ q

module _ (v : Lv) {k} (a : Ordᴸ k)
         (Rec : (u : Lv) → ∀ {m} (ξ : Ordᴸ m) → ξ ≺ᴸ a → ∀ {n} → Ordᴸ n → Set) where
  data Clᴸ₊ : ∀ {m} → Ordᴸ m → Set where
    base : ∀ {m} {x : Ordᴸ m} → x ≺ᴸ Ω v → Clᴸ₊ x
    plus : ∀ {m k′} {x : Ordᴸ m} {y : Ordᴸ k′} (σ : Sim k′ m) → Clᴸ₊ x → Clᴸ₊ y → Clᴸ₊ (add x σ y)
    col  : ∀ {u m n} {ξ : Ordᴸ m} {x : Ordᴸ n} → Clᴸ₊ (rf u) → Clᴸ₊ ξ → (q : ξ ≺ᴸ a) → Rec u ξ q x → Clᴸ₊ x
    cg   : ∀ {m n} {x : Ordᴸ m} {y : Ordᴸ n} → y ≼ᴸ x → x ≼ᴸ y → Clᴸ₊ x → Clᴸ₊ y

record Witᴸ (v : Lv) (S : ∀ {m} → Ordᴸ m → Set) {n} (y : Ordᴸ n) : Set where
  constructor wit
  field
    {pt} : Ordᴸ v
    mem  : S pt
    bd   : pt ≺ᴸ Ω (suc v)
    dom  : y ≼ᴸ pt

record Supᴸ (v : Lv) (S : ∀ {m} → Ordᴸ m → Set) {n} (t : Ordᴸ n) : Set where
  constructor sup
  field
    lt  : t ≺ᴸ Ω (suc v)
    ub  : ∀ {m} {x : Ordᴸ m} → S x → x ≺ᴸ Ω (suc v) → x ≺ᴸ t
    cof : ∀ {m} {y : Ordᴸ m} → y ≺ᴸ t → Witᴸ v S y

IsPsiᴸₐ : (v : Lv) → ∀ {k} (a : Ordᴸ k) → Accᴸ a → ∀ {n} → Ordᴸ n → Set
IsPsiᴸₐ v a (acc h) t = Supᴸ v (Clᴸ₊ v a (λ u ξ q x → IsPsiᴸₐ u ξ (h ξ q) x)) t

IsPsiᴸ : (v : Lv) → ∀ {k} (a : Ordᴸ k) → ∀ {n} → Ordᴸ n → Set
IsPsiᴸ v a t = IsPsiᴸₐ v a (wfᴸ a) t
```

**陈述.** `LΩ` 是 $\Omega$ 的层号, 所以 `Ω LΩ` 是 $\Omega_\Omega$: 字面的, 不是替身. $\psi_0(\Omega_\Omega)$ 与 $\psi_0(\Omega_\Omega+1)$ 的规格是下面两个类型. 它们不提 `S`.

```agda
LΩ : Lv
LΩ = toLv (Ω (suc zero))

ΩΩ-spec : ∀ {n} → Ordᴸ n → Set
ΩΩ-spec t = IsPsiᴸ zero (Ω LΩ) t

ΩΩ+1-spec : ∀ {n} → Ordᴸ n → Set
ΩΩ+1-spec t = IsPsiᴸ zero (Tree.suc (Ω LΩ)) t
```

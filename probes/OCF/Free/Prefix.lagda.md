# 无记号主线 (三): 符号化的树 `Ordˢ` 与 `Z`

> **`Ord₊ˢ` 多两个不带分支的构造子 `ŝ`, `ĉᴸ`; `Z` 是第 0 层的只读像.** `ĉᴸ` 的上标是历史名字, 与标签无关: 这个构造子不含 `T`.
> 脚本从 [Prefix](../Align/Prefix.lagda.md)、[UniformS](../Align/UniformS.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Prefix where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Aux
```

```agda
open Ord-Ord using (iter)
open Restr renaming (eq to eqᴿ; lt to ltᴿ)

```

## §2 新树族 (Symbolic §3 的修改版)

```agda
data Z : Set where
  zero : Z
  suc  : Z → Z
  lim  : (ℕ → Z) → Z
  ĉᴸ   : (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Z
```

```agda
module _ (ℓ : Ordᴵ) (Uˢ : (i : Ordᴵ) → i ◃ ℓ → Set) where
  data Ord₊ˢ : Set where
    zero : Ord₊ˢ
    suc  : Ord₊ˢ → Ord₊ˢ
    lim  : (f : ℕ → Ord₊ˢ) → Ord₊ˢ
    limᵢ : ∀ {i} (p : i <ᴵ ℓ) (f : Uˢ i (<→◃ p) → Ord₊ˢ) → Ord₊ˢ
    up   : ∀ {k} (r : k ◃₁ ℓ) (x : Uˢ k (◃₁→◃ r)) → Ord₊ˢ
    ŝ    : (c : Ordᴵ) → Ord₊ˢ → ((η : Ordᴵ) → c ⊑ᴵ η → Ord₊ˢ) → Ord₊ˢ
    ĉᴸ   : (c : Ordᴵ) → Z → ((η : Ordᴵ) → c ⊑ᴵ η → Z) → Ord₊ˢ → ((η : Ordᴵ) → c ⊑ᴵ η → Ord₊ˢ) → Ord₊ˢ

Uˢ : ∀ {ℓ} (i : Ordᴵ) → i ◃ ℓ → Set
Uˢ i zero         = Ord₊ˢ i Uˢ
Uˢ i (suc r)      = Uˢ i r
Uˢ _ (self {f} n) = Ord₊ˢ (f n) Uˢ
Uˢ i (lim n r)    = Uˢ i r

Ordˢ : Ordᴵ → Set
Ordˢ ℓ = Ord₊ˢ ℓ Uˢ

outˢ : ∀ {i ℓ} (r : i ◃ ℓ) → Uˢ i r → Ordˢ i
outˢ zero      x = x
outˢ (suc r)   x = outˢ r x
outˢ (self n)  x = x
outˢ (lim n r) x = outˢ r x

intoˢ : ∀ {i ℓ} (r : i ◃ ℓ) → Ordˢ i → Uˢ i r
intoˢ zero      x = x
intoˢ (suc r)   x = intoˢ r x
intoˢ (self n)  x = x
intoˢ (lim n r) x = intoˢ r x

out-intoˢ : ∀ {i ℓ} (r : i ◃ ℓ) (x : Ordˢ i) → outˢ r (intoˢ r x) ≡ x
out-intoˢ zero      x = refl
out-intoˢ (suc r)   x = out-intoˢ r x
out-intoˢ (self n)  x = refl
out-intoˢ (lim n r) x = out-intoˢ r x

coeˢ : ∀ {i ℓ₁ ℓ₂} (r : i ◃ ℓ₁) (r′ : i ◃ ℓ₂) → Uˢ i r → Uˢ i r′
coeˢ r r′ x = intoˢ r′ (outˢ r x)

toZ : Ordˢ zero → Z
toZ zero             = zero
toZ (suc x)          = suc (toZ x)
toZ (lim f)          = lim (λ n → toZ (f n))
toZ (limᵢ () f)
toZ (up () x)
toZ (ŝ c t₀ g)       = ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (toZ t₀) (λ η e → toZ (g η e))
toZ (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (toZ o₀) (λ η e → toZ (o η e))
```

```agda
record Restrˢ (j b : Ordᴵ) : Set where
  constructor restrˢ
  field
    {repˢ} : Ordᴵ
    eqˢ    : j ≅ᴵ repˢ
    ltˢ    : repˢ <ᴵ b
    backˢ  : Ordˢ repˢ → Ordˢ j
open Restrˢ

trˢ   : ∀ {a b} → a ≅ᴵ b → Ordˢ a → Ordˢ b
tr⁻ˢ  : ∀ {a b} → a ≅ᴵ b → Ordˢ b → Ordˢ a
resˢ  : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → Restrˢ j b
res⁻ˢ : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → Restrˢ j a

trˢ e zero    = zero
trˢ e (suc x) = suc (trˢ e x)
trˢ e (lim f) = lim (λ n → trˢ e (f n))
trˢ e (limᵢ q f) = limᵢ (ltˢ (resˢ q e)) (λ y → trˢ e (f (intoˢ (<→◃ q) (backˢ (resˢ q e) (outˢ (<→◃ (ltˢ (resˢ q e))) y)))))
trˢ (s≅ e) (up zero x)     = up zero (trˢ e x)
trˢ (l≅ h) (up (self n) x) = up (self n) (trˢ (h n) x)
trˢ e (ŝ c t₀ g)       = ŝ c (trˢ e t₀) (λ η d → trˢ e (g η d))
trˢ e (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (trˢ e o₀) (λ η d → trˢ e (o η d))

tr⁻ˢ e zero    = zero
tr⁻ˢ e (suc x) = suc (tr⁻ˢ e x)
tr⁻ˢ e (lim f) = lim (λ n → tr⁻ˢ e (f n))
tr⁻ˢ e (limᵢ q f) = limᵢ (ltˢ (res⁻ˢ q e)) (λ y → tr⁻ˢ e (f (intoˢ (<→◃ q) (backˢ (res⁻ˢ q e) (outˢ (<→◃ (ltˢ (res⁻ˢ q e))) y)))))
tr⁻ˢ (s≅ e) (up zero x)     = up zero (tr⁻ˢ e x)
tr⁻ˢ (l≅ h) (up (self n) x) = up (self n) (tr⁻ˢ (h n) x)
tr⁻ˢ e (ŝ c t₀ g)       = ŝ c (tr⁻ˢ e t₀) (λ η d → tr⁻ˢ e (g η d))
tr⁻ˢ e (ĉᴸ c t₀ g o₀ o) = ĉᴸ c t₀ g (tr⁻ˢ e o₀) (λ η d → tr⁻ˢ e (o η d))

resˢ zero      (s≅ e) = restrˢ e zero (tr⁻ˢ e)
resˢ (suc q)   (s≅ e) = restrˢ (eqˢ (resˢ q e)) (suc (ltˢ (resˢ q e))) (backˢ (resˢ q e))
resˢ (lim n q) (l≅ h) = restrˢ (eqˢ (resˢ q (h n))) (lim n (ltˢ (resˢ q (h n)))) (backˢ (resˢ q (h n)))

res⁻ˢ zero      (s≅ e) = restrˢ (≅ᴵ-sym e) zero (trˢ e)
res⁻ˢ (suc q)   (s≅ e) = restrˢ (eqˢ (res⁻ˢ q e)) (suc (ltˢ (res⁻ˢ q e))) (backˢ (res⁻ˢ q e))
res⁻ˢ (lim n q) (l≅ h) = restrˢ (eqˢ (res⁻ˢ q (h n))) (lim n (ltˢ (res⁻ˢ q (h n)))) (backˢ (res⁻ˢ q (h n)))
```

```agda
Ωˢ : (ℓ : Ordᴵ) → Ordˢ ℓ
Ωˢ zero      = suc zero
Ωˢ (suc ℓ)   = limᵢ zero (up zero)
Ωˢ (lim f s) = lim (λ n → up (self n) (Ωˢ (f n)))

addˢ : ∀ {k ℓ} → Ordˢ ℓ → Simᴵ k ℓ → Ordˢ k → Ordˢ ℓ
addˢ a σ zero              = a
addˢ a σ (suc b)           = suc (addˢ a σ b)
addˢ a σ (lim f)           = lim (λ n → addˢ a σ (f n))
addˢ a σ (limᵢ q f)        = limᵢ (σ q) (λ y → addˢ a σ (f (coeˢ (<→◃ (σ q)) (<→◃ q) y)))
addˢ a σ (up zero x)       = addˢ a (λ q → σ (suc q)) x
addˢ a σ (up (self n) x)   = addˢ a (λ q → σ (lim n q)) x
addˢ {k = zero}    a σ (ŝ c t₀ g) = ĉᴸ c (toZ t₀) (λ η e → toZ (g η e)) (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
addˢ {k = suc _}   a σ (ŝ c t₀ g) = ŝ c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
addˢ {k = lim _ _} a σ (ŝ c t₀ g) = ŝ c (addˢ a σ t₀) (λ η e → addˢ a σ (g η e))
addˢ a σ (ĉᴸ c t₀ g o₀ o)  = ĉᴸ c t₀ g (addˢ a σ o₀) (λ η e → addˢ a σ (o η e))

infixl 6 _+ˢ_
_+ˢ_ : ∀ {ℓ} → Ordˢ ℓ → Ordˢ ℓ → Ordˢ ℓ
a +ˢ b = addˢ a (λ q → q) b
```

## §1 `Z` 上的互模拟, 计值与证书无关

```agda
infix 4 _≅ᶻ_
data _≅ᶻ_ : Z → Z → Set where
  zᶻ : Z.zero ≅ᶻ Z.zero
  sᶻ : ∀ {x y} → x ≅ᶻ y → Z.suc x ≅ᶻ Z.suc y
  lᶻ : ∀ {f g : ℕ → Z} → (∀ n → f n ≅ᶻ g n) → Z.lim f ≅ᶻ Z.lim g
  ĉᶻ : ∀ {c c′ t₀ t₀′ o₀ o₀′} {g o : (η : Ordᴵ) → c ⊑ᴵ η → Z} {g′ o′ : (η : Ordᴵ) → c′ ⊑ᴵ η → Z} →
       c ≅ᴵ c′ → t₀ ≅ᶻ t₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → g η e ≅ᶻ g′ η′ e′) →
       o₀ ≅ᶻ o₀′ → (∀ η e η′ e′ → η ≅ᴵ η′ → o η e ≅ᶻ o′ η′ e′) → ĉᴸ c t₀ g o₀ o ≅ᶻ ĉᴸ c′ t₀′ g′ o₀′ o′

≅ᶻ-sym : ∀ {x y} → x ≅ᶻ y → y ≅ᶻ x
≅ᶻ-sym zᶻ     = zᶻ
≅ᶻ-sym (sᶻ d) = sᶻ (≅ᶻ-sym d)
≅ᶻ-sym (lᶻ h) = lᶻ (λ n → ≅ᶻ-sym (h n))
≅ᶻ-sym (ĉᶻ ec dt dg dp dO) =
  ĉᶻ (≅ᴵ-sym ec) (≅ᶻ-sym dt) (λ η e η′ e′ eη → ≅ᶻ-sym (dg η′ e′ η e (≅ᴵ-sym eη)))
     (≅ᶻ-sym dp) (λ η e η′ e′ eη → ≅ᶻ-sym (dO η′ e′ η e (≅ᴵ-sym eη)))

≅ᶻ-trans : ∀ {x y w} → x ≅ᶻ y → y ≅ᶻ w → x ≅ᶻ w
≅ᶻ-trans zᶻ     zᶻ      = zᶻ
≅ᶻ-trans (sᶻ d) (sᶻ d′) = sᶻ (≅ᶻ-trans d d′)
≅ᶻ-trans (lᶻ h) (lᶻ h′) = lᶻ (λ n → ≅ᶻ-trans (h n) (h′ n))
≅ᶻ-trans (ĉᶻ ec dt dg dp dO) (ĉᶻ ec′ dt′ dg′ dp′ dO′) =
  ĉᶻ (≅ᴵ-trans ec ec′) (≅ᶻ-trans dt dt′)
     (λ η e η″ e″ eη → ≅ᶻ-trans (dg η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (dg′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
     (≅ᶻ-trans dp dp′)
     (λ η e η″ e″ eη → ≅ᶻ-trans (dO η e η (⊑ᴵ-≅ˡ ec e) (≅ᴵ-refl η)) (dO′ η (⊑ᴵ-≅ˡ ec e) η″ e″ eη))
```

## §7 链的起点、`zero-l` 与 $\Omega$ 的单调性

```agda
𝟎ˢ : ∀ {ℓ} → Ordˢ ℓ
𝟎ˢ = Ord₊ˢ.zero
```

## §12 结论与边界

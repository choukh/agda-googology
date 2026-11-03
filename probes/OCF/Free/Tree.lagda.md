# 无记号主线 (七): 数据树 `O`, `ψ̄`, `ψᵒ`, `_⊕_`, `Ω̇`, `TΩ·2`

> **最终定义的主体.** `O α φ`: 数据树, 层号 $\alpha$ 进入下标, 地板 $\varphi$ 记录依赖. `ψ̄`: 对它递归的计值, 把它读成 `Run φ`. `TΩ·2`: $\psi_0(\Omega_{\Omega\cdot2})$ 的树.
> 脚本从 [Uniform4Base](../Align/Uniform4Base.lagda.md)、[Uniform4Two](../Align/Uniform4Two.lagda.md) 切出 (定义级切片), 代码行逐字, 讲解见原文件. 本文件的导入闭包不含记号或标签模块 (`probes/Survey/scripts/importclosure.py`).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示. 不引用记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Free.Tree where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ; _+ˢ_)
open import OCF.Free.Floor using (Flr; fz; fk; fb; _⊔_; Ev; Run; A; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun)
```

```agda
open Ord-Ord using (iter)
```

## §1 数据树

```agda
Fl : Flr
Fl = fz ⊔ fk zero
```

## §2 加法、嵌入、尾巴

```agda
asl : ∀ {a b d ℓ} → Ev ℓ (a ⊔ (b ⊔ d)) → Ev ℓ ((a ⊔ b) ⊔ d)
asl (u , (v , w)) = (u , v) , w

asr : ∀ {a b d ℓ} → Ev ℓ ((a ⊔ b) ⊔ d) → Ev ℓ (a ⊔ (b ⊔ d))
asr ((u , v) , w) = u , (v , w)

swp : ∀ {a b d ℓ} → Ev ℓ (a ⊔ (b ⊔ d)) → Ev ℓ (b ⊔ (a ⊔ d))
swp (u , (v , w)) = v , (u , w)

dupr2 : ∀ {a b ℓ} → Ev ℓ (a ⊔ b) → Ev ℓ (a ⊔ ((a ⊔ b) ⊔ b))
dupr2 (u , v) = u , ((u , v) , v)

infixl 6 _⊕_
```

## §1 数据树

```agda
module _ (α : Ordᴵ) (U : (i : Ordᴵ) → i ◃ α → Flr → Set) where
  data O₊ : Flr → Set where
    o0   : ∀ {φ} → O₊ φ
    os   : ∀ {φ} → O₊ φ → O₊ φ
    ol   : ∀ {φ} → (ℕ → O₊ φ) → O₊ φ
    oi   : ∀ {φ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → O₊ φ) → O₊ φ
    oŝ   : ∀ {φ} (c₀ : Ordᴵ) → O₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ φ) → O₊ φ
    oĉ   : ∀ {φ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → O₊ φ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → O₊ φ) → O₊ φ
    oclo : ∀ {φ} → O₊ (φ ⊔ fk zero) → ((η : Ordᴵ) → O₊ (φ ⊔ fk η)) → O₊ (φ ⊔ fk zero)
    owk  : ∀ {φ ψ} → (∀ {ℓ} → Ev ℓ ψ → Ev ℓ φ) → O₊ φ → O₊ ψ
    oΩ   : ∀ {φ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ → U k (<→◃ q) ξ → O₊ (ξ ⊔ φ)) → O₊ φ

O  : Ordᴵ → Flr → Set
Us : ∀ {α} (i : Ordᴵ) → i ◃ α → Flr → Set
O α φ = O₊ α Us φ
Us i zero         φ = O i φ
Us i (suc r)      φ = Us i r φ
Us _ (self {f} n) φ = O (f n) φ
Us i (lim n r)    φ = Us i r φ

outU : ∀ {i α} (r : i ◃ α) {φ} → Us i r φ → O i φ
outU zero      x = x
outU (suc r)   x = outU r x
outU (self n)  x = x
outU (lim n r) x = outU r x

intoU : ∀ {i α} (r : i ◃ α) {φ} → O i φ → Us i r φ
intoU zero      x = x
intoU (suc r)   x = intoU r x
intoU (self n)  x = x
intoU (lim n r) x = intoU r x

<◃ : ∀ {k a b} → k <ᴵ a → a ◃ b → k <ᴵ b
<◃ q zero      = suc q
<◃ q (suc r)   = suc (<◃ q r)
<◃ q (self n)  = lim n q
<◃ q (lim n r) = lim n (<◃ q r)
```

## §2 加法、嵌入、层号搬运

```agda

_⊕_ : ∀ {c φ ψ} → O c φ → O c ψ → O c (φ ⊔ ψ)
W ⊕ o0       = owk proj₁ W
W ⊕ os a     = os (W ⊕ a)
W ⊕ ol F     = ol (λ n → W ⊕ F n)
W ⊕ oi ac f  = oi (λ e → ac (proj₂ e)) (λ x → W ⊕ f x)
W ⊕ oŝ c₀ t g = oŝ c₀ (W ⊕ t) (λ η e → W ⊕ g η e)
W ⊕ oĉ c₀ z zg o₀ o = oĉ c₀ z zg (W ⊕ o₀) (λ η e → W ⊕ o η e)
W ⊕ oclo t g = owk asl (oclo (owk asr (W ⊕ t)) (λ η → owk asr (W ⊕ g η)))
W ⊕ owk le t = owk (λ e → proj₁ e , le (proj₂ e)) (W ⊕ t)
W ⊕ oΩ fe q h = oΩ (λ e → fe (proj₂ e)) q (λ ξ z → owk swp (W ⊕ h ξ z))

ι : ∀ {a b} (r : a ◃ b) {φ} → O a φ → O b φ
ι r o0 = o0
ι r (os a) = os (ι r a)
ι r (ol F) = ol (λ n → ι r (F n))
ι r (oi ac f) = oi ac (λ x → ι r (f x))
ι r (oŝ c₀ t g) = oŝ c₀ (ι r t) (λ η e → ι r (g η e))
ι r (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ι r o₀) (λ η e → ι r (o η e))
ι r (oclo t g) = oclo (ι r t) (λ η → ι r (g η))
ι r (owk le t) = owk le (ι r t)
ι r (oΩ fe q h) = oΩ fe (<◃ q r) (λ ξ z → ι r (h ξ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z))))

record RestrO (j b : Ordᴵ) : Set where
  constructor restrO
  field
    {repO} : Ordᴵ
    eqO    : j ≅ᴵ repO
    ltO    : repO <ᴵ b
    backO  : ∀ {ξ} → O repO ξ → O j ξ
open RestrO

trO  : ∀ {a b φ} → a ≅ᴵ b → O a φ → O b φ
tr⁻O : ∀ {a b φ} → a ≅ᴵ b → O b φ → O a φ
resO : ∀ {j a b} → j <ᴵ a → a ≅ᴵ b → RestrO j b
res⁻O : ∀ {j a b} → j <ᴵ b → a ≅ᴵ b → RestrO j a

trO e o0 = o0
trO e (os a) = os (trO e a)
trO e (ol F) = ol (λ n → trO e (F n))
trO e (oi ac f) = oi ac (λ x → trO e (f x))
trO e (oŝ c₀ t g) = oŝ c₀ (trO e t) (λ η d → trO e (g η d))
trO e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (trO e o₀) (λ η d → trO e (o η d))
trO e (oclo t g) = oclo (trO e t) (λ η → trO e (g η))
trO e (owk le t) = owk le (trO e t)
trO e (oΩ fe q h) = oΩ fe (ltO (resO q e)) (λ ξ z → trO e (h ξ (intoU (<→◃ q) (backO (resO q e) (outU (<→◃ (ltO (resO q e))) z)))))

tr⁻O e o0 = o0
tr⁻O e (os a) = os (tr⁻O e a)
tr⁻O e (ol F) = ol (λ n → tr⁻O e (F n))
tr⁻O e (oi ac f) = oi ac (λ x → tr⁻O e (f x))
tr⁻O e (oŝ c₀ t g) = oŝ c₀ (tr⁻O e t) (λ η d → tr⁻O e (g η d))
tr⁻O e (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (tr⁻O e o₀) (λ η d → tr⁻O e (o η d))
tr⁻O e (oclo t g) = oclo (tr⁻O e t) (λ η → tr⁻O e (g η))
tr⁻O e (owk le t) = owk le (tr⁻O e t)
tr⁻O e (oΩ fe q h) = oΩ fe (ltO (res⁻O q e)) (λ ξ z → tr⁻O e (h ξ (intoU (<→◃ q) (backO (res⁻O q e) (outU (<→◃ (ltO (res⁻O q e))) z)))))

resO zero      (s≅ e) = restrO e zero (tr⁻O e)
resO (suc q)   (s≅ e) = restrO (eqO (resO q e)) (suc (ltO (resO q e))) (backO (resO q e))
resO (lim n q) (l≅ h) = restrO (eqO (resO q (h n))) (lim n (ltO (resO q (h n)))) (backO (resO q (h n)))

res⁻O zero      (s≅ e) = restrO (≅ᴵ-sym e) zero (trO e)
res⁻O (suc q)   (s≅ e) = restrO (eqO (res⁻O q e)) (suc (ltO (res⁻O q e))) (backO (res⁻O q e))
res⁻O (lim n q) (l≅ h) = restrO (eqO (res⁻O q (h n))) (lim n (ltO (res⁻O q (h n)))) (backO (res⁻O q (h n)))

tl : ∀ {c k} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → Ordˢ k → O c φ
tl φ cv Ord₊ˢ.zero = o0
tl φ cv (Ord₊ˢ.suc a) = os (tl φ cv a)
tl φ cv (Ord₊ˢ.lim f) = ol (λ n → tl φ cv (f n))
tl φ cv (Ord₊ˢ.limᵢ q f) = oi (λ e → cv e q) (λ x → tl φ cv (f (intoˢ (<→◃ q) x)))
tl {k = suc k′} φ cv (Ord₊ˢ.up zero x) = owk (λ v → toFlo k′ (λ q → cv v (suc q))) (tl (flo k′) (cvFlo k′) x)
tl {k = lim f s} φ cv (Ord₊ˢ.up (self n) x) = owk (λ v → toFlo (f n) (λ q → cv v (lim n q))) (tl (flo (f n)) (cvFlo (f n)) x)
tl {k = zero} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oĉ c₀ (toZ t₀) (λ η e → toZ (g η e)) (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = suc _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = lim _ _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = oŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl φ cv (Ord₊ˢ.ĉᴸ c₀ t₀ g o₀ o) = oĉ c₀ t₀ g (tl φ cv o₀) (λ η e → tl φ cv (o η e))

Ω̇ : ∀ α → O α Fl
Ω̇ zero = oclo (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) (λ η → tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))
Ω̇ (suc α) = oΩ (λ e → e) zero (λ ξ z → owk proj₁ (ι zero z))
Ω̇ (lim f s) = ol (λ n → ι (self n) (Ω̇ (f n)))
```

## §3 折叠

```agda
repᵒ : ∀ {c φ} → O c φ → ℕ → O c φ
repᵒ x zero          = o0
repᵒ x (suc zero)    = x
repᵒ x (suc (suc m)) = owk (λ e → e , e) (repᵒ x (suc m) ⊕ x)

chainᵒ : ∀ {k φ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (O k φ → O k φ) → ℕ → O k φ
chainᵒ {k} fe f zero    = owk fe (Ω̇ k)
chainᵒ fe f (suc n) = f (chainᵒ fe f n)

ψᵒ : ∀ {α t} → t <ᴵ α → ∀ {φ} → O α φ → O t (Fl ⊔ φ)
ψᵒ {t = t} q o0 = owk proj₁ (Ω̇ t)
ψᵒ q (os a) = ol (repᵒ (ψᵒ q a))
ψᵒ q (ol F) = ol (λ n → ψᵒ q (F n))
ψᵒ q (oi ac f) = oi (λ e → ac (proj₂ e)) (λ x → ψᵒ q (f x))
ψᵒ q (oŝ c₀ t g) = oŝ c₀ (ψᵒ q t) (λ η e → ψᵒ q (g η e))
ψᵒ q (oĉ c₀ z zg o₀ o) = oĉ c₀ z zg (ψᵒ q o₀) (λ η e → ψᵒ q (o η e))
ψᵒ q (oclo t g) = owk asl (oclo (owk asr (ψᵒ q t)) (λ η → owk asr (ψᵒ q (g η))))
ψᵒ q (owk le x) = owk (λ e → proj₁ e , le (proj₂ e)) (ψᵒ q x)
ψᵒ q {φ} (oΩ fe r h) with <ᴵ-dec r q
... | injᵃ (via e s) =
  oΩ proj₁ s (λ ξ y → owk swp (ψᵒ q (h ξ (intoU (<→◃ r) (tr⁻O e (outU (<→◃ s) y))))))
... | injᵇ _ =
  ol (λ n → owk dupr2 (ψᵒ q (h (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n)))))
... | injᶜ _ =
  ol (λ n → owk dupr2 (ψᵒ q (h (Fl ⊔ φ) (intoU (<→◃ r) (chainᵒ proj₁ (λ z → owk dupr2 (ψᵒ r (h (Fl ⊔ φ) (intoU (<→◃ r) z)))) n)))))

ψ̄ : ∀ {c φ} → O c φ → Run φ
ψ̄ o0 = wk 0 (λ e → tt) ∅ᴿ
ψ̄ (os a) = sucRun (ψ̄ a)
ψ̄ (ol F) = limA 0 (λ n → ψ̄ (F n))
ψ̄ (oi ac f) = limᵢA 0 ac (λ x → ψ̄ (f x))
ψ̄ (oŝ c₀ t g) = ŝA 0 c₀ (ψ̄ t) (λ η e → ψ̄ (g η e))
ψ̄ (oĉ c₀ z zg o₀ o) = ĉA 0 c₀ z zg (ψ̄ o₀) (λ η e → ψ̄ (o η e))
ψ̄ (oclo t g) = cloA 0 (ψ̄ t) (λ η → ψ̄ (g η))
ψ̄ (owk le x) = wk 0 le (ψ̄ x)
ψ̄ {φ = φ} (oΩ fe r h) =
  limA 0 (λ n → wk 0 (λ v → v , v)
                (ψ̄ (h φ (intoU (<→◃ r) (chainᵒ fe (λ z → owk (λ v → fe v , (v , v)) (ψᵒ r (h φ (intoU (<→◃ r) z)))) n)))))

-- ψ₀(Ω_{Ω·2}): 闭包, 分支 η 处 ψ₀(Ω_{Ω+η})
TΩ·2 : Run (Fl ⊔ fk zero)
TΩ·2 = cloA 0 {Fl} (wk 0 proj₁ (ψ̄ (Ω̇ (suc zero)))) (λ η → wk 0 proj₁ (ψ̄ (Ω̇ η)))
```

## §4 评估 (纸面)

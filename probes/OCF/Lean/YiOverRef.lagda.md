# YiOver 参照一侧：第 1 层参照树的逐点前序

**验收文件，档位：编译定理 (引理)。** 只谈参照框架 (`Level`) 第 1 层的树 `T₁`。`_≤ₚ_`：结点逐点比较 (只比分支下标 ≥ 1 的分支)，另可落到第 1 支 (`i1`)；嵌入的第 0 层树按值比较 (`fu`)。
`mono⁰`：`a ≤ₚ b → ψ⁰ a ≼ ψ⁰ b`；`trans`：传递。不否定什么：`≤ₚ` 不含 "结点在一切分支之上即在其上" 的规则，那一条使 ψ⁰ 不单调 (`RR4MonoFragment`)。用法在 [YiOverMain](YiOverMain.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOverRef where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans; ≼-suc;
  iter-≼; ψ⁰-mono⁰; ψ⁰-suc-≼; 1≼ψ⁰)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)

T₀ T₁ : Set
T₀ = L.Ordᶜ L.zero
T₁ = L.Ordᶜ (L.suc L.zero)

𝟙 : T₀
𝟙 = L.suc L.zero
```

## 1 定义

`ψ₀` 是结点链里用的目标层 0 的折叠；`δ f` 是结点 `limᵢ zero f` 的 ψ⁰ 读的链。

```agda
ψ₀ : T₁ → T₀
ψ₀ = L.ψ {i = L.zero} {k = L.suc L.zero} {ℓ = L.suc L.zero} L.zero (λ r → r)

δ : (T₀ → T₁) → ℕ → T₀
δ f = iterᴸ (λ x → ψ₀ (f x)) 𝟙

data Flat : T₁ → Set where
  fz : Flat L.zero
  fs : ∀ {a} → Flat a → Flat (L.suc a)
  fl : ∀ {f : ℕ → T₁} → (∀ n → Flat (f n)) → Flat (L.lim f)
  fu : ∀ {y : T₀} → Flat (L.up L.zero y)

infix 4 _≤ₚ_
data _≤ₚ_ : T₁ → T₁ → Set where
  zz : L.zero ≤ₚ L.zero
  ss : ∀ {a b} → a ≤ₚ b → L.suc a ≤ₚ L.suc b
  ws : ∀ {a b} → a ≤ₚ b → a ≤ₚ L.suc b
  ≤l : ∀ {a} {f : ℕ → T₁} n → a ≤ₚ f n → a ≤ₚ L.lim f
  l≤ : ∀ {f : ℕ → T₁} {b} → (∀ n → f n ≤ₚ b) → L.lim f ≤ₚ b
  ii : ∀ {f g : T₀ → T₁} → (∀ (x y : T₀) → 𝟙 ≼ x → x ≼ y → f x ≤ₚ g y) →
       L.limᵢ L.zero f ≤ₚ L.limᵢ L.zero g
  i1 : ∀ {a} {g : T₀ → T₁} → a ≤ₚ g 𝟙 → a ≤ₚ L.limᵢ L.zero g
  fu : ∀ {a} {y : T₀} → Flat a → a ≼ y → a ≤ₚ L.up L.zero y
```

## 2 传递

```agda
flatᵖ : ∀ {a b} → a ≤ₚ b → Flat b → Flat a × (a ≼ b)
flatᵖ zz fz = fz , z≼
flatᵖ (ss p) (fs fb) = fs (proj₁ (flatᵖ p fb)) , s≼s (proj₂ (flatᵖ p fb))
flatᵖ (ws p) (fs fb) = proj₁ (flatᵖ p fb) , ≼-suc (proj₂ (flatᵖ p fb))
flatᵖ (≤l n p) (fl fb) = proj₁ (flatᵖ p (fb n)) , ≼l n (proj₂ (flatᵖ p (fb n)))
flatᵖ (l≤ h) fb = fl (λ n → proj₁ (flatᵖ (h n) fb)) , l≼ (λ n → proj₂ (flatᵖ (h n) fb))
flatᵖ (fu fa q) fu = fa , ≼u q

trans : ∀ {a b c} → a ≤ₚ b → b ≤ₚ c → a ≤ₚ c
trans p (ws q) = ws (trans p q)
trans p (≤l n q) = ≤l n (trans p q)
trans p (i1 q) = i1 (trans p q)
trans p (fu fb q) = fu (proj₁ (flatᵖ p fb)) (≼-trans (proj₂ (flatᵖ p fb)) q)
trans (l≤ h) q = l≤ (λ n → trans (h n) q)
trans zz zz = zz
trans (ss p) (ss q) = ss (trans p q)
trans (ws p) (ss q) = ws (trans p q)
trans (≤l n p) (l≤ h) = trans p (h n)
trans (ii h₁) (ii h₂) = ii (λ x z o xz → trans (h₁ x x o (≼-refl x)) (h₂ x z o xz))
trans (i1 p) (ii h₂) = i1 (trans p (h₂ 𝟙 𝟙 (≼-refl 𝟙) (≼-refl 𝟙)))
```

## 3 ψ⁰ 对 `≤ₚ` 单调

`ψ₀` 与 ψ⁰ 逐构造子同形 (结点处读同一条链)，两向的值序 (`ψ₀≼`, `≼ψ₀`)。结点：两条链逐项相关 (`ch`)，链从 1 起，所以只用到下标 ≥ 1 的分支。

```agda
ψσ≈ : ∀ (σ : L.Simᴵ L.zero (L.suc L.zero)) (y : T₀) →
  (L.ψ {i = L.zero} {k = L.zero} {ℓ = L.suc L.zero} L.zero σ y ≼ L.ψ⁰ y) ×
  (L.ψ⁰ y ≼ L.ψ {i = L.zero} {k = L.zero} {ℓ = L.suc L.zero} L.zero σ y)
ψσ≈ σ L.zero = ≼-refl _ , ≼-refl _
ψσ≈ σ (L.suc y) = l≼ (λ n → ≼l n (iter-≼ (proj₁ (ψσ≈ σ y)) n)) , l≼ (λ n → ≼l n (iter-≼ (proj₂ (ψσ≈ σ y)) n))
ψσ≈ σ (L.lim f) = l≼ (λ n → ≼l n (proj₁ (ψσ≈ σ (f n)))) , l≼ (λ n → ≼l n (proj₂ (ψσ≈ σ (f n))))
ψσ≈ σ (L.limᵢ () f)
ψσ≈ σ (L.up () x)

ψ₀≈ : ∀ (x : T₁) → (ψ₀ x ≼ L.ψ⁰ x) × (L.ψ⁰ x ≼ ψ₀ x)
ψ₀≈ L.zero = ≼-refl _ , ≼-refl _
ψ₀≈ (L.suc a) = l≼ (λ n → ≼l n (iter-≼ (proj₁ (ψ₀≈ a)) n)) , l≼ (λ n → ≼l n (iter-≼ (proj₂ (ψ₀≈ a)) n))
ψ₀≈ (L.lim f) = l≼ (λ n → ≼l n (proj₁ (ψ₀≈ (f n)))) , l≼ (λ n → ≼l n (proj₂ (ψ₀≈ (f n))))
ψ₀≈ (L.limᵢ L.zero f) =
  l≼ (λ n → ≼l n (proj₁ (ψ₀≈ (f (δ f n))))) , l≼ (λ n → ≼l n (proj₂ (ψ₀≈ (f (δ f n)))))
ψ₀≈ (L.limᵢ (L.suc ()) f)
ψ₀≈ (L.up L.zero y) = ψσ≈ (λ q → L.suc q) y

ψ₀≼ : ∀ x → ψ₀ x ≼ L.ψ⁰ x
ψ₀≼ x = proj₁ (ψ₀≈ x)

≼ψ₀ : ∀ x → L.ψ⁰ x ≼ ψ₀ x
≼ψ₀ x = proj₂ (ψ₀≈ x)

one : ∀ (f : T₀ → T₁) n → 𝟙 ≼ δ f n
one f zero = ≼-refl 𝟙
one f (suc n) = ≼-trans (1≼ψ⁰ (f (δ f n))) (≼ψ₀ (f (δ f n)))

flat⁰ : ∀ {a : T₁} {y : T₀} → Flat a → a ≼ y → L.ψ⁰ a ≼ L.ψ⁰ y
flat⁰ fa z≼ = 1≼ψ⁰ _
flat⁰ (fs fa) (s≼s p) = ψ⁰-suc-≼ (flat⁰ fa p)
flat⁰ fa (≼l n p) = ≼l n (flat⁰ fa p)
flat⁰ (fl fa) (l≼ h) = l≼ (λ n → flat⁰ (fa n) (h n))
flat⁰ fa (≼i {p = ()} x ex p)
flat⁰ () (i≼ h)
flat⁰ fa (≼u {r = ()} p)
flat⁰ fu (u≼ p) = ψ⁰-mono⁰ p

mono⁰ : ∀ {a b} → a ≤ₚ b → L.ψ⁰ a ≼ L.ψ⁰ b
mono⁰ zz = ≼-refl _
mono⁰ (ss p) = ψ⁰-suc-≼ (mono⁰ p)
mono⁰ (ws p) = ≼l 1 (mono⁰ p)
mono⁰ (≤l n p) = ≼l n (mono⁰ p)
mono⁰ (l≤ h) = l≼ (λ n → mono⁰ (h n))
mono⁰ {L.limᵢ L.zero f} {L.limᵢ L.zero g} (ii h) = l≼ (λ n → ≼l n (mono⁰ (h (δ f n) (δ g n) (one f n) (ch n))))
  where
  ch : ∀ n → δ f n ≼ δ g n
  ch zero = ≼-refl 𝟙
  ch (suc n) = ≼-trans (ψ₀≼ (f (δ f n)))
    (≼-trans (mono⁰ (h (δ f n) (δ g n) (one f n) (ch n))) (≼ψ₀ (g (δ g n))))
mono⁰ (i1 p) = ≼l 0 (mono⁰ p)
mono⁰ (fu fa q) = flat⁰ fa q

mono₀ : ∀ {a b} → a ≤ₚ b → ψ₀ a ≼ ψ₀ b
mono₀ {a} {b} p = ≼-trans (ψ₀≼ a) (≼-trans (mono⁰ p) (≼ψ₀ b))
```

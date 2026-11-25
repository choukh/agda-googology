# YiChain 底座：`≼ˣ` 的传递与吸收

**验收文件，档位：编译定理 (引理)。** 只谈参照框架第 0 层的树。`transˣ`：定义域 `≼ˣ` 传递。`ABS`/`VABS`：若 `c` 是 `b` 的结构前驱、`X` 与 ψ⁰ c 值相等且 `ψ⁰ c ≼ˣ X`，则 `ψ⁰ b ≼ˣ X + ψ⁰ b` 与 `X + ψ⁰ b ≼ ψ⁰ b`。
吸收要的判定 (左加数被吸收, 还是与主项相等) 由结构前驱的推导 (`≺z`/`≺s`/`≺l`) 给出，不用值上的三歧。不否定 `YiVmConLPO`：那里否定的是对一切值序推导的完备性。用法在 [YiChainOne](YiChainOne.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiChainBase where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_; _≤′_; ≤′-refl; ≤′-step)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Product.Base using (_×_; _,_)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼; ≼-suc; ≺→s≼; ⊑→≼; +-mono; ψ⁰-mono⁰)
open import OCF.Align.YiVmConExact using (_≼ˣ_; zˣ; sˣ; wˣ; ≼lˣ; lˣ; reflˣ; ≅→≼ˣ; ⊑→≼ˣ)
open import OCF.Lean.YiZeroAccP using (ψ⁰ˣ; +ˣ)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)

T₀ : Set
T₀ = L.Ordᶜ L.zero
```

## 1 传递与结构的小引理

```agda
transˣ : ∀ {a b c : T₀} → a ≼ˣ b → b ≼ˣ c → a ≼ˣ c
transˣ zˣ e = zˣ
transˣ (lˣ h) e = lˣ (λ n → transˣ (h n) e)
transˣ (sˣ d u) (sˣ e v) = sˣ (transˣ d e) (≼-trans v u)
transˣ (wˣ d) (sˣ e v) = wˣ (transˣ d e)
transˣ d@(sˣ _ _) (wˣ e) = wˣ (transˣ d e)
transˣ d@(wˣ _) (wˣ e) = wˣ (transˣ d e)
transˣ d@(≼lˣ _ _) (wˣ e) = wˣ (transˣ d e)
transˣ d@(sˣ _ _) (≼lˣ n e) = ≼lˣ n (transˣ d e)
transˣ d@(wˣ _) (≼lˣ n e) = ≼lˣ n (transˣ d e)
transˣ d@(≼lˣ _ _) (≼lˣ n e) = ≼lˣ n (transˣ d e)
transˣ (≼lˣ n d) (lˣ h) = transˣ d (h n)

assoc⁰ : ∀ (X Y t : T₀) → ((X L.+ Y) L.+ t) L.≅ (X L.+ (Y L.+ t))
assoc⁰ X Y L.zero = L.≅-refl⁰ (X L.+ Y)
assoc⁰ X Y (L.suc t) = L.s≅ (assoc⁰ X Y t)
assoc⁰ X Y (L.lim f) = L.l≅ (λ n → assoc⁰ X Y (f n))
assoc⁰ X Y (L.limᵢ () f)
assoc⁰ X Y (L.up () x)

⊑+ : ∀ (X t : T₀) → X L.⊑ (X L.+ t)
⊑+ X L.zero h = h
⊑+ X (L.suc t) h = L.≺s (⊑+ X t h)
⊑+ X (L.lim f) h = L.≺l 0 (⊑+ X (f 0) h)
⊑+ X (L.limᵢ () f) h
⊑+ X (L.up () x) h

up⊑ : ∀ {g : ℕ → T₀} → (∀ n → g n L.⊑ g (suc n)) → ∀ {n p} → n ≤′ p → g n L.⊑ g p
up⊑ st ≤′-refl h = h
up⊑ st (≤′-step q) h = st _ (up⊑ st q h)

≺→≼ : ∀ {c b : T₀} → c L.≺ b → c ≼ b
≺→≼ {c} d = ≼-trans (≼-suc (≼-refl c)) (≺→s≼ d)
```

## 2 吸收

`b = suc b′`：`c ≅ b′` 时左加数与主项 ψ⁰ b′ 值相等，各项错开一位 (`+ˣ`)；`c ≺ b′` 时左加数被 ψ⁰ b′ 吸收，递归后按结合律对齐。`b = lim g`：`c ≺ g m`，第 n 项搬到 `g (n ⊔ m)` (由 `HS` 的步进)。

```agda
module Abs {X c : T₀} (hx : L.ψ⁰ c ≼ˣ X) (hv : X ≼ L.ψ⁰ c) where

  VABS : ∀ (b : T₀) → L.HS b → c L.≺ b → (X L.+ L.ψ⁰ b) ≼ L.ψ⁰ b
  VABS (L.suc b) h (L.≺z e) = l≼ (λ n → ≼l (suc n) (+-mono (≼-trans hv (≅→≼ (L.ψ⁰-≅ e))) (≼-refl (iterᴸ (L.ψ⁰ b L.+_) L.zero n))))
  VABS (L.suc b) h (L.≺s d) = l≼ λ where
    zero → ≼l 1 (≼-trans hv (ψ⁰-mono⁰ (≺→≼ d)))
    (suc n) → ≼l (suc n) (≼-trans (≅→≼ (L.≅-sym (assoc⁰ X (L.ψ⁰ b) (iterᴸ (L.ψ⁰ b L.+_) L.zero n))))
      (+-mono (VABS b (L.hs⁻ h) d) (≼-refl (iterᴸ (L.ψ⁰ b L.+_) L.zero n))))
  VABS (L.lim g) h (L.≺l m d) = l≼ (λ n → ≼l (n ⊔ m)
    (≼-trans (+-mono (≼-refl X) (ψ⁰-mono⁰ (⊑→≼ (g n) (up⊑ (L.hl₂ h) (≤⇒≤′ (m≤m⊔n n m))))))
      (VABS (g (n ⊔ m)) (L.hl₁ h (n ⊔ m)) (up⊑ (L.hl₂ h) (≤⇒≤′ (m≤n⊔m n m)) d))))
  VABS (L.limᵢ () f) h d
  VABS (L.up () x) h d

  ABS : ∀ (b : T₀) → L.HS b → c L.≺ b → L.ψ⁰ b ≼ˣ (X L.+ L.ψ⁰ b)
  ABS (L.suc b) h (L.≺z e) = lˣ λ where
    zero → zˣ
    (suc n) → ≼lˣ n (+ˣ (transˣ (≅→≼ˣ (L.ψ⁰-≅ (L.≅-sym e))) hx) (≼-trans hv (≅→≼ (L.ψ⁰-≅ e)))
      (reflˣ (iterᴸ (L.ψ⁰ b L.+_) L.zero n)))
  ABS (L.suc b) h (L.≺s d) = lˣ λ where
    zero → zˣ
    (suc n) → ≼lˣ (suc n) (transˣ (+ˣ (ABS b (L.hs⁻ h) d) (VABS b (L.hs⁻ h) d) (reflˣ (iterᴸ (L.ψ⁰ b L.+_) L.zero n)))
      (≅→≼ˣ (assoc⁰ X (L.ψ⁰ b) (iterᴸ (L.ψ⁰ b L.+_) L.zero n))))
  ABS (L.lim g) h (L.≺l m d) = lˣ (λ n → ≼lˣ (n ⊔ m)
    (transˣ (ψ⁰ˣ (⊑→≼ˣ (g n) (up⊑ (L.hl₂ h) (≤⇒≤′ (m≤m⊔n n m)))))
      (ABS (g (n ⊔ m)) (L.hl₁ h (n ⊔ m)) (up⊑ (L.hl₂ h) (≤⇒≤′ (m≤n⊔m n m)) d))))
  ABS (L.limᵢ () f) h d
  ABS (L.up () x) h d
```

`step`：链的一步。`X` 有结构前驱 `c` 与 ψ⁰ c 值相等，`Y` 与 ψ⁰ X 值相等且 `ψ⁰ X ≼ˣ Y`，则 `X + Y` 对 ψ⁰ X 也是如此。

```agda
step : ∀ {X c Y : T₀} → L.HS X → c L.≺ X → L.ψ⁰ c ≼ˣ X → X ≼ L.ψ⁰ c →
  L.ψ⁰ X ≼ˣ Y → Y ≼ L.ψ⁰ X → (L.ψ⁰ X ≼ˣ (X L.+ Y)) × ((X L.+ Y) ≼ L.ψ⁰ X)
step {X} hX cX hx hv hy vy =
  transˣ (Abs.ABS hx hv X hX cX) (+ˣ (reflˣ X) (≼-refl X) hy) ,
  ≼-trans (+-mono (≼-refl X) vy) (Abs.VABS hx hv X hX cX)
```

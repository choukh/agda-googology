# YiChain 第 1 步：`ChainP` 在 n = 1

**验收文件，档位：编译定理。** `chainP₁ : Σ ℕ λ m → D.γ 1 ≼ᵖ read (co (pts m))`，取 m = 1，无前提。
办法：第 0 层的折叠与参照 ψ⁰ 在 `≼ˣ` 里对上 (`PHI`)；内层的累加链 cₙ₊₁ = cₙ + Ψ cₙ 每一步用 [YiChainBase](YiChainBase.lagda.md) 的吸收 (`step`)，前驱取上一个链点；外层第 1 点的左加数 1 也由吸收处理。
不涉及 n ≥ 2 (那里要第 1 层以上的折叠的同类引理)。共用陈述在 [YiLeanValFin](YiLeanValFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiChainOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanLegal using (chain-lgl; Ψ-lgl)
open import OCF.Lean.YiLeanTw3 using (R; F; pts)
open import OCF.Lean.YiLeanTw3 using (module Pt)
open Pt using (co)
open import OCF.Lean.YiLeanAccFin using (read; read-plus)
open import OCF.Lean.YiLeanValFin using (HS-read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼; +-mono)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiVmConExact using (_≼ˣ_; _≼ᵖ_; zˣ; ≼lˣ; lˣ; lᵖ; reflˣ; ≅→≼ˣ)
open import OCF.Lean.YiZeroAccP using (ψ⁰ˣ; +ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ; ⊑+; module Abs; step)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 第 0 层的折叠对参照的 ψ⁰

主线的 ω 倍从 `y` 起 (y, y+y, …)，参照从 0 起：错开一位。

```agda
module Phi (x : Ext zero zero) where

  succPHI : ∀ {A : T₀} (y : R) → A ≼ˣ read y → read y ≼ A →
    (L.lim (iterᴸ (A L.+_) L.zero) ≼ˣ read (succ zero y)) × (read (succ zero y) ≼ L.lim (iterᴸ (A L.+_) L.zero))
  succPHI {A} y ax av = lˣ (λ { zero → zˣ ; (suc n) → ≼lˣ n (proj₁ (cp n)) }) , l≼ (λ n → ≼l (suc n) (proj₂ (cp n)))
    where
    cp : ∀ n → (iterᴸ (A L.+_) L.zero (suc n) ≼ˣ read (acc (λ _ z → plus zero y z) y n)) ×
               (read (acc (λ _ z → plus zero y z) y n) ≼ iterᴸ (A L.+_) L.zero (suc n))
    cp zero = ax , av
    cp (suc n) =
      transˣ (+ˣ ax av (proj₁ (cp n))) (≅→≼ˣ (L.≅-sym (read-plus y (acc (λ _ z → plus zero y z) y n)))) ,
      ≼-trans (≅→≼ (read-plus y (acc (λ _ z → plus zero y z) y n))) (+-mono av (proj₂ (cp n)))

  PHI : ∀ (b : R) → (L.ψ⁰ (read b) ≼ˣ read (Ψ zero v0 x b)) × (read (Ψ zero v0 x b) ≼ L.ψ⁰ (read b))
  PHI G.zero = reflˣ _ , ≼-refl _
  PHI (G.suc a) = succPHI (Ψ zero v0 x a) (proj₁ (PHI a)) (proj₂ (PHI a))
  PHI (G.lim f) = lˣ (λ n → ≼lˣ n (proj₁ (PHI (f n)))) , l≼ (λ n → ≼l n (proj₂ (PHI (f n))))
  PHI (G.lc () g)
  PHI (G.em () a)
  PHI G.top = succPHI G.top (reflˣ _) (≼-refl _)

  lead : ∀ (X : T₀) (b : R) → X L.≺ (X L.+ read (Ψ zero v0 x b))
  lead X G.zero = L.≺z (L.≅-refl⁰ X)
  lead X (G.suc a) = L.≺l 0 (lead X a)
  lead X (G.lim f) = L.≺l 0 (lead X (f 0))
  lead X (G.lc () g)
  lead X (G.em () a)
  lead X G.top = L.≺l 0 (L.≺z (L.≅-refl⁰ X))

open Phi using (PHI; lead)
```

## 2 内层的累加链

`F top` 的链在第 0 层：c₀ = top，cₙ₊₁ = cₙ + Ψ cₙ。不变量：`ψ⁰ (read cₙ) ≼ˣ read cₙ₊₁` 且两者值相等；它的前驱见证是上一个链点 (第 0 步取 0)。

```agda
gk : R → R
gk = Ψ zero v0 (self zero)

cc : ℕ → R
cc = chain zero gk

cc-lgl : ∀ n → Lgl zero (cc n)
cc-lgl = chain-lgl zero gk (λ η l → Ψ-lgl zero v0 (self zero) η l)

hs : ∀ n → L.HS (read (cc n))
hs n = HS-read (cc n) (cc-lgl n)

rp : ∀ n → read (cc (suc n)) L.≅ (read (cc n) L.+ read (gk (cc n)))
rp n = read-plus (cc n) (gk (cc n))

record Wit (X : T₀) : Set where
  constructor wit
  field
    w  : T₀
    lt : w L.≺ X
    wx : L.ψ⁰ w ≼ˣ X
    wv : X ≼ L.ψ⁰ w

fin : ∀ n → Wit (read (cc n)) →
  (L.ψ⁰ (read (cc n)) ≼ˣ read (cc (suc n))) × (read (cc (suc n)) ≼ L.ψ⁰ (read (cc n)))
fin n (wit w lt wx wv) =
  transˣ (proj₁ s) (≅→≼ˣ (L.≅-sym (rp n))) , ≼-trans (≅→≼ (rp n)) (proj₂ s)
  where
  s = step (hs n) lt wx wv (proj₁ (PHI (self zero) (cc n))) (proj₂ (PHI (self zero) (cc n)))

J : ∀ n → (L.ψ⁰ (read (cc n)) ≼ˣ read (cc (suc n))) × (read (cc (suc n)) ≼ L.ψ⁰ (read (cc n)))
W : ∀ n → Wit (read (cc n))
J n = fin n (W n)
W zero = wit L.zero (L.≺z L.z≅) (reflˣ _) (≼-refl _)
W (suc n) = wit (read (cc n)) (L.≺-respʳ (lead (self zero) (read (cc n)) (cc n)) (L.≅-sym (rp n)))
  (proj₁ (J n)) (proj₂ (J n))
```

参照第 1 项内部的链 `D.G` 落在 `read cₙ` 之下。

```agda
Gc : ∀ k → D.G k ≼ˣ read (cc k)
Gc zero = reflˣ _
Gc (suc k) = transˣ (≅→≼ˣ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → L.suc q} (L.≅-refl⁰ (D.G k)))))
  (transˣ (ψ⁰ˣ (Gc k)) (proj₁ (J k)))
```

## 3 外层第 1 点

`co (pts 1) = top + F top`，`F top = lim (Ψ cₙ)`；左加数 1 由吸收处理 (`c = 0`)。

```agda
O : T₀
O = L.zero

z≺ : ∀ k → O L.≺ read (cc k)
z≺ zero = L.≺z L.z≅
z≺ (suc k) = L.≺-respʳ (⊑+ (read (cc k)) (read (gk (cc k))) (z≺ k)) (L.≅-sym (rp k))

x₁ : Ext zero zero
x₁ = λ _ → fold

term : ∀ k → L.ψ⁰ (D.G k) ≼ˣ read (co (pts 1))
term k = ≼lˣ k (transˣ
  (transˣ (ψ⁰ˣ (Gc k))
    (transˣ (Abs.ABS {X = L.suc L.zero} {c = O} (reflˣ _) (≼-refl _) (read (cc k)) (hs k) (z≺ k))
      (+ˣ (reflˣ _) (≼-refl _) (proj₁ (PHI x₁ (cc k))))))
  (≅→≼ˣ (L.≅-sym (read-plus G.top (Ψ zero v0 x₁ (cc k))))))

chainP₁ : Σ ℕ λ m → D.γ 1 ≼ᵖ read (co (pts m))
chainP₁ = 1 , lᵖ term
```

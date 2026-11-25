# YiChain 第 1 步的反向：`read (co (pts 1)) ≼ˣ D.γ 1`

**验收文件，档位：编译定理。** `back₁ : read (co (pts 1)) ≼ˣ D.γ 1`，与 [YiChainOne](YiChainOne.lagda.md) 合起来 `γ₁≈` 是两个方向的 `≼ˣ`，无前提。
办法与正向对称：反向吸收 `ABSR` (`X + ψ⁰ b ≼ˣ ψ⁰ b`，见证仍是结构前驱)，反向的 `PHIR`，内层链的反向不变量。用途：一般的 n 要两侧的值相等 (`≼ˣ` 的 `sˣ`)，这里说明第 0 层上上界一侧也能构造地给出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiChainBack where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R; pts; module Pt)
open Pt using (co)
open import OCF.Lean.YiLeanAccFin using (read; read-plus)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼; ⊑→≼; +-mono; ψ⁰-mono⁰)
import OCF.Align.RR4MonoFragment as MF
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiVmConExact using (_≼ˣ_; zˣ; wˣ; ≼lˣ; lˣ; reflˣ; ≅→≼ˣ; ⊑→≼ˣ; ≺→sˣ; ˣ→≼)
open import OCF.Lean.YiZeroAccP using (ψ⁰ˣ; +ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ; assoc⁰; up⊑)
open import OCF.Lean.YiChainOne using (cc; gk; hs; rp; J; module Phi; z≺; x₁; O; term)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 反向吸收

```agda
module AbsR {X c : T₀} (hx : X ≼ˣ L.ψ⁰ c) (hv : L.ψ⁰ c ≼ X) where

  ABSR : ∀ (b : T₀) → L.HS b → c L.≺ b → (X L.+ L.ψ⁰ b) ≼ˣ L.ψ⁰ b
  ABSR (L.suc b) h (L.≺z e) = lˣ (λ n → ≼lˣ (suc n)
    (+ˣ (transˣ hx (≅→≼ˣ (L.ψ⁰-≅ e))) (≼-trans (≅→≼ (L.ψ⁰-≅ (L.≅-sym e))) hv)
      (reflˣ (iterᴸ (L.ψ⁰ b L.+_) L.zero n))))
  ABSR (L.suc b) h (L.≺s d) = lˣ λ where
    zero → ≼lˣ 1 (transˣ hx (ψ⁰ˣ (transˣ (wˣ (reflˣ c)) (≺→sˣ d))))
    (suc n) → ≼lˣ (suc n) (transˣ (≅→≼ˣ (L.≅-sym (assoc⁰ X (L.ψ⁰ b) (iterᴸ (L.ψ⁰ b L.+_) L.zero n))))
      (+ˣ (ABSR b (L.hs⁻ h) d) (MF.≼-+ˡ X (L.ψ⁰ b)) (reflˣ (iterᴸ (L.ψ⁰ b L.+_) L.zero n))))
  ABSR (L.lim g) h (L.≺l m d) = lˣ (λ n → ≼lˣ (n ⊔ m)
    (transˣ (+ˣ (reflˣ X) (≼-refl X) (ψ⁰ˣ (⊑→≼ˣ (g n) (up⊑ (L.hl₂ h) (≤⇒≤′ (m≤m⊔n n m))))))
      (ABSR (g (n ⊔ m)) (L.hl₁ h (n ⊔ m)) (up⊑ (L.hl₂ h) (≤⇒≤′ (m≤n⊔m n m)) d))))
  ABSR (L.limᵢ () f) h d
  ABSR (L.up () x) h d
```

## 2 第 0 层折叠的反向

```agda
module PhiR (x : Ext zero zero) where

  succR : ∀ {A : T₀} (y : R) → read y ≼ˣ A → A ≼ read y →
    (read (succ zero y) ≼ˣ L.lim (iterᴸ (A L.+_) L.zero)) × (L.lim (iterᴸ (A L.+_) L.zero) ≼ read (succ zero y))
  succR {A} y ax av = lˣ (λ n → ≼lˣ (suc n) (proj₁ (cp n))) , l≼ (λ { zero → z≼ ; (suc n) → ≼l n (proj₂ (cp n)) })
    where
    cp : ∀ n → (read (acc (λ _ z → plus zero y z) y n) ≼ˣ iterᴸ (A L.+_) L.zero (suc n)) ×
               (iterᴸ (A L.+_) L.zero (suc n) ≼ read (acc (λ _ z → plus zero y z) y n))
    cp zero = ax , av
    cp (suc n) =
      transˣ (≅→≼ˣ (read-plus y (acc (λ _ z → plus zero y z) y n))) (+ˣ ax av (proj₁ (cp n))) ,
      ≼-trans (+-mono av (proj₂ (cp n))) (≅→≼ (L.≅-sym (read-plus y (acc (λ _ z → plus zero y z) y n))))

  PHIR : ∀ (b : R) → (read (Ψ zero v0 x b) ≼ˣ L.ψ⁰ (read b)) × (L.ψ⁰ (read b) ≼ read (Ψ zero v0 x b))
  PHIR G.zero = reflˣ _ , ≼-refl _
  PHIR (G.suc a) = succR (Ψ zero v0 x a) (proj₁ (PHIR a)) (proj₂ (PHIR a))
  PHIR (G.lim f) = lˣ (λ n → ≼lˣ n (proj₁ (PHIR (f n)))) , l≼ (λ n → ≼l n (proj₂ (PHIR (f n))))
  PHIR (G.lc () g)
  PHIR (G.em () a)
  PHIR G.top = succR G.top (reflˣ _) (≼-refl _)

open PhiR using (PHIR)
```

## 3 内层链的反向

```agda
record WitR (X : T₀) : Set where
  constructor witR
  field
    w  : T₀
    lt : w L.≺ X
    wx : X ≼ˣ L.ψ⁰ w
    wv : L.ψ⁰ w ≼ X

finR : ∀ n → WitR (read (cc n)) → read (cc (suc n)) ≼ˣ L.ψ⁰ (read (cc n))
finR n (witR w lt wx wv) = transˣ (≅→≼ˣ (rp n))
  (transˣ (+ˣ (reflˣ _) (≼-refl _) (proj₁ (PHIR (self zero) (cc n)))) (AbsR.ABSR wx wv (read (cc n)) (hs n) lt))

JR : ∀ n → read (cc (suc n)) ≼ˣ L.ψ⁰ (read (cc n))
WR : ∀ n → WitR (read (cc n))
JR n = finR n (WR n)
WR zero = witR L.zero (L.≺z L.z≅) (reflˣ _) (≼-refl _)
WR (suc n) = witR (read (cc n)) (L.≺-respʳ (Phi.lead (self zero) (read (cc n)) (cc n)) (L.≅-sym (rp n)))
  (JR n) (ˣ→≼ (proj₁ (J n)))

GcR : ∀ k → read (cc k) ≼ˣ D.G k
GcR zero = reflˣ _
GcR (suc k) = transˣ (JR k) (transˣ (ψ⁰ˣ (GcR k))
  (≅→≼ˣ (L.ψ⁰≅ψ {p = L.zero} {σ = λ q → L.suc q} (L.≅-refl⁰ (D.G k)))))
```

## 4 外层第 1 点

```agda
termR : ∀ k → read (plus zero G.top (Ψ zero v0 x₁ (cc k))) ≼ˣ D.γ 1
termR k = transˣ (≅→≼ˣ (read-plus G.top (Ψ zero v0 x₁ (cc k))))
  (transˣ (+ˣ (reflˣ _) (≼-refl _) (proj₁ (PHIR x₁ (cc k))))
    (transˣ (AbsR.ABSR {X = L.suc L.zero} {c = O} (reflˣ _) (≼-refl _) (read (cc k)) (hs k) (z≺ k))
      (transˣ (ψ⁰ˣ (GcR k)) (≼lˣ k (reflˣ _)))))

back₁ : read (co (pts 1)) ≼ˣ D.γ 1
back₁ = lˣ termR

γ₁≈ : (D.γ 1 ≼ˣ read (co (pts 1))) × (read (co (pts 1)) ≼ˣ D.γ 1)
γ₁≈ = lˣ term , back₁
```

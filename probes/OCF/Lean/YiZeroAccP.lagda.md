# YiZero 验收：判据 C2′ 归约到左加平移

**验收文件，档位：条件定理。** `c2′ : Tr → D.γ 1 ≼ᵖ read (co (pts 1))`，前提 `Tr` 是只谈第 0 层参照树的平移律 "x ≼ˣ y 推出 x ≼ˣ X + y"；`tri→tr : Tri → Tr` (故经典模型里成立，但 `Tri` 推出 LPO)。
无条件的部分：ψ⁰ 与同底的加法保持 `≼ˣ` (`ψ⁰ˣ`, `ψˣ`, `+ˣ`)，第 0 层的折叠读回与参照 ψ⁰ 结构互模拟 (`readΨ`，ω 倍从零起才成立)。链在两处用到平移：内层链点 cₙ₊₁ = cₙ + Ψ cₙ，外层第 1 点 = 1 + F top。
`Tr` 没有证；卡在 `sˣ` 的旁证 `X + b ≼ a` (要吸收 X + b ≈ b)。闭项在 [YiZeroTw3](YiZeroTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZeroAccP where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import OCF.Lean.YiZeroCore
open import OCF.Lean.YiZeroFold
open import OCF.Lean.YiZeroTw3
open Pt
open import OCF.Lean.YiZeroAcc using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; ψ⁰-mono⁰; +-mono)
import OCF.Align.RR4MonoFragment as MF
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.YiVmConExact using (_≼ˣ_; zˣ; sˣ; wˣ; ≼lˣ; lˣ; _≼ᵖ_; lᵖ; reflˣ; ˣ→≼; Tri; tri→cplˣ)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)

T₀ : Set
T₀ = L.Ordᶜ L.zero
```

## 1 `≼ˣ` 对加法与 ψ⁰ 的保持

```agda
wk+ : ∀ {a b : T₀} → a ≼ˣ b → ∀ y → a ≼ˣ (b L.+ y)
wk+ d L.zero = d
wk+ d (L.suc y) = wˣ (wk+ d y)
wk+ d (L.lim g) = ≼lˣ 0 (wk+ d (g 0))
wk+ d (L.limᵢ () f)
wk+ d (L.up () x)

+ˣ : ∀ {p p′ q q′ : T₀} → p ≼ˣ p′ → p′ ≼ p → q ≼ˣ q′ → (p L.+ q) ≼ˣ (p′ L.+ q′)
+ˣ {q′ = q′} d e zˣ = wk+ d q′
+ˣ d e (sˣ f g) = sˣ (+ˣ d e f) (+-mono e g)
+ˣ d e (wˣ f) = wˣ (+ˣ d e f)
+ˣ d e (≼lˣ n f) = ≼lˣ n (+ˣ d e f)
+ˣ d e (lˣ h) = lˣ (λ n → +ˣ d e (h n))

one≼ˣ : ∀ (b : T₀) → L.suc L.zero ≼ˣ L.ψ⁰ b
one≼ˣ L.zero = reflˣ _
one≼ˣ (L.suc b) = ≼lˣ 1 (one≼ˣ b)
one≼ˣ (L.lim g) = ≼lˣ 0 (one≼ˣ (g 0))
one≼ˣ (L.limᵢ () f)
one≼ˣ (L.up () x)

ψ⁰ˣ : ∀ {a b : T₀} → a ≼ˣ b → L.ψ⁰ a ≼ˣ L.ψ⁰ b
ψ⁰ˣ {b = b} zˣ = one≼ˣ b
ψ⁰ˣ {L.suc a} {L.suc b} (sˣ d e) = lˣ (λ n → ≼lˣ n (it n)) where
  it : ∀ n → iterᴸ (L.ψ⁰ a L.+_) L.zero n ≼ˣ iterᴸ (L.ψ⁰ b L.+_) L.zero n
  it zero = zˣ
  it (suc n) = +ˣ (ψ⁰ˣ d) (ψ⁰-mono⁰ e) (it n)
ψ⁰ˣ (wˣ d) = ≼lˣ 1 (ψ⁰ˣ d)
ψ⁰ˣ (≼lˣ n d) = ≼lˣ n (ψ⁰ˣ d)
ψ⁰ˣ (lˣ h) = lˣ (λ n → ψ⁰ˣ (h n))

ψˣ : ∀ {ℓ} (p : L.zero L.<ᴵ ℓ) (σ : L.Simᴵ L.zero ℓ) {a b : T₀} → a ≼ˣ b → L.ψ p σ a ≼ˣ L.ψ⁰ b
ψˣ p σ {b = b} zˣ = one≼ˣ b
ψˣ p σ {L.suc a} {L.suc b} (sˣ d e) = lˣ (λ n → ≼lˣ n (it n)) where
  it : ∀ n → iterᴸ (L.ψ p σ a L.+_) L.zero n ≼ˣ iterᴸ (L.ψ⁰ b L.+_) L.zero n
  it zero = zˣ
  it (suc n) = +ˣ (ψˣ p σ d)
    (≼-trans (ψ⁰-mono⁰ e) (≅→≼ (L.ψ⁰≅ψ {p = p} {σ = σ} (L.≅-refl⁰ a)))) (it n)
ψˣ p σ (wˣ d) = ≼lˣ 1 (ψˣ p σ d)
ψˣ p σ (≼lˣ n d) = ≼lˣ n (ψˣ p σ d)
ψˣ p σ (lˣ h) = lˣ (λ n → ψˣ p σ (h n))

respʳ : ∀ {a b c : T₀} → a ≼ˣ b → b L.≅ c → a ≼ˣ c
respʳ zˣ e = zˣ
respʳ (sˣ d v) (L.s≅ e) = sˣ (respʳ d e) (≼-trans (≅→≼ (L.≅-sym e)) v)
respʳ (wˣ d) (L.s≅ e) = wˣ (respʳ d e)
respʳ (≼lˣ n d) (L.l≅ h) = ≼lˣ n (respʳ d (h n))
respʳ (lˣ k) e = lˣ (λ n → respʳ (k n) e)
```

## 2 第 0 层的折叠读回就是参照的 ψ⁰

```agda
plus≅ : ∀ {A B : T₀} Y Z → A L.≅ read Y → B L.≅ read Z → (A L.+ B) L.≅ read (plus zero Y Z)
plus≅ Y G.zero a L.z≅ = a
plus≅ Y (G.suc Z) a (L.s≅ b) = L.s≅ (plus≅ Y Z a b)
plus≅ Y (G.lim f) a (L.l≅ h) = L.l≅ (λ n → plus≅ Y (f n) a (h n))
plus≅ Y (G.lc () g) a b
plus≅ Y (G.em () z) a b
plus≅ Y G.top a (L.s≅ L.z≅) = L.s≅ a

copies : ∀ {A : T₀} Y → A L.≅ read Y → ∀ n →
  iterᴸ (A L.+_) L.zero n L.≅ read (acc (λ _ z → plus zero Y z) G.zero n)
copies Y e zero = L.z≅
copies Y e (suc n) = plus≅ Y _ e (copies Y e n)

readΨ : ∀ x c → L.ψ⁰ (read c) L.≅ read (Ψ zero v0 x c)
readΨ x G.zero = L.s≅ L.z≅
readΨ x (G.suc a) = L.l≅ (copies (Ψ zero v0 x a) (readΨ x a))
readΨ x (G.lim f) = L.l≅ (λ n → readΨ x (f n))
readΨ x (G.lc () g)
readΨ x (G.em () a)
readΨ x G.top = L.l≅ (copies G.top (L.s≅ L.z≅))
```

## 3 归约

```agda
Tr : Set
Tr = ∀ (X x y : T₀) → x ≼ˣ y → x ≼ˣ (X L.+ y)

tri→tr : Tri → Tr
tri→tr t X x y d = tri→cplˣ t x (X L.+ y) (≼-trans (ˣ→≼ d) (MF.≼-+ˡ X y))

gk : R → R
gk = Ψ zero v0 (self zero)

module _ (tr : Tr) where
  Gc : ∀ n → D.G n ≼ˣ read (chain zero gk n)
  Gc zero = reflˣ _
  Gc (suc n) = respʳ
    (tr (read (chain zero gk n)) _ _ (respʳ (ψˣ L.zero _ (Gc n)) (readΨ (self zero) (chain zero gk n))))
    (plus≅ (chain zero gk n) (gk (chain zero gk n)) (L.≅-refl⁰ _) (L.≅-refl⁰ _))

  term : ∀ n → L.ψ⁰ (D.G n) ≼ˣ read (co (pts 1))
  term n = respʳ (tr (L.suc L.zero) _ _ (≼lˣ n (respʳ (ψ⁰ˣ (Gc n)) (readΨ _ (chain zero gk n)))))
    (plus≅ G.top (F G.top tt) (L.s≅ L.z≅) (L.≅-refl⁰ _))

  c2′ : D.γ 1 ≼ᵖ read (co (pts 1))
  c2′ = lᵖ term
```

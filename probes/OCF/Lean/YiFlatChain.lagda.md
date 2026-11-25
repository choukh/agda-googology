# YiFlat 链上：主线链点处的两向吸收

**验收文件，档位：编译定理 (n = 0) 与条件定理 (一般 n)。** 记 `X = read (co (pts (suc n)))`，`s = Ω (κ (suc n))`。`absorb n`：若 `X` 与 ψ⁰(Ω_{κ n}) 两向 `≼ˣ` (`P2at n`，即 `YiEmb2.P2₂` 的第 n 项)，则 `ψ⁰ s ≼ˣ X + ψ⁰ s` 且 `X + ψ⁰ s ≼ˣ ψ⁰ s`。`absorb₁`：n = 0 (s = Ω (κ 1)，X 是第 1 个链点) 无前提。
见证 `κ n ≺ᴵ κ (suc n)` 对一切 n 无条件 (`κ≺`)。`step₂`/`p2-from-fold`：`P2at` 归约到主线折叠值与 ψ⁰(Ω_{κ m}) 的两向 `≼ˣ` (`FoldB m`，m ≥ 1)；`FoldB` 未证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFlatChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R; lv; pts; obs; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read)
open import OCF.Lean.YiLeanValFin using (κ; chain-cum; HS-read)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
open import OCF.Align.YiVmConExact using (_≼ˣ_; ˣ→≼; reflˣ; ≅→≼ˣ)
open import OCF.Lean.YiZeroAccP using (+ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ)
open import OCF.Lean.YiChainCond using (p2₀)
open import OCF.Lean.YiChainBack using (back₁)
open import OCF.Lean.YiFlatAbs using (absΩ; absΩR)
```

## 1 链点严格上升

`F` 在 `top` 处的值沿每个极限的第 0 支走到 1，所以带 0 的前驱 (`Z-top`)；于是 X ≺ X + F X (`lead0`)。

```agda
Ψn⁰ : ∀ j (w : Way zero j) (gm : Raw j → R) (gk : Raw j → Raw j) →
  L.𝟎 {L.zero} L.≺ read (gm G.top) → L.𝟎 {L.zero} L.≺ read (Ψn zero j w gm gk)
Ψn⁰ j (keep () e) gm gk d
Ψn⁰ j fold gm gk d = L.≺l 0 d

Z-top : ∀ {k} (V : Lv k) (x : Ext zero k) → L.𝟎 {L.zero} L.≺ read (Ψ zero V x G.top)
Z-top v0 x = L.≺l 0 (L.≺z L.z≅)
Z-top (vs {k} V) x = Ψn⁰ k (x (inj₁ tt)) (λ η → Ψ zero V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η)
  (Z-top V (λ r → x (inj₂ r)))
Z-top (vl V st) x = L.≺l 0 (Z-top (V 0) (λ r → x (0 , r)))

lead0 : ∀ (X : T₀) {Y : T₀} → L.𝟎 {L.zero} L.≺ Y → X L.≺ (X L.+ Y)
lead0 X (L.≺z L.z≅) = L.≺z (L.≅-refl⁰ X)
lead0 X (L.≺z (L.upʳ {r = ()} e))
lead0 X (L.≺s d) = L.≺s (lead0 X d)
lead0 X (L.≺l n d) = L.≺l n (lead0 X d)
lead0 X (L.≺i {p = ()} x ex d)
lead0 X (L.≺u {r = ()} d)

X≺ : ∀ n → read (co (pts n)) L.≺ read (co (pts (suc n)))
X≺ n = L.≺-respʳ (lead0 (read (co (pts n))) (Z-top (lv (co (pts n)) (lw (pts n))) (λ _ → fold)))
  (L.≅-sym (chain-cum n))

κ≺ : ∀ n → κ n L.≺ᴵ κ (suc n)
κ≺ n = L.toLevel-≺ (HS-read (co (pts n)) (lw (pts n))) (HS-read (co (pts (suc n))) (lw (pts (suc n)))) (X≺ n)
```

## 2 两向吸收

```agda
absorb : ∀ n →
  (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n))) →
  (L.ψ⁰ (L.Ω (κ (suc n))) ≼ˣ (read (co (pts (suc n))) L.+ L.ψ⁰ (L.Ω (κ (suc n))))) ×
  ((read (co (pts (suc n))) L.+ L.ψ⁰ (L.Ω (κ (suc n)))) ≼ˣ L.ψ⁰ (L.Ω (κ (suc n))))
absorb n (f , b) = absΩ (κ≺ n) f (ˣ→≼ b) , absΩR (κ≺ n) b (ˣ→≼ f)

absorb₁ :
  (L.ψ⁰ (L.Ω (κ 1)) ≼ˣ (read (co (pts 1)) L.+ L.ψ⁰ (L.Ω (κ 1)))) ×
  ((read (co (pts 1)) L.+ L.ψ⁰ (L.Ω (κ 1))) ≼ˣ L.ψ⁰ (L.Ω (κ 1)))
absorb₁ = absorb 0 (p2₀ , back₁)
```

## 3 归约到折叠的两向界

下一点是这一点加折叠值 (`chain-cum`)：吸收之后只剩折叠值本身与 ψ⁰ s 的两向比较。

```agda
P2at : ℕ → Set
P2at n = (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n)))

FoldB : ℕ → Set
FoldB m = (L.ψ⁰ (L.Ω (κ m)) ≼ˣ read (obs (pts m))) × (read (obs (pts m)) ≼ˣ L.ψ⁰ (L.Ω (κ m)))

step₂ : ∀ n → P2at n → FoldB (suc n) → P2at (suc n)
step₂ n p f =
  transˣ (proj₁ (absorb n p)) (transˣ (+ˣ (reflˣ X) (≼-refl X) (proj₁ f)) (≅→≼ˣ (L.≅-sym (chain-cum (suc n))))) ,
  transˣ (≅→≼ˣ (chain-cum (suc n))) (transˣ (+ˣ (reflˣ X) (≼-refl X) (proj₂ f)) (proj₂ (absorb n p)))
  where X = read (co (pts (suc n)))

p2-from-fold : (∀ n → FoldB (suc n)) → ∀ n → P2at n
p2-from-fold fb zero = p2₀ , back₁
p2-from-fold fb (suc n) = step₂ n (p2-from-fold fb n) (fb n)
```

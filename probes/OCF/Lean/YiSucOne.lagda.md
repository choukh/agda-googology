# YiSuc 第 1 步：`ChainPt G.top tt 1` 两向

**验收文件，档位：编译定理，无前提。** `chainPt-top-1 : ChainPt G.top tt 1` ([YiUBRed](YiUBRed.lagda.md) 的共用陈述)：参照 `ψ⁰ (ψ₁ (Ω₁))` 与主线 `Ψ⁰ (top + Φ top)` 两个方向都在 `≼ˣ` 里 (两边读法都是 ψ₀(Ω₁²)，这里是定理)。
办法：外层结点用 [YiSucNode](YiSucNode.lagda.md) (主线链累加，参照不累加，对数 `flat ∘ ψ₁`)；分支 `top + M a` 先与 `Ω₁ + ψ₁ a` 并行 ([YiSucPar](YiSucPar.lagda.md))，再由 [YiSucAbs](YiSucAbs.lagda.md) 吸收 Ω₁。不涉及链的第 2 项以上 (那里要第 1 层上的吸收，见回报)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSucOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanLegal using (plus-lgl; chain-lgl; Ψ-lgl)
open import OCF.Lean.YiLeanTw3 using (R)
open import OCF.Lean.YiLeanAccFin using (read; read-plus)
import OCF.Align.Level as L
open import OCF.Align.YiVmConExact using (≅→≼ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ)
open import OCF.Lean.YiChainFlat using (flat; ψ⁰-flat)
open import OCF.Lean.YiFlatObs using (Good-Ω; HS-flat)
open import OCF.Lean.YiUBRed using (Two; ChainPt)
open import OCF.Lean.YiSucLx using (F₁; cong₁)
open import OCF.Lean.YiSucNode using (module Chains; module NodeTwo)
open import OCF.Lean.YiSucPar using (L1; R₁; Ω₁; ε; S; ok; Ψ⁰; xc; xk; M; baseΩ; two; Z1; lead; selfF; goodF)
open import OCF.Lean.YiSucAbs using (Pos; pt; pos-plus; refabs; strict)
```

## 1 外层结点的两边

```agda
h₁ : R → R₁
h₁ η = plus L1 G.top (M η)

gm gk : R → R
gm η = Ψ⁰ (λ _ → fold) (h₁ η)
gk η = Ψ⁰ xc (h₁ η)

open Chains F₁ gk

lgl : ∀ n → Lgl zero (d n)
lgl = chain-lgl zero gk (λ η l → Ψ-lgl zero (vs v0) xc (h₁ η) (plus-lgl L1 G.top (M η) tt (Ψ-lgl L1 v0 xk η l)))

pos : ∀ n → Pos (d n)
pos zero = pt
pos (suc n) = pos-plus (pos n) (gk (d n))

pΩ : L.𝟎 {L.zero} L.≺ flat Ω₁
pΩ = L.≺l 0 (L.≺z L.z≅)

s₀ : S Ω₁ ε G.top ε
s₀ = baseΩ , ok (Good-Ω (L.suc L.zero)) (L.Ω-refl _) tt tt tt pΩ

branch : ∀ x n → Two (L.ψ⁰ (F₁ (X n))) (read (Ψ⁰ x (h₁ (d n))))
branch x n = transˣ (proj₁ (refabs (pos n))) (proj₁ (two (d n) (lgl n) s₀ x)) ,
  transˣ (proj₂ (two (d n) (lgl n) s₀ x)) (proj₂ (refabs (pos n)))

lt : ∀ n → X n L.≺ X (suc n)
lt n = L.≺-respʳ (lead (X n) (Z1 xc (h₁ (d n)))) (L.≅-sym (read-plus (d n) (gk (d n))))
```

## 2 结论

```agda
module Top = NodeTwo F₁ selfF gm gk (λ y → flat (F₁ y))
  (branch (λ _ → fold)) (branch xc) cong₁
  (λ y → ≅→≼ˣ (ψ⁰-flat (F₁ y)) , ≅→≼ˣ (L.≅-sym (ψ⁰-flat (F₁ y))))
  (λ n → HS-flat (goodF (d n) (lgl n)) (selfF (X n)))
  (λ n → strict (lt n)) (L.≺l 1 pΩ)

chainPt-top-1 : ChainPt G.top tt 1
chainPt-top-1 = Top.result fold
```

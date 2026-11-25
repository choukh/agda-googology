# YiOver 第 2 层：主线折叠不超过参照

**验收文件，档位：编译定理，无前提。** `over₂ : read (F (fin 2) tt) ≼ L.ψ⁰ (L.Ω ⟨ 2 ⟩)`；与已有的 `lower₂` 合起来值相等 (`≈₂`)；严格超过被否定 (`no-over₂`)。最早的链点 (`ChainPt G.top tt 1` 的两边) 同样值相等 (`pt≈`, `no-over-pt`)。
办法：主线的链 `chain L1 Φ n` 不高于一条同样累加的参照链 `γ′ n` ([YiOverMain](YiOverMain.lagda.md) 的 `⊵`)，`γ′ n` 落在不累加的参照 `γ 1 (2n)` 之内 (`step-γ`)，第 1 个链点处不错开 (`O2ref`)。
不否定什么：结论是值序 `≼`，不是 `≼ˣ`；一般的链点 `n` 只到错开下标的上界 (`term`, `γ′≤γ`)，`γ′ n ≤ₚ γ 1 n` 没有证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOverTwo where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R; F; ⌜_⌝; lv)
open import OCF.Lean.YiLeanAccFin using (read; fin; L1; R₁; Φ; lower₂; chain₂; fold-lower)
open import OCF.Lean.YiLeanValFin using (HS-read)
open import OCF.Lean.YiUBRed using (L′; refγ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼l; l≼; ≼-trans)
open import OCF.Align.YiLvValBase using (⟨_⟩; γ; γ-self)
open import OCF.Align.YiVmConExact using (irr)
open import OCF.Lean.YiOverRef
open import OCF.Lean.YiOverOps
open import OCF.Lean.YiOverMain
```

## 1 链

```agda
γ′ : ℕ → T₁
γ′ zero = Ω₁
γ′ (suc n) = γ′ n L.+ ψ₁ (γ′ n)

Gd-γ′ : ∀ n → Gd (γ′ n)
Gd-γ′ zero = Gd-Ω
Gd-γ′ (suc n) = Gd-+ (Gd-γ′ n) (Gd-ψ₁ (Gd-γ′ n))

chain⊵ : ∀ n → chain L1 Φ n ⊵ γ′ n
chain⊵ zero = tp (λ a y o q → em q)
chain⊵ (suc n) = +-comp (chain⊵ n) (Φ-pres (chain⊵ n))

term : ∀ n → read (Ψ zero (vs v0) (λ _ → fold) (chain L1 Φ n)) ≼ L.ψ⁰ (γ′ n)
term n = up⁰ (λ _ → fold) (Gd-γ′ n) (chain⊵ n)

Gd-γ : ∀ m → Gd (γ 1 m)
Gd-γ zero = Gd-Ω
Gd-γ (suc m) = Gd-ψ₁ (Gd-γ m)

Inv-γ : ∀ m → Inv (γ 1 m)
Inv-γ zero = inv-Ω
Inv-γ (suc m) = inv-ψ₁ (Gd-γ m) (Inv-γ m)

dbl : ℕ → ℕ
dbl zero = zero
dbl (suc n) = suc (suc (dbl n))

γ′≤γ : ∀ n → γ′ n ≤ₚ γ 1 (dbl n)
γ′≤γ zero = Ω≤Ω
γ′≤γ (suc n) = step-γ (Gd-γ (dbl n)) (Inv-γ (dbl n)) (γ′≤γ n)
```

## 2 第 2 层 (O1)

```agda
over₂ : read (F (fin 2) tt) ≼ L.ψ⁰ (L.Ω ⟨ 2 ⟩)
over₂ = l≼ (λ n → ≼l (dbl n) (≼-trans (term n) (mono⁰ (γ′≤γ n))))

≈₂ : (L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (F (fin 2) tt)) × (read (F (fin 2) tt) ≼ L.ψ⁰ (L.Ω ⟨ 2 ⟩))
≈₂ = lower₂ , over₂

no-over₂ : ¬ (L.suc (L.ψ⁰ (L.Ω ⟨ 2 ⟩)) ≼ read (F (fin 2) tt))
no-over₂ h = irr _ (≼-trans h over₂)

ub₂ : read (F (fin 2) tt) ≼ L.ψ⁰ (L.Ω (L.toLevel (read (fin 2)) (HS-read (fin 2) tt)))
ub₂ = over₂

ub-suc-top : read (F (G.suc G.top) tt) ≼ L.ψ⁰ (L.Ω (L.toLevel (read (G.suc G.top)) (HS-read (G.suc G.top) tt)))
ub-suc-top = over₂
```

## 3 最早的链点 (O2)

`YiUBRed.ChainPt G.top tt 1` 的两边，逐字。

```agda
over-pt : read (Ψ zero (lv G.top tt) (λ _ → fold) (chain ⌜ G.top ⌝ (Ψ ⌜ G.top ⌝ (lv G.top tt) (self ⌜ G.top ⌝)) 1))
  ≼ L.ψ⁰ (refγ (L′ G.top tt) 1)
over-pt = ≼-trans (term 1) (mono⁰ O2ref)

low-pt : L.ψ⁰ (refγ (L′ G.top tt) 1)
  ≼ read (Ψ zero (lv G.top tt) (λ _ → fold) (chain ⌜ G.top ⌝ (Ψ ⌜ G.top ⌝ (lv G.top tt) (self ⌜ G.top ⌝)) 1))
low-pt = fold-lower (λ r → fold) {X = γ 1 1} (chain₂ 1) (γ-self 1 1)

no-over-pt : ¬ (L.suc (L.ψ⁰ (refγ (L′ G.top tt) 1))
  ≼ read (Ψ zero (lv G.top tt) (λ _ → fold) (chain ⌜ G.top ⌝ (Ψ ⌜ G.top ⌝ (lv G.top tt) (self ⌜ G.top ⌝)) 1)))
no-over-pt h = irr _ (≼-trans h over-pt)
```

## 4 值序下的 `SucP G.top tt` 与一切链点 (错开下标)

`sucPᵛ`：[YiUBRed](YiUBRed.lagda.md) 的 `SucP G.top tt` 把 `≼ˣ` 换成 `≼` 后的两个方向。`pt-shift`：第 n 个链点的读回在参照第 n 项与第 2n 项之间。

```agda
sucPᵛ : (L.ψ⁰ (L.Ω (L′ (G.suc G.top) tt)) ≼ read (F (G.suc G.top) tt)) ×
        (read (F (G.suc G.top) tt) ≼ L.ψ⁰ (L.Ω (L′ (G.suc G.top) tt)))
sucPᵛ = lower₂ , over₂

pt-shift : ∀ n → (L.ψ⁰ (γ 1 n) ≼ read (Ψ zero (vs v0) (λ _ → fold) (chain L1 Φ n))) ×
                 (read (Ψ zero (vs v0) (λ _ → fold) (chain L1 Φ n)) ≼ L.ψ⁰ (γ 1 (dbl n)))
pt-shift n = fold-lower (λ r → fold) {X = γ 1 n} (chain₂ n) (γ-self 1 n) , ≼-trans (term n) (mono⁰ (γ′≤γ n))
```

# 错位处的折叠: 左保留右折叠时 `Simʰ` 确实不成立

验收文件. 编译定理与有限测试 (`refl`), 无前提. 在 [YiCompatDlNeg](YiCompatDlNeg.lagda.md) 的错位配置上 (左: `tw 2` 的支 `ω+2` 的公共上界, 内层派发 `cmpw _ (inj₁ tt)`; 右: `Lw-tw 3`, 派发 `cmpw _ r₃`; 目标层都是 `ω+1`), 输入相关 (`sim-in`) 而输出不相关 (`not-out`), 反方向相关 (`rev-out`), 右边的输出与 `top` 互相 `Simʰ`, `top` 是左边输出的严格第一位置 (`top-below`).
左右互换 (左折叠右保留) 时同一对输入的输出相关 (`swap-ok`). 外层 (`Lw-tw 2` 对 `Lw-tw 3`, 外部派发折叠) 一对相关的输入, 内层链经过这个配置, 第 0 层的输出逐字相等 (`eq0`, 有限测试). 第 0 层上使输出不相关的输入没有找到.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCompatDlLoss where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R)
open import OCF.Lean.YiLamFold using (Lw; w0; Lw-tw; lgl→Lw)
open import OCF.Lean.YiDlFold using (Ψ; cmpw)
open import OCF.Lean.YiCrossIface
open import OCF.Lean.YiCompatDlNeg using (ʰ→P; reflR; ωR; ωR-lgl; ω2; Ωω; p₁; p₀; r₃; q₃; η₁)
```

## 1 错位配置上的一对输入

```agda
VL : Lw (suc (suc Ωω))
VL = lgl→Lw zero tt w0 ω2 ωR-lgl

ξL : Raw (suc (suc Ωω))
ξL = G.lc (inj₂ (inj₁ tt)) (λ _ → G.zero)

ξR : Raw (tw 3)
ξR = G.lc q₃ (λ _ → G.zero)

sim-in : Simʰ (suc (suc Ωω)) (tw 3) ξL ξR
sim-in = nN refl (ʰ→P (suc (suc Ωω)) (inj₂ (inj₁ tt)) (tw 3) q₃ (reflR ωR)) (λ _ _ _ → zS)

outL : Ψ (suc Ωω) VL (cmpw VL (inj₁ tt)) ξL ≡ G.lc (inj₁ tt) (λ _ → G.top)
outL = refl

outR : Ψ (suc Ωω) (Lw-tw 3) (cmpw (Lw-tw 3) r₃) ξR ≡ G.lim (λ _ → G.top)
outR = refl
```

## 2 输出不相关

保留的结点在 `ω+1` 层的 `top` 之上; 折叠给出的极限只能经 `cR` 落到孩子 `ω` 的 `top`, 再到第 0 个孩子 (第 0 层) 的 `top`, 那里没有孩子.

```agda
no-top₃ : ∀ {g} → Simʰ (suc Ωω) zero (G.lc (inj₁ tt) g) G.top → ⊥
no-top₃ (cR {i′ = ()} c d)

no-top₂ : ∀ {g} → Simʰ (suc Ωω) Ωω (G.lc (inj₁ tt) g) G.top → ⊥
no-top₂ (cR refl d) = no-top₃ d

no-top₁ : ∀ {g} → Simʰ (suc Ωω) (suc Ωω) (G.lc (inj₁ tt) g) G.top → ⊥
no-top₁ (cR c d) = no-top₂ d

not-out : Simʰ (suc Ωω) (suc Ωω) (Ψ (suc Ωω) VL (cmpw VL (inj₁ tt)) ξL)
  (Ψ (suc Ωω) (Lw-tw 3) (cmpw (Lw-tw 3) r₃) ξR) → ⊥
not-out (lR n d) = no-top₁ d

rev-out : Simʰ (suc Ωω) (suc Ωω) (Ψ (suc Ωω) (Lw-tw 3) (cmpw (Lw-tw 3) r₃) ξR)
  (Ψ (suc Ωω) VL (cmpw VL (inj₁ tt)) ξL)
rev-out = lL (λ _ → bR (reflR (G.suc ωR)))

R⊑top : Simʰ (suc Ωω) (suc Ωω) (Ψ (suc Ωω) (Lw-tw 3) (cmpw (Lw-tw 3) r₃) ξR) G.top
R⊑top = lL (λ _ → reflR (G.suc ωR))

top⊑R : Simʰ (suc Ωω) (suc Ωω) G.top (Ψ (suc Ωω) (Lw-tw 3) (cmpw (Lw-tw 3) r₃) ξR)
top⊑R = lR 0 (reflR (G.suc ωR))

top-below : Dn (suc Ωω) G.top (Ψ (suc Ωω) VL (cmpw VL (inj₁ tt)) ξL)
top-below = inj₁ refl
```

## 3 左右互换 (有限测试)

左边是 `Lw-tw 2` (派发 `dl`, 折叠), 右边是支 `ω+2` (结构派发, 保留).

```agda
ξ₂ : Raw (tw 2)
ξ₂ = G.lc p₀ (λ _ → G.zero)

sim-swap : Simʰ (tw 2) (suc (suc Ωω)) ξ₂ ξL
sim-swap = nN refl (ʰ→P (tw 2) p₀ (suc (suc Ωω)) (inj₂ (inj₁ tt)) (reflR ωR)) (λ _ _ _ → zS)

swap-ok : Simʰ (suc Ωω) (suc Ωω) (Ψ (suc Ωω) (Lw-tw 2) (cmpw (Lw-tw 2) p₁) ξ₂)
  (Ψ (suc Ωω) VL (cmpw VL (inj₁ tt)) ξL)
swap-ok = lL (λ _ → bR (reflR (G.suc ωR)))
```

## 4 外层的一对 (有限测试)

`ξ₀` 是 `tw 2` 的支 `ω+2` 里的结点 (嵌入), `ξ₀′` 是 `tw 3` 里位置 `r₃` 上的结点; 两边的分支取常值 `ξL`, 所以第 0 层的输出不依赖链点.

```agda
ξ₀ : Raw (tw 2)
ξ₀ = G.em (ω2 , ωR-lgl) (G.lc (inj₁ tt) (λ _ → ξL))

ξ₀′ : Raw (tw 3)
ξ₀′ = G.lc r₃ (λ _ → G.em (η₁ , tt) (G.em (ω2 , ωR-lgl) ξL))

ξL-refl : Simʰ (suc (suc Ωω)) (suc (suc Ωω)) ξL ξL
ξL-refl = nN refl (ʰ→P (suc (suc Ωω)) (inj₂ (inj₁ tt)) (suc (suc Ωω)) (inj₂ (inj₁ tt)) (reflR ωR)) (λ _ _ _ → zS)

sim₀ : Simʰ (tw 2) (tw 3) ξ₀ ξ₀′
sim₀ = eL (nN refl (ʰ→P (suc (suc Ωω)) (inj₁ tt) (tw 3) r₃ (reflR (G.suc ωR))) (λ _ _ _ → eR (eR ξL-refl)))

eq0 : Ψ zero (Lw-tw 2) (λ _ → fold) ξ₀ ≡ Ψ zero (Lw-tw 3) (λ _ → fold) ξ₀′
eq0 = refl
```

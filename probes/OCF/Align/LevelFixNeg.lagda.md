# 这一组定义的边界: 编译过的否定

> 不含记号. 结论写在 [LevelFix](LevelFix.lagda.md). **这些定理只否定写明的东西, 不否定 "一次性封闭".**

- `no-Lgl-Ωlim`: 块里的 `Lgl` 不接受跨孩子的步进: $\lim_n$ `em n top` 在 `Raw ω` 里不合法. 所以 $\Omega_\omega\cdot2$ 这样的值 (对 $n$ 的 $\lim$, 第 $n$ 项在第 $n$ 个孩子里) 过不了 $\Omega_{\omega+1}$ 的守卫. 只否定这个 `Lgl`. 成因是正性 (`LevelFixCore` 的 `P1`), 那是检查器的事实.
- `no-cp-Ω3-Ω2`: 第一位置守卫窄, 与 `no-fg-Ω3-Ω2` 同形. 这就是 `chain-stuck` 没有解决的原因: 链点不是下界的第一位置之上.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LevelFixNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.LevelFixCore
open import OCF.Align.LevelFixVal

ωF : LF
ωF = lim natF

Ωlimᵀ : Raw ωF
Ωlimᵀ = G.lim (λ n → G.em n G.top)

no-Lgl-Ωlim : Lgl ωF Ωlimᵀ → ⊥
no-Lgl-Ωlim (st , w) with st 0
... | inj₁ ()
... | inj₂ (() , _)

Ω₁+3 : LF
Ω₁+3 = suc (suc (suc Ω₁))

no-cp₀ : CP Ω₁+3 (suc zero) → ⊥
no-cp₀ (suc ())

no-cp₁ : CP Ω₁+3 Ω₁ → ⊥
no-cp₁ (fst p) = no-cp₀ p

no-cp-Ω3-Ω2 : CP Ω₁+3 Ω₁·2 → ⊥
no-cp-Ω3-Ω2 (fst (suc p)) = no-cp₁ p
```

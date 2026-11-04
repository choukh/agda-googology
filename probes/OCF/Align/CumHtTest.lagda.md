# 序数高度的世界: 有限测试

> 入口 [CumHt](CumHt.lagda.md). **有限测试, 不是证明.** 比较器 `refl`, 只看头部形状和小参数上的 FGH 值. 盲区: `FGH-1` 式的现象 (参数 0, 1 上一切 `HS` 树的值相同), 形状不看后面的项, 不看界, 不区分强度. 这里不读记号.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHtTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level using (FGH)
import OCF.Free.Level as FL
open import OCF.Align.CumHtBase using (Ord₀)
open import OCF.Align.LadderOrdCode using (ωᶜ; ω²ᶜ)
open import OCF.Align.CumHt

data Sh : Set where
  sz ss sl : Sh

sh : Ord₀ → Sh
sh FL.zero    = sz
sh (FL.suc _) = ss
sh (FL.lim _) = sl
sh (FL.limᵢ () _)
sh (FL.up () _)

-- 第 n 项的头部
at : Ord₀ → ℕ → Ord₀
at (FL.lim f) n = f n
at x n = x

-- 形状指纹: 深度 d, 宽度 w, 只读形状
data Fp : Set where
  stop fz′ : Fp
  fs′ : Fp → Fp
  fl′ : List Fp → Fp

take : ∀ {X : Set} → ℕ → (ℕ → X) → List X
take zero f = []
take (suc w) f = f 0 ∷ take w (λ n → f (suc n))

fp : ℕ → ℕ → Ord₀ → Fp
fp zero w x = stop
fp (suc d) w FL.zero = fz′
fp (suc d) w (FL.suc x) = fs′ (fp d w x)
fp (suc d) w (FL.lim f) = fl′ (take w (λ n → fp d w (f n)))
fp (suc d) w (FL.limᵢ () f)
fp (suc d) w (FL.up () x)

eqF : Fp → Fp → Bool
eqL : List Fp → List Fp → Bool
eqF stop stop = true
eqF fz′ fz′ = true
eqF (fs′ a) (fs′ b) = eqF a b
eqF (fl′ a) (fl′ b) = eqL a b
eqF _ _ = false
eqL [] [] = true
eqL (a ∷ x) (b ∷ y) = eqF a b ∧ eqL x y
eqL _ _ = false

same : ℕ → ℕ → Ord₀ → Ord₀ → Bool
same d w x y = eqF (fp d w x) (fp d w y)

t₁ : sh (Cum.T² 0) ≡ sl
t₁ = refl

t₂ : sh Cum.T²⁺¹ ≡ sl
t₂ = refl

t₃ : sh Tω ≡ sl
t₃ = refl

t₄ : sh Tω² ≡ sl
t₄ = refl

t₅ : sh (at (Cum.T² 0) 1) ≡ sl
t₅ = refl

t₆ : sh (at Cum.T²⁺¹ 1) ≡ sl
t₆ = refl

f₀ : fgh² 0 ≡ 1
f₀ = refl

f₁ : fgh²⁺¹ 0 ≡ 1
f₁ = refl

f₂ : fgh²ω 0 ≡ 1
f₂ = refl


-- 累加与不读输出的链: 深度 6 才分开
c₀ : same 5 2 (Cum.T² 0) (Ctl.T² 0) ≡ true
c₀ = refl

c₁ : same 6 2 (Cum.T² 0) (Ctl.T² 0) ≡ false
c₁ = refl

-- Ω² 与 Ω·ω 在深度 3 上已经不同
c₂ : same 3 2 (Cum.T² 0) Tω ≡ false
c₂ = refl

-- Ω² 与 Ω²+1: 深度 5 分开
c₃ : same 4 2 (Cum.T² 0) Cum.T²⁺¹ ≡ true
c₃ = refl

c₄ : same 5 2 (Cum.T² 0) Cum.T²⁺¹ ≡ false
c₄ = refl

-- Ω² 与 Ω²·2: 深度 5 分开
c₅ : same 4 2 (Cum.T² 0) (Cum.T² 1) ≡ true
c₅ = refl

c₆ : same 5 2 (Cum.T² 0) (Cum.T² 1) ≡ false
c₆ = refl

-- Ω·ω 与 Ω·ω²: 深度 5 分开
c₇ : same 4 2 Tω Tω² ≡ true
c₇ = refl

c₈ : same 5 2 Tω Tω² ≡ false
c₈ = refl
```

**没有结果的计算 (计时观察, 不是值, 也不是否定).** `FGH Tω 1 ≡ 2` 的 `refl` 18 秒没有结果, `fgh² 1 ≡ 2` 的 `refl` 45 秒没有结果. 所以这里的 FGH 只有参数 0 上的值, 它不区分任何树.

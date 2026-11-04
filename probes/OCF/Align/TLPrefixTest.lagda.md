# 前缀 (四): 基本列的毛刺, 有限测试

> 入口 [TLPrefix](TLPrefix.lagda.md). **有限测试, 不是证明.** 比较器 `same d w` ([CumUpAcceptF](CumUpAcceptF.lagda.md)): 深度 $d$, 宽度 $w$, 只读形状. 盲区: 不读第 $w$ 项以后, 不读深度 $d$ 以下, 不读值. `false` 说明两棵树在这个范围内形状不同; 不说明值不同 (值相同是定理 `TᵖΩ≈T⁰`).
>
> | 对象 | 结果 |
> | --- | --- |
> | 第 0 项, `TᵖΩ` 对 `T⁰` | 到 `same 6 2` 相同; 定理: 第 0 项就是 $\gamma_1$ (`Run` 的前提 `E₀`) |
> | 第 1 项, `TᵖΩ` 对 `T⁰` | `same 3 2` 相同, `same 4 2` 不同. **第一个毛刺在第 1 项, 深度 4** |
> | 第 1 项, `Tᶜ` 对 `T⁰` | `same 3 2` 相同, `same 4 2` 不同. 这个比较器分不开两种前缀的位置 |
> | 第 1 项, `TᵖΩ` 对 `Tᶜ` | `same 4 2` 相同, `same 6 2` 不同. 确实是两棵树 |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLPrefixTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Free.Level as FL
open import OCF.Align.CumUpAcceptF using (same)
open import OCF.Align.CumReadCF using (azero; z⊲)
open import OCF.Align.NoCumLit using (Ord₀)
open import OCF.Align.NoCumW using (one; g₀)
open import OCF.Align.NoCumPre using (Tᵖ)
open import OCF.Align.NoCumOmega using (T⁰)
open import OCF.Align.CumReadTop using (Tᶜ)

P : Ord₀
P = Tᵖ 1 azero one g₀ (z⊲ one)

pick : Ord₀ → ℕ → Ord₀
pick (FL.lim f) n = f n
pick x n = x

_ : same 6 2 (pick P 0) (pick T⁰ 0) ≡ true
_ = refl

_ : same 3 2 (pick P 1) (pick T⁰ 1) ≡ true
_ = refl

_ : same 4 2 (pick P 1) (pick T⁰ 1) ≡ false
_ = refl

_ : same 3 2 (pick Tᶜ 1) (pick T⁰ 1) ≡ true
_ = refl

_ : same 4 2 (pick Tᶜ 1) (pick T⁰ 1) ≡ false
_ = refl

_ : same 4 2 (pick P 1) (pick Tᶜ 1) ≡ true
_ = refl

_ : same 6 2 (pick P 1) (pick Tᶜ 1) ≡ false
_ = refl
```

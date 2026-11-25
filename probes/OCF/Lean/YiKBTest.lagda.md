# YiKB 形状测试: 设计怎样沿龙骨

> 有限测试 (`refl`), 不是定理; 只导入标准库与 YiKB. 展示: 塔层号的形状, 层的顶, 塔闭项的对角列, Λ 的闭项是塔闭项的极限, 以及 "Ω_Ω 当层号" 展开成按可数树 `y` 分支的 Ω_{Ω_y}.
> 这些等式只说明项的形状; 值有多大, 测试不回答 (值的判断见回报).
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKBTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiKBBlock
open import OCF.Lean.YiKBFold
```

塔: 第 n+1 层是以第 n 层为基底与下标层的 Ω 结点; 它的树在基底上的分支域是第 n 层的树.

```agda
_ : tw 1 ≡ sp z iΩ lev (lv↘ rf′)
_ = refl

_ : tw 2 ≡ sp (tw 1) iΩ lev (lv↘ rf′)
_ = refl

_ : Dom (tw 2) top ≡ T (tw 1)
_ = refl

_ : Dom (tw 2) (low top) ≡ T z
_ = refl

_ : lev {b = z} (suc (suc zero)) ≡ s (s z)
_ = refl
```

层的顶与闭项: 第 n+1 层的顶是 `c ↦ Ωtop (lev c)` 的 Ω 分支; 塔第 1 项是对角列 x ↦ 2 ⊔ ψ₀(Ω_x) 的极限, 从 1 起.

```agda
_ : Ωtop (tw 1) ≡ br top (λ c → lf (pk c (Ωtop (lev c))))
_ = refl

_ : twᶜ 0 ≡ suc zero
_ = refl

_ : twᶜ 1 ≡ lim (λ n → iter (λ x → join (suc (suc zero)) (down (lev x) (lv↘ rf′ x) (Ωtop (lev x)))) n (suc zero))
_ = refl

_ : twᶜ 2 ≡ down (tw 1) (sb rf)
      (lim (λ n → iter (λ c → join (suc (Ωtop (tw 1))) (down (lev c) (lv↘ rf′ c) (Ωtop (lev c)))) n (Ωtop (tw 1))))
_ = refl

_ : EBOᶜ ≡ lim (λ n → join (suc (suc zero)) (twᶜ n))
_ = refl
```

第 2 项对角列的第一个孩子是 Ω_Ω (`Ωtop (tw 1)`). 它当层号时展开成按可数树 `y` 分支的上确界, 第 `y` 个孩子是 "Ω_y 当层号" (基底是 `lev y`), 路径经 `ch y` 回到第 1 层; 它的顶坍缩到第 1 层后仍是按 `y` 的分支, 第 `y` 支是孩子 `y` 里的坍缩.

```agda
_ : lev (Ωtop (tw 1)) ≡
    sp (tw 1) (iP top) (λ y → lev (Ωtop (lev y))) (λ y → ch y (lv↘ rf′ (Ωtop (lev y))))
_ = refl

_ : down (lev (Ωtop (tw 1))) (sb rf) (Ωtop (lev (Ωtop (tw 1)))) ≡
    br top (λ y → join (suc (Ωtop (tw 1)))
      (lf (pk y (down (lev (Ωtop (lev y))) (lv↘ rf′ (Ωtop (lev y))) (Ωtop (lev (Ωtop (lev y))))))))
_ = refl
```

上确界结点上方一层: 顶坍缩一步的对角列从 `Ωtop` 起, 每步是 `E`; `E` 在上确界结点的叶上只记后继 (诊断 `YiKBProps.restart` 的来源).

```agda
_ : ∀ (x : ℕ) (t : T (lev {b = z} (suc zero))) (acc : T (sp z iℕ (λ n → lev {b = z} (suc zero)) (λ n → ss rf))) →
    E rf′ acc (lf (pk x t)) ≡ suc acc
_ = λ x t acc → refl
```

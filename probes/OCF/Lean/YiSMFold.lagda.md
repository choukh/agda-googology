# 主线候选: 兄弟孩子的折叠与闭项

> 主线候选（作者 2026-11-14 定兄弟孩子），未进 src. 折叠就是 [YiRBSib](YiRBSib.lagda.md) 的折叠, 原样重导出, 一行不改; 这里只补 Λ 上的证据 `rb-Λ` 与两个闭项 `twˢ`, `EBOˢ`.
> 不否定什么. 值的搬运在 [YiSMValue](YiSMValue.lagda.md) (塔各项, 终点 ≥ BTBO) 与 [YiSMEnd](YiSMEnd.lagda.md) (终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSMFold where

open import Data.Nat using (ℕ; zero)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRBSib public
```

## 闭项

Λ 的证据: ℕ 极限形状不带证据, 孩子是塔各项的证据 `rb-tw`.

```agda
rb-Λ : Rb Λ
rb-Λ = tt , rb-tw

twˢ : ℕ → Tr zero
twˢ n = proj₁ (ψ₀ʳ (tw n) (Ok-tw n) (rb-tw n) (proj₁ (Ωt (tw n))))

EBOˢ : Tr zero
EBOˢ = proj₁ (ψ₀ʳ Λ Ok-Λ rb-Λ (proj₁ (Ωt Λ)))
```

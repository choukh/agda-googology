# 塔第 2 项 (一): 塔逐项是第一位置序的一步, BTBO 下界上传

> 验收文件. 判决: 编译定理, 无前提. `row0` (`refl`): 塔第 n+1 项的结点折叠的第 0 行就是塔第 n 项 (孩子下标是零, 孩子的底, 证据, 路线都化简回标准的); 所以 `tw-step : zero ⊢ twᶜ n ◃ twᶜ (suc n)`.
> 值: `btbo-tw : ∀ n → D.BTBOᴵ ≼ read (twᶜ (suc n))`, 特别 `btbo-tw2`: 塔第 2 项不低于 ψ₀(Ω_Ω) (只是下界, 经第 0 行, 不经 `YiMEStep.row 1`).
> 不给出什么: 高于 ψ₀(Ω_Ω) 的界不在这里; 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiT2Mono where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (Ev-tw; Rt-tw)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; ◃⊑)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Align.Value using (_≼_; ≼-trans; ⊑→≼)
open import OCF.Align.YiBtValBT using (module D)
```

## 第 0 行

塔第 n+1 项的层号是 `Ωₗ (tw n) (λ c → tw n ⊕ ↑ (tw n) c)`; 它的 Ω 树在分支 c 上是 `up zero c (Ωt (tw n ⊕ ↑ (tw n) c))`. 链从零出发, 第 0 行落在层号 `tw n ⊕ zero`, 即 `tw n` 上.

```agda
G⁺ : (n : ℕ) → Tr (tw n) → Tr (tw (suc n))
G⁺ n c = up zero c (Ωt (tw n ⊕ ↑ (tw n) c)) (Ωt-nz (tw n ⊕ ↑ (tw n) c))

row0 : (n : ℕ) → ψ⊥ (tw (suc n)) (Ev-tw (suc n)) (Rt-tw (suc n)) (B₀ (tw (suc n))) (G⁺ n zero) ≡ twᶜ n
row0 n = refl

tw-step : (n : ℕ) → zero ⊢ twᶜ n ◃ twᶜ (suc n)
tw-step n = ◃l zero

tw≼ : (n : ℕ) → read (twᶜ n) ≼ read (twᶜ (suc n))
tw≼ n = ⊑→≼ (read (twᶜ n)) (◃⊑ (tw-step n))
```

## BTBO 下界上传

```agda
btbo-tw : (n : ℕ) → D.BTBOᴵ ≼ read (twᶜ (suc n))
btbo-tw zero    = btbo-tw1
btbo-tw (suc n) = ≼-trans (btbo-tw n) (tw≼ (suc n))

btbo-tw2 : D.BTBOᴵ ≼ read (twᶜ 2)
btbo-tw2 = btbo-tw 1
```

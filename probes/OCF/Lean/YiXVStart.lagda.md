# YiXV：最小实例与第一个未证上界
> 验收文件。编译定理：回灌点 0、1 的形状及上界，第 0 行上界，第 1 行的极限展开；没有塔第 1 项的上界。
> `Goal`、`Goalᶻ`、`Need1` 仅为待证命题的类型，不是它们的证明。`Need1` 尚未实填。
> 上界引用 `YiCeilRead.next≼`、`ε₀-upper`；链与读回直接用 `YiLSTw1`，不重定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVStart where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (Ev; Rt)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; next≽)
open import OCF.Lean.YiLSTw1 using (h₁; εh; ρh; G; pt)
open import OCF.Lean.YiCeilRead using (𝟏; ωx; next≼; ε₀-upper)
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiMTTab using (twᶻ)
open import OCF.Align.YiBtValBT using (module D)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; z≼; ≼l; ≼-refl)

Goal : Set
Goal = read (twᶜ 1) ≼ D.BTBOᴵ

Goalᶻ : Set
Goalᶻ = readRW (twᶻ 1) ≼ D.BTBOᴵ

point0 : pt 0 ≡ zero
point0 = refl

point1 : pt 1 ≡ next (suc zero) ◃s
point1 = refl

point1-value : (read (pt 1) ≼ ωx 𝟏) × (ωx 𝟏 ≼ read (pt 1))
point1-value = next≼ (suc zero) ◃s (≼-refl 𝟏) , next≽ (suc zero) ◃s (≼-refl 𝟏)

row0-form : G (pt 0) ≡ pt 1
row0-form = refl

point0-upper : read (pt 0) ≼ D.γ 0
point0-upper = z≼

point1-upper : read (pt 1) ≼ D.γ 1
point1-upper = ≼l 0 (next≼ (suc zero) ◃s (≼-refl (O.suc O.zero)))

row0-upper : read (G (pt 0)) ≼ D.γ 1
row0-upper = ≼l 0 (next≼ (suc zero) ◃s (≼-refl (O.suc O.zero)))

Need1 : Set
Need1 = read (G (pt 1)) ≼ D.γ 2
```

第 1 行是各有限层前缀的极限；层号 2 的调用使用的底，其第 0 分量已是层号 1 的 Ω 树折叠。

```agda
fg : ℕ → L
fg n = zero ⊕ ↑ zero (iter ((suc zero) +_) (suc zero) n)

level1 : h₁ (pt 1) ≡ lim fg
level1 = refl

e1 : Ev (lim fg)
e1 = εh (pt 1)

r1 : Rt (lim fg)
r1 = ρh (pt 1)

pre : ℕ → Tr zero
pre n = ψ₀ (lim fg) e1 r1 (cumΩ fg n)

row1-form : G (pt 1) ≡ lim pre
  (λ n → mono⊥ (lim fg) e1 r1 (B₀ (lim fg))
    (◃u (cumΩ fg n) (suc n) (Ωt (fg (suc n))) (Ωt-nz (fg (suc n)))))
row1-form = refl

pre0-form : pre 0 ≡ G (suc zero)
pre0-form = refl

pre0-upper : read (pre 0) ≼ D.γ 1
pre0-upper = ε₀-upper

B2 : Base (suc (suc zero))
B2 = dL fg e1 r1 (B₀ (lim fg)) 1 (cumΩ fg 0)

pre1-form : pre 1 ≡ ψ⊥ (suc (suc zero)) tt tt B2 (Ωt (suc (suc zero)))
pre1-form = refl

base2-form : b⊥ B2 ≡ G (suc zero)
base2-form = refl
```

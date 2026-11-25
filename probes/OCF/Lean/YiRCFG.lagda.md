# 验收 (FGH 式折叠 `Φ`, `YiFGFold`): 塔第 1 项上目标第 2 层的那一支, 形状

> 验收文件, 不进成品; 树、折叠、合法性一行不改. 判据 `YiRBCrit.CritAt gᶠ n` 的否定在 [YiRCNeg](YiRCNeg.lagda.md) (`fg-neg`); 保持引理没有搬.
> 编译定理, 无前提 (`refl`): 整棵 Ω 树朝第 2 层的折叠是保留的结点, 各支是 `gᶠ` (`wholeᶠ`); 那一支对一切 c 逐字是 "第 2 层的 Ω 树的后继, 加上孩子 c 的 Ω 树折到第 0 层再嵌回" (`fg-shape`); 与主线原行 (`YiRBCrit.main-shape`) 对照: 起点多一个后继, 回退项是 `Φ` 的; 这一行对一切底、起点与左项的式子是 `fg-row`.
> `YiFGFold` 在 Ω 形状层号经指定孩子的那一行照抄主线 (`YiFGCheck.M-row`), 所以这里没有新的一行. 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRCFG where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiFGFold
open import OCF.Lean.YiRBCrit using (two; h₁; blk; CritAt)
open import OCF.Lean.YiCLFam using (nat)
```

## 那一支

```agda
gᶠ : Tr zero → Tr⁺ two
gᶠ c = Φ (tw 1) (Ok-tw 1) (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (blk c)

CritF : ℕ → Set
CritF = CritAt gᶠ

wholeᶠ : Σ (Pos two) λ q → Σ (Br two q → Tr zero) λ cv →
  proj₁ (Φ (tw 1) (Ok-tw 1) (B₀ (tw 1)) two (inc (nat 2) self) (Ωt two) (proj₁ (Ωt (tw 1))))
  ≡ Ω q (λ z → proj₁ (gᶠ (cv z)))
wholeᶠ = _ , _ , refl

fg-shape : (c : Tr zero)
  → proj₁ (gᶠ c) ≡ suc (proj₁ (Ωt two)) + ι two (proj₁ (ψ₀ᶠ (h₁ c) (proj₂ (Ok-tw 1) c) (proj₁ (Ωt (h₁ c)))))
fg-shape c = refl
```

对一切底, 起点, 目标路径与左项 x, 这一行是 "x 的折叠 ⊞ 孩子树折到第 0 层" (与 `YiFGCheck.M-row` 同一事实, 这里对目标第 2 层逐字写出).

```agda
fg-row : (B : Base (tw 1)) (c′ : Tr zero) (v : two ≤ h₁ c′) (β : Tr⁺ two) (x : Tr (tw 1)) (c : Tr zero) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
  → Φ (tw 1) (Ok-tw 1) B two (inc c′ v) β (up x c y e)
  ≡ Φ (tw 1) (Ok-tw 1) B two (inc c′ v) β x ⊞ ψ₀ᶠ (h₁ c) (proj₂ (Ok-tw 1) c) y
fg-row B c′ v β x c y e = refl
```

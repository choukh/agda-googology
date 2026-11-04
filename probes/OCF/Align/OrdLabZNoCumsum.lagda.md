# NoCumsum (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [NoCumsum](NoCumsum.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZNoCumsum where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZDiagonal using (module Diagonal)
open import OCF.Align.OrdLabZUniform using (Uniform)
```

## §1 闭合的对角线

```agda
module D = Diagonal Uniform

γ : ℕ → Ordᶜ zero
γ = D.γ

cert : ∀ n → HS (γ n)
cert = D.cert

BTBOᴵ : Ordᶜ zero
BTBOᴵ = D.BTBOᴵ
```

## §4 结论与边界

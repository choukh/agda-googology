# 抽象理论 (七): 四条结构律不充分 (加法模型)

> 判决: 编译定理, 无前提, 只导入 `YiAbsFrame`. 框架里有一个实例 (`blk⁺`, `fold⁺`: 一个层号, 树是 ℕ, 嵌入是加法, 折叠是 β + x), 在每个层号上满足 `Hand`, `HandU`, 并满足 `Mono`, `Pres` (`add-model`).
> 读法: 只由这四条律 (嵌入一致, 一致目标的交接, 单调, 保持合法) 推不出超过加法的值; 值的下界要用到结点行的链与自身行这两类行律.
> 不否定什么: 不涉及具体块; 具体接口里另有 `kstep`, `self-up`, 这里没有它们.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsAdd where

open import Data.Nat using (ℕ; _+_; _<_)
open import Data.Nat.Properties using (+-assoc; +-monoʳ-<)
open import Data.Bool using (false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import OCF.Lean.YiAbsFrame

blk⁺ : Block
blk⁺ = record
  { Lv = ⊤ ; Tr = λ _ → ℕ ; Ch = λ _ → ⊤ ; chL = λ _ _ → tt ; ChT = λ _ _ → ℕ ; chT = λ _ _ y → y
  ; _⊑_ = λ _ _ → ⊤ ; self = tt ; inc = λ _ _ _ → tt ; incU = λ _ _ _ → tt
  ; up = λ x _ y → x + y ; hd = λ _ → false ; _◃_ = _<_ ; Leg = λ _ → ⊤ }

fold⁺ : Fold blk⁺
fold⁺ = record
  { Bs = λ _ → ⊤ ; LegB = λ _ _ → ⊤ ; Bt = λ _ → ℕ ; LegT = λ _ _ → ⊤
  ; ψ = λ _ _ _ _ β x → β + x ; ψβ = λ _ _ _ _ β x → β + x ; dn = λ _ _ _ _ → tt }

open Fold fold⁺

add-model : ((ℓ : ⊤) → Hand ℓ) × ((ℓ : ⊤) → HandU ℓ) × Mono × Pres
add-model = (λ ℓ b j c w β x y → sym (+-assoc β x y))
          , (λ ℓ b j c₁ ws β x c y → sym (+-assoc β x y))
          , (λ ℓ b j w β d → +-monoʳ-< β d)
          , (λ ℓ b lb j w β lβ x lx → tt)

add-only : (β x : ℕ) → ψ tt tt tt tt β x ≡ β + x
add-only β x = refl
```

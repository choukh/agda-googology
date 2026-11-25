# 换基那一格把替身的谓词交给整行

> 判决: 编译定理, 无前提, 不读记号. 塔第 1 项上朝非零孩子 d 的层折嵌入 `up x c y e` (换基折叠 `YiBSFold`): 对 `◃` 向上封闭的谓词 Q 在替身 `seen` 上成立, 就在整行的输出上成立 (`cell`); 陈述里替身不含原材料 y.
> 不给出什么: 不构造 Q; 原材料 y 的值只经第 0 层尾项进入, 这里没有关于它的定理.
> 来源: 行的形状是 `YiRKCell.w3`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSVCell where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiVALeaf using (NZ)
open import OCF.Lean.YiBSBase using (seen; rb-tw)
import OCF.Lean.YiBSFold as BS
open import OCF.Lean.YiRKCell using (w3)
open import OCF.Lean.YiSVMono

cell : ∀ {d} (nz : NZ d) (o : Ok (tw 1)) (Q : Tr (h₁ d) → Set) → (∀ {x y} → Q x → h₁ d ⊢ x ◃ y → Q y)
     → ∀ c (B : Base (tw 1)) (β : Tr⁺ (h₁ d)) (x : Tr (tw 1)) (y : Tr (h₁ c)) (e : h₁ c ⊢ zero ◃ y)
     → Q (proj₁ (seen Sᶻ (h₁ d) (proj₂ o d) (lift zero (↑ zero d)) (BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β x) c))
     → Q (proj₁ (BS.ψ (tw 1) o (rb-tw 1) B (h₁ d) (inc d self) β (up x c y e)))
cell {d} nz o Q Q↑ c B β x y e q =
  subst (λ z → Q (proj₁ z)) (sym (w3 nz c o B β x y e)) (go (+⊴ _ _))
  where
  go : ∀ {z} → _ ⊴ z → Q z
  go ⊴r     = q
  go (⊴◃ d′) = Q↑ q d′
```

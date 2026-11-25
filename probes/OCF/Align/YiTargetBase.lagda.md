# 目标来源诊断的共同接口

第 4 层。AllTags P a 表示 a 中每个正参数 ψ 的目标下标满足 P。
空参数 Ω 的下标本身不作为目标，但继续递归检查它内部已有的正 ψ。
这区别于泛取所有子项；γ 真正新造的正 ψ 头只有该链的共尾层 ν。
本篇仅固定语法不变量，不写树侧 ψ 或修改旧定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiTargetBase where

open import Data.Unit.Base using (⊤; tt)
open import Data.Product.Base using (_×_; _,_)
open import Data.List.Base using ([]; _∷_)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt)

HeadOK : (T → Set) → T → T → Set
HeadOK P u [] = ⊤
HeadOK P u (_ ∷ _) = P u

AllTags : (T → Set) → T → Set
AllTags P [] = ⊤
AllTags P (ψ u b ∷ xs) =
  HeadOK P u b × AllTags P u × AllTags P b × AllTags P xs

head-from : ∀ {P u} → P u → ∀ b → HeadOK P u b
head-from p [] = tt
head-from p (_ ∷ _) = p

singleton : ∀ {P u b} → HeadOK P u b → AllTags P u → AllTags P b →
  AllTags P (ψ u b ∷ [])
singleton h u b = h , u , b , tt

omega : ∀ {P u} → AllTags P u → AllTags P (Ωt u)
omega u = tt , u , tt , tt

head-map : ∀ {P Q u b} → (∀ {v} → P v → Q v) → HeadOK P u b → HeadOK Q u b
head-map {b = []} f h = tt
head-map {b = _ ∷ _} f h = f h

tags-map : ∀ {P Q} → (∀ {v} → P v → Q v) → ∀ a → AllTags P a → AllTags Q a
tags-map f [] h = tt
tags-map f (ψ u b ∷ xs) (h , tu , tb , ts) =
  head-map {u = u} {b = b} f h , tags-map f u tu , tags-map f b tb , tags-map f xs ts
```

P 可以是当前有限历史环境的成员关系。它不是树的合法性，
也不要求给原始树补码、比较裸层号或携带任何记号到乙的定义中。

# 全域证据的可满足实例（验收玩具块）
编译定理：三元素有限链实填全域证据、结点共现覆盖及弱口径 `Notation`，ψ 取常零。
标准库有限链比较器给出答案；接口前提已先在临时文件实填。反例另见 `YiTDDiamond`。
不把该有限链赋予主线强度；不声称有限编码或良基能由派发接口推出。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTDModels where

open import Data.Fin.Base using (Fin; zero)
import Data.Fin.Base as Fin
import Data.Fin.Properties as FP
open import Data.Bool.Base using (Bool; false; true)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiTDIface
import OCF.Lean.YiTDOrder as O

A₃ : Set
A₃ = Fin 3

_<₃_ : A₃ → A₃ → Set
_<₃_ = Fin._<_

frame₃ : Frame
frame₃ = record
  { A = A₃
  ; _<_ = _<₃_
  ; trans = FP.<-trans
  ; irrefl = FP.<-irrefl refl }

open On frame₃
module T = O.Theorems frame₃

full : Evidence Global
full = record
  { E = Answer
  ; answer = λ _ _ e → e
  ; provide = λ x y _ → T.tri→answer (FP.<-cmp x y) }

ψ₃ : A₃ → A₃
ψ₃ _ = zero

notation₃ : Notation
notation₃ = T.global→notation ψ₃ full

label₃ : A₃ × A₃ → Bool → A₃
label₃ (x , y) false = x
label₃ (x , y) true = y

nodes₃ : Nodes
nodes₃ = record { Node = A₃ × A₃; Child = λ _ → Bool; label = label₃ }

cover₃ : Covers nodes₃
cover₃ x y = (x , y) , false , true , refl , refl

local₃ : Evidence (Scope nodes₃)
local₃ = record
  { E = Answer
  ; answer = λ _ _ e → e
  ; provide = λ x y _ → Evidence.provide full x y tt }

covered₃ : Notation
covered₃ = T.covered→notation ψ₃ nodes₃ local₃ cover₃
```

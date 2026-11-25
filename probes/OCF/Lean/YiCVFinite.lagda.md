# 两个真实层号上的弱口径 Notation（验收文件）
编译定理：把字母表限为 YiCVHits 的两个真实层号，补等号后可实填原 Covers 并得到 Notation。
序是两层号原字面路径的严格部分，一元算子取常零；不是主线折叠的实现。
这说明“有 nothing”不能独自否定弱口径 Notation；全 L 的结论见 YiCVDomain.no-notation。
有限子域不提供主线强度，不把常零算子认作折叠，也不据此判断记号依赖。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCVFinite where

open import Data.Empty using (⊥)
open import Data.Bool.Base using (Bool; false; true)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_,_) 
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiTDIface as I
import OCF.Lean.YiTDOrder as Order
import OCF.Lean.YiCVDomain as D
import OCF.Lean.YiCVHits as H
open import OCF.Lean.YiRWBlock using (L)
open import OCF.Lean.YiRWPath using (z≤)

label : Bool → L
label = H.real-label

_<₂_ : Bool → Bool → Set
x <₂ y = label x D.≺ label y

frame₂ : I.Frame
frame₂ = record
  { A = Bool
  ; _<_ = _<₂_
  ; trans = D.trans≺
  ; irrefl = I.Frame.irrefl D.frame }

open I.On frame₂

label-injective : ∀ {c d} → label c ≡ label d → c ≡ d
label-injective {c = false} {d = false} _ = refl
label-injective {c = false} {d = true} ()
label-injective {c = true} {d = false} ()
label-injective {c = true} {d = true} _ = refl

nodes₂ : Nodes
nodes₂ = record { Node = ⊤; Child = λ _ → Bool; label = λ _ c → c }

cover₂ : Covers nodes₂
cover₂ x y = tt , x , y , refl , refl

answer₂ : ∀ x y → Answer x y
answer₂ false false = inj₂ (inj₁ refl)
answer₂ false true = inj₁ (z≤ (label true) , D.no-nd-zero)
answer₂ true false = inj₂ (inj₂ (z≤ (label true) , D.no-nd-zero))
answer₂ true true = inj₂ (inj₁ refl)

completion₂ : ∀ t c d → (c ≡ d) ⊎ H.Present (H.real-table t c d)
completion₂ t false false = inj₁ refl
completion₂ t false true = inj₂ (H.real-entry t)
completion₂ t true false = inj₂ (H.real-entry-back t)
completion₂ t true true = inj₁ refl

evidence₂ : ∀ t → Evidence (Scope nodes₂)
evidence₂ t = record
  { E = λ x y → (x ≡ y) ⊎ H.Present (H.real-table t x y)
  ; answer = λ x y _ → answer₂ x y
  ; provide = λ x y _ → completion₂ t x y }

ψ₂ : Bool → Bool
ψ₂ _ = false

notation₂ : H.Table → Notation
notation₂ t = Order.Theorems.covered→notation frame₂ ψ₂ nodes₂ (evidence₂ t) cover₂
```

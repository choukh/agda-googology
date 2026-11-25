# 原 Retains 在指定实际格上的适用域
验收文件；编译定理：first2/first3 的路径前提有实例，但局部目标层不等于零。
原 YiFOValue.Row.Retains 只在目标零层定义，故尚不能在这两格陈述原值比较；没有掉值结论。
来源：YiFOCells.first2/first3 的逐字踪迹，P₂ᶻ 的目标层与格坐标；不改树、折叠或合法性。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRTScope where
open import Data.Nat using (zero)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
import OCF.Lean.YiMTHit as H
import OCF.Lean.YiFOCells as C

local-target : L
local-target = tw 1 ⊕ ↑ (tw 1) H.b₁

local-target≢zero : local-target ≡ zero → ⊥
local-target≢zero ()

site≢zero : ∀ k h j c′ c m → H.P₂ᶻ k h j c′ c m → j ≡ zero → ⊥
site≢zero k h j c′ c m p q =
  local-target≢zero (trans (sym (proj₁ (proj₂ p))) q)

zero-grid-path : ∀ k (h : Tr k → L) → h zero ≤ h zero
zero-grid-path k h = self

Actual : H.Site
Actual k h j c′ c m = H.P₂ᶻ k h j c′ c m ×
  (h c ≤ h c′) × (j ≡ zero → ⊥)

first2 : H.HitTw Actual 2
first2 = 1 , inj₂ (zero , (1 , (zero , (0 , inj₂
  ((refl , refl , refl , refl , H.is₁ self) , self , local-target≢zero)))))

first3 : H.HitTw Actual 3
first3 = H.step Actual 2 first2

OriginalDomain : H.Site
OriginalDomain k h j c′ c m = H.P₂ᶻ k h j c′ c m × (j ≡ zero)

no-original-domain : ∀ k h j c′ c m → OriginalDomain k h j c′ c m → ⊥
no-original-domain k h j c′ c m (p , q) = site≢zero k h j c′ c m p q
```

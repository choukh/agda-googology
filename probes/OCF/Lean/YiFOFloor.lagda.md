# 字面地板证据上的局部补表原型
不读记号；ZeroFloor 给每个孩子一条从零孩子层出发的字面路径，patch 只填有一个零孩子的格。
来源：YiCWTable 的根表规则，推广到显式携带地板证据的孩子族；规范龙骨逐层实例化。
候选闭项合法；没有读回孩子的地板保持定理，也没有新增值界，不替换主线。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFOFloor where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; RbS; ψ)
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiCWTable as CW
record ZeroFloor (k : L) (h : Tr k → L) : Set where
  constructor floor
  field floor-path : (c : Tr k) → h zero ≤ h c
open ZeroFloor
patch : ∀ k h → ZeroFloor k h → RbS (sΩ k) h → RbS (sΩ k) h
patch k h f old zero zero = just (inj₁ self)
patch k h f old zero c′ = just (inj₂ (floor-path f c′))
patch k h f old c zero = just (inj₁ (floor-path f c))
patch k h f old c c′ = old c c′
keel-floor : ∀ n → ZeroFloor (tw n) (CW.hᵗ n)
keel-floor n = floor (λ c → lift (tw n) (↑ (tw n) c))
patched : (n : ℕ) → Rb (tw n)
patched zero = MT.rbᶻ zero
patched (suc n) = patch (tw n) (CW.hᵗ n) (keel-floor n) (proj₁ (MT.rbᶻ (tw (suc n)))) ,
  proj₂ (MT.rbᶻ (tw (suc n)))
legal : ∀ n → zero ⊢ zero ◃ proj₁
  (ψ (tw n) (Ok-tw n) (patched n) (B₀ (tw n)) zero (z≤ (tw n)) (Ωt zero) (proj₁ (Ωt (tw n))))
legal n = proj₂ (ψ (tw n) (Ok-tw n) (patched n) (B₀ (tw n)) zero (z≤ (tw n)) (Ωt zero) (proj₁ (Ωt (tw n))))
```

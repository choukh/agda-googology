# 与固定零下标的抽象 SelfKeep 搭接
验收文件（读记号）；当前 gradedᵍ 的 cl 固定为 ψ[]，故搭接取一般定理的 ν=[]。
`self-zeroᵍ` 实填零层；任意层的搭接仍需对应框架，不把 ψν 的非零下标实例称为原 SelfKeep。
入口：`SelfAtᵍ`、`self-under-frame`、`self-zeroᵍ`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTCompat where
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiGIBlock using (Bsᵍ; ψᵍ)
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGTIndex using (zero-frame)
open import OCF.Lean.YiGTSelf using (self-pres)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiMTTab as MT
import OCF.Align.EboLeanDef as E

SelfAtᵍ : L → Set
SelfAtᵍ ℓ = (b : Bsᵍ ℓ) (β : Tr⁺ ℓ) → proj₁ (proj₂ b) ≡ MT.rbᶻ ℓ
  → ∀ {P a x} → GR.R ℓ (E.ψ [] P ∷ []) (proj₁ β) → GR.R ℓ a x
  → GR.R ℓ (E.ψ [] (P ++ a) ∷ []) (proj₁ (ψᵍ ℓ b ℓ self β x))

self-under-frame : ∀ ℓ (b : Bsᵍ ℓ) → NodeFrame ℓ (proj₁ b) ℓ self []
  → (β : Tr⁺ ℓ) → ∀ {P a x} → GR.R ℓ (E.ψ [] P ∷ []) (proj₁ β) → GR.R ℓ a x
  → GR.R ℓ (E.ψ [] (P ++ a) ∷ []) (proj₁ (ψᵍ ℓ b ℓ self β x))
self-under-frame ℓ (o , r , B) fr β {P} {a} {x} mb m = self-pres ℓ o r B [] P fr β mb {a = a} {x = x} m

self-zeroᵍ : SelfAtᵍ zero
self-zeroᵍ (o , r , B) β rb = self-under-frame zero (o , r , B) (zero-frame zero o self) β
```

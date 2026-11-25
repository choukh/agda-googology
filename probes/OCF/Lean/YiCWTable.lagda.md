# 龙骨零孩子的比较表与闭项
不读记号；新候选，不替换主线。来源：作者 V230 与 SC6 的表，闭项照 YiMTTab 仅换表。
表只对龙骨根的零孩子提供路径，孩子内部仍用 rbᶻ；合法性由原 ψ 的返回类型保证。
不声称有站值下界；先验对照见 YiCWCheck，实际底与链见 YiCWActual。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWTable where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiMTTab using (rbᶻ; twᶻ)
hᵗ : (n : ℕ) → Tr (tw n) → L
hᵗ n c = tw n ⊕ ↑ (tw n) c
tbᵗ : (n : ℕ) (c c′ : Tr (tw n)) → Maybe ((hᵗ n c′ ≤ hᵗ n c) ⊎ (hᵗ n c ≤ hᵗ n c′))
tbᵗ n zero zero = just (inj₁ self)
tbᵗ n zero c′ = just (inj₂ (lift (tw n) (↑ (tw n) c′)))
tbᵗ n c zero = just (inj₁ (lift (tw n) (↑ (tw n) c)))
tbᵗ n _ _ = nothing
rbᵗ : (n : ℕ) → Rb (tw n)
rbᵗ zero = tt
rbᵗ (suc n) = tbᵗ n , λ c → rbᶻ (hᵗ n c)
rbΛ : Rb Λ
rbΛ = tt , rbᵗ
ψ₀ᵗ : (n : ℕ) → Tr (tw n) → Tr⁺ zero
ψ₀ᵗ n = ψ (tw n) (Ok-tw n) (rbᵗ n) (B₀ (tw n)) zero (z≤ (tw n)) (Ωt zero)
tw⁺ᵗ : ℕ → Tr⁺ zero
tw⁺ᵗ n = ψ₀ᵗ n (proj₁ (Ωt (tw n)))
twᵗ : ℕ → Tr zero
twᵗ n = proj₁ (tw⁺ᵗ n)
EBO⁺ᵗ : Tr⁺ zero
EBO⁺ᵗ = ψ Λ Ok-Λ rbΛ (B₀ Λ) zero (z≤ Λ) (Ωt zero) (proj₁ (Ωt Λ))
EBOᵗ : Tr zero
EBOᵗ = proj₁ EBO⁺ᵗ
tw-legal : ∀ n → zero ⊢ zero ◃ twᵗ n
tw-legal n = proj₂ (tw⁺ᵗ n)
EBO-legal : zero ⊢ zero ◃ EBOᵗ
EBO-legal = proj₂ EBO⁺ᵗ
tw-same : ∀ n → twᵗ n ≡ twᶻ n
tw-same zero = refl
tw-same (suc n) = refl
```

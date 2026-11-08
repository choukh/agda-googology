# 读回子ambient的限制操作证书

辅助证书约束实际res⁻的全部结果，并非无条件搬运任意Sim。
规范ambient由已证原bound计算实填；up下降仅剥去同一suc/lim编号。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedProofRoute where
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.CRwBase
open import OCF.Lean.GeneralOmegaCountableObserveIf using (F)
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height)
open import OCF.Align.GeneralOmegaCountableTypedIf
open import OCF.Align.GeneralOmegaCountableTypedProofIf
open import OCF.Align.GeneralOmegaCountableTypedProofRestrict

module Route (B : Cd) (l₁ l₂ : LgB B) where
  data BackMatch {a} (σ₁ : L.Simᴵ a (height B l₁)) (κ : K (F B)) :
    L.Restr (rank B l₂ κ) a → Set where
    matched : (q₁ : rank B l₁ κ L.<ᴵ a) → σ₁ q₁ ≡ bound B l₁ κ →
      BackMatch σ₁ κ (L.restr (L.≅ᴵ-sym (rank-shape B l₁ l₂ κ)) q₁
        (L.tr (rank-shape B l₁ l₂ κ)))

  Law : ∀ {a b} → a L.≅ᴵ b → L.Simᴵ a (height B l₁) → L.Simᴵ b (height B l₂) → Set
  Law e σ₁ σ₂ = ∀ κ q → σ₂ q ≡ bound B l₂ κ → BackMatch σ₁ κ (L.res⁻ q e)

  canonical-law : Law (proof-shape B l₁ l₂) (canonical B l₁) (canonical B l₂)
  canonical-law κ .(bound B l₂ κ) refl = subst (BackMatch (canonical B l₁) κ)
    (sym (restrict-back B l₁ l₂ κ)) (matched (bound B l₁ κ) refl)

  suc-law : ∀ {a b} {e : a L.≅ᴵ b} {σ₁ : L.Simᴵ (L.suc a) (height B l₁)}
    {σ₂ : L.Simᴵ (L.suc b) (height B l₂)} → Law (L.s≅ e) σ₁ σ₂ →
    Law e (λ q → σ₁ (L.suc q)) (λ q → σ₂ (L.suc q))
  suc-law {e = e} law κ q eq with L.res⁻ q e | law κ (L.suc q) eq
  ... | L.restr e′ q′ back | matched .(L.suc q′) align = matched q′ align

  lim-law : ∀ {f g sf sg} {e : ∀ n → f n L.≅ᴵ g n}
    {σ₁ : L.Simᴵ (L.lim f sf) (height B l₁)} {σ₂ : L.Simᴵ (L.lim g sg) (height B l₂)} →
    Law (L.l≅ e) σ₁ σ₂ → ∀ n → Law (e n) (λ q → σ₁ (L.lim n q)) (λ q → σ₂ (L.lim n q))
  lim-law {e = e} law n κ q eq with L.res⁻ q (e n) | law κ (L.lim n q) eq
  ... | L.restr e′ q′ back | matched .(L.lim n q′) align = matched q′ align
```

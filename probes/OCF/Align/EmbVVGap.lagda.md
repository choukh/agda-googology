# 值验收 (见证): $\simeq$ 确实不在 $\sqsubseteq^{\mathsf I}$ 与 $\cong^{\mathsf I}$ 的范围里

> 入口 [EmbVV](EmbVV.lagda.md). 不读记号. `succ-gap`: 层号 $\mathrm{suc}\,\omega^+$ 与 $\mathrm{suc}\,\omega$ 由 $\simeq$ 相关, 但互相不 $\sqsubseteq^{\mathsf I}$ ($\omega^+$ 是去头的 $\omega$). 所以 `V-≃` 对它们的结论不能由 `Ψ⁰-mono` (`V-≼`) 得到, 主定理不是空的.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVGap where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_)
open import OCF.Free.Level hiding (z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
open import OCF.Align.EmbVVEq using (_≃ᴵ_; z≃; s≃; lh≃; ≃-reflᴵ)

ω⁺ : Ordᴵ
ω⁺ = lim (λ n → natᴵ (suc n)) (λ n → natᴵ-step (suc n))

ω-≃ : ωᴵ ≃ᴵ ω⁺
ω-≃ = lh≃ (λ n → ≃-reflᴵ (natᴵ (suc n)))

nat-pred : ∀ {c m} → c <ᴵ natᴵ m → Σ ℕ (λ j → c ≅ᴵ natᴵ j)
nat-pred {m = suc m} zero = m , ≅ᴵ-refl _
nat-pred {m = suc m} (suc q) = nat-pred q

lim≇nat : ∀ {f s} j → lim f s ≅ᴵ natᴵ j → ⊥
lim≇nat zero ()
lim≇nat (suc j) ()

ω⁺≇ω : ω⁺ ≅ᴵ ωᴵ → ⊥
ω⁺≇ω (OCF.Free.Level.l≅ h) with h 0
... | ()

¬⊑₁ : suc ω⁺ ⊑ᴵ suc ωᴵ → ⊥
¬⊑₁ (s⊑ e zero) = ω⁺≇ω e
¬⊑₁ (s⊑ e (suc (lim n q))) with nat-pred q
... | j , d = lim≇nat j (≅ᴵ-trans e d)

¬⊑₂ : suc ωᴵ ⊑ᴵ suc ω⁺ → ⊥
¬⊑₂ (s⊑ e zero) = ω⁺≇ω (≅ᴵ-sym e)
¬⊑₂ (s⊑ e (suc (lim n q))) with nat-pred q
... | j , d = lim≇nat (suc j) (lem j e d)
  where
  lem : ∀ {a} j → ωᴵ ≅ᴵ a → a ≅ᴵ natᴵ j → ωᴵ ≅ᴵ natᴵ (suc j)
  lem j e d with ≅ᴵ-trans e d
  lem zero e d | ()
  lem (suc j) e d | ()

succ-gap : (suc ωᴵ ≃ᴵ suc ω⁺) × ((suc ω⁺ ⊑ᴵ suc ωᴵ → ⊥) × (suc ωᴵ ⊑ᴵ suc ω⁺ → ⊥))
succ-gap = s≃ ω-≃ , ¬⊑₁ , ¬⊑₂
```

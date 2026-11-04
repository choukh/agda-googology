# 跨段: 编译过的否定

> 入口 [CrossM](CrossM.lagda.md). 只否定写明的陈述, 都不否定跨段路线.
>
> | 定理 | 陈述 | 只否定什么 | 前提 |
> | --- | --- | --- | --- |
> | `no-⊂⌈⌉` | $\eta\sqsubseteq\eta'$ 但 $\lceil\eta\rceil\not\subset\lceil\eta'\rceil$ | "沿 $\eta\sqsubseteq\eta'$ 的码总有上移", 所以 `gŝ` 的 `mm` 字段 (对一切 $\eta\sqsubseteq\eta'$ 单调) 不能由 `up≺` 给. 不否定别的证明 | 具体反例, 不空 |
> | `≼↛⊑` | 有带 `HS` 的 $a$, $b$, 层号 `≼`, 而 $a\sqsubseteq^0 b$ 为假 | 由 Brouwer 序得 `gc` 要的结构序 | 具体反例, 不空; 见 [CrossMNode](CrossMNode.lagda.md) |

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CrossMNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level using (Ordᴵ; lim; suc; zero; _⊑ᴵ_; natᴵ; natᴵ-step; ωᴵ; Sim→⊑ᴵ; _<ᴵ_)
open import OCF.Align.LadderOrdPos using (Code; cz; cs; cl)
open import OCF.Align.LadderOrdCode using (⌈_⌉)
open import OCF.Align.CrossMUp using (_⊂_; ⊂r; es; el)

-- ω′ = lim (1, 2, 3, ...)
ω′ᴵ : Ordᴵ
ω′ᴵ = lim (λ n → natᴵ (suc n)) (λ n → natᴵ-step (suc n))

⊑ω′ : ωᴵ ⊑ᴵ ω′ᴵ
⊑ω′ = Sim→⊑ᴵ go
  where
  go : ∀ {c} → c <ᴵ ωᴵ → c <ᴵ ω′ᴵ
  go (lim n q) = lim n (suc q)

no₀ : ∀ {C} → ⌈ ωᴵ ⌉ ⊂ C → C ≡ cz → ⊥
no₀ ⊂r ()
no₀ (es x) ()
no₀ (el x) ()

no₁ : ∀ {C} → ⌈ ωᴵ ⌉ ⊂ C → C ≡ cs cz → ⊥
no₁ ⊂r ()
no₁ (es x) refl = no₀ x refl
no₁ (el x) ()

hd : Code → Code
hd (cl g) = g 0
hd c = c

no₂ : ∀ {C} → ⌈ ωᴵ ⌉ ⊂ C → C ≡ ⌈ ω′ᴵ ⌉ → ⊥
no₂ ⊂r e with cong hd e
... | ()
no₂ (es x) ()
no₂ (el x) e = no₁ x (cong hd e)

no-⊂⌈⌉ : Σ Ordᴵ λ η → Σ Ordᴵ λ η′ → (η ⊑ᴵ η′) × (⌈ η ⌉ ⊂ ⌈ η′ ⌉ → ⊥)
no-⊂⌈⌉ = ωᴵ , ω′ᴵ , ⊑ω′ , (λ x → no₂ x refl)
```

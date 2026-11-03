# 全部 $\theta$ 的证书: 目标的推广与回到原来的 `Rel`

> 底座, 不含记号. 结论写在 [InaccTheta](InaccTheta.lagda.md). `Good-ψₖ`: 闭包定理对目标 $k$ 无条件, `Good-ψ` 对任何 `OK` 的目标 $L$ 成立: 它**不**按阶段定制. 阶段只在取证书时出现: `wf` 只管第 0, 1 层, 因为 `Aℓ` 只在参数层 0 上非空 (`¬WF-ψ₂`). `Cert₃ᴼ` 说 $\theta=3$ 的证书在原来的 `Rel (Aℓ ℓ)` 里成立.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.InaccThetaTarget where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.InaccTreeBase using (Lv; zero; suc; Ordᴸ; Ω; toLv; Tree)
open import OCF.Align.InaccFloorTree using (Sib; fin; natL; module PF)
open import OCF.Align.InaccFloorBase using (Aℓ; module Rel)
open import OCF.Align.InaccThetaRel using (module Back)
open import OCF.Align.InaccThetaMono using (module Mono)
open import OCF.Align.InaccThetaFin using (module Fin)
open import OCF.Align.Level using (Ordᴵ; _<ᴵ_; zero; suc)

module Tgt (S : Sib) (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) (B₀ : Ordᴸ zero → Set) (a⊆b : ∀ x → Aℓ ℓ zero x → B₀ x) where
  open Mono S ℓ one B₀ a⊆b

  Ti-k : ∀ n → Ti (natL (suc n))
  Ti-k n = lvt-fin (natL (suc n)) (fin-nat (suc n)) , zt-nat n , lvr-nat (suc n)

  Good-ψₖ : ∀ n {k} {x : Ordᴸ k} → GoodT k x → Eq k x x → GoodT (natL (suc n)) (ψⁿ (suc n) x)
  Good-ψₖ n {k} g e = Good-ψ (fin (suc n) refl) (okF k (suc n) refl) (Ti-k n) (Good-Ω (natL (suc n)) (lvp-nat (suc n))) g e

  Good-ψₖΩ : ∀ n θ → LvP θ → GoodT (natL (suc n)) (ψⁿ (suc n) (Ω θ))
  Good-ψₖΩ n θ p@(g , r , _) = Good-ψₖ n (Good-Ω θ p) (Ω-self θ g r)

  ¬WF-ψ₂ : WFᴬ (toLv (ψⁿ 2 {k = zero} Tree.zero)) → ⊥
  ¬WF-ψ₂ (_ , (_ , () , _) , _)

module Orig (S : Sib) (ℓ : Ordᴵ) (one : suc zero <ᴵ ℓ) where
  open Fin S ℓ one (λ _ → ⊤) (λ _ _ → tt) using (Cert-n; A⊆B)
  open PF S using (F)

  Cert-nᴼ : ∀ n → Rel.WFᴬ (Aℓ ℓ) (toLv (F (natL n)))
  Cert-nᴼ n = Back.WF′→WFᴬ (Aℓ ℓ) A⊆B (toLv (F (natL n))) (Cert-n n)

  Cert₃ᴼ : Rel.WFᴬ (Aℓ ℓ) (toLv (F (natL 3)))
  Cert₃ᴼ = Cert-nᴼ 3
```

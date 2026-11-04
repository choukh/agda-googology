# 值判据 (九): 不动点行在低处的实例

> **判决: HOLDS (无条件的低处实例).** 底座. 结论写在 [ValueJudge](ValueJudge.lagda.md). `ValueJudgeSpec` 的 `FixRow` 在 `Lv` 上; 这里是 `Ordᶜ` 上同一个证明, 目的是说明它的前提可满足: `fix-Ω` 用它重新得到 `anchor-Ω` ($\psi_0(\Omega_1)=\varepsilon_0$), 切口无条件. 只用现成的 [OCFSpecAnchor](OCFSpecAnchor.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValueJudgeSpecLow where

open import Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (+-comm)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import OCF.Align.Level
open import OCF.Align.OCFSpecBase
open import OCF.Align.OCFSpecAnchor using (δ; γ; γ-step; Fδ; s-δ; γ≅δ; Fδ≼γ; anchor-Ω)

module FixRowᶜ {lv : ℕ → Ordᴵ} (a : (i : ℕ) → Ordᶜ (lv i)) {K} (A : Ordᶜ K) (t : ℕ → Ordᶜ zero)
               (H   : ∀ n → IsPsi zero (a n) (t n))
               (stp : ∀ n → a n ≼ a (suc n))
               (a≼A : ∀ n → a n ≼ A)
               (Cut : ∀ n {m} {y : Ordᶜ m} → C zero (a n) y → y ≺ᵛ A → y ≺ᵛ a (suc n)) where

  a-add : ∀ k n → a n ≼ a (k +ᴺ n)
  a-add zero    n = ≼-refl (a n)
  a-add (suc k) n = ≼-trans (a-add k n) (stp (k +ᴺ n))

  aˡ : ∀ n k → a n ≼ a (n +ᴺ k)
  aˡ n k = subst (λ w → a n ≼ a w) (+-comm k n) (a-add k n)

  irrR : ∀ {N′ u m n} {ξ : Ordᶜ m} {x′ : Ordᶜ n} (q₁ : ξ ≺ᵛ A) (q₂ : ξ ≺ᵛ a N′) → Recₐ A (wf A) u ξ q₁ x′ → Recₐ (a N′) (wf (a N′)) u ξ q₂ x′
  irrR {N′} {ξ = ξ} q₁ q₂ r′ = irr (belowᵛ A ξ q₁) (belowᵛ (a N′) ξ q₂) (≼-refl ξ , ≼-refl ξ) r′

  br : ∀ {m} {x : Ordᶜ m} → C zero A x → Σ ℕ λ n → C zero (a n) x
  br (base q) = 0 , base q
  br (plus σ c d) with br c | br d
  ... | n₁ , c₁ | n₂ , c₂ = (n₁ +ᴺ n₂) , plus σ (C-a (aˡ n₁ n₂) c₁) (C-a (a-add n₁ n₂) c₂)
  br (cg e c) with br c
  ... | n , c₁ = n , cg e c₁
  br (col cu cξ q r) with br cu | br cξ
  ... | n₁ , c₁ | n₂ , c₂ =
    let N   = n₁ +ᴺ n₂
        cu′ = C-a (aˡ n₁ n₂) c₁
        cξ′ = C-a (a-add n₁ n₂) c₂
        q′  = Cut N cξ′ q
    in suc N , col (C-a (stp N) cu′) (C-a (stp N) cξ′) q′ (irrR {N′ = suc N} q q′ r)

  fix : IsPsi zero A (lim t)
  fix = sup
    (≼i (suc (lim t)) (s≅ (l≅ (λ n → ≅-refl⁰ (t n)))) (≼u (≼-refl (suc (lim t)))))
    (λ c b → let n , c′ = br c in ≼l n (ub (H n) c′ b))
    (λ { (≼l n q) → let w = cof (H n) q in wit (C-a (a≼A n) (mem w)) (bd w) (dom w) })
```

**实例.** $a_n=\delta_n$ (塔), $A=\Omega_1$, $t_n=\psi_0(\delta_n)$. 切口: 成员低于 $\Omega_1$ 就低于 $t_n$ (`ub`), 而 $t_n\preccurlyeq\delta_{n+1}$. 这是 `Cut` 在低处无条件的一个实例. 所以 `FixRow` 的前提不空.

```agda
Ω₁′ : Ordᶜ (suc zero)
Ω₁′ = Ω (suc zero)

δ≼Ω : ∀ n → δ n ≼ Ω₁′
δ≼Ω n = ≼i (δ n) (≅-refl⁰ (δ n)) (≼u (≼-refl (δ n)))

δ-step : ∀ n → δ n ≼ δ (suc n)
δ-step n = ≼-trans (≅→≼ (≅-sym (γ≅δ n))) (≼-trans (≺→≼ (γ-step n)) (≅→≼ (γ≅δ (suc n))))

fix-Ω : IsPsi zero Ω₁′ (lim Fδ)
fix-Ω = FixRowᶜ.fix δ Ω₁′ Fδ s-δ δ-step δ≼Ω
  (λ n c b → ≼-trans (ub (s-δ n) c b) (≼-trans (Fδ≼γ n) (≅→≼ (γ≅δ (suc n)))))
```

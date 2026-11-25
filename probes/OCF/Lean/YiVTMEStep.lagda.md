# 值接口的记号直连实例 (四): 朝 ψ₀(Ω_{Ω+1}) 的形式检验 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiMEStep` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTMEStep where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ink; inb; posW; posW⁼; Ev; Ev-tw; Rt-tw) renaming (Rt to Rtᴾ)
open import OCF.Lean.YiVTFold
import OCF.Align.EboLeanDef as E
open E using (HC; γT)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMEBase
open import OCF.Lean.YiVTMEAnchor using (ψ₀ᵗ; Ω₁ᵗ; module G⁰)

module Lev (Ix : L → E.T → Set) where
  mutual
    Mᴸ : (j : L) → E.T → Tr j → Set
    Mᴸ j = Mᴰ (Sig j) (Lowᴸ j) (Chdᴸ j) (λ p ν → Ix (at j p) ν)

    Lowᴸ : (j : L) (p : Pos j) → E.T → Br j p → Set
    Lowᴸ (suc a)  t              = Low⁼ a t
    Lowᴸ (lim g)  (n , t)        = Low⁼ (g n) t
    Lowᴸ (Ωₗ k h) (inj₁ t)       = Low⁼ k t
    Lowᴸ (Ωₗ k h) (inj₂ (c , t)) = Low⁼ (h c) t

    Low⁼ : (a : L) (t : Pos⁼ a) → E.T → Br⁼ a t → Set
    Low⁼ a (inj₁ _) = Mᴸ a
    Low⁼ a (inj₂ p) = Lowᴸ a p

    Chdᴸ : (j : L) (c : Ch j) → E.T → ChT j c → Set
    Chdᴸ (suc a)  _ = Mᴸ a
    Chdᴸ (lim g)  n = Mᴸ (g n)
    Chdᴸ (Ωₗ k h) c = Mᴸ (h c)

t₊ : E.T
t₊ = ψ₀ᵗ (E.Ωs Ω₁ᵗ)

Step₂⁺ᴸ : Set
Step₂⁺ᴸ = (h : HC t₊) → Rt h ≼ read (twᶜ 2)

h₂ : Tr (tw 1) → L
h₂ c = tw 1 ⊕ ↑ (tw 1) c

G₂ : Tr (tw 1) → Tr (tw 2)
G₂ c = up zero c (Ωt (h₂ c)) (Ωt-nz (h₂ c))

c₂ : ℕ → Tr (tw 1)
c₂ = iter (λ z → ψs (tw 2) (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (tw 1) (ink self) (Ωt (tw 1)) (Ωt-nz (tw 1)) (G₂ z)) zero

row : ℕ → Tr zero
row n = ψ⊥ (tw 2) (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (G₂ (c₂ n))

nzrow : ∀ n → zero ⊢ zero ◃ row n
nzrow n = nz⊥ (tw 2) (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (G₂ (c₂ n))

form₂ : twᶜ 2 ≡ limc row nzrow
form₂ = refl

γ₊ : ℕ → E.T
γ₊ = γT (E.Ωs Ω₁ᵗ) Ω₁ᵗ

step⁺-red : (∀ n → M⁰ (ψ₀ᵗ (γ₊ n)) (row (suc n))) → Step₂⁺ᴸ
step⁺-red prem h = lower⁰ (mL refl (λ n → G⁰.m-cum row nzrow (suc n) (prem n))) h

_ : ψ₀ᵗ (γ₊ 0) ≡ E.EBOψ 2
_ = refl

row-form : ∀ n → row n ≡ ψ⊥ (h₂ (c₂ n)) (proj₂ (proj₂ (Ev-tw 2) (c₂ n))) (proj₂ (Rt-tw 2) (c₂ n))
                           (dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (c₂ n) zero) (Ωt (h₂ (c₂ n)))
row-form n = refl

row₀-btbo : M⁰ (E.EBOψ 2) (row 1) → (h : HC (E.EBOψ 2)) → Rt h ≼ read (twᶜ 2)
row₀-btbo m h = lower⁰ (G⁰.m-cum row nzrow 1 m) h

h₁ : Tr zero → L
h₁ z = zero ⊕ ↑ zero z

c₁-form : c₂ 1 ≡ Ω (inj₁ (inj₁ tt)) (λ z → Upc (tw 1) z (Ωt (tw 1)) (Ωt-nz (tw 1)) (Ωt (h₁ z)))
c₁-form = refl

lev₁-form : h₂ (c₂ 1) ≡ Ωₗ zero (λ z → tw 1 ⊕ ↑ (tw 1) (Upc (tw 1) z (Ωt (tw 1)) (Ωt-nz (tw 1)) (Ωt (h₁ z))))
lev₁-form = refl

_ : (k : L) (h : Tr k → L) (c : Tr k) (t : Pos⁼ (h c)) → posW (Ωₗ k h) (inj₂ (c , t)) ≡ inb c (posW⁼ (h c) t)
_ = λ k h c t → refl

drop-same : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (ρ : Rtᴾ (Ωₗ k h)) (B : Base (Ωₗ k h)) (j : L)
  (c : Tr k) (w : j ≤ h c) (β : Tr j) (nβ : j ⊢ zero ◃ β) (t : Pos⁼ (h c)) (G : Br⁼ (h c) t → Tr (Ωₗ k h))
  → ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ (Ω (inj₂ (c , t)) G)
  ≡ limc (λ n → ψs (Ωₗ k h) ε ρ B j (inb c w) β nβ (G (iter (λ z → fromBr (Ωₗ k h) (inj₂ (c , t))
            (ψs (Ωₗ k h) ε ρ B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))
              (bs B (at⁼ (h c) t) (inb c (posW⁼ (h c) t)))
              (ns B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))) (G z))) (br0⁼ (h c) t) n)))
         (λ n → nzs (Ωₗ k h) ε ρ B j (inb c w) β nβ (G (iter (λ z → fromBr (Ωₗ k h) (inj₂ (c , t))
            (ψs (Ωₗ k h) ε ρ B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))
              (bs B (at⁼ (h c) t) (inb c (posW⁼ (h c) t)))
              (ns B (at⁼ (h c) t) (inb c (posW⁼ (h c) t))) (G z))) (br0⁼ (h c) t) n)))
drop-same k h ε ρ B j c w β nβ t G = refl
```

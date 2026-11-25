# 候选 A: 判据的归约 (验收)

> 验收文件 (读记号). 编译定理, 条件: `crit : A0 → A1 → (h : HC tB) → Rt h ≼ readRW (proj₁ (ψ₀ (tw 1) o¹ Wt))`, tB 是 ψ₀(Ω_Ω+Ω₂), `Wt = up βΩ c2 (Ω₂ 树)` 是最小见证. 两条前提只说左项各支的孩子树: A0 (孩子 c 的 Ω 树朝第 0 层的折叠不低于 ψ₀(Ω_η), 任意路径), A1 (它经孩子 two 朝第 1 层的折叠不低于 ψ₁(Ω_η)), η 取遍 `M⁰ η c`.
> 无前提的部分: 第 2 层的归约 `At.lowerM` (前缀 t₀ 任意, 对满足四条下界的任意底), `hΩ`. 推论 (条件): `btbo-A0` (A0 推出塔第 1 项不低于 BTBO 的参照), `above-A` (判据推出见证严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照). 实例在 `YiKVInst`, 形状在 `YiKVCheck`.
> 不涉及上界; A0, A1 一般情形未证 (第一个障碍).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKVValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVPath
open import OCF.Lean.YiKVFold
open import OCF.Lean.YiKVRel
open import OCF.Lean.YiKVCheck using (o¹; h₁; c1; c2; βΩ; Wt; BW; g₁; A0f; cc)
open import OCF.Lean.YiCertFold using (Base)
import OCF.Align.EboLeanDef as E
open E using (HC; γT; natT; cof; cΩ) renaming (ψ to ψᵉ)
open import OCF.Lean.YiMENote using (cofψΩ; fsnψΩ)
open import OCF.Lean.YiNFOCase using (tA; tB; A≺B)
import OCF.Align.Level as O
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## 第 2 层的归约

孩子层号 two 上 Ω₂ 树的折叠 (目标第 0 层), 前缀 t₀ 任意: 记号 ψ₀(t₀+Ω₂) 的 γ-链 γ₀ = Ω₁, γₙ₊₁ = ψ₁(t₀+γₙ) 对着块里回灌的链 z. 底 B₂ 任意, 四条: 第 1 层底不低于 ψ₁(t₀) 与 Ω₁, 起点与第 0 层底不低于 ψ₀(t₀). 判据取 t₀ = Ω_Ω; t₀ = 0 时四条都是平凡的 (`YiKVInst.bho-lowerᴷ`).

```agda
ΩΩ : E.PT
ΩΩ = ψᵉ (E.Ωt (natT 1)) []

Pre Ω₂ᵗ : E.T
Pre = ΩΩ ∷ []
Ω₂ᵗ = E.Ωt (natT 2)

_ : tB ≡ ψ₀ᵗ (Pre ++ Ω₂ᵗ)
_ = refl

module At (t₀ : E.T) (o2 : Ok two) (B₂ : Base two) (β₀ : Tr⁺ zero)
  (hβ : M¹ (ψ₁ᵗ t₀) (proj₁ (B₂ one (inc tt self))))
  (hΩ : M¹ Ω₁ᵗ (proj₁ (B₂ one (inc tt self))))
  (h₀ : M⁰ (ψ₀ᵗ t₀) (proj₁ β₀))
  (hb′ : M⁰ (ψ₀ᵗ t₀) (proj₁ (B₂ zero (inc tt (inc tt self))))) where

  o1 : Ok one
  o1 = proj₂ o2 tt

  B1 : Base one
  B1 i u = ψ two o2 B₂ i (inc tt u) (B₂ i (inc tt u)) zero

  open PFm t₀ o1 B1 (B₂ one (inc tt self)) hβ
  open QHm t₀ o1 B1 hb′

  z : ℕ → Tr one
  z = iter (λ c → proj₁ (next⁺ (F⁺ c))) zero

  form : proj₁ (ψ two o2 B₂ zero (z≤ two) β₀ (proj₁ (Ωt two)))
       ≡ proj₁ (limc⁺ (λ k → next⁺ (H⁺ (z≤ one) β₀ (z k))))
  form = refl

  γ : ℕ → E.T
  γ = γT (t₀ ++ Ω₂ᵗ) u₁

  e₂ : cof (t₀ ++ Ω₂ᵗ) ≡ cΩ (natT 1)
  e₂ = cof++Ω t₀ Ω₂ᵗ refl

  sγ : ∀ n → M¹ (γ n) (z (suc n))
  sγ zero    = mw hΩ (◃l zero)
  sγ (suc n) = subst (λ s → M¹ (ψ₁ᵗ s) (z (suc (suc n)))) (sym (fsT++ t₀ _ [] (γ n))) (mw (PF (sγ n)) (◃l zero))

  lowerM : M⁰ (ψ₀ᵗ (t₀ ++ Ω₂ᵗ)) (proj₁ (ψ two o2 B₂ zero (z≤ two) β₀ (proj₁ (Ωt two))))
  lowerM = mL (cofψΩ u₀ (t₀ ++ Ω₂ᵗ) e₂) (λ n →
    subst (λ s → M⁰ s (proj₁ (ψ two o2 B₂ zero (z≤ two) β₀ (proj₁ (Ωt two)))))
      (sym (trans (fsnψΩ u₀ (t₀ ++ Ω₂ᵗ) n e₂) (cong ψ₀ᵗ (fsT++ t₀ _ [] (γ n)))))
      (G⁰.m-cum (λ k → next⁺ (H⁺ (z≤ one) β₀ (z k))) (suc n) (mw (QH (z≤ one) β₀ h₀ (sγ n)) (◃l zero))))
```

## 块上的最小见证

见证与底的定义, 以及它们的形状 (`wit`, `β₁-form`, `g₁0-form`, `β₀-form`, `b′-form`, 都是 `refl`) 在 `YiKVCheck`. 孩子 two 的第 1 层底是保留的结点, 第 c 支是 `g₁ c`; 第 0 层的起点与底都是回灌链 `cc` 的部分和, 第 c 项是 `A0f c w` (孩子 c 的 Ω 树朝第 0 层的标准折叠).

## 两条前提与判据的归约

```agda
A0 : Set
A0 = (η : E.T) (c : Tr zero) (w : zero ≤ h₁ c) → M⁰ η c → M⁰ (ψ₀ᵗ (E.Ωt η)) (proj₁ (A0f c w))

A1 : Set
A1 = (η : E.T) (c : Tr zero) → M⁰ η c → M¹ (ψ₁ᵗ (E.Ωt η)) (proj₁ (g₁ c))

hβ₁ : A1 → M¹ (ψ₁ᵗ Pre) (proj₁ (BW one (inc tt self)))
hβ₁ a1 = mΩ {p = q1} {g = λ c → proj₁ (g₁ c)} refl refl (λ η c l → a1 η c l)

hΩ : M¹ Ω₁ᵗ (proj₁ (BW one (inc tt self)))
hΩ = mw Mβ₀ (◃t (◃l zero) (◃t (◃l zero) (◃w {p = q1} {g = λ c → proj₁ (g₁ c)})))

chain0 : A0 → ∀ n → M⁰ (γT Pre [] n) (cc (suc n))
chain0 a0 zero    = pos⁰ (cc 1) (proj₂ (A0f zero (self ∙ kh o¹ zero)))
chain0 a0 (suc n) = a0 (γT Pre [] n) (cc (suc n)) (self ∙ kh o¹ (cc (suc n))) (chain0 a0 n)

h₀ : A0 → M⁰ (ψ₀ᵗ Pre) (proj₁ (ψ₀ (tw 1) o¹ βΩ))
h₀ a0 = mL refl (λ n →
  G⁰.m-cum (λ k → A0f (cc k) (z≤ (h₁ (cc k)))) (suc n) (a0 _ (cc (suc n)) (z≤ (h₁ (cc (suc n)))) (chain0 a0 n)))

hb′ : A0 → M⁰ (ψ₀ᵗ Pre) (proj₁ (BW zero (inc tt (inc tt self))))
hb′ a0 = mL refl (λ n →
  G⁰.m-cum (λ k → A0f (cc k) (self ∙ ab→≤ (crt o¹ (cc k)))) (suc n)
    (a0 _ (cc (suc n)) (self ∙ ab→≤ (crt o¹ (cc (suc n)))) (chain0 a0 n)))

crit : A0 → A1 → (h : HC tB) → Rt h ≼ readRW (proj₁ (ψ₀ (tw 1) o¹ Wt))
crit a0 a1 h = lower⁰ (At.lowerM Pre (proj₂ o¹ c2) BW (ψ₀ (tw 1) o¹ βΩ) (hβ₁ a1) hΩ (h₀ a0) (hb′ a0)) h
```

推论 (条件): A0 推出新块的塔第 1 项不低于 BTBO 的记号参照; 判据成立时最小见证严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (第十五次审查对精简块的估计值).

```agda
btbo-A0 : A0 → (h : HC (E.EBOψ 2)) → Rt h ≼ readRW (twᶜ 1)
btbo-A0 a0 h = lower⁰ (h₀ a0) h

above-A : A0 → A1 → (hA : HC tA) (hB : HC tB) → O.suc (Rt hA) ≼ readRW (proj₁ (ψ₀ (tw 1) o¹ Wt))
above-A a0 a1 hA hB = ≼-trans (A≺B hA hB) (crit a0 a1 hB)
```

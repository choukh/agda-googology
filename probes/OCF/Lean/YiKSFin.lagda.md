# 龙骨的陈述 (带前缀, F2): 有限层号的锚点是实例, 放宽与 ℕ 极限两步成立

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. `Qᴾ t T ℓ`: 对层号 ℓ 上满足 `OKB` 且第 0 层分量与 `b⊥` 对着 ψ₀(t) 的一切底, 记号项 T 对着 Ω 树以该底的折叠 (`M⁰`).
> 编译定理, 无前提: `qp-fin` (T 取 ψ₀(t+ψ₁(Ω_{m+3})), ℓ 取 `fin (m+3)`, 即 `YiANLv` 的 `Lv.Anchor.anchor`); `reachᴾ` (沿 `YiEVReach._⇐_` 的字面路径放宽, 对一切 t, T); `stepL` (ℕ 极限层号: 各孩子上的 `Qᴾ` 加 T 的余尾与基本列两条等式推出 `lim g` 上的 `Qᴾ`).
> 不给出什么: 后继一步与 Ω 形状一步 (读法的 `rS`, `rΩ`) 在层号是树时没有证; 前缀只在第 0 层给出, 所以 T 的形状是 ψ₀(t+ψ₁(Ω_ν)), 不是 ψ₀(t+Ω_ν). 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiKSFin where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; ins; inl; inb; Ev; Rt)
open import OCF.Lean.YiLegFold
import OCF.Lean.YiLSRead as S
open import OCF.Lean.YiLSFold using (OKB; ok-dS; ok-dL; ψ⊥-⊵; ψs-⊵)
open import OCF.Lean.YiT2Frame using (ok-dW)
open import OCF.Lean.YiEVReach using (cv⊴; preΩ; lim≽; Ω≽0; suc≽; _⇐_; ⇐r; ⇐s; ⇐l; ⇐w)
open import OCF.Lean.YiMEBase using (M⁰; mL; mw; read)
open import OCF.Lean.YiMEAnchor using (module G⁰)
open import OCF.Lean.YiMWPre using (M⁰-≼)
open import OCF.Lean.YiMWLow using (rd≼; rd≽)
open import OCF.Lean.YiANFam using (fin; ψᴺ; Ωᴺ)
open import OCF.Lean.YiANLv using (module Lv)
import OCF.Align.EboLeanDef as E
open E using (cof; cω; fsn)
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## 陈述, 有限层号的实例

```agda
Pre⊥ : (t : E.T) (ℓ : LF) → Base ℓ → Set
Pre⊥ t ℓ B = M⁰ (ψᴺ 0 t) (b⊥ B)

Pre0 : (t : E.T) (ℓ : LF) → Base ℓ → Set
Pre0 t ℓ B = (w : zero ≤ ℓ) → M⁰ (ψᴺ 0 t) (bs B zero w)

Qᴾ : (t T : E.T) (ℓ : LF) → Set
Qᴾ t T ℓ = (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Pre⊥ t ℓ B → Pre0 t ℓ B → M⁰ T (ψ⊥ ℓ ε ρ B (Ωt ℓ))

qp-fin : ∀ t m → Qᴾ t (ψᴺ 0 (t ++ ψᴺ 1 (Ωᴺ (suc (suc (suc m)))))) (fin (suc (suc (suc m))))
qp-fin t m ε ρ B ok h⊥ h0 = Lv.Anchor.anchor t m ε ρ B ok h⊥ h0
```

## 沿字面路径放宽

孩子的底的 `b⊥` 与第 0 层分量是父底的对应分量再折一次, 不降, 所以前缀的条件保持; 值上的一步是 `YiEVReach` 的 `suc≽`, `lim≽`, `Ω≽0`.

```agda
moveᴹ : ∀ {T} {x : Tr zero} → M⁰ T x → (y : Tr zero) → S.read x ≼ S.read y → M⁰ T y
moveᴹ {x = x} m y q = M⁰-≼ m y (≼-trans (rd≼ x) (≼-trans q (rd≽ y)))

reachᴾ : ∀ {t T j ℓ} → j ⇐ ℓ → Qᴾ t T j → Qᴾ t T ℓ
reachᴾ ⇐r Q = Q
reachᴾ (⇐s {a} p) Q ε ρ B ok h⊥ h0 =
  moveᴹ (reachᴾ p Q ε ρ (dS a ε ρ B zero) (ok-dS ε ρ B ok zero)
           (G⁰.m⊴ h⊥ (cv⊴ (ψ⊥-⊵ (suc a) ε ρ B zero)))
           (λ w → G⁰.m⊴ (h0 (ins w)) (cv⊴ (ψs-⊵ (suc a) ε ρ B zero (ins w) (bs B zero (ins w)) (ns B zero (ins w)) zero))))
    _ (suc≽ a ε ρ B ok)
reachᴾ (⇐l {g} n p) Q ε ρ B ok h⊥ h0 =
  moveᴹ (reachᴾ p Q (ε n) (proj₁ ρ n) (dL g ε ρ B n (preΩ g n)) (ok-dL g ε ρ B ok n (preΩ g n))
           (G⁰.m⊴ h⊥ (cv⊴ (ψ⊥-⊵ (lim g) ε ρ B (preΩ g n))))
           (λ w → G⁰.m⊴ (h0 (inl n w)) (cv⊴ (ψs-⊵ (lim g) ε ρ B zero (inl n w) (bs B zero (inl n w)) (ns B zero (inl n w)) (preΩ g n)))))
    _ (lim≽ g ε ρ B n)
reachᴾ (⇐w {k} {h} p) Q ε ρ B ok h⊥ h0 =
  moveᴹ (reachᴾ p Q (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (dW k h ε ρ B zero zero) (ok-dW k h ε ρ B ok zero zero)
           (G⁰.m⊴ h⊥ (cv⊴ (ψ⊥-⊵ (Ωₗ k h) ε ρ B zero)))
           (λ w → G⁰.m⊴ (h0 (inb zero w)) (cv⊴ (ψs-⊵ (Ωₗ k h) ε ρ B zero (inb zero w) (bs B zero (inb zero w)) (ns B zero (inb zero w)) zero))))
    _ (Ω≽0 k h ε ρ B)
```

## ℕ 极限层号一步

记号一侧的两条等式 (T 的余尾是 ω, 第 n 个基本列项是 `Ts n`) 作显式前提; T 取 ψ₀(t+ψ₁(Ω_ν)), ν 余尾 ω 时它们是记号的规则.

```agda
stepL : ∀ {t T} (g : ℕ → LF) (Ts : ℕ → E.T) → cof T ≡ cω → (∀ n → fsn T n ≡ Ts n)
  → (∀ n → Qᴾ t (Ts n) (g n)) → Qᴾ t T (lim g)
stepL {t} {T} g Ts e q Qs ε ρ B ok h⊥ h0 =
  mL e (λ n → subst (λ s → M⁰ s (ψ⊥ (lim g) ε ρ B (Ωt (lim g)))) (sym (q n))
    (reachᴾ (⇐l {g = g} n ⇐r) (Qs n) ε ρ B ok h⊥ h0))
```

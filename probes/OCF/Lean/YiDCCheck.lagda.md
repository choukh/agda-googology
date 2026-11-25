# 验收一侧: 三项连起来的一处检验 (有限层号上的值下界)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `valᴰ`: 规范前缀 t₀ 与满足 `GBᶠ` 的底之下, 第 n+1 层 Ω 树折到第 0 层的值不低于 ψ₀(t₀ + Ω_m) 的参照, 对一切 m ≤ n+1; `valᶜ`: 标准底, 空前缀的闭的一例.
> 做法: `leafᴰ` 接 `lowKeepᴰ` 接 `exitᴰ`. 值上不是新的: m = n+1 时就是 `lowKeepᶠ` 接 `lower⁰`, m ≤ n 时是它再接 `mono≤ⁿ`; 这里检验的是三项在 `M̃` 上能连起来.
> `wit₂`: 两步折叠的见证项 ψ₀(ψ₁(Ω₃)) 有 `M⁰` 关系 (它不是标准形, `YiDCExit.¬nf₂`), 这一类的出口没有做.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDCCheck where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.List using ([]; _++_)
open import Relation.Binary.PropositionalEquality using (refl)

open import OCF.Lean.YiLegBlock using (Tr; zero; _⊢_◃_)
open import OCF.Lean.YiLegOps using (Ωt; Ωt-nz)
open import OCF.Lean.YiLegPath using (self; ins; Ev) renaming (Rt to Rtᴸ)
open import OCF.Lean.YiLegFold using (Base; B₀; ψs)
import OCF.Align.EboLeanDef as E
open E using (natT; HC)
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiMEBase using (read; Rt; M⁰)
open import OCF.Lean.YiANFam using (fin; M; Mβ; ψᴺ; Ωᴺ)
open import OCF.Lean.YiANKp using (≤ⁿ-refl)
open import OCF.Lean.YiASIface using (Sbᶠ; s0; ss; pthᶠ; GBᶠ)
open import OCF.Lean.YiASProofLow using (lowKeepᶠ)
open import OCF.Lean.YiASProofMin using (mΩt; gbᶜ)
open import OCF.Lean.YiDCRel using (M̃; leafᴰ; lowKeepᴰ)
open import OCF.Lean.YiDCExit using (exitᴰ; Pre; pre[]; nf-low; ct-low)
```

## 有前缀的陈述

`sb0 n`: 第 0 层是 `fin n` 的子层号. `lowᴰ`: Ω_m (m ≤ n+1) 经 `leafᴰ` 对着第 n+1 层 Ω 树, 再经 `lowKeepᴰ` 折到第 0 层; 见证项是 ψ₀(t₀ + Ω_{n+1}).

```agda
sb0 : ∀ n → Sbᶠ n 0
sb0 zero    = s0
sb0 (suc n) = ss (sb0 n)

lowᴰ : ∀ n {m} → m ≤ⁿ suc n → (t₀ : E.T) (ε : Ev (fin (suc n))) (ρ : Rtᴸ (fin (suc n))) (B : Base (fin (suc n)))
     → GBᶠ n B t₀ → (β : Tr zero) (nβ : zero ⊢ zero ◃ β) → M⁰ (ψᴺ 0 t₀) β
     → M̃ 0 (ψᴺ 0 (t₀ ++ Ωᴺ m)) (ψs (fin (suc n)) ε ρ B zero (ins (pthᶠ (sb0 n))) β nβ (Ωt (fin (suc n))))
lowᴰ n {m} l t₀ ε ρ B gb β nβ hβ =
  lowKeepᴰ {ℓ = suc n} {j = 0} (ε , ρ , B) (ins (pthᶠ (sb0 n))) (β , nβ) t₀ (n , refl) (ss (sb0 n) , refl) (hβ , gb) tt
    (leafᴰ {ℓ = suc n} {ν = natT m} (m , refl , l))

valᴰ : ∀ n {m} → m ≤ⁿ suc n → (t₀ : E.T) → Pre t₀ (suc n)
     → (ε : Ev (fin (suc n))) (ρ : Rtᴸ (fin (suc n))) (B : Base (fin (suc n)))
     → GBᶠ n B t₀ → (β : Tr zero) (nβ : zero ⊢ zero ◃ β) → M⁰ (ψᴺ 0 t₀) β
     → (h : HC (ψᴺ 0 (t₀ ++ Ωᴺ m)))
     → Rt h ≼ read (ψs (fin (suc n)) ε ρ B zero (ins (pthᶠ (sb0 n))) β nβ (Ωt (fin (suc n))))
valᴰ n {m} l t₀ P ε ρ B gb β nβ hβ h =
  exitᴰ (lowᴰ n l t₀ ε ρ B gb β nβ hβ) (nf-low P l) (nf-low P (≤ⁿ-refl (suc n))) (ct-low (t₀ ++ Ωᴺ (suc n))) h
```

## 闭的一例

标准底, 底值是第 0 层 Ω 树, 前缀为空. 参照 ψ₀(Ω_m) 的推导 `hΩ m` 存在.

```agda
opaque
  hΩ : ∀ m → HC (ψᴺ 0 (Ωᴺ m))
  hΩ m = hc (nf-low (pre[] m) (≤ⁿ-refl m)) (ct-low (Ωᴺ m))

valᶜ : ∀ n {m} → m ≤ⁿ suc n → (ε : Ev (fin (suc n))) (ρ : Rtᴸ (fin (suc n))) (h : HC (ψᴺ 0 (Ωᴺ m)))
     → Rt h ≼ read (ψs (fin (suc n)) ε ρ (B₀ (fin (suc n))) zero (ins (pthᶠ (sb0 n))) (Ωt zero) (Ωt-nz zero) (Ωt (fin (suc n))))
valᶜ n l ε ρ h = valᴰ n l [] (pre[] (suc n)) ε ρ (B₀ (fin (suc n))) (gbᶜ n) (Ωt zero) (Ωt-nz zero) (mΩt 0) h
```

## 两步折叠的见证项

第 3 层 Ω 树折到第 1 层 (`y₁`), 再折到第 0 层. 两次 `lowKeepᶠ` (前缀为空) 给出的记号项是 ψ₀(ψ₁(Ω₃)).

```agda
module Two (ε : Ev (fin 3)) (ρ : Rtᴸ (fin 3)) (ε′ : Ev (fin 1)) (ρ′ : Rtᴸ (fin 1)) where

  y₁ : Tr (fin 1)
  y₁ = ψs (fin 3) ε ρ (B₀ (fin 3)) (fin 1) (ins (pthᶠ (ss s0))) (Ωt (fin 1)) (Ωt-nz (fin 1)) (Ωt (fin 3))

  wit₁ : M 1 (ψᴺ 1 (Ωᴺ 3)) y₁
  wit₁ = lowKeepᶠ {ℓ = 3} {j = 1} (ε , ρ , B₀ (fin 3)) (ins (pthᶠ (ss s0))) (Ωt (fin 1) , Ωt-nz (fin 1)) []
           (2 , refl) (ss (ss s0) , refl) (mΩt 1 , gbᶜ 2) tt (Mβ 2)

  wit₂ : M⁰ (ψᴺ 0 (ψᴺ 1 (Ωᴺ 3))) (ψs (fin 1) ε′ ρ′ (B₀ (fin 1)) zero (ins self) (Ωt zero) (Ωt-nz zero) y₁)
  wit₂ = lowKeepᶠ {ℓ = 1} {j = 0} (ε′ , ρ′ , B₀ (fin 1)) (ins self) (Ωt zero , Ωt-nz zero) []
           (0 , refl) (ss s0 , refl) (mΩt 0 , gbᶜ 0) tt wit₁
```

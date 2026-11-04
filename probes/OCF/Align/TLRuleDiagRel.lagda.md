# 折叠是和的作用 (七): 对角线对上旧折叠

> 不含记号. 入口 [TLRule](TLRule.lagda.md). `CI`: 每一格的状态对上 $\psi(\Omega_u)$, 新的层对上 $\psi_0(\Omega_u)$. 延长的状态: 旧目标用世界 $u$ 里的不变量, 新目标重新走一遍.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLRuleDiagRel where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF hiding (_⊕_)
open import OCF.Align.CumReadCFEq
import OCF.Align.TLRuleSum as N
open N using (D; n0; n1; _⨾_; sum; accL; ω⋅; Ωd; Dif; Ψ; Lg-Ψ; module Fold)
open import OCF.Align.TLRuleRel
open import OCF.Align.TLRuleMain using (module Top; Co; ce; Co-Rel; Co-Ψ)
open import OCF.Align.TLRuleDiag

import OCF.Align.TLRuleSim
module Si (W : A) (lW : Lg W) = OCF.Align.TLRuleSim W lW ω⋅

record CI (c : Cell) : Set where
  field
    inv : Si.Inv (u c) (lu c) (Y c) (Ω̇ (u c))
    co  : Co (v c) (ψ₀Ω (u c) (lu c))
open CI public

-- 一格的延长
module Step (c : Cell) (I : CI c) where
  private
    V = v c
    lV = lv c
    P = p c
    U = u c
    lU = lu c
    module T₁ = Top V lV
    module S₁ = Si V lV
  open Fold V lV ω⋅
  open Ext c

  z₀ : O V
  z₀ = emb P (Ω̇ U)

  z₀≈ : z₀ ≈ z₀
  z₀≈ = emb≈ P P (Ω≈ U)

  zero-inv : S₁.Inv {V} (λ _ → n0) o0
  zero-inv {t} τ T l = rz (Ω≈ t) (Ω≈ t)

  -- 新目标: 重新走 Ω_u
  fresh : S₁.Diff (Act self (Ωd U P lU) (λ _ → n0)) o0 z₀
  fresh = S₁.RS (accL V) self T₁.I₁ {w = n0} {z₀ = o0} tt (Ω-Rel U P lU) (λ _ → n0) zero-inv

  ext-inv : S₁.Inv ext z₀
  ext-inv {t} τ T l with cmpF P τ lV
  ... | inj₁ q = rr (inv I q (inj₁ q) lU) (ψQ (Ω̇ U) z₀ (inj₁ q) lU T l (emb≈ʳ P (Ω≈ U))) (ψQ z₀ z₀ T l T l z₀≈)
  ... | inj₂ q = fresh τ T l T l

  Δ-diff : S₁.Diff Δ z₀ (Ω̇ V)
  Δ-diff = S₁.RS (accL V) self T₁.I₁ {w = n0} {z₀ = z₀} z₀≈ (Dif-Rel V P self lV) ext ext-inv

  T₀ : Tg azero V
  T₀ = inj₁ (z⊲ V)

  CI′ : CI (step c)
  CI′ = record
    { inv = S₁.inv+ ext-inv Δ-diff
    ; co  = Co-Rel {a = V}
              (Δ-diff (z⊲ V) T₀ lV T₀ lV)
              (ce (co I) (ψQ (Ω̇ U) z₀ (inj₁ (z⊲ U)) lU T₀ lV (emb≈ʳ P (Ω≈ U))))
    }

start-CI : CI start
start-CI = record
  { inv = λ {t} τ T l → S₁.RS (accL one) self T₁.I₁ {w = n0} {z₀ = o0} tt (Ω-Rel one self tt) (λ _ → n0) (λ {t₁} τ₁ T₁′ l₁ → rz (Ω≈ t₁) (Ω≈ t₁)) τ T l T l
  ; co  = Co-Ψ one tt
  }
  where
  one : A
  one = asuc azero
  module T₁ = Top one tt
  module S₁ = Si one tt

cis : ∀ n → CI (cellΣ n)
cis zero = start-CI
cis (suc n) = Step.CI′ (cellΣ n) (cis n)

coΣ : ∀ n → Co (u (cellΣ (suc n))) (ψ₀Ω (u (cellΣ n)) (lu (cellΣ n)))
coΣ n = co (cis n)
```

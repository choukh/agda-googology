# 新 ψ 的逐项保持定理

合同只要求源层之下的 Ω 种子已有对应。证明对原 Rep 归纳；
链点的对应随迭代生成，再用输入 Ω 子句证明分支相关。
不改树、Rep 或低层 raw 域，不计算 raw 输入的码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactRep where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.EboLeanDef using (T; Cmp; sucT; cmpᵀ; lt; eq; gt; γT; fsT; Ωt; _<ᵀ_)
open import OCF.Align.EboLeanBase using (<ᵀ-trans; lt→<; eq→≡)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.JiaBase
open import OCF.Align.JiaRep
open RelLayer using (rz; rs; rl; ro)
open import OCF.Align.JiaRepMove using (rep-coe)
open import OCF.Align.JiaExactFold using (dispatch; module Fold)
open import OCF.Align.JiaExactSeeds using (SeedSpec; sound)
open import OCF.Align.JiaExactCode
open import OCF.Align.JiaAuditClosure using (cof-suc)
open import OCF.Align.JiaExactAdd using (rep-copies-single)

module Sound (seeds : Seeds) where
  open Seeds seeds
  open Fold seeds using (ψ)

  ψ-rep : ∀ {ℓ i} (aℓ : Acc′ ℓ) (ai : Acc′ i) (p : Below i ℓ) → SeedSpec seeds ℓ →
    ∀ {x c} → Rep aℓ x c → Rep ai (ψ aℓ ai p x) (Ψ i c)
  ψ-rep (acc h) (acc hi) target S rz = sound S target (acc hi)
  ψ-rep {i = i} (acc h) (acc hi) target S (rs {c = c} r) =
    rl (cof-ψ-1 i (sucT c) (cof-suc c))
      (λ n → subst (Rep (acc hi) _) (sym (fsn-ψ-suc i c n))
        (rep-copies-single (acc hi) (ψ-rep (acc h) (acc hi) target S r) n))
  ψ-rep {i = i} (acc h) (acc hi) target S (rl {c = c} e r) =
    rl (cof-ψ-ω i c e)
      (λ n → subst (Rep (acc hi) _) (sym (fsn-ψ-ω i c e n))
        (ψ-rep (acc h) (acc hi) target S (r n)))
  ψ-rep {ℓ} {i} (acc h) (acc hi) target S (ro {j} {p = q} {f} {c} ec r) =
    node-sound (cmpᵀ (sucT j) i) refl
    where
    aj = h (normal q) (smaller q)
    out : Tree j aj → Tree i (acc hi)
    out γ = ψ (acc h) (acc hi) target (f γ)
    step : Tree j aj → Tree j aj
    step γ = ψ (acc h) aj q (f γ)
    chain : ℕ → Tree j aj
    chain = iter step (seed j aj)
    chain-rep : ∀ n → Rep aj (chain n) (γT c j n)
    chain-rep zero = sound S q aj
    chain-rep (suc n) = ψ-rep (acc h) aj q S (r (chain-rep n))

    node-sound : (m : Cmp) (em : cmpᵀ (sucT j) i ≡ m) →
      Rep (acc hi) (dispatch (acc h) (acc hi) target q out step (seed j aj) m em) (Ψ i c)
    node-sound lt em = ro (cof-ψ-Ω i c j lt ec em)
      (λ {y} {d} s → subst (Rep (acc hi) _) (sym (fsT-ψ-Ω i c j lt ec em d))
        (ψ-rep (acc h) (acc hi) target S
          (r (rep-coe (hi (normal q) j<i) aj s))))
      where j<i = <ᵀ-trans (<-sucT j) (lt→< (sucT j) i em)
    node-sound eq em = ro (cof-ψ-Ω i c j eq ec em)
      (λ {y} {d} s → subst (Rep (acc hi) _) (sym (fsT-ψ-Ω i c j eq ec em d))
        (ψ-rep (acc h) (acc hi) target S
          (r (rep-coe (hi (normal q) j<i) aj s))))
      where j<i = subst (j <ᵀ_) (eq→≡ (sucT j) i em) (<-sucT j)
    node-sound gt em = rl (cof-ψ-Ω i c j gt ec em)
      (λ n → subst (Rep (acc hi) _) (sym (fsn-ψ-Ω i c j gt ec em n))
        (ψ-rep (acc h) (acc hi) target S (r (chain-rep n))))
```

这是有界种子合同下的保持定理，不是全塔种子或无参数闭项的交付。
合同的已实填实例见 `JiaExactSeeds.one-spec`。

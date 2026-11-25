# Ω 规范读法族与单个有限顶读法的障碍
验收文件；规范读法及其 Leaf 对全部塔成立，且在 Λ 上共尾于全部记号项。
编译否定 `no-finite-tops` 仅排除为每个 Cn 层号选单个 E.T 顶界；不否定 Leafᶜ。
同一 Λ 上 `leaf-Λ` 对任意记号项成立；一般 Cn 的 Leaf 仍未证。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLCanonical where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiLLCheck as LL
open import OCF.Lean.YiCNDomain using (Cn; cn-tw; cl; Ωc)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; <ᵀ-trans; <ᵀ-irrefl; <-≤)
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiNLRead
open import OCF.Lean.YiNLCtx
open import OCF.Lean.YiNLRaise

one-top : ∀ ℓ → Top ℓ []
one-top ℓ = extend identity ℓ (GR.c0 refl) (H.m1 refl H.mz)

reg-read : ∀ k {μ} → GR.Rd k μ → GR.Rd (Ωc k) (E.Ωs μ)
reg-read k {μ} q = GR.ca (inj₂ (μ , cof-regular μ , q , λ η c r →
  subst (GR.Rd (k ⊕ ↑ k c)) (sym (fs-regular μ η)) (GR.rd-add k (↑ k c) (readR k r))))

reg-top : ∀ k {μ} → GR.Rd k μ → Top (Ωc k) (E.Ωs μ)
reg-top k {μ} q = H.mΩ (ΩΩ (E.Ωs μ) (cof-regular μ)) q
  (λ η c r → subst (λ t → GR.R (Ωc k) t _)
    (sym (trans (fsΩΩ (E.Ωs μ) η (cof-regular μ)) (cong E.Ωt (fs-regular μ η))))
    (H.mU H.mz (raiseR k (prefix k) [] (GR.c0 refl) (one-top k) r)))

κ : ℕ → E.T
κ zero = []
κ (suc n) = E.Ωs (κ n)

canon-read : ∀ n → GR.Rd (tw n) (κ n)
canon-read zero = GR.c0 refl
canon-read (suc n) = reg-read (tw n) (canon-read n)

canon-top : ∀ n → Top (tw n) (κ n)
canon-top zero = one-top zero
canon-top (suc n) = reg-top (tw n) (canon-read n)

depth : E.T → ℕ
depth [] = zero
depth (E.ψ u b ∷ xs) = suc (depth u)

cofinal : ∀ t → t E.<ᵀ κ (suc (depth t))
cofinal [] = E.[]<
cofinal (E.ψ u b ∷ xs) = E.hd< (E.lv< (<ᵀ-trans (cofinal u) (<-sucT (κ (suc (depth u))))))

cn-Λ : Cn Λ
cn-Λ = cl cn-tw (λ n → P.ink P.self)

read-Λ : ∀ n → GR.Rd Λ (κ n)
read-Λ n = GR.rd-child sL tw n (canon-read n)

unbounded-Λ : ∀ t → Σ E.T (λ ν → GR.Rd Λ ν × (t E.<ᵀ ν))
unbounded-Λ t = κ (suc (depth t)) , read-Λ (suc (depth t)) , cofinal t

no-top-Λ : ∀ t → (∀ {ν} → GR.Rd Λ ν → ν ≤ᵀ t) → ⊥
no-top-Λ t ub = <ᵀ-irrefl (<-≤ (cofinal t) (ub (read-Λ (suc (depth t)))))

FiniteTops : Set
FiniteTops = ∀ {ℓ} → Cn ℓ → Σ E.T (λ t → ∀ {ν} → GR.Rd ℓ ν → ν ≤ᵀ t)

no-finite-tops : FiniteTops → ⊥
no-finite-tops tops = no-top-Λ (proj₁ (tops cn-Λ)) (proj₂ (tops cn-Λ))

leaf-Λ : ∀ ν → Top Λ ν
leaf-Λ ν = LL.G.m-cum sL tw (λ n → O.upz n (O.Ωt (tw n))) (suc (depth ν))
  (H.mU H.mz (LL.rdown (tw (suc (depth ν))) (Ωt-mono (inj₁ (cofinal ν))) (canon-top (suc (depth ν)))))
```

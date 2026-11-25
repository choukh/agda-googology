# 目标孩子 ω: 上确界归约到后继一步

> 验收文件 (读记号), 不进成品. 判决: 条件定理. `liftC : StepS → M 0 η c → Car (ψ_ω(Ω_η)) (↑ c)`: 推导的 `mz`, `mL`, `mw`, `mc` 四行无前提 (`mw` 一行用 `YiSVMono.mono-path`), 只有 `m1` 一行归到 `StepS`; `top-red : StepS → 塔第 1 项 Ω 树朝 ω 层的换基折叠承载 ψ_ω(Ω_{Ω₁})`.
> `StepS` 未证, 没有否定; 它的结论在 η ≤ ω+1 时对一切 x 成立 (`step-low`, 不用归纳前提), 第一处没有的是 η = ω+2.
> 来源: 归约的形状与记号引理 (`cofΩω`, `fsnΩω`, `Ωt≤`) 取自 `YiLTLift.liftQ` (那里目标是第 0 层).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSVRed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; natT; sucT)
open import OCF.Lean.YiMENote using (cofψω; fsnψω)
open import OCF.Lean.YiANFam using (Ωᴺ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
import OCF.Lean.YiHCFam as HF
open import OCF.Lean.YiHCOmega using (appᵘ)
open import OCF.Lean.YiLTLift using (cofΩω; fsnΩω; Ωt≤)
open import OCF.Lean.YiTBRow using (h₁)
open import OCF.Lean.YiTBTab using (ωᶜ)
open import OCF.Lean.YiBSBase using (seen)
open import OCF.Lean.YiSVMono
open import OCF.Lean.YiSVStep
open import OCF.Lean.YiSVCell
open import OCF.Lean.YiSVOmega

Qη : E.T → E.T
Qη η = ψω (E.Ωt η)

module Red (oc : (k : ℕ) → Ok (G k)) where
  open Wω using (Lω; Mω)
  module S = Sω oc
  module C (t : E.T) = Mono Lω (Rr , oc) (Mω (ψω [])) (Mω t) mw mw (λ a → Hω.Gω.m-right a)

  Car : E.T → L → Set
  Car = C.Car

  Cc : ∀ {s t u} → s ≤ᵀ t → Car t u → Car s u
  Cc le q ob r B β ok hβ = mc le (q ob r B β ok hβ)

  CL : ∀ {t u} → cof t ≡ cω → (∀ k → Car (fsn t k) u) → Car t u
  CL e h ob r B β ok hβ = mL e (λ k → h k ob r B β ok hβ)

  StepS : Set
  StepS = ∀ {η x} → cof η ≡ c1 → HF.M 0 (pred η) x → Car (Qη (pred η)) (↑ zero x) → Car (Qη η) (↑ zero (suc x))

  Cz : ∀ c → Car (Qη []) (↑ zero c)
  Cz c = Cc (appᵘ ωᵀ [] (Ωt≤ (inj₁ E.[]<))) (C.mono-path (Qη ωᵀ) (z⊑ (↑ zero c) (noΩ-↑ c)) (noΩ-↑ c) S.car₀)

  liftC : StepS → ∀ {η c} → HF.M 0 η c → Car (Qη η) (↑ zero c)
  liftC st (mz {x = c})             = Cz c
  liftC st (m1 e m)                 = st e m (liftC st m)
  liftC st {c = c} (mL {t = η} e h) =
    CL (cofψω ωᵀ (E.Ωt η) (cofΩω η e))
       (λ k → subst (λ z → Car z (↑ zero c))
                (sym (trans (fsnψω ωᵀ (E.Ωt η) k (cofΩω η e)) (cong ψω (fsnΩω η k e))))
                (liftC st (h k)))
  liftC st (mΩ {p = ()} _ _ _)
  liftC st (mU {c = ()} _ _)
  liftC st {c = c} (mw m d)         = C.mono-path _ (◃→⊑ zero d) (noΩ-↑ c) (liftC st m)
  liftC st (mc le m)                = Cc (appᵘ ωᵀ [] (Ωt≤ le)) (liftC st m)

  step-low : ∀ {η} → η ≤ᵀ sucT ωᵀ → ∀ x → Car (Qη η) (↑ zero (suc x))
  step-low le x = Cc (appᵘ ωᵀ [] (Ωt≤ le))
    (C.mono-path (Qη (sucT ωᵀ)) (one⊑ (suc x) (z◃ x ◃s)) (noΩ-↑ (suc x)) S.car₁)

open Wω using (Lω; Mω)
module Rᴬ = Red ocᴬ

Ω₁ᵀ : E.T
Ω₁ᵀ = Ωᴺ 1

cof-top : cof (Qη Ω₁ᵀ) ≡ cΩ (natT 0)
cof-top = refl

fs-top : ∀ η → fsT (Qη Ω₁ᵀ) η ≡ Qη η
fs-top η = refl

branch-red : Rᴬ.StepS → (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β)
           → ∀ η c → HF.M 0 η c → Mω (Qη η) (proj₁ (Fᴬ B β (blk c)))
branch-red st B β hβ η c m =
  cell nzω (Ok-tw 1) (Mω (Qη η)) mw c B β zero (proj₁ (Ωt (h₁ c))) (proj₂ (Ωt (h₁ c)))
    (Rᴬ.C.seen-car (Qη η) Sᶻ (lift zero (↑ zero ωᶜ)) β c (Rᴬ.liftC st m) hβ)

top-red : Rᴬ.StepS → (B : Base (tw 1)) (β : Tr⁺ Lω) → Mω (ψω []) (proj₁ β)
        → Mω (Qη Ω₁ᵀ) (proj₁ (Fᴬ B β (proj₁ (Ωt (tw 1)))))
top-red st B β hβ =
  top-from-branch B β {t = Qη Ω₁ᵀ} cof-top refl
    (λ η c m → subst (λ z → Mω z (proj₁ (Fᴬ B β (blk c)))) (sym (fs-top η)) (branch-red st B β hβ η c m))
```

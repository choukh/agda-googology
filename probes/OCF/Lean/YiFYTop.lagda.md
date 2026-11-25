# 任意层 Ω 树放大其折叠底
验收文件；编译定理 top-next：沿零层一致路径折叠 Ωt，值支配底的 ω 次累加，表与底任意。
未改树、折叠或合法性；不是全域跨层单调，也未给出记号强度。
来源：YiOLSum.Uniform 的累计下界、YiLTLim.nodeZ 的零层不保留、YiTBFam.ψ-⊵ 的底保持。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFYTop where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiLBInv as LB
import OCF.Lean.YiLTLim as LT
import OCF.Lean.YiOLSum as SUM
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)
node-next : {X : Set} {x₀ : X} (m : F.Keep B.zero X x₀)
  (G : X → O.Tr⁺ B.zero) (s : X → X) (b : O.Tr⁺ B.zero)
  → (∀ x → K.readRW (proj₁ b) ≼ K.readRW (proj₁ (G x)))
  → K.readRW (proj₁ (O.next⁺ b)) ≼ K.readRW (proj₁ (F.node⁺ m G s))
node-next {x₀ = x₀} m G s b low = LT.nodeZ m
  (λ y → K.readRW (proj₁ (O.next⁺ b)) ≼ K.readRW (proj₁ y)) G s U.bound
  where module U = SUM.Uniform b (λ n → G (O.iter s x₀ n)) (λ n → low (O.iter s x₀ n))
omega-next : (ℓ : B.L) (o : P.Ok ℓ) (r : TB.Rb ℓ) (bs : F.Base ℓ)
  (b : O.Tr⁺ B.zero) (p : B.Pos ℓ) (g : B.Br ℓ p → B.Tr ℓ)
  → K.readRW (proj₁ (O.next⁺ b)) ≼ K.readRW (proj₁
    (TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) b (B.Ω p g)))
omega-next ℓ o r bs b p g = node-next (F.kp ℓ o p (P.z≤ ℓ))
  (λ z → TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) b (g z))
  (λ z → B.fromBr ℓ p (proj₁ (TB.ψ ℓ o r bs (B.at ℓ p) (P.posW ℓ p)
    (bs (B.at ℓ p) (P.posW ℓ p)) (g z)))) b
  (λ z → LB.from⊴ (TF.ψ-⊵ ℓ o r bs B.zero (P.z≤ ℓ) b (g z)))
top-next : (ℓ : B.L) (o : P.Ok ℓ) (r : TB.Rb ℓ) (bs : F.Base ℓ) (b : O.Tr⁺ B.zero)
  → K.readRW (proj₁ (O.next⁺ b)) ≼ K.readRW (proj₁
    (TB.ψ ℓ o r bs B.zero (P.z≤ ℓ) b (proj₁ (O.Ωt ℓ))))
top-next B.zero o r bs b = ≼-refl _
top-next (B.nd B.sS h) o r bs b = omega-next (B.nd B.sS h) o r bs b
  (inj₂ (tt , inj₁ tt)) (λ c → proj₁ (O.upz tt (B.suc c , O.z◃ c B.◃s)))
top-next (B.nd B.sL h) o r bs b = ≼l 0 (top-next (h 0) (proj₂ o 0) (proj₂ r 0)
  (λ i u → bs i (P.inc 0 u)) b)
top-next (B.nd (B.sΩ k) h) o r bs b = omega-next (B.nd (B.sΩ k) h) o r bs b
  (inj₁ (inj₁ tt)) (λ c → proj₁ (O.upz c (O.Ωt (h c))))
```

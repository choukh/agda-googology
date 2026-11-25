# 新终点的继承底与真实链
不读记号；来源：YiGIInst 的底和 YiFRStep 的链，仅换为 YiCWTable 的表。
本文件的 chain 是 EBOᵗ 各支的实际回灌链；不借用旧链点，不提供值验收。
第 3 站的指定格与继承底等式见文末；等式不声称值随链严格增长。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCWActual where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₂)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
open import OCF.Lean.YiCWTable
FΛ : ℕ → B.Tr B.Λ
FΛ n = proj₁ (O.upz {s = B.sL} {h = B.tw} n (O.Ωt (B.tw n)))
pre : ℕ → B.Tr B.Λ
pre zero = B.zero
pre (suc n) = O.cum FΛ n
baseᴱ : ∀ n → F.Base (B.tw n)
baseᴱ n i u = TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) (pre n)
betaᴱ : ∀ n → O.Tr⁺ B.zero
betaᴱ n = TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (pre n)
station : ℕ → B.Tr B.zero
station n = proj₁ (TB.ψ (B.tw n) (P.Ok-tw n) (rbᵗ n) (baseᴱ n) B.zero (P.z≤ (B.tw n)) (betaᴱ n) (proj₁ (O.Ωt (B.tw n))))
branch-form : ∀ n → station n ≡ proj₁ (TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (O.cum FΛ n))
branch-form zero = refl
branch-form (suc n) = refl
module Step (n : ℕ) where
  ℓ = B.tw (suc n)
  k = B.tw n
  child = hᵗ n
  g : B.Tr k → B.Tr ℓ
  g c = proj₁ (O.upz {s = B.sΩ k} {h = child} c (O.Ωt (child c)))
  feed : B.Tr k → B.Tr k
  feed c = proj₁ (TB.ψ ℓ (P.Ok-tw (suc n)) (rbᵗ (suc n)) (baseᴱ (suc n)) k (P.ink P.self)
    (baseᴱ (suc n) k (P.ink P.self)) (g c))
  out : B.Tr k → O.Tr⁺ B.zero
  out c = TB.ψ ℓ (P.Ok-tw (suc n)) (rbᵗ (suc n)) (baseᴱ (suc n)) B.zero (P.z≤ ℓ) (betaᴱ (suc n)) (g c)
  chain : ℕ → B.Tr k
  chain = O.iter feed B.zero
  out-child : ∀ q → out (chain q) ≡ TB.ψ (child (chain q)) (proj₂ (P.Ok-tw (suc n)) (chain q)) (MT.rbᶻ (child (chain q)))
    (λ i u → baseᴱ (suc n) i (P.inc (chain q) u)) B.zero (P.z≤ (child (chain q))) (betaᴱ (suc n)) (proj₁ (O.Ωt (child (chain q))))
  out-child q = refl
c₁ : B.Tr (B.tw 2)
c₁ = Step.chain 2 1
hit₁ : proj₁ (rbᵗ 3) B.zero c₁ ≡ just (inj₂ (P.lift (B.tw 2) (B.↑ (B.tw 2) c₁)))
hit₁ = refl
old-miss₁ : proj₁ (MT.rbᶻ (B.tw 3)) B.zero c₁ ≡ nothing
old-miss₁ = refl
prior : F.Base (B.tw 3)
prior i u = TB.ψ B.Λ P.Ok-Λ rbΛ (F.B₀ B.Λ) i (P.inc 3 u) (O.Ωt i) (pre 2)
base-form : ∀ i (u : i P.≤ hᵗ 2 c₁) → baseᴱ 3 i (P.inc c₁ u) ≡
  TB.ψ (hᵗ 2 c₁) (proj₂ (P.Ok-tw 3) c₁) (MT.rbᶻ (hᵗ 2 c₁))
    (λ j v → prior j (P.inc c₁ v)) i u (prior i (P.inc c₁ u))
    (proj₁ (P.emb (hᵗ 2 c₁) (proj₂ (P.Ok-tw 3) c₁) (P.lift (B.tw 2) (B.↑ (B.tw 2) c₁)) (O.Ωt (B.tw 2))))
base-form i u = refl
```

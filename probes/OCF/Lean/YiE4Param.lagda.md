# 以整张比较表为参数的对象
验收工程副本；pre、底、起点、Step 与限制底按 r : Rb Λ 参数化。
塔表与孩子表均取 r 的对应分量；来源：YiGIInst、YiFRStep；入口见 YiE4Default。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiE4Param where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiE4Base as Q
module At (r : TB.Rb B.Λ) where
  table : ∀ n → TB.Rb (B.tw n)
  table n = proj₂ r n
  -- perf: S-1，参数化实例本身也是出生处；预段、底、起点全封。
  opaque
    FΛ : ℕ → B.Tr B.Λ
    FΛ n = proj₁ (O.upz {s = B.sL} {h = B.tw} n (O.Ωt (B.tw n)))
    FΛ-eq : ∀ n → FΛ n ≡ proj₁ (O.upz {s = B.sL} {h = B.tw} n (O.Ωt (B.tw n)))
    FΛ-eq n = refl
    pre : ℕ → B.Tr B.Λ
    pre zero = B.zero
    pre (suc n) = O.cum FΛ n
    pre-zero : pre 0 ≡ B.zero
    pre-zero = refl
    pre-suc : ∀ n → pre (suc n) ≡ O.cum FΛ n
    pre-suc n = refl
    baseᴱ : ∀ n → F.Base (B.tw n)
    baseᴱ n i u = TB.ψ B.Λ P.Ok-Λ r (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) (pre n)
    baseᴱ-eq : ∀ n → baseᴱ n ≡ (λ i u → TB.ψ B.Λ P.Ok-Λ r (F.B₀ B.Λ) i (P.inc n u) (O.Ωt i) (pre n))
    baseᴱ-eq n = refl
    betaᴱ : (n : ℕ) → O.Tr⁺ B.zero
    betaᴱ n = TB.ψ B.Λ P.Ok-Λ r (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (pre n)
    betaᴱ-eq : ∀ n → betaᴱ n ≡ TB.ψ B.Λ P.Ok-Λ r (F.B₀ B.Λ) B.zero (P.z≤ B.Λ) (O.Ωt B.zero) (pre n)
    betaᴱ-eq n = refl
  module Step (n : ℕ) where
    ℓ = B.tw (suc n)
    k = B.tw n
    child : B.Tr k → B.L
    child c = k B.⊕ B.↑ k c
    child-table : ∀ c → TB.Rb (child c)
    child-table c = proj₂ (table (suc n)) c
    -- perf: S-1，保留参数表的对应孩子分量，函数和整函数等式同封。
    opaque
      g : B.Tr k → B.Tr ℓ
      g c = proj₁ (O.upz {s = B.sΩ k} {h = child} c (O.Ωt (child c)))
      g-eq : g ≡ (λ c → proj₁ (O.upz {s = B.sΩ k} {h = child} c (O.Ωt (child c))))
      g-eq = refl
      feed : B.Tr k → B.Tr k
      feed c = proj₁ (TB.ψ ℓ (P.Ok-tw (suc n)) (table (suc n)) (baseᴱ (suc n)) k (P.ink P.self)
        (baseᴱ (suc n) k (P.ink P.self)) (g c))
      feed-eq : feed ≡ (λ c → proj₁ (TB.ψ ℓ (P.Ok-tw (suc n)) (table (suc n)) (baseᴱ (suc n)) k (P.ink P.self)
        (baseᴱ (suc n) k (P.ink P.self)) (g c)))
      feed-eq = refl
      out : B.Tr k → O.Tr⁺ B.zero
      out c = TB.ψ ℓ (P.Ok-tw (suc n)) (table (suc n)) (baseᴱ (suc n)) B.zero (P.z≤ ℓ) (betaᴱ (suc n)) (g c)
      out-eq : out ≡ (λ c → TB.ψ ℓ (P.Ok-tw (suc n)) (table (suc n)) (baseᴱ (suc n)) B.zero (P.z≤ ℓ) (betaᴱ (suc n)) (g c))
      out-eq = refl
      out-child : ∀ c → out c ≡ TB.ψ (child c) (proj₂ (P.Ok-tw (suc n)) c) (child-table c)
        (λ i u → baseᴱ (suc n) i (P.inc c u)) B.zero (P.z≤ (child c)) (betaᴱ (suc n)) (proj₁ (O.Ωt (child c)))
      out-child c = refl
    chain : ℕ → B.Tr k
    chain = O.iter feed B.zero
    chain-zero : chain 0 ≡ B.zero
    chain-zero = refl
    chain-step : ∀ q → chain (suc q) ≡ feed (chain q)
    chain-step q = refl
  -- perf: S-1，限制底在对应孩子层出生处封装。
  opaque
    restricted : ∀ c → F.Base (Step.child 2 c)
    restricted c i u = baseᴱ 3 i (P.inc c u)
    restricted-eq : ∀ c → restricted c ≡ (λ i u → baseᴱ 3 i (P.inc c u))
    restricted-eq c = refl
  make : B.Tr (B.tw 2) → Q.Ctx
  make c = Step.child 2 c , proj₂ (P.Ok-tw 3) c , Step.child-table 2 c , restricted c
  -- perf: S-1/C-9，规范链点、依赖环境和输出分块封装。
  opaque
    c₁ : B.Tr (B.tw 2)
    c₁ = Step.chain 2 1
    c₁-eq : c₁ ≡ Step.chain 2 1
    c₁-eq = refl
    ctx : Q.Ctx
    ctx = make c₁
    ctx-eq : ctx ≡ make c₁
    ctx-eq = refl
    β : O.Tr⁺ B.zero
    β = betaᴱ 3
    β-eq : β ≡ betaᴱ 3
    β-eq = refl
  -- perf: S-1，构造与规格同封，调用点使用导出等式。
  opaque
    output : O.Tr⁺ B.zero
    output = Q.collapse ctx β
    output-eq : output ≡ Q.collapse ctx β
    output-eq = refl
```

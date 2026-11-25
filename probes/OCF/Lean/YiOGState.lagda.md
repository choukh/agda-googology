# 实际前缀的底与起点保持
不读记号；编译定理：两条实际链的更新底保留 Ω 第一位置下界，起点逐前缀递增。
第 0 前缀逐字是标准底；非首前缀的起点精确为前一前缀输出，未填 ActualMissing。
来源：YiOFLimit 的实际更新、YiTBRow.mono；不重置 Base 或 β。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOGState where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiOFLocal as C
import OCF.Lean.YiTNRow as R
import OCF.Lean.YiTNShape as H
import OCF.Lean.YiTNShift as S
import OCF.Lean.YiTQChain as Q

oh : P.Ok (R.shift Q.omega)
oh = subst (λ d → P.Ok (R.shift d)) H.first S.Actual.oc
module A = C.At oh
module G = A.A.Source
module T = A.A.Target

opaque
  unfolding G.prefix G.part G.previous G.base-at G.start-at G.piece G.fold
  source-prefix-positive : (n : ℕ) → B._⊢_◃_ G.ℓ B.zero (G.prefix n)
  source-prefix-positive zero = proj₂ (G.part zero)
  source-prefix-positive (suc n) = B.◃t (source-prefix-positive n)
    (O.+-mono (G.prefix n) (proj₂ (G.part (suc n))))
  source-base-growth : (n : ℕ) (i : B.L) (u : P._≤_ i (C.g (suc n))) →
    B._⊢_◃_ i (proj₁ (O.Ωt i)) (proj₁ (G.base-at (suc n) i u))
  source-base-growth n i u = TB.mono G.ℓ C.og (MT.rbᶻ G.ℓ) (F.B₀ G.ℓ)
    i (P.inc (suc n) u) (O.Ωt i) (source-prefix-positive n)
  source-base-first : (i : B.L) (u : P._≤_ i (C.g 0)) → G.base-at 0 i u ≡ O.Ωt i
  source-base-first i u = refl
  source-start-growth : (n : ℕ) → B._⊢_◃_ B.zero (proj₁ (G.start-at n)) (proj₁ (G.start-at (suc n)))
  source-start-growth zero = TB.mono G.ℓ C.og (MT.rbᶻ G.ℓ) (F.B₀ G.ℓ)
    B.zero (P.inu C.wg) (O.Ωt B.zero) (source-prefix-positive zero)
  source-start-growth (suc n) = G.adj n
  source-start-first : G.start-at 0 ≡ O.Ωt B.zero
  source-start-first = refl
  source-start-next : (n : ℕ) → G.start-at (suc n) ≡ G.piece n
  source-start-next n = refl

opaque
  unfolding T.prefix T.part T.previous T.base-at T.start-at T.piece T.fold
  target-prefix-positive : (n : ℕ) → B._⊢_◃_ T.ℓ B.zero (T.prefix n)
  target-prefix-positive zero = proj₂ (T.part zero)
  target-prefix-positive (suc n) = B.◃t (target-prefix-positive n)
    (O.+-mono (T.prefix n) (proj₂ (T.part (suc n))))
  target-base-growth : (n : ℕ) (i : B.L) (u : P._≤_ i (C.h (suc n))) →
    B._⊢_◃_ i (proj₁ (O.Ωt i)) (proj₁ (T.base-at (suc n) i u))
  target-base-growth n i u = TB.mono T.ℓ oh (MT.rbᶻ T.ℓ) (F.B₀ T.ℓ)
    i (P.inc (suc n) u) (O.Ωt i) (target-prefix-positive n)
  target-base-first : (i : B.L) (u : P._≤_ i (C.h 0)) → T.base-at 0 i u ≡ O.Ωt i
  target-base-first i u = refl
  target-start-growth : (n : ℕ) → B._⊢_◃_ B.zero (proj₁ (T.start-at n)) (proj₁ (T.start-at (suc n)))
  target-start-growth zero = TB.mono T.ℓ oh (MT.rbᶻ T.ℓ) (F.B₀ T.ℓ)
    B.zero (P.inu C.wh) (O.Ωt B.zero) (target-prefix-positive zero)
  target-start-growth (suc n) = T.adj n
  target-start-first : T.start-at 0 ≡ O.Ωt B.zero
  target-start-first = refl
  target-start-next : (n : ℕ) → T.start-at (suc n) ≡ T.piece n
  target-start-next n = refl
```

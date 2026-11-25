# 极限 Ω 折叠的累计状态
不读记号；编译定理：逐前缀错位值界推出整行值界。
每个前缀保留实际更新的 Base 与 β，未给出这些状态间的保持律。
来源：YiRWOps.Ωt、YiTBRow 的 lim/inu 行；实际实例见 YiOFLocal。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOFLimit where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiVWVal as V
module At (g : ℕ → B.L) (o : P.Ok (B.nd B.sL g))
  (w : (n : ℕ) → P._≤_ B.zero (g n)) where
  ℓ = B.nd B.sL g
  opaque
    fold : B.Tr ℓ → O.Tr⁺ B.zero
    fold = TB.ψ ℓ o (MT.rbᶻ ℓ) (F.B₀ ℓ) B.zero (P.inu w) (O.Ωt B.zero)
    fold-eq : (x : B.Tr ℓ) → fold x ≡ TB.ψ ℓ o (MT.rbᶻ ℓ) (F.B₀ ℓ) B.zero (P.inu w) (O.Ωt B.zero) x
    fold-eq x = refl
    part : (n : ℕ) → O.Tr⁺ ℓ
    part n = O.upz n (O.Ωt (g n))
    prefix : ℕ → B.Tr ℓ
    prefix = O.cum (λ n → proj₁ (part n))
    piece : ℕ → O.Tr⁺ B.zero
    piece n = fold (prefix n)
    output : O.Tr⁺ B.zero
    output = fold (proj₁ (O.Ωt ℓ))
    adj : (n : ℕ) → B._⊢_◃_ B.zero (proj₁ (piece n)) (proj₁ (piece (suc n)))
    adj n = TB.mono ℓ o (MT.rbᶻ ℓ) (F.B₀ ℓ) B.zero (P.inu w) (O.Ωt B.zero)
      (O.+-mono (prefix n) (proj₂ (part (suc n))))
    row : proj₁ output ≡ B.lim (λ n → proj₁ (piece n)) adj
    row = refl
    first : piece 0 ≡ TB.ψ (g 0) (proj₂ o 0) (MT.rbᶻ (g 0)) (F.B₀ (g 0))
      B.zero (w 0) (O.Ωt B.zero) (proj₁ (O.Ωt (g 0)))
    first = refl
    previous : ℕ → B.Tr ℓ
    previous zero = B.zero
    previous (suc n) = prefix n
    prefix-form : (n : ℕ) → prefix n ≡ B.up (previous n) n
      (proj₁ (O.Ωt (g n))) (proj₂ (O.Ωt (g n)))
    prefix-form zero = refl
    prefix-form (suc n) = refl
    base-at : (n : ℕ) → F.Base (g n)
    base-at n i u = TB.ψ ℓ o (MT.rbᶻ ℓ) (F.B₀ ℓ) i (P.inc n u)
      (O.Ωt i) (previous n)
    start-at : ℕ → O.Tr⁺ B.zero
    start-at n = fold (previous n)
    state-row : (n : ℕ) → piece n ≡
      TB.ψ (g n) (proj₂ o n) (MT.rbᶻ (g n)) (base-at n)
        B.zero (w n) (start-at n) (proj₁ (O.Ωt (g n)))
    state-row zero = refl
    state-row (suc n) = refl
  point : (n : ℕ) → V.val B.zero (proj₁ (piece n)) V.≼ V.val B.zero (proj₁ output)
  point n = subst (λ x → V.val B.zero (proj₁ (piece n)) V.≼ V.val B.zero x)
    (sym row) (V.≼l n (V.≼-refl _))
module Pair (g h : ℕ → B.L) (og : P.Ok (B.nd B.sL g)) (oh : P.Ok (B.nd B.sL h))
  (wg : (n : ℕ) → P._≤_ B.zero (g n)) (wh : (n : ℕ) → P._≤_ B.zero (h n)) where
  module Source = At g og wg
  module Target = At h oh wh
  PrefixCover = (n : ℕ) → Σ ℕ λ m →
    V.val B.zero (proj₁ (Source.piece n)) V.≼ V.val B.zero (proj₁ (Target.piece m))
  from-prefix : PrefixCover → V.val B.zero (proj₁ Source.output)
    V.≼ V.val B.zero (proj₁ Target.output)
  from-prefix cov = subst (λ x → V.val B.zero x V.≼ V.val B.zero (proj₁ Target.output))
    (sym Source.row) (V.l≼ (λ n → V.≼-trans (proj₂ (cov n)) (Target.point (proj₁ (cov n)))))
```

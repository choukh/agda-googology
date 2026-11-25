# 指定颈结点的树侧比较义务
不读记号；合法闭项与首个累计项的比较已构造，Bound 未实填。
Cover 只量化这两条实际链的累计项，允许两个基本列使用不同下标。
来源：颈结点形状取自任务给定对象；内链与整行出口复用 YiTMInner。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTZLocal where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTMInner as I
import OCF.Lean.YiTZSmall as Small

two : B.L
two = B.nd B.sS (λ _ → Small.one)
o-two : P.Ok two
o-two = tt , λ _ → Small.o-one
child : B.Tr B.zero → B.L
child d = two B.⊕ (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (B.suc d)))
neck : B.L
neck = B.nd (B.sΩ B.zero) child
o-child : (d : B.Tr B.zero) → P.Ok (child d)
o-child d = P.Ok⊕ two (B.zero B.⊕ (B.zero B.⊕ B.↑ B.zero (B.suc d))) o-two
  (P.OkO⊕ two B.zero (B.zero B.⊕ B.↑ B.zero (B.suc d)) tt
    (P.OkO⊕ two B.zero (B.↑ B.zero (B.suc d)) tt
      (P.OkO↑ two B.zero tt (P.z≤ two) (B.suc d))))
o-neck : P.Ok neck
o-neck = (tt , (λ d → P.z≤ (child d))) , o-child

source-child : B.Tr B.zero → B.L
source-child d = B.zero B.⊕ B.↑ B.zero d
module Source = I.Inner B.zero source-child (P.Ok-tw 1)
  (MT.rbᶻ (B.tw 1)) (F.B₀ (B.tw 1)) (O.Ωt B.zero)
opaque
  unfolding Source.feed Source.g
  source-chain-one : Source.chain 1 ≡ proj₁ (MT.ψ₀ᶻ B.zero tt (proj₁ (O.Ωt B.zero)))
  source-chain-one = refl
opaque
  unfolding Source.out Source.g
  source-out-child : (d : B.Tr B.zero) → Source.out d
    ≡ MT.ψ₀ᶻ (source-child d) (proj₂ (P.Ok-tw 1) d) (proj₁ (O.Ωt (source-child d)))
  source-out-child d = refl
opaque
  source : O.Tr⁺ B.zero
  source = I.collapse (B.tw 1) (P.Ok-tw 1) (MT.rbᶻ (B.tw 1)) (F.B₀ (B.tw 1)) (O.Ωt B.zero)
  source-eq : proj₁ source ≡ MT.twᶻ 1
  source-eq = cong proj₁ (I.collapse-eq (B.tw 1) (P.Ok-tw 1)
    (MT.rbᶻ (B.tw 1)) (F.B₀ (B.tw 1)) (O.Ωt B.zero))
  source-row : source ≡ O.limc⁺ (λ n → Source.out (Source.chain n))
  source-row = Source.row
source-cum : ℕ → B.Tr B.zero
source-cum = O.cum (λ n → proj₁ (Source.out (Source.chain n)))

module At (o : P.Ok neck) where
  module Target = I.Inner B.zero child o (MT.rbᶻ neck) (F.B₀ neck) (O.Ωt B.zero)
  opaque
    unfolding Target.feed Target.g
    target-chain-one : Target.chain 1
      ≡ proj₁ (TB.ψ (child B.zero) (proj₂ o B.zero) (MT.rbᶻ (child B.zero))
        (F.B₀ (child B.zero)) B.zero (P.self P.∙ proj₂ (proj₁ o) B.zero) (O.Ωt B.zero)
        (proj₁ (O.Ωt (child B.zero))))
    target-chain-one = refl
  opaque
    unfolding Target.out Target.g
    target-out-child : (d : B.Tr B.zero) → Target.out d
      ≡ MT.ψ₀ᶻ (child d) (proj₂ o d) (proj₁ (O.Ωt (child d)))
    target-out-child d = refl
  opaque
    output : O.Tr⁺ B.zero
    output = I.collapse neck o (MT.rbᶻ neck) (F.B₀ neck) (O.Ωt B.zero)
    output-eq : output ≡ MT.ψ₀ᶻ neck o (proj₁ (O.Ωt neck))
    output-eq = I.collapse-eq neck o (MT.rbᶻ neck) (F.B₀ neck) (O.Ωt B.zero)
    output-row : output ≡ O.limc⁺ (λ n → Target.out (Target.chain n))
    output-row = Target.row
  target-cum : ℕ → B.Tr B.zero
  target-cum = O.cum (λ n → proj₁ (Target.out (Target.chain n)))
  Bound : Set
  Bound = V.val B.zero (proj₁ source) V.≼ V.val B.zero (proj₁ output)
  Cover : Set
  Cover = (n : ℕ) → Σ ℕ (λ m → V.val B.zero (source-cum n) V.≼ V.val B.zero (target-cum m))
  cover-row : Cover → V.val B.zero (proj₁ source)
    V.≼ V.val B.zero (proj₁ (O.limc⁺ (λ n → Target.out (Target.chain n))))
  cover-row cov = subst
    (λ z → V.val B.zero (proj₁ z) V.≼ V.val B.zero (proj₁ (O.limc⁺ (λ n → Target.out (Target.chain n)))))
    (sym source-row) (V.l≼ (λ n → V.≼l (proj₁ (cov n)) (proj₂ (cov n))))
  cover→bound : Cover → Bound
  cover→bound cov = subst (λ z → V.val B.zero (proj₁ source) V.≼ V.val B.zero (proj₁ z))
    (sym output-row) (cover-row cov)
  opaque
    unfolding Source.out Source.g Target.out Target.g
    first-piece : V.val B.zero (source-cum 0) V.≼ V.val B.zero (target-cum 0)
    first-piece = V.≼l 0 (V.≼-refl _)
  first-cover : Σ ℕ (λ m → V.val B.zero (source-cum 0) V.≼ V.val B.zero (target-cum m))
  first-cover = 0 , first-piece
  first-in-output : V.val B.zero (source-cum 0) V.≼ V.val B.zero (proj₁ output)
  first-in-output = subst (λ z → V.val B.zero (source-cum 0) V.≼ V.val B.zero (proj₁ z))
    (sym output-row) (V.≼l 0 first-piece)
  Next : Set
  Next = Σ ℕ (λ m → V.val B.zero (source-cum 1) V.≼ V.val B.zero (target-cum m))

module Canonical = At o-neck
```

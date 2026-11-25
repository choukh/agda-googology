# 两个目标在第四层同一张实际槽表上的检验

第四层。在指定正槽读值上，同时实例化首枝 ψ₀ψ₃(Ω₂) 与有限行的完整 Ω₂ 查询判据。对 ψ₀(Ω₃) 的那一行，已实付 ψ₀ψ₂²(0)，余下高度可由同一条可迭代的见证延长律覆盖。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchLiveTest where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import WVOne using (read; T₀)
open import OCF.Lean.YiRefTw2 using (Rt)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc)
import W4Fold
import WKTower as Tower
import B12Terminal as RunT
import B12ActualSlots as Slots
import B19IdealProduct as Alg
import B12TerminalSrc as Source
import B13FiniteClosed as Covered
import B12BtboCut as Ref
import Survey.EboPTOFinite as B
import Survey.W4PTOFinite as PTO
import Survey.W4FiniteRaiseWindow as W
import Survey.W4FiniteRaiseConsume as Start
import Survey.W4FirstBranchRunLive as Run
import Survey.W4FirstBranchRunSum as Sum
import Survey.W4FirstBranchTest as Test

module At (r : RunT.Run Tower.Lω) (cv : Slots.Covered r) where
  module A = Run.Actual r
  module Win = W.Receiver r
  module S = Sum.At r cv

  weak : ∀ {x y : T₀} → L.suc x ≼ y → x ≼ y
  weak {x} p = ≼-trans {b = L.suc x} (≼-suc (≼-refl x)) p

  -- 指数 1 在孩子语境内的观察恰为外面那一行的初始加项。
  first-covered : S.terms 0 ≼ A.Ω₂ 0 0
  first-covered = weak (A.Inner.At.gain A.C.initial A.C.target (A.I.run _ A.I.w A.I.β (proj₁ A.a)))

  module Q = Test.Sums A.Ω₂ (S.terms 0) (Win.full 2) first-covered

  matches : ∀ k → Q.total k ≡ S.sums k
  matches zero = refl
  matches (suc k) = cong (λ v → v L.+ L.lim (A.Ω₂ k)) (matches k)

  exact : L.lim Q.total ≈ᵛ Win.full 2
  exact = Alg._∙_ {y = L.lim S.sums} (Alg.lim (λ k → eq (matches k))) S.exact
    where
    eq : ∀ {a b : T₀} → a ≡ b → a ≈ᵛ b
    eq refl = Alg.id _

  paid : ∀ m n → A.Ω₂ m n ≼ Win.full 2
  paid m n = ≼-trans {b = A.prefix (suc m)} (weak (A.paid cv m n)) (weak (A.into (suc m)))

  module Branch = Q.Test exact paid Test.branch-scale
  module Row (j : ℕ) = Q.Test exact paid (Test.row-scale j)

module Live = At Source.middle Covered.middle-covered
open Live using (module A; module Row; module Branch; weak)

open import Survey.W4FirstBranchRoom public using (stage; rise)

base : ∀ m → L.suc (stage 2) ≼ A.Ω₂ m 0
base m = ≼-trans {b = W.Live.small 2} Start.base (weak (A.Ω₂-above-one m))

Hit = Row.hit 2
Extend = ∀ k → Hit (suc (suc k)) → Hit (suc (suc (suc k)))

close : Extend → Ref.finite 3 ≼ W.Live.full 2
close extend = ≼-trans {b = Rt (B.row-h 2)} (proj₂ (PTO.scale 2)) (Row.sufficient 2 all)
  where
  tail : ∀ k → Hit (suc (suc k))
  tail zero = 0 , 0 , base 0
  tail (suc k) = extend k (tail k)
  all : ∀ k → Hit k
  all zero = 0 , 0 , ≼-trans {b = stage 1} (rise 0)
    (≼-trans {b = stage 2} (weak (rise 1)) (weak (base 0)))
  all (suc zero) = 0 , 0 , ≼-trans {b = stage 2} (rise 1) (weak (base 0))
  all (suc (suc k)) = tail k

cross : Extend → L.suc (Ref.finite 3) ≼ read W4Fold.EBOᶜ
cross e = ≼-trans (OCF.Align.Value.s≼s (close e)) (W.in-tree 2)
```

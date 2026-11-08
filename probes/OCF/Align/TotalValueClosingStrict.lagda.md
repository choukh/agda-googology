# 原闭包行在新语义下严格高于其低行

种子只用原 Ωd1 的真实第零支；第二观察输出只用原 Q 的统一正性。
不假设全回调值单调，不把原 force 的严格性搬来充数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.TotalValueClosingStrict (S : HtB) where
open import Data.Nat using (zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; cong)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Align.LadderOrdTree S
open import OCF.Align.ValLabLadder S using (e₀; ev₀; rowC-eq)
open import OCF.Align.ValueJudgeBase
import OCF.Align.TotalValueBuildHighChain S as H
import OCF.Align.TotalValueNegSeedZero S as Seed
import OCF.Align.TotalValueNegPositive S as Pos
import OCF.Align.TotalValueClosureStrict as C
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A

module Row {n m} (r : n <ᴸ m) where
  raw : Z
  raw = toZ (ψ̄ᵠ ok₀ e₀ (rowC r (Ω̇ n)) ev₀ zero)

  record Parts : Set where
    field
      c : Ordᴵ
      t : Z
      g : (η : Ordᴵ) → c ⊑ᴵ η → Z
      shape : raw ≡ Z.ĉᴸ c t g t g

  parts : Parts
  parts = record { c = _ ; t = _ ; g = _ ; shape = refl }
  open Parts parts

  seed-lower : H.value n ≼ A.read (R.run t)
  seed-lower = Seed.seed-zero r ok₀ _ ev₀ zero

  next-positive : ∀ η e → suc (zero {ℓ = zero}) ≼ A.read (R.run (g η e))
  next-positive η e = Pos.positive _ _ (ι↓ {α = zero} r (Ω̇ n η)) ev₀ zero

  module Node = C.Node c t g t g
  strict : suc (H.value n) ≼ A.read (R.run raw)
  strict = subst (λ z → suc (H.value n) ≼ A.read (R.run z)) (sym shape)
    (≼-trans (s≼s seed-lower)
      (Node.strict-first (next-positive (Node.Tr.η zero) (Node.Tr.bound zero))))

closing-strict : ∀ {n m} (r : n <ᴸ m) → view m ≡ clos r → suc (H.value n) ≼ H.value m
closing-strict r ve = subst
  (λ x → suc (H.value _) ≼ A.read (R.run (toZ (ψ̄ᵠ ok₀ e₀ x ev₀ zero))))
  (sym (rowC-eq r ve)) (Row.strict r)
```

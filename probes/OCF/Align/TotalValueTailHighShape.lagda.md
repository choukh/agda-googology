# 完整端行的两层累计分解

所有外层和内层分量均保留，首输出仍是原𝟏L的实际读取。这个公式
把最高闭项的上界问题定位到整族非零闭包行，而不是有限抽样。
尚不把低行的新值替换成旧 EmbVV 行值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailHighShape where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Align.LadderOrdBase using (chain)
open import OCF.Align.LadderOrdPos using (HB; end; low; blk; ltB-same)
open import OCF.Align.LadderOrdCode using (ω²ᶜ; ωᶜ)
open import OCF.Align.LadderOrdTree (HB ω²ᶜ)
open import OCF.Align.TotalValueTailHighChain (HB ω²ᶜ)
open import OCF.Align.TotalValueTailCongruence using (complete-cong)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.LiteralCompletion as C
import OCF.Align.RadicalValueNativeFinal as Final
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; same-value; same-sym)
open import OCF.Align.TotalValueTailGenerated using (leg-shape)
open import OCF.Lean.Fold1If using (_≤ᵛ_)

outer : ℕ → Ht
outer n = low (blk n end)
outer-path : ∀ n → outer n <ᴸ end
outer-path n = tt
outer-view : view end ≡ chain outer outer-path
outer-view = refl
inner : ℕ → ℕ → Ht
inner n k = low (blk n (low (blk k end)))
inner-path : ∀ n k → inner n k <ᴸ outer n
inner-path zero k = tt
inner-path (suc n) k = ltB-same (λ _ → ωᶜ) (suc n) tt
inner-view : ∀ n → view (outer n) ≡ chain (inner n) (inner-path n)
inner-view zero = refl
inner-view (suc n) = refl

inner-output : ℕ → Ordᴵ
inner-output n = R.complete (seq (λ k → native (inner n k)))
double-output : Ordᴵ
double-output = R.complete (seq inner-output)

raw-shape : native end ≅ᴵ double-output
raw-shape = ≅ᴵ-trans (chain-shape end outer outer-path outer-view)
  (complete-cong branches)
  where
  branches : ∀ n → seq (λ k → native (outer k)) n ≅ᴵ seq inner-output n
  branches zero = ≅ᴵ-refl _
  branches (suc n) = chain-shape (outer n) (inner n) (inner-path n) (inner-view n)

forget-shape : ∀ {a b} → a ≅ᴵ b → Same (Final.forget a) (Final.forget b)
forget-shape z≅ = zz
forget-shape (s≅ p) = ss (forget-shape p)
forget-shape (l≅ p) = ll (λ n → forget-shape (p n))
closed-shape : Same (proj₁ Final.closed) (C.leg (Final.forget double-output))
closed-shape = leg-shape (forget-shape raw-shape)
closed-upper : proj₁ Final.closed ≤ᵛ C.leg (Final.forget double-output)
closed-upper = same-value closed-shape
closed-lower : C.leg (Final.forget double-output) ≤ᵛ proj₁ Final.closed
closed-lower = same-value (same-sym closed-shape)
```

这只是完整原对象的结构分解，closed-upper 不是具名粗上界。
若想用旧行作为上界，必须控制这里每个 native(inner n k) 的全部
回灌，以及累计与最后 leg 的有限和；仅有原 D-val 零参数，或每支
普通值界，都不能自动完成该控制。

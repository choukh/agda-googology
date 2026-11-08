# 新运行器保持完整的原 Z 结构相容关系

Free.Eq 的 ≅ᶻ 在闭包节点要求界同形，并要求回调在两侧各自可入、
且同形的坐标上返回相关树。正是这些异坐标字段使两条新真实轨道
可以同步；这里没有把 Pointwise 升级，也没有假设任意回调保值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueTailCongruence where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
open import OCF.Free.Eq using (_≅ᶻ_; zᶻ; sᶻ; lᶻ; ĉᶻ)
import OCF.Free.TotalOrbitRun as R
import OCF.Free.TotalOrbitBuild as A
import OCF.Align.TotalValueTraceShape as Trace

add-both-cong : ∀ {a b c d} → a ≅ᴵ b → c ≅ᴵ d → R.add a c ≅ᴵ R.add b d
add-both-cong p z≅ = p
add-both-cong p (s≅ q) = s≅ (add-both-cong p q)
add-both-cong p (l≅ q) = l≅ (λ n → add-both-cong p (q n))

sum-cong : ∀ {f g : ℕ → Ordᴵ} → (∀ n → f n ≅ᴵ g n) →
  ∀ n → R.sum f n ≅ᴵ R.sum g n
sum-cong p zero = p zero
sum-cong p (suc n) = add-both-cong (sum-cong p n) (p (suc n))
complete-cong : ∀ {f g : ℕ → Ordᴵ} → (∀ n → f n ≅ᴵ g n) →
  R.complete f ≅ᴵ R.complete g
complete-cong p = l≅ (sum-cong p)

run-cong : ∀ {x y} → x ≅ᶻ y → R.run x ≅ᴵ R.run y
run-cong zᶻ = z≅
run-cong (sᶻ p) = s≅ (run-cong p)
run-cong (lᶻ p) = complete-cong (λ n → run-cong (p n))
run-cong (ĉᶻ {c = c} {c′ = c′} {t₀ = t} {t₀′ = t′} {o₀ = o₀} {o₀′ = o₀′} {g = g} {o = o} {g′ = g′} {o′ = o′} ec dt dg dp dO) =
  ≅ᴵ-trans X.shape (≅ᴵ-trans (complete-cong outputs) (≅ᴵ-sym Y.shape))
  where
  module X = Trace.Node c t g o₀ o
  module Y = Trace.Node c′ t′ g′ o₀′ o′

  coordinates : ∀ n → X.η n ≅ᴵ Y.η n
  coordinates zero = ≅ᴵ-trans (Trace.equality-shape X.start)
    (≅ᴵ-trans (add-both-cong ec (run-cong dt)) (≅ᴵ-sym (Trace.equality-shape Y.start)))
  coordinates (suc n) = ≅ᴵ-trans (Trace.equality-shape (X.step n))
    (≅ᴵ-trans (add-both-cong ec
      (run-cong (dg (X.η n) (X.bound n) (Y.η n) (Y.bound n) (coordinates n))))
      (≅ᴵ-sym (Trace.equality-shape (Y.step n))))

  outputs : ∀ n → X.outputs n ≅ᴵ Y.outputs n
  outputs zero = run-cong dp
  outputs (suc n) = run-cong
    (dO (X.η n) (X.bound n) (Y.η n) (Y.bound n) (coordinates n))

read-run-cong : ∀ {x y} → x ≅ᶻ y → A.read (R.run x) ≅ A.read (R.run y)
read-run-cong p = A.read-cong (run-cong p)
```

结论适用于全域已有 ≅ᶻ 证据，不要求旧 Goodᴺ，也不要求两个闭包
使用相同的界证明。actual Trace 保留各自私有轨道的原 bound；
回调关系本身明确允许这些不同证据。这里不比较原 force 与新 run，
不声称两个仅有值相等的 Z 树会有相等输出。

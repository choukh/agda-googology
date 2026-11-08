# 不改运行器，取得其真实反馈轨道

见证由运行方程的定义性相等解出；不复制另一条轨道后假定证据相等。
对每个原节点给出精确部分和方程，不改原私有 where 的可见性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TotalValueActualTrace where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; ĉᴸ)
import OCF.Free.TotalOrbitRun as R

part : Ordᴵ → ℕ → Ordᴵ
part zero n = zero
part (suc a) n = zero
part (lim f st) n = f n

record Trace (c : Ordᴵ) (t : Z) (g : (η : Ordᴵ) → c ⊑ᴵ η → Z)
  (o₀ : Z) (o : (ζ : Ordᴵ) → c ⊑ᴵ ζ → Z) : Set where
  field
    η : ℕ → Ordᴵ
    bound : ∀ n → c ⊑ᴵ η n
    start : η zero ≡ R.add c (R.run t)
    step : ∀ n → η (suc n) ≡ R.add c (R.run (g (η n) (bound n)))
    computation : ∀ n →
      part (R.run (ĉᴸ c t g o₀ o)) n ≡
        R.sum (λ { zero → R.run o₀ ; (suc k) → R.run (o (η k) (bound k)) }) n

trace : ∀ c t g o₀ o → Trace c t g o₀ o
trace c t g o₀ o = record
  { η = _
  ; bound = _
  ; start = refl
  ; step = λ n → refl
  ; computation = go }
  where
  go : ∀ n → _
  go zero = refl
  go (suc n) = cong₂ R.add (go n) refl
```

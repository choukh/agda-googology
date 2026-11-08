# 全有限源层的实际可数求值与后继补偿

这里的read只包装原at与原末段fold，不新定义折叠。中间Value到目标0
才转VRel，故不用高层裸值序。完整ω重复吸收补偿，得到与源层无关的
可数输出和定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionUniformEvaluation where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (Σ₀)
open import OCF.Lean.Fold1If using (_≤ᵛ_; mul; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)
open import OCF.Align.FrozenValueFirst using (add-mono)
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunIf using (at)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Align.BoundedCompletionFiniteRunFloor using (legal-num)
open import OCF.Align.BoundedCompletionUniformIf using (Value; vs)
import OCF.Align.BoundedCompletionUniformClosure as V
import OCF.Align.BoundedCompletionUniformRun as Run
import OCF.Align.BoundedCompletionTerminalValueIf as TV
import OCF.Align.BoundedCompletionTerminalValueRun as Eval
import OCF.Align.BoundedCompletionOutputRepeat as Repeat
import OCF.Align.BoundedNativeTerminalReady as T

input : ∀ n → HB (Native (num n)) → HB (Native hz)
input n a = at n zero (legal-num n) hself (z⊲ᴮ (num n)) a
read : ∀ n → Cd → HB (Native (num n)) → Cd
read n b a = T.fold b (input n a)

related : ∀ n {a b} → Value (num n) a b → TV.VRel (input n a) (input n b)
related n p = V.value-zero (Run.compare n zero (legal-num n) (legal-num n)
  hself hself (z⊲ᴮ (num n)) (z⊲ᴮ (num n)) p)
positive : ∀ n a → TV.VRel (hs hz) (input n a)
positive n a = V.value-zero (Run.positive n zero (legal-num n) hself (z⊲ᴮ (num n)) a)

monotone : ∀ n {a b u v} → Value (num n) a b → u ≤ᵛ v → read n u a ≤ᵛ read n v b
monotone n p uv = Eval.eval (related n p) uv

successor-repeat : ∀ n {a} → Value (num n) a a → ∀ b →
  hl (mul (read n b a)) ≤ᵛ read n b (hs a)
successor-repeat n {a} p b = Repeat.Repeat.lower (input n a) (related n p) (positive n a) b

padded-add : ∀ n {a b u v w} → Value (num n) a a → Value (num n) b b →
  u ≤ᵛ w → v ≤ᵛ w → read n u a ⊞ read n v b ≤ᵛ read n w (a ⊞ hs b)
padded-add n {a} {b} {u} {v} {w} ra rb uw vw = ≤-trans twice
  (successor-repeat n (V.add-rel ra rb) w)
  where
  twice : read n u a ⊞ read n v b ≤ᵛ hl (mul (read n w (a ⊞ b)))
  twice = ≤l 1 (add-mono (monotone n (V.prefix-rel ra b) uw)
    (monotone n (V.right-rel a rb) vw))

pad : ∀ n → (ℕ → HB (Native (num n))) → ℕ → HB (Native (num n))
pad n f zero = f zero
pad n f (suc k) = pad n f k ⊞ hs (f (suc k))
pad-self : ∀ n f → (∀ k → Value (num n) (f k) (f k)) → ∀ k →
  Value (num n) (pad n f k) (pad n f k)
pad-self n f r zero = r zero
pad-self n f r (suc k) = V.add-rel (pad-self n f r k) (vs (r (suc k)))

sum≤pad : ∀ n f → (∀ k → Value (num n) (f k) (f k)) → ∀ (seeds : ℕ → Cd) w →
  (∀ k → seeds k ≤ᵛ w) → ∀ k →
  Σ₀ (λ j → read n (seeds j) (f j)) k ≤ᵛ read n w (pad n f k)
sum≤pad n f r seeds w upper zero = monotone n (r zero) (upper zero)
sum≤pad n f r seeds w upper (suc k) = ≤-trans
  (add-mono (sum≤pad n f r seeds w upper k) (≤-refl _))
  (padded-add n (pad-self n f r k) (r (suc k)) (≤-refl w) (upper (suc k)))

floor-repeat : ∀ n b → hl (mul (read n b (floor n))) ≤ᵛ read n b (hs (floor n))
floor-repeat n b = successor-repeat n (V.floor-value n) b
```

floor-repeat对全部真实有限flL实证前提。该结果不是Old各世界折叠已等于
read，也未把任意raw输入当作Value自相关；全层旧/新轨道桥须另证。
